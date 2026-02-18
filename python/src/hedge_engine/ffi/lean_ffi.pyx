# cython: language_level=3
"""
Cython FFI bindings to Lean 4 accounting kernel.

Exposes @[export hedge_*] functions from OptionHedge.Accounting.
All monetary values are in basis points (×10,000).

Reference counting rules (Lean deterministic RC):
- Objects created here start at rc=1 (caller owns).
- Passing to an FFI function transfers ownership — do not lean_dec after.
- lean_ctor_get returns a *borrowed* reference — lean_inc if kept past parent.
- Return values from FFI are owned by the caller — lean_dec when done.
- Scalars (lean_box, lean_is_scalar) need no ref counting.
"""

from libc.stdint cimport int64_t, uint8_t
from libc.string cimport strlen

# ---------------------------------------------------------------------------
# C declarations — lean.h
# ---------------------------------------------------------------------------

cdef extern from "lean/lean.h":
    ctypedef void* lean_object

    # --- Runtime lifecycle ---
    # lean_initialize_runtime_module is in libleanrt but NOT declared in lean.h;
    # it is forward-declared in the extern-from-* block below.
    void lean_io_mark_end_initialization()
    bint lean_io_result_is_error(lean_object* r)

    # --- Reference counting ---
    void lean_inc(lean_object* o)
    void lean_dec(lean_object* o)
    void lean_dec_ref(lean_object* o)

    # --- Scalars / tagged pointers ---
    bint lean_is_scalar(lean_object* o)
    lean_object* lean_box(size_t n)
    size_t lean_unbox(lean_object* o)

    # --- Integers (Lean `Int` ↔ C int64) ---
    lean_object* lean_int64_to_int(int64_t n)
    int64_t lean_scalar_to_int64(lean_object* o)

    # --- Strings ---
    lean_object* lean_mk_string(const char* s)
    const char* lean_string_cstr(lean_object* s)

    # --- Constructors (inductive types / structures) ---
    lean_object* lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz)
    void lean_ctor_set(lean_object* o, unsigned i, lean_object* v)
    lean_object* lean_ctor_get(lean_object* o, unsigned i)
    unsigned lean_obj_tag(lean_object* o)


# ---------------------------------------------------------------------------
# Lean module initialiser + hedge_* exports  (forward declarations)
# ---------------------------------------------------------------------------

cdef extern from *:
    """
    // lean_initialize_runtime_module is exported from libleanrt but not
    // declared in lean.h — forward-declare it here.
    extern void lean_initialize_runtime_module(void);

    // Lean module initialiser — must be called before any hedge_* function.
    extern lean_object* initialize_option_x2dhedge_x2dengine_OptionHedge_Accounting(
        uint8_t builtin);

    // FFI exports from OptionHedge.Accounting
    extern lean_object* hedge_position_value(lean_object*);
    extern lean_object* hedge_sum_position_values(lean_object*);
    extern lean_object* hedge_portfolio_nav(lean_object*);
    extern lean_object* hedge_mk_portfolio(lean_object*, lean_object*);
    extern lean_object* hedge_get_position(lean_object*, lean_object*);
    extern lean_object* hedge_apply_trade(lean_object*, lean_object*);
    """
    void lean_initialize_runtime_module()
    lean_object* initialize_option_x2dhedge_x2dengine_OptionHedge_Accounting(
        uint8_t builtin)
    lean_object* hedge_position_value(lean_object* pos)
    lean_object* hedge_sum_position_values(lean_object* portfolio)
    lean_object* hedge_portfolio_nav(lean_object* portfolio)
    lean_object* hedge_mk_portfolio(lean_object* cash, lean_object* positions)
    lean_object* hedge_get_position(lean_object* portfolio, lean_object* asset_id)
    lean_object* hedge_apply_trade(lean_object* portfolio, lean_object* trade)


# ---------------------------------------------------------------------------
# Internal marshalling helpers (cdef — not visible from Python)
# ---------------------------------------------------------------------------

cdef lean_object* _py_int_to_lean(int64_t n):
    """Python/C int64 → Lean Int."""
    return lean_int64_to_int(n)


cdef int64_t _lean_int_to_py(lean_object* o):
    """Lean Int → C int64.  Only handles scalar (non-bignum) integers."""
    if lean_is_scalar(o):
        return lean_scalar_to_int64(o)
    # Basis-point values fit in int64; a bignum here indicates a bug.
    raise OverflowError("Lean Int is a bignum — unexpected for basis-point values")


cdef lean_object* _py_str_to_lean(str s):
    """Python str → Lean String."""
    encoded = s.encode("utf-8")
    return lean_mk_string(encoded)


cdef str _lean_str_to_py(lean_object* s):
    """Lean String → Python str (borrowed ref, does not consume s)."""
    return lean_string_cstr(s).decode("utf-8")


cdef lean_object* _py_pos_to_lean(dict pos):
    """Python position dict → Lean Position (tag=0, 3 obj-fields).

    Position fields at the C level (proof `markPrice_pos` is erased):
      0: asset    : String
      1: quantity : Int
      2: markPrice: Int
    """
    cdef lean_object* lean_pos = lean_alloc_ctor(0, 3, 0)
    lean_ctor_set(lean_pos, 0, _py_str_to_lean(pos.get("asset_id", "")))
    lean_ctor_set(lean_pos, 1, _py_int_to_lean(pos["quantity"]))
    lean_ctor_set(lean_pos, 2, _py_int_to_lean(pos["mark_price"]))
    return lean_pos


cdef dict _lean_pos_to_py(lean_object* pos):
    """Lean Position → Python dict (borrowed ref, does not consume pos).

    lean_inc the fields we read so they survive past the parent being freed.
    """
    cdef lean_object* asset_obj = lean_ctor_get(pos, 0)
    cdef lean_object* qty_obj   = lean_ctor_get(pos, 1)
    cdef lean_object* price_obj = lean_ctor_get(pos, 2)
    lean_inc(asset_obj)
    lean_inc(qty_obj)
    lean_inc(price_obj)
    result = {
        "asset_id":   _lean_str_to_py(asset_obj),
        "quantity":   _lean_int_to_py(qty_obj),
        "mark_price": _lean_int_to_py(price_obj),
    }
    lean_dec(asset_obj)
    lean_dec(qty_obj)
    lean_dec(price_obj)
    return result


cdef lean_object* _py_list_to_lean(list positions):
    """Python list[dict] → Lean `List Position` (cons-list, owned ref).

    Lean List representation:
      nil        = lean_box(0)          (scalar, no RC needed)
      cons h t   = lean_alloc_ctor(1, 2, 0)  fields: 0=head, 1=tail
    Build in reverse so the final list preserves original order.
    """
    cdef lean_object* lst = lean_box(0)   # List.nil
    cdef lean_object* node
    for pos_dict in reversed(positions):
        node = lean_alloc_ctor(1, 2, 0)   # List.cons
        lean_ctor_set(node, 0, _py_pos_to_lean(pos_dict))
        lean_ctor_set(node, 1, lst)
        lst = node
    return lst


cdef lean_object* _py_to_portfolio(int64_t cash, list positions):
    """Construct a Lean Portfolio via hedge_mk_portfolio (consumes its args)."""
    cdef lean_object* cash_lean = _py_int_to_lean(cash)
    cdef lean_object* pos_list  = _py_list_to_lean(positions)
    return hedge_mk_portfolio(cash_lean, pos_list)


cdef lean_object* _py_trade_to_lean(str asset_id, int64_t delta_qty,
                                     int64_t exec_price, int64_t fee):
    """Python trade fields → Lean Trade (tag=0, 4 obj-fields; proof fields erased).

    Trade fields at the C level (executionPrice_pos and fee_nonneg are erased):
      0: assetId        : String
      1: deltaQuantity  : Int
      2: executionPrice : Int
      3: fee            : Int
    """
    cdef lean_object* trade = lean_alloc_ctor(0, 4, 0)
    lean_ctor_set(trade, 0, _py_str_to_lean(asset_id))
    lean_ctor_set(trade, 1, _py_int_to_lean(delta_qty))
    lean_ctor_set(trade, 2, _py_int_to_lean(exec_price))
    lean_ctor_set(trade, 3, _py_int_to_lean(fee))
    return trade


cdef list _lean_list_to_py(lean_object* lst):
    """Lean List Position → Python list[dict] (borrowed ref, does not consume lst).

    Traverses the cons-list and returns each position as a dict.
    lean_is_scalar distinguishes nil (scalar lean_box(0)) from cons (heap object).
    """
    cdef lean_object* head
    result = []
    while not lean_is_scalar(lst):   # lean_is_scalar(lst) == True means nil
        head = lean_ctor_get(lst, 0)
        result.append(_lean_pos_to_py(head))
        lst = lean_ctor_get(lst, 1)  # borrowed tail
    return result


cdef dict _lean_portfolio_to_py(lean_object* portfolio):
    """Lean Portfolio → Python dict. Consumes portfolio (owned ref).

    Portfolio fields at the C level (nav_valid proof is erased):
      0: cash      : Int
      1: positions : List Position
      2: nav       : Int
    """
    cdef lean_object* cash_obj = lean_ctor_get(portfolio, 0)
    cdef lean_object* pos_list = lean_ctor_get(portfolio, 1)
    cdef lean_object* nav_obj  = lean_ctor_get(portfolio, 2)
    lean_inc(cash_obj)
    lean_inc(pos_list)
    lean_inc(nav_obj)
    lean_dec(portfolio)   # fields survive because we lean_inc'd them above
    cdef int64_t cash_val = _lean_int_to_py(cash_obj)
    cdef int64_t nav_val  = _lean_int_to_py(nav_obj)
    positions = _lean_list_to_py(pos_list)
    lean_dec(cash_obj)
    lean_dec(nav_obj)
    lean_dec(pos_list)
    return {"cash": cash_val, "positions": positions, "nav": nav_val}


# ---------------------------------------------------------------------------
# Public API — matches existing stub signatures
# ---------------------------------------------------------------------------

def initialize_lean():
    """Initialise Lean runtime and the OptionHedge.Accounting module.

    Must be called exactly once before any other FFI function.
    """
    lean_initialize_runtime_module()
    cdef lean_object* res = \
        initialize_option_x2dhedge_x2dengine_OptionHedge_Accounting(1)
    if lean_io_result_is_error(res):
        lean_dec(res)
        raise RuntimeError("Failed to initialise Lean OptionHedge.Accounting module")
    lean_dec(res)
    lean_io_mark_end_initialization()


def position_value(int quantity, int mark_price) -> int:
    """hedge_position_value: quantity × markPrice (basis points)."""
    # Construct a temporary Position with an empty asset string.
    # The asset field is irrelevant for value calculation.
    cdef lean_object* pos = lean_alloc_ctor(0, 3, 0)
    lean_ctor_set(pos, 0, lean_mk_string(b""))
    lean_ctor_set(pos, 1, _py_int_to_lean(quantity))
    lean_ctor_set(pos, 2, _py_int_to_lean(mark_price))
    cdef lean_object* result = hedge_position_value(pos)   # consumes pos
    cdef int64_t val = _lean_int_to_py(result)
    lean_dec(result)
    return val


def sum_position_values(list positions) -> int:
    """hedge_sum_position_values: sum of all position values (basis points)."""
    cdef lean_object* portfolio = _py_to_portfolio(0, positions)
    cdef lean_object* result    = hedge_sum_position_values(portfolio)  # consumes
    cdef int64_t val = _lean_int_to_py(result)
    lean_dec(result)
    return val


def calc_nav(int cash, list positions) -> int:
    """hedge_portfolio_nav: O(1) NAV read from stored field (basis points)."""
    cdef lean_object* portfolio = _py_to_portfolio(cash, positions)
    cdef lean_object* result    = hedge_portfolio_nav(portfolio)  # consumes
    cdef int64_t val = _lean_int_to_py(result)
    lean_dec(result)
    return val


def apply_trade(int cash, list positions, str asset_id,
                int delta_quantity, int execution_price, int fee) -> dict:
    """hedge_apply_trade: apply a trade, returning updated portfolio dict.

    Returns {"cash": int, "positions": list[dict], "nav": int}.
    Both portfolio and trade are consumed by the FFI call.
    """
    cdef lean_object* portfolio = _py_to_portfolio(cash, positions)
    cdef lean_object* trade     = _py_trade_to_lean(asset_id, delta_quantity,
                                                     execution_price, fee)
    cdef lean_object* result    = hedge_apply_trade(portfolio, trade)  # consumes both
    return _lean_portfolio_to_py(result)   # consumes result


def get_position(list positions, str asset_id) -> dict | None:
    """hedge_get_position: lookup a position by asset ID.

    Returns the matching position dict, or None if not found.

    Lean Option representation:
      none   = lean_box(0)   →  tag 0  (scalar)
      some x = ctor tag 1    →  tag 1, field 0 = Position
    """
    cdef lean_object* portfolio = _py_to_portfolio(0, positions)
    cdef lean_object* id_lean   = _py_str_to_lean(asset_id)
    cdef lean_object* result    = hedge_get_position(portfolio, id_lean)  # consumes both

    cdef unsigned tag = lean_obj_tag(result)
    if tag == 0:   # Option.none
        return None

    # Option.some — field 0 is the Position
    cdef lean_object* pos = lean_ctor_get(result, 0)
    lean_inc(pos)          # keep pos alive after result is freed
    lean_dec(result)
    py_pos = _lean_pos_to_py(pos)
    lean_dec(pos)
    return py_pos
