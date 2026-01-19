# cython: language_level=3
"""
Cython FFI bindings to Lean 4 accounting kernel.

Exposes calc_nav and other @[export] functions from Lean.
"""

cdef extern from "lean/lean.h":
    ctypedef void* lean_object

    # Lean runtime initialization
    void lean_initialize_runtime_module()
    void lean_io_mark_end_initialization()

    # Reference counting
    void lean_inc(lean_object*)
    void lean_dec(lean_object*)

    # Integer operations
    lean_object* lean_box(size_t)
    lean_object* lean_int_to_int(lean_object*)
    int lean_is_scalar(lean_object*)

# External declarations for our exported Lean functions
cdef extern from *:
    """
    // Forward declarations for Lean exports
    extern lean_object* calc_nav(lean_object*);
    extern lean_object* sum_position_values(lean_object*);
    extern lean_object* position_value(lean_object*);
    """
    lean_object* calc_nav(lean_object*)
    lean_object* sum_position_values(lean_object*)
    lean_object* position_value(lean_object*)


def initialize_lean():
    """Initialize Lean runtime. Call once before using any FFI functions."""
    lean_initialize_runtime_module()
    lean_io_mark_end_initialization()


# TODO: Implement actual Portfolio/Position marshalling in next iteration
# For now, just stub to verify compilation works
def calc_nav_stub():
    """Stub function - full implementation requires Portfolio marshalling."""
    return 0
