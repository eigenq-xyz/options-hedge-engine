"""Test FFI bindings to Lean accounting kernel."""

import pytest

# Import the package first so __init__.py pre-loads libuv (required by the
# Lean runtime) before we attempt to import the compiled extension directly.
import hedge_engine.ffi as _ffi_pkg  # noqa: F401

# Detect whether a functional compiled Cython extension is available.
# Checking importability alone is not sufficient — a stale .so may exist but
# lack symbols from the current kernel version.  We require portfolio_value to be
# present as a minimum signal that the extension is up to date.
try:
    import hedge_engine.ffi.lean_ffi as _lean_ffi_ext

    HAS_LEAN_FFI = hasattr(_lean_ffi_ext, "portfolio_value")
except ImportError:
    HAS_LEAN_FFI = False

from hedge_engine.ffi import (
    apply_trade,
    get_position,
    initialize_lean,
    portfolio_value,
    position_value,
    sum_position_values,
)

# -- Lean runtime --


def test_lean_runtime_initialization():
    """Lean runtime initializes without error."""
    initialize_lean()


# -- position_value --


def test_position_value_long():
    """100 shares at $50.00 (500,000 bp) = $5,000.00 (50,000,000 bp)."""
    assert position_value(100, 500000) == 50_000_000


def test_position_value_short():
    """-50 shares at $180.00 (1,800,000 bp) = -$9,000.00 (-90,000,000 bp)."""
    assert position_value(-50, 1800000) == -90_000_000


def test_position_value_zero_quantity():
    """Zero quantity always yields zero value."""
    assert position_value(0, 500000) == 0


# -- sum_position_values --


def test_sum_position_values_empty():
    """Empty position list sums to zero."""
    assert sum_position_values([]) == 0


def test_sum_position_values_multiple():
    """SPY + AAPL position values."""
    positions = [
        {"asset_id": "SPY", "quantity": 100, "mark_price": 500000},
        {"asset_id": "AAPL", "quantity": 50, "mark_price": 1800000},
    ]
    assert sum_position_values(positions) == 140_000_000


# -- portfolio_value --


def test_portfolio_value_empty_portfolio():
    """Portfolio value of empty portfolio equals cash."""
    assert portfolio_value(cash=1_000_000, positions=[]) == 1_000_000


def test_portfolio_value_with_positions():
    """Portfolio value = cash + sum of position values."""
    positions = [
        {"asset_id": "SPY", "quantity": 100, "mark_price": 500000},
        {"asset_id": "AAPL", "quantity": 50, "mark_price": 1800000},
    ]
    assert portfolio_value(cash=1_000_000, positions=positions) == 141_000_000


# -- get_position --


def test_get_position_found():
    """Lookup returns matching position."""
    positions = [
        {"asset_id": "SPY", "quantity": 100, "mark_price": 500000},
        {"asset_id": "AAPL", "quantity": 50, "mark_price": 1800000},
    ]
    result = get_position(positions, "SPY")
    assert result is not None
    assert result["asset_id"] == "SPY"
    assert result["quantity"] == 100


def test_get_position_not_found():
    """Lookup returns None for missing asset."""
    positions = [
        {"asset_id": "SPY", "quantity": 100, "mark_price": 500000},
    ]
    assert get_position(positions, "TSLA") is None


def test_get_position_empty():
    """Lookup in empty list returns None."""
    assert get_position([], "SPY") is None


# -- apply_trade --

# Test portfolio: $100 (1,000,000 bp) cash, 100 SPY @ $50 (500,000 bp), 50 AAPL @ $180 (1,800,000 bp)
# Portfolio value = 1,000,000 + 50,000,000 + 90,000,000 = 141,000,000 bp
_TEST_POSITIONS = [
    {"asset_id": "SPY", "quantity": 100, "mark_price": 500000},
    {"asset_id": "AAPL", "quantity": 50, "mark_price": 1800000},
]
_TEST_CASH = 1_000_000


def test_apply_trade_buy_more_existing():
    """Buy 10 more SPY at market price — quantity increases, NAV drops by fee."""
    result = apply_trade(
        cash=_TEST_CASH,
        positions=_TEST_POSITIONS,
        asset_id="SPY",
        delta_quantity=10,
        execution_price=500000,
        fee=100000,
    )
    assert result["portfolio_value"] == 140_900_000  # portfolio value − fee
    assert result["cash"] == -4_100_000  # 1M − (10×500k + 100k)
    spy = next(p for p in result["positions"] if p["asset_id"] == "SPY")
    assert spy["quantity"] == 110


def test_apply_trade_open_new_position():
    """Buy TSLA (new position) at zero fee — NAV unchanged."""
    result = apply_trade(
        cash=_TEST_CASH,
        positions=_TEST_POSITIONS,
        asset_id="TSLA",
        delta_quantity=20,
        execution_price=2000000,
        fee=0,
    )
    assert result["portfolio_value"] == 141_000_000  # unchanged (zero fee)
    assert result["cash"] == -39_000_000  # 1M − 20×2M
    tsla = next(
        (p for p in result["positions"] if p["asset_id"] == "TSLA"), None
    )
    assert tsla is not None
    assert tsla["quantity"] == 20


def test_apply_trade_close_position():
    """Sell all AAPL — position removed, NAV drops by fee only."""
    result = apply_trade(
        cash=_TEST_CASH,
        positions=_TEST_POSITIONS,
        asset_id="AAPL",
        delta_quantity=-50,
        execution_price=1800000,
        fee=50000,
    )
    assert result["portfolio_value"] == 140_950_000  # 141M − 50k fee
    assert result["cash"] == 90_950_000  # 1M + 90M − 50k fee
    aapl = next(
        (p for p in result["positions"] if p["asset_id"] == "AAPL"), None
    )
    assert aapl is None  # position fully removed


def test_apply_trade_cash_debit():
    """Cash is debited by exactly deltaQuantity * executionPrice + fee."""
    result = apply_trade(
        cash=10_000_000,
        positions=[],
        asset_id="SPY",
        delta_quantity=5,
        execution_price=600000,
        fee=200000,
    )
    expected_cash = 10_000_000 - (5 * 600_000 + 200_000)
    assert result["cash"] == expected_cash


def test_apply_trade_self_financing():
    """At-market trade: portfolio value changes only by the fee (self-financing property)."""
    initial_pv = portfolio_value(cash=_TEST_CASH, positions=_TEST_POSITIONS)
    fee = 75_000
    result = apply_trade(
        cash=_TEST_CASH,
        positions=_TEST_POSITIONS,
        asset_id="SPY",
        delta_quantity=5,
        execution_price=500000,  # at-market price
        fee=fee,
    )
    assert result["portfolio_value"] == initial_pv - fee


# -- Lean kernel FFI verification --


@pytest.mark.skipif(not HAS_LEAN_FFI, reason="Cython extension not built")
def test_portfolio_value_via_lean_ffi():
    """Verify that portfolio_value is routed through the compiled Lean kernel.

    When the Cython extension is present, hedge_engine.ffi imports from it
    rather than the pure-Python stubs. This test confirms we are exercising
    the real Lean FFI path.
    """
    import hedge_engine.ffi as ffi_mod

    # The portfolio_value function should come from the Cython extension, not stubs.
    assert ffi_mod.portfolio_value.__module__ == "hedge_engine.ffi.lean_ffi", (
        "portfolio_value is not from the Cython extension — pure-Python stubs may still be active"
    )
    # Functional check: same answer as stubs for a simple case.
    result = portfolio_value(cash=1_000_000, positions=[])
    assert result == 1_000_000
