"""Test FFI bindings to Lean accounting kernel."""

import pytest

from hedge_engine.ffi import calc_nav_portfolio, initialize_lean


def test_lean_runtime_initialization():
    """Test that Lean runtime initializes successfully."""
    # Should not raise
    initialize_lean()


def test_calc_nav_empty_portfolio():
    """Test NAV calculation with empty portfolio (stub implementation)."""
    nav = calc_nav_portfolio(cash=1000000, positions=[])
    assert nav == 1000000  # $100.00


def test_calc_nav_with_positions():
    """Test NAV calculation with positions (stub implementation)."""
    positions = [
        {"asset_id": "SPY", "quantity": 100, "mark_price": 500000},
        {"asset_id": "AAPL", "quantity": 50, "mark_price": 1800000},
    ]
    nav = calc_nav_portfolio(cash=1000000, positions=positions)
    expected = 1000000 + (100 * 500000) + (50 * 1800000)
    assert nav == expected


@pytest.mark.skip(reason="Cython compilation not yet implemented")
def test_calc_nav_via_lean_ffi():
    """Future: Test actual Lean FFI after Cython extension is compiled."""
    pass
