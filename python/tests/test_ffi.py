"""
Test FFI bindings to Lean accounting kernel.

These tests verify that:
1. Cython extension compiles and loads
2. Lean runtime initializes without crashing
3. Basic function calls work (stub implementations for now)
"""

import pytest

from hedge_engine.ffi import calc_nav_stub, initialize_lean


def test_lean_runtime_initialization():
    """Test that Lean runtime initializes successfully."""
    # Should not raise
    initialize_lean()


def test_calc_nav_stub():
    """Test calc_nav stub function (marshalling not implemented yet)."""
    result = calc_nav_stub()
    assert isinstance(result, int)
    assert result == 0  # Stub implementation returns 0


@pytest.mark.skip(reason="Portfolio marshalling not implemented yet")
def test_calc_nav_with_portfolio():
    """
    Future test: Calculate NAV for real portfolio.

    Requires implementing Portfolio/Position marshalling between Python and Lean.
    This is the next step after basic FFI infrastructure works.
    """
    pass
