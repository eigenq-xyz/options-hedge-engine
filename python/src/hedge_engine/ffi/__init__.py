"""FFI module for calling Lean 4 accounting kernel from Python.

Exports match the Lean @[export hedge_*] functions in Accounting.lean.
Until the Cython extension is built, Python stubs replicate the logic.
"""

__all__ = [
    "initialize_lean",
    "calc_nav",
    "position_value",
    "sum_position_values",
    "get_position",
    "apply_trade",
]

try:
    from .lean_ffi import (  # type: ignore[import-untyped]
        apply_trade,
        calc_nav,
        get_position,
        initialize_lean,
        position_value,
        sum_position_values,
    )
except ImportError:
    # Cython extension not built yet — provide pure-Python stubs.
    # All monetary values are in basis points (×10,000).

    def initialize_lean() -> None:
        """Stub: Lean runtime initialization (no-op)."""

    def position_value(quantity: int, mark_price: int) -> int:
        """Stub for hedge_position_value: quantity × markPrice."""
        return quantity * mark_price

    def sum_position_values(positions: list[dict[str, int]]) -> int:
        """Stub for hedge_sum_position_values: sum of position values."""
        return sum(p["quantity"] * p["mark_price"] for p in positions)

    def calc_nav(cash: int, positions: list[dict[str, int]]) -> int:
        """Stub for hedge_portfolio_nav: cash + sum of position values."""
        return int(cash + sum_position_values(positions))

    def get_position(
        positions: list[dict[str, int | str]], asset_id: str
    ) -> dict[str, int | str] | None:
        """Stub for hedge_get_position: lookup by asset ID."""
        for p in positions:
            if p["asset_id"] == asset_id:
                return p
        return None

    def apply_trade(
        cash: int,
        positions: list[dict[str, int | str]],
        asset_id: str,
        delta_quantity: int,
        execution_price: int,
        fee: int,
    ) -> dict[str, int | list[dict[str, int | str]]]:
        """Stub for hedge_apply_trade: apply a trade to a portfolio.

        Returns {"cash": int, "positions": list[dict], "nav": int}.
        Mirrors applyTrade semantics from Basic.lean exactly.
        """
        old_qty = next((int(p["quantity"]) for p in positions if p["asset_id"] == asset_id), 0)
        new_qty = old_qty + delta_quantity
        new_cash = cash - (delta_quantity * execution_price + fee)
        stripped = [p for p in positions if p["asset_id"] != asset_id]
        if new_qty == 0:
            new_positions: list[dict[str, int | str]] = list(stripped)
        else:
            new_positions = stripped + [
                {"asset_id": asset_id, "quantity": new_qty, "mark_price": execution_price}
            ]
        nav = new_cash + sum(int(p["quantity"]) * int(p["mark_price"]) for p in new_positions)
        return {"cash": new_cash, "positions": new_positions, "nav": nav}
