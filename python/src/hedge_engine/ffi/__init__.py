"""FFI module for calling Lean 4 accounting kernel from Python."""

__all__ = ["initialize_lean", "calc_nav_portfolio"]

try:
    from .lean_ffi import calc_nav_portfolio, initialize_lean  # type: ignore[import-untyped]
except ImportError:
    # Cython extension not built yet - provide stubs
    def initialize_lean() -> None:
        """Stub: Lean runtime initialization."""

    def calc_nav_portfolio(cash: int, positions: list) -> int:  # type: ignore[type-arg]
        """Stub: NAV calculation (Cython extension not compiled)."""
        return int(cash + sum(p["quantity"] * p["mark_price"] for p in positions))
