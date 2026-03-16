"""Numeric conventions: float ↔ basis-point integer conversion.

All monetary values that cross the FFI boundary into Lean must be integers
in basis points (×10,000).  These two functions are the only place that
conversion happens; everything else in the Python layer works in floats.
"""


def to_bp(x: float) -> int:
    """Convert a dollar amount to basis points (×10,000), rounding half-up."""
    return round(x * 10_000)


def from_bp(n: int) -> float:
    """Convert basis points back to a dollar float."""
    return n / 10_000
