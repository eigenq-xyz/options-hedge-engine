"""Source-agnostic input type for the backtest runner."""

from dataclasses import dataclass


@dataclass(frozen=True)
class PricePath:
    """A time-indexed sequence of underlying spot prices.

    Source-agnostic: may originate from GBM simulation, hardcoded
    scenario data (Hull Table 19.2), or real market data (WRDS).

    Attributes:
        times: Time points in years (length N+1, starting at 0).
        prices: Spot prices in dollars (same length as ``times``).
    """

    times: list[float]
    prices: list[float]

    def __post_init__(self) -> None:
        if len(self.times) != len(self.prices):
            raise ValueError(
                "times and prices must have the same length, "
                f"got {len(self.times)} and {len(self.prices)}"
            )
        if len(self.times) < 2:
            raise ValueError(
                "PricePath must have at least 2 points "
                f"(got {len(self.times)})"
            )

    @property
    def n_steps(self) -> int:
        """Number of time steps (one less than number of price points)."""
        return len(self.prices) - 1

    @property
    def dt(self) -> float:
        """Time between first and last point divided by number of steps."""
        return (self.times[-1] - self.times[0]) / self.n_steps
