"""Hardcoded deterministic price paths for backtest validation.

Hull "Options, Futures, and Other Derivatives" 11th ed., Table 19.2:
    Written 100,000 European calls
    S₀=49, K=50, r=5%, σ=20%, T=20 weeks (~0.3846 yr)
    Expected delta-hedging cost: ~$263,300

This is the canonical multi-period validation scenario.  It is
deterministic and independent of any simulator, so the backtest result
is reproducible without a random seed.
"""

from hedge_engine.backtest.data_types import PricePath

# Hull Table 19.2 week-by-week underlying prices (21 values: week 0..20)
# Source: Hull "Options, Futures, and Other Derivatives" 12th ed., Table 19.2
# Option closes in the money (S_T=57.25 > K=50); cost of hedging = $263,300
_HULL_192_PRICES: list[float] = [
    49.00,  # week 0  — initial
    48.12,  # week 1
    47.37,  # week 2
    50.25,  # week 3
    51.75,  # week 4
    53.12,  # week 5
    53.00,  # week 6
    51.87,  # week 7
    51.38,  # week 8
    53.00,  # week 9
    49.88,  # week 10
    48.50,  # week 11
    49.88,  # week 12
    50.37,  # week 13
    52.13,  # week 14
    51.88,  # week 15
    52.87,  # week 16
    54.87,  # week 17
    54.62,  # week 18
    55.87,  # week 19
    57.25,  # week 20 — expiry
]

_WEEKS_PER_YEAR = 52.0


def hull_192_path() -> PricePath:
    """Return the Hull Table 19.2 price path.

    Times are in years; 21 entries (week 0 through week 20).
    """
    n = len(_HULL_192_PRICES) - 1  # 20 steps
    times = [i / _WEEKS_PER_YEAR for i in range(n + 1)]
    return PricePath(times=times, prices=list(_HULL_192_PRICES))


# Scenario parameters (used by tests and runner)
HULL_192_K = 50.0  # strike
HULL_192_R = 0.05  # risk-free rate (annualised)
HULL_192_SIGMA = 0.20  # implied volatility (annualised)
HULL_192_N_CONTRACTS = 100_000  # written call contracts (100 per contract)
# Expected total hedging cost from Hull Table 19.2 ($)
HULL_192_EXPECTED_COST = 263_300.0
HULL_192_COST_TOLERANCE = 0.05  # ±5%
