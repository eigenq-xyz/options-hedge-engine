"""Hardcoded deterministic price paths for backtest validation.

Hull "Options, Futures, and Other Derivatives" 12th ed.:

Table 19.2 — option closes IN the money (S_T=57.25 > K=50):
    Written 100,000 European calls; cost of hedging ~$263,300

Table 19.3 — option closes OUT of the money (S_T=48.12 < K=50):
    Written 100,000 European calls; cost of hedging ~$256,600

Both scenarios: S₀=49, K=50, r=5%, σ=20%, T=20 weeks (~0.3846 yr)

These paths are deterministic and independent of any simulator; the
backtest results are reproducible without a random seed.
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


# Hull Table 19.3 week-by-week underlying prices (21 values: week 0..20)
# Source: Hull "Options, Futures, and Other Derivatives" 12th ed., Table 19.3
# Option closes out of the money (S_T=48.12 < K=50); cost of hedging = $256,600
_HULL_193_PRICES: list[float] = [
    49.00,  # week 0  — initial
    49.75,  # week 1
    52.00,  # week 2
    50.00,  # week 3
    48.38,  # week 4
    48.25,  # week 5
    48.75,  # week 6
    49.63,  # week 7
    48.25,  # week 8
    48.25,  # week 9
    51.12,  # week 10
    51.50,  # week 11
    49.88,  # week 12
    49.88,  # week 13
    48.75,  # week 14
    47.50,  # week 15
    48.00,  # week 16
    46.25,  # week 17
    48.13,  # week 18
    46.63,  # week 19
    48.12,  # week 20 — expiry
]


def hull_193_path() -> PricePath:
    """Return the Hull Table 19.3 price path (OTM expiry).

    Times are in years; 21 entries (week 0 through week 20).
    """
    n = len(_HULL_193_PRICES) - 1  # 20 steps
    times = [i / _WEEKS_PER_YEAR for i in range(n + 1)]
    return PricePath(times=times, prices=list(_HULL_193_PRICES))


# Scenario parameters (used by tests and runner)
HULL_192_K = 50.0  # strike
HULL_192_R = 0.05  # risk-free rate (annualised)
HULL_192_SIGMA = 0.20  # implied volatility (annualised)
HULL_192_N_CONTRACTS = 100_000  # written call contracts (100 per contract)
# Expected total hedging cost from Hull Table 19.2 ($)
HULL_192_EXPECTED_COST = 263_300.0
HULL_192_COST_TOLERANCE = 0.03  # ±3%

# Table 19.3 shares the same option parameters as 19.2
HULL_193_K = HULL_192_K
HULL_193_R = HULL_192_R
HULL_193_SIGMA = HULL_192_SIGMA
HULL_193_N_CONTRACTS = HULL_192_N_CONTRACTS
# Expected total hedging cost from Hull Table 19.3 ($)
HULL_193_EXPECTED_COST = 256_600.0
HULL_193_COST_TOLERANCE = 0.03  # ±3%

# --- Short straddle scenario (Hull 19.2 path, ATM straddle) ----------------
# Uses the Hull 19.2 price path with a written straddle (short call + short put)
# at K=50.  S₀=49 is near ATM; the call expires ITM (S_T=57.25 > K=50) and
# the put expires OTM.  This scenario demonstrates portfolio-level delta
# hedging with net delta ≈ 0 initially and growing as the spot moves.
STRADDLE_K = 50.0
STRADDLE_R = 0.05
STRADDLE_SIGMA = 0.20
STRADDLE_N_CONTRACTS = 100_000  # written contracts per leg
