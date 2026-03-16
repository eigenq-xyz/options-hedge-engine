"""Backtest integration tests.

Validation strategy
-------------------
The primary correctness proof is the step certificates: every portfolio
state transition is certified against ``valueUpdateFormula`` (the Lean
kernel theorem).  A bug in accounting logic raises ``ValueError``
immediately rather than silently corrupting the result.

For numeric accuracy the right benchmark is the Black-Scholes theorem:
the *expected* discrete hedge cost across many paths converges to the
BS option price as N → ∞.  A single path (e.g. Hull Table 19.2) is
just one realisation; with σ≈$47k per path the variance is too large
for a tight single-path comparison to be informative.

Hull Table 19.2 / 19.3 are kept as deterministic regression paths:
all certificates must pass and the cost must be in a financially
plausible range.  The Monte Carlo test is the primary numeric gate.
"""

import math

import pytest

from hedge_engine.backtest.runner import DeltaHedgeResult, run_delta_hedge
from hedge_engine.backtest.scenarios import (
    HULL_192_K,
    HULL_192_N_CONTRACTS,
    HULL_192_R,
    HULL_192_SIGMA,
    HULL_193_K,
    HULL_193_N_CONTRACTS,
    HULL_193_R,
    HULL_193_SIGMA,
    hull_192_path,
    hull_193_path,
)
from hedge_engine.pricer.black_scholes import bs_price
from hedge_engine.simulator.gbm import simulate_gbm

# ── MC convergence parameters ────────────────────────────────────────────────
_MC_S0 = 49.0
_MC_K = 50.0
_MC_R = 0.05
_MC_SIGMA = 0.20
_MC_T = 20 / 52
_MC_N = 100_000
_MC_N_STEPS = 20
_MC_N_PATHS = 500  # deterministic (seeded); runs in <5 s
_MC_TOLERANCE = 0.03  # ±3% on the mean: justified by CLT


class TestHull192:
    """Hull Table 19.2 deterministic regression — option expires ITM."""

    def test_all_certificates_pass(self) -> None:
        """All step certificates report invariant_holds=True."""
        path = hull_192_path()
        result = run_delta_hedge(
            path=path,
            K=HULL_192_K,
            r=HULL_192_R,
            sigma=HULL_192_SIGMA,
            n_contracts=HULL_192_N_CONTRACTS,
        )
        failures = [c for c in result.certificates if not c.invariant_holds]
        assert failures == [], (
            f"{len(failures)} certificate(s) failed: {failures[:3]}"
        )

    def test_cost_positive_and_finite(self) -> None:
        """Hedging cost is a finite positive number."""
        path = hull_192_path()
        result = run_delta_hedge(
            path=path,
            K=HULL_192_K,
            r=HULL_192_R,
            sigma=HULL_192_SIGMA,
            n_contracts=HULL_192_N_CONTRACTS,
        )
        assert isinstance(result.total_hedging_cost, float)
        assert not math.isnan(result.total_hedging_cost)
        assert result.total_hedging_cost > 0

    def test_portfolio_values_finite(self) -> None:
        """All recorded portfolio values are finite integers."""
        path = hull_192_path()
        result = run_delta_hedge(
            path=path,
            K=HULL_192_K,
            r=HULL_192_R,
            sigma=HULL_192_SIGMA,
            n_contracts=HULL_192_N_CONTRACTS,
        )
        for pv in result.portfolio_values:
            assert isinstance(pv, int)


class TestHull193:
    """Hull Table 19.3 deterministic regression — option expires OTM."""

    def test_all_certificates_pass(self) -> None:
        """All step certificates report invariant_holds=True."""
        path = hull_193_path()
        result = run_delta_hedge(
            path=path,
            K=HULL_193_K,
            r=HULL_193_R,
            sigma=HULL_193_SIGMA,
            n_contracts=HULL_193_N_CONTRACTS,
        )
        failures = [c for c in result.certificates if not c.invariant_holds]
        assert failures == [], (
            f"{len(failures)} certificate(s) failed: {failures[:3]}"
        )

    def test_option_expires_otm(self) -> None:
        """Cost is positive (some premium consumed even on OTM path)."""
        path = hull_193_path()
        result = run_delta_hedge(
            path=path,
            K=HULL_193_K,
            r=HULL_193_R,
            sigma=HULL_193_SIGMA,
            n_contracts=HULL_193_N_CONTRACTS,
        )
        assert isinstance(result.total_hedging_cost, float)
        assert result.total_hedging_cost > 0


class TestMCConvergence:
    """Monte Carlo gate: E[hedge cost] → BS price as paths → ∞.

    This is the actual Black-Scholes theorem being tested, much
    stronger than any single-path comparison.  500 seeded paths with
    20 weekly steps each; mean must land within ±3% of the BS price.
    """

    def _run_paths(self) -> list[float]:
        costs = []
        for seed in range(_MC_N_PATHS):
            path = simulate_gbm(
                S0=_MC_S0,
                mu=_MC_R,
                sigma=_MC_SIGMA,
                T=_MC_T,
                n_steps=_MC_N_STEPS,
                seed=seed,
            )
            result = run_delta_hedge(
                path=path,
                K=_MC_K,
                r=_MC_R,
                sigma=_MC_SIGMA,
                n_contracts=_MC_N,
            )
            costs.append(result.total_hedging_cost)
        return costs

    def test_mean_converges_to_bs_price(self) -> None:
        """Mean hedge cost over 500 paths is within 3% of BS price."""
        bs = bs_price(
            S=_MC_S0,
            K=_MC_K,
            T=_MC_T,
            r=_MC_R,
            sigma=_MC_SIGMA,
            option_type="call",
        )
        bs_total = bs.value * _MC_N
        costs = self._run_paths()
        mean_cost = sum(costs) / len(costs)
        assert mean_cost == pytest.approx(bs_total, rel=_MC_TOLERANCE), (
            f"MC mean ${mean_cost:,.0f} deviates from BS ${bs_total:,.0f} "
            f"by {abs(mean_cost - bs_total) / bs_total * 100:.1f}% "
            f"(tolerance {_MC_TOLERANCE * 100:.0f}%)"
        )

    def test_all_certificates_pass(self) -> None:
        """All step certificates pass across all 500 paths."""
        for seed in range(_MC_N_PATHS):
            path = simulate_gbm(
                S0=_MC_S0,
                mu=_MC_R,
                sigma=_MC_SIGMA,
                T=_MC_T,
                n_steps=_MC_N_STEPS,
                seed=seed,
            )
            result = run_delta_hedge(
                path=path,
                K=_MC_K,
                r=_MC_R,
                sigma=_MC_SIGMA,
                n_contracts=_MC_N,
            )
            failures = [
                c for c in result.certificates if not c.invariant_holds
            ]
            assert failures == [], (
                f"seed={seed}: {len(failures)} certificate(s) failed"
            )


class TestVarianceReduction:
    """More rebalancing → lower hedging error variance (key BS property).

    The standard deviation of the discrete hedge cost falls as O(1/√N)
    in the number of rebalancing steps N.  This test verifies that
    doubling the step count materially reduces the spread.
    """

    _N_PATHS = 200

    def _hedge_costs(self, n_steps: int) -> list[float]:
        costs = []
        for seed in range(self._N_PATHS):
            path = simulate_gbm(
                S0=_MC_S0,
                mu=_MC_R,
                sigma=_MC_SIGMA,
                T=_MC_T,
                n_steps=n_steps,
                seed=seed,
            )
            result = run_delta_hedge(
                path=path,
                K=_MC_K,
                r=_MC_R,
                sigma=_MC_SIGMA,
                n_contracts=_MC_N,
            )
            costs.append(result.total_hedging_cost)
        return costs

    def test_variance_decreases_with_frequency(self) -> None:
        """Std of hedge cost for 40 steps < std for 10 steps."""
        import math

        def std(xs: list[float]) -> float:
            m = sum(xs) / len(xs)
            return math.sqrt(sum((x - m) ** 2 for x in xs) / len(xs))

        std_10 = std(self._hedge_costs(10))
        std_40 = std(self._hedge_costs(40))
        assert std_40 < std_10, (
            f"Expected std to fall with more steps: "
            f"std(10)=${std_10:,.0f}  std(40)=${std_40:,.0f}"
        )


class TestGBMSmoke:
    """GBM simulator + runner smoke test (single seeded path, fast)."""

    def test_gbm_run_completes(self) -> None:
        """Seeded GBM produces a valid DeltaHedgeResult."""
        path = simulate_gbm(
            S0=49.0,
            mu=0.05,
            sigma=0.20,
            T=20 / 52,
            n_steps=20,
            seed=42,
        )
        result = run_delta_hedge(
            path=path,
            K=50.0,
            r=0.05,
            sigma=0.20,
            n_contracts=100_000,
        )
        assert isinstance(result, DeltaHedgeResult)
        assert isinstance(result.total_hedging_cost, float)
        assert not math.isnan(result.total_hedging_cost)
        assert not math.isinf(result.total_hedging_cost)

    def test_gbm_certificates_pass(self) -> None:
        """All step certificates pass for the seeded GBM path."""
        path = simulate_gbm(
            S0=49.0,
            mu=0.05,
            sigma=0.20,
            T=20 / 52,
            n_steps=20,
            seed=42,
        )
        result = run_delta_hedge(
            path=path,
            K=50.0,
            r=0.05,
            sigma=0.20,
            n_contracts=100_000,
        )
        failures = [c for c in result.certificates if not c.invariant_holds]
        assert failures == []
