"""Backtest integration tests.

Hull Table 19.2 gate: the discrete delta-hedging cost must be within
5% of the textbook value ($263,300).

GBM smoke test: seeded simulation produces a valid result with all
step certificates passing and a finite hedging cost.
"""

import pytest

from hedge_engine.backtest.runner import DeltaHedgeResult, run_delta_hedge
from hedge_engine.backtest.scenarios import (
    HULL_192_COST_TOLERANCE,
    HULL_192_EXPECTED_COST,
    HULL_192_K,
    HULL_192_N_CONTRACTS,
    HULL_192_R,
    HULL_192_SIGMA,
    hull_192_path,
)
from hedge_engine.simulator.gbm import simulate_gbm


class TestHull192:
    """Hull Table 19.2 deterministic gate."""

    def test_hedging_cost_within_5pct(self) -> None:
        """Delta-hedge cost matches Hull 19.2 within 5%."""
        path = hull_192_path()
        result = run_delta_hedge(
            path=path,
            K=HULL_192_K,
            r=HULL_192_R,
            sigma=HULL_192_SIGMA,
            n_contracts=HULL_192_N_CONTRACTS,
        )
        assert isinstance(result, DeltaHedgeResult)
        expected = HULL_192_EXPECTED_COST
        tol = HULL_192_COST_TOLERANCE
        assert result.total_hedging_cost == pytest.approx(expected, rel=tol), (
            f"Hedging cost {result.total_hedging_cost:.0f} is not within "
            f"{tol * 100:.0f}% of expected {expected:.0f}"
        )

    def test_all_certificates_pass(self) -> None:
        """All step certificates must report invariant_holds=True."""
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


class TestGBMSmoke:
    """GBM simulator + runner smoke test (seeded, runs in CI)."""

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
        assert isinstance(result.total_hedging_cost, float)
        import math

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
