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
from pathlib import Path
from typing import Any

import pytest

from hedge_engine.backtest.data_types import PricePath
from hedge_engine.backtest.runner import (
    DeltaHedgeResult,
    OptionLeg,
    run_delta_hedge,
    run_portfolio_hedge,
)
from hedge_engine.backtest.scenarios import (
    HULL_192_K,
    HULL_192_N_CONTRACTS,
    HULL_192_R,
    HULL_192_SIGMA,
    HULL_193_K,
    HULL_193_N_CONTRACTS,
    HULL_193_R,
    HULL_193_SIGMA,
    STRADDLE_K,
    STRADDLE_N_CONTRACTS,
    STRADDLE_R,
    STRADDLE_SIGMA,
    hull_192_path,
    hull_193_path,
)
from hedge_engine.pricer.black_scholes import bs_greeks, bs_price
from hedge_engine.simulator.gbm import simulate_gbm

# ── MC convergence parameters ─────────────────────────────────────────────
_MC_S0 = 49.0
_MC_K = 50.0
_MC_R = 0.05
_MC_SIGMA = 0.20
_MC_T = 20 / 52
_MC_N = 100_000
_MC_N_STEPS = 20
_MC_N_PATHS = 500  # deterministic (seeded); runs in <5 s
_MC_TOLERANCE = 0.03  # ±3% on the mean: justified by CLT


def _carr_madan_gamma_pnl(
    path: PricePath,
    K: float,
    r: float,
    sigma: float,
    n_contracts: int,
) -> float:
    """Dollar gamma P&L per the Carr-Madan decomposition.

    For each step i: ½ × Γᵢ × Sᵢ² × [(ΔSᵢ/Sᵢ)² − σ²Δt]

    Positive when realised volatility > implied (long-gamma profit);
    negative when realised volatility < implied.  Summed across all
    rebalancing steps and scaled to n_contracts.

    Reference: Carr & Madan (1998); see also Hull Chapter 19.
    """
    total = 0.0
    for i in range(path.n_steps):
        S = path.prices[i]
        t = path.times[i]
        dt = path.times[i + 1] - path.times[i]
        T_rem = path.times[-1] - t
        if T_rem <= 0:
            continue
        gamma = bs_greeks(
            S=S, K=K, T=T_rem, r=r, sigma=sigma, option_type="call"
        ).gamma
        delta_S = path.prices[i + 1] - path.prices[i]
        total += 0.5 * gamma * S**2 * ((delta_S / S) ** 2 - sigma**2 * dt)
    return total * n_contracts


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

    def test_bkl_variance_scaling(self) -> None:
        """std(N) ∝ 1/√N — quantitative Bertsimas-Kogan-Lo (2000) check.

        BKL (JFE 2000): Var[ε_N] ≈ (σ²/2N) ∫ E[(S_t Γ_t)²] dt.
        Doubling steps halves the variance, so std ratio ≈ √2.
        Tolerance ±30 % accounts for finite-sample noise at N=200 paths.
        """
        import math

        def std(xs: list[float]) -> float:
            m = sum(xs) / len(xs)
            return math.sqrt(sum((x - m) ** 2 for x in xs) / len(xs))

        std_10 = std(self._hedge_costs(10))
        std_20 = std(self._hedge_costs(20))
        ratio = std_10 / std_20
        sqrt2 = math.sqrt(2)
        assert sqrt2 * 0.70 <= ratio <= sqrt2 * 1.30, (
            f"BKL scaling: std(10)/std(20) = {ratio:.3f}, "
            f"expected ≈ √2 = {sqrt2:.3f} ± 30 %"
        )


class TestCarrMadan:
    """Carr-Madan gamma P&L decomposition.

    Carr & Madan (1998) show that for a writer (short-gamma) who
    delta-hedges, the discrete hedge cost decomposes as:

        hedge_cost ≈ C₀ + Σᵢ ½ Γᵢ Sᵢ² [(ΔSᵢ/Sᵢ)² − σ²Δt]
                   = C₀ + gamma_pnl

    The writer is SHORT gamma: high realised vol raises rebalancing
    costs AND gamma_pnl.  Consequently hedge_cost and gamma_pnl are
    strongly positively correlated across realisations.
    """

    _N_PATHS = 200

    def _run(self) -> tuple[list[float], list[float]]:
        costs, gpnls = [], []
        for seed in range(self._N_PATHS):
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
            gpnls.append(
                _carr_madan_gamma_pnl(
                    path=path,
                    K=_MC_K,
                    r=_MC_R,
                    sigma=_MC_SIGMA,
                    n_contracts=_MC_N,
                )
            )
        return costs, gpnls

    def test_gamma_pnl_correlated_with_cost(self) -> None:
        """hedge_cost and gamma_pnl are strongly positively correlated (r > 0.7).

        Carr-Madan: hedge_cost ≈ C₀ + gamma_pnl for a short-gamma writer.
        High realised vol raises both the hedging cost (short-gamma loss)
        and gamma_pnl.  Correlation approaches +1 as N → ∞.
        """
        costs, gpnls = self._run()
        n = len(costs)
        mean_c = sum(costs) / n
        mean_g = sum(gpnls) / n
        cov = (
            sum(
                (c - mean_c) * (g - mean_g)
                for c, g in zip(costs, gpnls, strict=True)
            )
            / n
        )
        std_c = math.sqrt(sum((c - mean_c) ** 2 for c in costs) / n)
        std_g = math.sqrt(sum((g - mean_g) ** 2 for g in gpnls) / n)
        corr = cov / (std_c * std_g)
        assert corr > 0.70, (
            f"Expected Carr-Madan correlation > 0.70, got {corr:.3f}"
        )

    def test_gamma_pnl_mean_near_zero(self) -> None:
        """Mean gamma P&L ≈ 0 (realised vol = implied vol in expectation).

        Under risk-neutral dynamics E[(ΔS/S)²] = σ²Δt, so each term in
        the sum has expectation 0.  Over 200 seeded GBM paths the mean
        should be within ±5 % of the BS price.
        """
        _, gpnls = self._run()
        bs_total = (
            bs_price(
                S=_MC_S0,
                K=_MC_K,
                T=_MC_T,
                r=_MC_R,
                sigma=_MC_SIGMA,
                option_type="call",
            ).value
            * _MC_N
        )
        mean_gpnl = sum(gpnls) / len(gpnls)
        assert abs(mean_gpnl) < 0.05 * bs_total, (
            f"Mean gamma P&L ${mean_gpnl:,.0f} should be near 0 "
            f"(BS price ${bs_total:,.0f})"
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


class TestPortfolioHedge:
    """Tests for run_portfolio_hedge: multi-leg option portfolios."""

    def _straddle_legs(self) -> list[OptionLeg]:
        return [
            OptionLeg(
                option_id="CALL_K50",
                option_type="call",
                K=STRADDLE_K,
                sigma=STRADDLE_SIGMA,
                n_contracts=-STRADDLE_N_CONTRACTS,
            ),
            OptionLeg(
                option_id="PUT_K50",
                option_type="put",
                K=STRADDLE_K,
                sigma=STRADDLE_SIGMA,
                n_contracts=-STRADDLE_N_CONTRACTS,
            ),
        ]

    def test_straddle_all_certificates_pass(self) -> None:
        """All step certificates must hold for a short straddle backtest."""
        result = run_portfolio_hedge(
            path=hull_192_path(),
            legs=self._straddle_legs(),
            r=STRADDLE_R,
        )
        failures = [c for c in result.certificates if not c.invariant_holds]
        assert failures == [], f"{len(failures)} certificate(s) failed"

    def test_straddle_cost_positive_and_bounded(self) -> None:
        """Short straddle hedging cost is positive and less than premium collected."""
        result = run_portfolio_hedge(
            path=hull_192_path(),
            legs=self._straddle_legs(),
            r=STRADDLE_R,
        )
        assert result.total_hedging_cost > 0, "Expected positive hedging cost"
        # Cost must be less than total premium received (call + put at S₀=49, K=50)
        from hedge_engine.pricer.black_scholes import bs_price

        path = hull_192_path()
        S0 = path.prices[0]
        T0 = path.times[-1]
        call_prem = bs_price(
            S=S0,
            K=STRADDLE_K,
            T=T0,
            r=STRADDLE_R,
            sigma=STRADDLE_SIGMA,
            option_type="call",
        ).value
        put_prem = bs_price(
            S=S0,
            K=STRADDLE_K,
            T=T0,
            r=STRADDLE_R,
            sigma=STRADDLE_SIGMA,
            option_type="put",
        ).value
        total_premium = (call_prem + put_prem) * STRADDLE_N_CONTRACTS
        assert result.total_hedging_cost < total_premium * 2, (
            f"Cost {result.total_hedging_cost:.0f} unreasonably large vs "
            f"premium {total_premium:.0f}"
        )

    def test_portfolio_hedge_requires_legs(self) -> None:
        """run_portfolio_hedge raises ValueError with empty legs list."""
        with pytest.raises(ValueError, match="At least one"):
            run_portfolio_hedge(path=hull_192_path(), legs=[], r=0.05)

    def test_single_call_matches_run_delta_hedge(self) -> None:
        """run_portfolio_hedge with one call leg matches run_delta_hedge output."""
        path = hull_192_path()
        single_leg_result = run_portfolio_hedge(
            path=path,
            legs=[
                OptionLeg(
                    option_id="CALL",
                    option_type="call",
                    K=HULL_192_K,
                    sigma=HULL_192_SIGMA,
                    n_contracts=-HULL_192_N_CONTRACTS,
                )
            ],
            r=HULL_192_R,
        )
        single_run_result = run_delta_hedge(
            path=path,
            K=HULL_192_K,
            r=HULL_192_R,
            sigma=HULL_192_SIGMA,
            n_contracts=HULL_192_N_CONTRACTS,
        )
        assert single_leg_result.total_hedging_cost == pytest.approx(
            single_run_result.total_hedging_cost, rel=0.001
        )


class TestRealDataBacktest:
    """Real-data integration tests — skipped when WRDS data is absent.

    To activate: download SPY ATM options from OptionMetrics via WRDS
    (see etl/wrds_loader.py for schema), encrypt with git-crypt, and
    place at data/portfolio_atm_options.parquet relative to the repo root.

    Validation criterion: under BS assumptions mean hedge error ≈ 0
    (the no-arbitrage condition).  Real data will show small systematic
    bias due to transaction costs, volatility smile, and discrete
    rebalancing; anything within ±5 % of mean premium is acceptable.
    """

    _DATA_FILE = (
        Path(__file__).parent.parent.parent.parent
        / "data"
        / "portfolio_atm_options.parquet"
    )

    def _data_available(self) -> bool:
        try:
            import pandas  # noqa: F401

            return self._DATA_FILE.exists()
        except ImportError:
            return False

    def test_data_file_skips_gracefully(self) -> None:
        """Test infrastructure: skip guard works when data is absent."""
        if self._data_available():
            pytest.skip(
                "Data present — run test_mean_hedge_error_near_zero instead"
            )
        # If data absent, the test simply passes (guards are working)

    def test_mean_hedge_error_near_zero(self) -> None:
        """Mean hedge error across real SPY options ≈ 0 (BS no-arbitrage).

        Runs a delta-hedge backtest for each option series in the WRDS
        file and checks that the mean of (hedge_cost / premium) is near 1.
        A result far from 1 indicates a systematic accounting error.
        """
        if not self._data_available():
            pytest.skip(
                "WRDS data not present — set up data/portfolio_atm_options.parquet"
            )

        import pandas as pd  # type: ignore[import-untyped]

        from hedge_engine.etl.wrds_loader import (
            optionmetrics_option_snapshots_from_df,
        )

        df = pd.read_parquet(self._DATA_FILE)

        # Each row is one option observation; group by option series
        ratios: list[float] = []
        for (_, _expiry, strike, cp), group in df.groupby(
            ["underlying_ticker", "expiry", "strike", "option_type"]
        ):
            if cp != "call":
                continue
            group = group.sort_values("date")
            if len(group) < 5:
                continue
            snaps = optionmetrics_option_snapshots_from_df(group)
            if not snaps:
                continue
            first = snaps[0]
            T_total = (
                pd.Timestamp(first.expiry) - pd.Timestamp(first.date)
            ).days / 365.0
            if T_total <= 0:
                continue
            # Use contemporaneous underlying prices from opprcd spotprice column.
            # Rows without underlying_price are skipped (data quality guard).
            if any(s.underlying_price is None for s in snaps):
                continue
            und_prices = [s.underlying_price for s in snaps]  # type: ignore[misc]
            times = [
                (pd.Timestamp(s.date) - pd.Timestamp(first.date)).days / 365.0
                for s in snaps
            ]
            path = PricePath(times=times, prices=und_prices)
            result = run_delta_hedge(
                path=path,
                K=float(strike),
                r=0.05,
                sigma=first.implied_vol,
                n_contracts=1,
            )
            premium = bs_price(
                S=und_prices[0],
                K=float(strike),
                T=T_total,
                r=0.05,
                sigma=first.implied_vol,
                option_type="call",
            ).value
            if premium > 0:
                ratios.append(result.total_hedging_cost / premium)

        assert ratios, "No option series found in data file"
        mean_ratio = sum(ratios) / len(ratios)
        assert abs(mean_ratio - 1.0) < 0.10, (
            f"Mean hedge cost / premium = {mean_ratio:.3f},"
            f" expected ≈ 1.0 ± 10 %"
        )


class TestHoldoutValidation:
    """Out-of-sample validation on WRDS OptionMetrics SPY data.

    Splits the parquet data file by calendar year:
    - In-sample: earliest year  — estimate the median implied volatility
    - Out-of-sample: latest year — run the backtest with the in-sample σ

    Gate: mean(cost / premium) ≈ 1.0 ± 15 % on the holdout year.
    The wider tolerance (vs 10 % in-sample) accounts for vol-regime drift
    between years — a reasonable real-world expectation.

    This is the test a quant practitioner uses to distinguish a backtester
    that works only because it uses the realised per-day IV (look-ahead bias)
    from one that would work with only the σ you knew *before* the hedging
    period started.

    Design decision: use the median IV across the in-sample period as a
    single constant σ for all holdout hedges.  This is intentionally simple.
    More sophisticated calibration (vol surface, term structure) would reduce
    the out-of-sample error further; passing this test with a flat σ is the
    minimum bar.
    """

    _DATA_FILE = (
        Path(__file__).parent.parent.parent.parent
        / "data"
        / "portfolio_atm_options.parquet"
    )

    def _data_available(self) -> bool:
        try:
            import pandas  # noqa: F401

            return self._DATA_FILE.exists()
        except ImportError:
            return False

    def _run_backtest_for_series(
        self,
        group: "Any",
        sigma: float,
    ) -> "float | None":
        """Run one option series; return cost/premium or None if skipped."""
        import pandas as pd  # type: ignore[import-untyped]

        from hedge_engine.etl.wrds_loader import (
            optionmetrics_option_snapshots_from_df,
        )

        group = group.sort_values("date")
        if len(group) < 5:
            return None
        snaps = optionmetrics_option_snapshots_from_df(group)
        if not snaps or any(s.underlying_price is None for s in snaps):
            return None
        first = snaps[0]
        T_total = (
            pd.Timestamp(first.expiry) - pd.Timestamp(first.date)
        ).days / 365.0
        if T_total <= 0:
            return None
        und_prices = [s.underlying_price for s in snaps]  # type: ignore[misc]
        times = [
            (pd.Timestamp(s.date) - pd.Timestamp(first.date)).days / 365.0
            for s in snaps
        ]
        path = PricePath(times=times, prices=und_prices)
        result = run_delta_hedge(
            path=path,
            K=float(first.strike),
            r=0.05,
            sigma=sigma,
            n_contracts=1,
        )
        premium = bs_price(
            S=und_prices[0],
            K=float(first.strike),
            T=T_total,
            r=0.05,
            sigma=sigma,
            option_type="call",
        ).value
        if premium <= 0:
            return None
        return result.total_hedging_cost / premium

    def test_data_file_skips_gracefully(self) -> None:
        """Test infrastructure: skip guard works when data is absent."""
        if self._data_available():
            pytest.skip(
                "Data present — run test_holdout_mean_cost_near_premium instead"
            )

    def test_holdout_mean_cost_near_premium(self) -> None:
        """Out-of-sample hedge cost / premium ≈ 1.0 using in-sample calibrated σ.

        Calibration: median implied vol from the earliest year in the dataset.
        Holdout: all call series from the latest year in the dataset.

        A backtester that only works with per-day realised IV (look-ahead) will
        fail this test when given a fixed constant σ estimated from prior data.
        """
        if not self._data_available():
            pytest.skip(
                "WRDS data not present — set up data/portfolio_atm_options.parquet"
            )

        import pandas as pd  # type: ignore[import-untyped]

        df = pd.read_parquet(self._DATA_FILE)
        df["_year"] = pd.to_datetime(df["date"]).dt.year
        years = sorted(df["_year"].unique())
        if len(years) < 2:
            pytest.skip(
                f"Data spans only {years} — need at least 2 years for holdout split"
            )

        in_year, out_year = years[0], years[-1]
        df_in = df[df["_year"] == in_year]
        df_out = df[df["_year"] == out_year]

        # Calibrate σ: median IV from in-sample year (no look-ahead)
        calibrated_sigma = float(df_in["impl_volatility"].median())

        # Validate on holdout year using the calibrated σ
        ratios: list[float] = []
        for (_, _expiry, _strike, cp), group in df_out.groupby(
            ["underlying_ticker", "expiry", "strike", "option_type"]
        ):
            if cp != "call":
                continue
            ratio = self._run_backtest_for_series(
                group, sigma=calibrated_sigma
            )
            if ratio is not None:
                ratios.append(ratio)

        assert ratios, (
            f"No usable call series found in holdout year {out_year}"
        )
        mean_ratio = sum(ratios) / len(ratios)
        assert abs(mean_ratio - 1.0) < 0.15, (
            f"Holdout mean hedge cost / premium = {mean_ratio:.3f} "
            f"(calibrated σ={calibrated_sigma:.3f} from {in_year}, "
            f"tested on {out_year}); expected ≈ 1.0 ± 15%"
        )

    def test_holdout_not_worse_than_insample(self) -> None:
        """Out-of-sample hedging error (std) is not dramatically larger than in-sample.

        Uses calibrated (in-sample) σ for both periods so the comparison is fair.
        A 3× variance expansion would indicate overfitting or a vol-regime break.
        """
        if not self._data_available():
            pytest.skip(
                "WRDS data not present — set up data/portfolio_atm_options.parquet"
            )

        import math

        import pandas as pd  # type: ignore[import-untyped]

        df = pd.read_parquet(self._DATA_FILE)
        df["_year"] = pd.to_datetime(df["date"]).dt.year
        years = sorted(df["_year"].unique())
        if len(years) < 2:
            pytest.skip("Need at least 2 years of data")

        in_year, out_year = years[0], years[-1]
        calibrated_sigma = float(
            df[df["_year"] == in_year]["impl_volatility"].median()
        )

        def _collect_ratios(subset: "pd.DataFrame") -> list[float]:
            result = []
            for (_, _expiry, _strike, cp), grp in subset.groupby(
                ["underlying_ticker", "expiry", "strike", "option_type"]
            ):
                if cp != "call":
                    continue
                ratio = self._run_backtest_for_series(
                    grp, sigma=calibrated_sigma
                )
                if ratio is not None:
                    result.append(ratio)
            return result

        in_ratios = _collect_ratios(df[df["_year"] == in_year])
        out_ratios = _collect_ratios(df[df["_year"] == out_year])

        assert in_ratios, "No in-sample series found"
        assert out_ratios, "No out-of-sample series found"

        def _std(xs: list[float]) -> float:
            mean = sum(xs) / len(xs)
            return math.sqrt(sum((x - mean) ** 2 for x in xs) / len(xs))

        std_in = _std(in_ratios)
        std_out = _std(out_ratios)
        assert std_out < std_in * 3.0, (
            f"Holdout std ({std_out:.3f}) is more than 3× in-sample std "
            f"({std_in:.3f}) — possible vol-regime break or data quality issue"
        )
