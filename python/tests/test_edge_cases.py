"""Edge case tests for the delta-hedging backtest.

Covers settlement and pricing scenarios at the boundaries of
normal operation:

- Deep ITM settlement (S_T=80, K=50): exercises ITM ``applyTrade`` path
- Deep OTM settlement (S_T=20, K=50): exercises OTM abandonment path
- Near-expiry (T_rem < 1 day): delta approaches 0 or 1, no NaN
- Zero-quantity MTM: ``delta_quantity=0`` on a zero position leaves PV
  unchanged (``valueUpdateFormula`` with pre_trade_qty=0 gives ΔPV=0)
"""

import math

import pytest

from hedge_engine.backtest.data_types import PricePath
from hedge_engine.backtest.runner import run_delta_hedge
from hedge_engine.ffi import apply_trade
from hedge_engine.pricer.black_scholes import bs_greeks
from hedge_engine.pricer.conventions import to_bp

# ── Shared fixtures ────────────────────────────────────────────────────────

_K = 50.0
_R = 0.05
_SIGMA = 0.20
_N_CONTRACTS = 1_000  # small N for speed


def _short_path(prices: list[float], n_weeks: int) -> PricePath:
    """Build a minimal price path from a list of prices."""
    assert len(prices) == n_weeks + 1
    times = [w / 52.0 for w in range(n_weeks + 1)]
    return PricePath(times=times, prices=prices)


# ── Deep ITM settlement ────────────────────────────────────────────────────


class TestDeepITMSettlement:
    """Option expires deep in-the-money: S_T=80 >> K=50.

    Exercises the ITM settlement path (``applyTrade`` at payoff price).
    The option writer suffers a large loss; hedging cost should be positive
    and finite.
    """

    _PATH = _short_path([49.0, 65.0, 80.0], n_weeks=2)

    def test_all_certificates_pass(self) -> None:
        """All step certificates hold for a deep-ITM path."""
        result = run_delta_hedge(
            path=self._PATH,
            K=_K,
            r=_R,
            sigma=_SIGMA,
            n_contracts=_N_CONTRACTS,
        )
        failures = [c for c in result.certificates if not c.invariant_holds]
        assert failures == [], f"{len(failures)} certificate(s) failed"

    def test_cost_positive_and_finite(self) -> None:
        """Hedging cost is a finite positive number."""
        result = run_delta_hedge(
            path=self._PATH,
            K=_K,
            r=_R,
            sigma=_SIGMA,
            n_contracts=_N_CONTRACTS,
        )
        assert isinstance(result.total_hedging_cost, float)
        assert not math.isnan(result.total_hedging_cost)
        assert not math.isinf(result.total_hedging_cost)
        assert result.total_hedging_cost > 0


# ── Deep OTM settlement ────────────────────────────────────────────────────


class TestDeepOTMSettlement:
    """Option expires deep out-of-the-money: S_T=20 << K=50.

    Exercises the OTM abandonment path (position erased, cash unchanged).
    The option expires worthless; the writer retains the premium minus
    hedging costs.
    """

    _PATH = _short_path([49.0, 35.0, 20.0], n_weeks=2)

    def test_all_certificates_pass(self) -> None:
        """All step certificates hold for a deep-OTM path."""
        result = run_delta_hedge(
            path=self._PATH,
            K=_K,
            r=_R,
            sigma=_SIGMA,
            n_contracts=_N_CONTRACTS,
        )
        failures = [c for c in result.certificates if not c.invariant_holds]
        assert failures == [], f"{len(failures)} certificate(s) failed"

    def test_cost_finite(self) -> None:
        """Hedging cost is a finite number (premium retained minus costs)."""
        result = run_delta_hedge(
            path=self._PATH,
            K=_K,
            r=_R,
            sigma=_SIGMA,
            n_contracts=_N_CONTRACTS,
        )
        assert isinstance(result.total_hedging_cost, float)
        assert not math.isnan(result.total_hedging_cost)
        assert not math.isinf(result.total_hedging_cost)


# ── Near-expiry ────────────────────────────────────────────────────────────


class TestNearExpiry:
    """T_rem < 1 day: delta approaches 0 or 1, no NaN or Inf produced.

    Validates that the Black-Scholes pricer handles very small time-to-expiry
    without producing degenerate values — important because the last
    rebalancing step often has T_rem of order 1/365.
    """

    _HALF_DAY = 0.5 / 365.0

    def test_deep_itm_near_expiry_delta_near_one(self) -> None:
        """Deep ITM + near expiry: delta → 1, no NaN."""
        g = bs_greeks(
            S=70.0,
            K=50.0,
            T=self._HALF_DAY,
            r=_R,
            sigma=_SIGMA,
            option_type="call",
        )
        assert not math.isnan(g.delta)
        assert not math.isinf(g.delta)
        assert g.delta > 0.99

    def test_deep_otm_near_expiry_delta_near_zero(self) -> None:
        """Deep OTM + near expiry: delta → 0, no NaN."""
        g = bs_greeks(
            S=30.0,
            K=50.0,
            T=self._HALF_DAY,
            r=_R,
            sigma=_SIGMA,
            option_type="call",
        )
        assert not math.isnan(g.delta)
        assert not math.isinf(g.delta)
        assert g.delta < 0.01

    def test_run_completes_near_expiry(self) -> None:
        """Runner completes a path whose last step has T_rem ≈ half a day."""
        # 3 rebalancing steps in 0.5 weeks → final T_rem ≈ 0.5/52 / 3
        T = 0.5 / 52
        n = 3
        times = [i * T / n for i in range(n + 1)]
        prices = [49.0, 50.0, 51.0, 52.0]
        path = PricePath(times=times, prices=prices)
        result = run_delta_hedge(
            path=path,
            K=_K,
            r=_R,
            sigma=_SIGMA,
            n_contracts=_N_CONTRACTS,
        )
        assert not math.isnan(result.total_hedging_cost)
        assert not math.isinf(result.total_hedging_cost)
        failures = [c for c in result.certificates if not c.invariant_holds]
        assert failures == []


# ── Zero-quantity mark-to-market ───────────────────────────────────────────


class TestZeroQtyMTM:
    """``delta_quantity=0`` on an empty position leaves PV unchanged.

    ``valueUpdateFormula``:  ΔPV = pre_trade_qty × (exec − mark) − fee
    When ``pre_trade_qty = 0`` (no existing position) and ``fee = 0``:
        ΔPV = 0  →  portfolio value is unchanged.

    This is the mechanism used by the runner to mark the option position
    to market each period (issuing a zero-delta trade updates the stored
    mark price without affecting the PV — PV changes only because the
    formula uses the *pre-trade* quantity, which for a short position is
    nonzero).  This test verifies the degenerate case (truly zero position).
    """

    def test_zero_position_zero_delta_trade_leaves_pv_unchanged(self) -> None:
        """Zero-qty trade on empty portfolio: PV unchanged, no position added."""
        initial_cash_bp = to_bp(1_000.0)
        exec_price_bp = to_bp(2.50)

        port = apply_trade(
            cash=initial_cash_bp,
            positions=[],  # no existing positions
            asset_id="CALL",
            delta_quantity=0,
            execution_price=exec_price_bp,
            fee=0,
        )

        # No position created (qty stays 0 → erased per WellFormed invariant)
        assert port["positions"] == []
        # Cash unchanged (delta_qty=0, fee=0 → new_cash = old_cash)
        assert port["cash"] == initial_cash_bp
        # PV unchanged (cash + no positions)
        assert port["portfolio_value"] == initial_cash_bp

    def test_zero_delta_trade_with_fee_deducts_cash(self) -> None:
        """A zero-qty trade with a nonzero fee still deducts cash correctly."""
        initial_cash_bp = to_bp(1_000.0)
        fee_bp = to_bp(0.01)  # 1 cent fee

        port = apply_trade(
            cash=initial_cash_bp,
            positions=[],
            asset_id="CALL",
            delta_quantity=0,
            execution_price=to_bp(2.50),
            fee=fee_bp,
        )

        assert int(port["cash"]) == pytest.approx(
            initial_cash_bp - fee_bp, abs=1
        )
