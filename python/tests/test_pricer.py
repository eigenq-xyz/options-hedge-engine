"""Pricer tests against DerivaGem / Hull reference values.

All expected prices and deltas come from Hull "Options, Futures, and Other
Derivatives" 11th ed. and are verifiable in DG400a Black-Scholes sheets.

Tolerances:
- Price: abs=0.01  (one cent)
- Delta: abs=0.001 (0.1 percentage point)
"""

import math

import pytest

from hedge_engine.pricer.black_scholes import (
    BSGreeks,
    BSPrice,
    bs_greeks,
    bs_price,
)
from hedge_engine.pricer.conventions import from_bp, to_bp

# ---------------------------------------------------------------------------
# Conventions
# ---------------------------------------------------------------------------


class TestConventions:
    def test_to_bp_round_trip(self) -> None:
        assert from_bp(to_bp(1.2345)) == pytest.approx(1.2345, abs=1e-4)

    def test_to_bp_rounding(self) -> None:
        # $50.00  → 500,000 bp
        assert to_bp(50.0) == 500_000
        # $4.76   → 47,600 bp
        assert to_bp(4.76) == 47_600
        # $0.8075 → 8,075 bp  (rounded half-even by Python's built-in round)
        assert to_bp(0.8075) in (8_075, 8_076)  # both acceptable

    def test_from_bp(self) -> None:
        assert from_bp(500_000) == pytest.approx(50.0)
        assert from_bp(47_600) == pytest.approx(4.76)


# ---------------------------------------------------------------------------
# DerivaGem / Hull reference vectors
# ---------------------------------------------------------------------------


class TestBSPrice:
    """Black-Scholes prices vs. DerivaGem reference values."""

    def test_hull_ex15_6_call(self) -> None:
        """Hull Example 15.6: S=42, K=40, T=0.5yr, r=10%, σ=20%, call → 4.76."""
        result = bs_price(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="call"
        )
        assert isinstance(result, BSPrice)
        assert result.value == pytest.approx(4.76, abs=0.01)

    def test_hull_ex15_6_put(self) -> None:
        """Hull Example 15.6: same params, put → 0.81."""
        result = bs_price(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="put"
        )
        assert result.value == pytest.approx(0.81, abs=0.01)

    def test_atm_call(self) -> None:
        """ATM call: S=100, K=100, T=1yr, r=5%, σ=20% → ~10.45."""
        result = bs_price(
            S=100, K=100, T=1.0, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.value == pytest.approx(10.45, abs=0.01)

    def test_deep_itm_call(self) -> None:
        """Deep ITM call: S=120, K=100, T=0.5yr, r=5%, σ=20% → ~22.95 (DG400a verified)."""
        result = bs_price(
            S=120, K=100, T=0.5, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.value == pytest.approx(22.95, abs=0.01)

    def test_near_expiry_call(self) -> None:
        """Near-expiry call: S=105, K=100, T=1/365, no NaN, positive value."""
        result = bs_price(
            S=105, K=100, T=1 / 365, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.value > 0
        assert not math.isnan(result.value)
        assert not math.isinf(result.value)

    def test_put_call_parity(self) -> None:
        """Put-call parity: C - P = S·e^{-qT} - K·e^{-rT} (no dividends: q=0)."""
        S, K, T, r, sigma = 42.0, 40.0, 0.5, 0.10, 0.20
        call = bs_price(S=S, K=K, T=T, r=r, sigma=sigma, option_type="call")
        put = bs_price(S=S, K=K, T=T, r=r, sigma=sigma, option_type="put")
        lhs = call.value - put.value
        rhs = S - K * math.exp(-r * T)
        assert lhs == pytest.approx(rhs, abs=1e-8)

    def test_value_bp_is_to_bp_of_value(self) -> None:
        """value_bp must equal to_bp(value) exactly."""
        result = bs_price(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="call"
        )
        assert result.value_bp == to_bp(result.value)

    def test_intrinsic_at_expiry_call(self) -> None:
        """T ≤ 0: return intrinsic value (no time value)."""
        result = bs_price(
            S=55, K=50, T=0.0, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.value == pytest.approx(5.0, abs=1e-9)

    def test_intrinsic_at_expiry_otm(self) -> None:
        """T ≤ 0, OTM: value is 0."""
        result = bs_price(
            S=45, K=50, T=0.0, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.value == pytest.approx(0.0, abs=1e-9)


class TestBSGreeks:
    """Black-Scholes delta vs. DerivaGem reference values."""

    def test_hull_ex15_6_call_delta(self) -> None:
        """Hull Example 15.6: call delta ≈ 0.7791."""
        result = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="call"
        )
        assert isinstance(result, BSGreeks)
        assert result.delta == pytest.approx(0.7791, abs=0.001)

    def test_hull_ex15_6_put_delta(self) -> None:
        """Hull Example 15.6: put delta ≈ −0.2209."""
        result = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="put"
        )
        assert result.delta == pytest.approx(-0.2209, abs=0.001)

    def test_atm_call_delta(self) -> None:
        """ATM call: S=100, K=100, T=1yr, r=5%, σ=20% → delta ≈ 0.6368."""
        result = bs_greeks(
            S=100, K=100, T=1.0, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.delta == pytest.approx(0.6368, abs=0.001)

    def test_deep_itm_call_delta(self) -> None:
        """Deep ITM call: S=120, K=100, T=0.5yr, r=5%, σ=20% → delta ≈ 0.9378 (DG400a verified)."""
        result = bs_greeks(
            S=120, K=100, T=0.5, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.delta == pytest.approx(0.9378, abs=0.001)

    def test_call_put_delta_relationship(self) -> None:
        """Call delta - put delta = 1 (put-call parity on delta, no dividends)."""
        call = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="call"
        )
        put = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="put"
        )
        assert call.delta - put.delta == pytest.approx(1.0, abs=1e-10)

    def test_gamma_positive(self) -> None:
        """Gamma is always positive for long options."""
        result = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="call"
        )
        assert result.gamma > 0

    def test_call_put_gamma_equal(self) -> None:
        """Call and put have identical gamma (put-call parity)."""
        call = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="call"
        )
        put = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="put"
        )
        assert call.gamma == pytest.approx(put.gamma, rel=1e-10)

    def test_delta_bounds_call(self) -> None:
        """Call delta is in (0, 1)."""
        result = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="call"
        )
        assert 0 < result.delta < 1

    def test_delta_bounds_put(self) -> None:
        """Put delta is in (−1, 0)."""
        result = bs_greeks(
            S=42, K=40, T=0.5, r=0.10, sigma=0.20, option_type="put"
        )
        assert -1 < result.delta < 0

    def test_expired_call_itm_delta(self) -> None:
        """Expired ITM call has delta = 1."""
        result = bs_greeks(
            S=55, K=50, T=0.0, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.delta == pytest.approx(1.0)

    def test_expired_call_otm_delta(self) -> None:
        """Expired OTM call has delta = 0."""
        result = bs_greeks(
            S=45, K=50, T=0.0, r=0.05, sigma=0.20, option_type="call"
        )
        assert result.delta == pytest.approx(0.0)
