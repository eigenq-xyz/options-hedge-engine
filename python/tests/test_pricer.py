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


# ---------------------------------------------------------------------------
# Independent scipy reference implementation
# ---------------------------------------------------------------------------


def _ref_bs_price(
    S: float,
    K: float,
    T: float,
    r: float,
    sigma: float,
    option_type: str,
) -> float:
    """Black-Scholes price — direct scipy formula, independent of our code.

    This is the canonical formula from Hull (2022) Chapter 15, implemented
    from scratch using only scipy.stats.norm.  It has no shared code with
    ``hedge_engine.pricer.black_scholes`` and serves as an independent oracle.
    """
    from scipy.stats import norm  # type: ignore[import-untyped]

    if T <= 0:
        if option_type == "call":
            return max(S - K, 0.0)
        return max(K - S, 0.0)
    d1 = (math.log(S / K) + (r + 0.5 * sigma**2) * T) / (sigma * math.sqrt(T))
    d2 = d1 - sigma * math.sqrt(T)
    if option_type == "call":
        return float(S * norm.cdf(d1) - K * math.exp(-r * T) * norm.cdf(d2))
    return float(K * math.exp(-r * T) * norm.cdf(-d2) - S * norm.cdf(-d1))


def _ref_delta(
    S: float,
    K: float,
    T: float,
    r: float,
    sigma: float,
    option_type: str,
) -> float:
    """BS delta — direct scipy formula, independent of our code."""
    from scipy.stats import norm  # type: ignore[import-untyped]

    if T <= 0:
        if option_type == "call":
            return 1.0 if S > K else 0.0
        return -1.0 if S < K else 0.0
    d1 = (math.log(S / K) + (r + 0.5 * sigma**2) * T) / (sigma * math.sqrt(T))
    if option_type == "call":
        return float(norm.cdf(d1))
    return float(norm.cdf(d1) - 1.0)


_BENCHMARK_SCENARIOS = [
    # (S, K, T, r, sigma, option_type)  — spans ATM, ITM, OTM, long/short expiry
    (42.0, 40.0, 0.5, 0.10, 0.20, "call"),  # Hull Ex 15.6 call
    (42.0, 40.0, 0.5, 0.10, 0.20, "put"),  # Hull Ex 15.6 put
    (100.0, 100.0, 1.0, 0.05, 0.20, "call"),  # ATM call, 1yr
    (100.0, 100.0, 1.0, 0.05, 0.20, "put"),  # ATM put, 1yr
    (120.0, 100.0, 0.5, 0.05, 0.20, "call"),  # deep ITM call
    (80.0, 100.0, 0.5, 0.05, 0.20, "put"),  # deep ITM put
    (80.0, 100.0, 0.5, 0.05, 0.20, "call"),  # deep OTM call
    (120.0, 100.0, 0.5, 0.05, 0.20, "put"),  # deep OTM put
    (100.0, 100.0, 1 / 52, 0.05, 0.25, "call"),  # one-week ATM, higher vol
    (490.0, 490.0, 21 / 365, 0.05, 0.155, "call"),  # SPY-like ATM ~1mo
    (490.0, 510.0, 21 / 365, 0.05, 0.165, "call"),  # SPY-like OTM ~1mo
    (490.0, 470.0, 21 / 365, 0.05, 0.145, "put"),  # SPY-like ITM put ~1mo
]


class TestBenchmarkImplementation:
    """Cross-validate our pricer against an independent scipy reference.

    The reference functions above implement Black-Scholes from first principles
    using only ``scipy.stats.norm`` — no shared code with
    ``hedge_engine.pricer.black_scholes``.  Agreement to machine precision
    (rel=1e-6) across all scenarios confirms that our implementation is
    indistinguishable from the standard formula.

    This is the test a quant practitioner uses to establish that the pricing
    engine is correct, independent of Hull's 3dp-rounded reference tables.
    """

    @pytest.mark.parametrize("S,K,T,r,sigma,ot", _BENCHMARK_SCENARIOS)
    def test_price_matches_reference(
        self,
        S: float,
        K: float,
        T: float,
        r: float,
        sigma: float,
        ot: str,
    ) -> None:
        our = bs_price(S=S, K=K, T=T, r=r, sigma=sigma, option_type=ot).value
        ref = _ref_bs_price(S=S, K=K, T=T, r=r, sigma=sigma, option_type=ot)
        assert our == pytest.approx(ref, rel=1e-6, abs=1e-10), (
            f"Price mismatch: our={our:.8f} ref={ref:.8f} "
            f"for S={S} K={K} T={T} σ={sigma} {ot}"
        )

    @pytest.mark.parametrize("S,K,T,r,sigma,ot", _BENCHMARK_SCENARIOS)
    def test_delta_matches_reference(
        self,
        S: float,
        K: float,
        T: float,
        r: float,
        sigma: float,
        ot: str,
    ) -> None:
        our = bs_greeks(S=S, K=K, T=T, r=r, sigma=sigma, option_type=ot).delta
        ref = _ref_delta(S=S, K=K, T=T, r=r, sigma=sigma, option_type=ot)
        assert our == pytest.approx(ref, rel=1e-6, abs=1e-10), (
            f"Delta mismatch: our={our:.8f} ref={ref:.8f} "
            f"for S={S} K={K} T={T} σ={sigma} {ot}"
        )

    def test_no_scenario_produces_nan_or_inf(self) -> None:
        """None of the benchmark scenarios produce NaN or infinite values."""
        for S, K, T, r, sigma, ot in _BENCHMARK_SCENARIOS:
            p = bs_price(S=S, K=K, T=T, r=r, sigma=sigma, option_type=ot).value
            d = bs_greeks(
                S=S, K=K, T=T, r=r, sigma=sigma, option_type=ot
            ).delta
            assert math.isfinite(p), (
                f"Non-finite price for {S},{K},{T},{sigma},{ot}"
            )
            assert math.isfinite(d), (
                f"Non-finite delta for {S},{K},{T},{sigma},{ot}"
            )
