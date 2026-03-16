"""Black-Scholes pricing and Greeks for European options.

This module is an "advanced ETL" step: it takes raw market inputs (floats),
computes prices and Greeks as floats, and exposes `value_bp` — the integer
basis-point form that crosses the FFI boundary into the Lean kernel.

All computation stays in Python/scipy; Lean never touches floats.
"""

import math
from dataclasses import dataclass
from typing import Literal

from scipy.stats import norm

from hedge_engine.pricer.conventions import to_bp

OptionType = Literal["call", "put"]


@dataclass(frozen=True)
class BSPrice:
    """Black-Scholes option price.

    `value` is the dollar float; `value_bp` is `to_bp(value)` — the only
    form that is passed to the Lean kernel.
    """

    value: float
    value_bp: int


@dataclass(frozen=True)
class BSGreeks:
    """First-order Black-Scholes Greeks."""

    delta: float
    gamma: float
    vega: float
    theta: float
    rho: float


def _d1_d2(
    S: float, K: float, T: float, r: float, sigma: float
) -> tuple[float, float]:
    """Compute d₁ and d₂.  Caller ensures T > 0, S > 0, K > 0, sigma > 0."""
    log_sk = math.log(S / K)
    vol_sqrt_t = sigma * math.sqrt(T)
    d1 = (log_sk + (r + 0.5 * sigma**2) * T) / vol_sqrt_t
    d2 = d1 - vol_sqrt_t
    return d1, d2


def bs_price(
    S: float,
    K: float,
    T: float,
    r: float,
    sigma: float,
    option_type: OptionType,
) -> BSPrice:
    """Compute the Black-Scholes price for a European option.

    Args:
        S: Current underlying spot price (dollars).
        K: Strike price (dollars).
        T: Time to expiry in years.  If T ≤ 0 the intrinsic value is returned.
        r: Continuously compounded risk-free rate (annualised).
        sigma: Implied volatility (annualised).
        option_type: ``"call"`` or ``"put"``.

    Returns:
        :class:`BSPrice` with `value` (float) and `value_bp` (int, basis points).
    """
    assert S > 0, f"spot price must be positive, got {S}"
    assert K > 0, f"strike must be positive, got {K}"
    assert sigma > 0, f"volatility must be positive, got {sigma}"

    if T <= 0:
        # At or past expiry: return intrinsic value
        intrinsic = (
            max(S - K, 0.0) if option_type == "call" else max(K - S, 0.0)
        )
        return BSPrice(value=intrinsic, value_bp=to_bp(intrinsic))

    d1, d2 = _d1_d2(S, K, T, r, sigma)
    discount = math.exp(-r * T)

    if option_type == "call":
        value = S * norm.cdf(d1) - K * discount * norm.cdf(d2)
    else:
        value = K * discount * norm.cdf(-d2) - S * norm.cdf(-d1)

    return BSPrice(value=value, value_bp=to_bp(value))


def bs_greeks(
    S: float,
    K: float,
    T: float,
    r: float,
    sigma: float,
    option_type: OptionType,
) -> BSGreeks:
    """Compute first-order Black-Scholes Greeks for a European option.

    Args:
        S: Current underlying spot price (dollars).
        K: Strike price (dollars).
        T: Time to expiry in years.  If T ≤ 0 Greeks are returned as 0 / ±1.
        r: Continuously compounded risk-free rate (annualised).
        sigma: Implied volatility (annualised).
        option_type: ``"call"`` or ``"put"``.

    Returns:
        :class:`BSGreeks` with delta, gamma, vega, theta, rho.
    """
    assert S > 0, f"spot price must be positive, got {S}"
    assert K > 0, f"strike must be positive, got {K}"
    assert sigma > 0, f"volatility must be positive, got {sigma}"

    if T <= 0:
        if option_type == "call":
            delta = 1.0 if S > K else 0.0
        else:
            delta = -1.0 if S < K else 0.0
        return BSGreeks(delta=delta, gamma=0.0, vega=0.0, theta=0.0, rho=0.0)

    d1, d2 = _d1_d2(S, K, T, r, sigma)
    sqrt_t = math.sqrt(T)
    discount = math.exp(-r * T)
    n_d1 = norm.pdf(d1)  # standard normal PDF at d1

    gamma = n_d1 / (S * sigma * sqrt_t)
    vega = S * n_d1 * sqrt_t  # per unit of vol (not per percentage point)
    theta_call = -(S * n_d1 * sigma) / (
        2 * sqrt_t
    ) - r * K * discount * norm.cdf(d2)

    if option_type == "call":
        delta = norm.cdf(d1)
        theta = theta_call
        rho = K * T * discount * norm.cdf(d2)
    else:
        delta = norm.cdf(d1) - 1.0
        theta = theta_call + r * K * discount
        rho = -K * T * discount * norm.cdf(-d2)

    return BSGreeks(delta=delta, gamma=gamma, vega=vega, theta=theta, rho=rho)
