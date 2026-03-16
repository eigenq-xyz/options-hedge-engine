"""Geometric Brownian Motion price path simulator.

This is one of several possible sources of a `PricePath`; the backtest
runner accepts any `PricePath` regardless of origin (GBM, Hull hardcoded,
WRDS, etc.).
"""

import numpy as np
from numpy.random import Generator

from hedge_engine.backtest.data_types import PricePath


def simulate_gbm(
    S0: float,
    mu: float,
    sigma: float,
    T: float,
    n_steps: int,
    seed: int | None = None,
) -> PricePath:
    """Simulate a single GBM price path.

    Args:
        S0: Initial spot price (dollars).
        mu: Drift (annualised, e.g. risk-free rate for risk-neutral).
        sigma: Volatility (annualised).
        T: Total time horizon in years.
        n_steps: Number of time steps.
        seed: Optional RNG seed for reproducibility.

    Returns:
        :class:`PricePath` with ``n_steps + 1`` prices (including S0).
    """
    rng: Generator = np.random.default_rng(seed)
    dt = T / n_steps
    z = rng.standard_normal(n_steps)

    # Exact GBM discretisation (no Euler bias)
    log_returns = (mu - 0.5 * sigma**2) * dt + sigma * np.sqrt(dt) * z
    prices = np.empty(n_steps + 1)
    prices[0] = S0
    np.exp(log_returns, out=prices[1:])
    np.cumprod(prices[1:], out=prices[1:])
    prices[1:] *= S0

    times = np.linspace(0.0, T, n_steps + 1)
    return PricePath(times=times.tolist(), prices=prices.tolist())
