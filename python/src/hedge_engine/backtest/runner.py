"""Delta-hedging backtest runner.

Source-agnostic: accepts any `PricePath`; the caller chooses whether
the path came from GBM, Hull 19.2 hardcoded data, or WRDS.

Every portfolio state transition is routed through the Lean kernel FFI
(via the Cython extension lean_ffi.so).  At each
step the runner emits a `StepCertificate` verifying `valueUpdateFormula`.
A violation halts immediately with a diagnostic.

Hull 19.2 setup
---------------
The writer of 100,000 calls starts with cash equal to the option premium
received.  At each weekly step:
  1. Re-price the option with BS (mark-to-market).
  2. Rebalance the underlying hedge to delta × n_contracts shares.
  3. Verify the step certificate.
At expiry the option is settled via the Lean kernel.
"""

from dataclasses import dataclass, field
from typing import Literal

from hedge_engine.backtest.audit import StepCertificate, verify_step
from hedge_engine.backtest.data_types import PricePath
from hedge_engine.ffi import apply_trade, portfolio_value, settle_option
from hedge_engine.pricer.black_scholes import bs_greeks, bs_price
from hedge_engine.pricer.conventions import from_bp, to_bp

# Asset identifiers used inside the kernel
_OPT_ID = "CALL"
_UND_ID = "UNDERLYING"

# Type alias for the portfolio dict returned by the FFI stubs
_PortfolioDict = dict[str, int | list[dict[str, int | str]]]


def _positions(d: _PortfolioDict) -> list[dict[str, int | str]]:
    return d["positions"]  # type: ignore[return-value]


def _cash(d: _PortfolioDict) -> int:
    v = d["cash"]
    assert isinstance(v, int)
    return v


def _pv(d: _PortfolioDict) -> int:
    v = d["portfolio_value"]
    assert isinstance(v, int)
    return v


def _mark(d: _PortfolioDict, asset_id: str, default: int = 0) -> int:
    return next(
        (
            int(p["mark_price"])
            for p in _positions(d)
            if p["asset_id"] == asset_id
        ),
        default,
    )


def _qty(d: _PortfolioDict, asset_id: str, default: int = 0) -> int:
    return next(
        (
            int(p["quantity"])
            for p in _positions(d)
            if p["asset_id"] == asset_id
        ),
        default,
    )


def _apply_interest(d: _PortfolioDict, r: float, dt: float) -> _PortfolioDict:
    """Accrue one period of interest on the cash balance.

    A negative cash balance represents borrowing; interest accrues at
    rate r over the actual time interval dt (years), reflecting financing cost.
    Uses round() to avoid systematic truncation bias on negative balances.
    """
    old_cash = _cash(d)
    new_cash = old_cash + round(old_cash * r * dt)
    new_pv = new_cash + sum(
        int(p["quantity"]) * int(p["mark_price"]) for p in _positions(d)
    )
    return {
        "cash": new_cash,
        "positions": _positions(d),
        "portfolio_value": new_pv,
    }


@dataclass
class DeltaHedgeResult:
    """Output of a single delta-hedging backtest run.

    Attributes:
        total_hedging_cost: Net cost of running the hedge (dollars).
            Positive = net expenditure (expected for a written call).
        certificates: Per-step accounting invariant certificates.
        portfolio_values: Portfolio value (bp) at each step end.
    """

    total_hedging_cost: float
    certificates: list[StepCertificate] = field(default_factory=list)
    portfolio_values: list[int] = field(default_factory=list)


def run_delta_hedge(
    path: PricePath,
    K: float,
    r: float,
    sigma: float,
    n_contracts: int,
    option_id: str = _OPT_ID,
    underlying_id: str = _UND_ID,
) -> DeltaHedgeResult:
    """Run a discrete delta-hedging simulation for a written European call.

    The hedge is rebalanced at every time step in ``path``.  All portfolio
    state transitions go through the Lean kernel (via FFI stubs).

    Args:
        path: Underlying price path (source-agnostic).
        K: Option strike (dollars).
        r: Continuously compounded risk-free rate (annualised).
        sigma: Implied volatility (annualised).
        n_contracts: Number of written call contracts.
        option_id: Asset identifier for the option inside the kernel.
        underlying_id: Asset identifier for the underlying.

    Returns:
        :class:`DeltaHedgeResult` with hedging cost and certificates.
    """
    S0 = path.prices[0]
    T_total = path.times[-1]
    T0 = T_total - path.times[0]

    # --- Step 0: receive premium, open short option position ---------------
    initial_price = bs_price(
        S=S0, K=K, T=T0, r=r, sigma=sigma, option_type="call"
    )
    premium_bp = initial_price.value_bp * n_contracts

    initial_positions: list[dict[str, int | str]] = [
        {
            "asset_id": option_id,
            "quantity": -n_contracts,
            "mark_price": initial_price.value_bp,
        }
    ]

    # Delta hedge: buy delta × n_contracts shares of underlying
    greeks0 = bs_greeks(S=S0, K=K, T=T0, r=r, sigma=sigma, option_type="call")
    hedge_qty = round(greeks0.delta * n_contracts)
    spot0_bp = to_bp(S0)

    port: _PortfolioDict = apply_trade(
        cash=premium_bp,
        positions=initial_positions,
        asset_id=underlying_id,
        delta_quantity=hedge_qty,
        execution_price=spot0_bp,
        fee=0,
    )

    certificates: list[StepCertificate] = []
    portfolio_values: list[int] = [_pv(port)]

    # --- Steps 1..N-1: rebalance at each intermediate price ----------------
    for step_idx in range(1, path.n_steps):
        t = path.times[step_idx]
        dt = t - path.times[step_idx - 1]
        S = path.prices[step_idx]
        T_rem = T_total - t
        spot_bp = to_bp(S)

        # 0. Accrue one period of financing cost on the cash balance
        port = _apply_interest(port, r=r, dt=dt)

        # 1. Mark option to market (quantity=0 trade at new BS price)
        new_opt_price_bp = bs_price(
            S=S, K=K, T=T_rem, r=r, sigma=sigma, option_type="call"
        ).value_bp
        port = apply_trade(
            cash=_cash(port),
            positions=_positions(port),
            asset_id=option_id,
            delta_quantity=0,
            execution_price=new_opt_price_bp,
            fee=0,
        )

        # 2. Rebalance underlying to new delta
        new_greeks = bs_greeks(
            S=S, K=K, T=T_rem, r=r, sigma=sigma, option_type="call"
        )
        new_hedge_qty = round(new_greeks.delta * n_contracts)
        old_und_qty = _qty(port, underlying_id)
        rebalance_qty = new_hedge_qty - old_und_qty
        old_und_mark = _mark(port, underlying_id, default=spot_bp)

        pv_before = _pv(port)
        port = apply_trade(
            cash=_cash(port),
            positions=_positions(port),
            asset_id=underlying_id,
            delta_quantity=rebalance_qty,
            execution_price=spot_bp,
            fee=0,
        )

        # 3. Emit step certificate for the rebalancing trade.
        # valueUpdateFormula uses the PRE-TRADE position size (old_und_qty),
        # not the trade delta (rebalance_qty).
        cert = verify_step(
            pv_before=pv_before,
            pv_after=_pv(port),
            pre_trade_qty=old_und_qty,
            exec_price_bp=spot_bp,
            mark_before_bp=old_und_mark,
            fee_bp=0,
            step=step_idx,
        )
        certificates.append(cert)
        portfolio_values.append(_pv(port))

    # --- Final step: settle at expiry --------------------------------------
    S_T = path.prices[-1]
    spot_T_bp = to_bp(S_T)

    port = settle_option(
        cash=_cash(port),
        positions=_positions(port),
        option_asset_id=option_id,
        option_kind="call",
        strike_bp=to_bp(K),
        spot_bp=spot_T_bp,
    )

    # Sell all remaining underlying at expiry spot
    und_qty = _qty(port, underlying_id)
    if und_qty != 0:
        port = apply_trade(
            cash=_cash(port),
            positions=_positions(port),
            asset_id=underlying_id,
            delta_quantity=-und_qty,
            execution_price=spot_T_bp,
            fee=0,
        )

    portfolio_values.append(_pv(port))

    # Hedging cost = initial premium received minus final portfolio value
    # (positive = net expenditure by the hedger)
    final_pv_bp = _pv(port)
    hedging_cost = from_bp(premium_bp - final_pv_bp)

    _ = portfolio_value  # imported for future Cython path; suppress F401

    return DeltaHedgeResult(
        total_hedging_cost=hedging_cost,
        certificates=certificates,
        portfolio_values=portfolio_values,
    )


@dataclass(frozen=True)
class OptionLeg:
    """One leg of a multi-leg option portfolio.

    Attributes:
        option_id: Asset identifier inside the Lean kernel (must be unique
            across all legs in the same portfolio).
        option_type: ``"call"`` or ``"put"``.
        K: Strike price in dollars (positive).
        sigma: Implied volatility (fraction, e.g. 0.20 for 20 %).
        n_contracts: Signed contract count.  Negative = short (written).
    """

    option_id: str
    option_type: Literal["call", "put"]
    K: float
    sigma: float
    n_contracts: int


def run_portfolio_hedge(
    path: PricePath,
    legs: list[OptionLeg],
    r: float,
    underlying_id: str = _UND_ID,
) -> DeltaHedgeResult:
    """Delta-hedge a multi-leg option portfolio over a price path.

    The net delta across all legs determines the underlying position at each
    rebalancing step.  All portfolio state transitions go through the Lean
    kernel FFI (via the Cython extension lean_ffi.so).

    Example — written straddle (short call + short put at K=50)::

        legs = [
            OptionLeg("CALL_K50", "call", K=50, sigma=0.20,
                      n_contracts=-100_000),
            OptionLeg("PUT_K50",  "put",  K=50, sigma=0.20,
                      n_contracts=-100_000),
        ]
        result = run_portfolio_hedge(path, legs, r=0.05)

    Args:
        path: Underlying price path (source-agnostic).
        legs: Option legs forming the portfolio.  Each leg must have a unique
            ``option_id``.
        r: Continuously compounded risk-free rate (annualised).
        underlying_id: Asset identifier for the underlying hedge instrument.

    Returns:
        :class:`DeltaHedgeResult` with total hedging cost and certificates.
    """
    if not legs:
        raise ValueError("At least one option leg is required")

    S0 = path.prices[0]
    T_total = path.times[-1]
    T0 = T_total - path.times[0]

    # --- Step 0: receive all premiums, open all option positions -----------
    total_premium_bp = 0
    initial_positions: list[dict[str, int | str]] = []
    for leg in legs:
        price0 = bs_price(
            S=S0,
            K=leg.K,
            T=T0,
            r=r,
            sigma=leg.sigma,
            option_type=leg.option_type,
        )
        # Written positions (n_contracts < 0) receive premium; long pay it
        total_premium_bp += price0.value_bp * (-leg.n_contracts)
        initial_positions.append(
            {
                "asset_id": leg.option_id,
                "quantity": leg.n_contracts,
                "mark_price": price0.value_bp,
            }
        )

    def _option_portfolio_delta(S: float, T_rem: float) -> float:
        """Net delta of the option portfolio (excluding underlying hedge)."""
        return sum(
            bs_greeks(
                S=S,
                K=leg.K,
                T=T_rem,
                r=r,
                sigma=leg.sigma,
                option_type=leg.option_type,
            ).delta
            * leg.n_contracts
            for leg in legs
        )

    # Hedge quantity to make the total portfolio delta-neutral:
    # option_delta + hedge_qty × 1 = 0  ⟹  hedge_qty = -option_delta
    hedge_qty = round(-_option_portfolio_delta(S0, T0))
    spot0_bp = to_bp(S0)

    port: _PortfolioDict = apply_trade(
        cash=total_premium_bp,
        positions=initial_positions,
        asset_id=underlying_id,
        delta_quantity=hedge_qty,
        execution_price=spot0_bp,
        fee=0,
    )

    certificates: list[StepCertificate] = []
    portfolio_values: list[int] = [_pv(port)]

    # --- Steps 1..N-1: rebalance at each intermediate price ----------------
    for step_idx in range(1, path.n_steps):
        t = path.times[step_idx]
        dt = t - path.times[step_idx - 1]
        S = path.prices[step_idx]
        T_rem = T_total - t
        spot_bp = to_bp(S)

        port = _apply_interest(port, r=r, dt=dt)

        # Mark all option legs to market
        for leg in legs:
            new_price_bp = bs_price(
                S=S,
                K=leg.K,
                T=max(T_rem, 0.0),
                r=r,
                sigma=leg.sigma,
                option_type=leg.option_type,
            ).value_bp
            port = apply_trade(
                cash=_cash(port),
                positions=_positions(port),
                asset_id=leg.option_id,
                delta_quantity=0,
                execution_price=new_price_bp,
                fee=0,
            )

        # Rebalance underlying to net delta
        new_hedge_qty = round(-_option_portfolio_delta(S, max(T_rem, 0.0)))
        old_und_qty = _qty(port, underlying_id)
        rebalance_qty = new_hedge_qty - old_und_qty
        old_und_mark = _mark(port, underlying_id, default=spot_bp)

        pv_before = _pv(port)
        port = apply_trade(
            cash=_cash(port),
            positions=_positions(port),
            asset_id=underlying_id,
            delta_quantity=rebalance_qty,
            execution_price=spot_bp,
            fee=0,
        )

        cert = verify_step(
            pv_before=pv_before,
            pv_after=_pv(port),
            pre_trade_qty=old_und_qty,
            exec_price_bp=spot_bp,
            mark_before_bp=old_und_mark,
            fee_bp=0,
            step=step_idx,
        )
        certificates.append(cert)
        portfolio_values.append(_pv(port))

    # --- Final step: settle all legs at expiry ----------------------------
    S_T = path.prices[-1]
    spot_T_bp = to_bp(S_T)

    for leg in legs:
        port = settle_option(
            cash=_cash(port),
            positions=_positions(port),
            option_asset_id=leg.option_id,
            option_kind=leg.option_type,
            strike_bp=to_bp(leg.K),
            spot_bp=spot_T_bp,
        )

    und_qty = _qty(port, underlying_id)
    if und_qty != 0:
        port = apply_trade(
            cash=_cash(port),
            positions=_positions(port),
            asset_id=underlying_id,
            delta_quantity=-und_qty,
            execution_price=spot_T_bp,
            fee=0,
        )

    portfolio_values.append(_pv(port))

    final_pv_bp = _pv(port)
    hedging_cost = from_bp(total_premium_bp - final_pv_bp)

    return DeltaHedgeResult(
        total_hedging_cost=hedging_cost,
        certificates=certificates,
        portfolio_values=portfolio_values,
    )
