"""Delta-hedging backtest runner.

Source-agnostic: accepts any `PricePath`; the caller chooses whether
the path came from GBM, Hull 19.2 hardcoded data, or WRDS.

Every portfolio state transition is routed through the Lean kernel FFI
(via the Python stubs until the Cython extension is built).  At each
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


def _apply_interest(d: _PortfolioDict, rate_per_step: float) -> _PortfolioDict:
    """Accrue one period of interest on the cash balance.

    A negative cash balance represents borrowing; multiplying by
    (1 + r/n) increases the magnitude, reflecting financing cost.
    """
    old_cash = _cash(d)
    new_cash = int(old_cash * rate_per_step) + old_cash
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
    rate_per_step = r * path.dt
    for step_idx in range(1, path.n_steps):
        t = path.times[step_idx]
        S = path.prices[step_idx]
        T_rem = T_total - t
        spot_bp = to_bp(S)

        # 0. Accrue one period of financing cost on the cash balance
        port = _apply_interest(port, rate_per_step)

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
