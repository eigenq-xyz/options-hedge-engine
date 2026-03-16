"""Delta-hedging backtest runner.

Source-agnostic: accepts any ``PricePath``; the caller chooses whether
the path came from GBM, Hull 19.2 hardcoded data, or WRDS.

Every portfolio state transition is routed through the Lean verified
accounting layer (via the Cython extension lean_ffi.so). At each
step the runner emits a ``StepCertificate`` verifying ``valueUpdateFormula``.
A violation halts immediately with a diagnostic.

Architecture
------------
The core loop is ``run_backtester(path, strategy)``. A ``HedgingStrategy``
encapsulates all options-specific logic: which legs to open, how to price
them, and the target delta-neutral underlying quantity at each step. This
makes it straightforward to add new strategies (delta-gamma, VRP overlay,
spread hedging) without touching the bookkeeping loop.

Built-in strategies
-------------------
- ``SingleLegStrategy``: delta-hedge for one written European option
  (replaces the old ``run_delta_hedge`` implementation)
- ``PortfolioStrategy``: delta-hedge for a multi-leg option portfolio
  (replaces the old ``run_portfolio_hedge`` implementation)

Convenience wrappers ``run_delta_hedge`` and ``run_portfolio_hedge``
preserve the original call signatures for backward compatibility.

Hull 19.2 setup
---------------
The writer of 100,000 calls starts with cash equal to the option premium
received. At each weekly step:
  1. Re-price the option with BS (mark-to-market).
  2. Rebalance the underlying hedge to delta x n_contracts shares.
  3. Verify the step certificate.
At expiry the option is settled via the Lean verified accounting layer.
"""

from dataclasses import dataclass, field
from typing import Literal, Protocol

from hedge_engine.backtest.audit import StepCertificate, verify_step
from hedge_engine.backtest.data_types import PricePath
from hedge_engine.ffi import apply_trade, settle_option
from hedge_engine.pricer.black_scholes import bs_greeks, bs_price
from hedge_engine.pricer.conventions import from_bp, to_bp

# Asset identifiers used inside the verified accounting layer
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


@dataclass(frozen=True)
class OptionLeg:
    """One leg of a multi-leg option portfolio.

    Attributes:
        option_id: Asset identifier inside the Lean verified accounting
            layer (must be unique across all legs in the same portfolio).
        option_type: ``"call"`` or ``"put"``.
        K: Strike price in dollars (positive).
        sigma: Implied volatility (fraction, e.g. 0.20 for 20 %).
        n_contracts: Signed contract count. Negative = short (written).
    """

    option_id: str
    option_type: Literal["call", "put"]
    K: float
    sigma: float
    n_contracts: int


# ---------------------------------------------------------------------------
# HedgingStrategy protocol
# ---------------------------------------------------------------------------


class HedgingStrategy(Protocol):
    """Protocol for pluggable delta-hedging strategies.

    A ``HedgingStrategy`` encapsulates all options-specific logic so that
    ``run_backtester`` can run a generic bookkeeping loop without knowing
    which options are in the portfolio. New strategies (delta-gamma, VRP
    overlay, calendar spreads, etc.) are added by implementing this protocol.

    All monetary quantities are in basis points (x10,000).
    """

    @property
    def r(self) -> float:
        """Continuously compounded risk-free rate (annualised), used for
        interest accrual between rebalancing steps."""
        ...

    def option_legs(self) -> list[OptionLeg]:
        """All option legs managed by this strategy.

        Used by ``run_backtester`` at expiry to settle each leg in order.
        """
        ...

    def initial_option_positions(
        self, S0: float, T0: float
    ) -> list[dict[str, int | str]]:
        """Initial position dicts for all legs at inception (t=0).

        Each dict has keys ``asset_id`` (str), ``quantity`` (int),
        ``mark_price`` (int, basis points).
        """
        ...

    def total_premium_bp(self, S0: float, T0: float) -> int:
        """Net premium received at inception (basis points).

        Positive for a net written portfolio (cash inflow).
        """
        ...

    def initial_hedge_qty(self, S0: float, T0: float) -> int:
        """Target underlying quantity at t=0 for a delta-neutral portfolio."""
        ...

    def mark_prices(self, S: float, T_rem: float) -> dict[str, int]:
        """Mark-to-market price in basis points for each leg.

        Returns a dict ``{option_id: price_bp}`` for every leg in the
        strategy. The runner calls ``apply_trade`` (zero-quantity) for each
        entry to update the mark price in the portfolio.
        """
        ...

    def target_hedge_qty(self, S: float, T_rem: float) -> int:
        """Target underlying quantity at the current rebalancing step."""
        ...


# ---------------------------------------------------------------------------
# Built-in strategy implementations
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SingleLegStrategy:
    """Delta-hedge strategy for one written European option.

    ``n_contracts`` is a positive integer representing the number of
    contracts written (the position is short). This matches the convention
    of the legacy ``run_delta_hedge`` wrapper.

    Implements ``HedgingStrategy``.
    """

    K: float
    r: float
    sigma: float
    n_contracts: int
    option_type: Literal["call", "put"] = "call"
    option_id: str = _OPT_ID

    def option_legs(self) -> list[OptionLeg]:
        return [
            OptionLeg(
                option_id=self.option_id,
                option_type=self.option_type,
                K=self.K,
                sigma=self.sigma,
                n_contracts=-self.n_contracts,  # signed: written = negative
            )
        ]

    def initial_option_positions(
        self, S0: float, T0: float
    ) -> list[dict[str, int | str]]:
        price_bp = bs_price(
            S=S0,
            K=self.K,
            T=T0,
            r=self.r,
            sigma=self.sigma,
            option_type=self.option_type,
        ).value_bp
        return [
            {
                "asset_id": self.option_id,
                "quantity": -self.n_contracts,
                "mark_price": price_bp,
            }
        ]

    def total_premium_bp(self, S0: float, T0: float) -> int:
        price_bp = bs_price(
            S=S0,
            K=self.K,
            T=T0,
            r=self.r,
            sigma=self.sigma,
            option_type=self.option_type,
        ).value_bp
        return price_bp * self.n_contracts

    def initial_hedge_qty(self, S0: float, T0: float) -> int:
        delta = bs_greeks(
            S=S0,
            K=self.K,
            T=T0,
            r=self.r,
            sigma=self.sigma,
            option_type=self.option_type,
        ).delta
        return round(delta * self.n_contracts)

    def mark_prices(self, S: float, T_rem: float) -> dict[str, int]:
        price_bp = bs_price(
            S=S,
            K=self.K,
            T=T_rem,
            r=self.r,
            sigma=self.sigma,
            option_type=self.option_type,
        ).value_bp
        return {self.option_id: price_bp}

    def target_hedge_qty(self, S: float, T_rem: float) -> int:
        delta = bs_greeks(
            S=S,
            K=self.K,
            T=T_rem,
            r=self.r,
            sigma=self.sigma,
            option_type=self.option_type,
        ).delta
        return round(delta * self.n_contracts)


@dataclass(frozen=True)
class PortfolioStrategy:
    """Delta-hedge strategy for a multi-leg option portfolio.

    ``legs`` is a list of :class:`OptionLeg` with signed ``n_contracts``
    (negative = written). This matches the convention of the legacy
    ``run_portfolio_hedge`` wrapper.

    The net delta across all legs determines the underlying position at
    each rebalancing step.

    Implements ``HedgingStrategy``.
    """

    legs: list[OptionLeg]
    r: float

    def option_legs(self) -> list[OptionLeg]:
        return list(self.legs)

    def initial_option_positions(
        self, S0: float, T0: float
    ) -> list[dict[str, int | str]]:
        positions: list[dict[str, int | str]] = []
        for leg in self.legs:
            price_bp = bs_price(
                S=S0,
                K=leg.K,
                T=T0,
                r=self.r,
                sigma=leg.sigma,
                option_type=leg.option_type,
            ).value_bp
            pos: dict[str, int | str] = {
                "asset_id": leg.option_id,
                "quantity": leg.n_contracts,
                "mark_price": price_bp,
            }
            positions.append(pos)
        return positions

    def total_premium_bp(self, S0: float, T0: float) -> int:
        total = 0
        for leg in self.legs:
            price_bp = bs_price(
                S=S0,
                K=leg.K,
                T=T0,
                r=self.r,
                sigma=leg.sigma,
                option_type=leg.option_type,
            ).value_bp
            total += price_bp * (-leg.n_contracts)
        return total

    def initial_hedge_qty(self, S0: float, T0: float) -> int:
        net_delta = sum(
            bs_greeks(
                S=S0,
                K=leg.K,
                T=T0,
                r=self.r,
                sigma=leg.sigma,
                option_type=leg.option_type,
            ).delta
            * leg.n_contracts
            for leg in self.legs
        )
        return round(-net_delta)

    def mark_prices(self, S: float, T_rem: float) -> dict[str, int]:
        return {
            leg.option_id: bs_price(
                S=S,
                K=leg.K,
                T=T_rem,
                r=self.r,
                sigma=leg.sigma,
                option_type=leg.option_type,
            ).value_bp
            for leg in self.legs
        }

    def target_hedge_qty(self, S: float, T_rem: float) -> int:
        net_delta = sum(
            bs_greeks(
                S=S,
                K=leg.K,
                T=T_rem,
                r=self.r,
                sigma=leg.sigma,
                option_type=leg.option_type,
            ).delta
            * leg.n_contracts
            for leg in self.legs
        )
        return round(-net_delta)


# ---------------------------------------------------------------------------
# Core backtest loop
# ---------------------------------------------------------------------------


def run_backtester(
    path: PricePath,
    strategy: HedgingStrategy,
    underlying_id: str = _UND_ID,
) -> DeltaHedgeResult:
    """Run a discrete delta-hedging backtest for any ``HedgingStrategy``.

    The loop is strategy-agnostic: it delegates all options-specific logic
    (pricing, delta computation, settlement) to the strategy object, and
    handles only portfolio bookkeeping and step-certificate emission.

    Args:
        path: Underlying price path (source-agnostic).
        strategy: A ``HedgingStrategy`` implementation that provides
            option pricing, delta computation, and settlement logic.
        underlying_id: Asset identifier for the underlying hedge instrument.

    Returns:
        :class:`DeltaHedgeResult` with hedging cost and certificates.
    """
    S0 = path.prices[0]
    T_total = path.times[-1]
    T0 = T_total - path.times[0]

    # --- Step 0: receive premiums, open all option positions ---------------
    initial_positions = strategy.initial_option_positions(S0, T0)
    premium_bp = strategy.total_premium_bp(S0, T0)
    hedge_qty = strategy.initial_hedge_qty(S0, T0)
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
        T_rem = max(T_total - t, 0.0)
        spot_bp = to_bp(S)

        # 0. Accrue financing cost on the cash balance
        port = _apply_interest(port, r=strategy.r, dt=dt)

        # 1. Mark all option legs to market
        for opt_id, price_bp in strategy.mark_prices(S, T_rem).items():
            port = apply_trade(
                cash=_cash(port),
                positions=_positions(port),
                asset_id=opt_id,
                delta_quantity=0,
                execution_price=price_bp,
                fee=0,
            )

        # 2. Rebalance underlying to new net delta
        new_hedge_qty = strategy.target_hedge_qty(S, T_rem)
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

    # --- Final step: settle all legs at expiry -----------------------------
    S_T = path.prices[-1]
    spot_T_bp = to_bp(S_T)

    for leg in strategy.option_legs():
        port = settle_option(
            cash=_cash(port),
            positions=_positions(port),
            option_asset_id=leg.option_id,
            option_kind=leg.option_type,
            strike_bp=to_bp(leg.K),
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
    hedging_cost = from_bp(premium_bp - _pv(port))

    return DeltaHedgeResult(
        total_hedging_cost=hedging_cost,
        certificates=certificates,
        portfolio_values=portfolio_values,
    )


# ---------------------------------------------------------------------------
# Backward-compatible convenience wrappers
# ---------------------------------------------------------------------------


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

    Convenience wrapper around :func:`run_backtester` with a
    :class:`SingleLegStrategy`. Preserves the original call signature.

    Args:
        path: Underlying price path (source-agnostic).
        K: Option strike (dollars).
        r: Continuously compounded risk-free rate (annualised).
        sigma: Implied volatility (annualised).
        n_contracts: Number of written call contracts (positive integer).
        option_id: Asset identifier for the option inside the accounting layer.
        underlying_id: Asset identifier for the underlying.

    Returns:
        :class:`DeltaHedgeResult` with hedging cost and certificates.
    """
    strategy = SingleLegStrategy(
        K=K,
        r=r,
        sigma=sigma,
        n_contracts=n_contracts,
        option_type="call",
        option_id=option_id,
    )
    return run_backtester(path, strategy, underlying_id)


def run_portfolio_hedge(
    path: PricePath,
    legs: list[OptionLeg],
    r: float,
    underlying_id: str = _UND_ID,
) -> DeltaHedgeResult:
    """Delta-hedge a multi-leg option portfolio over a price path.

    Convenience wrapper around :func:`run_backtester` with a
    :class:`PortfolioStrategy`. Preserves the original call signature.

    The net delta across all legs determines the underlying position at each
    rebalancing step.

    Example -- written straddle (short call + short put at K=50)::

        legs = [
            OptionLeg("CALL_K50", "call", K=50, sigma=0.20,
                      n_contracts=-100_000),
            OptionLeg("PUT_K50",  "put",  K=50, sigma=0.20,
                      n_contracts=-100_000),
        ]
        result = run_portfolio_hedge(path, legs, r=0.05)

    Args:
        path: Underlying price path (source-agnostic).
        legs: Option legs forming the portfolio. Each leg must have a unique
            ``option_id``. ``n_contracts`` is signed (negative = written).
        r: Continuously compounded risk-free rate (annualised).
        underlying_id: Asset identifier for the underlying hedge instrument.

    Returns:
        :class:`DeltaHedgeResult` with total hedging cost and certificates.
    """
    if not legs:
        raise ValueError("At least one option leg is required")
    strategy = PortfolioStrategy(legs=legs, r=r)
    return run_backtester(path, strategy, underlying_id)
