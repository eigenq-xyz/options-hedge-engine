"""Per-step invariant certificates for the backtest audit trail.

At each step the runner emits a `StepCertificate` that checks whether
`valueUpdateFormula` held for the trade applied at that step:

    ΔportfolioValue = qty × (execPrice − markBefore) − fee

A bug in accounting logic produces `invariant_holds = False` and
the runner halts with a diagnostic — not silent wrong results.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class StepCertificate:
    """Audit record for a single backtest step.

    All monetary values are in basis points (×10,000).

    Attributes:
        step: Step index (0-based).
        portfolio_value_before: Portfolio value before the trade.
        portfolio_value_after: Portfolio value after the trade.
        delta_pv: Observed change: ``after − before``.
        expected_delta_pv: Predicted by ``valueUpdateFormula``:
            ``pre_trade_qty × (exec_price − mark_before) − fee``.
            ``pre_trade_qty`` is the position size *before* the trade.
        invariant_holds: ``delta_pv == expected_delta_pv``.
    """

    step: int
    portfolio_value_before: int
    portfolio_value_after: int
    delta_pv: int
    expected_delta_pv: int
    invariant_holds: bool


def verify_step(
    pv_before: int,
    pv_after: int,
    pre_trade_qty: int,
    exec_price_bp: int,
    mark_before_bp: int,
    fee_bp: int,
    step: int,
) -> StepCertificate:
    """Compute a `StepCertificate` and check the accounting invariant.

    All monetary arguments are in basis points.

    The formula checked is Lean's ``valueUpdateFormula``:
        ΔPV = pre_trade_qty × (execPrice − markBefore) − fee

    where ``pre_trade_qty`` is the size of the position *before* the
    trade executes (not the trade delta).  For a new position this is 0,
    so only the fee affects portfolio value — consistent with the theorem.

    Args:
        pv_before: Portfolio value before the trade (bp).
        pv_after: Portfolio value after the trade (bp).
        pre_trade_qty: Signed position size before the trade.
        exec_price_bp: Execution price per unit (bp).
        mark_before_bp: Mark price of the position before the trade (bp).
        fee_bp: Transaction fee (bp, non-negative).
        step: Step index for the certificate.

    Returns:
        :class:`StepCertificate` with ``invariant_holds`` set.

    Raises:
        ValueError: If ``invariant_holds`` is ``False`` (accounting bug).
    """
    delta_pv = pv_after - pv_before
    expected = pre_trade_qty * (exec_price_bp - mark_before_bp) - fee_bp
    holds = delta_pv == expected

    cert = StepCertificate(
        step=step,
        portfolio_value_before=pv_before,
        portfolio_value_after=pv_after,
        delta_pv=delta_pv,
        expected_delta_pv=expected,
        invariant_holds=holds,
    )

    if not holds:
        raise ValueError(
            f"Accounting invariant violated at step {step}: "
            f"delta_pv={delta_pv} bp, expected={expected} bp. "
            f"Certificate: {cert}"
        )

    return cert
