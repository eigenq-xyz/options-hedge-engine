"""Tests for the per-step accounting invariant audit module."""

import pytest

from hedge_engine.backtest.audit import StepCertificate, verify_step


class TestVerifyStep:
    def test_holds_when_invariant_satisfied(self) -> None:
        """Certificate issued when delta_pv == expected.

        pre_trade_qty=10 means 10 shares were held BEFORE the trade.
        expected = 10 * (500_000 - 490_000) - 0 = 100_000
        """
        cert = verify_step(
            pv_before=1_000_000,
            pv_after=1_100_000,
            pre_trade_qty=10,
            exec_price_bp=500_000,
            mark_before_bp=490_000,
            fee_bp=0,
            step=0,
        )
        assert isinstance(cert, StepCertificate)
        assert cert.invariant_holds is True
        assert cert.delta_pv == 100_000
        assert cert.expected_delta_pv == 100_000

    def test_raises_when_invariant_violated(self) -> None:
        """ValueError raised when delta_pv != expected."""
        with pytest.raises(ValueError, match="Accounting invariant violated"):
            verify_step(
                pv_before=1_000_000,
                pv_after=1_200_000,  # wrong: should be 1_100_000
                pre_trade_qty=10,
                exec_price_bp=500_000,
                mark_before_bp=490_000,
                fee_bp=0,
                step=3,
            )

    def test_at_market_trade_zero_delta(self) -> None:
        """At-market trade (exec == mark) leaves pv unchanged if no fee."""
        cert = verify_step(
            pv_before=5_000_000,
            pv_after=5_000_000,
            pre_trade_qty=100,
            exec_price_bp=300_000,
            mark_before_bp=300_000,
            fee_bp=0,
            step=1,
        )
        assert cert.invariant_holds is True
        assert cert.delta_pv == 0
        assert cert.expected_delta_pv == 0

    def test_fee_reduces_pv(self) -> None:
        """Fee reduces portfolio value even on an at-market trade."""
        fee = 50_000
        cert = verify_step(
            pv_before=5_000_000,
            pv_after=5_000_000 - fee,
            pre_trade_qty=100,
            exec_price_bp=300_000,
            mark_before_bp=300_000,
            fee_bp=fee,
            step=2,
        )
        assert cert.invariant_holds is True
        assert cert.delta_pv == -fee

    def test_step_index_recorded(self) -> None:
        """Step index is stored in the certificate."""
        cert = verify_step(
            pv_before=0,
            pv_after=0,
            pre_trade_qty=0,
            exec_price_bp=100_000,
            mark_before_bp=100_000,
            fee_bp=0,
            step=42,
        )
        assert cert.step == 42

    def test_short_position_price_rises(self) -> None:
        """Short position (pre_trade_qty < 0) loses when price rises.

        pre_trade_qty=-10, exec=600_000 bp, mark=500_000 bp:
        expected = -10 * (600_000 - 500_000) - 0 = -1_000_000
        """
        cert = verify_step(
            pv_before=10_000_000,
            pv_after=9_000_000,
            pre_trade_qty=-10,
            exec_price_bp=600_000,
            mark_before_bp=500_000,
            fee_bp=0,
            step=5,
        )
        assert cert.invariant_holds is True
        assert cert.expected_delta_pv == -1_000_000

    def test_new_position_zero_pretrade_qty(self) -> None:
        """Opening a brand-new position (pre_trade_qty=0) has zero MTM gain."""
        # Only fee affects PV when opening a new position
        cert = verify_step(
            pv_before=1_000_000,
            pv_after=1_000_000,
            pre_trade_qty=0,
            exec_price_bp=500_000,
            mark_before_bp=0,
            fee_bp=0,
            step=0,
        )
        assert cert.invariant_holds is True
        assert cert.expected_delta_pv == 0
