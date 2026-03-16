"""ETL schema and loader tests.

WRDS-dependent tests are skipped if pandas is absent or if a WRDS
session is not active (no credentials in environment).
"""

import pytest
from pydantic import ValidationError

from hedge_engine.backtest.data_types import PricePath
from hedge_engine.etl.data_types import OptionSnapshot, UnderlyingSnapshot
from hedge_engine.etl.wrds_loader import price_path_from_snapshots


class TestUnderlyingSnapshot:
    def test_valid(self) -> None:
        s = UnderlyingSnapshot(ticker="spy", date="2024-01-15", close=450.0)
        assert s.ticker == "SPY"  # normalised to upper
        assert s.close == 450.0

    def test_close_must_be_positive(self) -> None:
        with pytest.raises(ValidationError):
            UnderlyingSnapshot(ticker="SPY", date="2024-01-15", close=0.0)

    def test_empty_ticker_rejected(self) -> None:
        with pytest.raises(ValidationError):
            UnderlyingSnapshot(ticker="  ", date="2024-01-15", close=100.0)

    def test_bad_date_format_rejected(self) -> None:
        with pytest.raises(ValidationError):
            UnderlyingSnapshot(ticker="SPY", date="15-01-2024", close=100.0)


class TestOptionSnapshot:
    def test_valid_call(self) -> None:
        s = OptionSnapshot(
            underlying_ticker="spy",
            date="2024-01-15",
            expiry="2024-03-15",
            strike=450.0,
            option_type="C",
            mid_price=5.0,
            implied_vol=0.18,
        )
        assert s.option_type == "call"
        assert s.underlying_ticker == "SPY"
        assert s.underlying_price is None  # optional, absent by default

    def test_valid_call_with_underlying_price(self) -> None:
        s = OptionSnapshot(
            underlying_ticker="SPY",
            date="2024-01-15",
            expiry="2024-03-15",
            strike=450.0,
            option_type="call",
            mid_price=5.0,
            implied_vol=0.18,
            underlying_price=449.5,
        )
        assert s.underlying_price == 449.5

    def test_nonpositive_underlying_price_rejected(self) -> None:
        with pytest.raises(ValidationError):
            OptionSnapshot(
                underlying_ticker="SPY",
                date="2024-01-15",
                expiry="2024-03-15",
                strike=450.0,
                option_type="call",
                mid_price=5.0,
                implied_vol=0.18,
                underlying_price=0.0,
            )

    def test_valid_put(self) -> None:
        s = OptionSnapshot(
            underlying_ticker="SPY",
            date="2024-01-15",
            expiry="2024-03-15",
            strike=450.0,
            option_type="put",
            mid_price=3.0,
            implied_vol=0.19,
        )
        assert s.option_type == "put"

    def test_invalid_option_type(self) -> None:
        with pytest.raises(ValidationError):
            OptionSnapshot(
                underlying_ticker="SPY",
                date="2024-01-15",
                expiry="2024-03-15",
                strike=450.0,
                option_type="X",
                mid_price=5.0,
                implied_vol=0.18,
            )

    def test_negative_vol_rejected(self) -> None:
        with pytest.raises(ValidationError):
            OptionSnapshot(
                underlying_ticker="SPY",
                date="2024-01-15",
                expiry="2024-03-15",
                strike=450.0,
                option_type="call",
                mid_price=5.0,
                implied_vol=-0.1,
            )


class TestPricePathFromSnapshots:
    def _make_snapshots(self, prices: list[float]) -> list[UnderlyingSnapshot]:
        return [
            UnderlyingSnapshot(
                ticker="SPY",
                date=f"2024-01-{i + 1:02d}",
                close=p,
            )
            for i, p in enumerate(prices)
        ]

    def test_basic(self) -> None:
        snaps = self._make_snapshots([100.0, 101.0, 102.0])
        path = price_path_from_snapshots(snaps)
        assert isinstance(path, PricePath)
        assert path.prices == [100.0, 101.0, 102.0]
        assert len(path.times) == 3

    def test_custom_t_total(self) -> None:
        snaps = self._make_snapshots([49.0, 50.0, 51.0])
        path = price_path_from_snapshots(snaps, T_total=1.0)
        assert path.times[-1] == pytest.approx(1.0)
        assert path.times[0] == pytest.approx(0.0)

    def test_too_few_snapshots(self) -> None:
        snaps = self._make_snapshots([100.0])
        with pytest.raises(ValueError, match="at least 2"):
            price_path_from_snapshots(snaps)


class TestWRDSLoader:
    """WRDS DataFrame loaders — skipped if pandas unavailable."""

    @pytest.fixture
    def pd(self) -> "object":
        pd = pytest.importorskip("pandas")
        return pd

    def test_underlying_from_df(self, pd: "object") -> None:
        import pandas  # type: ignore[import-untyped]

        from hedge_engine.etl.wrds_loader import underlying_snapshots_from_df

        df = pandas.DataFrame(
            {
                "ticker": ["SPY", "SPY"],
                "date": ["2024-01-15", "2024-01-16"],
                "prc": [450.0, 452.0],
            }
        )
        rows = underlying_snapshots_from_df(df)
        assert len(rows) == 2
        assert rows[0].ticker == "SPY"
        assert rows[1].close == 452.0

    def test_option_from_df(self, pd: "object") -> None:
        import pandas  # type: ignore[import-untyped]

        from hedge_engine.etl.wrds_loader import option_snapshots_from_df

        df = pandas.DataFrame(
            {
                "ticker": ["SPY"],
                "date": ["2024-01-15"],
                "exdate": ["2024-03-15"],
                "strike_price": [450.0],
                "cp_flag": ["C"],
                "mid_price": [5.0],
                "impl_volatility": [0.18],
            }
        )
        rows = option_snapshots_from_df(df)
        assert len(rows) == 1
        assert rows[0].option_type == "call"
        assert rows[0].strike == 450.0

    def test_optionmetrics_from_df_with_spotprice(self, pd: "object") -> None:
        """optionmetrics loader populates underlying_price from spotprice column."""
        import pandas  # type: ignore[import-untyped]

        from hedge_engine.etl.wrds_loader import (
            optionmetrics_option_snapshots_from_df,
        )

        df = pandas.DataFrame(
            {
                "underlying_ticker": ["SPY", "SPY", "SPY"],
                "date": ["2024-01-15", "2024-01-16", "2024-01-17"],
                "expiry": ["2024-02-16", "2024-02-16", "2024-02-16"],
                "strike": [450.0, 450.0, 450.0],
                "option_type": ["C", "C", "C"],
                "best_bid": [5.0, 5.2, 4.8],
                "best_offer": [5.2, 5.4, 5.0],
                "impl_volatility": [0.18, 0.18, 0.18],
                "underlying_price": [449.5, 450.1, 448.0],
            }
        )
        rows = optionmetrics_option_snapshots_from_df(df)
        assert len(rows) == 3
        assert rows[0].underlying_price == pytest.approx(449.5)
        assert rows[1].underlying_price == pytest.approx(450.1)

    def test_optionmetrics_from_df_without_spotprice(
        self, pd: "object"
    ) -> None:
        """underlying_price is None when spotprice column is absent."""
        import pandas  # type: ignore[import-untyped]

        from hedge_engine.etl.wrds_loader import (
            optionmetrics_option_snapshots_from_df,
        )

        df = pandas.DataFrame(
            {
                "underlying_ticker": ["SPY"],
                "date": ["2024-01-15"],
                "expiry": ["2024-02-16"],
                "strike": [450.0],
                "option_type": ["C"],
                "best_bid": [5.0],
                "best_offer": [5.2],
                "impl_volatility": [0.18],
            }
        )
        rows = optionmetrics_option_snapshots_from_df(df)
        assert len(rows) == 1
        assert rows[0].underlying_price is None

    def test_optionmetrics_skips_crossed_spread(self, pd: "object") -> None:
        """Rows with ask < bid are silently skipped."""
        import pandas  # type: ignore[import-untyped]

        from hedge_engine.etl.wrds_loader import (
            optionmetrics_option_snapshots_from_df,
        )

        df = pandas.DataFrame(
            {
                "underlying_ticker": ["SPY", "SPY"],
                "date": ["2024-01-15", "2024-01-16"],
                "expiry": ["2024-02-16", "2024-02-16"],
                "strike": [450.0, 450.0],
                "option_type": ["C", "C"],
                "best_bid": [5.5, 5.0],  # first row: crossed spread
                "best_offer": [5.0, 5.2],
                "impl_volatility": [0.18, 0.18],
                "underlying_price": [449.5, 449.5],
            }
        )
        rows = optionmetrics_option_snapshots_from_df(df)
        assert len(rows) == 1  # only the second row passes
