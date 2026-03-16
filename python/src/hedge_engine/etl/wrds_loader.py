"""WRDS data loader: converts raw WRDS query output to engine types.

WRDS access requires a valid subscription.  Tests that call these
functions should be guarded with ``pytest.importorskip`` or an
environment-variable skip so CI passes without credentials.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from hedge_engine.backtest.data_types import PricePath
from hedge_engine.etl.data_types import OptionSnapshot, UnderlyingSnapshot

if TYPE_CHECKING:  # avoid hard runtime dependency on pandas
    import pandas as pd


def underlying_snapshots_from_df(
    df: pd.DataFrame,
    ticker_col: str = "ticker",
    date_col: str = "date",
    close_col: str = "prc",
) -> list[UnderlyingSnapshot]:
    """Parse a WRDS CRSP daily stock file into `UnderlyingSnapshot` objects.

    Args:
        df: Raw WRDS DataFrame.
        ticker_col: Column containing the ticker symbol.
        date_col: Column containing the observation date (``YYYY-MM-DD``).
        close_col: Column containing the closing price.

    Returns:
        List of validated :class:`UnderlyingSnapshot` instances.
    """
    rows: list[UnderlyingSnapshot] = []
    for _, row in df.iterrows():
        rows.append(
            UnderlyingSnapshot(
                ticker=str(row[ticker_col]),
                date=str(row[date_col]),
                close=float(row[close_col]),
            )
        )
    return rows


def option_snapshots_from_df(
    df: pd.DataFrame,
    underlying_col: str = "ticker",
    date_col: str = "date",
    expiry_col: str = "exdate",
    strike_col: str = "strike_price",
    type_col: str = "cp_flag",
    mid_col: str = "mid_price",
    vol_col: str = "impl_volatility",
) -> list[OptionSnapshot]:
    """Parse a WRDS OptionMetrics file into `OptionSnapshot` objects.

    Args:
        df: Raw WRDS OptionMetrics DataFrame.
        underlying_col: Column for the underlying ticker.
        date_col: Observation date column.
        expiry_col: Option expiry date column.
        strike_col: Strike price column (dollars).
        type_col: Option type column (``"C"`` or ``"P"``).
        mid_col: Mid-price column (dollars).
        vol_col: Implied volatility column (fraction).

    Returns:
        List of validated :class:`OptionSnapshot` instances.
    """
    type_map = {"C": "call", "P": "put"}
    rows: list[OptionSnapshot] = []
    for _, row in df.iterrows():
        rows.append(
            OptionSnapshot(
                underlying_ticker=str(row[underlying_col]),
                date=str(row[date_col]),
                expiry=str(row[expiry_col]),
                strike=float(row[strike_col]),
                option_type=type_map.get(str(row[type_col]).upper(), "call"),
                mid_price=float(row[mid_col]),
                implied_vol=float(row[vol_col]),
            )
        )
    return rows


def price_path_from_snapshots(
    snapshots: list[UnderlyingSnapshot],
    T_total: float | None = None,
) -> PricePath:
    """Convert a sorted list of `UnderlyingSnapshot` into a `PricePath`.

    Args:
        snapshots: Chronologically sorted snapshots for a single ticker.
        T_total: Total time horizon in years.  If ``None``, the number
            of observations minus one is used (i.e. one step per day).

    Returns:
        :class:`PricePath` with evenly spaced times from 0 to T_total.
    """
    if len(snapshots) < 2:
        raise ValueError(
            "Need at least 2 snapshots to form a PricePath, "
            f"got {len(snapshots)}"
        )
    n = len(snapshots) - 1
    horizon = T_total if T_total is not None else float(n)
    times = [i * horizon / n for i in range(n + 1)]
    prices = [s.close for s in snapshots]
    return PricePath(times=times, prices=prices)
