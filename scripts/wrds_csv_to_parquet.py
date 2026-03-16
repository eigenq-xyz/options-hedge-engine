"""Convert WRDS OptionMetrics CSV exports to the engine's parquet schema.

Usage
-----
Place the three WRDS CSV downloads in the data/ directory:

  data/optionmetrics_secid_ticker_cusip.csv   -- Security Names
  data/optionmetrics_tickers_options_data.csv -- Option Price
  data/optionmetrics_asset_prices.csv         -- Security Prices (daily close)

Then run:
    cd /path/to/options-hedge-engine
    uv run python scripts/wrds_csv_to_parquet.py

Output: data/portfolio_atm_options.parquet
"""

from pathlib import Path

import pandas as pd

_DATA = Path(__file__).parent.parent / "data"

# ── Input files (WRDS CSV exports) ──────────────────────────────────────
SECNMD_CSV = _DATA / "optionmetrics_secid_ticker_cusip.csv"
OPPRCD_CSV = _DATA / "optionmetrics_tickers_options_data.csv"
SECPRD_CSV = _DATA / "optionmetrics_asset_prices.csv"
OUT_FILE = _DATA / "portfolio_atm_options.parquet"

TARGET_TICKERS = {"SPY", "QQQ", "AAPL", "MSFT", "JPM"}
# ───────────────────────────────────────────────────────────────────────────


def build_secid_map(secnmd_csv: Path) -> dict[int, str]:
    """Return {secid: ticker} for the target tickers."""
    df = pd.read_csv(secnmd_csv, low_memory=False)
    df.columns = [c.lower().strip() for c in df.columns]

    # Keep only the most-recent active row per secid
    df["effect_date"] = pd.to_datetime(df["effect_date"])
    df = df.sort_values("effect_date").drop_duplicates("secid", keep="last")

    df = df[df["ticker"].str.upper().isin(TARGET_TICKERS)]
    mapping = dict(zip(df["secid"].astype(int), df["ticker"].str.upper()))
    print("secid map:", mapping)
    return mapping


def load_security_prices(secprd_csv: Path, secid_map: dict[int, str]) -> pd.DataFrame:
    """Return DataFrame with (secid, date, underlying_price) from daily closes."""
    df = pd.read_csv(secprd_csv, low_memory=False)
    df.columns = [c.lower().strip() for c in df.columns]

    df["secid"] = df["secid"].astype(int)
    df = df[df["secid"].isin(secid_map)]
    df["date"] = pd.to_datetime(df["date"]).dt.strftime("%Y-%m-%d")

    return df[["secid", "date", "close"]].rename(columns={"close": "underlying_price"})


def load_and_clean(
    opprcd_csv: Path,
    secid_map: dict[int, str],
    spot_df: pd.DataFrame,
) -> pd.DataFrame:
    """Load option prices, join spot prices, and apply ATM/expiry filters."""
    df = pd.read_csv(opprcd_csv, low_memory=False)
    df.columns = [c.lower().strip() for c in df.columns]

    # Map secid → ticker
    df["secid"] = df["secid"].astype(int)
    df["underlying_ticker"] = df["secid"].map(secid_map)
    df = df[df["underlying_ticker"].notna()]

    # Rename to engine schema
    df = df.rename(
        columns={
            "exdate": "expiry",
            "strike_price": "strike",
            "cp_flag": "option_type",
        }
    )

    # Normalise date strings
    df["date"] = pd.to_datetime(df["date"]).dt.strftime("%Y-%m-%d")
    df["expiry"] = pd.to_datetime(df["expiry"]).dt.strftime("%Y-%m-%d")
    # Normalise option_type to "call"/"put" (OptionMetrics uses "C"/"P")
    df["option_type"] = df["option_type"].str.upper().map({"C": "call", "P": "put"})

    # Join underlying spot prices from Security Prices table
    df = df.merge(spot_df, on=["secid", "date"], how="inner")
    df = df.drop(columns=["secid"])

    # Filter: calls only, valid quotes, non-null IV, valid spot
    df = df[
        (df["option_type"] == "call")
        & (df["best_bid"] > 0)
        & (df["best_offer"].notna())
        & (df["impl_volatility"].notna())
        & (df["underlying_price"] > 0)
    ]

    # Sanity check: OptionMetrics stores strike × 1000 — fix BEFORE ATM filter
    median_ratio = (df["strike"] / df["underlying_price"]).median()
    if median_ratio > 100:
        print("NOTE: strike stored x1000 — dividing by 1000")
        df["strike"] = df["strike"] / 1000.0

    # Filter: 20–40 calendar days to expiry
    days = (pd.to_datetime(df["expiry"]) - pd.to_datetime(df["date"])).dt.days
    df = df[(days >= 20) & (days <= 40)]

    # Filter: ATM ±3%
    moneyness = (df["strike"] / df["underlying_price"] - 1).abs()
    df = df[moneyness <= 0.03]

    return df.reset_index(drop=True)


def main() -> None:
    """Build data/portfolio_atm_options.parquet from WRDS CSV exports."""
    for path in (SECNMD_CSV, OPPRCD_CSV, SECPRD_CSV):
        if not path.exists():
            raise FileNotFoundError(f"Required file not found: {path}")

    print("Building secid map ...")
    secid_map = build_secid_map(SECNMD_CSV)
    missing = TARGET_TICKERS - set(secid_map.values())
    if missing:
        print(f"WARNING: these tickers were not found in secnmd: {missing}")

    print("Loading security prices ...")
    spot_df = load_security_prices(SECPRD_CSV, secid_map)

    print("Loading and filtering option data ...")
    df = load_and_clean(OPPRCD_CSV, secid_map, spot_df)

    summary = df.groupby("underlying_ticker").agg(
        rows=("date", "count"),
        date_min=("date", "min"),
        date_max=("date", "max"),
        iv_median=("impl_volatility", "median"),
    )
    print("\nSummary by ticker:")
    print(summary.to_string())
    print(f"\nTotal rows: {len(df):,}")

    OUT_FILE.parent.mkdir(exist_ok=True)
    df.to_parquet(OUT_FILE, index=False)
    print(f"\nSaved -> {OUT_FILE}")


if __name__ == "__main__":
    main()
