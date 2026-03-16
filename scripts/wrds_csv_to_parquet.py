"""Convert WRDS OptionMetrics CSV exports to the engine's parquet schema.

Usage
-----
1. Download Security Names CSV from WRDS → OptionMetrics → Ivy DB US → Security Names
   Save as ~/Downloads/secnmd.csv  (or update SECNMD_CSV below)

2. Download Option Price CSV from WRDS → OptionMetrics → Ivy DB US → Option Price
   Save as ~/Downloads/opprcd.csv  (or update OPPRCD_CSV below)

3. Run:
       cd /path/to/options-hedge-engine
       uv run python scripts/wrds_csv_to_parquet.py

Output: data/portfolio_atm_options.parquet
"""

from pathlib import Path

import pandas as pd

# ── Edit these paths if your downloads landed somewhere else ───────────────
SECNMD_CSV = Path.home() / "Downloads" / "secnmd.csv"
OPPRCD_CSV = Path.home() / "Downloads" / "opprcd.csv"
OUT_FILE = Path(__file__).parent.parent / "data" / "portfolio_atm_options.parquet"

TARGET_TICKERS = {"SPY", "QQQ", "AAPL", "MSFT", "JPM"}
# ──────────────────────────────────────────────────────────────────────────


def build_secid_map(secnmd_csv: Path) -> dict[int, str]:
    """Return {secid: ticker} for the target tickers."""
    df = pd.read_csv(secnmd_csv, low_memory=False)

    # Column names vary slightly by WRDS export — normalise to lowercase
    df.columns = [c.lower().strip() for c in df.columns]

    # Keep only the most-recent active row per secid
    df["effect_date"] = pd.to_datetime(df["effect_date"])
    df = df.sort_values("effect_date").drop_duplicates("secid", keep="last")

    df = df[df["ticker"].str.upper().isin(TARGET_TICKERS)]
    mapping = dict(zip(df["secid"].astype(int), df["ticker"].str.upper()))
    print("secid map:", mapping)
    return mapping


def load_and_clean(opprcd_csv: Path, secid_map: dict[int, str]) -> pd.DataFrame:
    df = pd.read_csv(opprcd_csv, low_memory=False)
    df.columns = [c.lower().strip() for c in df.columns]

    # Map secid → ticker
    df["secid"] = df["secid"].astype(int)
    df["underlying_ticker"] = df["secid"].map(secid_map)
    df = df[df["underlying_ticker"].notna()].drop(columns=["secid"])

    # Rename to engine schema
    df = df.rename(
        columns={
            "exdate": "expiry",
            "strike_price": "strike",
            "cp_flag": "option_type",
            "spotprice": "underlying_price",
        }
    )

    # Normalise date strings
    df["date"] = pd.to_datetime(df["date"]).dt.strftime("%Y-%m-%d")
    df["expiry"] = pd.to_datetime(df["expiry"]).dt.strftime("%Y-%m-%d")
    df["option_type"] = df["option_type"].str.upper()

    # Filter: calls only, valid quotes, non-null IV
    df = df[
        (df["option_type"] == "C")
        & (df["best_bid"] > 0)
        & (df["best_offer"].notna())
        & (df["impl_volatility"].notna())
        & (df["underlying_price"] > 0)
    ]

    # Filter: 20–40 calendar days to expiry
    days = (pd.to_datetime(df["expiry"]) - pd.to_datetime(df["date"])).dt.days
    df = df[(days >= 20) & (days <= 40)]

    # Filter: ATM ±3%
    moneyness = (df["strike"] / df["underlying_price"] - 1).abs()
    df = df[moneyness <= 0.03]

    # Sanity check: OptionMetrics sometimes stores strike × 1000
    median_moneyness = (df["strike"] / df["underlying_price"]).median()
    if median_moneyness > 100:
        print("WARNING: strike appears to be stored × 1000 — dividing by 1000")
        df["strike"] = df["strike"] / 1000.0

    return df.reset_index(drop=True)


def main() -> None:
    if not SECNMD_CSV.exists():
        raise FileNotFoundError(f"Security names CSV not found: {SECNMD_CSV}")
    if not OPPRCD_CSV.exists():
        raise FileNotFoundError(f"Option price CSV not found: {OPPRCD_CSV}")

    print("Building secid map …")
    secid_map = build_secid_map(SECNMD_CSV)
    missing = TARGET_TICKERS - set(secid_map.values())
    if missing:
        print(f"WARNING: these tickers were not found in secnmd: {missing}")

    print("Loading and filtering option data …")
    df = load_and_clean(OPPRCD_CSV, secid_map)

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
    print(f"\nSaved → {OUT_FILE}")


if __name__ == "__main__":
    main()
