# WRDS OptionMetrics Data Download

Target: `data/portfolio_atm_options.parquet`
Tickers: SPY, QQQ, AAPL, MSFT, JPM
Date range: 2019-01-01 to 2024-12-31

---

## Step 1 — Log in

Go to **wrds.wharton.upenn.edu** and sign in.

---

## Step 2 — Find the secids

1. Left sidebar: **OptionMetrics → Ivy DB US → Security Names**
2. Date range: 2019-01-01 to 2024-12-31
3. Ticker field: `SPY QQQ AAPL MSFT JPM`
4. Variables: check `secid` and `ticker` (ignore `expire_date` if not available)
5. Submit → download as **CSV**
6. Open the CSV — write down the `secid` for each ticker.
   Each ticker may have a few rows; use the secid that appears most often
   (they are almost certainly all the same value per ticker).

**Tell Akhil / Claude the five secids before running Step 3** so the script
can be verified before the large download.

---

## Step 3 — Download option prices

1. Sidebar: **OptionMetrics → Ivy DB US → Option Price**
2. Date range: **2019-01-01 to 2024-12-31**
3. Security ID: paste the five secids from Step 2, one per line
4. Variables — check exactly these eight:
   - `secid`
   - `date`
   - `exdate`
   - `strike_price`
   - `cp_flag`
   - `best_bid`
   - `best_offer`
   - `impl_volatility`
5. Submit → download as **CSV**
   (expect several hundred MB — this is normal for 5 tickers × 6 years)

---

## Step 3b — Download underlying spot prices

1. Sidebar: **OptionMetrics → Ivy DB US → Security Prices**
2. Date range: **2019-01-01 to 2024-12-31**
3. Security ID: paste the same five secids, one per line
4. Variables — check exactly these three:
   - `secid`
   - `date`
   - `close`
5. Submit → download as **CSV**
   (small file — just daily closing prices)

---

## Step 4 — Save the files

| File                | Save as                  |
|---------------------|--------------------------|
| Security Names CSV  | `~/Downloads/secnmd.csv` |
| Option Price CSV    | `~/Downloads/opprcd.csv` |
| Security Prices CSV | `~/Downloads/secprd.csv` |

---

## Step 5 — Convert to parquet

The script `scripts/wrds_csv_to_parquet.py` handles column renaming,
secid→ticker mapping, spot-price join, ATM ±3% filter, 20–40 day expiry
filter, and a strike×1000 sanity check.

```bash
cd /path/to/options-hedge-engine
uv run python scripts/wrds_csv_to_parquet.py
```

Expected output:

```text
underlying_ticker  rows   date_min    date_max    iv_median
AAPL               ~3200  2019-01-02  2024-12-31  ~0.248
JPM                ~2900  2019-01-02  2024-12-31  ~0.218
MSFT               ~3100  2019-01-02  2024-12-31  ~0.225
QQQ                ~3300  2019-01-02  2024-12-31  ~0.195
SPY                ~3800  2019-01-02  2024-12-31  ~0.141
```

Output file: `data/portfolio_atm_options.parquet`

---

## Step 6 — Run the real-data tests

```bash
cd python
uv run pytest tests/test_backtest.py -v -k "RealData or Holdout"
```

These two test classes activate automatically once the parquet file exists:

| Test class | What it checks |
| --- | --- |
| `TestRealDataBacktest` | cost/premium ~1.0 +/-10%, all tickers, in-sample sigma |
| `TestHoldoutValidation` | cost/premium ~1.0 +/-15% on 2024, sigma from 2019-2023 |

A passing holdout test means the engine generalises across vol regimes
(2020 COVID crash, 2022 bear market, 2023–2024 normalization).

---

## Notes

- `strike_price` in OptionMetrics is in dollars. If the script prints
  `WARNING: strike appears to be stored × 1000`, it divides automatically.
- `secprd.close` is the daily closing price of the underlying — the true
  spot price used for delta computation and ATM filtering.
- The parquet schema expected by the engine:
  `underlying_ticker, date, expiry, strike, option_type, best_bid,
   best_offer, impl_volatility, underlying_price`
