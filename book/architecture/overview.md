# Architecture Overview

**Last Updated**: 2026-01-18 (v0.1-scaffold)

## Core Principle: No Code Duplication + Data Source Agnostic

**Lean** and **Python** have distinct, non-overlapping responsibilities:

1. **Lean**: Accounting kernel implementation + formal verification (data source agnostic)
2. **Python**: Data pipeline (backtests OR simulations) + FFI bindings + certificate emission

**Key Design Goal**: The accounting kernel must work for:
- ✅ Historical backtests (WRDS data)
- ✅ MCMC simulations (stochastic processes) - *future*
- ✅ Synthetic data (testing)
- ✅ Live trading (market feeds) - *future*

---

## Component 1: Accounting Kernel (100% Lean) - Pure Functions

### Responsibility

Implement ALL portfolio accounting logic as **pure functions**:
- Portfolio state representation (`Portfolio`, `Position`, `Trade`)
- NAV calculation (`calcNAV : Portfolio → Int`)
- Trade application (`applyTrade : Portfolio → Trade → Portfolio`)
- Cash accrual (`accrueInterest : Portfolio → Rate → Portfolio`)
- Position management

**Critical**: Functions accept data as inputs, never load data themselves.

### Implementation

```lean
-- OptionHedge/Accounting.lean

@[export lean_calc_nav]
def calcNAV (p : Portfolio) : Int :=
  p.cash + sumPositionValues p.positions

@[export lean_apply_trade]
def applyTrade (p : Portfolio) (t : Trade) : Portfolio :=
  -- Implementation with proofs
  ...
```

### Formal Verification

Prove invariants about accounting functions:
- NAV identity
- Self-financing property
- Conservation of quantities
- Cash update correctness
- Time monotonicity
- Domain constraints
- Deterministic replay

```lean
-- OptionHedge/Invariants.lean

theorem navIdentity (p : Portfolio) :
  calcNAV p = p.cash + sumPositionValues p.positions := by
  -- Proof
  ...
```

### Compilation & Export

```bash
# Lake compiles Lean → C
lake build OptionHedge

# Generates:
# - .lake/build/lib/libOptionHedge.a (static library)
# - .lake/build/lib/libOptionHedge.so (shared library)
# - C headers with exported functions
```

### Python Interface

Python calls Lean functions via Cython FFI (NO Python implementation of accounting):

```python
# python/src/hedge_engine/bindings/accounting.pyx (Cython)

cdef extern from "lean/lean.h":
    ctypedef struct lean_object

cdef extern from "OptionHedge.h":
    lean_object* lean_calc_nav(lean_object* portfolio)
    lean_object* lean_apply_trade(lean_object* portfolio, lean_object* trade)

def calc_nav(portfolio):
    """Calculate NAV by calling Lean."""
    # Convert Python → Lean
    lean_portfolio = python_to_lean_portfolio(portfolio)
    # Call Lean function
    result = lean_calc_nav(lean_portfolio)
    # Convert Lean → Python
    return lean_to_python_int(result)
```

---

## Component 2: Data Pipeline (Python + Lean Verification)

### Python: Multiple Data Sources

The data pipeline is **modular** - swap sources without changing accounting kernel:

**Historical Backtests (v0.10):**
```python
# python/src/hedge_engine/etl/wrds_loader.py

def load_option_metrics(start_date, end_date):
    """Load historical OptionMetrics data from WRDS."""
    # Connect to WRDS database
    # Load option prices, implied vols, etc.
    return options_dataframe
```

**MCMC Simulations (future):**
```python
# python/src/hedge_engine/simulation/mcmc.py

def generate_price_paths(initial (Source-Agnostic)

After getting data (historical OR simulated), Python describes it in a certificate:

```python
# python/src/hedge_engine/certificate/emitter.py

def emit_data_certificate(data, source_type, validation_results):
    """Emit certificate describing data - works for ANY source."""
    return {
        "version": "1.0",
        "source_type": source_type,  # "historical_wrds" | "mcmc_simulation" | "synthetic"
        "date_range": {"start": "2024-01-01", "end": "2024-12-31"},
        "row_count": len(data),
        "validation": {
            "no_nulls": validation_results.nulls_ok,
            "dates_monotonic": validation_results.dates_sorted,
            "prices_positive": validation_results.prices_valid,
        },
        "assumptions": {
            # These are what Lean verifies - same for any source!
            "max_strike_price": 10000.0,
            "min_days_to_expiry": 1,
            "implied_vol_range": [0.01, 5.0],
        }
    }
```

**Key**: Certificate describes "what the data looks like", NOT "where it came from". Lean verifies assumptions, doesn't care about source. """Emit certificate describing ETL output."""
    return {
        "version": "1.0",
        "etl_type": "option_metrics",
        "date_range": {"start": "2024-01-01", "end": "2024-12-31"},
        "row_count": len(data),
        "schema_version": "OptionMetrics_v2024",
        "validation": {
            "no_nulls": validation_results.nulls_ok,
            "dates_monotonic": validation_results.dates_sorted,
            "prices_positive": validation_results.prices_valid,
        },
        "assumptions": {
            "max_strike_price": 10000.0,
            "min_days_to_expiry": 1,
            "implied_vol_range": [0.01, 5.0],
        }
    }
``` (Source-Agnostic)

Lean validates assumptions, doesn't care if data is historical or simulated:

```lean
-- OptionHedge/Certificate/DataVerifier.lean

structure DataCertificate where
  version : String
  sourceType : String  -- "historical_wrds" | "mcmc_simulation" | etc.
  rowCount : Nat
  validation : ValidationResults
  assumptions : Assumptions

-- Verify assumptions - same check regardless of source!
def verifyDataAssumptions (cert : DataCertificate) : Bool :=
  cert.assumptions.maxStrikePrice ≤ MAX_ALLOWED_STRIKE ∧
  cert.assumptions.minDaysToExpiry ≥ MIN_DAYS_TO_EXPIRY ∧
  cert.validation.pricesPositive = true
  -- Source type is informational only, not part of verification

theorem dataCertificateValid (cert : DataCertificate)
  (h : verifyDataAssumptions cert = true) :
  -- Theorem holds for ANY data source
  (h : verifyETLAssumptions cert = true) :
  -- If certificate passes, data meets accounting kernel assumptions
  DataMeetsAssumptions cert := by
  ...
```

**Historical Backtest:**
```
┌─────────────────────────────────────────────┐
│  WRDS Database (OptionMetrics, FEDS)       │
└──────────────┬──────────────────────────────┘
               │
               ↓ SQL queries
┌─────────────────────────────────────────────┐
│  Python ETL (hedge_engine/etl/)             │
│  - Load historical data                     │
│  - Clean & validate                         │
└──────────────┬──────────────────────────────┘
               │
               ├─→ Emit Certificate (JSON)
               │   └─→ Lean verifies assumptions
               │
               ↓ Call via FFI (prices as input)
┌─────────────────────────────────────────────┐
│  Lean Accounting Kernel (compiled C)        │
│  - Accepts prices from ANY source           │
│  - calcNAV, applyTrade (pure functions)     │
└──────────────┬──────────────────────────────┘
               │
               ↓ Return results
┌─────────────────────────────────────────────┐
│  Python Orchestration                       │
│  - Receives NAV, updated portfolio          │
│  - Continues backtest                       │
└─────────────────────────────────────────────┘
```

**MCMC Simulation (future):**
```
┌─────────────────────────────────────────────┐
│  Stochastic Process Model (GBM, etc.)      │
└──────────────┬──────────────────────────────┘
               │
               ↓ Generate paths
┌─────────────────────────────────────────────┐
│  Python Simulator (hedge_engine/sim/)       │
│  - Generate price paths                     │
│  - Validate statistical properties          │
└──────────────┬──────────────────────────────┘
               │
               ├─→ Emit Certificate (JSON)
               │   └─→ Lean verifies assumptions (same as backtest!)
               │
               ↓ Call via FFI (simulated prices)
┌─────────────────────────────────────────────┐
│  SAME Lean Accounting Kernel                │
│  - Doesn't care if prices are historical    │
│  - Pure functions: state + prices → NAV     │
└──────────────┬──────────────────────────────┘
               │
               ↓ Return results
┌─────────────────────────────────────────────┐
│  Python MCMC Loop                           │
│  - Aggregate across scenarios               │
│  - Compute statistics                       │
└─────────────────────────────────────────────┘
```

**Key**: Same accounting kernel, different data sources!Python Orchestration                       │
│  - Receives NAV, updated portfolio          │
│  - Continues backtest                       │
└─────────────────────────────────────────────┘
```

---

## Milestone Breakdown

### v0.2-nav (Lean + FFI)
- Setup Lake for Lean → C shared library compilation
- Implement `calcNAV` in Lean with `@[export]`
- Create Cython FFI bindings
- Add FFI round-trip tests
- Prove NAV identity theorem

**Note**: Original v0.2-numeric milestone removed - numeric types simplified to raw Int with basis points convention.

### v0.3-trades (Lean + FFI)
- Implement `applyTrade` in Lean with `@[export]`
- Prove conservation theorems
- **Python**: Cython binding to call `lean_apply_trade`

### v0.4-certs (Python only)
- **Python**: Certificate schema (Pydantic)
- **Python**: Certificate emission after ETL

### v0.5-verifier (Lean only)
- **Lean**: Parse JSON certificates (data-agnostic)
- **Python**: Data sources, orchestration, visualization (flexible)
- **No duplication**: Zero overlap in responsibilities

### 4. Flexibility for Future Use Cases

Accounting kernel works for multiple scenarios:
- **Backtests**: Historical WRDS data (v0.10)
- **MCMC simulations**: Stochastic price paths (future)
- **Stress testing**: Synthetic worst-case scenarios (future)
- **Live trading**: Real-time market feeds (future)
- **Research**: Custom data sources for academic studies

All use the same proven-correct accounting kernel!

### 5. Swappable Data Layer

Can swap Python for another language without touching accounting:
- **R** for statistical analysis + same Lean kernel
- **Julia** for numerical computing + same Lean kernel
- **JavaScript** for web interfaces + same Lean kernel
data loading in Lean
- Lean isn't designed for data wrangling
- Would need complex FFI to access databases

❌ **DON'T**: Hard-code data source assumptions in accounting kernel
- Don't check "is this from WRDS?" in Lean
- Kernel should be pure functions: `(state, prices) → new_state`

❌ **DON'T**: Mix responsibilities
- Certificate verification belongs in Lean (it's a proof)
- Data loading belongs in Python (it's I/O)
- Time-stepping loop belongs in Python (orchestration)

---

## Questions & Answers

**Q: Why not just write everything in Lean?**
A: ETL requires database connectors, pandas-like operations, visualization. Python's ecosystem is unmatched for data engineering. Lean would require extensive FFI to existing C libraries.

**Q: Why not just write everything in Python?**
A: Can't formally verify Python code. Would have to trust accounting implementation. Defeats the whole point of formal verification.

**Q: How does this support MCMC simulations?**
A: Accounting kernel is pure functions - doesn't care if prices are historical or simulated. Just swap the data source (WRDS loader → MCMC simulator) and use the same kernel. Certificate verifier checks the same assumptions regardless of source.

**Q: What about live trading with market feeds?**
A: Same story! Replace batch data loader with streaming feed. Accounting kernel unchanged. This is exactly why we keep it data-source agnostic.

**Q: What's the FFI overhead?**
A: ~10-50ns per function call. For batch operations (e.g., applying 1000 trades), amortized cost is negligible. Profiled in v0.7.

**Q: How are types converted across FFI?**
A: Lean `Int` → C `lean_object*` → Cython wrapper → Python `int`. Strings, arrays require marshaling. See DEVELOPMENT.md for details.

**Q: What if certificate verification fails?**
A: Backtest/simulation halts. Certificate shows exactly which assumption was violated (e.g., "negative price detected"). Fix data pipeline
- **Python**: Data wrangling, orchestration, visualization
- **No duplication**: Zero overlap in responsibilities

### 4. Flexibility

Can swap Python for another language without touching accounting:
- **R** for statistical analysis
- **Julia** for numerical computing
- **JavaScript** for web interfaces

All would use the same Lean accounting kernel via FFI.

---

## Anti-Patterns (What NOT to Do)

❌ **DON'T**: Implement accounting in Python
- Defeats purpose of formal verification
- Creates drift between Lean spec and Python impl

❌ **DON'T**: Implement ETL in Lean
- Lean isn't designed for data wrangling
- Would need complex FFI to access databases

❌ **DON'T**: Mix responsibilities
- Certificate verification belongs in Lean (it's a proof)
- Data loading belongs in Python (it's I/O)

---

## Questions & Answers

**Q: Why not just write everything in Lean?**
A: ETL requires database connectors, pandas-like operations, visualization. Python's ecosystem is unmatched for data engineering. Lean would require extensive FFI to existing C libraries.

**Q: Why not just write everything in Python?**
A: Can't formally verify Python code. Would have to trust accounting implementation. Defeats the whole point of formal verification.

**Q: What's the FFI overhead?**
A: ~10-50ns per function call. For batch operations (e.g., applying 1000 trades), amortized cost is negligible. Profiled in v0.7.

**Q: How are types converted across FFI?**
A: Lean `Int` → C `lean_object*` → Cython wrapper → Python `int`. Strings, arrays require marshaling. See DEVELOPMENT.md for details.

**Q: What if certificate verification fails?**
A: Backtest halts. Certificate shows exactly which assumption was violated (e.g., "negative price detected"). Fix Python ETL and rerun.

---

## Further Reading

- [DECISIONS.md](../DECISIONS.md) - ADR-000 (Architecture), ADR-001 (Numeric Types)
- [DEVELOPMENT.md](../DEVELOPMENT.md) - FFI implementation details
- [Lean 4 FFI Examples](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/ffi)
- [book/architecture/ffi_guide.md](../book/architecture/ffi_guide.md) - Step-by-step FFI tutorial (v0.3+)
