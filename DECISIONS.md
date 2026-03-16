# Architectural Decision Records

**Purpose**: Document significant design decisions for future reference and consultation.

**Last Updated**: 2026-01-18
**Status**: Work in Progress (v0.1-scaffold)

---

## ADR-000: Architecture - Lean for Accounting, Python for ETL

**Status**: ✅ Accepted
**Date**: 2026-01-18
**Implementation**: All milestones

### Context

Need clear separation of concerns between Lean (verification + implementation) and Python (data engineering). Must support both historical backtests AND future MCMC simulations without architectural changes.

### Decision

**Two distinct subprojects with no code duplication:**

1. **Accounting Kernel (100% Lean) - Data Source Agnostic**
   - Lean implements ALL portfolio accounting (NAV, trades, cash, positions)
   - **Pure functions**: `state + action → new state`
   - **No I/O**: Kernel never touches databases, files, or data sources
   - **No assumptions** about whether data is historical or simulated
   - Lean proves formal invariants about accounting logic
   - Lean code compiled to C via Lake, exposed with `@[export]`
   - Called from Python via Cython FFI

2. **Data Pipeline (Python + Lean Verification) - Multiple Sources**
   - **Historical backtests**: Python loads WRDS OptionMetrics and FEDS data
   - **MCMC simulations** (future): Python generates stochastic paths
   - **Either way**: Python emits JSON "certificate" describing data
   - Lean verifies certificate against assumptions/axioms
   - **Lean does NOT care about data source** - just validates certificate

**Data Flow (Backtest):**
```
WRDS Data → Python ETL → Certificate (JSON)
                ↓                    ↓
         Lean Accounting ←──── Lean Verifier
         (compiled to C)       (checks certificate)
                ↓
         Python (via FFI)
```

**Data Flow (MCMC - Future):**
```
Stochastic Process → Python Simulator → Certificate (JSON)
                            ↓                    ↓
                     Lean Accounting ←──── Lean Verifier
                     (compiled to C)       (checks certificate)
                            ↓
                     Python (via FFI)
```

**Same kernel, different data sources!**

### Rationale

1. **No duplication**: Each language does exactly one job
2. **Lean strengths**: Formal verification + compiled performance for critical accounting
3. **Python strengths**: Data wrangling, rich ecosystem (pandas, numpy)
4. **Clear interfaces**: FFI for accounting calls, JSON certificates for data validation
5. **Verifiable end-to-end**: Accounting is proven correct, data input is validated
6. **Data source flexibility**: Kernel works for historical data, MCMC sims, synthetic data, live feeds

### Consequences

**Positive**:
- Zero duplicate code between Lean and Python
- Accounting kernel is fully formally verified
- Data pipeline has flexibility while maintaining guarantees
- Can swap Python for another language without touching accounting
- **Future-proof**: Same kernel for backtests, MCMC, live trading

**Negative**:
- FFI complexity (Lean → C → Cython → Python)
- Certificate schema must be kept in sync (both languages)
- Learning curve for Lean FFI

### Design Principles for Data Source Agnosticism

**✅ DO:**
- Accounting functions are pure: `Portfolio → Trade → Portfolio`
- Accept prices/quantities as inputs (data source is irrelevant to the kernel)
- Certificate schema describes "what data looks like", not "where it came from"
- Keep time-stepping logic in Python (can be historical or simulated)

**❌ DON'T:**
- Hard-code WRDS-specific logic in Lean
- Assume sequential time (MCMC might jump around)
- Embed data loading in accounting kernel
- Make assumptions about data frequency (daily vs. intraday vs. tick)

### Implementation Plan

**Lean side (lakefile.lean):**
```lean
-- Export accounting functions
@[export lean_calc_nav]
def calcNAV (p : Portfolio) : Int := ...

-- Build shared library
target accounting_shared : FilePath := do
  buildLeanSharedLibOfStatic ...
```

**Python side:**
- `bindings/` - Cython .pyx files with `cdef extern` declarations
- `etl/` - WRDS data loading modules
- `certificate/` - JSON schema + emission

### Consultation Points

- FFI performance: Is overhead acceptable for backtest throughput? → Profile in v0.6
- Certificate granularity: Per-row or batched? → Start batched, refine if needed

---

## ADR-001: Scaled Integer Arithmetic for Financial Precision

**Status**: ✅ Accepted
**Date**: 2026-01-18
**Implementation**: v0.2-numeric

### Context

Need exact decimal arithmetic for portfolio accounting (cash, prices, NAV) to enable formal verification. Lean implements all accounting logic (per ADR-000).

### Decision

Use **scaled integer arithmetic** (basis points) as canonical representation:

**Lean**:
```lean
structure Price where
  basisPoints : Int  -- Price × 10,000 (4 decimal places)
```

**Python**:
```python
from decimal import Decimal, getcontext
getcontext().prec = 28  # High precision

class Price:
    def __init__(self, value: Decimal):
        self.decimal = value

    def to_lean_int(self) -> int:
        """Convert to basis points for Lean"""
        return int(self.decimal * 10000)
```

**FFI Boundary**: Pass integers (basis points), never floats.

### Rationale

1. **Exactness**: No binary floating-point rounding errors (0.1 + 0.2 = 0.3 guaranteed)
2. **Provability**: Integer arithmetic in Lean is fully decidable and easily proven
3. **Performance**: Fast integer operations (vs. Rat's GCD overhead)
4. **Industry standard**: Matches Java BigDecimal, SQL DECIMAL, financial systems
5. **Determinism**: Same inputs always produce identical outputs (critical for verification)

### Consequences

**Positive**:
- Exact NAV calculations
- Provably correct invariants
- Deterministic replay

**Negative**:
- Must track scale factor (mental overhead)
- Division requires careful rounding (prove rounding error bounds)
- Greeks may need higher precision (8 decimals) → use separate `GreekValue` type

**Neutral**:
- Black-Scholes still uses `float` for speed → convert to `Decimal` at boundary

### Alternatives Considered

1. **Rat everywhere**: Exact fractions, but denominators grow (1/3 + 1/7 = 10/21 → explosion). GCD computation overhead.
2. **Float everywhere**: Fast but non-exact, rounding errors accumulate, hard to verify.
3. **Real (Lean type)**: Proof-only, not computable.

### Consultation Points

- **Quant researchers**: Is 4 decimal places sufficient for option prices? (Some may need 6)
- **Practitioners**: How do production systems handle Greeks (float vs. decimal)?
- **Lean experts**: Best practices for division with rounding in proofs?

### References

- Lean Numeric Types Research (internal)
- Mathlib: `Data.Rat.Basic`
- Industry: [Martin Fowler on Money Pattern](https://martinfowler.com/eaaCatalog/money.html)

---

## ADR-002: JSON Certificates with String-Encoded Decimals

**Status**: ✅ Accepted
**Date**: 2026-01-18
**Implementation**: v0.5-certs

### Context

Need interchange format for Python → Lean verification. Must preserve precision.

### Decision

Use JSON with decimals as **strings**:

```json
{
  "cash": "105234.5000",
  "price": "123.4567",
  "precision_decimals": 4
}
```

Lean parses strings to `Int` (multiply by 10^precision).

### Rationale

- JSON numbers are floats (imprecise)
- String preserves exact decimal representation
- Lean parses: `"105234.5000"` → remove "." → `1052345000` → scale by precision

### Alternatives

- Binary format (MessagePack): More efficient, but harder to debug. Defer unless perf critical.
- JSON numbers: Loses precision in parsing.

---

## ADR-003: Epsilon-Tolerance Verification (1 Basis Point)

**Status**: ✅ Accepted (subject to revision)
**Date**: 2026-01-18
**Implementation**: v0.6-verifier

### Context

Conversion from float-based pricers to decimal-based accounting may introduce rounding.

### Decision

Lean verifier accepts `epsilon = 0.0001` (1 basis point) tolerance:

```lean
theorem navIdentityApprox (s : State) (ε : Rat) :
  |calcNAV s - s.nav| < ε := by ...
```

### Rationale

- Balances exactness with practical numerical stability
- 1bp is negligible for portfolio-level accounting
- Prevents spurious failures from final-digit rounding

### Consultation Points

- **Professors**: Is 1bp academically rigorous enough?
- **Practitioners**: Do production systems use tighter tolerances?

### Future Review

- v0.11: Profile actual errors, tighten to 0.1bp if feasible
- Consider variable ε by invariant (strict for cash, looser for Greeks)

---

## ADR-004: Monorepo with Lean + Python + Docs

**Status**: ✅ Accepted
**Date**: 2026-01-18
**Implementation**: v0.1-scaffold

### Context

Need to co-locate Lean proofs, Python implementation, and JupyterBook docs.

### Decision

Single repository with subdirectories:
- `lean/`: Lake project
- `python/`: uv-managed package
- `book/`: JupyterBook
- Root `Makefile` orchestrates all

### Rationale

- Easier to keep schemas in sync (same PR updates both)
- Unified CI (test both sides together)
- Atomic changes (Lean + Python + docs in one commit)

### Alternatives

- Separate repos: Schema sync harder, but cleaner separation. Rejected for v1.0.

---

## ADR-005: Tag-Based Development Milestones

**Status**: ✅ Accepted
**Date**: 2026-01-18
**Implementation**: v0.1-scaffold

### Context

Need development methodology suitable for solo academic project with incremental progress.

### Decision

Use semantic version tags (v0.X-name) for milestones:
- Each tag represents a complete, demo-able feature
- Tags are ordered but can be reordered based on challenges
- GitHub as single source of truth

### Rationale

- Academic rigor: Each milestone is verifiable
- Flexibility: Can adapt based on what proves difficult
- Documentation: Git history preserves research process
- Candid: Milestones reflect actual progress, not aspirational timelines

---

## Future ADRs (Pending)

- ADR-006: FFI Strategy (CLI vs. Lean library import) - v0.6+
- ADR-007: Certificate Versioning Scheme - v0.5
- ADR-008: Optimizer Certificate Detail Level - v0.9
- ADR-009: Data Encryption Strategy - v0.10

**Template for New ADRs**: See DEVELOPMENT.md (coming in v0.1)
