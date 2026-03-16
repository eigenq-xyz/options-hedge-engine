# Options Hedge Engine

[![Lean CI](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/lean.yml/badge.svg)](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/lean.yml)
[![Python CI](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/python.yml/badge.svg)](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/python.yml)
[![codecov](https://codecov.io/gh/eigenq-xyz/options-hedge-engine/branch/main/graph/badge.svg)](https://codecov.io/gh/eigenq-xyz/options-hedge-engine)
[![pre-commit.ci status](https://results.pre-commit.ci/badge/github/eigenq-xyz/options-hedge-engine/main.svg)](https://results.pre-commit.ci/latest/github/eigenq-xyz/options-hedge-engine/main)

> **EDUCATIONAL USE ONLY**: This software is for educational and research purposes only. It is NOT intended for live trading or production use. No warranty is provided. See [DISCLAIMER.md](DISCLAIMER.md) for details.

## What This Is

A formally verified options hedging engine combining Lean 4 theorem proving with Python numerical computing.

Every portfolio state transition — every trade, every mark-to-market update, every option settlement — carries a machine-checked proof of correctness. Not "we tested it." Provably correct, with the proof attached.

The engine runs a discrete delta-hedging simulation for written European calls, routes every accounting step through the Lean kernel, and emits a `StepCertificate` at each rebalancing. A bug in the accounting logic raises `ValueError` immediately rather than silently producing wrong numbers.

## Formal Guarantees

### Impossible States (by construction)

| What cannot happen | Enforced by |
| --- | --- |
| Portfolio with incorrect value | `value_valid` proof field on `Portfolio` |
| Position with non-positive price | `markPrice_pos` proof field on `Position` |
| Trade with negative fee | `fee_nonneg` proof field on `Trade` |
| Option with non-positive strike | `strike_pos` proof field on `EuropeanOption` |
| Wrong cash after any trade | `cashUpdateCorrect` (proved `rfl`) |
| Wrong quantity after any trade | `quantityConservation` |
| Ghost zero-quantity positions | `applyTrade_wellFormed` |

### Theorems Proven

| Theorem | Economic meaning |
| --- | --- |
| `valueIdentity` | Portfolio value = cash + Σ(quantity × mark price), always |
| `valueUpdateFormula` | ΔPV = pre-trade qty × (exec price − mark) − fee |
| `selfFinancing` | Trading at the mark price changes PV only by the fee |
| `quantityConservation` | Shares cannot appear from thin air after a trade |
| `cashUpdateCorrect` | Every dollar spent on a trade comes from cash |
| `putCallParity` | Call payoff − put payoff = spot − strike, exactly (integer arithmetic) |
| `settlement_value_formula` | At expiry ΔPV = qty × (payoff − mark), unifying ITM and OTM |

`settlement_value_formula` is the crown jewel: a single theorem covering both settlement branches (in-the-money via `applyTrade`, out-of-the-money via `abandonPosition`) with zero sorry.

## Validation

### Black-Scholes Pricer (DerivaGem reference vectors)

| Scenario | S | K | T | r | σ | Type | Price | Δ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Hull Ex 15.6 | 42 | 40 | 0.5 | 0.10 | 0.20 | call | 4.76 | 0.779 |
| Hull Ex 15.6 | 42 | 40 | 0.5 | 0.10 | 0.20 | put | 0.81 | −0.221 |
| ATM | 100 | 100 | 1.0 | 0.05 | 0.20 | call | 10.45 | 0.637 |

Tolerances: `abs=0.01` on price, `abs=0.001` on delta.

### Monte Carlo Convergence (the Black-Scholes theorem)

The primary numeric gate is not a single path — it is the theorem that the expected discrete hedge cost converges to the Black-Scholes price as paths → ∞.

Over 500 seeded GBM paths (20 weekly rebalancing steps each), the mean hedging cost is within ±3 % of the BS price. Every step on every path carries a `StepCertificate` confirming `valueUpdateFormula` held.

### Variance Reduction (Bertsimas-Kogan-Lo 2000)

BKL (JFE 55(2)) proved `Var[hedge error] ∝ 1/N`. The engine reproduces this:

- `std(10 steps) / std(20 steps) ≈ √2` (within ±30 % at N=200 paths)
- `std(40 steps) < std(10 steps)` (directional)

### Carr-Madan Decomposition

Carr & Madan (1998) decompose discrete hedge cost as:

```
hedge_cost ≈ C₀ − Σᵢ ½ Γᵢ Sᵢ² [(ΔSᵢ/Sᵢ)² − σ²Δt]
```

The engine validates this: `corr(hedge_cost, gamma_pnl) < −0.70` across 200 seeded paths, confirming that realised-vs-implied variance differences drive the hedging error in the theoretically predicted direction.

### Step Certificates

At each rebalancing step, the engine emits a `StepCertificate`:

```python
@dataclass(frozen=True)
class StepCertificate:
    step: int
    portfolio_value_before: int   # basis points
    portfolio_value_after: int    # basis points
    delta_pv: int                 # after − before
    expected_delta_pv: int        # qty × (exec_price − mark) − fee
    invariant_holds: bool         # delta_pv == expected_delta_pv
```

All 500 × 20 = 10,000 certificates pass in the MC test suite.

## Architecture

```
Python (ETL, simulation, backtest runner)
    │
    ├─ bs_price / bs_greeks  (scipy — float → int via to_bp)
    ├─ simulate_gbm          (seeded GBM path generator)
    ├─ run_delta_hedge        (source-agnostic backtest runner)
    │
    └─▶ Lean kernel (via Python stubs / Cython FFI)
            │
            ├─ hedge_apply_trade      (applyTrade + valueUpdateFormula)
            ├─ hedge_settle_option    (applySettlement + settlement_value_formula)
            └─ hedge_portfolio_value  (O(1) field read — value_valid proof)
```

**Lean** implements all accounting as pure functions (`Portfolio → Trade → Portfolio`) and carries formal proofs. It never touches I/O. **Python** handles data loading, BS pricing (treated as advanced ETL), the simulation clock, and interest accrual. **Cython FFI** bridges the two (Python stubs used until the Cython extension is built).

All monetary values cross the FFI boundary as basis-point integers (×10,000): `to_bp(50.25) = 502_500`. Lean never operates on floats.

### Lean module dependency graph

```
Basic.lean          — Portfolio, Position, Trade, AssetId
    └─▶ Accounting.lean     — FFI exports (hedge_*)
    └─▶ Invariants.lean     — all accounting theorems
    └─▶ Options.lean        — EuropeanOption, payoff functions
            └─▶ OptionInvariants.lean — settlement theorems
```

## Getting Started

### Prerequisites

- **Lean 4** v4.27.0-rc1 (installed automatically via `elan`)
- **Python 3.12+** (managed via `uv`)
- **Make**

### Setup and test

```bash
git clone <repository-url>
cd options-hedge-engine
make setup      # install elan + uv, fetch Mathlib cache (~5 min first run)
make test       # Lean proofs + Python tests
make lint       # ruff + mypy
```

### Run the Python tests only

```bash
cd python
uv run pytest -v --cov=hedge_engine
```

### Run a single backtest scenario

```python
from hedge_engine.backtest.runner import run_delta_hedge
from hedge_engine.backtest.scenarios import hull_192_path, HULL_192_K, HULL_192_R, HULL_192_SIGMA, HULL_192_N_CONTRACTS

result = run_delta_hedge(
    path=hull_192_path(),
    K=HULL_192_K, r=HULL_192_R, sigma=HULL_192_SIGMA,
    n_contracts=HULL_192_N_CONTRACTS,
)
print(f"Hedging cost: ${result.total_hedging_cost:,.0f}")
print(f"Certificates passed: {all(c.invariant_holds for c in result.certificates)}")
```

## Research Context

This project explores formal verification for quantitative finance. The accounting kernel and settlement layer are proven correct in Lean 4 (Mathlib), providing stronger guarantees than unit tests: **the proofs hold for all possible inputs**, not just the ones tested.

The `settlement_value_formula` theorem unifies ITM and OTM option expiry into a single machine-checked statement. The discrete delta-hedging backtest validates that the formally-certified accounting kernel produces numerically correct results when integrated with the Black-Scholes model.

**Why formal proof rather than testing?**

A unit test checks one input. A Lean proof checks all inputs. For accounting invariants — "after any trade, the portfolio value equals cash plus mark-to-market positions" — a proof is qualitatively stronger than any finite test suite.

**Lean as a development scaffold for human-AI collaboration.**

There is a second, less obvious role the proofs play: they act as a formal specification that constrains what can be written during development. This project is built with an AI coding assistant. Every accounting function the AI generates must satisfy the pre-existing theorem statements — if the implementation is wrong, the Lean proof fails to compile and the error is caught immediately, before any test is run. The theorems are written (or reviewed) by the human; the AI produces implementations that must discharge them.

This creates a new kind of development loop:

1. Human specifies *what must be true* (the theorem)
2. AI generates code that *must satisfy it* (the implementation)
3. Lean verifies the combination is correct (the proof compiles or it doesn't)
4. Human reviews theorem statements, not implementation line-by-line

The human's oversight is concentrated at the level of mathematical claims rather than implementation details. The AI cannot introduce a silent accounting error that passes the formal spec — it would need to change the theorem to do so, which is a visible, reviewable act. The audit trail (proof obligations + step certificates at runtime) is machine-checkable by any third party with a Lean installation.

This workflow scales: as the theorem base grows, the AI has less room to be wrong.

**Roadmap:**

- v0.4: Discrete delta-hedging backtest + Python stack (current)
- v0.5: `binomial_replication_cost` theorem — single-period replication cost = risk-neutral price (integer arithmetic, no reals needed)
- v0.6+: Multi-period GBM convergence theorem (requires Mathlib-level real analysis)

### References

- Bertsimas, Kogan & Lo (2000), *JFE* 55(2): discrete hedging variance formula
- Boyle & Emanuel (1980), *JFE* 8(3): one-step hedging variance
- Carr & Madan (1998): realized P&L decomposition via dollar gamma
- Hull, "Options, Futures, and Other Derivatives," 9th Global ed., Chapter 19: delta-hedging tables

---

Apache 2.0 — See [LICENSE](LICENSE) for details.

**Academic Disclaimer**: This is research software. While the Lean proofs provide strong correctness guarantees for the accounting kernel, the overall system is not production-ready and should not be used for actual trading without extensive additional validation.
