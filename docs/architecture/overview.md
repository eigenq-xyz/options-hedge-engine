# Architecture Overview

**Current version**: v0.4-backtest

## Core Principle

**Lean** and **Python** have distinct, non-overlapping responsibilities:

- **Lean**: Accounting kernel + formal proofs (pure functions, data-source agnostic)
- **Python**: Black-Scholes pricing, GBM simulation, backtest runner, ETL, certificates
- **Cython FFI**: Bridge between the two (Python stubs used until the Cython extension is built)

## System Diagram

```text
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

## Lean Module Dependency Graph

```text
Basic.lean          — Portfolio, Position, Trade, AssetId
    └─▶ Accounting.lean     — FFI exports (hedge_*)
    └─▶ Invariants.lean     — all accounting theorems
    └─▶ Options.lean        — EuropeanOption, payoff functions
            └─▶ OptionInvariants.lean — settlement theorems
```

## Numeric Precision

All monetary values use **basis points** (×10,000) as `Int`:

```python
to_bp(50.25) = 502_500
from_bp(502_500) = 50.25
```

Floats are computed in Python (BS pricing, Greeks), converted to integers at the boundary,
and the integer is the only thing that crosses into the Lean kernel. Lean never operates on floats.

## FFI Boundary

```python
# Python stubs (python/src/hedge_engine/ffi/__init__.py)
# Mirror Lean's @[export hedge_*] functions exactly

def apply_trade(cash, positions, asset_id, delta_quantity, execution_price, fee)
    # returns: {"cash": int, "positions": list[dict], "portfolio_value": int}

def settle_option(cash, positions, option_asset_id, option_kind, strike_bp, spot_bp)
    # returns: {"cash": int, "positions": list[dict], "portfolio_value": int}
```

The Cython extension (`ffi/lean_ffi.pyx`) calls the compiled Lean C symbols directly.
Until the Cython extension is built, the pure-Python stubs replicate the same logic
(but do not execute through the proven Lean kernel at runtime).

## Step Certificates

At each backtest step, the runner emits a `StepCertificate`:

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

`invariant_holds = False` raises `ValueError` immediately; the runner cannot continue
with a violated accounting invariant.

## Interest Accrual

Interest accrual is handled in Python only:

```python
def _apply_interest(portfolio, rate_per_step):
    new_cash = int(old_cash * rate_per_step) + old_cash
    ...
```

The Lean kernel is stateless about time. `valueUpdateFormula` certifies individual
trades, not time evolution. Interest is a between-trade event and never belongs in
the kernel.

## Key Design Decisions

See [DECISIONS.md](https://github.com/eigenq-xyz/options-hedge-engine/blob/main/DECISIONS.md) for full ADR documentation:

- **ADR-000**: Lean for accounting, Python for ETL, data-source agnostic kernel
- **ADR-001**: Scaled integer arithmetic (basis points) instead of floats or rationals
- **ADR-002**: JSON certificates with string-encoded decimals
- **ADR-004**: Monorepo structure with root Makefile orchestration
