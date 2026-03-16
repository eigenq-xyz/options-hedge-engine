/-
Copyright (c) 2026 Option Hedge Engine Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Karra
-/

import OptionHedge.Basic

/-!
# Option Hedge Engine

Formally verified options portfolio accounting and hedging system (v0.4).

This library provides:
- Exact decimal arithmetic using scaled integers (basis points × 10,000)
- Portfolio state representation with `value_valid` proof field
- Formally proven accounting invariants: `valueIdentity`, `valueUpdateFormula`,
  `selfFinancing`, `quantityConservation`, `cashUpdateCorrect`
- European option settlement: `integerPayoffDifference`, `settlement_value_formula`
- FFI exports (C symbols via `@[export hedge_*]`) for Cython bridge

## Module structure

```
Basic.lean            — Core types: AssetId, Position, Portfolio, Trade
Accounting.lean       — FFI exports: hedge_apply_trade, hedge_settle_option, …
Invariants.lean       — Accounting theorems (valueUpdateFormula, selfFinancing, …)
Options.lean          — EuropeanOption, callPayoff, putPayoff, applySettlement
OptionInvariants.lean — Settlement theorems (integerPayoffDifference, settlement_value_formula)
Tests/UnitTests.lean  — Concrete computation tests via native_decide
```
-/
