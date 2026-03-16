/-
Copyright (c) 2026 Option Hedge Engine Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Karra
-/

import OptionHedge.Basic

/-!
# European Options

Types and functions for European option settlement.

This module defines:
- `OptionKind`: Call or Put
- `EuropeanOption`: Option contract with type-level strike positivity
- `callPayoff`, `putPayoff`, `optionPayoff`: Payoff functions (non-negative, exact integer)
- `Trade.settlementITM`: Closing trade for in-the-money expiry
- `Portfolio.abandonPosition`: Erase a worthless position (OTM expiry)
- `SettlementResult`, `EuropeanOption.settle`, `applySettlement`: Unified settlement

## Design Notes

`executionPrice_pos` on `Trade` requires `executionPrice > 0`.  OTM options have payoff 0,
which would violate this constraint, so OTM settlement uses `Portfolio.abandonPosition`
(erase the position via `Portfolio.mk'`) rather than `applyTrade`.  The crown-jewel theorem
`settlement_value_formula` in `OptionInvariants.lean` unifies both branches.
-/

namespace OptionHedge

/-- Call or Put -/
inductive OptionKind where
  | Call
  | Put
  deriving DecidableEq, Repr, BEq

/-- A European option contract.

The `strike_pos` field is a proof that `strike > 0`,
making it impossible to construct an option with a non-positive strike. -/
structure EuropeanOption where
  assetId   : AssetId
  kind      : OptionKind
  strike    : Int
  strike_pos : strike > 0
  deriving DecidableEq

instance : BEq EuropeanOption := ⟨fun a b => decide (a = b)⟩

instance : Repr EuropeanOption where
  reprPrec o _ :=
    s!"EuropeanOption(assetId := {repr o.assetId}, kind := {repr o.kind}, strike := {repr o.strike})"

/-- Smart constructor: builds a EuropeanOption with strike proved positive.
    The proof is auto-discharged by `omega` for concrete positive literals. -/
def EuropeanOption.mk' (assetId : AssetId) (kind : OptionKind) (strike : Int)
    (h : strike > 0 := by omega) : EuropeanOption :=
  ⟨assetId, kind, strike, h⟩

/-- Call payoff: max(spot − strike, 0) -/
@[inline]
def callPayoff (spot strike : Int) : Int := max 0 (spot - strike)

/-- Put payoff: max(strike − spot, 0) -/
@[inline]
def putPayoff (spot strike : Int) : Int := max 0 (strike - spot)

/-- Option payoff dispatched by kind -/
def optionPayoff (opt : EuropeanOption) (spot : Int) : Int :=
  match opt.kind with
  | .Call => callPayoff spot opt.strike
  | .Put  => putPayoff  spot opt.strike

/-- Build the settlement trade for an ITM option.

    Semantics: close the entire position at `payoff` basis points per share.
    Requires `payoff > 0` (i.e., the option is strictly in-the-money) to satisfy
    `Trade.executionPrice_pos`. -/
def Trade.settlementITM (opt : EuropeanOption) (currentQty payoff : Int)
    (h : payoff > 0) : Trade :=
  Trade.mk' opt.assetId (-currentQty) payoff 0 h (by omega)

/-- Remove a worthless (OTM) position from the portfolio.

    Erases the position and recomputes `portfolioValue` via `Portfolio.mk'`,
    so the portfolio value drops by exactly `pos.value`. -/
def Portfolio.abandonPosition (p : Portfolio) (id : AssetId) : Portfolio :=
  Portfolio.mk' p.cash (p.positions.erase id)

/-- Result of option settlement: either ITM (with a closing trade) or OTM. -/
inductive SettlementResult where
  | ITM (t : Trade)
  | OTM

/-- Determine settlement outcome given spot price and current quantity.

    - ITM: payoff > 0 → close with a `settlementITM` trade
    - OTM: payoff = 0 → abandon the position (no cash impact) -/
def EuropeanOption.settle (opt : EuropeanOption) (spot currentQty : Int) :
    SettlementResult :=
  let payoff := optionPayoff opt spot
  if h : payoff > 0 then
    .ITM (Trade.settlementITM opt currentQty payoff h)
  else
    .OTM

/-- Apply a settlement result to a portfolio.

    - ITM: call `applyTrade` with the closing trade
    - OTM: call `abandonPosition` to erase the worthless position -/
def applySettlement (p : Portfolio) (opt : EuropeanOption)
    (sr : SettlementResult) : Portfolio :=
  match sr with
  | .ITM t => applyTrade p t
  | .OTM   => p.abandonPosition opt.assetId

end OptionHedge
