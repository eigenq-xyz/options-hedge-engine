/-
Copyright (c) 2026 Option Hedge Engine Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Karra
-/

/-!
# Basic Types

Core data structures for portfolio state representation.

This module defines:
- `AssetId`: Asset identifier (string alias)
- `Position`: Asset holdings with quantities and prices
- `Portfolio`: Complete portfolio state with type-level NAV invariant
- `Trade`: A single trade with type-level price/fee invariants
- `applyTrade`: Apply a trade to a portfolio (returns a new valid Portfolio)

These types form the foundation of the verified accounting kernel.

## Numeric Conventions

All monetary values use **basis points** (×10,000) for exact decimal arithmetic:
- `markPrice`: Asset price in basis points (e.g., $50.25 = 502,500)
- `cash`: Portfolio cash in basis points
-/

namespace OptionHedge

/-- Type alias for asset identifiers -/
abbrev AssetId := String

/-- Position in a single asset.

The `markPrice_pos` field is a proof that `markPrice > 0`,
making it impossible to construct a Position with a non-positive price. -/
structure Position where
  asset : AssetId
  quantity : Int      -- Signed: positive = long, negative = short
  markPrice : Int     -- Price in basis points (×10,000)
  markPrice_pos : markPrice > 0
  deriving DecidableEq

instance : BEq Position := ⟨fun a b => decide (a = b)⟩

instance : Repr Position where
  reprPrec p _ :=
    s!"Position(asset := {repr p.asset}, quantity := {repr p.quantity}, markPrice := {repr p.markPrice})"

instance : Inhabited Position where
  default := ⟨"", 0, 1, by omega⟩

/-- Smart constructor: builds a Position with price proved positive.
    The proof is auto-discharged by `omega` for concrete positive literals. -/
def Position.mk' (asset : AssetId) (quantity : Int) (markPrice : Int)
    (h : markPrice > 0 := by omega) : Position :=
  ⟨asset, quantity, markPrice, h⟩

/-- Calculate the market value of a single position -/
@[inline]
def Position.value (pos : Position) : Int :=
  pos.quantity * pos.markPrice

/-- Calculate total value of a list of positions -/
def sumPositionValues (positions : List Position) : Int :=
  positions.foldl (fun acc pos => acc + pos.value) 0

/-- Portfolio state with type-level NAV invariant.

The `nav_valid` field is a proof that `nav = cash + sumPositionValues positions`,
making it impossible to construct a Portfolio with an incorrect NAV. -/
structure Portfolio where
  cash : Int
  positions : List Position
  nav : Int
  nav_valid : nav = cash + sumPositionValues positions

instance : Repr Portfolio where
  reprPrec p _ :=
    s!"Portfolio(cash := {repr p.cash}, positions := {repr p.positions}, nav := {repr p.nav})"

/-- Smart constructor: builds a Portfolio with NAV computed and proved correct. -/
def Portfolio.mk' (cash : Int) (positions : List Position) : Portfolio :=
  { cash := cash
    positions := positions
    nav := cash + sumPositionValues positions
    nav_valid := rfl }

/-- Convenience: empty portfolio with given cash -/
def Portfolio.empty (cash : Int) : Portfolio :=
  Portfolio.mk' cash []

/-- Look up a position by asset ID -/
def Portfolio.getPosition (p : Portfolio) (id : AssetId) : Option Position :=
  p.positions.find? (fun pos => pos.asset == id)

/-- Get the held quantity for an asset (0 if not in portfolio) -/
def Portfolio.getQuantity (p : Portfolio) (id : AssetId) : Int :=
  match p.getPosition id with
  | some pos => pos.quantity
  | none     => 0

/-- Remove all positions matching the given asset ID -/
def removePosition (positions : List Position) (id : AssetId) : List Position :=
  positions.filter (fun pos => pos.asset != id)

/-- A single trade instruction.

The `executionPrice_pos` field proves `executionPrice > 0` and
`fee_nonneg` proves `fee ≥ 0`, making invalid trades unrepresentable. -/
structure Trade where
  assetId        : AssetId
  deltaQuantity  : Int    -- Signed: positive = buy, negative = sell
  executionPrice : Int    -- Price in basis points (×10,000)
  fee            : Int    -- Transaction cost in basis points (≥ 0)
  executionPrice_pos : executionPrice > 0
  fee_nonneg         : fee ≥ 0
  deriving DecidableEq

instance : BEq Trade := ⟨fun a b => decide (a = b)⟩

instance : Repr Trade where
  reprPrec t _ :=
    s!"Trade(assetId := {repr t.assetId}, deltaQuantity := {repr t.deltaQuantity}, \
executionPrice := {repr t.executionPrice}, fee := {repr t.fee})"

instance : Inhabited Trade where
  default := ⟨"", 0, 1, 0, by omega, by omega⟩

/-- Smart constructor: builds a Trade with price and fee proved valid.
    Both proofs are auto-discharged by `omega` for concrete literals. -/
def Trade.mk' (assetId : AssetId) (deltaQuantity : Int) (executionPrice : Int) (fee : Int)
    (hp : executionPrice > 0 := by omega) (hf : fee ≥ 0 := by omega) : Trade :=
  ⟨assetId, deltaQuantity, executionPrice, fee, hp, hf⟩

/-- Apply a trade to a portfolio, returning an updated Portfolio.

    Semantics:
    - The position for `t.assetId` is updated: new quantity = old + deltaQuantity,
      new markPrice = executionPrice.  If the new quantity is zero, the position
      is removed entirely.
    - Cash is debited: new cash = old cash - (deltaQuantity * executionPrice + fee).
    - NAV is recomputed by `Portfolio.mk'`, so `nav_valid` holds by `rfl`. -/
def applyTrade (p : Portfolio) (t : Trade) : Portfolio :=
  let newQty   := p.getQuantity t.assetId + t.deltaQuantity
  let newCash  := p.cash - (t.deltaQuantity * t.executionPrice + t.fee)
  let stripped := removePosition p.positions t.assetId
  let newPositions :=
    if newQty = 0 then stripped
    else stripped ++ [⟨t.assetId, newQty, t.executionPrice, t.executionPrice_pos⟩]
  Portfolio.mk' newCash newPositions

end OptionHedge
