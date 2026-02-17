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

end OptionHedge
