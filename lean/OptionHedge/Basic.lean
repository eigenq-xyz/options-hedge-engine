/-
Copyright (c) 2026 Option Hedge Engine Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Karra
-/

/-!
# Basic Types

Core data structures for portfolio state representation.

This module defines:
- `Asset`: Asset identifiers
- `Position`: Asset holdings with quantities and prices
- `Portfolio`: Complete portfolio state including cash and positions

These types form the foundation of the verified accounting kernel.

## Numeric Conventions

All monetary values use **basis points** (×10,000) for exact decimal arithmetic:
- `markPrice`: Asset price in basis points (e.g., $50.25 = 502,500)
- `cash`: Portfolio cash in basis points
- `accruedInterest`: Interest in basis points

See OptionHedge.Numeric for detailed explanation.
-/

namespace OptionHedge

/-- Asset identifier -/
structure Asset where
  id : String
  deriving Repr, BEq, Hashable

/-- Type alias for asset identifiers -/
def AssetId := String

/-- Position in a single asset -/
structure Position where
  asset : Asset
  quantity : Int      -- Signed: positive = long, negative = short
  markPrice : Int     -- Price in basis points (×10,000)
  deriving Repr

/-- Portfolio state -/
structure Portfolio where
  cash : Int                  -- Cash in basis points (×10,000)
  positions : List Position
  accruedInterest : Int       -- Interest in basis points (×10,000)
  deriving Repr

end OptionHedge
