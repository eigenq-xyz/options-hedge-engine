/-
  Accounting Functions

  Core portfolio accounting: NAV calculation, trade application, cash accrual.
  These functions are intentionally simple in v0.1 and will be proven correct in v0.3-v0.4.

  Numeric Convention: All Int values representing money use basis points
  (×10,000 for 4 decimal places). Example: $123.4567 = 1,234,567 basis points.
-/

import OptionHedge.Basic

namespace OptionHedge

/-- Calculate the market value of a single position -/
@[export position_value]
def Position.value (pos : Position) : Int :=
  pos.quantity * pos.markPrice

/-- Calculate total value of all positions -/
@[export sum_position_values]
def sumPositionValues (positions : List Position) : Int :=
  positions.foldl (fun acc pos => acc + pos.value) 0

/-- Calculate Net Asset Value (NAV) of portfolio
    NAV = cash + Σ(position values) -/
@[export calc_nav]
def calcNAV (p : Portfolio) : Int :=
  p.cash + sumPositionValues p.positions

/-- Apply a single trade to portfolio (simplified for v0.1)
    Updates position quantity and deducts cash -/
def applyTrade (p : Portfolio) (t : Trade) : Portfolio :=
  sorry  -- Implementation in v0.4

/-- Apply multiple trades sequentially -/
def applyTrades (p : Portfolio) (trades : List Trade) : Portfolio :=
  trades.foldl applyTrade p

/-- Accrue interest on cash balance (simplified for v0.1) -/
def accrueInterest (p : Portfolio) (rate : Int) : Portfolio :=
  sorry  -- Implementation in v0.4

end OptionHedge
