/-
  Accounting FFI Exports

  C-callable wrappers for the core accounting functions defined in Basic.lean.
  All exported symbols use the `hedge_` prefix to avoid C namespace collisions.

  Numeric Convention: All Int values representing money use basis points
  (×10,000 for 4 decimal places). Example: $123.4567 = 1,234,567 basis points.
-/

import OptionHedge.Basic

namespace OptionHedge

/-- FFI: Calculate the market value of a single position -/
@[export hedge_position_value]
def positionValueFFI (pos : Position) : Int :=
  pos.value

/-- FFI: Sum all position values in a portfolio -/
@[export hedge_sum_position_values]
def sumPositionValuesFFI (p : Portfolio) : Int :=
  sumPositionValues p.positions

/-- FFI: Get the NAV of a portfolio (O(1) field access) -/
@[export hedge_portfolio_nav]
def calcNavFFI (p : Portfolio) : Int :=
  p.nav

/-- FFI: Construct a portfolio from cash and positions -/
@[export hedge_mk_portfolio]
def mkPortfolioFFI (cash : Int) (positions : List Position) : Portfolio :=
  Portfolio.mk' cash positions

/-- FFI: Look up a position by asset ID -/
@[export hedge_get_position]
def getPositionFFI (p : Portfolio) (id : AssetId) : Option Position :=
  p.getPosition id

/-- FFI: Apply a trade to a portfolio -/
@[export hedge_apply_trade]
def applyTradeFFI (p : Portfolio) (t : Trade) : Portfolio :=
  applyTrade p t

end OptionHedge
