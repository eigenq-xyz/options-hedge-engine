/-
  Accounting FFI Exports

  C-callable wrappers for the core accounting functions defined in Basic.lean.
  All exported symbols use the `hedge_` prefix to avoid C namespace collisions.

  Numeric Convention: All Int values representing money use basis points
  (×10,000 for 4 decimal places). Example: $123.4567 = 1,234,567 basis points.
-/

import OptionHedge.Basic
import OptionHedge.Options

namespace OptionHedge

/-- FFI: Calculate the market value of a single position -/
@[export hedge_position_value]
def positionValueFFI (pos : Position) : Int :=
  pos.value

/-- FFI: Sum all position values in a portfolio -/
@[export hedge_sum_position_values]
def sumPositionValuesFFI (p : Portfolio) : Int :=
  sumPositionValues p.positions

/-- FFI: Get the portfolio value (O(1) field access) -/
@[export hedge_portfolio_value]
def portfolioValueFFI (p : Portfolio) : Int :=
  p.portfolioValue

/-- FFI: Construct a portfolio from cash and positions (takes List, converts to HashMap) -/
@[export hedge_mk_portfolio]
def mkPortfolioFFI (cash : Int) (positions : List Position) : Portfolio :=
  Portfolio.mkFromList cash positions

/-- FFI: Look up a position by asset ID -/
@[export hedge_get_position]
def getPositionFFI (p : Portfolio) (id : AssetId) : Option Position :=
  p.getPosition id

/-- FFI: Apply a trade to a portfolio -/
@[export hedge_apply_trade]
def applyTradeFFI (p : Portfolio) (t : Trade) : Portfolio :=
  applyTrade p t

/-- FFI: Convert portfolio positions to a List for Python -/
@[export hedge_portfolio_positions_to_list]
def portfolioPositionsToListFFI (p : Portfolio) : List Position :=
  p.positionsToList

/-- FFI: Compute option payoff given spot price -/
@[export hedge_option_payoff]
def optionPayoffFFI (opt : EuropeanOption) (spot : Int) : Int :=
  optionPayoff opt spot

/-- FFI: Settle an option position; returns portfolio unchanged if position absent -/
@[export hedge_settle_option]
def settleOptionFFI (p : Portfolio) (opt : EuropeanOption) (spot : Int) : Portfolio :=
  match p.getPosition opt.assetId with
  | none     => p   -- no position to settle
  | some pos => applySettlement p opt (opt.settle spot pos.quantity)

end OptionHedge
