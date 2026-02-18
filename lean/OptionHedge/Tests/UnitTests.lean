/-
Copyright (c) 2026 Option Hedge Engine Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Karra
-/

import OptionHedge.Basic
import OptionHedge.Accounting

/-!
# Unit Tests

Concrete tests for portfolio types, NAV calculation, position lookup, and trade application.
-/

namespace OptionHedge.Tests

/-! ## Empty portfolio -/

example : (Portfolio.empty 1000000).cash = 1000000 := rfl
example : (Portfolio.empty 1000000).nav = 1000000 := rfl
example : (Portfolio.empty 1000000).positions = [] := rfl

/-! ## Position value -/

-- SPY: 100 shares at $50.00 (500,000 bp) = $5,000.00 (50,000,000 bp)
example : (Position.mk' "SPY" 100 500000).value = 50000000 := by native_decide

-- Short position: -50 shares at $180.00 = -$9,000.00
example : (Position.mk' "AAPL" (-50) 1800000).value = -90000000 := by native_decide

/-! ## Portfolio with positions -/

private def testPositions : List Position :=
  [ Position.mk' "SPY" 100 500000
  , Position.mk' "AAPL" 50 1800000 ]

-- Sum of position values: 50,000,000 + 90,000,000 = 140,000,000 bp
example : sumPositionValues testPositions = 140000000 := by native_decide

-- NAV = cash + positions = 1,000,000 + 140,000,000 = 141,000,000 bp
example : (Portfolio.mk' 1000000 testPositions).nav = 141000000 := by native_decide

/-! ## Position lookup -/

example : ((Portfolio.mk' 0 testPositions).getPosition "SPY").isSome = true := by native_decide

example : ((Portfolio.mk' 0 testPositions).getPosition "SPY").get! =
    Position.mk' "SPY" 100 500000 := by native_decide

example : ((Portfolio.mk' 0 testPositions).getPosition "TSLA").isNone = true := by native_decide

/-! ## Trade application -/

-- Starting portfolio: $100 cash, 100 SPY @ $50, 50 AAPL @ $180.
-- All prices in basis points (×10,000).
-- NAV = 1,000,000 + 50,000,000 + 90,000,000 = 141,000,000 bp
private def testPortfolio : Portfolio :=
  Portfolio.mk' 1000000 testPositions

example : testPortfolio.nav = 141000000 := by native_decide

/-! ### Buy more SPY (existing position, at-market price) -/

-- Buy 10 SPY at $50.00 (500,000 bp), fee = $10 (100,000 bp)
private def tradeBuySPY : Trade := Trade.mk' "SPY" 10 500000 100000

-- Quantity increases from 100 to 110
example : (applyTrade testPortfolio tradeBuySPY).getQuantity "SPY" = 110 := by native_decide

-- Cash debited by 10 * 500,000 + 100,000 = 5,100,000
example : (applyTrade testPortfolio tradeBuySPY).cash = -4100000 := by native_decide

-- NAV decreases only by the fee (at-market trade)
example : (applyTrade testPortfolio tradeBuySPY).nav = 140900000 := by native_decide

/-! ### Open new position (buy TSLA, zero fee) -/

-- Buy 20 TSLA at $200.00 (2,000,000 bp), fee = 0
private def tradeOpenTSLA : Trade := Trade.mk' "TSLA" 20 2000000 0

-- New position created with correct quantity
example : (applyTrade testPortfolio tradeOpenTSLA).getQuantity "TSLA" = 20 := by native_decide

-- Cash debited by 20 * 2,000,000 = 40,000,000
example : (applyTrade testPortfolio tradeOpenTSLA).cash = -39000000 := by native_decide

-- NAV unchanged (zero fee, at-market price)
example : (applyTrade testPortfolio tradeOpenTSLA).nav = testPortfolio.nav := by native_decide

/-! ### Close position (sell all AAPL, at-market price) -/

-- Sell 50 AAPL at $180.00 (1,800,000 bp), fee = $5 (50,000 bp)
private def tradeCloseAAPL : Trade := Trade.mk' "AAPL" (-50) 1800000 50000

-- Position removed when quantity reaches zero
example : (applyTrade testPortfolio tradeCloseAAPL).getPosition "AAPL" = none := by native_decide
example : (applyTrade testPortfolio tradeCloseAAPL).getQuantity "AAPL" = 0 := by native_decide

-- Cash credited by 50 * 1,800,000 less fee: 1,000,000 + 90,000,000 - 50,000 = 90,950,000
example : (applyTrade testPortfolio tradeCloseAAPL).cash = 90950000 := by native_decide

-- NAV decreases only by the fee
example : (applyTrade testPortfolio tradeCloseAAPL).nav =
    testPortfolio.nav - 50000 := by native_decide

end OptionHedge.Tests
