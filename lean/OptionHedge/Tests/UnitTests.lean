/-
Copyright (c) 2026 Option Hedge Engine Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Karra
-/

import OptionHedge.Basic
import OptionHedge.Accounting

/-!
# Unit Tests

Concrete tests for portfolio types, NAV calculation, and position lookup.
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

end OptionHedge.Tests
