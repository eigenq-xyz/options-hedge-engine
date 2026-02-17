/-
  Formal Invariants

  Theorem statements for all portfolio accounting invariants.
  Proofs are implemented alongside each milestone (not deferred).

  With NAV as a stored field carrying a type-level proof (`nav_valid`),
  the NAV identity is enforced by construction. Any function that returns
  a Portfolio must produce a valid proof, guaranteeing NAV correctness.
-/

import OptionHedge.Basic
import OptionHedge.Accounting

namespace OptionHedge

/-! ## NAV Identity -/

/-- NAV equals cash plus sum of position values.
With NAV as a stored field, this is just the proof field itself. -/
theorem navIdentity (p : Portfolio) :
    p.nav = p.cash + sumPositionValues p.positions :=
  p.nav_valid

/-- The smart constructor computes NAV correctly -/
theorem mk'_nav (cash : Int) (positions : List Position) :
    (Portfolio.mk' cash positions).nav = cash + sumPositionValues positions :=
  rfl

/-- An empty portfolio's NAV equals its cash -/
theorem empty_nav (cash : Int) :
    (Portfolio.empty cash).nav = cash := by
  simp [Portfolio.empty, Portfolio.mk', sumPositionValues, List.foldl]

/-- Position value is quantity times mark price -/
theorem position_value_def (pos : Position) :
    pos.value = pos.quantity * pos.markPrice :=
  rfl

/-! ## Domain Constraints -/

/-- Mark prices must be positive.
Proved directly from the `markPrice_pos` field on Position — no axiom needed. -/
theorem pricesPositive (pos : Position) : pos.markPrice > 0 :=
  pos.markPrice_pos

/-
## Future Theorems (v0.3+)

When Trade type is defined, the following will be proved.
Critically, since applyTrade must return a Portfolio (which carries
nav_valid), NAV correctness is enforced by the type system.

theorem quantityConservation (p : Portfolio) (t : Trade) :
  let p' := applyTrade p t
  p'.getQuantity t.assetId = p.getQuantity t.assetId + t.deltaQuantity

theorem cashUpdateCorrect (p : Portfolio) (t : Trade) :
  let p' := applyTrade p t
  p'.cash = p.cash - (t.deltaQuantity * t.executionPrice + t.fee)

theorem selfFinancing (p : Portfolio) (t : Trade)
  (h : t.executionPrice = markPrice) :
  let p' := applyTrade p t
  p'.nav = p.nav - t.fee

theorem feeNonNegative (t : Trade) : t.fee ≥ 0
-/

end OptionHedge
