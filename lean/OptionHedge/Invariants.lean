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
import Mathlib.Tactic

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

/-! ## Trade Invariants (v0.3) -/

/-- Fees are always non-negative (enforced by the `fee_nonneg` proof field on Trade). -/
theorem feeNonNegative (t : Trade) : t.fee ≥ 0 := t.fee_nonneg

/-- Applying a trade debits cash by `deltaQuantity * executionPrice + fee`. -/
theorem cashUpdateCorrect (p : Portfolio) (t : Trade) :
    (applyTrade p t).cash = p.cash - (t.deltaQuantity * t.executionPrice + t.fee) := rfl

/-! ### Helper lemmas for list arithmetic -/

/-- `foldl` with an additive offset can be factored out. -/
private theorem foldl_value_offset (c : Int) (ps : List Position) :
    List.foldl (fun acc p => acc + p.value) c ps =
    c + List.foldl (fun acc p => acc + p.value) 0 ps := by
  induction ps generalizing c with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl]
    have h1 := ih (c + h.value)
    have h2 := ih (0 + h.value)
    omega

/-- `sumPositionValues` expands at the head of a list. -/
private theorem sumPositionValues_cons (pos : Position) (ps : List Position) :
    sumPositionValues (pos :: ps) = pos.value + sumPositionValues ps := by
  simp only [sumPositionValues, List.foldl_cons]
  have := foldl_value_offset (0 + pos.value) ps
  omega

/-- `sumPositionValues` is additive over list concatenation. -/
private theorem sumPositionValues_append (ps qs : List Position) :
    sumPositionValues (ps ++ qs) = sumPositionValues ps + sumPositionValues qs := by
  simp only [sumPositionValues, List.foldl_append]
  exact foldl_value_offset (sumPositionValues ps) qs

/-- `sumPositionValues` of a singleton is the position's value. -/
private theorem sumPositionValues_singleton (pos : Position) :
    sumPositionValues [pos] = pos.value := by
  rw [sumPositionValues_cons]
  simp [sumPositionValues]

/-- Every element of `removePosition ps id` has a different asset. -/
private theorem removePosition_ne_id (ps : List Position) (id : AssetId)
    (q : Position) (hq : q ∈ removePosition ps id) : q.asset ≠ id := by
  simp only [removePosition, List.mem_filter, bne_iff_ne] at hq
  exact hq.2

/-- `find?` for the removed id returns `none` on the stripped list. -/
private theorem find?_removePosition_none (ps : List Position) (id : AssetId) :
    (removePosition ps id).find? (fun p => p.asset == id) = none := by
  apply List.find?_eq_none.mpr
  intro q hq
  have hne : q.asset ≠ id := removePosition_ne_id ps id q hq
  simp [beq_iff_eq, hne]

/-- `sumPositionValues` splits cleanly over the filter for an asset id. -/
private theorem sumPositionValues_filter_split (ps : List Position) (id : AssetId) :
    sumPositionValues ps =
    sumPositionValues (removePosition ps id) +
    sumPositionValues (ps.filter (fun p => p.asset == id)) := by
  induction ps with
  | nil => simp [sumPositionValues, removePosition]
  | cons h t ih =>
    rw [sumPositionValues_cons]
    by_cases hid : h.asset = id
    · -- h matches id: excluded from removePosition, included in filter
      have hbeq : (h.asset == id) = true  := beq_iff_eq.mpr hid
      have hbne : (h.asset != id) = false := by simp [hid]
      have hrm : removePosition (h :: t) id = removePosition t id := by
        simp [removePosition, hbne]
      have hfl : (h :: t).filter (fun p => p.asset == id) =
                 h :: t.filter (fun p => p.asset == id) := by
        simp [hbeq]
      rw [hrm, hfl, sumPositionValues_cons]
      omega
    · -- h does not match id: included in removePosition, excluded from filter
      have hbeq : (h.asset == id) = false := by simp [hid]
      have hbne : (h.asset != id) = true  := by simp [hid]
      have hrm : removePosition (h :: t) id = h :: removePosition t id := by
        simp [removePosition, hbne]
      have hfl : (h :: t).filter (fun p => p.asset == id) =
                 t.filter (fun p => p.asset == id) := by
        simp [hbeq]
      rw [hrm, hfl, sumPositionValues_cons]
      omega

/-! ### Quantity Conservation -/

/-- Applying a trade updates the position quantity correctly. -/
theorem quantityConservation (p : Portfolio) (t : Trade) :
    (applyTrade p t).getQuantity t.assetId =
    p.getQuantity t.assetId + t.deltaQuantity := by
  set newQty   := p.getQuantity t.assetId + t.deltaQuantity with hqdef
  set stripped := removePosition p.positions t.assetId
  -- The positions field after applyTrade is definitionally an if-then-else
  have hpos : (applyTrade p t).positions =
      if newQty = 0 then stripped
      else stripped ++ [⟨t.assetId, newQty, t.executionPrice, t.executionPrice_pos⟩] := rfl
  -- fact about stripped's find?
  have hfind : stripped.find? (fun p => p.asset == t.assetId) = none :=
    find?_removePosition_none p.positions t.assetId
  simp only [Portfolio.getQuantity, Portfolio.getPosition, hpos]
  split_ifs with h
  · -- newQty = 0: find? returns none → getQuantity = 0
    simp [hfind, h]
  · -- newQty ≠ 0: new position is appended, find? returns it
    rw [List.find?_append, hfind]
    simp

/-! ### Self-Financing -/

/-- When a trade executes at the existing mark price, NAV changes only by the fee.

    `hUniq` asserts that the position list has exactly one entry for the traded
    asset — the invariant maintained by `applyTrade` on properly-built portfolios. -/
theorem selfFinancing (p : Portfolio) (t : Trade) (pos : Position)
    (hPos  : p.getPosition t.assetId = some pos)
    (hPrice : t.executionPrice = pos.markPrice)
    (hUniq : p.positions.filter (fun q => q.asset == t.assetId) = [pos]) :
    (applyTrade p t).nav = p.nav - t.fee := by
  -- Step 1: p.getQuantity t.assetId = pos.quantity
  have hqty : p.getQuantity t.assetId = pos.quantity := by
    simp only [Portfolio.getQuantity, hPos]
  -- Step 2: decompose sumPositionValues p.positions
  have hsum : sumPositionValues p.positions =
      sumPositionValues (removePosition p.positions t.assetId) + pos.value := by
    have hsplit := sumPositionValues_filter_split p.positions t.assetId
    rw [hUniq] at hsplit
    linarith [sumPositionValues_singleton pos]
  -- Step 3: cash after trade
  have hcash : (applyTrade p t).cash = p.cash - (t.deltaQuantity * t.executionPrice + t.fee) := rfl
  -- Step 4: newQty = pos.quantity + deltaQuantity; newPositions
  set newQty   := p.getQuantity t.assetId + t.deltaQuantity with hqdef
  set stripped := removePosition p.positions t.assetId
  have hq : newQty = pos.quantity + t.deltaQuantity := by rw [hqdef, hqty]
  have hpositions : (applyTrade p t).positions =
      if newQty = 0 then stripped
      else stripped ++ [⟨t.assetId, newQty, t.executionPrice, t.executionPrice_pos⟩] := rfl
  -- Step 5: compute (applyTrade p t).nav
  have hnav : (applyTrade p t).nav =
      (applyTrade p t).cash + sumPositionValues (applyTrade p t).positions :=
    (applyTrade p t).nav_valid
  -- Step 6: case split on newQty = 0
  by_cases h : newQty = 0
  · -- newQty = 0: pos.quantity + deltaQuantity = 0, so pos.quantity = -deltaQuantity
    rw [hnav, hcash, p.nav_valid, hsum, hpositions, if_pos h]
    -- pos.value = pos.quantity * t.executionPrice (via hPrice)
    have hv : pos.value = pos.quantity * t.executionPrice := by
      simp [Position.value, hPrice]
    -- -deltaQuantity * executionPrice = pos.quantity * executionPrice
    have hq_neg : pos.quantity = -t.deltaQuantity := by omega
    have heq : pos.quantity * t.executionPrice = -t.deltaQuantity * t.executionPrice := by
      rw [hq_neg]
    linarith [hv, heq]
  · -- newQty ≠ 0: new position appended; sum expands by newQty * executionPrice
    rw [hnav, hcash, p.nav_valid, hsum, hpositions, if_neg h,
        sumPositionValues_append, sumPositionValues_singleton]
    -- singleton value = newQty * executionPrice
    have hnew : (⟨t.assetId, newQty, t.executionPrice, t.executionPrice_pos⟩ : Position).value =
        newQty * t.executionPrice := by simp [Position.value]
    rw [hnew]
    -- pos.value = pos.quantity * executionPrice (via hPrice)
    have hv : pos.value = pos.quantity * t.executionPrice := by
      simp [Position.value, hPrice]
    -- newQty * executionPrice = pos.quantity * executionPrice + deltaQuantity * executionPrice
    have hq_exp : newQty * t.executionPrice =
        pos.quantity * t.executionPrice + t.deltaQuantity * t.executionPrice := by
      rw [hq]; ring
    linarith [hv, hq_exp]

end OptionHedge
