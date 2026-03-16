/-
  Formal Invariants

  Theorem statements for all portfolio accounting invariants.
  Proofs are implemented alongside each milestone (not deferred).

  With portfolio value as a stored field carrying a type-level proof (`value_valid`),
  the portfolio value identity is enforced by construction. Any function that returns
  a Portfolio must produce a valid proof, guaranteeing portfolio value correctness.
-/

import OptionHedge.Basic
import OptionHedge.Accounting
import Mathlib.Tactic

namespace OptionHedge

/-! ## Portfolio Value Identity -/

/-- Portfolio value equals cash plus sum of position values.

    Economic meaning: the portfolio's stated value is always consistent
    with its components — cash plus mark-to-market positions.  No hidden
    value can accumulate.  This holds for *every* `Portfolio` value, not
    just the ones tested; the proof covers all possible inputs.

    With portfolio value as a stored field, this is just the proof field
    itself. -/
theorem valueIdentity (p : Portfolio) :
    p.portfolioValue = p.cash + sumPositionValues p.positions :=
  p.value_valid

/-- The smart constructor computes portfolio value correctly -/
theorem mk'_value (cash : Int) (positions : Std.HashMap AssetId Position) :
    (Portfolio.mk' cash positions).portfolioValue = cash + sumPositionValues positions :=
  rfl

/-- An empty portfolio's value equals its cash -/
theorem empty_value (cash : Int) :
    (Portfolio.empty cash).portfolioValue = cash := by
  have h1 : (Portfolio.empty cash).portfolioValue =
      cash + sumPositionValues (∅ : Std.HashMap AssetId Position) := rfl
  have h2 : sumPositionValues (∅ : Std.HashMap AssetId Position) = 0 := by
    simp [sumPositionValues, Std.HashMap.fold_eq_foldl_toList]
  linarith

/-- Position value is quantity times mark price -/
theorem position_value_def (pos : Position) :
    pos.value = pos.quantity * pos.markPrice :=
  rfl

/-! ## Domain Constraints -/

/-- Mark prices must be positive.

    Economic meaning: no position can carry a zero or negative price —
    a defensive constraint that prevents division-by-zero and degenerate
    portfolios.  Enforced structurally: every `Position` must supply a
    `markPrice_pos : markPrice > 0` proof at construction time.

    Proved directly from the `markPrice_pos` field on Position — no axiom
    needed. -/
theorem pricesPositive (pos : Position) : pos.markPrice > 0 :=
  pos.markPrice_pos

/-! ## Trade Invariants -/

/-- Fees are always non-negative (enforced by the `fee_nonneg` proof field on Trade).

    Economic meaning: the engine cannot award rebates — transaction costs
    can only reduce portfolio value, never increase it.  A negative fee
    would be a hidden source of wealth; this theorem rules it out. -/
theorem feeNonNegative (t : Trade) : t.fee ≥ 0 := t.fee_nonneg

/-- Applying a trade debits cash by `deltaQuantity * executionPrice + fee`.

    Economic meaning: every dollar spent purchasing shares (or received
    from selling) flows through the cash balance.  There is no hidden
    source of funds.  Proved by `rfl` — the definition is the theorem. -/
theorem cashUpdateCorrect (p : Portfolio) (t : Trade) :
    (applyTrade p t).cash = p.cash - (t.deltaQuantity * t.executionPrice + t.fee) := rfl

/-! ### Helper lemmas for sumPositionValues and HashMap operations -/

/-- Shifting the foldl init by a constant shifts the result by the same constant. -/
private theorem foldl_val_shift (l : List (AssetId × Position)) (init : Int) :
    l.foldl (fun acc p => acc + p.2.value) init =
    l.foldl (fun acc p => acc + p.2.value) 0 + init := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (init + h.2.value), ih h.2.value]
    ring

/-- sumPositionValues is invariant under HashMap toList permutation. -/
private theorem sumPositionValues_of_toList_perm
    {m₁ m₂ : Std.HashMap AssetId Position} (h : m₁.toList.Perm m₂.toList) :
    sumPositionValues m₁ = sumPositionValues m₂ := by
  simp only [sumPositionValues, Std.HashMap.fold_eq_foldl_toList]
  exact h.foldl_eq' (f := fun acc p => acc + p.2.value)
    (comm := fun _ _ _ _ _ => by ring) 0

/-- Inserting a key (after erasing it) increases sumPositionValues by that position's value.
    Promoted to `protected` so downstream proofs can reference it by full qualified name. -/
protected theorem sumPositionValues_insert
    (m : Std.HashMap AssetId Position) (k : AssetId) (v : Position) :
    sumPositionValues ((m.erase k).insert k v) = sumPositionValues (m.erase k) + v.value := by
  simp only [sumPositionValues, Std.HashMap.fold_eq_foldl_toList]
  have hFilter : (m.erase k).toList.filter (fun p => !(k == p.1)) =
                 (m.erase k).toList := by
    apply List.filter_eq_self.mpr
    intro ⟨k', _⟩ hmem
    cases hbeq : (k == k') with
    | true =>
      have hEq : k = k' := LawfulBEq.eq_of_beq hbeq
      subst hEq
      exact absurd (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem)
        (by simp)
    | false => rfl
  have hPerm : ((m.erase k).insert k v).toList.Perm (⟨k, v⟩ :: (m.erase k).toList) := by
    have := Std.HashMap.toList_insert_perm (m := m.erase k) (k := k) (v := v)
    simp only [Bool.not_eq_true, Bool.decide_eq_false] at this
    rwa [hFilter] at this
  rw [hPerm.foldl_eq' (comm := fun _ _ _ _ _ => by ring) 0]
  simp only [List.foldl_cons, zero_add]
  rw [foldl_val_shift]

/-- Erasing a key reduces sumPositionValues by that position's value.
    Promoted to `protected` so downstream proofs can reference it by full qualified name. -/
protected theorem sumPositionValues_erase_of_mem
    (m : Std.HashMap AssetId Position) (k : AssetId) (v : Position)
    (h : m[k]? = some v) :
    sumPositionValues (m.erase k) = sumPositionValues m - v.value := by
  have hEquiv : Std.HashMap.Equiv ((m.erase k).insert k v) m := by
    apply Std.HashMap.Equiv.of_forall_getElem?_eq
    intro k'
    cases hk : (k == k') with
    | true =>
      have hEq : k = k' := LawfulBEq.eq_of_beq hk
      subst hEq
      simp [h]
    | false =>
      simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hk]
  have hEqSum : sumPositionValues ((m.erase k).insert k v) = sumPositionValues m :=
    sumPositionValues_of_toList_perm (Std.HashMap.Equiv.toList_perm hEquiv)
  linarith [OptionHedge.sumPositionValues_insert m k v]

/-- Erasing an absent key leaves sumPositionValues unchanged. -/
private theorem sumPositionValues_erase_of_not_mem
    (m : Std.HashMap AssetId Position) (k : AssetId)
    (h : m[k]? = none) :
    sumPositionValues (m.erase k) = sumPositionValues m := by
  apply sumPositionValues_of_toList_perm
  apply Std.HashMap.Equiv.toList_perm
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k'
  cases hk : (k == k') with
  | true =>
    have hEq : k = k' := LawfulBEq.eq_of_beq hk
    subst hEq
    simp [h]
  | false =>
    simp [Std.HashMap.getElem?_erase, hk]

/-! ### Quantity Conservation -/

/-- Applying a trade updates the position quantity correctly.

    Economic meaning: shares cannot appear from thin air or silently
    disappear after a trade.  The post-trade quantity equals the
    pre-trade quantity plus `deltaQuantity`, for every possible prior
    state and every possible trade size. -/
theorem quantityConservation (p : Portfolio) (t : Trade) :
    (applyTrade p t).getQuantity t.assetId =
    p.getQuantity t.assetId + t.deltaQuantity := by
  have hEq : (applyTrade p t).positions =
      if p.getQuantity t.assetId + t.deltaQuantity = 0 then
        p.positions.erase t.assetId
      else
        (p.positions.erase t.assetId).insert t.assetId
          ⟨t.assetId, p.getQuantity t.assetId + t.deltaQuantity,
           t.executionPrice, t.executionPrice_pos⟩ := rfl
  by_cases hQty : p.getQuantity t.assetId + t.deltaQuantity = 0
  · have hPos : (applyTrade p t).positions = p.positions.erase t.assetId := by
      rw [hEq, if_pos hQty]
    simp only [Portfolio.getQuantity, Portfolio.getPosition, hPos,
               Std.HashMap.getElem?_erase_self]
    simp only [Portfolio.getQuantity, Portfolio.getPosition] at hQty
    omega
  · have hPos : (applyTrade p t).positions =
        (p.positions.erase t.assetId).insert t.assetId
          ⟨t.assetId, p.getQuantity t.assetId + t.deltaQuantity,
           t.executionPrice, t.executionPrice_pos⟩ := by
      rw [hEq, if_neg hQty]
    simp only [Portfolio.getQuantity, Portfolio.getPosition, hPos,
               Std.HashMap.getElem?_insert_self]

/-! ### Portfolio Value Update Formula -/

/-- Portfolio value update formula.

    Economic meaning: when you trade an asset, the change in portfolio value equals
    the mark-to-market gain on your *existing* position (quantity × price improvement)
    minus the fee. A brand-new position (qty = 0 before) contributes zero MTM gain.
    This formalizes that trading at a price above your mark creates immediate paper profit. -/
theorem valueUpdateFormula (p : Portfolio) (t : Trade) :
    (applyTrade p t).portfolioValue =
    p.portfolioValue + p.getQuantity t.assetId * (t.executionPrice - p.getMarkPrice_orZero t.assetId)
          - t.fee := by
  rw [valueIdentity (applyTrade p t), valueIdentity p, cashUpdateCorrect]
  suffices h : sumPositionValues (applyTrade p t).positions =
      sumPositionValues p.positions +
      p.getQuantity t.assetId * (t.executionPrice - p.getMarkPrice_orZero t.assetId) +
      t.deltaQuantity * t.executionPrice by linarith
  have hApply : (applyTrade p t).positions =
      if p.getQuantity t.assetId + t.deltaQuantity = 0 then p.positions.erase t.assetId
      else (p.positions.erase t.assetId).insert t.assetId
            ⟨t.assetId, p.getQuantity t.assetId + t.deltaQuantity,
             t.executionPrice, t.executionPrice_pos⟩ := rfl
  rw [hApply]
  by_cases hQty : p.getQuantity t.assetId + t.deltaQuantity = 0
  · -- newQty = 0: position erased
    rw [if_pos hQty]
    cases hLookup : p.positions[t.assetId]? with
    | none =>
      have hGetQty : p.getQuantity t.assetId = 0 := by
        simp [Portfolio.getQuantity, Portfolio.getPosition, hLookup]
      have hGetMark : p.getMarkPrice_orZero t.assetId = 0 := by
        simp [Portfolio.getMarkPrice_orZero, Portfolio.getPosition, hLookup]
      have hDelta : t.deltaQuantity = 0 := by linarith [hGetQty ▸ hQty]
      rw [hGetQty, hGetMark, hDelta, sumPositionValues_erase_of_not_mem _ _ hLookup]
      ring
    | some pos =>
      have hGetQty : p.getQuantity t.assetId = pos.quantity := by
        simp [Portfolio.getQuantity, Portfolio.getPosition, hLookup]
      have hGetMark : p.getMarkPrice_orZero t.assetId = pos.markPrice := by
        simp [Portfolio.getMarkPrice_orZero, Portfolio.getPosition, hLookup]
      have hDelta : t.deltaQuantity = -pos.quantity := by
        have := hGetQty ▸ hQty; omega
      rw [hGetQty, hGetMark, hDelta,
          OptionHedge.sumPositionValues_erase_of_mem _ _ _ hLookup]
      simp only [Position.value]
      ring
  · -- newQty ≠ 0: position inserted
    rw [if_neg hQty]
    cases hLookup : p.positions[t.assetId]? with
    | none =>
      have hGetQty : p.getQuantity t.assetId = 0 := by
        simp [Portfolio.getQuantity, Portfolio.getPosition, hLookup]
      have hGetMark : p.getMarkPrice_orZero t.assetId = 0 := by
        simp [Portfolio.getMarkPrice_orZero, Portfolio.getPosition, hLookup]
      rw [hGetQty, hGetMark,
          OptionHedge.sumPositionValues_insert,
          sumPositionValues_erase_of_not_mem _ _ hLookup]
      simp only [Position.value]
      ring
    | some pos =>
      have hGetQty : p.getQuantity t.assetId = pos.quantity := by
        simp [Portfolio.getQuantity, Portfolio.getPosition, hLookup]
      have hGetMark : p.getMarkPrice_orZero t.assetId = pos.markPrice := by
        simp [Portfolio.getMarkPrice_orZero, Portfolio.getPosition, hLookup]
      rw [hGetQty, hGetMark,
          OptionHedge.sumPositionValues_insert,
          OptionHedge.sumPositionValues_erase_of_mem _ _ _ hLookup]
      simp only [Position.value]
      ring

/-! ### Self-Financing -/

/-- Self-financing property: when a trade executes at the existing mark price,
    portfolio value changes only by the fee.

    Economic meaning: buying or selling at today's mark price is a "fair" trade —
    no value is created or destroyed, only the transaction fee is paid. -/
theorem selfFinancing (p : Portfolio) (t : Trade) (pos : Position)
    (hPos  : p.getPosition t.assetId = some pos)
    (hPrice : t.executionPrice = pos.markPrice) :
    (applyTrade p t).portfolioValue = p.portfolioValue - t.fee := by
  rw [valueUpdateFormula]
  have hMark : p.getMarkPrice_orZero t.assetId = pos.markPrice := by
    simp [Portfolio.getMarkPrice_orZero, hPos]
  rw [hMark, hPrice]
  ring

/-! ## Well-Formedness Invariants (v0.3.2) -/

/-- An empty portfolio is well-formed: no positions, so the condition is vacuously true. -/
theorem empty_wellFormed (cash : Int) : (Portfolio.empty cash).WellFormed := by
  intro id pos h
  have hEmpty : (Portfolio.empty cash).positions = {} := rfl
  rw [hEmpty] at h
  simp at h

/-- `applyTrade` preserves well-formedness: it erases positions that reach zero quantity
    and only inserts positions with non-zero quantity. -/
theorem applyTrade_wellFormed (p : Portfolio) (t : Trade) (hw : p.WellFormed) :
    (applyTrade p t).WellFormed := by
  intro id pos hLookup
  have hPositions : (applyTrade p t).positions =
      if p.getQuantity t.assetId + t.deltaQuantity = 0 then p.positions.erase t.assetId
      else (p.positions.erase t.assetId).insert t.assetId
            ⟨t.assetId, p.getQuantity t.assetId + t.deltaQuantity,
             t.executionPrice, t.executionPrice_pos⟩ := rfl
  by_cases hQty : p.getQuantity t.assetId + t.deltaQuantity = 0
  · -- Positions = p.positions.erase t.assetId
    rw [hPositions, if_pos hQty] at hLookup
    by_cases hId : id = t.assetId
    · -- id = t.assetId: erased — contradiction
      subst hId
      simp at hLookup
    · -- id ≠ t.assetId: falls through to p.positions
      have hbeq : (t.assetId == id) = false := by
        cases h : (t.assetId == id) with
        | true => exact absurd (LawfulBEq.eq_of_beq h) (Ne.symm hId)
        | false => rfl
      rw [show (p.positions.erase t.assetId)[id]? = p.positions[id]? from by
        simp [Std.HashMap.getElem?_erase, hbeq]] at hLookup
      exact hw id pos hLookup
  · -- Positions = (p.positions.erase t.assetId).insert t.assetId newPos
    rw [hPositions, if_neg hQty] at hLookup
    by_cases hId : id = t.assetId
    · -- id = t.assetId: new position has quantity = newQty ≠ 0
      subst hId
      simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hLookup
      subst hLookup
      exact hQty
    · -- id ≠ t.assetId: falls through insert and erase to p.positions
      have hbeq : (t.assetId == id) = false := by
        cases h : (t.assetId == id) with
        | true => exact absurd (LawfulBEq.eq_of_beq h) (Ne.symm hId)
        | false => rfl
      rw [show ((p.positions.erase t.assetId).insert t.assetId _)[id]? = p.positions[id]? from by
        simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hbeq]] at hLookup
      exact hw id pos hLookup

end OptionHedge
