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
theorem mk'_nav (cash : Int) (positions : Std.HashMap AssetId Position) :
    (Portfolio.mk' cash positions).nav = cash + sumPositionValues positions :=
  rfl

/-- An empty portfolio's NAV equals its cash -/
theorem empty_nav (cash : Int) :
    (Portfolio.empty cash).nav = cash := by
  -- nav = cash + sumPositionValues {} by rfl; fold over empty list = 0
  have h1 : (Portfolio.empty cash).nav =
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
Proved directly from the `markPrice_pos` field on Position — no axiom needed. -/
theorem pricesPositive (pos : Position) : pos.markPrice > 0 :=
  pos.markPrice_pos

/-! ## Trade Invariants (v0.3) -/

/-- Fees are always non-negative (enforced by the `fee_nonneg` proof field on Trade). -/
theorem feeNonNegative (t : Trade) : t.fee ≥ 0 := t.fee_nonneg

/-- Applying a trade debits cash by `deltaQuantity * executionPrice + fee`. -/
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
    Uses toList_insert_perm: k ∉ m.erase k so filter (¬k==·) = id on its toList. -/
private theorem sumPositionValues_insert
    (m : Std.HashMap AssetId Position) (k : AssetId) (v : Position) :
    sumPositionValues ((m.erase k).insert k v) = sumPositionValues (m.erase k) + v.value := by
  simp only [sumPositionValues, Std.HashMap.fold_eq_foldl_toList]
  -- k is absent from (m.erase k), so the filter in toList_insert_perm is identity
  have hFilter : (m.erase k).toList.filter (fun p => !(k == p.1)) =
                 (m.erase k).toList := by
    apply List.filter_eq_self.mpr
    intro ⟨k', _⟩ hmem
    -- If k == k', then k = k', but (m.erase k)[k]? = none — contradiction
    cases hbeq : (k == k') with
    | true =>
      have hEq : k = k' := LawfulBEq.eq_of_beq hbeq
      subst hEq
      exact absurd (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem)
        (by simp)  -- getElem?_erase_self is @[simp]; simp closes the ⊢ ¬ none = some _ goal
    | false => rfl
  -- toList_insert_perm gives the perm; simplify away the filter
  have hPerm : ((m.erase k).insert k v).toList.Perm (⟨k, v⟩ :: (m.erase k).toList) := by
    have := Std.HashMap.toList_insert_perm (m := m.erase k) (k := k) (v := v)
    -- ¬k == ·.1 elaborates as decide(¬(b=true)); normalize to !(k==·.1)
    simp only [Bool.not_eq_true, Bool.decide_eq_false] at this
    rwa [hFilter] at this
  -- Apply foldl_eq' and reduce the cons
  rw [hPerm.foldl_eq' (comm := fun _ _ _ _ _ => by ring) 0]
  simp only [List.foldl_cons, zero_add]
  rw [foldl_val_shift]

/-- Erasing a key reduces sumPositionValues by that position's value.
    Uses: (m.erase k).insert k v ~m m (by Equiv.of_forall_getElem?_eq),
    giving equal foldl; combined with sumPositionValues_insert. -/
private theorem sumPositionValues_erase_of_mem
    (m : Std.HashMap AssetId Position) (k : AssetId) (v : Position)
    (h : m[k]? = some v) :
    sumPositionValues (m.erase k) = sumPositionValues m - v.value := by
  -- (m.erase k).insert k v agrees with m on every key lookup
  -- grind applies getElem?_insert and getElem?_erase (@[grind =]), case-splits on k==k',
  -- and uses h : m[k]? = some v + LawfulBEq to close both branches.
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
  -- Therefore their toList are permutations → equal sumPositionValues
  have hEqSum : sumPositionValues ((m.erase k).insert k v) = sumPositionValues m :=
    sumPositionValues_of_toList_perm (Std.HashMap.Equiv.toList_perm hEquiv)
  linarith [sumPositionValues_insert m k v]

/-! ### Quantity Conservation -/

/-- Applying a trade updates the position quantity correctly. -/
theorem quantityConservation (p : Portfolio) (t : Trade) :
    (applyTrade p t).getQuantity t.assetId =
    p.getQuantity t.assetId + t.deltaQuantity := by
  -- applyTrade builds positions via erase then conditional insert
  have hEq : (applyTrade p t).positions =
      if p.getQuantity t.assetId + t.deltaQuantity = 0 then
        p.positions.erase t.assetId
      else
        (p.positions.erase t.assetId).insert t.assetId
          ⟨t.assetId, p.getQuantity t.assetId + t.deltaQuantity,
           t.executionPrice, t.executionPrice_pos⟩ := rfl
  -- Case split before simp to avoid unfolding Portfolio.getQuantity inside the if-condition
  by_cases hQty : p.getQuantity t.assetId + t.deltaQuantity = 0
  · -- quantity is zero: position erased, getElem? returns none → getQuantity = 0
    have hPos : (applyTrade p t).positions = p.positions.erase t.assetId := by
      rw [hEq, if_pos hQty]
    simp only [Portfolio.getQuantity, Portfolio.getPosition, hPos,
               Std.HashMap.getElem?_erase_self]
    -- hQty still uses p.getQuantity; unfold it to match the match-expression in the goal
    simp only [Portfolio.getQuantity, Portfolio.getPosition] at hQty
    omega
  · -- quantity non-zero: position inserted, getElem? returns some new position
    have hPos : (applyTrade p t).positions =
        (p.positions.erase t.assetId).insert t.assetId
          ⟨t.assetId, p.getQuantity t.assetId + t.deltaQuantity,
           t.executionPrice, t.executionPrice_pos⟩ := by
      rw [hEq, if_neg hQty]
    simp only [Portfolio.getQuantity, Portfolio.getPosition, hPos,
               Std.HashMap.getElem?_insert_self]

/-! ### Self-Financing -/

/-- When a trade executes at the existing mark price, NAV changes only by the fee. -/
theorem selfFinancing (p : Portfolio) (t : Trade) (pos : Position)
    (hPos  : p.getPosition t.assetId = some pos)
    (hPrice : t.executionPrice = pos.markPrice) :
    (applyTrade p t).nav = p.nav - t.fee := by
  have hLookup : p.positions[t.assetId]? = some pos := hPos
  -- Extract quantity from the looked-up position
  have hGetQty : p.getQuantity t.assetId = pos.quantity := by
    simp [Portfolio.getQuantity, Portfolio.getPosition, hLookup]
  -- Rewrite both NAVs using the stored nav_valid proofs
  rw [navIdentity (applyTrade p t), navIdentity p, cashUpdateCorrect, hPrice]
  -- It suffices to show sumPositionValues changes by exactly deltaQuantity * markPrice
  suffices h : sumPositionValues (applyTrade p t).positions =
               sumPositionValues p.positions + t.deltaQuantity * pos.markPrice by linarith
  have hPos' : (applyTrade p t).positions =
      if p.getQuantity t.assetId + t.deltaQuantity = 0 then
        p.positions.erase t.assetId
      else
        (p.positions.erase t.assetId).insert t.assetId
          ⟨t.assetId, p.getQuantity t.assetId + t.deltaQuantity,
           t.executionPrice, t.executionPrice_pos⟩ := rfl
  rw [hPos']
  by_cases hQty : p.getQuantity t.assetId + t.deltaQuantity = 0
  · -- Position erased entirely: sum drops by pos.value = pos.quantity * markPrice
    simp only [if_pos hQty]
    rw [sumPositionValues_erase_of_mem _ _ _ hLookup]
    simp only [Position.value]
    -- deltaQuantity = -pos.quantity since their sum is 0; ring handles the rest
    have hDelta : t.deltaQuantity = -pos.quantity := by
      have h := hGetQty ▸ hQty; omega
    rw [hDelta]; ring
  · -- Position updated in-place: sum changes by net delta
    simp only [if_neg hQty]
    rw [sumPositionValues_insert, sumPositionValues_erase_of_mem _ _ _ hLookup]
    simp only [Position.value, hGetQty, hPrice]; ring

end OptionHedge
