/-
Copyright (c) 2026 Option Hedge Engine Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Karra
-/

import OptionHedge.Options
import OptionHedge.Invariants
import Mathlib.Tactic

/-!
# Option Invariants

Formal theorems for European option settlement.

This module proves:
- Payoff non-negativity and characterization (ITM/OTM)
- Put-call parity (integer, exact)
- OTM abandonment: portfolio value drops by position's mark value
- ITM settlement: cash increases by qty × payoff, position closed
- `settlement_value_formula` (crown jewel): portfolio value change = qty × (payoff − mark)
  for BOTH ITM and OTM paths, unifying the two settlement branches
-/

namespace OptionHedge

/-! ## Payoff Non-Negativity -/

/-- Call payoff is always non-negative.

    Economic meaning: the holder of a call never owes money at expiry —
    they exercise only when it is profitable to do so.  The right but not
    the obligation to buy. -/
theorem callPayoff_nonneg (spot strike : Int) : callPayoff spot strike ≥ 0 :=
  le_max_left 0 (spot - strike)

/-- Put payoff is always non-negative.

    Economic meaning: the holder of a put never owes money at expiry —
    they exercise only when it is profitable to do so.  The right but not
    the obligation to sell. -/
theorem putPayoff_nonneg (spot strike : Int) : putPayoff spot strike ≥ 0 :=
  le_max_left 0 (strike - spot)

/-- Option payoff is always non-negative.

    Economic meaning: a European option can never obligate its holder to
    pay at expiry.  This holds for both calls and puts, covering all
    possible spot prices. -/
theorem optionPayoff_nonneg (opt : EuropeanOption) (spot : Int) :
    optionPayoff opt spot ≥ 0 := by
  simp only [optionPayoff]
  cases opt.kind with
  | Call => exact callPayoff_nonneg spot opt.strike
  | Put  => exact putPayoff_nonneg  spot opt.strike

/-! ## Payoff Characterization -/

/-- Call is in-the-money: payoff equals spot minus strike.

    Economic meaning: when the underlying closes above the strike the
    holder receives the intrinsic value (spot − strike) in cash. -/
theorem callPayoff_itm (spot strike : Int) (h : spot > strike) :
    callPayoff spot strike = spot - strike :=
  max_eq_right (by omega)

/-- Call is out-of-the-money (or at-the-money): payoff is zero.

    Economic meaning: when the underlying closes at or below the strike,
    exercising the call is unprofitable and the option expires worthless. -/
theorem callPayoff_otm (spot strike : Int) (h : spot ≤ strike) :
    callPayoff spot strike = 0 :=
  max_eq_left (by omega)

/-- Put is in-the-money: payoff equals strike minus spot.

    Economic meaning: when the underlying closes below the strike the
    holder receives the intrinsic value (strike − spot) in cash. -/
theorem putPayoff_itm (spot strike : Int) (h : spot < strike) :
    putPayoff spot strike = strike - spot :=
  max_eq_right (by omega)

/-- Put is at-the-money or out-of-the-money: payoff is zero.

    Economic meaning: when the underlying closes at or above the strike,
    exercising the put is unprofitable and the option expires worthless. -/
theorem putPayoff_otm (spot strike : Int) (h : spot ≥ strike) :
    putPayoff spot strike = 0 :=
  max_eq_left (by omega)

/-! ## Integer Payoff Difference -/

/-- Integer payoff difference: call payoff minus put payoff equals spot minus strike.

    This is a pure integer identity (max(0,S−K) − max(0,K−S) = S−K), proved by omega.
    It does not model the financial put-call parity relation C − P = S − K·e^{−rT},
    which requires continuous-time pricing and is not expressed here. -/
theorem integerPayoffDifference (spot strike : Int) :
    callPayoff spot strike - putPayoff spot strike = spot - strike := by
  simp only [callPayoff, putPayoff]; omega

/-! ## OTM Abandonment -/

/-- Abandoning a position decreases portfolio value by that position's mark value.

    Economic meaning: an OTM option expires worthless; the mark value is written off. -/
theorem abandonPosition_portfolioValue (p : Portfolio) (id : AssetId) (pos : Position)
    (hPos : p.getPosition id = some pos) :
    (p.abandonPosition id).portfolioValue = p.portfolioValue - pos.value := by
  simp only [Portfolio.abandonPosition, mk'_value]
  rw [OptionHedge.sumPositionValues_erase_of_mem _ _ _ hPos, valueIdentity]
  ring

/-- Abandoning a position leaves cash unchanged. -/
theorem abandonPosition_cash_unchanged (p : Portfolio) (id : AssetId) :
    (p.abandonPosition id).cash = p.cash := rfl

/-- Abandoning a position preserves portfolio well-formedness. -/
theorem abandonPosition_wellFormed (p : Portfolio) (id : AssetId) (hw : p.WellFormed) :
    (p.abandonPosition id).WellFormed := by
  intro k v hLookup
  have hPositions : (p.abandonPosition id).positions = p.positions.erase id := rfl
  rw [hPositions] at hLookup
  cases hk : (id == k) with
  | true =>
    have heq : id = k := LawfulBEq.eq_of_beq hk
    subst heq; simp at hLookup
  | false =>
    rw [show (p.positions.erase id)[k]? = p.positions[k]? from by
        simp [Std.HashMap.getElem?_erase, hk]] at hLookup
    exact hw k v hLookup

/-! ## ITM Settlement -/

/-- ITM settlement credits cash by quantity × payoff.

    Economic meaning: closing a long option ITM at expiry receives
    exactly its intrinsic value in cash — no more, no less.  The kernel
    cannot overpay or underpay the settlement. -/
theorem settlement_cash_itm (p : Portfolio) (opt : EuropeanOption)
    (currentQty payoff : Int) (h : payoff > 0) :
    (applyTrade p (Trade.settlementITM opt currentQty payoff h)).cash =
    p.cash + currentQty * payoff := by
  simp only [cashUpdateCorrect, Trade.settlementITM, Trade.mk']
  ring

/-- ITM settlement closes the position: quantity becomes zero after settlement.

    Requires `hQty` asserting the portfolio holds exactly `currentQty` of the option. -/
theorem settlement_position_closed (p : Portfolio) (opt : EuropeanOption)
    (currentQty payoff : Int) (h : payoff > 0)
    (hQty : p.getQuantity opt.assetId = currentQty) :
    (applyTrade p (Trade.settlementITM opt currentQty payoff h)).getQuantity
        opt.assetId = 0 := by
  -- Rewrite opt.assetId as t.assetId so quantityConservation can pattern-match
  rw [show opt.assetId = (Trade.settlementITM opt currentQty payoff h).assetId from rfl]
  rw [quantityConservation]
  simp only [Trade.settlementITM, Trade.mk', hQty]
  ring

/-! ## Crown Jewel: Settlement Portfolio Value Formula -/

/-- Settlement value formula: settling an option changes portfolio value by
    qty × (payoff − mark), where payoff = max(0, S−K) for calls.

    Economic meaning: at expiry, the change in portfolio value equals the quantity held
    times the difference between the option's payoff and its pre-expiry mark price.
    - If `payoff > mark`: the portfolio gains (option was undervalued).
    - If `payoff < mark`: the portfolio loses (option was overvalued or expired OTM).
    - If `payoff = mark`: portfolio value is unchanged (option was fairly marked).

    Unifies ITM settlement (`applyTrade` path) and OTM abandonment (`abandonPosition` path)
    in a single equation, proved without case-splitting on the runner side.

    Formal proof is stronger than a unit test: it holds regardless of moneyness,
    strike, spot price, or contract count. -/
theorem settlement_value_formula (p : Portfolio) (opt : EuropeanOption)
    (pos : Position) (hPos : p.getPosition opt.assetId = some pos)
    (spot : Int) :
    (applySettlement p opt (opt.settle spot pos.quantity)).portfolioValue =
      p.portfolioValue + pos.quantity * (optionPayoff opt spot - pos.markPrice) := by
  have hGetQty : p.getQuantity opt.assetId = pos.quantity := by
    simp [Portfolio.getQuantity, hPos]
  have hGetMark : p.getMarkPrice_orZero opt.assetId = pos.markPrice := by
    simp [Portfolio.getMarkPrice_orZero, hPos]
  simp only [EuropeanOption.settle]
  by_cases h : optionPayoff opt spot > 0
  · -- ITM: close position via applyTrade
    rw [dif_pos h]
    simp only [applySettlement]
    rw [valueUpdateFormula]
    simp only [Trade.settlementITM, Trade.mk', hGetQty, hGetMark]
    ring
  · -- OTM: abandon the worthless position
    rw [dif_neg h]
    have hPayoff : optionPayoff opt spot = 0 := by
      have := optionPayoff_nonneg opt spot; omega
    simp only [applySettlement]
    rw [abandonPosition_portfolioValue _ _ _ hPos, position_value_def, hPayoff]
    ring

end OptionHedge
