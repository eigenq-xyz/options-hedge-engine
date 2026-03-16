# Formal Guarantees

The Lean 4 accounting kernel carries machine-checked proofs for all possible inputs.
These are not tests; the proofs are verified by Lean's type checker at compile time.

## Impossible States (by construction)

The following states **cannot occur** in any run of the engine. They are excluded by
the type system and proven invariants, not by runtime checks.

| What cannot happen | Enforced by |
|--------------------|-------------|
| Portfolio with incorrect value | `value_valid` proof field on `Portfolio` |
| Position with non-positive price | `markPrice_pos` proof field on `Position` |
| Trade with negative fee | `fee_nonneg` proof field on `Trade` |
| Option with non-positive strike | `strike_pos` proof field on `EuropeanOption` |
| Wrong cash after any trade | `cashUpdateCorrect` (proved `rfl`) |
| Wrong quantity after any trade | `quantityConservation` |
| Ghost zero-quantity positions | `applyTrade_wellFormed` |

## Theorems Proven

### Accounting Kernel (`Invariants.lean`)

| Theorem | Economic meaning |
|---------|-----------------|
| `valueIdentity` | Portfolio value = cash + Σ(qty × mark price), always. No hidden value can accumulate. |
| `valueUpdateFormula` | ΔPV = pre-trade qty × (exec price − mark) − fee. The exact change from any trade. |
| `selfFinancing` | Trading at the mark price changes PV only by the fee (no free money). |
| `quantityConservation` | Shares cannot appear from thin air or silently vanish after a trade. |
| `cashUpdateCorrect` | Every dollar spent on a trade flows through the cash balance. Proved `rfl`. |
| `applyTrade_wellFormed` | No zero-quantity ghost positions can exist after any trade sequence. |

### Options Layer (`OptionInvariants.lean`)

| Theorem | Economic meaning |
|---------|-----------------|
| `callPayoff_nonneg` | A call holder never owes money at expiry (right but not obligation). |
| `putPayoff_nonneg` | A put holder never owes money at expiry (right but not obligation). |
| `callPayoff_itm` | When S > K: call payoff = S − K exactly. |
| `callPayoff_otm` | When S ≤ K: call payoff = 0 exactly. |
| `integerPayoffDifference` | Call payoff − put payoff = S − K (pure integer identity; not continuous-time put-call parity). |
| `settlement_cash_itm` | ITM settlement credits exactly qty × payoff, with no over/underpayment. |
| `settlement_value_formula` | **Crown jewel.** ΔPV = qty × (payoff − mark), for both ITM and OTM paths unified. |

## The Crown Jewel: `settlement_value_formula`

```lean
theorem settlement_value_formula (p : Portfolio) (opt : EuropeanOption)
    (pos : Position) (hPos : p.getPosition opt.assetId = some pos)
    (spot : Int) :
    (applySettlement p opt (opt.settle spot pos.quantity)).portfolioValue =
      p.portfolioValue + pos.quantity * (optionPayoff opt spot - pos.markPrice)
```

This theorem covers **both** settlement branches in a single statement:

- **ITM** (`payoff > 0`): `applyTrade` at the payoff price. ΔPV = qty × (payoff − mark).
- **OTM** (`payoff = 0`): `abandonPosition` erases the worthless option. ΔPV = qty × (0 − mark) = −qty × mark (writing off the mark value).

The key insight is that the formula is identical in both cases: the OTM branch is simply the case where `payoff = 0`.

## Zero Sorry

All proofs are complete with no `sorry` tactics anywhere. `sorry` in Lean is equivalent
to admitting an axiom without proof; the zero-sorry discipline means every claim in
this codebase is actually machine-verified.

```bash
# Verify zero sorry:
cd lean && lake build   # any sorry would cause a compilation error
```

This is the simplest possible audit: one command, binary output.
