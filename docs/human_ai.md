# Human–AI Collaboration via Lean

This project is built with **Claude Code** (Anthropic's AI coding assistant, `claude-sonnet-4-6`).
The Lean proof system plays a second, less obvious role beyond runtime verification:
it acts as a **formal development scaffold** that structurally constrains what Claude Code
can generate.

## The Development Loop

```text
1. Human specifies WHAT MUST BE TRUE   →  the theorem
2. AI generates code THAT MUST SATISFY IT  →  the implementation
3. Lean verifies the combination is correct  →  proof compiles or it doesn't
4. Human reviews THEOREM STATEMENTS, not implementation line-by-line
```

Every accounting function the AI generates must satisfy pre-existing theorem statements.
If the implementation is wrong, the Lean proof fails to compile — caught before any test runs.

## Why This Is Structurally Different from Code Review

Traditional AI-assisted development requires the human to review generated code
line-by-line for correctness. This does not scale: a 200-line function is hard to audit,
and subtle accounting errors can hide in correct-looking code.

The Lean scaffold inverts this. The human's oversight is concentrated at the level of
**mathematical claims** rather than implementation details:

- Did the AI correctly implement `applyTrade`? → Check whether `valueUpdateFormula` compiles.
- Did it correctly implement option settlement? → Check whether `settlement_value_formula` compiles.

The AI cannot introduce a silent accounting error that passes the formal spec.
It would need to change the theorem to do so — a visible, reviewable act.

## The Audit Trail

The proof obligations (Lean theorem statements) plus the runtime certificates
(`StepCertificate` objects) together form a complete audit trail:

1. **Proof obligations** — machine-verified at compile time for all inputs
2. **Step certificates** — machine-checkable at runtime for each specific backtest run

Any third party with a Lean installation can independently verify both from source.

## Zero Sorry as a Human Responsibility

`sorry` in Lean is an escape hatch that admits an axiom without proof. The zero-sorry
discipline is the **human's responsibility** in this workflow:

- The AI writes tactic proofs
- The human verifies that `lake build` completes with zero sorry before any merge
- This is the simplest possible checkpoint: one command, binary output

If `sorry` appeared, the theorem would be unverified. The step certificates would
still be emitted at runtime, but their guarantee ("valueUpdateFormula holds") would
rest on an unproven foundation. Zero sorry means the guarantee is solid.

## This Workflow Scales

As the theorem base grows, the AI has less room to be wrong. Each new theorem
adds another dimension of correctness that new implementations must satisfy.
The formal spec becomes a growing constraint that accumulates over time —
the opposite of technical debt.

## References

This development methodology is discussed by Jeremy Avigad (CMU) in the context
of Lean for mathematical formalization. The key observation: **human oversight
concentrating at the theorem level rather than the implementation level** is a
qualitative change in how AI-generated code can be trusted for critical systems.

Potential venues for a methodology paper:

- LMFP (Lean for Mathematical Finance and Physics)
- CPP (Certified Programs and Proofs)
- ITP (Interactive Theorem Proving)
