# Numerical Validation

Formal proofs guarantee correctness for all inputs. These numerical results confirm
the engine produces accurate outputs on specific, externally verifiable benchmarks.

## Black-Scholes Pricer (DerivaGem Reference Vectors)

The pricer is validated against Hull's DerivaGem (DG400a) reference values.

| Scenario | S | K | T | r | σ | Type | Price | Δ |
|----------|---|---|---|---|---|------|-------|---|
| Hull Ex 15.6 | 42 | 40 | 0.5 | 0.10 | 0.20 | call | 4.76 | 0.779 |
| Hull Ex 15.6 | 42 | 40 | 0.5 | 0.10 | 0.20 | put | 0.81 | −0.221 |
| ATM | 100 | 100 | 1.0 | 0.05 | 0.20 | call | 10.45 | 0.637 |

Tolerances: `abs=0.01` on price, `abs=0.001` on delta.

All monetary values cross the FFI boundary as basis-point integers (×10,000):
`to_bp(50.25) = 502_500`. The Lean kernel never operates on floats.

## Monte Carlo Convergence (the Black-Scholes Theorem)

The primary numeric gate is the Black-Scholes theorem itself: the expected discrete
hedge cost converges to the BS price as paths → ∞.

Over **500 seeded GBM paths** (20 weekly rebalancing steps each):

- Mean hedging cost is within **±3% of the BS price** (justified by CLT)
- Every step on every path carries a `StepCertificate` confirming `valueUpdateFormula` held
- 10,000 total certificates, all passing

Setup: S₀=49, K=50, r=5%, σ=20%, T=20 weeks, 100,000 contracts.

## Variance Reduction (Bertsimas-Kogan-Lo 2000)

BKL (JFE 55(2)) proved `Var[hedge error] ∝ 1/N`. The engine reproduces this:

$$\text{Var}[\varepsilon_N] \approx \frac{\sigma^2}{2N} \int_0^T E\left[(S_t \Gamma_t)^2\right] dt$$

Over 200 seeded paths:

- `std(10 steps) / std(20 steps) ≈ √2` (within ±30% at N=200 paths)
- `std(40 steps) < std(10 steps)` (directional check)

## Carr-Madan Decomposition

Carr & Madan (1998) decompose discrete hedge cost as:

$$\text{hedge\_cost} \approx C_0 + \sum_i \tfrac{1}{2} \Gamma_i S_i^2 \left[\left(\frac{\Delta S_i}{S_i}\right)^2 - \sigma^2 \Delta t\right]$$

The writer is **short gamma**: high realized volatility raises both the hedging cost
(from more expensive rebalancing) and gamma P&L simultaneously.

Over 200 seeded paths:

- `corr(hedge_cost, gamma_pnl) > 0.70` (strongly positive, as predicted)
- `mean(gamma_pnl) ≈ 0` (realised vol = implied vol in expectation under GBM)

## Hull Table 19.2 / 19.3 (Deterministic Regression)

Both Hull tables are run as deterministic regression tests:
all step certificates must pass and the cost must be in a financially plausible range.

| Table | Terminal S | K | Outcome | Engine cost |
|-------|-----------|---|---------|-------------|
| 19.2 | 57.25 (ITM) | 50 | Exercises | ~$253,700 |
| 19.3 | 48.12 (OTM) | 50 | Expires worthless | positive |

Note: Hull's published costs use 3dp-rounded deltas; our engine uses float deltas
(more accurate). The difference is expected and documented.
