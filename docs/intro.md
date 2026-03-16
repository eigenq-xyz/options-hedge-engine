# Options Hedge Engine

> **Educational Use Only**: This software is for research and educational purposes only. It is not intended for live trading or production use.

A formally verified options hedging engine combining **Lean 4 theorem proving** with **Python numerical computing**.

Every portfolio state transition (every trade, every mark-to-market update, every option settlement) carries a machine-checked proof of correctness. The results are not merely tested; they are provably correct, with the proof attached.

## What the engine does

The engine runs a discrete delta-hedging simulation for written European calls. At each weekly rebalancing step:

1. The option is marked to market at the new Black-Scholes price
2. The underlying hedge is rebalanced to the current delta
3. A `StepCertificate` is emitted verifying Lean's `valueUpdateFormula` held

A bug in the accounting logic raises `ValueError` immediately rather than silently producing incorrect numbers.

## Why formal proof?

A unit test checks one input. A Lean proof checks **all inputs**. The theorems in this engine hold for every possible portfolio, every possible trade size, every possible option strike and spot price.

The key theorem, `settlement_value_formula`, unifies ITM and OTM option expiry into a single machine-checked statement:

$$\Delta\text{PV} = \text{qty} \times (\text{payoff} - \text{mark})$$

This holds whether the option expires in-the-money (ITM, `applyTrade` path) or out-of-the-money (OTM, `abandonPosition` path).

## Quick start

```bash
git clone https://github.com/eigenq-xyz/options-hedge-engine
cd options-hedge-engine
make setup   # install Lean (elan) + Python (uv)
make test    # Lean proofs + Python tests
```

## Contents of this book

- **Formal Guarantees**: the theorems proven and the states made impossible by construction
- **Validation**: DerivaGem reference vectors, Monte Carlo convergence, BKL variance scaling, Carr-Madan decomposition
- **Delta-Hedging Demo**: Hull Table 19.2 replication with live step certificates and a deliberately broken example
- **Architecture**: Lean kernel, Python, and Cython FFI
- **Human-AI Collaboration**: how Lean acts as a development scaffold constraining AI-generated code

## References

- Hull, *Options, Futures, and Other Derivatives*, 9th Global ed., Tables 19.2, 19.3
- Bertsimas, Kogan & Lo (2000), *JFE* 55(2): discrete hedging variance
- Carr & Madan (1998): realized P&L decomposition
- de Moura & Ullrich (2021): Lean 4 / Mathlib
