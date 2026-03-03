# Options Hedge Engine

[![Lean CI](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/lean.yml/badge.svg)](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/lean.yml)
[![Python CI](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/python.yml/badge.svg)](https://github.com/eigenq-xyz/options-hedge-engine/actions/workflows/python.yml)
[![codecov](https://codecov.io/gh/eigenq-xyz/options-hedge-engine/branch/main/graph/badge.svg)](https://codecov.io/gh/eigenq-xyz/options-hedge-engine)
[![pre-commit.ci status](https://results.pre-commit.ci/badge/github/eigenq-xyz/options-hedge-engine/main.svg)](https://results.pre-commit.ci/latest/github/eigenq-xyz/options-hedge-engine/main)

Formally verified options portfolio backtesting and hedging engine combining Lean 4 theorem proving with Python numerical computing.

> ⚠️ **EDUCATIONAL USE ONLY**: This software is for educational and research purposes only. It is NOT intended for live trading or production use. No warranty is provided. See [DISCLAIMER.md](DISCLAIMER.md) for details.

## Overview

- **Current Focus:** Historical backtesting system with WRDS OptionMetrics data
- **Future Roadmap:** LP-based portfolio optimization for hedging strategies

This project implements a formally verified backtesting engine where:
- **Lean 4** implements ALL accounting logic (compiled to C) + proves formal invariants
- **Python** handles ETL (data loading) and calls Lean via Cython FFI
- **Certificates** for ETL verification: Python emits JSON describing data, Lean validates

### Key Features

- ✅ Accounting kernel: 100% Lean (implementation + proofs), compiled to C
- ✅ Exact decimal arithmetic (no floating-point errors)
- ✅ Cython FFI: Python calls Lean accounting functions directly
- ✅ ETL certificates: Lean verifies data against assumptions
- ✅ No code duplication between Lean and Python
- 📚 Comprehensive documentation with JupyterBook

## Quick Start

```bash
# Clone and setup (requires ~5 minutes on first run)
git clone <repository-url>
cd option-hedge-engine
make setup

# Run tests
make test

# View documentation
make docs-serve  # Opens http://localhost:8000
```

### Prerequisites

- **Lean 4**: Installed via `elan` (automatic during `make setup`)
- **Python 3.12**: Managed via `uv`
- **Make**: Standard on macOS/Linux, requires WSL on Windows
- **git-crypt** (optional): For encrypted data sources

## Project Structure

```
option-hedge-engine/
├── lean/              # Lean 4 formal verification
│   ├── OptionHedge/   # Core library
│   └── lakefile.lean  # Build configuration
├── python/            # Python implementation
│   ├── src/           # Source code
│   └── tests/         # Unit tests
├── book/              # JupyterBook documentation
├── data/              # Market data (encrypted)
├── integration/       # End-to-end tests
├── Makefile          # Unified build system
├── DECISIONS.md      # Architectural decisions
└── RISKS.md          # Risk register
```

## Documentation

- **[DECISIONS.md](DECISIONS.md)**: Architectural decision records
- **[RISKS.md](RISKS.md)**: Comprehensive risk register
- **[CONTRIBUTING.md](CONTRIBUTING.md)**: Development workflow and guidelines
- **JupyterBook** (coming in v0.11): `make docs-serve`

## Architecture

The system uses a certificate-based verification architecture:

1. Python executes one timestep (pricing, optimization, trade)
2. Python emits a JSON certificate with before/after states
3. Lean verifies the certificate against formal invariants
4. If verification passes, proceed; otherwise, halt with diagnostic

This ensures that every portfolio state transition is mathematically provable correct.

### Invariants Proven

1. **NAV Identity**: NAV = cash + Σ(position × price)
2. **Self-Financing**: NAV changes only by explicit fees (at-market trades)
3. **Conservation**: Position quantities conserved across trades
4. **Cash Correctness**: Cash updates match trade execution
5. **Time Monotonicity**: Timestamps increase, expired options settled
6. **Domain Constraints**: Prices > 0, fees ≥ 0, quantities ∈ ℝ
7. **Deterministic Replay**: Same inputs → same outputs

## Research Context

This is an academic research project exploring formal verification for quantitative finance. The goal is to demonstrate that critical financial computations can be proven correct using theorem provers, increasing confidence in backtest results and reducing bugs in production trading systems.

### References

- DerivaGem (Hull & White): Reference for options pricing validation
- Lean 4 Mathlib: Foundation for mathematical proofs
- QuantEcon: Documentation framework

## License

Apache 2.0 - See [LICENSE](LICENSE) for details.

## Status

**Work in Progress** - Currently implementing v0.2-nav. This repository serves as a living record of the research and development process. All architectural decisions and risks are documented candidly for future reference and consultation.

---

**Academic Disclaimer**: This is research software. While the Lean proofs provide strong correctness guarantees for the accounting kernel, the overall system is not production-ready and should not be used for actual trading without extensive additional validation.
