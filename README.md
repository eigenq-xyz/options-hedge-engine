# Options Hedge Engine

[![Lean CI](https://github.com/akhilkarra/options-hedge-engine/actions/workflows/lean.yml/badge.svg)](https://github.com/akhilkarra/options-hedge-engine/actions/workflows/lean.yml)
[![Python CI](https://github.com/akhilkarra/options-hedge-engine/actions/workflows/python.yml/badge.svg)](https://github.com/akhilkarra/options-hedge-engine/actions/workflows/python.yml)
[![codecov](https://codecov.io/gh/akhilkarra/options-hedge-engine/branch/main/graph/badge.svg)](https://codecov.io/gh/akhilkarra/options-hedge-engine)
[![pre-commit.ci status](https://results.pre-commit.ci/badge/github/akhilkarra/options-hedge-engine/main.svg)](https://results.pre-commit.ci/latest/github/akhilkarra/options-hedge-engine/main)

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

## Development Milestones

Progress tracked via git tags:

- [x] **v0.1-scaffold**: Build system and project structure
- [ ] **v0.2-numeric**: Exact decimal types
- [ ] **v0.3-nav**: Portfolio state and NAV calculation
- [ ] **v0.4-trades**: Trade application with proofs
- [ ] **v0.5-certs**: Certificate emission
- [ ] **v0.6-verifier**: Lean certificate verifier
- [ ] **v0.7-integration**: End-to-end CI pipeline
- [ ] **v0.8-pricer**: Black-Scholes implementation
- [ ] **v0.9-optimizer**: LP hedging optimizer
- [ ] **v0.10-data**: Market data integration
- [ ] **v0.11-backtest**: Full backtest execution
- [ ] **v0.12-cvar**: CVaR optimization
- [ ] **v0.13-proofs**: Complete formal proofs
- [ ] **v0.14-docs**: Documentation deployment
- [ ] **v0.15 (v1.0)**: Production-ready system

See full milestone descriptions in the planning documentation.

## Documentation

- **[DECISIONS.md](DECISIONS.md)**: Architectural decision records
- **[RISKS.md](RISKS.md)**: Comprehensive risk register
- **[CONTRIBUTING.md](CONTRIBUTING.md)**: Development workflow and guidelines
- **JupyterBook** (coming in v0.14): `make docs-serve`

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

**Work in Progress** - Currently implementing v0.1-scaffold. This repository serves as a living record of the research and development process. All architectural decisions and risks are documented candidly for future reference and consultation.

---

**Academic Disclaimer**: This is research software. While the Lean proofs provide strong correctness guarantees for the accounting kernel, the overall system is not production-ready and should not be used for actual trading without extensive additional validation.
