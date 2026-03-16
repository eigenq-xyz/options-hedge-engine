# Contributing Guide

Welcome to the Options Hedge Engine project. This guide covers development setup, workflow, and conventions.

---

## Prerequisites

**Required:**
- **macOS or Linux** (Windows users: WSL 2 required)
- **Git** (version control)
- **Make** (build orchestration)
- **uv** (Python package manager): Install with `curl -LsSf https://astral.sh/uv/install.sh | sh`

**Installed by `make setup`:**
- **Lean 4** via elan (Lean toolchain manager)
- **Python 3.12** via uv
- **Python dependencies** (pytest, ruff, mypy, jupyterbook, etc.)

**Optional:**
- **direnv**: Auto-activate Python venv when entering project directory (`brew install direnv`)

---

## One-Time Setup

```bash
# 1. Clone repository
git clone https://github.com/eigenq-xyz/options-hedge-engine.git
cd options-hedge-engine

# 2. Install all dependencies
make setup
# This takes ~5 minutes first time (downloads Lean toolchain + Python packages)

# 3. Verify installation
make test
# Expected: All Lean proofs compile, all Python tests pass

# 4. (Optional) Setup direnv for auto-activation
# Install: brew install direnv (macOS) or apt install direnv (Linux)
# Add to shell: eval "$(direnv hook bash)" in ~/.bashrc
# Create .envrc: echo "source python/.venv/bin/activate" > .envrc
# Allow: direnv allow

# 5. (Optional) Configure git-crypt for data access
# Request decryption key from project maintainer via secure channel
# Then run: git-crypt unlock /path/to/key
```

---

## Development Workflow

### Lean Development

```bash
cd lean

# Build proofs
lake build

# Run tests
lake test

# Watch mode (rebuild on file changes)
make watch

# Check for axioms (should be zero in completed milestones)
grep -r "axiom" OptionHedge/

# Open in VSCode with Lean 4 extension
code .
```

**Lean Tips:**
- Install **Lean 4 VSCode extension**: `ms-vscode.lean4`
- Proofs show live feedback in editor
- Use `sorry` as placeholder during development, replace with actual proof
- Check CI before pushing: proofs must compile with no errors

### Python Development

```bash
cd python

# Install/update dependencies
uv sync

# Run tests
uv run pytest

# Run tests with coverage
uv run pytest --cov=hedge_engine --cov-report=term-missing

# Type checking
uv run mypy src/

# Linting
uv run ruff check src/ tests/

# Format code
uv run ruff format src/ tests/

# Interactive Python shell
uv run ipython
```

**Python Tips:**
- Use `Decimal` for all financial calculations (never `float` for money)
- Add type hints to all functions
- Write tests for new features (`tests/test_*.py`)
- Follow existing code style (enforced by ruff)

### Documentation

```bash
# Build JupyterBook
make docs-build

# Build and serve locally (http://localhost:8000)
make docs-serve

# Execute notebooks (for caching outputs)
cd python
uv run jupyter-book build ../book --execute
```

**Documentation Tips:**
- Add docstrings to all public functions/classes
- Create notebooks for new features in `book/examples/`
- Document architectural decisions in [DECISIONS.md](DECISIONS.md)
- Update [RISKS.md](RISKS.md) if new risks identified

### Integration Testing

```bash
# Run full integration test
make integration

# Manually test certificate pipeline
cd python
uv run python scripts/emit_test_certs.py > /tmp/certs.json
cd ../lean
lake exe verify_certs /tmp/certs.json
```

---

## Code Conventions

### Lean

```lean
-- Module naming: PascalCase
-- OptionHedge/Numeric.lean, OptionHedge/Accounting.lean

-- Structure names: PascalCase
structure Portfolio where
  cash : Int
  positions : List Position

-- Function names: camelCase
def calcNAV (p : Portfolio) : Int := ...

-- Theorem names: camelCase with descriptive suffix
theorem navIdentityHolds (p : Portfolio) : ... := by ...

-- Comments: Explain why, not what
-- Use docstrings for public API
/-- Calculate net asset value of portfolio.
    NAV = cash + Σ(position.quantity × position.mark_price) -/
def calcNAV ...
```

### Python

```python
# Follow PEP 8
# Use type hints everywhere
# Docstrings in Google style

from decimal import Decimal
from typing import List

class Portfolio:
    """Represents portfolio state at a point in time.

    Attributes:
        cash: Cash balance in account (Decimal for precision)
        positions: List of open positions
    """

    def __init__(self, cash: Decimal, positions: List[Position]) -> None:
        self.cash = cash
        self.positions = positions

    def calc_nav(self) -> Decimal:
        """Calculate net asset value.

        Returns:
            Total portfolio value (cash + position values)
        """
        position_value = sum(p.quantity * p.mark_price for p in self.positions)
        return self.cash + position_value
```

### Git Commit Messages

```
[tag] Brief summary (50 chars)

- Detailed explanation if needed
- Use bullet points for multiple changes
- Reference issues: Fixes #123

Examples:
[v0.2] Implement Price type with scaled integer arithmetic
[v0.3] Prove NAV identity theorem
[docs] Add numeric precision policy documentation
[fix] Handle edge case in certificate parser
```

---

## Testing Requirements

### Before Pushing

```bash
# At project root
make test        # All tests must pass
make lint        # No linting errors
make integration # Integration test passes
```

### Test Coverage

- **Python**: Aim for 80%+ coverage (enforced in CI)
- **Lean**: All theorems must have proofs (no `sorry` in main code)
- **Integration**: At least one end-to-end test per milestone

### Writing Tests

**Python:**
```python
# tests/test_accounting.py
from decimal import Decimal
from hedge_engine.accounting import Portfolio, calc_nav

def test_nav_calculation():
    """NAV equals cash plus position values."""
    portfolio = Portfolio(
        cash=Decimal("1000.00"),
        positions=[
            Position("SPY", Decimal("10"), Decimal("400.00")),  # 10 shares @ $400
        ]
    )
    expected = Decimal("5000.00")  # 1000 + 10*400
    assert calc_nav(portfolio) == expected
```

**Lean:**
```lean
-- Tests/UnitTests.lean
import OptionHedge.Accounting

-- Simple test case
example : Price.add ⟨100⟩ ⟨200⟩ = ⟨300⟩ := rfl
```

---

## Common Tasks

### Adding a New Invariant

1. **Document in RISKS.md**: Why is this invariant important?
2. **Define theorem in Lean** (`OptionHedge/Invariants.lean`)
3. **Implement proof** (`OptionHedge/Proofs/NewInvariant.lean`)
4. **Add to verifier** (`OptionHedge/Certificate/Verifier.lean`)
5. **Test in Python** (`tests/test_invariants.py`)
6. **Document in notebook** (`book/invariants/new_invariant.ipynb`)

### Adding a New Certificate Field

1. **Update Python schema** (`python/src/hedge_engine/certificate/schema.py`)
2. **Update Lean schema** (`lean/OptionHedge/Certificate/Schema.lean`)
3. **Update parser** (`lean/OptionHedge/Certificate/Parser.lean`)
4. **Increment schema version** if breaking change
5. **Add tests** for new field in both languages
6. **Update docs** (`book/architecture/certificate_flow.md`)

### Updating Dependencies

**Python:**
```bash
cd python
# Add new dependency
uv add package-name

# Update all dependencies
uv lock --upgrade

# Commit updated uv.lock
git add uv.lock && git commit -m "[deps] Update Python dependencies"
```

**Lean:**
```bash
cd lean
# Update Lean toolchain
lake update

# Commit updated lake-manifest.json
git add lake-manifest.json && git commit -m "[deps] Update Lean dependencies"
```

---

## Troubleshooting

### Lean Issues

**Problem**: `lake build` fails with "unknown package"
```bash
# Solution: Update dependencies
cd lean && lake update
```

**Problem**: Proofs compile slowly
```bash
# Solution: Increase parallelism
lake build -j 8  # Use 8 cores
```

**Problem**: VSCode Lean extension not working
```bash
# Solution: Restart Lean server
Cmd+Shift+P → "Lean 4: Restart Server"
```

### Python Issues

**Problem**: `uv sync` fails
```bash
# Solution: Clear cache and retry
uv cache clean
uv sync
```

**Problem**: Import errors in tests
```bash
# Solution: Install package in editable mode
cd python
uv pip install -e .
```

**Problem**: `make docs-serve` fails
```bash
# Solution: Clean build and retry
rm -rf book/_build
make docs-build
```

### Data Access

**Problem**: Need decryption key for data/
```
# Solution: Request from project maintainer
# Send GPG public key or Signal contact
# Key will be provided via secure channel only
```

**Problem**: git-crypt not installed
```bash
# macOS
brew install git-crypt

# Linux
sudo apt install git-crypt
```

---

## CI Pipeline

GitHub Actions runs on every push:

1. **Lean Build** (`.github/workflows/lean.yml`)
   - Compiles all proofs
   - Checks for `axiom` usage
   - Runs Lean tests

2. **Python Tests** (`.github/workflows/python.yml`)
   - Linting (ruff)
   - Type checking (mypy)
   - Unit tests with coverage

3. **Integration** (`.github/workflows/integration.yml`)
   - Runs after Lean + Python pass
   - Python emits certificates → Lean verifies

4. **Documentation** (`.github/workflows/docs.yml`)
   - Builds JupyterBook
   - Deploys to GitHub Pages (main branch only)

**Local CI Simulation** (requires `act`):
```bash
brew install act
make ci-local
```

---

## Getting Help

- **Questions**: Open a [Discussion](https://github.com/eigenq-xyz/options-hedge-engine/discussions)
- **Bugs**: Open an [Issue](https://github.com/eigenq-xyz/options-hedge-engine/issues)
- **Lean help**: [Lean Zulip](https://leanprover.zulipchat.com/)
- **Python help**: Check [DEVELOPMENT.md](DEVELOPMENT.md) for detailed technical info

---

## Code of Conduct

- Be respectful and constructive
- This is a research project; questions and discussions are welcome
- Document your reasoning (especially for design decisions)
- Prioritize correctness over cleverness

---

Contributions of all kinds are welcome.
