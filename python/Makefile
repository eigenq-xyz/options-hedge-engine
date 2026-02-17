.PHONY: help setup build build-ffi test lint typecheck format clean

help:
	@echo "Python Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  setup      - Install dependencies with uv"
	@echo "  build      - Build Python package"
	@echo "  build-ffi  - Compile Lean Cython extension (requires lake build first)"
	@echo "  test       - Run tests with coverage"
	@echo "  lint       - Check code style with ruff"
	@echo "  typecheck  - Type check with mypy"
	@echo "  format     - Format code with ruff"
	@echo "  clean      - Remove build artifacts"

setup:
	@command -v uv >/dev/null 2>&1 || { \
		echo "Installing uv..."; \
		curl -LsSf https://astral.sh/uv/install.sh | sh; \
	}
	uv sync --all-extras

build:
	uv build

build-ffi:	## Compile the Lean↔Python Cython extension in-place
	@echo "==> Ensuring Lake C IR files are up to date..."
	@cd ../lean && lake build
	@echo "==> Building Cython extension..."
	uv run python setup_ffi.py build_ext --inplace

test:
	uv run pytest -v --cov=hedge_engine --cov-report=term-missing

lint:
	uv run ruff check src/ tests/

typecheck:
	uv run mypy src/

format:
	uv run ruff format src/ tests/

clean:
	rm -rf .venv/ dist/ .pytest_cache/ .coverage .mypy_cache/ .ruff_cache/
	find . -type d -name __pycache__ -exec rm -rf {} +
	find . -type f -name "*.pyc" -delete
