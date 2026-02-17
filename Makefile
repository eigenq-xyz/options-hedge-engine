.PHONY: help setup clean test lint build docs-build docs-serve integration dev-lean dev-python watch-lean

help:		## Show this help message
	@echo "Option Hedge Engine - Makefile"
	@echo ""
	@echo "Available targets:"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-15s\033[0m %s\n", $$1, $$2}'

setup:		## Install all dependencies (Lean + Python)
	@echo "==> Installing Lean toolchain..."
	@cd lean && $(MAKE) setup
	@echo ""
	@echo "==> Installing Python dependencies..."
	@cd python && $(MAKE) setup
	@echo ""
	@echo "✓ Setup complete! Try 'make test' next."

build:		## Build Lean proofs + Python package + Cython FFI extension
	@echo "==> Building Lean..."
	@cd lean && $(MAKE) build
	@echo ""
	@echo "==> Building Cython FFI extension..."
	@cd python && $(MAKE) build-ffi
	@echo ""
	@echo "==> Building Python package..."
	@cd python && $(MAKE) build

test:		## Run all tests (Lean + Python)
	@echo "==> Testing Lean..."
	@cd lean && $(MAKE) test
	@echo ""
	@echo "==> Testing Python..."
	@cd python && $(MAKE) test

lint:		## Lint/typecheck all code
	@echo "==> Linting Python..."
	@cd python && $(MAKE) lint
	@echo ""
	@echo "==> Type checking Python..."
	@cd python && $(MAKE) typecheck

clean:		## Clean build artifacts
	@cd lean && $(MAKE) clean
	@cd python && $(MAKE) clean
	@rm -rf book/_build

docs-build:	## Build JupyterBook locally
	@cd python && uv run jupyter-book build ../book

docs-serve:	## Serve JupyterBook locally (port 8000)
	@echo "Serving docs at http://localhost:8000"
	@cd book/_build/html && python3 -m http.server 8000

integration:	## Run integration test (Python → Lean verify)
	@echo "==> Running integration tests..."
	@./integration/test_lean_verify.sh

dev-lean:	## Open Lean project in VSCode
	@code lean/

dev-python:	## Activate Python venv shell
	@cd python && uv run bash

watch-lean:	## Watch Lean files and rebuild on change
	@cd lean && $(MAKE) watch
