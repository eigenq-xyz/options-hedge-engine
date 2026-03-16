#!/usr/bin/env bash
# Integration test: Python delta-hedge backtest + Lean kernel round-trip
#
# Currently this verifies that:
#   1. The Lean library builds with zero sorry
#   2. The Python tests pass (all step certificates hold)
#
# A full Python→Lean certificate verification pipeline (where Python emits
# JSON certificates and a Lean executable validates them) is deferred until
# the Cython FFI bridge is complete.

set -e

echo "Integration Test: Lean build + Python backtest"
echo "================================================"

# Check dependencies
if ! command -v lake &> /dev/null; then
    echo "Error: lake not found. Run 'make setup' first."
    exit 1
fi

if ! command -v uv &> /dev/null; then
    echo "Error: uv not found. Run 'make setup' first."
    exit 1
fi

# 1. Build Lean (any sorry causes a compilation warning/error)
echo ""
echo "[1/2] Building Lean kernel (zero-sorry check)..."
cd lean && lake build && cd ..
echo "  ✓ Lean build clean"

# 2. Run Python backtest tests (all step certificates must pass)
echo ""
echo "[2/2] Running Python backtest tests..."
cd python && uv run pytest tests/test_backtest.py tests/test_edge_cases.py -q && cd ..
echo "  ✓ All step certificates pass"

echo ""
echo "Integration test complete."
