#!/usr/bin/env bash
# Verify the owl repo: build, format, tests, db rescan.
# Usage:
#   scripts/verify.sh             full pipeline (includes slow field/ring suites)
#   scripts/verify.sh --quick     fast iteration (skips slow suites)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="${1:-full}"
DB="${RA_DB:-rust_code.db}"

SKIP=()
if [[ "$MODE" == "--quick" || "$MODE" == "quick" ]]; then
  # Slow in debug builds (field ~5 min, ring/stress ~1 min each).
  SKIP=(--skip field_demo_example_checks --skip field_laws_lib_checks \
        --skip comm_ring_demo_example_checks --skip ring_demo_example_checks \
        --skip ring_laws_lib_checks --skip stress_mul_algebra_example_checks)
fi

echo "==> [1/4] cargo build"
cargo build

echo "==> [2/4] cargo fmt --check"
cargo fmt --check

echo "==> [3/4] cargo test ${MODE}"
cargo test -- "${SKIP[@]}"

echo "==> [4/4] rust-analyzer-db scan"
uvx rust-analyzer-db scan src --db "$DB"
# The scan auto-writes MCP docs into the scanned dir; remove the stray files
# so they don't get committed or confuse agents.
rm -f src/AGENTS.md src/.gitignore

echo "==> verify OK (mode: ${MODE})"
