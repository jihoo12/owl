#!/usr/bin/env bash
# Verify the owl repo: build, format, tests, db rescan.
# Usage:
#   scripts/verify.sh          full pipeline
#   scripts/verify.sh --quick  alias (kept for habit-compat; since the perf
#                              work of 2026-08 there are no slow suites left
#                              to skip — the whole suite runs in <1 min).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="${1:-full}"
DB="${RA_DB:-rust_code.db}"

echo "==> [1/4] cargo build"
cargo build

echo "==> [2/4] cargo fmt --check"
cargo fmt --check

echo "==> [3/4] cargo test ${MODE}"
cargo test

echo "==> [4/4] rust-analyzer-db scan"
uvx rust-analyzer-db scan src --db "$DB"
# The scan auto-writes MCP docs into the scanned dir; remove the stray files
# so they don't get committed or confuse agents.
rm -f src/AGENTS.md src/.gitignore

echo "==> verify OK (mode: ${MODE})"
