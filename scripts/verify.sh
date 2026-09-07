#!/usr/bin/env bash
# Verify the owl repo: build, format, tests.
# Usage:
#   scripts/verify.sh          full pipeline
#   scripts/verify.sh --quick  alias (kept for habit-compat; since the perf
#                              work of 2026-08 there are no slow suites left
#                              to skip — the whole suite runs in <1 min).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="${1:-full}"

echo "==> [1/3] cargo build"
cargo build

echo "==> [2/3] cargo fmt --check"
cargo fmt --check

echo "==> [3/3] cargo test"
cargo test

echo "==> verify OK (mode: ${MODE})"
