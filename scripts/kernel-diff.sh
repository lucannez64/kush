#!/usr/bin/env bash
# Differential sweep of the Kush kernel (examples/kernel) against the Rust
# kernel: the example corpus, its mutants, a file of typing cases, and
# SEEDS generated files (default 2000), and every item of the kernel's
# syntax specification (examples/kernel/spec/scoped.kush, slow in debug). See docs/kernel-in-kush.md, section 3.
#
#   scripts/kernel-diff.sh [SEEDS]
set -euo pipefail
cd "$(dirname "$0")/.."
seeds="${1:-2000}"
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
KUSH_KIK_SEEDS="$seeds" mbx test -j 2 -p kush --test kernel_in_kush --test kernel_diff --test kernel_spec -- --nocapture --include-ignored 2>&1 \
  | grep -E '^test |test result|mutants:|generated terms|panicked|item [0-9]+ of'
