#!/usr/bin/env bash
# Run the whole compiler test suite with cargo-nextest: every test is its own
# process and tests from all ~130 test binaries run in parallel, instead of
# one binary after another. Parallelism follows the machine: half the
# hardware threads, and at most one job per 3 GiB of available memory.
#
#   scripts/test-all.sh [nextest arguments...]
set -euo pipefail
cd "$(dirname "$0")/.."
threads=$(nproc)
available_gib=$(awk '/MemAvailable/ { print int($2 / 1048576) }' /proc/meminfo)
jobs=$(( threads / 2 ))
(( jobs > available_gib / 3 )) && jobs=$(( available_gib / 3 ))
(( jobs < 2 )) && jobs=2
free_gib=$(df --output=avail -BG / | tail -1 | tr -dc 0-9)
echo "test-all: $jobs jobs ($threads threads, ${available_gib} GiB memory available, ${free_gib} GiB disk free)"
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
exec mbx nextest run -p kush --no-fail-fast --build-jobs "$jobs" --test-threads "$jobs" "$@"
