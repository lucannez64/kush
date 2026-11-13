#!/usr/bin/env bash
# Kernel benchmark: the Rust kernel (`kush kernel`, release build) against the
# Kush kernel (examples/kernel) built with LLVM and Cranelift, on the same
# exchange files. Prints the median of 5 runs and the peak memory, and checks
# that every build gives the Rust kernel's answers (a `budget` line on either
# side is inconclusive). See README.md for results.
#
#   benchmarks/kernel/run.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
root=$PWD
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

export CARGO_PROFILE_RELEASE_DEBUG=0
mbx build --release -j 2 -p kush --bin kush >/dev/null 2>&1
kush=$root/target/release/kush
"$kush" build --manifest-path examples/kernel/Kush.toml -o "$work/kush-llvm" --release --backend llvm >/dev/null
"$kush" build --manifest-path examples/kernel/Kush.toml -o "$work/kush-cranelift" --release >/dev/null

# Workloads.
for name in proofs induction logical-data finite-proofs large-naturals universes logical-lambdas; do
  "$kush" core "examples/$name.kush" >> "$work/corpus.kcore.parts"
  "$kush" core "examples/$name.kush" > "$work/$name.kcore"
done
"$kush" core examples/kernel/spec/scoped.kush > "$work/spec-full.kcore"
grep -v '^(normalize' "$work/spec-full.kcore" > "$work/spec-declarations.kcore"
python3 - "$work" <<'PY'
import sys
work = sys.argv[1]
with open(f"{work}/queries.kcore", "w") as f:
    for i in range(2000):
        f.write(f"(normalize (natelim (lam nat nat) (lit {i}) (lam nat (lam nat (succ (var 0)))) (lit 30)))\n")
with open(f"{work}/deep.kcore", "w") as f:
    f.write("(normalize (natelim (lam nat nat) zero (lam nat (lam nat (succ (var 0)))) (lit 30000)))\n")
with open(f"{work}/checks.kcore", "w") as f:
    f.write("(def add 0 (pi nat (pi nat nat)) (lam nat (lam nat (natelim (lam nat nat) (var 0) (lam nat (lam nat (succ (var 0)))) (var 1)))))\n")
    for i in range(2000):
        a, b = i % 37, (i * 7) % 41
        f.write(f"(check (refl nat (lit {a+b})) (eq nat (app (app (global add) (lit {a})) (lit {b})) (lit {a+b})))\n")
PY

measure() { # label command...
  local label=$1; shift
  local times=() memory=0
  for _ in 1 2 3 4 5; do
    local result
    result=$( { /usr/bin/time -f "%e %M" "$@" > /dev/null; } 2>&1 | tail -1 )
    times+=("${result% *}")
    local kb=${result#* }
    (( kb > memory )) && memory=$kb
  done
  printf "  %-15s %8ss %6s MB\n" "$label" "$(printf '%s\n' "${times[@]}" | sort -n | sed -n 3p)" "$((memory / 1024))"
}

agree() { # file
  "$kush" kernel "$1" > "$work/rust.out"
  for build in kush-llvm kush-cranelift; do
    "$work/$build" check "$1" > "$work/kush.out"
    paste -d '\t' "$work/rust.out" "$work/kush.out" | while IFS=$'\t' read -r rust mine; do
      if [[ $rust != "$mine" && $rust != budget* && $mine != budget* ]]; then
        echo "  DISAGREEMENT ($build): $rust | $mine" >&2
        exit 1
      fi
    done
  done
}

for workload in queries deep checks spec-declarations spec-full logical-data finite-proofs; do
  echo "== $workload ($(wc -l < "$work/$workload.kcore") items)"
  agree "$work/$workload.kcore"
  measure rust "$kush" kernel "$work/$workload.kcore"
  measure kush-llvm "$work/kush-llvm" check "$work/$workload.kcore"
  measure kush-cranelift "$work/kush-cranelift" check "$work/$workload.kcore"
done
