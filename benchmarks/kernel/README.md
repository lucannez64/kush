# Kernel benchmark: Rust kernel versus Kush kernel

`run.sh` times the Rust kernel (`kush kernel FILE`, a release build of the
compiler) against the [Kush kernel](../../examples/kernel/README.md)
(`kernel check FILE`) built with LLVM (`--release --backend llvm`) and with
Cranelift (`--release`), on the same exchange files. Each time is the median
of 5 runs; memory is the peak resident set. Before timing a workload the
script checks that both Kush builds give the Rust kernel's answer on every
item (a `budget` answer on either side is inconclusive, never a pass).

Measured 2026-11-13 on an AMD Ryzen 5 PRO 5675U (6 cores, Linux), clang 23:

| Workload | Items | Rust | Kush, LLVM | Kush, Cranelift |
| --- | ---: | ---: | ---: | ---: |
| 2,000 normalize queries (a 30-step induction each) | 2000 | 0.12 s, 11 MB | **0.05 s**, 5 MB | 0.23 s, 7 MB |
| One 30,000-step induction | 1 | 0.33 s, 392 MB | **0.08 s**, 76 MB | 0.12 s, 78 MB |
| 2,000 checks of `add a b = a + b` | 2001 | 0.09 s, 11 MB | **0.04 s**, 7 MB | 0.15 s, 5 MB |
| Syntax spec, declarations only | 53 | 1.61 s, 31 MB | **0.02 s**, 5 MB | 0.11 s, 5 MB |
| Syntax spec with normalize queries | 103 | 21.8 s, 110 MB | **0.12 s**, 39 MB | 0.35 s, 39 MB |
| `logical-data`, `finite-proofs` | 44, 63 | under 0.01 s | under 0.01 s | under 0.01 s |

The answers agree everywhere, except three normalize queries of the full
specification on which the Rust kernel runs out of its step budget and the
Kush kernel finishes.

**Reading the numbers.** The gap is the algorithm, not the language:

- The Rust kernel compares terms by normalizing both sides fully and then
  comparing the normal forms, recursively, and clones `Box` trees as it goes
  (hence 392 MB for the deep induction).
- The Kush kernel compares lazily (equal ids, then weak head reduction,
  unfolding only what it needs), keeps terms hash-consed (equality is one
  integer comparison, sharing is free), skips closed subterms in substitution,
  caches traversals and normal forms, tries proof irrelevance (the only step
  that infers types) last, and frees each query's terms when it is answered.
- On small inputs (the corpus) both finish in milliseconds. On simple but
  numerous queries the Kush kernel is 2 to 3 times faster; on the
  specification's large induction proofs it is 80 to 180 times faster,
  because there normalize-then-compare does a great deal of work that lazy
  comparison never needs.
- LLVM makes the Kush kernel 3 to 5 times faster than Cranelift on
  computation-heavy workloads.

The Rust kernel is the trusted reference and was written for simplicity; the
same lazy algorithm could be ported to it (the relation would not change),
which is a separate decision. In ordinary use the Rust side's time goes mostly
into elaboration rather than the kernel: `kush core` of the specification
(elaboration and checking) takes about 15 s in a release build.

```sh
benchmarks/kernel/run.sh      # about 3 minutes
```
