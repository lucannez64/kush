# Headerless buffers: speed and memory

Compiler checkpoints: `1f0cf54` (header elision), `516b360` (checked byte-append
fast path and smaller capacity decoder). Baseline compiler: `e6662c2`.
Application sources, input seed, algorithms and JSON oracle are unchanged.
Both languages use Cranelift, with checked arithmetic; Rust's prebuilt standard
library may contain LLVM-generated code. This is not a Rust LLVM comparison.

**For this JSON editor with metadata inline in both languages, current Kush
beats Rust on measured wall time and peak resident memory. Requested heap is
essentially tied, with Kush slightly higher. The original boxed layout still
uses more memory than Rust. These are workload-specific results.**

## Low-load Boat confirmation

Same hash-verified prebuilt inline binaries, 16,384 documents × 31 edits,
deliberate reuse, one pinned CPU, five samples after one warmup in shuffled
order. No compilation ran during this cohort. Host: Ryzen 9 9950X, Ubuntu/glibc
2.39. Load average was 0.00 at the start and 0.08 at the end. Per-child `wait4`
provides wall/CPU time and peak RSS, with no timing-wrapper process.

| Control | Median wall ms | Median CPU ms | Median peak RSS KiB |
|---|---:|---:|---:|
| Previous Kush | 394.979 | 394.168 | 16,128 |
| Current Kush | 417.574 | 417.006 | 15,616 |
| Rust CLIF / deliberate reuse | 482.201 | 481.018 | 16,128 |

Current Kush takes **13.4% less wall time** and **13.3% less CPU time** than
Rust, with **3.2% less peak RSS**. Every current-Kush timing sample is below
every Rust sample in this short cohort. This is supporting evidence, not a
confidence interval or a universal performance guarantee.

There is a real tradeoff against **previous Kush**: current Kush takes **5.7%
more wall time** here while using **3.2% less peak RSS**. Header elision is not
a free speed optimization. The runtime and code generation change together;
this experiment does not isolate every remaining instruction cost.

[Raw confirmation, hashes, host and samples](boat-confirmation.json).

## Laptop: final matched cohorts

Ryzen 5 PRO 5675U, Linux/glibc, CPU 7. Each application layout has its own
shuffled old/current/Rust cohort: seven timing/RSS samples after two warmups,
three separate phase-RSS probes, and separate allocation tracing. Sizes 256,
4,096 and 16,384; 31 edits. Background proof-checking work was active: inline
load rose from approximately 8.8 to 13.0. Speed samples are noisy; use the
within-cohort comparisons and the low-load confirmation, not absolute times
across cohorts or earlier reports. Process-tree CPU time includes the small
GNU time wrapper and is recorded via child `getrusage` deltas.

### Inline metadata, large deliberate-reuse case

| Metric | Previous Kush | Current Kush | Rust CLIF |
|---|---:|---:|---:|
| Median wall time | 1,333.5 ms | 1,316.1 ms | 1,806.3 ms |
| Median process-tree CPU time | 1,224.8 ms | 1,221.5 ms | 1,577.1 ms |
| Median peak RSS | 16,500 KiB | 16,076 KiB | 16,372 KiB |
| Peak live requested heap | 13.508 MiB | 13.007 MiB | 13.002 MiB |
| Allocator requests (alloc + realloc) | 81,926 | 81,935 | 81,978 |
| Cumulative requested bytes | 37.750 MiB | 36.751 MiB | 35.568 MiB |
| Median RSS after large release | 5,012 KiB | 4,580 KiB | 4,092 KiB |

Current Kush is **27.1% faster in wall time** and uses **1.8% less peak RSS**
than Rust in this busy-laptop cohort. Peak requested heap is **4,936 bytes
(4.82 KiB, 0.036%) higher**. Allocator requests are essentially equal. Cumulative
requested bytes and post-release RSS remain higher than Rust; there is no win
on every allocation/retention metric.

Versus previous Kush, the large-case requested-heap peak falls by 526,272
bytes, roughly 0.5 MiB. The apparent 1.3% wall-time improvement over previous
Kush is small relative to sample variation and is not a solid speedup claim;
the low-load Boat run instead shows the tradeoff above. Medium-case wall time
is also somewhat worse than previous Kush, though still below Rust.

[All sizes, rebuild/reuse controls and phases](inline/report.md) ·
[Raw inline data](inline/results.json).

### Original boxed metadata, large deliberate-reuse case

| Metric | Previous Kush | Current Kush | Rust CLIF |
|---|---:|---:|---:|
| Median wall time | 956.8 ms | 788.1 ms | 1,149.5 ms |
| Median process-tree CPU time | 908.8 ms | 766.3 ms | 1,125.4 ms |
| Median peak RSS | 19,308 KiB | 18,424 KiB | 18,016 KiB |
| Peak live requested heap | 13.883 MiB | 13.382 MiB | 13.127 MiB |
| Allocator requests (alloc + realloc) | 98,309 | 98,320 | 98,378 |

Kush is **31.4% faster** than Rust here, but uses **2.3% more peak RSS** and
**1.9% more peak requested heap**. This layout does not beat Rust on both
speed and memory. Retaining the boxed control prevents attributing the inline
application's result to automatic box elimination.

[All boxed controls](boxed/report.md) · [Raw boxed data](boxed/results.json).

## What changed and where the bytes went

Small ordinary buffers (total request at most 1024 bytes) no longer carry a
separate 16-byte private allocation header. Their existing capacity word
encodes the physical size class alongside logical capacity. Large and exact
fallible-grown buffers retain the original header. No libc usable-size guess,
side table, ownership relaxation or hidden allocation is introduced.

At the edited capacities (512 text bytes / 32 children):

| Inline document component | Previous Kush | Current Kush | Rust |
|---|---:|---:|---:|
| Outer slot, including metadata node | 32 B | 32 B | 64 B |
| Text storage | 544 B | 528 B | 512 B |
| Child storage | 288 B | 272 B | 256 B |
| Total | **864 B** | **832 B** | **832 B** |

Removing two private headers saves 32 bytes/document: 0.5 MiB over 16,384
documents. Small parser/pool allocations and serialization transients explain
the remaining few KiB at the measured peak. The boxed case retains a private
metadata-box header and stays 16 bytes/document above Rust (856 versus 840).
Resident memory also depends on libc size classes, fragmentation, code pages
and retained pool blocks; it is not determined by requested bytes alone.

## Initial regression and correction

The initial header-only implementation did reduce memory but was **10.4%
slower than previous Kush** in its large inline case (956.9 versus 866.7 ms).
Those absolute times belong to a different cohort. The raw data is retained:
[initial header-only results](header-only-inline/results.json).

Capacity decoding occurred in hot byte-push loops. The correction uses a
16-bit decoder for the proven-small case and a checked inline release-mode
append when capacity is available. The original helper retains growth,
overflow and full reserved-buffer failures. Positive large capacity words
still use their full width. Range checks remain before byte stores. This
mitigates the initial regression but does not justify claiming a universal
speed improvement over the previous implementation.

## Validation and identity

- Final full Boat gate: **1,169 passed, zero failed**; formatting and strict
  all-target workspace Clippy passed. Sandbox stopped afterwards. An earlier
  header-only gate passed 1,165 tests before four append-path tests were added.
- Default/release tests cover raw/large transitions, full large capacities,
  negative/out-of-range bytes, reserved logical capacity despite physical
  slack, and exact native/reference logical allocation-stat equality.
- Direct C checks cover sizes 0..1100, alignment, retained capacity after map
  narrowing, failed/successful growth, pool count reset, drain and retained
  double-release rejection. Current-source AddressSanitizer and Undefined-
  BehaviorSanitizer checks passed with leak detection enabled.
- Every cohort passed 24 canonical JSON/oracle cases, current evaluator/native
  comparisons, invalid-argument checks and every measured-run checksum. Every
  newly tracked workload allocation/byte was released at exit.
- Both free-list families share the existing per-class and global byte caps.
  Some mixed workloads lose cross-family pool hits; the extra small request
  counts are visible in the raw data. No runtime logical counters were hidden.
- Previous CLI SHA-256:
  `56fdad191f3d4a5da51621db41107b64844648e6b553eb30ac3df46a7dc024f0`.
- Current CLI SHA-256:
  `3153476046530ad689830f091f6d8203bb438e73ede77e41a30a15da92f0e25f`.

Reproduce using [the harness](../../README.md), with and without
`--inline-metadata`, and `--previous-compiler` for the same-cohort baseline.
`confirm.py` performs no builds: it verifies a bundle's binary hashes, checks
its output against the JSON oracle, and measures each child with `wait4`.
The Boat bundle contained only application executables and their manifest;
no host credentials or target-directory cache was copied.

[Interactive comparison](comparison.html). Logs:
`/tmp/kush-boat-headerless-fast-final.log`,
`/tmp/kush-headerless-fast-inline-benchmark.log`,
`/tmp/kush-headerless-fast-boxed-benchmark.log`,
`/tmp/kush-boat-headerless-confirm.log`.
