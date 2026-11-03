# Compact records/vectors and inline metadata

Compiler source: `4f50070`; benchmark controls: `4d47b70`; remote freshness fix:
`f3e7f8a`. Same Ryzen 5 PRO 5675U laptop, glibc allocator, CPU 11. Both
languages use Cranelift. Each layout has its own matched old/new/Rust cohort:
seven timing/RSS samples after two warmups, three independent phase RSS probes,
and separate allocation-tracing binaries. Sizes: 256 and 16,384 documents;
31 alternating edits. Do not compare timing ratios across the two cohorts.

## Compiler-only improvement: original boxed application

| Large corpus, deliberate reuse | Previous Kush | Current Kush | Rust CLIF |
|---|---:|---:|---:|
| Peak live requested heap | 14.510 MiB | 13.883 MiB | 13.127 MiB |
| Median peak RSS | 20,304 KiB | 19,392 KiB | 18,004 KiB |
| Allocator requests (alloc + realloc) | 98,314 | 98,309 | 98,378 |
| Cumulative requested bytes | 39.001 MiB | 38.126 MiB | 35.693 MiB |
| Median after-large-drop RSS | 6,372 KiB | 5,860 KiB | 4,604 KiB |
| Median wall time | 2,294.2 ms | 2,265.7 ms | 2,912.7 ms |

Removing nominal struct tags and ordinary vector width metadata reduces peak
requested heap by **4.3%** and median peak RSS by **4.5%** without changing the
application's boxes. The heap gap versus Rust falls from **10.5% to 5.8%**;
the RSS gap falls from **12.8% to 7.7%**. Allocation counts stay essentially
equal on the reuse path. This is chiefly a representation improvement.

## Application layout: metadata inline in both languages

| Large corpus, deliberate reuse | Previous Kush | Current Kush | Rust CLIF |
|---|---:|---:|---:|
| Peak live requested heap | 14.010 MiB | 13.508 MiB | 13.002 MiB |
| Median peak RSS | 17,100 KiB | 16,584 KiB | 16,344 KiB |
| Allocator requests (alloc + realloc) | 81,930 | 81,926 | 81,978 |
| Cumulative requested bytes | 38.502 MiB | 37.750 MiB | 35.568 MiB |
| Median after-large-drop RSS | 5,368 KiB | 5,092 KiB | 4,092 KiB |
| Median wall time | 2,315.3 ms | 2,307.7 ms | 3,077.7 ms |

Kush now has **3.9% more peak requested heap** and **1.5% more peak RSS** than
the equivalent inline Rust control, with essentially equal allocator requests.
The box was removed explicitly in both sources. This does **not** establish
automatic box elimination by Kush, nor superiority over Rust memory management.
The boxed controls remain available. The generated [Kush inline source](inline/workload.kush)
is preserved alongside the raw measurements.

## Accounting for the remaining gap

At the edited capacities (512 text bytes / 32 children), requested bytes per
document, including its outer-vector slot, are:

| Component | Previous boxed Kush | Current boxed Kush | Boxed Rust |
|---|---:|---:|---:|
| Metadata box | 48 | 32 | 16 |
| Text storage | 544 | 544 | 512 |
| Child storage | 304 | 288 | 256 |
| Outer document slot | 32 | 24 | 56 |
| Total | **928** | **888** | **840** |

The compiler saves 40 bytes per boxed document, or 0.625 MiB over 16,384
documents. Nonempty nominal records no longer store a discriminator. The
ordinary vector buffer header is 16 rather than 24 bytes; its element width
is known statically at every compiled runtime call. Real enums and other
aggregate ABIs retain their tags. Allocation headers remain 16 bytes.

Inlining metadata leaves current Kush at **864** bytes/document versus Rust
at **832**: Kush pays 64 bytes for two buffer/allocation-header pairs, while
its thin handles save 32 bytes in the outer slot. That remaining net 32 bytes
accounts for 0.5 MiB across the large corpus. Small seed/parser allocations,
pool retention and serialization transients account for the small difference
between this payload accounting and the measured peaks. RSS additionally
depends on libc fragmentation and page retention; requested bytes do not
predict resident memory exactly.

The small-process results do not show a consistent RSS improvement because
fixed residency dominates. Rebuild allocator requests remain much higher than
reuse in both languages. Timings here do not indicate a meaningful new speed
change versus previous Kush, and are not a general language performance claim.

## Validation and reproducibility

- Full final Boat gate: **1,152 passed, zero failed**; formatting and strict
  workspace/all-target Clippy passed. Sandbox stopped with snapshot preserved.
- Local focused allocator/vector/memory/record tests: 79 passed, including the
  new zero-offset nested-field, owning-pattern/coercion and compacted-vector
  regression tests. Additional record-only borrowing/type suites passed during
  the earlier stage; the integrated Boat gate covers the final representation.
- Each layout passed 24 full canonical JSON/oracle cases over old/new/Rust
  rebuild/reuse, current Kush evaluator/native agreement, invalid arguments,
  and all measured checksums. The tracer self-test passed. Every newly tracked
  workload allocation/byte was released at exit in every traced run.
- `--skip-build` rejects a mismatched boxed/inline layout. Source/binary/toolchain
  hashes and every sample are retained in the raw result files.
- Installed CLI SHA-256:
  `a1af97e3268effd5e1058298896a8d8c744c1206498af814fab1eb16f93eeb34`.
  Installed CLI check/build and a 16-document/31-edit checksum smoke passed.

Two initial remote gates are **not** counted as passing. The first caught
layout-sensitive test inputs and formatting. The next verified new source
bytes but reused old test executables because uploaded mtimes predated the
cached build. The sync script now tracks per-file content hashes and refreshes
changed source timestamps without discarding dependency caches. The final run
explicitly rebuilt Kush and passed the corrected tests. No failed evidence was
discarded or reported as success.

Reproduce using the [benchmark instructions](../../README.md), with and without
`--inline-metadata`, plus `--previous-compiler` pointing to the preserved
pre-layout compiler. Its allocation header/pool already use 16 bytes/64 blocks
per class; this isolates the new record/vector change from the earlier pool
change. Linux/glibc and the documented seed-parser differences still apply.

[Boxed raw results](boxed/results.json) · [Boxed full report](boxed/report.md) ·
[Inline raw results](inline/results.json) · [Inline full report](inline/report.md) ·
[Interactive comparison](comparison.html)

Logs: `/tmp/kush-compact-layout-tests-final.log`,
`/tmp/kush-boat-compact-layout-fresh.log`, `/tmp/kush-layout-boxed-benchmark.log`,
`/tmp/kush-layout-inline-benchmark.log`.
