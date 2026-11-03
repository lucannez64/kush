# Compact headers and bounded class retention: measured correction

Compiler checkpoint `528a804`, measured locally on the same Ryzen 5 PRO 5675U laptop. Old/current Kush and Rust controls ran in one shuffled cohort on CPU 11. Timing/peak RSS use seven samples after two warmups. Phase RSS uses three independent uninstrumented probes, with medians and raw frames retained. Allocation tracing is separate.

## Changes

- Compact the private allocation header from 32 to 16 bytes: retain the full usable-capacity word and share a union between the live marker and inactive free-list link. Alternate live markers encode small-block eligibility without another word. Payload alignment remains 16 bytes.
- Keep at most 64 free blocks per size class as well as the existing global 1 MiB budget. Overflow blocks return to libc; live allocations are never reclaimed by this policy.
- Source checking, allocation effects, buffer capacities, fallible-probe ordering, logical allocation diagnostics and owner/drop behavior stay unchanged. No nominal-record tags or public buffer layouts were removed.

## Large corpus, deliberate reuse

16,384 documents × 31 alternating edits; includes seed parse, construction, edits, serialization, drop, a fresh small corpus, and cleanup.

| Metric | Previous Kush | Current Kush | Rust CLIF reuse |
|---|---:|---:|---:|
| Peak requested live heap | 16.252 MiB | 14.510 MiB | 13.127 MiB |
| Median peak RSS | 21580 KiB | 20296 KiB | 18068 KiB |
| Median RSS after large corpus release | 12908 KiB | 6288 KiB | 4608 KiB |
| Allocator requests (alloc + realloc) | 98,315 | 98,314 | 98,378 |
| Cumulative requested bytes | 40.502 MiB | 39.001 MiB | 35.693 MiB |
| Median wall time | 2318.525 ms | 2284.350 ms | 2905.153 ms |

Peak requested heap falls **10.7%**, median peak RSS falls **5.9%**, and post-release RSS falls **51.3%**. Reuse timings remain close within this cohort. Absolute times differ substantially from the earlier laptop snapshot for every control; this analysis compares matched old/current binaries, not times from separate sessions.

This reduces the gap, but current Kush still uses **10.5% more peak requested heap** and **12.3% more peak RSS** than Rust reuse here. It is not a memory-parity claim.

## Requested-byte explanation

At the large document capacities (512 text bytes / 32 children), per-document requested allocation accounting changes from **976 bytes to 928 bytes**. Metadata box: 64 → 48; text buffer: 560 → 544; child buffer: 320 → 304; outer document slot: 32 unchanged. This saves **0.75 MiB** across 16,384 documents. Buffer/record tags and Rust's inline Vec representation still account for remaining differences.

The peak retained pool in the reuse run falls from **1,048,544 bytes to 63,680 bytes**. The pool at the high-live-heap phase is smaller still: old text/child-buffer classes stop accumulating after 64 entries. Resident retention can exceed cached requested bytes because libc controls page release and fragmentation; the experiment measures RSS rather than equating these quantities.

## The cost of lower retention

At 256 documents, rebuild-only Kush allocator requests rise from **1,552 to 13,102**; wall time rises from 50.338 to 53.689 ms. At the largest corpus, rebuild requests rise from 835,946 to 1,077,550. This is a memory-versus-cache-hit tradeoff, not a universal performance improvement. The deliberate reuse path avoids that recurring traffic. Small-process RSS does not consistently decrease because fixed residency dominates.

## Validation and measurement integrity

- Full Boat gate at `528a804`: **1,149 tests**, formatting and strict workspace/all-target Clippy passed; sandbox stopped with its snapshot preserved.
- Local focused checks: 105 tests covering the C runtime, allocator pool, fallible memory, native release modes and Rust/C interop, plus the fortified-libc portability correction.
- Direct C runtime checks cover alignment, zero/class-boundary allocations, both live markers, growth contents, fallible hits, class counts, count reset, corruption and double-release rejection.
- Independent JSON oracle: 24 full-output cases across old/current/Rust rebuild/reuse, plus current Kush reference/native agreement and invalid-argument checks. All measured-run checksums matched.
- The preserved baseline compiler hash matches the original archived JSON benchmark. Old and current applications were rebuilt with exactly the same updated C probes.
- The tracer now inserts at the first available tombstone for a fresh allocation address. This removes a long-probe artifact under realloc-heavy Rust workloads without allocating bookkeeping storage. Known-size malloc/calloc/aligned/realloc/refusal/peak/final-live self-tests passed. Tracer execution time is not used as application performance.
- Every newly tracked workload block and byte is released at exit, including the final pool drain. Header changes and lower retention do not relax borrowing/ownership checks.

The first Boat attempt found a source-swap failure caused by read-only old generated files. The swap now promotes the verified upload before best-effort old-tree cleanup, rolls back a failed promotion, and aborts checks on failure. The next attempt exposed GCC's warning on existing intentionally ignored diagnostic-write returns; explicit best-effort handling fixed that while keeping strict C warnings enabled. The final full gate passed.

Logs: `/tmp/kush-compact-pool-final-tests.log`, `/tmp/kush-compact-pool-clippy.log`, `/tmp/kush-compact-runtime-portability.log`, `/tmp/kush-boat-compact-pool-final.log`. See [raw results](results.json), [all sizes and phases](report.md), and the [benchmark README](../../README.md).
