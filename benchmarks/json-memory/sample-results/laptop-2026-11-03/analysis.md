# Interpretation: laptop checkpoint, 2026-11-03

This cohort was measured locally at workload checkpoint `4b061f9`, on an AMD Ryzen 5 PRO 5675U, CPU 11. Seven timing/RSS samples after two warmups; separate allocation-trace and phase-RSS processes. Both languages use Cranelift; Rust editing uses safe APIs and the same shared C probe. The report generator adds derived request counts and phase selectors after measurement; its own hash is recorded separately.

## The fair reuse comparison

16,384 owned documents, 31 alternating edit batches, then serialization, release and a fresh 16-document corpus.

| Metric | Kush reuse | Rust deliberate reuse |
|---|---:|---:|
| Allocator requests (alloc + realloc) | 98,315 | 98,378 |
| Peak live requested heap | 16.252 MiB | 13.127 MiB |
| Median peak RSS | 20.980 MiB | 17.598 MiB |
| Bytes requested cumulatively | 40.502 MiB | 35.693 MiB |
| Median total wall time | 636.375 ms | 808.492 ms |

Kush uses 23.8% more peak requested heap and 19.2% more peak RSS. It takes 21.3% less wall time here. Allocator-request totals are effectively equal; their difference is a small fixed startup/parser/shrink-workload offset. **This does not establish a memory advantage over deliberate Rust reuse.**

## Where reuse and pooling help

Rebuilding Rust makes 3,686,474 successful allocation/reallocation requests. Kush reuse makes 98,315: 97.3% fewer. That comparison is useful for churn, but Rust reuse removes almost the same requests. Within Kush, reuse cuts requests from 835,946 to 98,315.

Kush rebuild also has fewer libc requests than Rust rebuild because its bounded pool serves many requests without going back to libc. Reallocations can happen in place: the large Rust rebuild trace has 743,518 in-place reallocations and 1,353,634 moved reallocations. Neither allocator requests nor moved reallocations are OS page-allocation counts.

## Retention deserves separate attention

The diagnostic large-run phase probe reads 12,916 KiB RSS for Kush reuse after the large corpus is dropped, versus 4,656 KiB for Rust reuse. These are single phase snapshots, not medians. Kush has only about 1 MiB of outstanding requested pool storage at that point, so byte retention and resident-page retention are different quantities. The experiment does not isolate which share comes from pool policy, libc retention, or fragmentation. At normal exit the pool drains; the tracer reports zero newly workload-allocated live blocks and bytes for every variant.

## Where the requested-heap gap comes from

Source-layout accounting for one large-phase document is consistent with the
recorded stage-2 requested-byte totals (x86-64, capacities 512 text / 32 children):

| Heap component, per document | Kush requested bytes | Rust requested bytes |
|---|---:|---:|
| Boxed metadata | 64 | 16 |
| Text buffer | 560 | 512 |
| Child-number buffer | 320 | 256 |
| Document slot in outer vector | 32 | 56 |
| **Subtotal** | **976** | **840** |

Kush's metadata box includes its record tag, 16-byte class rounding and 32-byte
allocation header. Buffer rows include runtime/allocation headers and padding.
Rust keeps Vec descriptors inline in the outer document slot, which is why its
slot is larger but its separate buffers are smaller. These are requested bytes,
not usable-size or RSS estimates.

Across 16,384 documents the subtotal gap is **2.125 MiB**. Kush additionally
retains 1,048,544 bytes in its bounded pool. The trace's stage-2 totals reconcile
exactly with these subtotals plus the fixed outer header, seed, and recorded Rust
startup baseline. The serialization buffer makes the observed peak slightly
higher than this stage snapshot. This accounting explains requested heap; it
does not explain resident-page behavior after frees.

## Next optimization targets suggested by this measurement

- Measure a controlled smaller-header/layout variant. Kush currently adds 32-byte allocation headers, word-granular record tags, runtime buffer headers and size-class padding. The large-phase layout budget above identifies the requested-byte overhead; an actual optimization still needs measurement across other layouts and workloads.
- Test pool-drain/retention policies at an explicit low-memory boundary, then measure both retained requested bytes and RSS. A 1 MiB cap alone does not guarantee only 1 MiB of resident retention.
- Keep the deliberate Rust reuse control. Improving only the rebuild comparison would hide the actual memory gap.

## Validation

- Known-size C recorder self-test: malloc, calloc, aligned_alloc, posix_memalign, successful realloc, refused realloc, exact peak and final-live accounting.
- Sixteen full-output cases across four variants: independent Python JSON values, byte-for-byte encoding and checksums.
- Two Kush reference/native output comparisons with foreign no-op probes removed.
- Invalid argument cases rejected consistently.
- All measured-run checksums matched; all trace runs released every newly tracked workload allocation by exit.
- C builds pass `-Wall -Wextra -Werror`; Rust application passes strict Clippy and rustfmt.
- Measurements and builds ran locally with spare capacity, Rust builds limited to two jobs, and runtime measurements pinned to CPU 11. No local builds ran alongside timing samples.

Raw samples, binaries/source hashes, compiler versions, environment settings, logical Kush counters, pool counters and phase frames are in [results.json](results.json). The peak-RSS binaries contain no allocation recorder. See the [benchmark README](../../README.md) for the measurement domain and limitations.
