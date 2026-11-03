# Headerless small ordinary buffers

Ordinary `Bytes`, `String`, and `Vec<T>` buffers whose allocation request is at
most 1024 bytes now omit the separate 16-byte `KushAllocHeader`. Their existing
16-byte length/capacity prefix and data offset remain unchanged. This removes
one allocation header per qualifying buffer, without removing bounds checks,
changing public logical capacity, or relying on libc's incidental usable size.

Vectors encode a marker and their physical 16-byte size class (1 through 64)
in the high byte of the capacity word; its low 16 bits hold logical capacity.
The intervening bits stay reserved. Small vectors cannot approach that limit.
Larger and exact fallible-grown vectors retain the original allocation header
and complete positive capacity word.

Bytes and strings keep an ordinary, unencoded capacity word on the hot path.
Their element width never changes, and their public capacity never shrinks:
the raw physical class is always `round_up(16 + capacity, 16)`. This remains
true when a push grows logical capacity within existing class slack. Growth
and typed byte-buffer release reconstruct the pool encoding immediately
before calling the shared buffer allocator. Byte appends and capacity reads
therefore need no tag test, mask, or conditional move. Large byte buffers keep
the original private header. No full-width supported capacity is truncated.

The encoded physical class survives `clear`, narrowing maps, logical capacity
changes, and subsequent widening. Growth copies the recorded usable extent,
reinstalls the destination's capacity encoding, and releases the old block
once. Exact fallible-grown buffers retain the original header even when small;
this preserves their exact capacity across later no-op operations. A fallible
request that fits retained storage still bypasses both allocation and the
failure-injection probe. Refusal leaves the old owner and metadata intact.

Headerless and header-bearing blocks use separate intrusive free lists and
share the existing 64-block-per-size-class and 1 MiB physical-byte limits.
Inactive headerless blocks keep the next pointer in the unused length word
and an invalid class marker in the capacity word. Normal exit drains both
families. Typed destruction uses `kush_bytes_free` for Bytes/String and
`kush_buffer_free` for vectors; boxes, task blocks,
closures and allocator contexts continue to use the original header-aware
release. Logical allocation diagnostics retain their existing meaning.

Vector capacity reads decode the logical value; release-mode `Vec.push` does
so inline. Bytes/String capacity reads load the plain word. Host I/O, custom-allocator backing byte
blocks and the Rust/C bridge keep the same data offsets and opaque handles.
User-allocator container descriptors (`AllocBox`/`AllocVec`) have their own
protocol and remain header-bearing.

Release byte appends use an inline, range-checked fast path when capacity
is available; the original runtime helper handles cold growth and full-buffer
failures. Release-mode length, capacity and clear operations are lowered
directly into Cranelift, including String byte length. Checked byte reads stay
a runtime call: inlining them shifted a hot loop and slowed an older core (see
the plain-capacity analysis). UTF-8 scalar operations retain their original
runtime. Vector appends keep the
compact capacity decoder.

The tradeoff is a few instructions for decoding and separate pool families.
Some mixed allocation workloads may get fewer cross-type pool hits. Larger
ordinary buffers and exact fallible-grown buffers still pay for the original
header. Speed, requested heap, allocator requests and resident memory therefore
need separate measurements; reduced per-buffer storage does not establish a
universal performance improvement.

Direct C-runtime checks cover capacities 0 through 1100, alignment, content
preservation, the small/large transition, non-truncating positive capacity
words, retained capacity after map narrowing, refusal and successful growth,
class-count reset, final drain and retained double-release rejection. Local
AddressSanitizer/UndefinedBehaviorSanitizer probes exercise the same small-to-
large transitions. Language tests cover allocator containers, fallible memory,
vector reuse, host APIs and physical pool accounting.

## Validation and measurements

Compiler checkpoint `516b360`: the full Boat gate passed **1,169 tests**,
formatting and strict Clippy. Direct AddressSanitizer/UndefinedBehaviorSanitizer
checks passed locally. The sandbox was stopped after validation and confirmation.

The [matched speed/memory report](../benchmarks/json-memory/sample-results/headerless-buffers-2026-11-03/analysis.md)
includes old/current Kush and Rust controls, boxed/inline layouts, an initial
header-only speed regression, a corrected append fast path, and a low-load Boat
confirmation. It records the remaining speed tradeoff versus previous Kush and
the distinction between peak RSS and requested heap.


The [plain-capacity follow-up](../benchmarks/json-memory/sample-results/plain-byte-capacity-2026-11-03/analysis.md)
removes byte-buffer decoding from the hot path while keeping those allocation
savings. The combined code passed 1,170 tests, formatting and strict Clippy on
Boat. Its matched Boat cohort improves speed versus both earlier Kush versions
and Rust, with the same requested heap as the earlier headerless implementation;
the busy-laptop speed result remains mixed. Raw data and exact scope are linked.
