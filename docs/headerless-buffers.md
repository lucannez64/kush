# Headerless small ordinary buffers

Ordinary `Bytes`, `String`, and `Vec<T>` buffers whose allocation request is at
most 1024 bytes now omit the separate 16-byte `KushAllocHeader`. Their existing
16-byte length/capacity prefix and data offset remain unchanged. This removes
one allocation header per qualifying buffer, without removing bounds checks,
changing public logical capacity, or relying on libc's incidental usable size.

The capacity word uses its high byte for a marker and a 16-byte allocation
size class (1 through 64). Its low 16 bits hold logical capacity; the intervening bits stay reserved. Small
buffers cannot approach that capacity-bit limit: their physical allocation
already bounds the logical value. Larger buffers retain the original header
and their complete positive capacity word, so large supported capacities are
not truncated or capped by this encoding.

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
families. Typed buffer destruction uses `kush_buffer_free`; boxes, task blocks,
closures and allocator contexts continue to use the original header-aware
release. Logical allocation diagnostics retain their existing meaning.

Every runtime capacity read decodes the logical value. The release-mode
`Vec.push` fast path does so inline. Host I/O, custom-allocator backing byte
blocks and the Rust/C bridge keep the same data offsets and opaque handles.
User-allocator container descriptors (`AllocBox`/`AllocVec`) have their own
protocol and remain header-bearing.

Release byte appends use an inline, range-checked fast path when capacity
is available; the original runtime helper handles cold growth and full-buffer
failures. Vector appends share the compact capacity decoder.

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
