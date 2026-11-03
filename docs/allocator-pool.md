# Bounded native allocator pool

Status: implemented for the native (Cranelift) backend only. This is a runtime
optimization, not a source-language feature, a memory-safety proof, or a
real-time latency guarantee.

Native programs allocate owning storage (`Box`, `Bytes`, `Vec`, string copies,
closure environments, task control and result blocks) through the C runtime's
`kush_alloc`/`kush_free`. Small blocks now come from a bounded size-class cache
instead of always reaching the system allocator. The reference evaluator is
unchanged and never runs compiled code.

```sh
cargo run -p kush -- run examples/reuse.kush --stats
KUSH_ALLOCATOR_POOL_STATS=1 cargo run -p kush -- run examples/reuse.kush --stats
```

The first command prints exactly the stable `allocation-stats:` line. The
second adds one native-only `allocator-pool:` line; the program's stdout and
exit status are unchanged in both cases.

## Block layout

Every native allocation has a 16-byte header immediately before its payload:

| Field | Meaning |
| --- | --- |
| `usable` | Payload capacity in bytes, recorded at allocation time. |
| union: `magic` | While live, one of two markers records live state and pool eligibility. |
| union: `next` | While retained, the same word holds the next free-list block. |

The free-list link and live marker are never needed at the same time. Claiming
from a list reads the link before installing the live marker; release validates
that marker before writing a link. The exact-size/unpooled marker keeps growth
and free classification separate without another header word. Header size is
statically asserted to be 16 bytes.

The header size is a multiple of the requested 16-byte alignment and the
runtime asks the system allocator for 16-byte-aligned storage, so payloads
remain 16-byte aligned. The header is what makes `kush_free` exact: a handle is
always the payload pointer, the true block start is recovered by subtraction,
and the header is checked before release or growth. This is an internal
invariant check, not general invalid-pointer protection: an interior pointer or
a pointer to system-freed memory can be invalid to inspect, and a stale handle
can match a new allocation after a block is reused. Memory safety still depends
on the compiler's ownership and borrowing checks.

`kush_grow` replaces the runtime's former direct `realloc` calls (byte-buffer
push, vector push, and vector reserve). It checks the header, returns the same
payload when the requested capacity already fits in `usable`, and otherwise
allocates a replacement, copies the live capacity, and releases the old block
exactly once. Growth is non-counting in both directions: logical allocation
call counts and the caller's `buffer-growths` observation are unchanged, which
is why the reference and native diagnostics still agree.

## Size classes and retention

- Requests with a payload of at most 1024 bytes are rounded up to a 16-byte
  size class: 16, 32, ..., 1024 (64 classes). A zero-byte request maps to the
  smallest class.
- Requests above 1024 bytes are unpooled: exact-size system blocks that are
  released immediately on free.
- A freed small block returns to its class free list only while the total
  retained physical size (16-byte header plus padded payload) stays at or below
  1 MiB (1048576 bytes). Blocks that would exceed the cap go back to the system
  immediately, so the cache can never grow without bound.
- Each size class retains at most 64 free blocks. Excess blocks return to libc
  even while the global budget has space. This prevents a past burst in one
  size class from keeping thousands of blocks and crowding out other classes.
  Class counts decrease on both ordinary and fallible claims and reset on drain.
  This is a bound on retained blocks/bytes, not a bound on RSS: libc may keep
  pages after free.
- `aligned_alloc` sizes are checked for overflow (`header + payload + padding`)
  and allocation failure still aborts through `kush_panic`.
- Every retained block is released by `kush_pool_drain` on a normal exit,
  before the live-allocation check. Nothing is retained after the process
  finishes its `main`.

Task control blocks and task result buffers use the same header-aware
`kush_alloc`/`kush_free` path; a large control block is simply unpooled.
Coroutine stacks still use `mmap`/`munmap` with their guard page and are not
part of the pool.

## Diagnostics

The stable line is unchanged, byte for byte:

```text
allocation-stats: allocations=<n> deallocations=<n> peak-live=<n> buffer-growths=<n> reuses=<n> fusions=<n>
```

`allocations`, `deallocations`, and `peak-live` count logical
`kush_alloc`/`kush_free` calls. A pooled physical hand-off is not an allocation
and a retained block is not a live owner, so these counters are identical to the
pre-pool runtime and, apart from tasks and stacks, to the reference evaluator.
`buffer-growths` still counts one successful capacity change per logical growth,
even when the retained size class already had room and no new block was
requested.

An opt-in native-only line is available in `--stats` builds:

```sh
KUSH_ALLOCATOR_POOL_STATS=1 ./program
```

```text
allocator-pool: hits=<n> misses=<n> retains=<n> releases=<n> drained=<n> retained-bytes=<n> peak-retained-bytes=<n>
```

| Field | Meaning |
| --- | --- |
| `hits` | Small allocations served from a class free list. |
| `misses` | Small allocations that needed a new system block. |
| `retains` | Freed blocks kept in a class instead of being released. |
| `releases` | Freed blocks (pooled or unpooled) returned to the system. |
| `drained` | Retained blocks released by the normal-exit drain. |
| `retained-bytes` | Retained physical block bytes at print time; always 0 after the drain. |
| `peak-retained-bytes` | Highest retained physical block bytes observed; at most 1048576. |

The line is guarded by both `--stats` and the environment variable so the
stable one-line interface never changes by default and non-stats builds are
byte-identical under any environment.

Pooling does not reuse reference allocation IDs, does not change whether an
operation has the `alloc` effect, and does not relax `#[noalloc]`: those are
checked from source and effects, not from allocator behavior. `Box.reuse` and
in-place vector transforms keep their existing "same allocation" guarantees.

The source-level allocator strategy and fallible allocation contracts are in
[memory-completion.md](memory-completion.md). The pool remains an internal
physical optimization; `Arena` chunks are intentionally outside its logical
counting and fallible operations use separate non-aborting runtime entry points.

## Limits

- The pool is small-block-only and single-threaded, matching the runtime's one
  OS thread and strict task hand-off.
- Retention is bounded by physical block bytes, not by a block count, and is
  drained only on a normal exit. A panicking program aborts the process as
  before.
- Size classes cover payloads up to 1024 bytes. Larger buffers, including grown
  vectors and byte buffers, still pay one system allocation per growth.
- The pool is a storage-reuse optimization; its latency has not been benchmarked. It does not promise a worst-case
  allocation time, and it is not a substitute for capacity proofs.

## Tests

`crates/kush/tests/allocator_pool.rs` covers:

- opt-in diagnostics and a byte-identical `allocation-stats:` line with and
  without pooling;
- physical hits for repeated boxes, bytes, and vectors;
- zero-capacity buffers and the exact 1024/1025-byte class boundary;
- buffer growth from pooled to unpooled storage with content preservation,
  including a logical growth that fits inside the retained class;
- `Vec.clear`, `Vec.reserve`, and `Bytes.push_reserved` integration, including
  the `#[noalloc]` contract;
- task result blocks served from the same header-aware path;
- nested owner cleanup and checked overflow rejection; and
- per-class burst retention, the independent 1 MiB global cap, and a full drain at exit;
- direct C-runtime checks for the compact header, payload alignment, live/free
  marker transitions, corruption/double-release rejection, growth contents,
  fallible pool hits, and class-count reset.

Run them with:

```sh
cargo test -p kush --test allocator_pool
```

## Compact-header and retention checkpoint (2026-11-03)

Compiler `528a804` passes the full Boat gate (1,149 tests, formatting, strict
Clippy). Local direct C checks also cover alignment and marker state, fallible
pool hits, growth and both retention bounds. The stable logical stats format
is unchanged; physical byte expectations reflect the 16-byte header.

The [matched JSON editor comparison](../benchmarks/json-memory/sample-results/compact-pool-2026-11-03/analysis.md)
measures lower live heap and post-release RSS. Limiting retained blocks also
increases libc requests for rebuild-heavy batches; this policy makes a bounded
memory/cache-hit tradeoff. Deliberate buffer/box reuse remains preferable when
the application can retain its own capacity.
