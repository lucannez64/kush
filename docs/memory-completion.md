# Memory and optimization completion contract

Status: implemented in the checked executable subset and in both the reference
evaluator and the native Cranelift backend, with the boundaries stated below.
This document supersedes the "explicit boundaries" lists in
[reuse.md](reuse.md), [vector-reuse.md](vector-reuse.md), and
[allocator-pool.md](allocator-pool.md) for the five backlog items it covers.
It does not claim a general optimizer, a general allocator, or performance
superiority.

```sh
cargo test -p kush --test memory_completion
cargo test -p kush --test reuse --test vector_reuse --test allocator_pool
python3 scripts/memory-bench.py --kush target/release/kush
```

## 1. Automatic fusion with an equivalence argument

`Vec.map_in_place(Vec.map_in_place(values, f), g)` is still the source shape.
A post-check analysis now decides whether the two traversals may be merged:

```text
f(e0), g(e0), f(e1), g(e1), ...
```

instead of

```text
f(e0), f(e1), ...; g(e0), g(e1), ...
```

A callback is **fusion-safe** only when all of the following hold:

- it is a noncapturing `fn(...)` value;
- its declared effect row contains none of `io`, `suspend`, or `panic`; only
  the empty row or an `alloc`-only row is accepted;
- its body is structurally total: no `while`, no `loop`, no direct or mutual
  recursion, no indirect call, and no structured-task operation;
- every direct callee is itself fusion-safe.

The intermediate element type must agree (`inner_target == source`), and each
step already satisfies its own non-increasing width rule. For a step with a
non-empty (`alloc`-only) effect row, the intermediate type must additionally be
non-owning. That keeps the drop order of every intermediate observably
identical: a fused traversal keeps at most one intermediate live instead of a
whole second vector. Pure (empty-effect) steps keep the pre-existing behaviour,
including owning intermediates consumed by the next callback.

The analysis is selected after every body has been checked, so it inspects the
actual checked IR rather than guessing from source types. `fusions` counts each
merged map layer. Inline selection during type checking was removed so a pure
callback with a loop or recursion cannot slip through a weaker check.

### Why this is semantics-preserving

With no `io`, `suspend`, or `panic`, callback execution produces no observable
trace and cannot change scheduling, cancellation, or the location of a
language-level panic. Structural totality means each callback makes finitely
many steps; the only remaining effect is allocation, which is a resource event
rather than a program-visible trace. A fallible allocation becomes a checked
value in both orders, and an aborting allocation ends the process in both
orders. Allocation *counts* are unchanged by fusion. Peak live storage and the
relative order of physical allocation/free events may differ; those are
tooling observations, not language results, and the benchmark harness measures
them instead of assuming them.

Arbitrary effectful interleaving is deliberately **not** enabled. A callback
with `io`, `panic`, or `suspend` keeps the original pass-by-pass order because
fusing it would move output, panic sites, or scheduling points. `Vec.map_chain_in_place`
remains the explicit operation that chooses interleaved order at the source
level; it is never counted as automatic fusion.

### Unresolved generality

The analysis is conservative, not a general termination or effect prover. It
does not prove termination of loops, does not handle recursion or indirect
calls, does not prove a `panic`-effect callback panic-free, and does not merge
through effects other than `alloc`. Those cases remain explicit non-fusions.
The engine never treats a rejection as a proof that the original shape is
incorrect or unsafe; it simply leaves both passes intact.

## 2. Widening reuse: `Box.reuse_grow`

```rust
let owner: Box<i64> = Box.new(1);
let owner: Box<[i64; 2]> = Box.reuse_grow(owner, [20, 22]);
```

`Box.reuse_grow` consumes an owned `Box<T>` and returns a `Box<U>`:

- Both arguments are evaluated strictly, left to right, before mutation.
- If the new payload fits the existing allocation, the allocation is kept and
  no allocator call occurs. If it is wider, storage may grow and **move**.
- The operation requires `{alloc, panic}`. A growth is an allocating fallback
  and can abort on allocation failure. `#[noalloc]` rejects the operation from
  its source signature; there is no hidden allocating fallback in `Box.reuse`
  or under `#[noalloc]`.
- The old affine payload is destroyed exactly once after both arguments are
  evaluated and before the new payload is written. A linear old payload is
  rejected; an owning payload that may carry a propagated binding obligation is
  rejected exactly as for `Box.reuse`.
- A binding-based `@[1]` obligation on the old owner transfers to the returned
  owner, and a linear new payload keeps its obligation on that owner. Narrowing
  remains legal, so the same operation covers shrinking and growing.
- Bytes beyond the new payload's inline width are stale padding. They are never
  read: every operation is typed by the current owner's width, and a later
  reuse drops only the current width. Growth copies the old block's `usable`
  capacity before releasing it; the old block is released exactly once.

The reference evaluator models the allocation as one logical identity and
always "fits"; the native runtime calls the header-aware grow path, which
returns the same payload when the recorded usable capacity already covers the
new size. Allocation/deallocation counters are unchanged either way, and the
stable `reuses` counter increments once per successful operation.

## 3. Fallible allocation and reuse

These operations return the conventional `Result<T, E>` declared in the file;
there is no process abort disguised as `Err`. They require the exact
`enum Result<T, E> { Ok(T), Err(E) }` shape used by `?` and I/O.

| Operation | Success | Failure | Effects |
| --- | --- | --- | --- |
| `Box.try_new(value)` | `Ok(Box<T>)` | `Err(value)`: the untouched payload | `{alloc}` |
| `Box.try_reuse(owner, payload)` | `Ok(Box<U>)`, possibly grown/moved | `Err(owner)`: the original allocation and payload intact | `{alloc}` |
| `Bytes.try_with_capacity(n)` | `Ok(Bytes)` with exact capacity `n` | `Err(n)`: the requested capacity | `{alloc}` |

- `Box.try_new` moves the payload into the box on success and returns the same
  owner unchanged in `Err`. Cleanup is therefore exact on both paths.
- `Box.try_reuse` requires a **non-owning** new payload. The old owner is
  preserved in `Err` without dropping its payload; because the new payload owns
  nothing, refusal loses no supplied owner. On success the old payload is
  destroyed once, the new payload is stored, and a growth may move the block.
  A request that needs no growth cannot fail.
- `Bytes.try_with_capacity` rejects negative and overflowing requests as
  `Err(requested)`; ordinary `Bytes.with_capacity` still aborts on those. The
  reference evaluator keeps its existing 16 MiB modeled byte-buffer budget, so
  a request above that budget is a reference `Err` even if a host allocator
  could satisfy it. Native runs are limited by the real allocator and by
  `KUSH_MAX_CAPACITY`; parity tests use sizes inside the reference budget.
- The runtime uses `kush_try_alloc`/`kush_try_grow`, which report system
  allocator refusal instead of calling `kush_panic`. Ordinary `kush_alloc` and
  `kush_grow` still abort. The pool's logical counters change only on success.

### Deterministic failure probes

Reference evaluation accepts a fallible-allocation budget:

```rust
let program = check(source)?;
let (value, stats) = program.evaluate_with_alloc_budget(&mut output, 0)?;
```

The budget charges only fallible attempts, not ordinary allocation. Zero makes
the next fallible attempt fail; a non-widening `Box.try_reuse` still succeeds
because it performs no allocator action. This is a reference test tool, not a
language effect or a native limit.

The native runtime supports a test-only probe:

```sh
KUSH_ALLOC_FAIL_AFTER=0 ./program
```

It applies to `kush_try_alloc` and growth-capable `kush_try_grow` attempts
only; ordinary allocation ignores it. A real `aligned_alloc` failure returns
the same `Err` paths, and a huge `Bytes.try_with_capacity` request is rejected
for size overflow before touching the allocator. The environment variable is
documented as a fault-injection hook, not a production policy.

Tests cover reference/native agreement on success, budget and fault-injected
failure, an overflowing native request, payload/owner preservation on failure,
and balanced cleanup on every path.

## 4. Allocator ownership: the built-in `Arena`

The supported allocator abstraction is a built-in bump-allocation region. No
FFI and no arbitrary user-defined allocator callback is implemented or
claimed.

```rust
let arena = Arena.new();
let first = Arena.alloc(&arena, 20);       // ArenaBox<i64>
let second = Arena.alloc(&arena, 22);
drop(arena);                               // safe: the boxes retain the region
ArenaBox.take(first) + ArenaBox.take(second)
```

- `Arena.new()` is one logical allocation (the region descriptor). Internal
  chunks are physical storage obtained directly from the system allocator and
  are not counted as separate logical allocations; the region is one logical
  deallocation when its last reference is released.
- `Arena.alloc(&arena, value)` requires `{alloc, panic}`. It borrows the arena
  for the call and returns an owning `ArenaBox<T>` that retains one region
  reference. The region therefore cannot be used or freed after the last
  reference disappears.
- `ArenaBox.read(&box)` reads a copyable payload. Ownership rejects copying an
  owning or linear payload, exactly as `Box.read` does.
- `ArenaBox.take(box)` moves the payload out and releases the box's region
  reference without dropping the payload. Dropping a box normally destroys the
  payload exactly once and then releases the reference.
- Dropping the `Arena` value while boxes are live is safe and defined: the
  boxes still keep the region alive. What would be a use-after-allocator-drop
  is not a reachable operation. The ordinary ownership checks still reject
  using the arena *variable* after moving it (for example `drop(arena)` followed
  by `Arena.alloc(&arena, ...)` reports "cannot borrow a moved owner").
- Linear payloads and payloads that may carry a propagated binding obligation
  are rejected: a region destroys remaining contents implicitly, so it cannot
  hide a linear obligation.
- `Arena` and `ArenaBox<T>` may cross function boundaries, and a box may be
  captured by a structured task; the region reference travels with the box and
  is released when the task or its joined value drops it.

Limits: chunks are only freed when the whole region is released; there is no
per-value `free`, no allocator trait, no user callback, no `realloc` inside a
region, and no claim that an arena is faster for every workload. Region
allocation failure aborts through the ordinary `panic` path of `Arena.alloc`;
a fallible region API is not implemented.

## 5. Reproducible benchmark harness

`scripts/memory-bench.py` builds one native binary per workload, warms it up,
runs timed repetitions, and records:

- the stable `allocation-stats:` line for native and reference evaluation at a
  small parity size (the harness fails if they disagree);
- native wall time measured around the child process and maximum RSS from
  `/usr/bin/time -f %M`;
- `allocator-pool: ... peak-retained-bytes` for native runs;
- workload scale, iteration count, and per-run medians.

```sh
cargo build --release -p kush
python3 scripts/memory-bench.py --kush target/release/kush --repeats 7
python3 scripts/memory-bench.py --kush target/release/kush --json memory.json
```

Workloads are deterministic source templates: box reuse versus box replacement,
an in-place vector map, reserved byte pushes, and arena allocation/take. The
harness reports measured numbers and comparisons such as allocation counts; it
does not assert that one spelling is faster, does not use wall time as a proof,
and does not compare across machines as if that were reproducible. Use the same
machine, binary, and iteration count to compare revisions.

The stable diagnostics line is unchanged:

```text
allocation-stats: allocations=<n> deallocations=<n> peak-live=<n> buffer-growths=<n> reuses=<n> fusions=<n>
```

It remains a tooling observation about one execution, never a language effect
or a proof obligation.

## Test map

- `crates/kush/tests/memory_completion.rs`: fusion positives and rejections
  (I/O, panic, loops, recursion, indirect calls), explicit-chain non-fusion,
  widening reuse and owner obligations, fallible success/refusal with the
  reference budget and the native probe, overflow, arena lifetime and task
  capture, provenance rejections, and reference/native diagnostics parity.
- `crates/kush/tests/reuse.rs`, `vector_reuse.rs`, `allocator_pool.rs`: existing
  same-allocation reuse, pure-map fusion, explicit chains, pool bounds, and
  stable diagnostics.
- `scripts/memory-bench.py`: measured counters, RSS, timing, and retention.

## Explicitly still absent

- arbitrary user-defined allocator implementations or allocator callbacks, and
  any FFI allocator interface;
- per-value free or compaction inside an arena;
- automatic fusion of effectful (`io`, `panic`, `suspend`), recursive, looping,
  or indirectly called callbacks;
- a general termination proof or a general effect system for fusion;
- performance or physical-memory superiority claims;
- payload-byte accounting in the stable diagnostics line.
