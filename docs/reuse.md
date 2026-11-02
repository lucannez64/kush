# Checked reuse, in-place transforms, and allocation diagnostics

Status: implemented for the executable value subset in both the reference
evaluator and the Cranelift backend. This milestone provides explicit,
checked storage-reuse operations and observable allocation tooling. It does not
add a general optimizer, an allocator implementation, or a claim that a
transformation is always faster.

```sh
cargo run -p kush -- check examples/reuse.kush
cargo run -p kush -- eval examples/reuse.kush --stats
cargo run -p kush -- run examples/reuse.kush --stats
```

The example prints `100`, `4`, and `3`. Its 100-step box update performs one
allocation, and its vector transforms keep the original vector allocation.
The allocation diagnostics line is described [below](#allocation-diagnostics).

## Checked unique box reuse

```rust
let owner: Box<i64> = Box.new(0);
let current = Box.read(&owner);
let owner: Box<i64> = Box.reuse(owner, current + 1);
```

`Box.reuse(owner, new_payload)` consumes an owned `Box<T>` and returns a
`Box<U>` that uses the **same allocation**. There is no allocating fallback:

- Both arguments are evaluated strictly, left to right, before any mutation.
- After both succeed, the old payload is destroyed exactly once.
- The new payload is then written into the preserved allocation.
- If the new payload's inline layout is wider than the old payload's, checking
  fails. The safe direction is `width(U) <= width(T)`; a narrower payload simply
  uses fewer words of the existing storage.
- `Box.reuse` has no `alloc` effect. It is legal under `#[noalloc]` when the
  argument expressions themselves do not allocate, and `Box.reuse` cannot hide
  an allocation that the source did not declare.
- The old payload must be affine. If it carries a `#[linear]` obligation,
  `Box.reuse` is rejected because it would destroy that value implicitly. Take
  the payload out and consume it explicitly instead. A linear owner whose old
  payload itself owns resources is also rejected conservatively: a binding-based
  obligation may have been transferred into that payload by boxing or a
  constructor, even when its nominal payload type is affine.
- A binding-based `@[1]` obligation on the old owner is transferred to the
  returned owner. Binding the result to an ungraded local does not launder the
  obligation.
- Moving the owner while an immutable borrow or slice view is live is rejected
  by the existing ownership and view checks.

All boxes use word-granular inline layouts in this subset, so a width test is
sufficient and no alignment change can make a non-wider payload invalid. This
is deliberately conservative: reuse never attempts an allocator-level
shrink/grow or a fallible reserve.

Early exits are safe. If a later argument executes `?`, `return`, or another
diverging path before the reuse completes, the pending owner is still tracked
and is destroyed exactly once by normal cleanup. The reference evaluator and
native backend both evaluate the arguments before dropping the old payload.

## Allocation-preserving vector transforms

```rust
fn inc(x: i64) -> i64 ! {panic} { x + 1 }

let values: Vec<i64> = /* owning vector */;
let values = Vec.map_in_place(values, inc);
```

`Vec.map_in_place(values, f)` consumes the vector, applies `f` to every element
in order, and returns the same vector allocation with the transformed elements.
It acquires no heap storage. The callable is a first-class value:

- It must be a copyable, noncapturing `fn(T) -> U ! {e}`. `once fn` and
  `linear once fn` callbacks are rejected, because the transform may invoke the
  callable once per element and cannot duplicate an owning callable.
- The callback's effect row is required by the enclosing function. An
  allocating callback therefore makes `map_in_place` require `alloc`, and a
  `#[noalloc]` function rejects it. The contract is checked from the source
  types and effects, never inferred from whether a later optimization fires.
- Parameter grades remain part of the callback signature. For example a
  `fn(i64 @[2])` callback still promises to observe each copyable element twice.
  Linear elements remain rejected by the existing `Vec` model.
- The callback's parameter must accept the source element with the same runtime
  layout, and its result must have the same layout as the requested result
  element. A representation-changing coercion is rejected inside this operation.
- The result element layout must be no wider than the source element layout:
  `width(U) <= width(T)`. Native execution compacts elements to the new stride
  in place and updates the vector header, so later `Vec.get`, `Vec.at`, slices,
  push, and destruction all observe the compacted layout. Reference execution
  models elements directly and performs the same logical transformation.
- Owning affine elements are moved into the callback and are not copied as
  owners. A callback that returns a new owner stores that owner in the same
  slot; a callback that consumes the element (for example returning a scalar
  through `Box.take`) releases it exactly once. Generated vector destruction
  uses only the final element layout.
- Moving an aliased vector or a vector with a live slice view is rejected.
- An empty vector still evaluates its callback expression, then performs zero
  element calls. A `?` in the callback expression itself returns early and
  cleans the pending vector owner.

Changing the element type requires a binding with the new expected type:

```rust
let narrow: Vec<i64> = Vec.map_in_place(wide, project_first);
```

An assignment target with the old `Vec<T>` type intentionally fixes the result
layout to `T`; it cannot silently change an existing binding's type.

## Nested pure-map fusion

A nested `Vec.map_in_place(Vec.map_in_place(values, f), g)` can be fused into a
single traversal. Fusion is deliberately conservative:

- both callbacks must be noncapturing `fn` values with the **empty** effect row;
- the nested maps must agree on the intermediate element layout;
- the usual non-increasing width checks must hold for every step.

Empty-effect callbacks cannot perform I/O, allocate, or panic, so applying
`g` after each `f` does not reorder observable effects relative to running all
of `f` and then all of `g`. A callback with `io`, `alloc`, or `panic` disables
fusion and preserves the original call order. The compiler reports the number of
selected fusions in diagnostics; this is an observation about generated code,
not a source-language effect or a proof fact.

Fusion does not change the number of allocations in this vector model; it
reduces traversal passes. No claim is made about speed without measurement.

## Allocation diagnostics

Use the optional `--stats` flag:

```sh
cargo run -p kush -- eval examples/reuse.kush --stats
cargo run -p kush -- run examples/reuse.kush --stats
cargo run -p kush -- build examples/reuse.kush -o target/reuse --stats
```

The program's own stdout and exit status are unchanged. Diagnostics are written
to stderr as exactly one line with this stable format:

```text
allocation-stats: allocations=<n> deallocations=<n> peak-live=<n> buffer-growths=<n> reuses=<n> fusions=<n>
```

- `allocations` counts successful allocation events: boxes, byte buffers,
  vector allocations, closure environments, and byte literals.
- `deallocations` counts completed frees of those allocations. A normal exit
  still requires all owning allocations to have been released.
- `peak-live` is the maximum number of live allocations observed.
- `buffer-growths` counts successful capacity growth operations for byte buffers
  and vectors. Reallocation replaces storage and is not counted as an
  allocation/free pair.
- `reuses` counts successful checked `Box.reuse` operations.
- `fusions` is the compiler-selected nested pure-map count.

For the reference evaluator the same counters are available through
`Executable::evaluate_with_stats`. Native diagnostics are emitted by the
generated runtime at normal exit; the existing live-allocation check remains.
A program that aborts, traps, or diverges may not print the line.

These counters are tooling observations about one execution. They are not
language effects, resource contracts, or proof evidence, and they do not make
`noalloc` depend on an optimization succeeding. The Rust host allocations used
by the compiler and reference interpreter are separate from the generated
program's allocation model.

## Measured demonstration

The example workload is a literal before/after comparison, not a synthetic
benchmark claim:

- Updating one box 100 times with `Box.reuse` reports
  `allocations=1 ... reuses=100`.
- Replacing each update with `Box.new` in the same loop reports
  `allocations=101` (one initial box plus 100 replacements).
- Mapping four vector elements in place reports the same single vector
  allocation with no additional allocation events.

These counts come from the reference and native implementations agreeing on
the stable diagnostics line in the test suite. No payload-byte totals or speed
superiority are claimed.

## Explicit boundaries

The completion work extends this milestone with widening reuse, fallible
allocation, the built-in `Arena` strategy, and a narrower automatic-fusion
analysis; see [memory-completion.md](memory-completion.md). Still not
implemented or guaranteed here:

- arbitrary user-defined allocator callbacks or an FFI allocator interface
  (the native runtime has a [bounded small-block pool](allocator-pool.md) and
  the source-level `Arena` strategy; neither is a pluggable user allocator);
- widening a vector element in place (widening a **box** payload is available
  through the explicit `Box.reuse_grow` contract);
- general compiler fusion of arbitrary expressions, effectful callbacks with
  I/O/panic/suspend, or callable arguments with observable evaluation;
- in-place transformation of borrowed, shared, or aliased storage;
- reassociation or vectorization, LLVM, forced cancellation unwinding, or
  nonblocking task I/O;
- payload byte accounting and performance superiority claims.

General functional updates may still allocate. A guaranteed in-place operation
must use one of these explicit APIs and satisfy their preconditions; there is no
hidden allocating fallback under `#[noalloc]`.

## Additional memory operations

See [vector reuse](vector-reuse.md) for `Vec.clear`, `Vec.reserve`, and explicit
interleaved effectful map chains, and [allocator pooling](allocator-pool.md)
for bounded physical small-block reuse. Automatic fusion still requires pure
callbacks; an explicit chain defines its own interleaved effect order.
