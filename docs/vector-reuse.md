# Explicit vector reuse: clear, reserve, and interleaved chains

Status: implemented in the reference evaluator and the Cranelift backend for
the checked executable value subset. These operations are explicit source-level
contracts. They are not a general optimizer, an allocator, or a claim that a
program becomes faster.

```rust
let values: Vec<i64> = /* owning vector */;
let values = Vec.clear(values);
let values = Vec.reserve(values, 8);
let values = Vec.map_chain_in_place(values, first, second);
```

The existing allocation diagnostics format is unchanged:

```text
allocation-stats: allocations=<n> deallocations=<n> peak-live=<n> buffer-growths=<n> reuses=<n> fusions=<n>
```

The rules below extend [reuse.md](reuse.md); they do not replace the checked
box reuse or `Vec.map_in_place` contracts described there.

`Vec.clear` and `Vec.reserve` also accept the receiver-method spelling
(`values.clear()`, `values.reserve(8)`), which is the same checked operation
with the receiver evaluated once. `Vec.map_chain_in_place` is namespace-only,
like `Vec.map_in_place`.

## `Vec.clear`: keep the allocation, release the elements

`Vec.clear(values)` consumes an owned `Vec<T>` and returns the **same vector
allocation** with length zero:

- Element slots are destroyed in reverse order (`len - 1` down to `0`), exactly
  once. Owning elements are therefore released without copying them.
- The allocated capacity is retained. A later `Vec.push` reuses the existing
  storage until that capacity is exhausted.
- The vector allocation itself is not freed and no new allocation occurs.
  Clearing does not change the allocation/deallocation counters for the vector.
  Destroying owning elements increments their own deallocation counts normally.
- `Vec.clear` has the empty effect row. It is legal under `#[noalloc]` when the
  receiver expression itself does not allocate. Element destruction is not an
  `alloc`, `io`, `panic`, or `suspend` event.
- An empty vector is still evaluated and returned; it has no elements to drop.
- The receiver must be an owned vector. Moving a vector that is aliased or has a
  live slice view is rejected by the existing ownership and borrow checks.
- Vectors cannot contain linear values, task handles, references, or slice
  views, so clearing cannot hide a linear obligation or emit a dangling view.

Reference and native execution agree on values, output, failure, and the
diagnostics line. Native free order follows the same reverse traversal; the
reference evaluator uses its ordinary reverse element drop.

## `Vec.reserve`: checked room for more elements

`Vec.reserve(values, additional)` consumes an owned `Vec<T>` and returns the
same vector allocation after ensuring:

```text
capacity >= length + additional
```

- `additional` is an `i64` and must be non-negative. A negative value panics.
- The addition is checked. A request that would overflow the supported capacity
  panics instead of wrapping.
- If the current capacity already suffices (`length + additional <= capacity`),
  nothing happens: no reallocation and no buffer-growth count.
- If room is needed, storage grows **at most once**, to exactly
  `length + additional`. There is no speculative over-allocation beyond the
  requested size, so later growth behavior is predictable.
- A successful growth increments `buffer-growths` by one. Reallocation replaces
  storage and is not an allocation/deallocation pair; `allocations` and
  `deallocations` do not change.
- `Vec.reserve` requires the `{alloc, panic}` effects. A `#[noalloc]` function
  rejects it from the source signature, independently of whether a particular
  call would actually reallocate.
- The receiver is consumed and returned, so the same ownership and borrow rules
  as `Vec.push` and `Vec.clear` apply: it must be an owned, unaliased vector
  without a live slice view.

The reference evaluator enforces its normal 1Mi-element capacity budget, so a
request beyond that modeled limit fails there. The native runtime rejects
requests that its capacity byte check cannot represent. Neither path wraps or
silently truncates; the reference and native parity tests use sizes inside the
reference budget so their growth counts stay directly comparable. Capacity is
deliberately not exposed as a source-level query in this milestone; growth
behavior is observed through subsequent pushes and the stable `buffer-growths`
counter.

## `Vec.try_reserve`: return the original vector on refusal

`Vec.try_reserve(values, additional)` (also `values.try_reserve(additional)`)
consumes `Vec<T>` and returns the conventional `Result<Vec<T>, Vec<T>>`.
`Ok(values)` has room for `len + additional`; `Err(values)` preserves the
original elements, length, capacity, and allocation. Neither branch drops or
copies an owning element. Negative requests, size overflow, and allocator
refusal return `Err`, without an implicit panic or a buffer-growth increment.

Both arguments are evaluated once, left to right. Argument effects and early
returns retain normal cleanup. The operation requires `{alloc}` even when a
particular call fits, and is rejected under `#[noalloc]`. A live borrow still
prevents moving the receiver. A linear owner obligation transfers through the
result; `clear`, `reserve`, and `try_reserve` cannot erase it.

A successful logical capacity increase increments `buffer-growths` once. If
the retained physical allocation already covers the request, no allocator
attempt occurs, even if logical capacity increases. This includes small-block
rounding and storage retained after map narrowing. Otherwise fallible growth
uses exact-sized storage and preserves the old allocation on refusal. Logical
allocation/deallocation counters stay unchanged in either branch.

The reference evaluator models retained physical bytes as well as logical
capacity, so deterministic allocation-budget tests agree with native
`KUSH_ALLOC_FAIL_AFTER` probes. Its existing 1Mi-element vector budget remains:
requests above that limit return `Err` in reference execution, while native
execution may succeed if the real allocator permits them.

## `Vec.map_chain_in_place`: explicit interleaved transforms

`Vec.map_chain_in_place(values, f, g)` consumes an owned `Vec<T>` and applies
both callbacks to every element. The order is fixed and explicit:

```text
f(e0), g(e0), f(e1), g(e1), f(e2), g(e2), ...
```

This is **not** "run all of `f`, then all of `g`" and it is **not** an automatic
semantics-preserving fusion of effectful maps. The operation itself chooses the
interleaved order; a separate nested `map_in_place` calls keep their original
pass-by-pass order unless the existing pure-map fusion rules explicitly apply.

### Callback contract

Each callback is a reusable, noncapturing `fn(S) -> S'` value:

- `f` must take the source element type `T` with the same runtime layout and
  return the intermediate type `M`.
- `g` must take exactly `M` with the same runtime layout and return the final
  element type `U`.
- `?`, `return`, `break`, and other early exits keep their normal cleanup
  behavior. A failing callback expression or a diverging callback still cleans
  pending owners exactly once.
- Both callback expressions are evaluated once, left to right, **before** the
  element loop starts. This includes the empty-vector case: the vector and both
  callback values are evaluated, then zero elements are visited.
- The callbacks' effects are required independently by the enclosing function.
  The effective requirement is the union of both effect rows. An allocating or
  I/O-performing callback is visible to `#[noalloc]` and effect checking even
  when the vector is empty.
- `once fn` and `linear once fn` callbacks are rejected: the operation may call
  each callback once per element, so an owning callable cannot be duplicated
  or reused. Capturing lambdas are `once fn` values and are therefore rejected
  as well.
- A callback parameter grade is part of its contract and is preserved.

### Layout and payload rules

- The source and each callback result must be concrete runtime values.
  References, `&mut` references, slice/text views, and `Never` are rejected as
  element payloads.
- Linear element types are rejected, as they are for every `Vec` operation.
  Task handles cannot be stored in a vector; functions that return task handles
  are already rejected by the task scope rules.
- Intermediate SSA layouts may be **wider** than the source element layout.
  They exist only as transient values between `f` and `g`, are never stored in
  the vector, and do not change the allocation's element stride. This is safe
  in both backends.
- The **final** element layout must be no wider than the source layout:
  `width(U) <= width(T)`. Native execution compacts elements to the final
  stride in place and updates the vector header; reference execution models the
  values directly. A widening result is rejected with a request to build a new
  vector instead.
- The final layout must equal the callback result layout. An explicit result
  element type therefore cannot request a representation-changing coercion; it
  can only confirm the callback's layout.
- Owning affine intermediates are allowed. They move into `g` and are not
  copied as owners. A callback that returns an owner stores it in the same
  slot; a callback that consumes it releases it exactly once.

The final element type can be selected with one explicit type argument or by
the binding's expected `Vec<U>` type:

```rust
let narrowed: Vec<i64> = Vec.map_chain_in_place(values, widen, project);
```

### Fusion boundaries

`map_chain_in_place` never flattens a nested map or chain automatically. Two
explicit chains perform two sequential passes. This keeps the operation's
observable order obvious and avoids silently reordering effectful callbacks.

The existing automatic pure-map fusion remains unchanged and still requires
**every** callback in the merged nest to be a noncapturing `fn` value with the
empty effect row. A `map_in_place` whose receiver is a `map_chain_in_place` may
therefore be merged only when all callbacks are empty-effect and the
intermediate layout already agrees. That is the pre-existing conservative rule;
it does not make effectful callbacks fusion candidates.

`fusions` counts only compiler-selected nested pure-map merges. An explicit
`map_chain_in_place` does not increment it, because its interleaving is a
source-level choice rather than an optimization observation.

### Review: do owning intermediates need an extra fusion guard?

No extra guard was added in this milestone, and the existing fusion condition
was left unchanged:

- Automatic fusion already requires the empty effect row for every callback.
  A callback that allocates, performs I/O, or can panic cannot satisfy that
  condition.
- A pure callback can still carry or reuse an owning affine value, for example
  `Box.take` or an effect-free `Box.reuse` wrapper. Separate passes and
  interleaved fusion both move that owner into the next callback and release it
  exactly once. The intermediate slot is only transient SSA storage; no vector
  storage is removed or duplicated.
- Every intermediate layout in the existing fusion path already satisfies the
  non-increasing width rule of its own map, so fusing does not widen the
  preserved allocation.
- Making the guard stricter would reject safe empty-effect code without fixing
  an observable ordering or ownership difference. No regression justified it.
  The regression suite checks both sides: a fused nest with an owning
  intermediate stays balanced, while an allocating intermediate keeps two
  separate passes and reports zero fusions.

## Allocation diagnostics for these operations

The stable line and field meanings are unchanged:

- `allocations` does not grow for `clear`, `reserve`, or `map_chain_in_place`.
  Reserve reallocates; it does not allocate a new vector. A chain reuses the
  existing vector and callback values.
- `deallocations` grows when `Vec.clear` destroys owning elements, and for the
  final vector drop, exactly as with any other owning value. Balanced cleanup
  must still hold at normal exit.
- `peak-live` is unaffected by clear/reserve bookkeeping. It still tracks live
  owning allocations, including boxes held by vector elements.
- `buffer-growths` grows by exactly one for a reserve that must grow, and by
  zero when the retained capacity already suffices. Clear never grows storage.
- `reuses` and `fusions` are unchanged by these operations. `Vec.reserve` is not
  a `Box.reuse`; `map_chain_in_place` is not a compiler fusion.

These counters remain tooling observations about one execution, not language
effects, resource contracts, or proof evidence. `noalloc` is checked from the
source effect rows, never from whether reserve happened to avoid a reallocation.

## Explicit boundaries

The memory-completion work adds a built-in `Arena` strategy, fallible box/byte
allocation, and `Box.reuse_grow`; see
[memory-completion.md](memory-completion.md). Not implemented or guaranteed by
this milestone:

- a pluggable user-defined allocator or allocator callbacks (the `Arena`
  strategy and the native [pool](allocator-pool.md) are built in);
- fallible `Vec.reserve` specifically (fallible `Box.try_new`,
  `Box.try_reuse`, and `Bytes.try_with_capacity` are available);
- widening a vector element in place, including widening the final chain
  result;
- automatic flattening or general fusion of effectful maps and chains;
- changing the evaluation order of existing callbacks or `map_in_place`;
- in-place transformation of borrowed, shared, or aliased storage;
- reallocation-free guarantees for unrelated vectors, payload byte accounting,
  or performance superiority claims;
- `Vec.pop`, removal in the middle, or arbitrary index movement.

`Vec.clear` and `Vec.reserve` keep the vector's single allocation. A chain keeps
that allocation and only transiently widens SSA values. Any operation that
needs a wider final element or a different allocation must build a new vector.

## Allocator-level follow-up

The bounded native pool is now implemented in [allocator-pool.md](allocator-pool.md),
and the source-level `Arena` strategy plus fallible allocation are described in
[memory-completion.md](memory-completion.md). Neither relaxes the rules above:
the stable diagnostics format, balanced deallocation counts, non-increasing
element width, reverse element destruction, checked negative/overflow reserve,
and reference/native parity remain required.
