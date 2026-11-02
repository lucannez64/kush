# Full five-area completion backlog

Baseline: `10d9588`, implementation `29674d2`, 681 tests/fmt/Clippy passed on
Boat and independent review reported no blocking findings. The user requested
completion of the five areas below, rather than another milestone described as
complete while features remain. Every unchecked item is still outstanding.
Implementation and review must establish each item's precise supported contract;
changing a diagnostic or deleting an explicit rejection is not completion.

## Borrowing

Integrated on `main` in `401662d` and `342537d`; see
[expanded borrowing contracts](borrowing-extensions.md) for the exact contract
and remaining limits.

- [ ] General shared/exclusive reference support, including escape and reborrow
  contracts. **Partial:** reference parameters may be returned and reborrowed
  through calls; stored shared/exclusive reference locals, implicit use
  reborrow, explicit `&*p`/`&mut *p`, and shared `&Box`/`&Vec`/`&Bytes`/`&String`
  escape contracts are checked. Reference fields, reference element containers,
  and reference-valued arrow parameters/results remain rejected.
- [ ] Broader sound lifetime inference. **Partial:** function/arrow/lambda
  results can be inferred from a single record-field source and ambiguous
  origins are rejected. Elided function results with several input lifetimes
  now use a conservative body-origin seed: a direct parameter name, field,
  slice, or one branch of a block/`if`/`match` value selects that parameter's
  lifetime, while several return-position lifetimes remain rejected. Inferred
  outlives bounds, helper-call body inference, per-field inference from a
  multi-lifetime record, and general unification are still absent.
- [x] Capturing lambdas returning borrowed slices with represented provenance.
  The capture index and field path travel in the callable contract and the
  result is resolved against the capture's outer provenance.
- [x] Borrowed records in callable parameters/results/captures. Arrows carry
  per-field leaves, indirect calls freshen record lifetimes, and scoped
  closures may capture and return record fields.
- [ ] Borrowed records in structured tasks with checked scope ownership.
  **Partial:** scope bodies and child tasks may capture records from
  scope-external storage; scope-owned storage is rejected. A child task may
  return a borrowed record, and `Task.join` transfers per-field provenance
  through the conventional `TaskExit<T>` so field loans remain checked until
  the matched value is consumed or dropped. Cancelled completed results drop
  owned metadata without freeing borrowed storage. Borrowed `Task.scope`
  results and borrowed `TaskExit<T>` values across function/callable
  boundaries remain rejected.
- [x] Nested record-field borrows and disjoint-field loans. Direct nested
  subviews and structurally disjoint mutable field subviews are checked; whole
  record moves stay blocked and merged records lose field identity.

## Traits

- [x] Associated types and constants with checked projection/substitution.
  Scalar compile-time constants, required/default values, `Self` and bounded
  `T` projections, per-impl substitution, and missing/extra/type mismatch
  diagnostics are implemented and tested.
- [x] Generic and blanket implementations with coherent overlap rules. Type
  patterns, parameter solving, bound discharge, unconstrained-parameter
  rejection, duplicate detection, and per-instantiation method checking are
  implemented and tested.
- [ ] Trait objects and checked dynamic dispatch/object safety. **Partial:** Closed-world
  union representation, owned and copyable shared receivers, object-argument
  dispatch, owning cleanup, associated-item agreement, and explicit rejection
  of open sets, mutable/generic/borrowing-ownership cases are implemented and
  tested. Stored `&dyn Trait`/`&mut dyn Trait` values remain outside the
  subset.
- [x] Specialization with an explicit deterministic coherence contract. Unique
  most-specific resolution, concrete-over-generic preference, duplicate
  rejection, and incomparable-overlap rejection are implemented and tested.
  `default fn`, negative impls, and arbitrary overlap remain rejected.

Open trait work still includes mutable dynamic dispatch and stored borrowed
trait objects, open/generic object member sets, const/grade/effect/lifetime impl
parameters, associated type defaults, and non-scalar associated constants. The
implemented closed-world union dispatch is not a claim of general vtable-based
trait-object support. See [trait contracts](traits.md).

## Grades and linear resources

- [x] General grade inference beyond bare result-only expected-arrow inference.
  Implemented as a single-occurrence affine solver over `+`/`*` for direct calls
  with explicitly graded arguments and for expected arrows; unsolvable or
  ambiguous equations stay explicit. See `docs/grade-inference.md`.
- [x] User-defined grade algebras with validated laws and decidable checking
  boundaries. Explicit finite carriers and total `add`/`mul` tables are checked
  by exhaustive enumeration (closure, identities, associativity, commutativity,
  distributivity, annihilation). See `docs/grade-algebras.md`.
- [x] Copyable exact-use result transfer across every control-flow/discard
  position. A copyable `@[1]` result is a must-use observation, never an owning
  move; `let`, assignment, return, blocks, branches, match arms, loops, `?`,
  captures, aggregates, and every tested discard position are checked. See
  `docs/copyable-result-transfer.md`.
- [ ] Grade-zero runtime erasure with relevance/effect guarantees. **Partial:** local
  `@[0]` bindings are not materialized in either backend; initializer effects,
  order, and allocation balance are preserved. Parameter slots remain ABI-bound
  but unobservable, and result `@[0]` is still rejected. See
  `docs/grade-zero-erasure.md`. Parameter/result erasure is still outstanding.
- [x] Cancellation cleanup of linear resources and linear task results.
  Cooperative cancellation transfers a completed owning/linear payload as
  `Completed` instead of dropping it; such task handles are linear and must be
  joined explicitly. Copyable must-use task results and forced cancellation
  unwinding remain out of scope. See `docs/linear-task-results.md`.

Finite-algebra compiler metadata now has explicit compilation/executable
owners and weak lookup entries. Program-drop tests verify table reclamation;
this fix still needs the integrated test/review gate.

## Advanced types and effects

- [ ] Structural record subtyping and representation-changing coercions.
  **Partial:** anonymous `struct { ... }` rows, canonical field order,
  width subtyping, checked field-copy coercions, affine-field cleanup, linear
  field erasure rejection, and borrowed-leaf/mutability invariance are
  implemented in both backends. Nested field representation changes, open rows,
  structural record literals, generic structural patterns, and structural
  records in impl headers are explicitly rejected. See
  [subtyping.md](subtyping.md#structural-records).
- [ ] Broader algebraic subtype inference with documented decidability
  boundaries. **Partial:** contextual array/vector/tuple literals and
  first-order generic matching now accumulate constraints over every finite
  union alternative instead of choosing the first matching arm. Conflicting or
  incomparable bindings are explicit. General principal inference, indexed
  unions, and multi-variable backtracking remain out of scope. See
  [subtyping.md](subtyping.md#contextual-and-algebraic-inference).
- [ ] Effect handlers and checked resumption ownership. **Partial:** lexical
  one-shot tail-resumptive `handle`/`perform`, nested shadowing, first-class
  handler callables, a linear identity resumption token, handler-effect
  propagation, and owning payload/cleanup checks work in both backends.
  Captured continuations, non-tail resumption, multishot handlers, dynamic
  handler stacks across calls, and user-defined effect rows are not
  implemented; `perform` inside a lambda is rejected. See
  [effect-handlers.md](effect-handlers.md).
- [ ] General row constraints beyond concrete exclusions. **Partial:** a finite
  constraint solver accumulates inclusion constraints across every higher-order
  argument, supports up to three unbound row variables (4096 assignments),
  unions evidence from repeated row variables, applies exclusion bounds, and
  rejects ambiguous/nonminimal groups. There are no lower bounds, row
  subtraction, recursive row unification, or open-row principal inference. See
  [effect-constraints.md](effect-constraints.md#accumulated-row-constraints).
- [ ] Broader runtime-dependent proofs with mutation/version tracking.
  **Partial:** mutable scalar locals index erased proofs at their current
  version; assignment appends a fresh versioned binder, an old literal proof is
  rejected against the new value, and a closure capture is an independent
  frozen snapshot. Proof-valued runtime locals, mutable captures as a live
  view, and arithmetic proof search remain absent. See
  [runtime-indices.md](runtime-indices.md#4-freezing-and-mutation).
- [ ] Runtime-sized inline arrays with checked lifetime/storage layout.
  **Partial:** `DynArray<T, capacity>` has compile-time capacity, runtime
  length, inline storage, checked push overflow, checked reads, owning-prefix
  drop, and native/reference agreement. There is no `pop`/`set`, literal,
  pattern, view, or runtime `[T; n]`; capacity remains a compile-time bound.
  See [dynamic-arrays.md](dynamic-arrays.md).

## Memory and optimization

- [x] Automatic fusion where effect/order/termination analysis proves
  equivalence. **Implemented** in `docs/memory-completion.md`: a post-check
  analysis merges only noncapturing callbacks whose effect row is empty or
  `alloc`-only and whose checked bodies are structurally total (no loops,
  recursion, indirect calls, task operations, I/O, or panic). Effectful
  drop-order is guarded by a non-owning intermediate requirement. At most one
  allocating callback stage may merge; the other stages must be inert and
  non-owning so fallible allocation order is preserved. Arbitrary
  effectful interleaving remains rejected; the explicit chain chooses that
  order at source level.
- [ ] Widening reuse with explicit allocation/capacity guarantees. **Partial:**
  **Implemented for box payloads:** `Box.reuse_grow` checks the old owner and
  payload obligations, destroys the old payload once, and either keeps the
  allocation or grows/moves it under an explicit `{alloc, panic}` contract.
  `#[noalloc]` rejects it; `Box.reuse` keeps its no-allocating-fallback
  contract. Widening a vector element in place remains explicitly unsupported.
- [ ] Custom allocators and lifetime-safe allocator ownership. **Partial, with
  a documented built-in allocator strategy:** `Arena`/`ArenaBox` with
  reference-retained regions, deterministic drop, function/task escape, and
  checked provenance. Arbitrary user-defined allocator callbacks and FFI are
  deliberately not implemented and are not claimed.
- [ ] Fallible allocation/reuse with exact cleanup on all failure paths. **Partial:**
  **Implemented:** `Box.try_new`, growth-capable `Box.try_reuse`, and
  `Bytes.try_with_capacity` return the conventional checked `Result`; failures
  preserve the old owner and, for `try_new`, the supplied payload. Real native
  malloc refusal and a reference allocation budget are both exercised; no
  process abort is disguised as `Err`. Fallible arena allocation and
  `Vec.try_reserve` remain outstanding.
- [x] Reproducible performance and physical-memory benchmarks.
  **Implemented:** `scripts/memory-bench.py` measures allocation counters,
  reference/native parity, wall time, maximum RSS, and native pool retention
  for deterministic workloads. It reports measurements, not superiority.

Arbitrary effectful callback interleaving is not semantics-preserving: callback
output, panic, and scheduling order can differ. Existing explicit map chains
select that order deliberately. Automatic fusion proves the documented
trace-free/total equivalence rather than silently changing the language's
evaluation semantics; the unresolved general cases are listed in
[memory-completion.md](memory-completion.md#unresolved-generality).

## Advanced types and effects validation

The six advanced items are implemented as the restricted fragments above, not
as the complete v0.1 dependent/algebraic/effect calculus. Local evidence:

```sh
CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/types-effects \
  CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 \
  cargo test -p kush --offline -j 6
cargo fmt --all -- --check
cargo clippy -p kush --all-targets --offline
```

The full workspace test run for this branch passed 778 tests across 58 test
binaries, with formatting and Clippy clean. The new
`crates/kush/tests/advanced_types_effects.rs` covers positive execution,
rejection diagnostics, native/reference agreement, and owning cleanup for all
six items. Existing exact-grade, trait, borrowing, async, runtime-index, and
subtyping suites still pass unchanged except for the deliberate
mutable-index/frozen-capture relaxations documented in
[runtime-indices.md](runtime-indices.md).

Baseline note: commit `3e478cf` did not compile in this checkout because a
stale `result_linear` field was present in a `Function` literal at
`crates/kush/src/executable.rs:8361`; that unrelated field was removed to
restore compilation before this area's work.

## Completion evidence

Each item needs positive and rejection tests, native/reference agreement where
applicable, exact cleanup checks for owning values, documentation of semantics,
and integration checks. Code must be committed and independently reviewed.
This list is not a promise that all requirements have a general decidable or
single-day implementation; unresolved design conflicts remain visible here.
