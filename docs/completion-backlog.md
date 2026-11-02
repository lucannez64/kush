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
  contracts. **Partial:** reference parameters may be returned and reborrowed through calls;
  stored shared/exclusive reference locals, implicit use reborrow, explicit
  `&*p`/`&mut *p`, shared `&Box`/`&Vec`/`&Bytes`/`&String` escape contracts, and
  direct reference fields in nominal records are checked. `Box<&T>` and
  `Vec<&T>` element containers carry explicit type-level lifetime annotations
  and preserve owner loans through construction, reads, calls, records, and
  arrows. Reference-valued arrow parameters/results are checked for direct and
  indirect calls, including lambda parameters and single-parameter reference
  results. Mutable owner borrows (`&mut Box`/`&mut Vec`/`&mut Bytes`/`&mut
  String`), `&str` fields/containers, and reading a reference field through
  `&Record` remain deliberate exclusions. See
  [borrowing-extensions.md](borrowing-extensions.md).
- [ ] Broader sound lifetime inference. **Partial:** function/arrow/lambda
  results can be inferred from a single record-field source or a per-field body
  origin. A multi-lifetime record now supports per-field selection, including
  nested field paths; several returned lifetimes remain explicitly ambiguous.
  Inferred outlives bounds, helper-call body inference, and general unification
  are still absent.
- [x] Capturing lambdas returning borrowed slices with represented provenance.
  The capture index and field path travel in the callable contract and the
  result is resolved against the capture's outer provenance.
- [x] Borrowed records in callable parameters/results/captures. Arrows carry
  per-field leaves, indirect calls freshen record lifetimes, and scoped
  closures may capture and return record fields.
- [x] Borrowed records in structured tasks with checked scope ownership.
  Scope bodies and child tasks may capture records from scope-external storage;
  scope-owned storage is rejected. A child task may return a borrowed record,
  and `Task.join` transfers per-field provenance through the conventional
  `TaskExit<T>` so field loans remain checked until the matched value is
  consumed or dropped. `Task.scope` may return a borrowed record, and a
  borrowed `TaskExit<T>` may cross a function or callable boundary when its
  payload lifetimes are supplied by the caller. Cancelled completed results
  drop owned metadata without freeing borrowed storage. A child task still
  cannot return a borrowed `TaskExit<T>`, and a lambda/task environment cannot
  hide one.
- [x] Nested record-field borrows and disjoint-field loans. Direct nested
  subviews and structurally disjoint mutable field subviews are checked; whole
  record moves stay blocked and merged records lose field identity.

## Traits

- [x] Associated types and constants with checked projection/substitution.
  Scalar compile-time constants, required/default values, associated type
  defaults with trait-argument substitution, chained `Self::Other` projections,
  cycle/unknown/bare-`Self` rejection, object-member agreement, `Self` and
  bounded `T` projections, per-impl substitution, and missing/extra/type
  mismatch diagnostics are implemented and tested. Associated constants may
  also be finite tuples or inline arrays of compile-time constants, including
  aggregate defaults and aliases; owning/`String` constants and constants that
  depend on an impl type parameter remain outside the subset.
- [x] Generic and blanket implementations with coherent overlap rules. Type,
  natural (`Nat`), and grade impl-header parameters; array-length and trait
  argument solving; bound discharge; unconstrained-parameter rejection;
  duplicate detection; and per-instantiation method checking are implemented
  and tested. Effect parameters have no determining position in an impl header
  and are rejected as unconstrained; lifetime parameters remain rejected by the
  parser.
- [ ] Trait objects and checked dynamic dispatch/object safety. **Partial:**
  Closed-world union representation, owned, copyable shared, and mutable
  receivers with write-back to a direct object local, temporary mutable
  receivers, stored copyable `&dyn Trait`/`&mut dyn Trait` values with
  reference write-back, object-argument dispatch, owning cleanup, associated
  item/default agreement, and explicit rejection of open sets,
  non-copyable borrowed objects, owning-through-borrowed calls,
  mutable-through-shared calls, generic methods, and nominal fields mentioning
  `dyn` (directly or through `Box`/`Vec`/tuples) are implemented and tested.
  Open/generic member sets and borrowed objects with owning/linear members
  remain outside the subset.
- [x] Specialization with an explicit deterministic coherence contract. Unique
  most-specific resolution, concrete-over-generic preference, duplicate
  rejection, and incomparable-overlap rejection are implemented and tested.
  `default fn`, negative impls, and arbitrary overlap remain rejected.

Open trait work still includes open/generic object member sets, `dyn Trait`
anywhere inside a nominal field, borrowed objects with owning/linear members,
object methods with lifetime or exact-use contracts, owning or `String`
associated constants, associated constants depending on an impl type
parameter, and lifetime/effect impl parameters. The implemented closed-world union dispatch is
not a claim of general vtable-based trait-object support. See
[trait contracts](traits.md).

## Grades and linear resources

- [x] General grade inference beyond bare result-only expected-arrow inference.
  **Implemented subset:** simultaneous equations over natural `+`/`*` grades and
  declared finite algebras, including repeated/nonlinear natural occurrences
  with a proven target bound, multi-binder substitution, conflict detection,
  and unique-solution enumeration. Ambiguous, over-budget, underlying-type, and
  arbitrary multivariate Diophantine cases stay explicit; this is not a
  principal solver. See `docs/grade-inference.md`.
- [x] User-defined grade algebras with validated laws and decidable checking
  boundaries. Explicit finite carriers and total `add`/`mul` tables are checked
  by exhaustive enumeration (closure, identities, associativity, commutativity,
  distributivity, annihilation). Finite-algebra grade inference enumerates the
  carrier for a unique solution; idempotent-one observation semantics and the
  rejection of identical zero/one are explicit. See `docs/grade-algebras.md`.
- [x] Copyable exact-use result transfer across every control-flow/discard
  position. A copyable `@[1]` result is a must-use observation, never an owning
  move; `let`, assignment, return, blocks, branches, match arms, loops, `?`,
  captures, aggregates, every tested discard position, and copyable task
  results are checked. See `docs/copyable-result-transfer.md` and
  `docs/linear-task-results.md`.
- [x] Grade-zero runtime erasure with relevance/effect guarantees. Implemented
  for local bindings, parameters, results, function values, checked adapters,
  closures, static/default/dynamic trait dispatch, and both backends.
  Initializer/argument effects, source order, allocation balance, and actual
  eager cleanup are preserved. Erased parameters/results have no ABI slot or
  return payload; subtyping across differing physical arities synthesizes
  checked adapters instead of casting function pointers. Affine-owned zero
  bindings eagerly initialize and drop; owning/linear parameters and results
  stay rejected, as do vector-map callbacks that would erase observed elements.
  See `docs/grade-zero-erasure.md`.
- [x] Cancellation cleanup of linear resources and linear task results.
  Cooperative cancellation transfers a completed owning/linear/copyable
  must-use payload as `Completed` instead of dropping it; such task handles are
  linear and must be joined explicitly, and a copyable joined exit remains
  must-use. Forced cancellation unwinding remains out of scope. See
  `docs/linear-task-results.md`.

Finite-algebra compiler metadata has explicit compilation/executable owners and
weak lookup entries. Program-drop tests verify table reclamation; the integrated
test/review gate for this change is tracked by the parent integration, not by an
outstanding implementation item.

## Advanced types and effects

- [ ] Structural record subtyping and representation-changing coercions.
  **Partial:** anonymous `struct { ... }` rows, canonical field order,
  width/order subtyping, recursive nested structural field conversions,
  atom-to-union field injection, affine-field cleanup, linear field erasure
  rejection, and borrowed-leaf/mutability invariance are implemented in both
  backends. Nested union repacking, callable field adaptation, open rows,
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
  `Bytes.try_with_capacity`, and `Vec.try_reserve` return the conventional
  checked `Result`; failures
  preserve the old owner and, for `try_new`, the supplied payload. Real native
  malloc refusal and a reference allocation budget are both exercised; no
  process abort is disguised as `Err`. Vector refusal retains every element,
  length, capacity, and owner obligation; physical-capacity and failure-budget
  parity are tested. Fallible arena allocation remains outstanding.
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

## Combined integration checkpoint

At `20e9a0d`, the borrowing/trait/grade changes, advanced types/effects, and
memory changes are integrated on `main`. Local Linux x86-64 validation used
`target/main-integration` with debug information disabled and six Cargo jobs:

- Full locked workspace suite: **832 passed, 0 failed**.
- All-targets Clippy with warnings denied: passed.
- Formatting: checked after resolving the combined grade/array match arms.
- Memory benchmark smoke run: all five workloads preserved native/reference
  allocation-counter parity; results are observations, not a speed claim.

The combined Boat gate passed for source checkpoint `20e9a0d`: **832 tests,
formatting, and Clippy**, with the sandbox confirmed stopped afterwards.
Independent review found no acceptance, ABI, ownership, or refusal-behavior
defect in its focused probes. It found a skipped match-guard traversal in
fusion analysis and stale copyable-task-result documentation; both were fixed.
The regression and existing memory/task suites pass locally (33 tests), with
formatting and library Clippy clean. This focused follow-up does not replace
the preceding full gate. Earlier branch-only test counts above are historical
evidence, not evidence that remaining unchecked features are complete.

The match-guard review fix at `3429713` also passed its focused Boat gate:
33 tests, sandbox confirmed stopped. The later `Vec.try_reserve` change is a
separate checkpoint: 86 focused local tests passed (memory, vector reuse,
allocator pool, grades, and linear resources); its remote gate is pending.

## Trait follow-up integration

Associated type defaults, `Nat`/`Grade` impl parameters, mutable dynamic
write-back, stored copyable borrowed objects, and tuple/array associated
constants are integrated. Parent integration additionally rejects mutable
calls on immutable locals and retains shared/exclusive receiver loans through
later arguments. Tests cover nested receiver mutation/replacement, legal
nested shared reads, stored-reference aliases, and mutable dispatch with
physically erased parameters/results. The 40 advanced-trait tests pass on
both backends; library/all-target Clippy and formatting pass locally. The combined remote gate at `059f99c` passed **857 tests, formatting, and
Clippy**, and the sandbox stopped afterwards. This also validates
`Vec.try_reserve`. Open-world membership, nominal-field objects, and borrowed
owning objects remain unchecked above.

## Borrowing branch validation checkpoint

At this branch's borrowing integration, the remaining reference and task
borrow items above are implemented on top of `d6b559f`. Local Linux x86-64
validation used `target/borrow-refs` with debug information disabled and two
Cargo jobs:

- Full locked workspace suite: **840 passed, 0 failed** across 61 test
  binaries.
- All-targets Clippy with warnings denied: passed.
- Formatting: `cargo fmt --all -- --check` passed.
- `tests/borrowing_safety.rs` still passes unchanged; the new positive and
  hostile cases live in `tests/borrowing_references.rs` and cover reference
  fields, reference element containers, reference-valued arrows, borrowed
  `Task.scope` records, and borrowed `TaskExit<T>` boundaries with
  native/reference agreement and balanced cleanup.

Still deliberately outside the contract: mutable owner borrows (`&mut Box`,
`&mut Vec`, `&mut Bytes`, `&mut String`), `&str` fields/containers, reading a
reference field through `&Record`, child tasks returning a borrowed
`TaskExit<T>`, capturing a borrowed `TaskExit<T>` in a lambda/task environment,
and helper-call or general lifetime unification. These are actual limits, not
silently relabelled successes.

The new borrowing integration gate and independent review are pending. Earlier
branch-only test counts above are historical evidence, not evidence that the
remaining unchecked features are complete.

Parent borrowing integration forwards named function container-result leaves
through the same call-provenance channel as records, validates their result
lifetime contracts, and merges all vector element sources on append/replacement.
The replacement value comes from the third `Vec.set` argument. Regressions cover
owner replacement after multi-source construction/update, legal clearing,
container results through named/indirect calls, and exclusive boxed reference
returns. Twelve new reference test cases pass locally, together with the
existing borrowing-safety, memory, and advanced-trait suites. The combined gate
with the latest borrowing changes is pending.
