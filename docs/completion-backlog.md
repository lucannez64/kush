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
  Two checked representations are implemented. A finite non-generic member set
  keeps the closed-world union (`owned`, copyable shared, and mutable receivers
  with temporary write-back, object arguments, associated item/default
  agreement). A trait with a generic/blanket impl, or one appearing in a
  nominal field (including `Box<dyn Trait>`/`Vec<dyn Trait>`), uses a two-word
  dynamic fat object: a registered member identifier and an owned payload
  pointer. Coercion registers the concrete member's checked method table,
  instantiates generic and non-type (`Nat`) impl parameters, allocates the
  payload under `alloc`, and dispatch resolves the identifier at runtime.
  Shared and mutable `&dyn`/`&mut dyn` and direct-local calls dispatch in place
  without copying, so borrowed objects with owning or linear members work;
  linear objects still require explicit consumption. Lifetime-parameterized
  object methods may return a view tied to a borrowed receiver or another
  caller-owned argument; the selected member's checked borrow contract is the
  lifetime witness. Generic method type parameters, owning-through-borrowed
  calls, mutable-through-shared calls, borrowed results through owned or
  temporary receivers, and associated projections supplied only by a
  parameter-dependent generic impl remain explicit rejections. Owning projected
  receivers must still be destructured into locals before method dispatch.
- [x] Specialization with an explicit deterministic coherence contract. Unique
  most-specific resolution, concrete-over-generic preference, duplicate
  rejection, and incomparable-overlap rejection are implemented and tested.
  `default fn`, negative impls, and arbitrary overlap remain rejected.

Open trait work still includes borrowed results through an owned or temporary
receiver, exact-use `@[1]` object-method results, associated projections
supplied only by a parameter-dependent generic impl, owning or `String`
associated constants, associated constants depending on an impl type parameter,
and lifetime/effect impl parameters. The dynamic representation is a
whole-program checked member table with a fixed fat-object layout, not an
FFI-compatible vtable or arbitrary open-world membership. See
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
  atom-to-union field injection, nested union-to-union repacking,
  structural record literals and patterns, affine-field cleanup, linear field
  erasure rejection, and borrowed-leaf/mutability invariance are implemented in
  both backends. Callable field adaptation, open rows, and structural records
  in impl headers remain explicitly rejected. See
  [subtyping.md](subtyping.md#structural-records).
- [ ] Broader algebraic subtype inference with documented decidability
  boundaries. **Partial:** contextual array/vector/tuple/structural literals
  and first-order generic matching accumulate constraints over every finite
  union alternative instead of choosing the first matching arm. A declared
  union pattern with one bare type variable and a concrete fixed part binds the
  residual alternatives (`T | i64`). Conflicting, incomparable, and non-unique
  residual bindings are explicit. General principal inference, indexed unions,
  and multi-variable backtracking remain out of scope. See
  [subtyping.md](subtyping.md#contextual-and-algebraic-inference).
- [ ] Effect handlers and checked resumption ownership. **Partial:** lexical
  one-shot `handle`/`perform`, nested shadowing, first-class handler callables,
  a linear resumption token, handler-effect propagation, owning payload/cleanup
  checks, and declared `effect` operations with a dynamic one-shot handler
  stack across called functions work in both backends. A tail `perform` keeps
  the allocation-free identity token; a `perform` that is the whole value of a
  top-level statement now lowers to a real one-shot continuation closure, so
  the handler can run code after `resume(x)` returns. The continuation fragment
  requires exactly one such perform, the body result to equal the operation
  result, no `return`/`break`/`continue` through the resumption, and rejects
  mutable/borrowed captures; a capturing continuation requires `alloc`. The
  dynamic stack stores pure noncapturing `fn` handlers and restores its depth
  on early returns. A dynamically resolved `perform` requires `panic`, since a
  missing handler aborts. General expression-context and multi-prompt
  continuations, non-tail dynamic resumption, multishot handlers, capturing
  dynamic handlers, task-crossing dynamic frames, and user-defined effect-row
  names are not implemented. See [effect-handlers.md](effect-handlers.md).
- [ ] General row constraints beyond concrete exclusions. **Partial:** a finite
  Boolean constraint solver accumulates inclusion constraints across every
  higher-order argument, supports up to three unbound row variables (4096
  assignments), unions evidence from repeated row variables, supports union and
  subtraction inside declared rows (`{e - io}`), applies exclusion and
  required-effect (`+`) lower bounds, and rejects ambiguous/nonminimal groups.
  The unique componentwise-minimal solution is the principal row for solved
  groups, but an unconstrained open row variable is still rejected rather than
  defaulted to `{}`. There is no recursive row unification, row aliasing, or
  general first-class row difference. See
  [effect-constraints.md](effect-constraints.md#accumulated-row-constraints).
- [ ] Broader runtime-dependent proofs with mutation/version tracking.
  **Partial:** mutable scalar locals index erased proofs at their current
  version; assignment appends a fresh versioned binder or records an assigned
  canonical literal; an old literal proof is rejected against the new value; a
  by-value scalar alias keeps the copied binder across later mutation; a
  closure capture is an independent frozen snapshot. Branch joins keep an
  index only when every reaching branch agrees, and loop joins invalidate a
  changed scalar to a fresh binder. Erased proof-valued locals can alias
  checked logical terms and be re-passed to erased parameters. Mutable captures
  as a live view and arithmetic proof search remain absent. See
  [runtime-indices.md](runtime-indices.md#4-freezing-mutation-and-joins).
- [ ] Runtime-sized inline arrays with checked lifetime/storage layout.
  **Partial:** `DynArray<T, capacity>` has compile-time capacity, runtime
  length, inline storage, checked push overflow, checked reads, `set`, `pop`,
  owning-prefix drop, and native/reference agreement. `set`/`pop` are copyable
  element operations and check the live runtime length. There is no literal,
  pattern, slice view, or runtime `[T; n]`; capacity remains a compile-time
  bound. See [dynamic-arrays.md](dynamic-arrays.md).

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
- [x] Widening reuse with explicit allocation/capacity guarantees.
  **Implemented for box payloads and vector elements:** `Box.reuse_grow`
  checks the old owner and payload obligations, destroys the old payload once,
  and either keeps the allocation or grows/moves it under an explicit
  `{alloc, panic}` contract. `Vec.map_in_place_grow` and
  `Vec.map_chain_in_place_grow` widen the final element layout under the same
  explicit contract, reuse retained physical capacity when it fits, and
  otherwise grow/move once with safe backwards relocation and unchanged
  callback order, drop behavior, and final stride. `#[noalloc]` rejects all
  three; plain `Box.reuse` and the non-growing map operations keep their
  no-allocating-fallback contracts.
- [ ] Custom allocators and lifetime-safe allocator ownership. **Partial, with
  a documented built-in allocator strategy:** `Arena`/`ArenaBox` with
  reference-retained regions, deterministic drop, function/task escape, and
  checked provenance. `Arena.with_strategy` adds a user-defined, noncapturing
  pure chunk-sizing policy stored as a code pointer in the region.
  Arbitrary user-defined alloc/dealloc callbacks, an allocator trait, FFI, and
  containers that own a general allocator value are deliberately not
  implemented and are not claimed.
- [x] Fallible allocation/reuse with exact cleanup on all failure paths.
  **Implemented:** `Box.try_new`, growth-capable `Box.try_reuse`,
  `Bytes.try_with_capacity`, `Vec.try_reserve`, and `Arena.try_alloc` return
  the conventional checked `Result`; failures preserve the old owner, the
  supplied payload, and (for arena/vector) the original region or vector state.
  Real native malloc refusal and a reference allocation budget are both
  exercised; no process abort is disguised as `Err`. Vector refusal retains
  every element, length, capacity, and owner obligation; physical-capacity and
  failure-budget parity are tested. A refused arena chunk request leaves the
  region's references, chunks, and bump position untouched, and a request that
  fits the current chunk spends no fallible attempt.
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
owning objects were still unchecked at that historical checkpoint; the
trait-object completion checkpoint below addresses them.

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

The independent vector/trait review confirmed vector reserve parity and found a
projected owning method-receiver double-free. Method dispatch now rejects an
owning field projection before it can copy an owner, including static owned
methods and dynamic owned/mutable calls. Mutable projected copyable objects
are also rejected instead of silently losing updates. Regressions cover tuple
fields, generic wrappers, and legal destructuring before mutable dispatch.
The previous 857-test gate predates these fixes and the latest borrowing/effect
integration; the new full gate is pending.

## Trait object completion checkpoint

The remaining trait-object contracts are implemented on top of `460ec58`:
open/generic member sets use a fixed two-word dynamic fat object with a checked
per-member method table, nominal fields may spell `dyn Trait` directly, stored
borrowed objects with owning/linear members dispatch in place, call-scoped
lifetime parameters are accepted on object methods, and generic impl headers
with `Nat` parameters substitute per registered member. Local Linux x86-64
validation used `target/dyn-traits` with debug information disabled and two
Cargo jobs:

- Full locked workspace suite: **890 passed, 0 failed**.
- `cargo fmt --all -- --check`: passed.
- All-targets Clippy: passed.

`crates/kush/tests/trait_advanced.rs` adds positive and hostile cases for open
blanket impls, nested generic member dispatch, `Nat` impl substitution, nominal
`dyn`/`Box<dyn>` fields, borrowed owning and linear members (including linear
consumption rejection), lifetime-parameterized object methods returning a view
of a caller argument in both representations, temporary shared dispatch
rejection, and owned/temporary-receiver borrowed-result rejection.
Native/reference agreement and allocation balance are checked by the shared
`agrees` helper.
The remote combined gate is parent-coordinated.

## Latest combined gate

Compiler checkpoint `460ec58` passes **878 tests** in the full locked local
workspace suite and the full Boat gate. Formatting and all-targets Clippy pass.
This includes the projected-receiver double-free fix, the reference-container
and vector-source fixes, and the declared-effect/structural/DynArray follow-up.
Boat reused the persistent workspace marker after resume. Remaining unchecked
items above are still outstanding; this gate does not establish completeness
or constitute an independent review of the latest borrowing/effect changes.

## Independent borrowing/effects review follow-up

An independent read-only review of `460ec58` (borrowing and advanced
type/effect integration) found three defects, now fixed with regressions:

- **High:** structural record coercion (`Coercion::Struct`) treated as
  transparent by the ownership pass, so per-field borrow provenance stayed at
  source field indices. A field that moved index lost its loan, letting the
  owner be replaced while a slice view or `Vec<&T>` element was still live
  (native read of freed storage). Provenance and field places are now remapped
  through the coercion's target-to-source field map; dropped fields release
  their loans.
- **Medium:** shared `&Box<&T>` / `&Vec<&T>` parameters hit an internal
  "stored reference has no capability provenance" error on any element read.
  They now carry per-element provenance rooted at the parameter with the
  declared element lifetime. `&mut` reference-container parameters keep the
  previous behavior. Mismatched annotation labels on nested reference types
  (`&'a Box<&'a T>` against an unlabeled argument) are still reported as a
  type mismatch.
- **Medium:** a dynamically resolved `perform` aborts when no handler is
  active but did not require `panic`; it now does.

The reviewer found handler-depth restoration (`break`, `return`, `?`, nested
calls), task isolation of dynamic frames, and vector element-origin unions
sound within its probe budget.

## Memory remainder checkpoint

Compiler checkpoint `c78c444` implements the remaining executable memory-area
gaps on top of `460ec58`:

- `Arena.try_alloc` is fallible, returns the untouched payload on refusal, and
  leaves region references, chunks, and bump state unchanged. Requests fitting
  the current chunk spend no fallible attempt.
- `Vec.map_in_place_grow` and `Vec.map_chain_in_place_grow` provide explicit
  `{alloc, panic}` vector-element widening. They reuse retained physical
  capacity when it fits, otherwise grow/move once; native relocation is
  backwards for widening and forwards for narrowing, callbacks stay in forward
  source order, owning elements are consumed once, and the final stride governs
  later vector operations.
- `Arena.with_strategy` stores a user-defined pure noncapturing
  `fn(need, current) -> capacity` chunk-sizing policy as a code pointer.
  This is an allocation policy, not a general allocator.
- Growth-capable maps are excluded from automatic fusion.

Local Linux x86-64 validation used `target/memory-c1616b8a` with debug
information disabled and two Cargo jobs:

- Full locked workspace suite: **893 passed, 0 failed** across 61 test binaries.
- `cargo fmt --all -- --check`: passed.
- All-targets Clippy with warnings denied: passed.
- New tests cover fallible-arena success/refusal/region reuse, chunk-strategy
  behavior and rejections, structured-payload preservation, vector widening
  growth/reuse/order/drop/layout, chain widening, fusion exclusion, and
  native/reference parity.

The Boat gate for `c78c444` is parent-coordinated and was not run from this
checkout. Arbitrary user alloc/dealloc callbacks, allocator traits, FFI, and
container-owned general allocators remain absent; the custom-allocator backlog
item stays unchecked, so this checkpoint does not claim that all memory work is
complete.

## Merged gate after review fixes and memory remainder

Merge `0f640b5` (review fixes `2f807d5` plus memory remainder `c78c444`)
passes **896 tests** on the full Boat gate, with formatting and all-targets
Clippy clean. The trait-object/open-world work is still in progress on a
separate branch and is not included.

## Merged gate with open dynamic trait objects

Merge `49ea138` adds the open dynamic trait-object work (`2481d7d`,
`7963eed`: fixed-layout dynamic objects with per-member method tables,
nominal `dyn` fields, in-place borrowed dispatch of owning/linear members,
lifetime-parameterized object methods, per-member `Nat` impl substitution) on
top of `7f372cf`. The full Boat gate passes **908 tests**, formatting, and
all-targets Clippy. This work has not yet had an independent review.
Remaining boundaries are listed in [traits.md](traits.md).
