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
  reborrow, explicit `&*p`/`&mut *p`, shared and exclusive
  `&Box`/`&Vec`/`&Bytes`/`&String` escape contracts, direct reference fields in
  nominal records, and reading shared reference/slice/text fields through
  `&Record` are checked. `Box<&T>`, `Vec<&T>`, `Box<&str>`, and `Vec<&str>`
  element containers carry explicit type-level lifetime annotations and
  preserve owner loans through construction, reads, calls, records, and arrows.
  `Vec<Holder<'a>>` and `Box<Holder<'a>>` store borrowed records with per-field
  element provenance; construction, indexed reads, `push`/`set`/`clear`, box
  reads/takes, `&mut` writes, records, and direct/indirect calls keep every
  field owner loaned. Mutable owner borrows are supported for `&mut Box`/`&mut
  Vec`/`&mut Bytes`/`&mut String`: `Box.set` and
  `Vec.push`/`set`/`clear`/`reserve` update the caller's container, and a
  written reference must outlive the declared element lifetime. A call that
  mutates a `&mut` container also merges the written reference's owner loan into
  the caller's container provenance. General `&place`/`&mut place` references
  now alias nested and owning record fields, inline-array elements, `Vec<T>`
  elements, and hidden temporary owners; both backends use real storage
  identity, structural disjointness (record fields and distinct constant
  indices), ancestor suspension, and last-use release. General `*p` reads copy
  only non-owning, non-linear referents, and `*p = value` replaces an affine
  referent by destroying the old payload exactly once. A temporary aggregate or
  owning handle is hoisted into hidden storage whose cleanup follows every
  checked reference. Remaining exclusions: `&mut str` (unrestricted byte writes
  can invalidate UTF-8), place references into slice elements, mutation of a
  record with borrowed fields as a whole, runtime-index disjointness (all
  dynamic indices of one base conflict), and a child task returning a borrowed
  `TaskExit`. See
  [borrowing-extensions.md](borrowing-extensions.md).
- [ ] Broader sound lifetime inference. **Partial:** function/arrow/lambda
  results can be inferred from a single record-field source or a per-field body
  origin. A multi-lifetime record supports per-field selection, including
  nested field paths. Several returned sources now form an anonymous
  intersection: the result is outlived by every source, all owners stay loaned,
  and a call site selects the shortest provable actual lifetime or keeps the
  anonymous identity. Inference follows local destructuring bindings and simple
  aliases (`let Pair { left, right } = pair;`, nested record patterns). Missing
  outlives bounds between a returned source and an explicit result lifetime are
  inferred and validated at call sites, including through destructured bindings;
  a body that delegates to a helper follows the helper's declared result
  source. This is a finite, closed constraint graph over one function's
  declared lifetimes with a documented reachability decision procedure (see
  [borrowing-extensions.md](borrowing-extensions.md#lifetime-constraints-and-decidability)).
  A returned `&Field` may also name a field of a `&Record` parameter; the finite
  `reference_reaches_type` reachability rule accepts it when the parameter
  lifetime outlives the result, and the ownership pass still proves the exact
  origin. Principal unification for recursive lifetime constraints, variance,
  and row variables remains explicitly absent.
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
  agreement). A trait with a generic/blanket impl, a generic method, or one
  appearing in a nominal field (including `Box<dyn Trait>`/`Vec<dyn Trait>`),
  uses a two-word dynamic fat object: a registered member identifier and an
  owned payload pointer. Coercion registers the concrete member's checked
  method table, instantiates generic and non-type (`Nat`/`Grade`) impl
  parameters, allocates the payload under `alloc`, and dispatch resolves the
  identifier at runtime. A trait whose only impls are generic or blanket impls
  is usable as `dyn`: its table starts empty and members are registered at
  coercion. Generic methods are monomorphized per call-site type/`Nat`/grade/
  effect argument list into the member table, including later members and later
  call sites. Shared and mutable `&dyn`/`&mut dyn` and direct-local calls
  dispatch in place without copying, so borrowed objects with owning or linear
  members work; linear objects still require explicit consumption. Lifetime-
  parameterized object methods may return a view tied to a borrowed receiver or
  another caller-owned argument. An owned receiver may return a view of a
  caller-owned argument (it has no receiver lifetime). A temporary shared
  dynamic receiver is bound to a hidden local and may likewise return an
  explicit argument-tied view, but an elided or receiver-tied view remains
  rejected. Associated projections supplied only by a parameter-dependent
  generic impl are fixed by the first concrete member registered for that
  object specialization; every later member must agree. Shared dispatch on an
  owning projected field (`pair.0.read()`, `self.inner.read()`) borrows the
  field in place. Remaining explicit rejections: receiver-tied borrowed results
  through owned or temporary receivers, mutable or consuming dispatch on a
  projected field, an associated projection needed before any member of that
  object specialization is registered, and multi-trait `dyn A + B` syntax
  (closed-world objects already share coincident member sets; an open dynamic
  object represents one trait specialization). Effect-row trait parameters do
  not exist in the language, so `dyn Trait<Effect>` cannot be named. The
  dynamic representation is a whole-program checked member table with a fixed
  fat-object layout, not an FFI-compatible vtable or arbitrary open-world
  membership.
- [x] Specialization with an explicit deterministic coherence contract. Unique
  most-specific resolution, concrete-over-generic preference, duplicate
  rejection, and incomparable-overlap rejection are implemented and tested.
  `default fn`, negative impls, and arbitrary overlap remain rejected.

Open trait work still includes receiver-tied borrowed results through an owned
or temporary receiver, exact-use `@[1]` object-method results, mutable or
consuming dispatch on projected fields, projections needed before any member of
an object specialization is registered, multi-trait `dyn A + B` syntax, owning
or `String` associated constants, associated constants depending on an impl
type parameter, and lifetime/effect impl parameters. The dynamic representation
is a whole-program checked member table with a fixed fat-object layout, not an
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

- [x] Structural record subtyping and representation-changing coercions.
  **Implemented:** anonymous `struct { ... }` rows, canonical field order,
  width/order subtyping, recursive nested structural field conversions,
  atom-to-union field injection, nested union-to-union repacking,
  representation-changing callable-field adapters (with one-time linear
  capture and checked effects), erased `..` open-row annotations, structural
  record literals and patterns, exact-row structural impl headers (including
  generic patterns), affine-field cleanup, linear field erasure rejection, and
  borrowed-leaf/mutability invariance are implemented in both backends.
  Named `..r` row variables are monomorphized per concrete residual row and
  preserve unmentioned owning, linear, and borrowed fields through function
  parameters/results; nested rows unify recursively, one row variable must
  receive the same residual from every parameter, and an unbound tail is
  rejected. Open named-row impl headers dispatch on structural receivers with
  checked coherence. Explicit top-level field renaming uses
  `value as struct { target: T from source }` with each source moved once.
  Structural `==`/`!=` compares every canonical field when leaves are copyable
  scalars or nested structural rows; both operands are evaluated once in both
  backends. Remaining boundaries are documented, not silent: nested field
  renaming, row subtraction/aliasing, first-class row values, bare `..` impl
  headers, borrowed structural results, and floating-point/owning/borrowed/
  union/nominal structural equality. See
  [subtyping.md](subtyping.md#structural-records).
- [ ] Broader algebraic subtype inference with documented decidability
  boundaries. **Partial:** contextual array/vector/tuple/structural literals
  and first-order generic matching accumulate constraints over every finite
  union alternative instead of choosing the first matching arm. A declared
  union pattern with one bare type variable and a concrete fixed part binds the
  residual alternatives (`T | i64`); this rule is principal. Several bare
  variables partition the residual alternatives with a bounded (4096-step)
  canonical search (`T | U | i64`). Cross-parameter backtracking now replays
  the whole constraint group from the base substitution when a later parameter
  rejects an earlier partition; the replay is deterministic, lexicographic,
  and capped at 4096 complete attempts, with budget exhaustion explicit. Named
  row variables provide recursive residual-row unification for structural
  records. The principal result and its exact boundary are documented:
  single-variable residuals are principal, multi-variable partitions are
  deterministic but not principal, and indexed/dependent unions remain an
  explicit-specialization boundary (a union of `Option<i64> | Option<Bool>` is
  never collapsed to an invariant `Option<i64 | Bool>`). General indexed-union
  inference is still missing, so this item stays unchecked. See
  [subtyping.md](subtyping.md#contextual-and-algebraic-inference).
- [ ] Effect handlers and checked resumption ownership. **Partial, still
  open:** lexical one-shot `handle`/`perform`, nested shadowing, first-class
  handler callables, a linear resumption token, handler-effect propagation,
  owning payload/cleanup checks, and declared `effect` operations with a
  dynamic one-shot handler stack across called functions work in both backends.
  A tail `perform` keeps the allocation-free identity token; a `perform` that is
  the whole value of a top-level statement lowers to a real one-shot
  continuation closure, so the handler can run code after `resume(x)` returns.
  The continuation fragment requires exactly one such perform, the body result
  to equal the operation result, no `return`/`break`/`continue` through the
  resumption, and rejects mutable/borrowed captures; a capturing continuation
  requires `alloc`. A dynamically resolved `perform` requires `panic`, since a
  missing handler aborts. New since the previous checkpoint: a declared
  `effect Op` is also a concrete effect-row entry checked like
  `io`/`alloc`/`panic`/`suspend` (a perform requires `Op`; a lexical handle
  discharges it for its body), with a finite sixteen-bit row universe (at most
  twelve declared operations). Dynamic frames accept pure capturing `once`
  handlers and own/drop their environment exactly once on pop or early exit; a
  child task inherits the innermost contiguous suffix of copyable noncapturing
  frames while capturing/one-shot frames are an isolation boundary. A
  capture-free continuation may use the copyable `fn(R) -> R` multishot token
  and be resumed zero or more times. Still missing and explicitly rejected:
  general expression-context continuations and multiple non-tail performs per
  handled body (a single top-level statement perform only), non-tail
  resumption of a dynamically resolved perform across the call stack (dynamic
  performs remain tail-resumptive identity), and multishot for continuations
  with nonempty (even copyable) captures, which keep an owned environment.
  See [effect-handlers.md](effect-handlers.md).
- [x] General row constraints beyond concrete exclusions. A finite Boolean
  constraint solver accumulates inclusion constraints across every higher-order
  argument, unions evidence from repeated row variables, and supports arbitrarily
  nested union and subtraction on the declared side (`{e - io}`,
  `{(e | alloc) - io - alloc}`). Declared `effect row Name = { ... };` aliases
  expand transparently, may name other aliases, and reject cycles. The solver is
  per-bit: the sixteen concrete effect bits are independent, so `n` variables need
  `2^n` assignments per bit instead of `16^n` whole rows, with a documented bound
  of 16 variables per call group. An unconstrained open row now defaults to its
  principal least row (`{}` without a lower bound, exactly the required bits with
  `<e: Effects + ...>`), and the callee body is rechecked under that
  specialization so defaulting cannot hide an effect. Solutions must be unique
  componentwise-minimal; incomparable minimal rows are still explicit ambiguity
  errors. Because rows are finite sixteen-bit vectors, recursive row expressions
  are solved by the same accumulation rather than a separate infinite
  unification step. Remaining language limits: parameterized row aliases,
  first-class row values (rows only occur in effect annotations), row equality
  predicates. See
  [effect-constraints.md](effect-constraints.md#accumulated-row-constraints).
- [ ] Broader runtime-dependent proofs with mutation/version tracking.
  **Partial:** mutable scalar locals index erased proofs at their current
  version; assignment appends a fresh versioned binder or records an assigned
  canonical literal; an old literal proof is rejected against the new value; a
  by-value scalar alias keeps the copied binder across later mutation; a
  closure capture is an independent frozen snapshot. Branch joins keep an
  index only when every reaching branch agrees, and loop joins invalidate a
  changed scalar to a fresh binder. Erased proof-valued locals can alias
  checked logical terms and be re-passed to erased parameters. The separate
  erased arithmetic `{ ... }` fragment now supports general linear expressions
  (`c * x`, `x + y`, lengths) and is discharged by exact Fourier–Motzkin
  elimination with an independently verified Farkas-style refutation
  certificate; nonlinear terms, cutting planes, and the documented row/term
  budgets remain explicit "not established" boundaries. Still absent: mutable
  captures as a live view. A closure capture is a sound copy/snapshot; live
  sharing needs a checked closure borrow lifetime so the environment cannot
  outlive the captured location, which is not implemented. See
  [runtime-indices.md](runtime-indices.md#4-freezing-mutation-and-joins) and
  [runtime-indices.md](runtime-indices.md#4a-arithmetic-proof-search).
- [ ] Runtime-sized inline arrays with checked lifetime/storage layout.
  **Partial:** `DynArray<T, capacity>` has compile-time capacity, runtime
  length, inline storage, checked push overflow, checked reads, `set`, `pop`,
  owning-prefix drop, contextual literals, shared `&[T]` views, exclusive
  `&mut [T]` views over the live prefix with exclusive-loan rules, views
  through a direct local record's `DynArray` field (including nested fields),
  elementwise equality for one-word comparable elements, and length-checked
  patterns with a trailing `..`/`..name` tail binding and mandatory catch-all.
  Literals are statically bounded by the capacity and use the checked push
  sequence, so their overflow guards are unreachable and no `panic` effect is
  added. Views read the runtime length word, use the same slice operations as
  arrays, reject owner moves/drops/push/set/pop/reads while live, reject
  aliasing exclusive views, and cannot escape the owner's lexical scope. Still
  missing: runtime `[T; n]` (the array length in a type annotation remains a
  compile-time `Nat`; a runtime length is an explicit diagnostic pointing at
  `Vec<T>`), a pattern suffix after `..`, borrowed-element or recursive
  element patterns, and views over a `DynArray` inside a reference-based record
  place or temporary record. Capacity remains a compile-time `Nat`. See
  [dynamic-arrays.md](dynamic-arrays.md).

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
- [ ] Custom allocators and lifetime-safe allocator ownership.
  **Partial:** `Allocator.new(alloc, free)` packages two noncapturing
  callbacks, `fn(i64) -> Bytes` and `fn(Bytes) -> Unit`, and is a copyable
  code-pointer value that owns nothing. `Allocator.with_realloc(alloc, free,
  realloc)` adds a checked `fn(Bytes, old_bytes: i64, bytes: i64) -> Bytes`
  growth hook; `AllocVec` growth uses it when a block already exists, and the
  hook consumes the old block and returns a block with at least the requested
  capacity that still contains the live bytes. `AllocBox<T>` and `AllocVec<T>`
  store their own copy of the callbacks and therefore keep the allocator alive
  with every allocation: dropping or moving the allocator binding while
  containers are live is defined and safe, release always uses the copy
  recorded in the container, and both containers are affine so each block is
  released exactly once. Allocation callbacks may declare only
  `alloc`/`panic`; release callbacks must be pure because they also run during
  implicit drop. A returned `Bytes` block with less than the requested capacity
  is a refusal: `AllocBox.new` panics, `AllocBox.try_new` returns the untouched
  payload, and the refusal block is released through the same allocator.
  `AllocVec.push` uses the growth hook or allocates a fresh block, copies live
  elements, and releases the old block through the same pair. `AllocVec.try_push`
  is fallible: refusal returns the unchanged vector and the untouched element
  in `Err`, preserving every element, length, capacity, and block, and it never
  uses the growth hook because a refusing hook would already have consumed the
  old block. `AllocVec.pop` returns `(vector, element)` for copyable elements
  and panics on an empty vector. `Arena`/`ArenaBox` with reference-retained
  regions, deterministic drop, function/task escape, and
  `Arena.with_strategy` remain available. Explicit remaining limits: no user
  `Allocator` trait and no container type parameter over an allocator type;
  containers accept the copyable code-pointer value, not an arbitrary
  instance-carrying implementor. An instance-carrying allocator would need an
  owned callable environment and a lifetime-safe vtable, and the language has
  no FFI, raw pointers, or `unsafe`, so this remains an explicit language
  boundary rather than a silent partial implementation. Also absent:
  user-supplied per-container metadata allocation (fixed headers are
  runtime-owned bookkeeping) and FFI/raw-pointer callbacks. See
  [memory-completion.md](memory-completion.md#41-user-defined-allocators).
- [x] Fallible allocation/reuse with exact cleanup on all failure paths.
  **Implemented:** `Box.try_new`, growth-capable `Box.try_reuse`,
  `Bytes.try_with_capacity`, `Vec.try_reserve`, `Arena.try_alloc`, and
  user-allocator `AllocBox.try_new` return the conventional checked `Result`;
  failures preserve the old owner, the supplied payload, and (for
  arena/vector/allocator) the original region, vector, or allocator state. An
  allocator callback that returns an undersized block is a refusal, not a
  partial success, and the refusal block is released by the same allocator.
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

## Dynamic trait-object review follow-up

An independent review of the open dynamic trait objects (`2481d7d`,
`7963eed`) found no memory unsafety in about 35 probes, but three type-system
defects, fixed in `7909e58` with regressions:

- **High:** object linearity was computed after layout linearity, so a record,
  inline array, or enum holding a linear `dyn` object (and `DynArray` of
  objects) could drop it implicitly. Layout and object linearity are now one
  joint fixed point; `DynArray` elements and width-erased structural fields
  conservatively reject dynamic objects.
- **Medium:** a stored `&dyn` did not block a later `&mut dyn` or mutable
  dispatch on the owner. Objects now use the record shared/exclusive borrow
  discipline.
- **Medium-low:** a trait with one concrete impl collapsed `dyn Trait` to the
  member type, so stored `&dyn`/`&mut dyn` dispatch was rejected. Closed
  objects now keep a one-alternative union representation.

Documented limits added: generic-only traits cannot be `dyn`, and temporary
shared receivers of open objects are rejected. Full Boat gate: **911 tests**,
formatting, and Clippy pass.

## Merged gate with resumption, row subtraction, and proof joins

Merge `a296e01` adds one-shot non-tail lexical resumption, finite effect-row
subtraction, and branch/loop proof joins with proof-valued locals (`87de1ef`
through `d3ab542`) on top of the dynamic-object review fixes. The full Boat
gate passes **919 tests**, formatting, and Clippy. An independent review of
this merge is pending.

## Merged gate with structural adapters, open rows, and partition inference

Merge `a6a99ac` adds structural callable-field adapters, structural impl
headers, erased open rows, and bounded multi-variable union partition
inference (`0a93e3f` through `f27606a`). The full Boat gate passes
**924 tests**, formatting, and Clippy. An independent review is pending.

## Allocator and DynArray completion checkpoint

The user-allocator completion and the runtime-sized-array literal/view work are
implemented on top of `a87f77b`; `DynArray` patterns and mutable views remain
explicit rejections, so that backlog item stays partial:

- `e19c470` adds checked `Allocator`, `AllocBox<T>`, and `AllocVec<T>` values,
  their reference/native lowering and drops, the fallible
  `AllocBox.try_new` path, and `crates/kush/tests/allocator_containers.rs`.
- `7f99701` adds contextual `DynArray` literals and shared live-prefix `&[T]`
  views with owner-loan tracking in
  `crates/kush/tests/advanced_types_effects.rs`; `DynArray` patterns and
  mutable views are explicit, tested rejections and remain outstanding.
- `0c8681b` boxes the new evaluator heap states so the recursive reference
  evaluator keeps its previous stack frame headroom; this restores the JSON
  recursion/limit test that the larger `Value` enum had pushed past the default
  test-thread stack.
- `890743f`, `4f5b26e`, and `2d7615a` update the memory/dynamic-array/backlog
  contracts and add the divergent-payload and multiword-element regressions.

Local Linux x86-64 validation used
`CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/alloc-dynarray` with debug
information disabled and two Cargo jobs:

- Full `cargo test -p kush --offline -j 2` passed with 921 tests, 0 failed.
- `cargo fmt --all -- --check` passed.
- `cargo clippy -p kush --all-targets --offline -j 2 -- -D warnings` passed.

Still explicit, tested rejections or documented limits: `DynArray` patterns,
mutable `&mut [T]` DynArray views, runtime `[T; n]`, allocator traits, FFI/raw
pointers, allocator-supplied container metadata, and a general `realloc` hook.
The remote Boat gate for this checkpoint was not run from this checkout.

## Merged gate with references/lifetimes and allocators/DynArray

Merges `6d48059` (references and lifetime inference, `6dbc336` through
`5ee82c0`) and `d111733` (user allocators and DynArray literals/views,
`e19c470` through `d7a71fa`) are on `main`. Conflict resolution unified owner
borrow discipline across records, trait objects, and owning handles, and
extended dynamic-object and borrowed-element checks to `AllocBox`/`AllocVec`.
The full Boat gate passes **943 tests**, formatting, and Clippy. Independent
reviews of these two merges are pending.

## Resumption/proof review follow-up

An independent review of `a296e01` found no leaks or double drops in
continuation captures, and confirmed row subtraction cannot hide performed
effects. It found five defects, now fixed with regressions:

- **High:** `match` arms did not join scalar proof indices (each arm saw the
  previous arm's state), so a proof about one arm's literal was accepted in
  another arm or after the match. Arms now start from one baseline and are
  joined N-way like `if`.
- **High:** leaving a nested block truncated the proof context but left scalar
  indices pointing past it, so two different locals could share a binder and a
  false `Eq` was accepted. Every scope exit now re-binds such scalars.
- **Medium:** `?` inside a non-tail continuation was checked against the
  operation result and could swallow errors; it is now rejected like `return`.
- **Low:** `break`/`continue` for loops inside a continuation were rejected,
  and `let mut x = perform ...` lost `mut` in the continuation. Both fixed.
Full Boat gate after these fixes (`f44a221`): **946 tests**, formatting, and
Clippy pass.

## Structural review follow-up

An independent review of `a6a99ac` confirmed callable-adapter
capture/cleanup, borrow provenance through structural coercions, open-row
erasure of linear/`dyn` fields, and structural impl coherence. It found four
defects, fixed with regressions:

- **High:** injecting a record into a union alternative with a different
  structural row copied raw words instead of converting, reading wrong fields,
  leaking erased owners, and (natively) passing a scalar as a `Box` pointer.
  Injection now converts to the selected member first; union-to-union and
  nested repacking require an unchanged member layout and otherwise ask for an
  explicit conversion.
- **High:** native closure-environment drop synthesis walked only some
  expression kinds, so an adapter under `DynArray.push` (and similar) crashed
  the native compiler. Analyses now use an exhaustive `Expr::for_each_child`
  walk; byte-literal collection uses it too.
- **Medium-low:** a structural record result with a borrowed field produced an
  internal error; it is now a clean rejection.
- **Low:** multi-variable union partitions followed pattern operand order;
  they now follow generic declaration order as documented.

## Mutable-owner/allocator/DynArray review follow-up

An independent review of `6d48059` and `d111733` confirmed aliasing
rejections (`f(&mut v, &mut v)`, `&mut` under live views), direct container
write escape checks, lifetime inference against smuggling, `&Record` text
fields, allocator growth/release through the recorded allocator, and DynArray
view rules for push/set/assignment. It found three defects, fixed with
regressions:

- **High:** a reference written into a container through a stored `&mut`
  reference local was recorded only on that local, so the owner escaped the
  block-exit check and natively read a freed `String` (also `Box.set` and
  `Vec<&Record>`). The element loan is now also recorded on the referenced
  owner.
- **High:** `AllocVec<T>` accepted reference/text elements without tracking
  their provenance. `AllocBox`/`AllocVec` element types may no longer carry
  borrows (at annotation and at `AllocVec.new`), and `AllocVec` joins `Vec` in
  rejecting linear elements.
- **Low:** `DynArray.pop` was accepted while a slice view of the array was
  live, contrary to the documented contract; it is now rejected.

## Gate after all review follow-ups

`dedb144` (all four implementation merges plus every review fix) passes the
full Boat gate: **953 tests**, formatting, and Clippy.

## Structural rows and algebraic inference checkpoint

Local Linux x86-64 validation used
`CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/close-structural` with
debug information disabled and two Cargo jobs:

- Full `cargo test -p kush --offline -j 2`: **958 passed, 0 failed** across 61
  test binaries.
- `cargo fmt --all -- --check`: passed.
- `cargo clippy -p kush --all-targets --offline -j 2 -- -D warnings`: passed.

The structural-record backlog item is checked: true named row variables
(including nested residual-row unification and open-row impl headers), explicit
top-level field renaming, and structural equality over comparable leaves are
implemented in both backends with hostile and positive tests. The algebraic
inference item remains unchecked because indexed/dependent union inference is
still absent: it is an explicit-specialization boundary, not a silently guessed
alternative. Cross-parameter partition replay is bounded at 4096 complete
attempts; the single-variable residual rule is principal, while multi-variable
partitions are deterministic but not principal. Borrowed structural results,
nested field renaming, row subtraction/aliasing, first-class row values, and
bare `..` impl headers remain explicit, tested rejections. See
[subtyping.md](subtyping.md#structural-records).

## Declared effect rows, owned dynamic frames, and task inheritance

`6c6b08e` and `c55ccbf` extend the effect-handler fragment on top of
`15f62d3`:

- `6c6b08e` makes `effect Op: P -> R;` a concrete effect-row entry and widens
  the finite row universe from eight to sixteen bits (four built-ins plus up to
  twelve declared operations). A dynamic `perform Op` requires `Op` like
  `io`/`alloc`/`panic`/`suspend`; a lexical `handle Op` discharges it for its
  body. The constraint solver now enumerates only the effects a minimal
  solution can need, so declared rows stay within the 4096-assignment budget.
- `c55ccbf` lets a declared operation's dynamic frame own a pure capturing
  `once` handler environment. The environment is transferred to the first
  perform, or dropped exactly once by pop, early `return`, `break`, or
  `continue`. A one-shot frame is skipped by later performs instead of being
  reused. A child task inherits the innermost contiguous suffix of copyable
  noncapturing frames; capturing and one-shot frames are the isolation
  boundary. A capture-free continuation may use the copyable
  `fn(R) -> R` multishot token; continuations with any captures stay one-shot.

Local Linux x86-64 validation used
`CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/close-effects` with debug
information disabled and two Cargo jobs:

- Full `cargo test -p kush --offline -j 2`: **958 passed, 0 failed** across 62
  test binaries.
- `cargo fmt --all -- --check`: passed.
- `cargo clippy -p kush --all-targets --offline -j 2 -- -D warnings`: passed.

The effect backlog item stays **unchecked**. Still explicitly rejected and
tested: general expression-context continuations, more than one non-tail
`perform` per handled body, non-tail resumption of a dynamically resolved
perform across the call stack, multishot with nonempty captures, and multishot
handlers for declared operations (their dynamic perform always supplies the
one-shot token). The remote Boat gate was not run from this checkout.

## Evaluator stack regression after owned dynamic handlers

The full Boat gate for `97e0cd1` failed in the JSON depth-limit suite with a
host stack overflow. The evaluator's handler, allocation, and direct-call
branches now live in non-inlined helpers, so their temporaries do not enlarge
every recursive expression frame. Fuel and depth limits, JSON inputs, and
cleanup behavior are unchanged.

Local validation used `mbx` exclusively with `target/mbx-main` and two jobs:
full locked workspace tests **963 passed, 0 failed**, all-targets Clippy with
warnings denied passed, formatting passed. The previously overflowing JSON
suite passes with the default test-thread stack. The full Boat gate also passed: 963 tests, formatting, and Clippy.
The effect-row/proof branch `t3/7dc078f9` remains unmerged at this checkpoint.

## Row constraints and arithmetic proof-search checkpoint

This branch implements the two backlog areas as far as their sound contracts
allow, on top of `15f62d3`:

- **General row constraints** are now a finite, per-bit Boolean row solver.
  Unconstrained open rows default to their principal least row (exactly the
  `<e: Effects + ...>` lower bound, or `{}` without one), the callee body is
  rechecked under that specialization, and the old three-variable/4096-assignment
  limit is lifted to 16 variables per call group with `2^n` assignments per
  effect bit. Declared `effect row Name = { ... };` aliases expand transparently,
  compose, and reject cycles. Nested union/subtraction on the declared side is
  covered by `tests/effect_constraints.rs`, including hostile alias/hiding and
  subtraction cases and native/reference agreement. Remaining language limits:
  parameterized row aliases, first-class row values, row equality predicates,
  and user-defined effects.
- **Arithmetic proof search** is implemented in the separate erased arithmetic
  `{ ... }` fragment. Linear expressions (`c * x`, `x + y`, lengths) become
  integer linear inequalities; Fourier–Motzkin elimination over exact rationals
  produces a refutation certificate whose non-negative multipliers are checked
  independently by `facts::verify`. `tests/arithmetic_proofs.rs` covers
  coefficient scaling, multi-variable elimination, branch facts, integer
  strictness, native/reference agreement, nonlinear rejection, and stale-version
  rejection. Documented limits: no nonlinear terms, no cutting planes or full
  Presburger completeness, and explicit 64-term/4096-row/200000-pair budgets.
- **Mutable captures as a live view remain unimplemented and the runtime-proof
  backlog item stays unchecked.** A closure capture is still a sound copy /
  independent snapshot; live sharing would need a checked closure borrow
  lifetime so the environment cannot outlive the captured location.
  `tests/runtime_indices.rs` and `tests/advanced_types_effects.rs` keep the
  snapshot contract explicit.

Local Linux x86-64 validation used
`CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/close-rows-proofs` with
debug information disabled and two Cargo jobs:

- Full `cargo test -p kush --offline -j 2`: **968 passed, 0 failed** across 63
  test binaries (including the new `arithmetic_proofs` binary and three
  independent certificate-verifier unit tests).
- `cargo fmt --all -- --check`: passed.
- `cargo clippy -p kush --all-targets --offline -j 2 -- -D warnings`: passed.

The remote Boat gate for this checkpoint was not run from this checkout.

## Per-bit solver merge and handler-boundary review fixes

The row-alias/principal-row/proof-search merge retains the sixteen-bit declared
effect universe. It enumerates per-bit assignments for at most sixteen row
variables instead of multiplying whole-row subset counts, eliminating the
reported `u128` budget overflow. A regression covers eight full sixteen-bit
rows. Already-specialized variables are included when evaluating constraints.

Child tasks now inherit only the innermost contiguous suffix of copyable
noncapturing frames. An owned/one-shot frame blocks access to frames below it,
so a shadowed outer operation cannot become visible in a child. Tests cover
both blocked lookup and a valid copyable frame above the barrier in both
backends. Handler ownership comments and declared-effect diagnostics are
updated. Local mbx validation: 98 focused tests, formatting, all-targets Clippy
passed. The combined remote gate with later queued branches remains pending.

## Borrowing closure follow-up

Three commits on top of `15f62d3` broaden the borrowing contract:

- `f8f371b` stores borrowed records in `Box`/`Vec` containers with per-field
  element provenance. Construction, indexed reads, `push`/`set`/`clear`, box
  reads/takes, `&mut` container writes, containing records, direct calls, and
  indirect calls preserve every field's owner loan. Hostile cases cover owner
  replacement, block-local escapes, `&mut Vec<Holder>` writes, and clearing a
  vector before using a previously read element.
- `c043b22` infers anonymous intersection results when a body returns several
  distinct input lifetimes. Every source owner stays loaned, a caller may
  select the shortest provable actual lifetime, and inference now follows local
  destructuring bindings, nested record patterns, and simple aliases before
  choosing result sources. Explicit results receive the same inferred outlives
  edges, including through a destructured binding. The constraint closure is
  documented with its finite reachability decision procedure.
- `a017173` documents and tests the exact remaining boundaries: mutable owner
  borrows of temporaries, record fields, and index results; general
  `&record.field`; `&mut str`; and a child task returning a borrowed
  `TaskExit<T>`. `Task<TaskExit<...>>` now has a specific diagnostic instead of
  the generic container rejection.

None of these closes the two Borrowing backlog items completely, so both stay
unchecked. In particular item 1 still lacks mutable field/index/temporary
borrows and general field addresses, and item 2 still lacks principal
unification for recursive lifetime constraints, variance, and rows.

Local Linux x86-64 validation used
`CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/close-refs` with debug
information disabled and two Cargo jobs:

- Full `cargo test -p kush --offline -j 2`: **959 passed, 0 failed** across 62
  test binaries.
- `cargo fmt --all -- --check`: passed.
- `cargo clippy -p kush --all-targets --offline -j 2 -- -D warnings`: passed.

No Boat run or credential access was used for this checkout.

## Trait-object follow-up checkpoint

On top of `15f62d3`, the remaining dynamic-object work is implemented in:

- `adf5fb9`: traits whose only impls are generic/blanket impls are usable as
  `dyn`; parameter-dependent associated projections are fixed by the first
  registered member and later disagreement is rejected; `dyn` accepts `Nat`
  and `Grade` trait arguments.
- `787f846`: borrowed results may flow from caller-owned arguments through an
  owned receiver, and a temporary shared open object is bound to a hidden local
  so owning payloads are released exactly once.
- `e0bd1a8`: generic methods are monomorphized per dynamic call site into the
  member table, including method `Nat` arguments, explicit and inferred
  arguments, and members registered before or after the call site.
- `88efb0d`: shared dispatch on an owning projected field borrows that exact
  place in place (`pair.0.read()`, `self.inner.read()`), while consuming and
  mutable projected dispatch stay rejected.
- `ec175a3`: multi-trait `dyn A + B` syntax has an explicit language-diagnostic
  rejection.
- `74a0621`: a temporary receiver may return a view explicitly tied to another
  caller-owned argument; an elided or receiver-tied view is still rejected.

Local Linux x86-64 validation used
`CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/close-traits` with debug
information disabled and two Cargo jobs:

- Full `cargo test -p kush --offline -j 2`: **966 passed, 0 failed** across
  59 test binaries.
- `cargo fmt --all -- --check`: passed.
- `cargo clippy -p kush --all-targets --offline -j 2 -- -D warnings`: passed.

The trait-object backlog item stays unchecked. Remaining explicit boundaries
are receiver-tied borrowed results through owned or temporary receivers,
mutable/consuming dispatch on projected fields, a projection required before any
member of an object specialization is registered, multi-trait `dyn A + B`, and
effect-row trait parameters (which the trait grammar does not support at all).
See [traits.md](traits.md).

## DynArray and allocator remainder checkpoint

This checkout implements the remaining executable DynArray and allocator
features on top of `15f62d3`:

- `DynArray` now has exclusive `&mut [T]` views over the live prefix (with
  `Slice.set` write-through and exclusive-loan rules), views through a direct
  local record's `DynArray` field including nested fields, elementwise
  `==`/`!=` for one-word comparable elements, and length-checked patterns with
  a trailing `..`/`..name` tail binding. A pattern match over a runtime length
  must end in an unguarded catch-all; a suffix after `..`, owning/linear/view
  element bindings, and reference-based record places remain explicit,
  tested rejections.
- User allocators gain an optional checked growth hook
  (`Allocator.with_realloc`) used by `AllocVec` growth, plus fallible
  `AllocVec.try_push` (refusal returns the unchanged vector and untouched
  element) and `AllocVec.pop` for copyable elements. The growth hook consumes
  the previous block and observes its live byte count; a short returned block
  panics rather than losing vector state.
- Runtime `[T; n]` remains an explicit diagnostic; `DynArray` capacity is still
  a compile-time `Nat`. No user `Allocator` trait, instance-carrying allocator,
  container allocator parameter, FFI/raw-pointer callback, or per-element free
  was added. The custom-allocator item therefore remains partial.

Local Linux x86-64 validation used
`CARGO_TARGET_DIR=/home/hirew/Projects/kush/target/close-dynarray` with debug
information disabled and two Cargo jobs:

- Full `cargo test -p kush --offline -j 2`: **961 passed, 0 failed**.
- `cargo fmt --all -- --check`: passed.
- `cargo clippy -p kush --all-targets --offline -j 2 -- -D warnings`: passed.

New coverage lives in `crates/kush/tests/advanced_types_effects.rs` (mutable
and field views, equality, patterns, hostile aliasing/move/drop/out-of-range
cases, native/reference agreement and balanced cleanup) and
`crates/kush/tests/allocator_containers.rs` (growth hook, fallible refusal with
state and owning-element preservation, `pop`, and hostile hook signatures,
effects, and short blocks). The remote Boat gate was not run from this
checkout.

## Combined queued-branch integration

The row/proof, borrowed-record container/lifetime, generic dynamic method, and
DynArray/allocator follow-ups are merged together after the `f6e5405` evaluator
stack fix. Shared projected receivers retain checked owner loans; mutable and
consuming projected dispatch remain rejected. Dynamic-method effect arguments
use the full sixteen-bit row representation.

The allocator merge also visits the realloc callback expression in native
analyses, preserving literals and initializer cleanup. Reference evaluation
stores the optional growth hook as `Option<usize>` so function index zero is a
valid callback rather than a no-hook sentinel. Positive/refusal, initializer,
first-declared-hook, DynArray, and JSON suites pass in both backends (95 focused
tests). Full local and Boat combined validation is pending. Each feature's
remaining explicit boundaries above remain outstanding.

## Realloc payload integrity correction

An adversarial hook returning zero-filled replacement storage exposed a
reference/native mismatch: reference elements survived, while native owning
handles were corrupted and native execution aborted. The compiler now retains
the typed payload privately across a hook, presents zeroed readable old bytes,
and restores live elements into the validated returned block. The hook manages
storage rather than typed representations. Reference callback byte views are
also zeroed even when the original allocation callback filled its buffer.
Regressions verify scalar preservation, owning cleanup, and callback opacity
in both backends. The two stale invalid-effect diagnostic expectations from the
combined local run were updated; both affected suites pass (33 tests). A new
full combined local/Boat gate is pending for this correction.

## Queued merges and allocator integrity local gate

Compiler checkpoint `9df5bb6` passes the full local workspace suite:
**1011 passed, 0 failed**. Formatting and all-targets Clippy with warnings denied
pass. Local builds used mbx exclusively in a standalone managed target directory
(`~/.cache/kush-mbx-integration`), with four test-build jobs after checking spare
capacity and two Clippy jobs. This gate includes the typed-payload growth-hook
regression and all queued borrowing, trait, row/proof, and DynArray branches.
The full Boat gate is pending. Unchecked backlog items remain unresolved.

## Addressable place references checkpoint

The remaining reference-place forms are implemented in `7680cf9` on top of `edb98f1`:

- `&place` / `&mut place` alias direct local bindings, nested and owning
  nominal-record fields, inline-array elements, `Vec<T>` elements, and hidden
  temporary owners. The reference evaluator stores a pinned root plus a typed
  word path; the native backend uses the real field/element address. Roots stay
  loaned until the reference's checked last use, and the whole owner remains an
  ancestor capability.
- Disjoint-field loans now include structurally distinct record fields and
  distinct constant element indices. A runtime index is conservative: all
  dynamic indices of one base conflict. An out-of-bounds index panics in both
  backends, and a statically out-of-range constant index is a check error.
- A temporary aggregate or owning handle is hoisted into a hidden local in the
  enclosing statement list. Its resource drops at block end, after every
  checked reference's last use, exactly once. Projected values are never copied
  into a reference, and the hidden owner is never duplicated.
- General `*p` reads copy only non-owning, non-linear referents. `*p = value`
  requires an exclusive reference and destroys an old affine payload once
  before storing the replacement; linear referents and owning handle
  replacement through `*p` are rejected in favor of their dedicated
  operations.
- A returned `&Field` may derive from a `&Record` parameter. The signature
  check uses a finite recursive field-reachability rule, and the ownership pass
  still proves the exact origin and mutability.
- Pinned local ownership resources now alias the live storage cell instead of a
  binding-time snapshot, so replacing an affine record or box payload through a
  reference is neither leaked nor double-dropped.

`&mut str` remains an explicit rejection. Text views are validated UTF-8, byte
positions are not scalar boundaries, and an unrestricted byte store can create
invalid UTF-8. A sound operation must replace a complete Unicode scalar with an
encoding of unchanged byte length (or re-encode and move the following bytes);
that operation is not part of the current text fragment.

Local Linux x86-64 validation used `~/.cache/kush-mbx-reference-places` with
debug information disabled and two jobs:

- Full locked workspace suite: **1014 passed, 0 failed**.
- `cargo fmt --all -- --check`: passed.
- All-targets Clippy with warnings denied: passed.

New coverage lives in `crates/kush/tests/borrowing_references.rs` (nested,
owning, array, vector, temporary, branch-selected place, returned-field,
affine-replacement, linear-replacement rejection, hostile alias/escape/bounds,
and native/reference cases) with updated expectations in `borrowed_methods.rs`
and `strings.rs`. The full Boat gate is parent-coordinated.
The broader lifetime-inference item stays unchecked: recursive lifetime
variables, record variance annotations, and row/lifetime unification remain
outside the grammar and are not silently guessed.
