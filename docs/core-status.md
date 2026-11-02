# Core implementation status

This page records the implemented programming-language core and its validation.
It is not a claim of complete v0.1 conformance, a formal soundness proof, or
memory/performance superiority over Rust.

| Area | Implemented |
| --- | --- |
| Modules | Imports, visibility, cross-file spans, embedded library modules |
| Generic data/functions | Type, natural-const, grade and effect specialization; nominal records/enums; transparent aliases |
| Collections | Owning vectors and bytes, const-length inline arrays, shared and exclusive slice views |
| Basic values | Checked `i8`/`i16`/`i32`/`i64`/`u8`/`u16`/`u32`/`u64` arithmetic and explicit conversions, Unicode `Char`, inline tuples of 2–16 elements with positional projection/destructuring, validated UTF-8 `String` over owning buffers, immutable borrowed `&str` text views with checked byte-offset substrings, builtin method spellings, and statically dispatched user-defined inherent/trait methods, generic traits with explicit type/`Nat`/`Grade` specializations, generic methods, inherited default method bodies, and compile-time bounded-generic obligations |
| Control flow | Exhaustive matching, guards, loops, early returns, Result propagation |
| Dependent core | Universes, dependent functions, equality/transport/J, positive indexed logical data and elimination |
| Propositions | Impredicative Prop, proof irrelevance with restricted elimination, constructor-local indices |
| Runtime bridge | Checked erased evidence, dependent erased binders, immutable scalar indices, kernel-normalized const lengths |
| Usage grades | Natural/many usage, grade arithmetic and specialization, exact branch/loop/call checking, owning `@[1]` result-transfer contracts and copyable must-use `@[1]` result contracts (static metadata, no runtime representation) |
| Subtyping | Normalized heterogeneous unions/intersections, coherent coercions, exhaustive narrowing, effect/grade-aware arrows |
| Higher-order code | Function values, typed lambdas, affine/linear once closures, scoped borrowed-capture once closures, effect-polymorphic calls |
| Memory/backend | Affine/linear checking, deterministic cleanup, checked box reuse, allocation-preserving in-place vector transforms, conservative pure-map fusion, independent evaluator, Cranelift native Linux x86-64 |
| Borrowing/lifetimes | Explicit `'a` signatures with conservative single-input slice-result elision, explicit checked function outlives bounds (`<'long: 'short, 'short>`) for shared/mutable slice and borrowed-record returns, lifetime-aware callable types (`fn<'a>(&'a [T]) -> &'a [T]`) with checked substitution and call-through-value provenance, shared and mutable borrowed slice returns, checked capability ancestry with parent suspension/restoration, mutable sub-views and retained reborrows, last-use loan release with loop/branch fixed points, exclusive `&mut [T]` views, `Slice.set`, fallible `Slice.try_get`, checked disjoint mutable splits with `Slice.split_at_mut`, lexical `once fn` closures capturing borrowed slice views, lifetime-parameterized records with shared `&'a [T]` or exclusive `&'a mut [T]` fields, checked mixed `Box`/`Vec`/`Bytes` metadata, per-field provenance, destructuring, shared copies, move-only exclusive fields and checked helper returns, plus call-scoped nominal-record `&self`/`&mut self` receivers and ordinary `&Record`/`&mut Record` parameters with copyable field reads, exclusive copyable-field writes, exact receiver/trait contracts and call-argument loan retention |
| Allocation diagnostics | Stable `--stats` stderr line for reference and native execution: allocations, deallocations, peak live, buffer growths, reuses, fusions |
| Structured async | `suspend` effect, `#[nosuspend]`, `Task.scope`/`spawn`/`yield`/`join`/`cancel`/`check_cancel`, owned once task bodies, typed `TaskExit<T>`, cooperative cancellation, deterministic native/reference scheduling, guarded stackful native tasks, scoped slice borrowing by scope bodies and child tasks |

## Integrated application

```sh
cargo run -p kush -- check examples/integrated-core.kush
cargo run -p kush -- eval examples/integrated-core.kush
cargo run -p kush -- run examples/integrated-core.kush
```

Both executions exit with status 42 (no printed output). The example combines
const-generic array aliases, slices and proved indexing, exact-use grades,
effect-polymorphic higher-order calls, a callable union, runtime-indexed erased
proofs, and a linear-once closure. Its regression checks that only the box and
closure environment allocate and that both allocations are released.

For a multi-file stdin application:

```sh
printf '(1 + 2) * -3\n' | cargo run -p kush -- run examples/calc.kush
# -9
```

Checked storage reuse and allocation diagnostics:

```sh
cargo run -p kush -- check examples/reuse.kush
cargo run -p kush -- eval examples/reuse.kush --stats
cargo run -p kush -- run examples/reuse.kush --stats
```

The example prints `100`, `4`, and `3`. `Box.reuse` retains one box allocation
across 100 updates, and `Vec.map_in_place` retains vector storage while
transforming elements. `--stats` writes one stable `allocation-stats:` line to
stderr without changing program stdout or exit status. See
[checked reuse and allocation diagnostics](reuse.md). These counters are
tooling observations, not source effects or proof facts.

## Integration review and regression fixes

Independent adversarial reviews found representation and obligation-transfer
bugs that ordinary feature tests had missed. Active regressions now cover:

- inserting element coercions in inferred generic array/function/record paths,
  including union tags and pure-to-once calling-convention adapters;
- checking linear availability at short-circuit, while and break joins,
  and preserving owning obligations across repeating loop back-edges;
- preserving owning obligations through loop results, `?`, destructuring,
  boxing/unboxing, reordered-record temporaries and closure captures;
- deriving capture signatures and synthetic capture-local obligations before
  lowering, with independent ownership validation afterward;
- graph-based linearity reachability through recursive/deep types rather than
  exponential recursive unfolding or a depth cutoff that could miss obligations;
- native/reference agreement, invalid-program rejection, and valid consumption
  paths for those boundaries.

The lifetime milestones add explicit shared and mutable slice returns,
conservative single-input slice-result lifetime elision, explicit checked
function outlives bounds such as `<'long: 'short, 'short>`, loop-aware last-use
loans, exclusive mutable slices, mutable sub-views,
retained-parent reborrows, checked disjoint mutable splits through the
restricted `let (left, right) = Slice.split_at_mut(view, mid);` form, and scoped
`once fn` closures that capture borrowed slice views. A borrowed capture is
accepted only as a direct `let` initializer or immediate callee; the resulting
local may only be called or implicitly dropped while its scope is live, so a
return, aggregate, box, union, generic call, adapter, or task cannot erase the
loan. Borrowed captures store view descriptors; dropping those descriptors
never frees the original array/`Vec`/`Bytes`. A mixed closure still owns and
cleans up its separate owning captures. Regression coverage includes immutable
and mutable captures, owner and parent conflicts, split-side closure siblings,
loop and branch reuse, nested closures, same-task suspension, native/reference
writes and allocation balance, and explicit rejection of every supported escape
position. Review
exposed argument evaluation holes: earlier slice arguments and builtin receivers must keep their owners
loaned while later arguments execute, and temporary views must obey the same
exclusivity rules as bound views. The checker now tracks capability ancestry, so
a child view derived from a parent is distinguishable from a competing alias:
the parent is suspended while the child is live and restored after the child's
last use. Regression coverage includes direct and indirect calls, nested
argument blocks, array/Vec/Bytes replacement, shared versus exclusive temporary
conflicts, disjoint-owner controls, nested builtin reborrows, mutable returned
subviews across branches/loops/tasks, checked split siblings across calls,
reborrows, nested splits, branches, loops, and same-task suspension,
native/reference agreement, allocation balance, and pinned-array
replacement/copy agreement between both backends.

Normal-exit checks also cover pending linear expression results: a later
argument cannot return, propagate `?`, or exit an enclosing loop while abandoning
an already-evaluated linear callee or earlier linear argument. A loop contained
entirely inside an argument may still finish normally. Affine cleanup remains
valid on these paths. See the [borrowing audit record](borrowing-audit.md).

The [borrowed pipeline example](../examples/borrowed-pipeline.kush) combines
elided returns, checked split siblings and borrowed closures over a byte buffer.
A closure callee remains loaned while its argument joins another task. The
reference evaluator and native executable both print `20`, `120`, and `7`.

A following record-reference milestone adds call-scoped `&self`/`&mut self`
methods, `self: &Self`/`self: &mut Self`, and ordinary `&Record`/`&mut Record`
function parameters. Only direct local owners are borrowed. Reads of scalar and
copyable fields work through shared and exclusive references; exclusive
references may replace copyable, non-owning fields. Stored, returned, captured,
projected, temporary, reborrowed-through-reference, borrowed-field, and
owning-field access remains explicitly rejected. See
[borrowed records](borrowed-records.md) and [static traits](traits.md).

The borrowed-record milestone adds `struct Window<'a, T> { view: &'a [T], ... }`
and exclusive `view: &'a mut [T]` fields with checked destructuring, shared
copies, move-only exclusive fields, helper returns, multiple distinct field
lifetimes, nested borrowed records, lifetime aliases, and mixed `Box`/`Vec`/
`Bytes` metadata that is moved and freed exactly once. Per-field provenance
survives calls and reordered record temporaries; shared fields cannot be
upgraded to mutable, and an exclusive field is extracted by destructuring first.
Stored views elsewhere, containers/unions/generic/callable/task escapes, linear
or stream/callable/union mixed metadata, and self-reference are rejected. See
[borrowed and mixed records](borrowed-records.md).

These tests and reviews do not establish the absence of all bugs. The kernel,
compiler, C runtime support and toolchain remain trusted implementations.

The mutable/mixed borrowed-record milestone passes 466 automated tests,
formatting and Clippy on Boat (the preceding shared-record milestone passed 449
and the preceding borrowing milestone passed 431). Separate sampled reviews
cover elision identities, split-side provenance, borrowed closure argument loans,
pending-linear exits and fallible slice access. The source and documentation
remain uncommitted for review.

The float milestone adds IEEE-754 `f32`/`f64` values with one-word
bit-preserving storage, IEEE arithmetic and comparisons, explicit checked
conversions, and shortest round-trip printing that agree between the reference
evaluator and the native C runtime. Floats remain opaque to the erased-proof
kernel, whose symbolic carriers stay `i64`, `Bool`, and `Unit`. The preceding
basic-values milestone (fixed-width integers and conversions, `Char`, tuples,
checked UTF-8 `String`, and builtin method syntax) passed 529 tests.

The borrowed-text milestone adds a distinct immutable `&str` view over validated
`String` storage: zero-allocation `String.as_str`, checked byte-offset
substrings (`String.substr`, `Str.substr`, and range syntax on an existing
`&str`), byte/scalar length and scalar access, and an explicit allocating
`Str.to_string`. Substrings check ordering, bounds, and UTF-8 scalar boundaries
and panic on failure in both backends. Views reuse the shared slice-view
capability machinery for owner loans, last-use release, nested subviews, helper
returns with explicit or elided lifetimes, explicit outlives bounds, and
later-argument loans. Text views are deliberately excluded from records,
tuples, arrays, `Vec`, `Box`, enums, unions, generic type parameters, closures,
tasks, and arrow types; `&mut str` is rejected. The full Boat run passes **551
automated tests**, formatting, and Clippy with warnings denied. See
[borrowed text views](borrowed-text.md).

The static trait/method milestone adds trait declarations with owned and
call-scoped borrowed nominal-record receivers, concrete `impl Trait for Type`
blocks, inherent `impl Type` methods, `Self` substitution, exact signature
checking (parameters, grades, erasure markers, result, lifetimes, and effects),
`T: Trait` bounds discharged at specialization time, deterministic
duplicate/ambiguity checks, cross-module `pub` methods, and explicit
`receiver.Trait.method(...)` qualification.

The generic-static-interface stage extends that subset with generic trait
declarations and specializations: `trait Convert<T>`, `impl Convert<i64> for
Point`, and bounds such as `T: Convert<i64>`. Trait identity is keyed by the
trait binding plus canonical checked type/Nat/Grade arguments, so one receiver
may implement several specializations and duplicate or ambiguous cases are
distinguished. Method impls are compared by capture-avoiding alpha-equivalence
of method generics and lifetimes, with `Self` and trait arguments substituted
without capture. Generic inherent and trait methods infer or accept explicit
arguments through the existing specialization machinery, preserve parameter
grades/effects/erasure/lifetimes, and enforce method bounds even in unused
bodies. Borrowed `&self`/`&mut self` receivers keep their one-evaluation order
and loan retention; references still cannot pass through a generic parameter.
Calls lower to ordinary `Target::Function` calls, so the existing effect,
proof, ownership, and cleanup checks apply unchanged. There are no vtables,
trait objects, associated types, blanket impls, effect-row
trait parameters, or escaping/general reference receivers. The full Boat run
passes **602 tests**, formatting, and Clippy with warnings denied. See
[static traits and user-defined methods](traits.md).

The default-method extension lets a trait method declare a body. An impl that
omits the method inherits a fresh checked specialization per `(impl, method)`
pair: `Self` and the trait's type/`Nat`/`Grade`/effect arguments are substituted
into the default signature and body, the receiver is re-validated against the
concrete impl target, and the body is checked with the ordinary effect, grade,
ownership, lifetime, and proof rules. Inherited defaults join the same static
dispatch and ambiguity tables as explicit impl methods, and an empty
`impl Trait for Type { }` is accepted when every required method has a default.
An override still must match the trait signature exactly; there is no
specialization, no `default fn` modifier, and no associated items. Inside a
default body, an unqualified call on `Self` prefers the enclosing trait
specialization so sibling defaults remain callable for a generic trait with
several specializations. Inherited defaults follow the trait declaration's
visibility. The source, thirteen integration tests, a runnable example, and
these documents are implemented locally and **not yet validated by a full Boat
run**; the new tests pass locally on Linux x86-64 in both the reference
evaluator and the Cranelift backend, but the workspace-wide
formatting/Clippy/test gate is still outstanding.

The linear-resource milestone adds explicit `@[1]` result contracts for owning,
intrinsically linear, and copyable results. An owning contract transfers a
resource obligation; a copyable contract transfers a must-use observation
obligation. The contracts are threaded through named and generic functions,
typed lambdas, callable arrow types and aliases, static trait and method
signatures, indirect calls, checked adapters, `let` aliases, assignment,
branches, loop back-edge fixed points and break results, `?` owning success
payloads, constructors and destructuring, `Box.new`/`Box.take`/`Box.reuse`, and
linear-once captures. Arrow subtyping requires an exact result-grade match.
Ungraded results no longer silently make a binding-based `@[1]` owner affine;
the former acceptance is replaced by an explicit diagnostic and graded
replacement tests. Task and scope results that would carry a linear obligation
stay rejected. The grade is static metadata erased at runtime: payload types,
allocation counts, and the ABI are unchanged. General result-grade inference, custom
grade semirings, grade-zero erasure, and
cancellation-time linear cleanup remain future work. The full Boat run passes
**618 tests**, formatting, and Clippy with warnings denied; the new
`examples/linear-resources.kush` prints `20`, `21`, `21`, `7`, and `42` and
exits with status 0 in both backends. See [usage grades](grades.md) and
[owned resources](ownership.md).

## Deliberate current boundaries

See [kernel](kernel.md), [propositions](propositions.md),
[runtime indices](runtime-indices.md), [dependent indices](dependent-indices.md),
[grades](grades.md), [subtyping](subtyping.md), [functions](functions.md),
[slices](slices.md), [basic values](basic-values.md), and
[borrowing/lifetimes](lifetimes.md) for the full rules
and rejected cases.

The basic-value layer is implemented for fixed-width machine integers, `Char`,
tuples, validated UTF-8 `String`, and IEEE-754 `f32`/`f64`, with receiver-style
spellings for the existing builtin operations. Floats have one-word
bit-preserving storage, IEEE arithmetic/comparisons, explicit checked
conversions, and shortest round-trip printing in both backends; the exact
contracts and limits are recorded in [basic-values.md](basic-values.md).
Tuples are 2–16 inline elements and do not store borrows, borrowed records, or
task handles. Strings have no byte slicing; borrowed `&str` views and checked
byte-offset substrings are available but stay immutable and outside aggregates,
closures, tasks, generics, and arrow types. Byte and scalar access stay
explicit, and there is no fallible substring API, text equality, or text
search/iteration protocol.

Important boundaries include first-order positive logical recursion, immutable
scalar-only runtime logical indices, const-sized inline storage, explicit
lifetime annotations with conservative slice-result elision and checked
function outlives bounds but no general inference, call-scoped owner-reference
borrows,
borrowed and mixed records restricted to declared-lifetime slice fields plus
ordinary non-linear owning metadata (no container/union/callable/task storage,
direct exclusive/owned field moves, or linear/stream metadata),
borrowed captures restricted to nonescaping scoped `once fn` closures,
no general disjoint-range inference beyond checked `Slice.split_at_mut` pairs,
nominal records, explicit
specialization when inference is ambiguous, and
no overload representation for incomparable callable intersections.
Explicit `@[1]` result contracts are implemented for owning and intrinsically
linear results: a factory or transfer function hands a linear obligation to its
caller, and an ungraded result can no longer make a binding-based `@[1]` owner
affine. Result grades are static metadata erased at runtime, are threaded
through generic functions, lambdas, arrow types, trait/method contracts,
indirect calls, aliases, and adapters, and are matched exactly by subtyping.
Only `@[1]` is supported: `@[0]`, `> 1`, `many`, and abstract result grades without
a concrete specialization remain rejected on both owning and copyable results.
Copyable `@[1]` results are must-use observations, not owning moves. Custom grade
algebras, general grade inference, grade-zero erasure, and cancellation-time linear
cleanup are not implemented. Task results that would carry a linear obligation
remain rejected.

LLVM, general filesystem/FFI APIs, general automatic effectful fusion, widening reuse, nonblocking task I/O, forced cancellation unwinding, benchmarked
performance superiority, and kernel/embedded targets remain future work. The
implemented reuse fragment is explicit and checked; see [reuse.md](reuse.md).
The task system is cooperative on one OS thread; see
[async.md](async.md) for its exact scheduling, cancellation, ownership, and
allocation boundaries.


The dependency-first streaming foundation adds `Bytes.clear` and bounded
`IO.read_chunk`. The `stream-copy.kush` example processes arbitrary total input
with a single reusable allocation and a checked noalloc/nosuspend loop. This
remains blocking standard-stream I/O. See [foundation roadmap](foundation-roadmap.md)
for the dependencies of filesystem, FFI and nonblocking I/O work.

## Expanded borrowing, effects, and memory reuse

Noncapturing lambdas can return a slice borrowed from their single slice input;
indirect calls retain the source lifetime and checked split metadata. Scoped
closures may also return a slice or borrowed record from exactly one captured
slice/record field, and function arrows now carry borrowed-record parameters
and results. Borrowed records may be captured by scope bodies and child tasks
when their leaves derive from storage outside the scope. Nested record-field
subviews and structurally disjoint mutable field loans are checked, as are
reference returns tied to reference parameters and stored shared/exclusive
reference locals with explicit reborrows. A child task may return a borrowed
record; `Task.join` carries per-field provenance through `TaskExit<T>`, and
cancellation drops owned metadata without touching borrowed storage. Reference
fields, reference containers, and reference-valued arrows remain rejected. See
[expanded borrowing contracts](borrowing-extensions.md).

[Effect-row exclusions](effect-constraints.md) permit concrete forbidden-effect
sets on executable function/method binders. Checked specializations enforce the
constraint, including inferred arguments and trait defaults. `noalloc` and
`nosuspend` permit only rows constrained to exclude their forbidden effect.
There are still no handlers, row subtraction, or general constraint solver.

[Vector reuse](vector-reuse.md) adds capacity-preserving `Vec.clear`, checked
`Vec.reserve`, and explicitly interleaved effectful map chains. Existing nested
maps retain their original observable order. [Native allocator pooling](allocator-pool.md)
reuses small blocks under a 1 MiB physical retention cap, with normal-exit drain
and unchanged logical allocation diagnostics. The pool adds 32 bytes of header
per allocation and has no benchmarked latency or memory superiority claim.

[Bounded result-grade inference](result-grade-inference.md) infers a bare,
result-only grade parameter as `1` from a checked expected arrow. Transparent
aliases can carry grade parameters in result positions. Composite grade
inference, direct-call grade inference, and grade-parameterized aliases in
parameter/storage positions remain rejected.

The integrated additions above passed the full corrected Boat gate: **681
tests**, formatting, and Clippy with warnings denied. Independent review of
implementation commit `29674d2` found no blocking defects in source inspection
and six focused native/reference probes. See the [milestone review](milestone-review.md)
for scope, evidence, and remaining boundaries.

The expanded-borrowing milestone adds borrowed records in callable parameters
and results, scoped capture-derived slice/record results, borrowed-record
captures in scope bodies and child tasks, nested field subviews, disjoint-field
mutable loans, record-reference escape/reborrow, and lifetime inference from
record leaves with explicit ambiguity rejection. Local validation on Linux
x86-64 passes **690 automated tests**, formatting, and Clippy with warnings
denied, including native/reference agreement for every positive case in
`tests/borrowing_extensions.rs`. This sub-milestone ran locally under the shared
Cargo cache; an integrated Boat gate remains for the parent milestone. See
[expanded borrowing contracts](borrowing-extensions.md).
