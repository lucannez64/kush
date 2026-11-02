# Borrowing implementation and review record

This records the 2026-10-31 borrowing milestones and their validation. It is an
engineering audit record, not a soundness proof. The kernel, compiler, evaluator,
native lowering and runtime remain trusted implementations.

## Implemented contracts

- Immutable and mutable views retain their original array, vector or byte-buffer
  storage. View creation, reborrowing and splitting allocate no program storage.
- Borrowed helper results preserve caller provenance. Explicit lifetimes and
  conservative signature elision describe the same checked relationships.
- Local loans end at a checked last use. Loop back-edges use a fixed point;
  textual last occurrence alone cannot release a continuing loan.
- Child views suspend ancestors. Opposite sides of one checked
  `Slice.split_at_mut` group are the only disjoint sibling exemption.
- Scoped borrowed closures retain captured view loans through their callable
  lifetime and through evaluation of all call arguments. Their environments
  still allocate and must declare `alloc` and `panic`.
- Normal exits cannot abandon linear results already evaluated for an enclosing
  operation. Affine results retain their deterministic cleanup behavior.

The exact syntax and restrictions are in [lifetimes.md](lifetimes.md).

## Confirmed defects and fixes

The first review found that last-use liveness alone did not keep an earlier
slice argument loaned while later arguments evaluated. This admitted vector
reallocation and byte-buffer replacement followed by access through stale
descriptors. Related gaps allowed conflicting temporary mutable views and
replacement of copyable arrays during a temporary borrow.

The checker now retains typed temporary regions throughout argument evaluation,
including indirect calls and builtin index/value arguments. Array assignment
checks loans regardless of whether the array is copyable. The evaluator also
preserves a pinned array cell when a local is replaced or initialized again.

A later review found the analogous problem for a locally bound borrowed
closure used as a callee. The environment had already been evaluated, but local
liveness ended before later arguments. The checker now saves capture provenance
before consuming the callee and reinstates its temporary regions for every
argument. Both local callees and immediate lambdas are covered.

Review of mutable reborrows also found that a shared child froze mutable local
views but not mutable slice parameters. Capability suspension now applies to
both. A usability issue involving `Slice.len(view)` in the view's own subview
bounds was fixed with a metadata-only exception; moves, writes and rival views
in those bounds still fail checking.

A final cleanup probe found that a linear callee could be moved into a pending
call and then destroyed implicitly when an argument returned early. Pending
linear values now participate in normal-exit checking. Loop exits distinguish
temporaries created inside the loop from those belonging to an enclosing
operation that the loop will eventually complete.

## Independent probe coverage

Separate reviews exercised split group reuse, nested split ancestry, branch and
helper-result label intersections, parameter suspension, argument order,
temporary aliases, midpoint evaluation, byte/aggregate strides and empty sides.
They also exercised closure capture, forbidden escapes, early cleanup, same-task
suspension and signature elision.

The last independent audit ran 70 generated probes and 11 targeted follow-ups.
Accepted cases were compared between the reference evaluator and Cranelift
native execution for output, status and allocation balance. That audit found no
additional confirmed defect in its sample. This does not establish the absence
of other bugs or a formal safety theorem.

Repository regressions are in
[lifetimes.rs](../crates/kush/tests/lifetimes.rs). The
[borrowed pipeline](../examples/borrowed-pipeline.kush) integrates byte-buffer
mutation, elided helper returns, split siblings, borrowed closure callees and
task joining during argument evaluation.

A separate review of pending-linear cleanup ran 22 checks, including 13
accepted cases on both backends. Those controls covered affine cleanup, nested
loop exits, match-bound resources, linear callees held across task joins, and
pipeline cancellation. It found no additional confirmed defect in that sample.

## Borrowed shared-slice records

The next milestone added lifetime-parameterized records with shared `&'a [T]`
fields, per-field provenance, destructuring, copies, multiple distinct field
lifetimes, nested borrowed records and lifetime-aliased result types. Erased
lifetime arguments are a separate category from type/natural/grade/effect
arguments and add no runtime word, tag or allocation.

During implementation, three concrete blocking issues were found and fixed:

- block-tail loans were initially cleared for every non-slice value, which
  regressed an existing call-scoped `&Box` argument test. Blocks now retain loans
  for slice, borrowed-record, and owner-reference values and clear only genuinely
  non-borrowing tails;
- record literals with reordered fields are lowered through source-order
  temporaries; the checker now retains each earlier field's loan while later
  fields evaluate, so an owner cannot be replaced or dropped between two fields
  of one literal;
- a record-provenance pass assumed every `Construct` was a record and indexed
  variant zero. It now reads only record layouts, leaving ordinary enum
  construction unchanged.

Explicit field lifetimes are checked against the source view's lifetime; a field
from `'b` cannot be returned as `'a`, and a swapped record literal or a wrong
field projection is rejected. Call results union the origins of every argument
field carrying the selected callee lifetime, so a wrong output cannot borrow an
unrelated field. Compiler-inferred local/argument labels are kept only as
checker-only identities; they are never surface lifetimes.

The regression suite in [borrowed_records.rs](../crates/kush/tests/borrowed_records.rs)
covers construction, access, destructuring, copies, aliases, nested/generic
records, multiple lifetimes, helper results, Vec/Bytes/array owners, split
siblings, loops/branches, early `?`, same-task suspension, zero/allocation-balanced
execution, and native/reference agreement. At that shared-only milestone it also rejected
local-owner escapes, wrong/shuffled fields, owner replacement/drop in later
fields or arguments, mutable or owning mixed fields, container/union/enum/array
storage, generic type-parameter crossing, function-value parameters/results,
closures and task captures, and mutable upgrades of shared fields. The example is
[borrowed-records.kush](../examples/borrowed-records.kush).

## Mutable fields and mixed owning records

The next milestone added exclusive `&'a mut [T]` record fields and mixed
`Box`/`Vec`/`Bytes` metadata whose owned payload contains no borrow. A record
with any exclusive field is affine/move-only transitively, even when it owns no
heap storage. A shared-only record remains copyable. An exclusive field must be
extracted by destructuring first; direct projection is rejected so one exclusive
descriptor cannot be duplicated while the record is still available. Mixed
records move their owned fields exactly once, free only those fields, and pass
borrow provenance and ownership together across helper returns.

The checker now records per-leaf lifetime, mutability, origins and split labels.
Record parameters are checked for exclusive provenance at call and return
boundaries; an exclusive result must derive from an exclusive parameter or
exclusive record-field leaf. The aggregate record capability is exclusive when
any leaf is exclusive, so every owner behind a live mutable-field record stays
suspended until the record and its field aliases are dead.

During implementation two concrete issues were found and fixed:

- the reordered-literal temporary hold initially reserved the field view slot
  itself, which made moving that view into the record look like moving a
  still-borrowed value. The hold now reserves only the underlying owners and
  parents; the live temporary view still prevents a rival view;
- record results initially reset every leaf to shared, which would have hidden
  an exclusive call-result capability. Record call results now carry each leaf's
  mutability and reject an upgrade from a shared parameter.

The regression suite now covers mutable construction, helper returns, nested
records and aliases, move-only transitive affinity, direct-projection rejection,
field reborrows, owner suspension/restoration through later arguments and
constructor field order, split siblings stored in one record, mixed owning
`Box`/`Bytes`/`Vec` payloads, unused-record drop, reordered and partial
constructors, `?`/loop exits, same-task suspension, `noalloc` helpers,
self-reference, containers, and linear/stream metadata. Examples are
[mutable-borrowed-records.kush](../examples/mutable-borrowed-records.kush) and
[mixed-borrowed-records.kush](../examples/mixed-borrowed-records.kush).

## Remaining boundaries

Borrowed records support shared or exclusive slice fields plus ordinary owned
metadata that cannot hide a borrow. Direct exclusive/owned field moves remain
restricted to destructuring first. Storage in enums/unions/containers,
callable/task capture, generic type-parameter crossing, self-reference, linear
fields, streams, unions, callables and record field sub-slicing remain
unsupported. Other stored views, general lifetime-parameterized callables,
borrowed task captures, owner-reference returns, lifetime bounds and general
disjoint-range inference remain unsupported. Borrowed closures are restricted
lexical once-callables; they cannot be forwarded, returned, stored or moved to
another binding. Signature elision is deliberately conservative and does not
infer lifetimes by inspecting a function body.

All compilation, native execution and Cargo checks for these milestones ran on
Boat. Local source remains authoritative, remote source is hash-verified on
upload, and the sandbox is stopped after validation.

## Final automated validation

The final full Boat check for the mutable/mixed borrowed-record milestone
passed **466 tests**, `cargo fmt --check`, and Clippy with `-D warnings`. The
earlier borrowed-record milestone passed 449 tests and the earlier borrowing
milestone passed 431 tests. `Slice.try_get` adds effect-free bounds failure through the
conventional `Option<T>` type; direct record and union payload regressions verify
native layout and tag handling. The pure access operation adds no allocation,
suspension or panic effect, while its argument expressions retain their effects.

The integration pipeline prints `20`, `120`, and `7` on both backends. A
cooperative cancellation variant was independently probed and remained
allocation-balanced. Native and reference task infrastructure can report
different allocation totals; each must balance its own allocations and frees.

The final fallible-access review also compared standard-library `Option`,
reversed tags, aggregate and union payloads, maximum/negative/empty bounds,
index effects and mutable reborrows on both backends. A discovered global-name
lookup issue was fixed before that review: `Slice.try_get` now records the
lexically visible `Option` binding at name resolution and checks that exact
nominal enum shape. Private foreign declarations cannot supply the result type.
The review found no additional confirmed defect in its sampled cases.

The independent borrowed-record review ran 21 safe probes and 64 must-reject
probes, plus 118 focused baseline tests, and found no memory-safety defect in
that sample. It confirmed two conservative rejections: inline nested borrowed
record inference used declaration lifetime names, and destructuring retained a
temporary scrutinee loan for the entire remainder of the block. Both were fixed
and covered by positive and negative regressions. Explicit wrong-lifetime
construction still rejects; last-use release works for arrays, vectors and byte
buffers; destructuring in a later argument preserves the earlier argument's
loan. The final full suite after these fixes passed 449 tests, formatting and
Clippy on Boat. The later mutable/mixed milestone's full suite passed 461 tests,
formatting and Clippy.


## Mutable and mixed record review corrections

The independent review found a general owning-record projection bug: a
non-moving place read was registered as a temporary owner, so reading a scalar
or shared field could double-free an owned sibling, or free it before returning
the record. Place reads (`Peek` and nested place projections) now retain the
original local as the sole owner. Regression cases cover plain and mixed
records, nested projections, parameters, and projection followed by a record
return, with native/reference agreement and balanced allocations.

The same review identified three further gaps, now covered by regressions:
mutable slice results accept matching exclusive record-field leaves, final
`..` record patterns parse with checked omitted-field cleanup, and forbidden
metadata categories are rejected transitively through nominal aggregates and
owned wrappers. Shared-to-exclusive result upgrades remain rejected.

After these corrections, the full Boat run passed **466 tests**, formatting
and Clippy with `-D warnings`. These checks are regression evidence, not a
formal soundness proof.

## Borrowed nominal-record receivers and reference parameters

The call-scoped record-reference milestone added `&self`/`&mut self` receivers,
`self: &Self`/`self: &mut Self`, ordinary `&Record`/`&mut Record` parameters,
copyable field reads through both reference forms, and copyable non-owning
field replacement through exclusive references. The reference evaluator pins a
borrowed record local in a shared cell; the native backend pins nominal-record
locals to stack storage. A field write updates the same storage the caller
observes, and borrowing an owning record does not duplicate or free its owned
fields.

Implementation review found and fixed three concrete issues before the final
run:

- call-scoped `Borrow` nodes used to reset the temporary alias sets after their
  own expression, so a later argument could read an owner held by `&mut Record`.
  Exclusive and shared record loans now persist through the enclosing full
  expression and are restored only when that expression completes;
- destructuring or moving a record local after it had been promoted to a pinned
  cell evaluated the cell wrapper instead of the record value. Moves now
  materialize the pinned value, keeping reference and native behavior aligned;
- the new record-reference path initially changed an unrelated owner-reference
  diagnostic used by the existing bytes-method tests. Record-specific loan sets
  now carry the new restriction without changing non-record reference behavior.

The regression suite covers shared inspection and exclusive updates in both
backends, ordinary helper calls, owning-record cleanup and allocation balance,
nested copyable records and inline-array reads, linear-record borrowing,
trait receiver contract mismatches and explicit qualification, bounded generic
helpers, `#[noalloc]`/`#[nosuspend]` helpers, later-argument alias conflicts,
moves/drops/replacement/read conflicts, temporary/field/projection borrows,
stored-reference and return escapes, shared-write and shared-to-exclusive
upgrades, borrowed-field access, and exclusive-record method aliases.

This remains an engineering milestone, not a proof. It is not general `&T` /
`&mut T` support: references are call-scoped, only direct local nominal-record
owners are borrowed, stored/returned/captured/reborrowed references and
owning-field replacement stay rejected, and both backends and the runtime are
trusted. The full Boat run after this milestone passes **584 tests**,
`cargo fmt --check`, and Clippy with `-D warnings`.
