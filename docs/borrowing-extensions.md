# Expanded borrowing contracts

Status: implemented checked contracts for borrowed records in callable
signatures and scoped captures, capture-derived borrowed results, borrowed
records in structured-task captures and task results, nested record-field
subviews, disjoint-field mutable loans, stored shared/exclusive reference
locals with explicit reborrow, and reference escape/reborrow for records and
owner containers. The reference evaluator and the Cranelift native backend
agree on every positive case in `tests/borrowing_extensions.rs`. This is an
engineering contract inside the existing capability model, not a formal
soundness proof.

This page records the precise additions and the remaining deliberate limits.
See [borrowing and lifetimes](lifetimes.md),
[borrowed and mixed records](borrowed-records.md), and
[structured async](async.md) for the underlying rules.

## Borrowed records in callable signatures

Function arrow types may now contain a record with borrowed slice fields, both
by value and in the result:

```rust
struct Window<'a> { view: &'a [i64], start: i64 }

fn len<'a>(window: Window<'a>) -> i64 ! {panic} {
    Slice.len(window.view) - window.start
}

fn advance<'a>(window: Window<'a>) -> Window<'a> ! {} { window }

fn apply<'a>(f: fn<'b>(Window<'b>) -> i64 ! {panic}, w: Window<'a>) -> i64 ! {panic} {
    f(w)
}
```

- Every record-field lifetime in an arrow must be bound by that arrow. An
  arrow cannot mention an enclosing function's lifetime or an inferred local
  identity.
- `BorrowSig` now carries aligned per-parameter leaf lists and a result leaf
  list in addition to the slice fields. Canonicalization numbers lifetime
  names across slices and record leaves together, so one lifetime shared by a
  slice and a record field keeps one identity.
- Arrow subtyping requires the same leaf paths with implied outlives bounds.
  A result field that may flow from a parameter must map to a target parameter
  that outlives the target result. Exclusive result leaves require exclusive
  source leaves.
- Each indirect call freshens the arrow's record lifetimes from the actual
  argument value, exactly like a direct call. The argument record is built
  against its own inferred labels; the call boundary relates them to the
  arrow's declared labels. No lifetime annotation is trusted without that
  check.
- Owner references (`&Box`, `&Bytes`, `&Vec`, `&String`, `&Record`, `&mut
  Record`) and `&str` views remain outside arrow value types.

## Capture-derived results

A scoped `once fn` closure may return a borrowed slice or a borrowed record
whose storage comes from one of its captures:

```rust
let window = Window { view: &owner[..] };
let tail = fn() -> &[i64] ! {panic} { window.view[1..] };
let rest = tail();
```

- The result must have **exactly one** possible origin across call parameters,
  captured slice views, and captured record fields. Zero origins and several
  origins are rejected; the diagnostic asks for one explicit source.
- A capturing lambda may spell an explicit result lifetime when it selects one
  of its record fields or captured views. A noncapturing lambda keeps the
  conventional elision spelling.
- Parameter-derived and capture-derived results cannot be mixed or unified.
  A closure either returns a caller argument borrow or an environment borrow.
- The closure's callable contract records the source capture index and, for a
  record field, the field path (`BorrowSig::capture_result`). At the call the
  checker resolves that index against the capture's actual outer provenance
  and records the result's origins, split labels, mutability, and lifetime.
  The representation is checker-only; the closure environment still stores the
  existing inert descriptors.
- A capture-returning closure is scoped exactly like an ordinary
  borrowed-capture closure: it must be called immediately or through its exact
  local binding. It cannot be coerced to a plain arrow, returned, stored, or
  passed on.
- The child closure function is checked with a capture-lifetime label on each
  captured slice. Its own return check therefore proves that every returned
  view derives from a capture, not from a local or temporary.

## Borrowed records in structured tasks

A scope body may capture a borrowed record whose storage is owned outside the
scope, and a child may capture that record in turn:

```rust
let window = Window { view: &data[..], start: 1 };
Task.scope(fn() -> i64 ! {alloc, panic, suspend} {
    let t = Task.spawn(fn() -> i64 ! {panic, suspend} {
        Task.yield();
        Slice.get(window.view, window.start)
    });
    // ...
})
```

- The scope's final join outlives every child, so externally captured storage
  remains loaned for the rest of the scope.
- A record owned by the scope body itself (for example one built over a local
  array) cannot be lent to a child; the existing
  "captured from outside the scope" check now recognizes borrowed records as
  well as slice views.
- Lending a record leaf retains the record's owners for the rest of the scope,
  with the same split-side and mutability rules as lent slice views.
- A child may now return a borrowed record as `Task<T>`. The result leaves are
  resolved from the child's captured records exactly like a capture-derived
  closure result; the handle carries that provenance and `Task.join` transfers
  it to the `TaskExit<T>` value. Matching `TaskExit.Completed(record)` binds
  the same per-field loans, which stay checked until the record is consumed or
  dropped. The conventional `TaskExit<T>` shape is the only enum allowed to
  carry a borrowed payload, and user code cannot construct one: only
  `Task.join` produces it.
- A cancelled child that has already computed a result drops that value in the
  worker. Owned metadata is released exactly once and borrowed slice
  descriptors are inert, so cancellation never frees caller-owned storage.
  Cancellation before completion drops the child frame and captured descriptors
  under the same rules.
- `Task.scope` results still cannot be borrowed records or borrowed
  `TaskExit<T>` values, and a borrowed task result cannot cross a function or
  callable boundary. Match it and read the fields inside the scope.

## Nested record-field subviews

A shared or exclusive slice field may be sub-sliced through a projection chain
instead of destructuring the whole record:

```rust
struct Inner<'a> { view: &'a [i64] }
struct Outer<'a> { inner: Inner<'a>, note: i64 }

let outer = Outer { inner: Inner { view: &data[..] }, note: 1 };
let tail = outer.inner.view[2..];
```

- The root must still be a direct local owner (or a parameter); temporaries
  and call results are not place roots.
- The projection is a place, not a copied field value. The checker does not
  retain an aggregate temporary for it and does not create a second copy of an
  exclusive descriptor.
- The resulting view inherits the field leaf's origins, split labels, lifetime
  and mutability. Shared storage cannot be upgraded to `&mut [T]`.

## Disjoint-field loans

Borrowing two records fields of one local record is supported when their field
paths are structurally disjoint:

```rust
struct Pair<'a> { left: &'a mut [i64], right: &'a mut [i64] }

let pair = Pair { left: &mut a[..], right: &mut b[..] };
let left = &mut pair.left[..];
let right = &mut pair.right[..];
Slice.set(left, 0, 10);
Slice.set(right, 0, 30);
```

- A field loan carries a checker-only place identity `(record root, field
  path)`. Two places are disjoint only when neither path is a prefix of the
  other and the root is the same record binding.
- The record binding remains an ancestor capability: moving, dropping,
  replacing, or passing the whole record while any field view can still be
  used is rejected. Reading a structurally disjoint field remains allowed.
- Two subviews of the same field, or a field view and a whole-record
  capability, still conflict. The exemption is structural only; it does not
  infer disjoint ranges from arithmetic.
- A record returned from a helper re-anchors each leaf's place identity to the
  destination binding, so disjointness survives helper calls and branches only
  when the checker can still identify that binding. A merged or temporary
  record loses field identity and is treated conservatively.

## Reference storage, escape, and reborrow

`&Record` and `&mut Record` may now be stored in a local reference binding, and
the same escape contract extends to shared references to `Box`, `Vec`, `Bytes`,
and `String`:

```rust
fn identity<'a>(p: &'a Point) -> &'a Point ! {panic} { p }
fn relay<'a>(p: &'a Point) -> &'a Point ! {panic} { identity(p) }

fn bump<'a>(p: &'a mut Point) -> &'a mut Point ! {panic} {
    p.x = p.x + 1;
    p
}
```

- The result is elided only when exactly one input borrow lifetime exists, or
  written explicitly with an outlives bound; the usual "may shorten, never
  widen" rule applies.
- An exclusive `&mut Record` result requires an exclusive `&mut Record`
  parameter whose lifetime outlives the result. Shared storage is never
  upgraded.
- Shared `&Box<T>`, `&Bytes`, `&Vec<T>`, and `&String` results may be returned
  from a reference parameter to the same pointee type. `&str` remains a distinct
  text-view type, and exclusive owner borrows remain unsupported.
- Returning a reference to a local record, a field, a temporary, a by-value
  record parameter, or a record value is rejected with a dangling-borrow
  diagnostic. A stored reference is checked by its storage roots, not by the
  descriptor binding: reborrowing a caller reference is allowed, while
  reborrowing a stack local or a by-value parameter is not.
- The caller keeps the owner loaned while the returned reference is used. A
  reference result retains its origin through the enclosing full expression,
  including later arguments. The checker is conservative here: splitting the
  reference's last use inside one expression (for example `bump(&mut p).x +
  p.y`) is rejected; bind the read to a local first.
- A reference local has one static lifetime label and capability ancestry,
  including its underlying owner roots. Reading it is an implicit reborrow, so
  a stored `&mut` capability may be used more than once without being moved;
  moving or dropping the owner remains blocked until the reference's checked
  last use. Reference bindings themselves are immutable.
- `&*p` and `&mut *p` are explicit reborrows. They narrow an existing stored or
  parameter reference for the enclosing expression, cannot upgrade shared
  storage, and cannot be used to dereference a value that is not a reference.
  A bare `*p` dereference remains unsupported; use `p.field` for field reads.
- Reference fields in records, reference element containers (`Box<&T>`,
  `Vec<&T>`), and reference-valued arrow parameters/results remain rejected.
  General reference containers still need type-level leaf metadata and checks
  across generic coercions and every control-flow merge.

## Lifetime inference boundaries

The additions keep inference conservative and local to signatures and
captures:

- A function slice result may be elided when exactly one distinct input
  borrow lifetime exists. Borrowed record parameters now contribute one
  candidate per field lifetime, so a single record source is enough.
- An arrow slice result uses the same rule, now counting record leaves.
- A lambda/closure result uses parameters, captured slice views, and captured
  record fields as candidates. Ambiguous origins are rejected rather than
  unified.
- When an elided function result has several input-lifetime candidates, the
  function body is inspected for returned values rooted in a parameter. A
  direct name, field projection, or slice of one parameter resolves the result
  to that parameter's lifetime; block, `if`, and `match` value positions keep
  only the branches that produce the result. Return positions that mention
  several parameter lifetimes remain an explicit ambiguity error, and the
  ownership pass still checks every returned origin against the selected
  lifetime.
- No inferred outlives bounds, no variance annotations, and no general
  owner-reference inference. Body inference does not follow helper calls or
  infer a per-field lifetime from a record parameter with several leaf
  lifetimes; those still require explicit annotations or one shared lifetime.

## Remaining deliberate limits

- Reference fields in records, reference containers, and reference-returning
  function values remain rejected. Stored reference locals and explicit
  reborrows are supported as described above.
- A task result may carry a borrowed record, but a `Task.scope` result and any
  function/callable boundary carrying a borrowed `TaskExit<T>` remain rejected.
- No general `&Record.field` reference form. Field access is either a copyable
  field read, a slice-field subview, or whole-record reference parameter.
- Disjoint-field reasoning is structural and path-based, not a general range or
  alias algebra. Merged record values lose field identity.
- Capture-result lambdas cannot mix environment and parameter origins, and
  cannot be coerced or passed on.
- The analysis remains path-insensitive and conservative. Both backends and
  the runtime are trusted implementation components.
