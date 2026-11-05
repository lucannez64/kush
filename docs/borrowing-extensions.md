# Expanded borrowing contracts

Status: implemented checked contracts for borrowed records in callable
signatures and scoped captures, capture-derived borrowed results, borrowed
records in structured-task captures and task results, nested record-field
subviews, disjoint-field mutable loans, stored shared/exclusive reference
locals with explicit reborrow, reference escape/reborrow for records and owner
containers, shared reference fields and their projection through `&Record`,
reference element containers (including `&str` elements), reference-valued
arrows, borrowed `Task.scope` records and `TaskExit` values across
function/callable boundaries, mutable owner references with in-place container
writes, containers of borrowed records with per-field element provenance,
per-field body lifetime inference, inferred outlives bounds, multi-source
anonymous intersection results, destructuring-derived inference,
helper-call body inference, addressable place references (nested/owning record
fields, inline-array and vector indices, and hidden temporary owners), checked
`*p` reads and `*p = value` replacement, and returned field references rooted
in a `&Record` parameter. The reference evaluator and the Cranelift native
backend agree on every positive case in `tests/borrowing_extensions.rs`,
`tests/borrowing_references.rs`, and `tests/strings.rs`. This is an engineering
contract inside the existing capability model, not a formal soundness proof.

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
- A borrowed `Task.scope` result keeps the capture-result provenance of the
  scope closure. The conventional `TaskExit<T>` may cross a function or
  callable boundary when the payload's declared field lifetimes are supplied
  by the caller; matching it there rebinds the same per-field loans. A child
  task still cannot return a borrowed `TaskExit<T>`, and a lambda or task
  cannot hide a borrowed `TaskExit<T>` in its environment: match it in the
  scope that joined it before storing it in a closure or spawning a child.
- The conventional `TaskExit<T>` shape is the only enum allowed to carry a
  borrowed payload, and user code cannot construct one: only `Task.join`
  produces it.
- A cancelled child that has already computed a result drops that value in the
  worker. Owned metadata is released exactly once and borrowed slice
  descriptors are inert, so cancellation never frees caller-owned storage.
  Cancellation before completion drops the child frame and captured descriptors
  under the same rules.

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

## Addressable place references, indexing, and temporary owners

`&place` and `&mut place` may now name a direct local binding, a record-field
chain (including nested and owning fields), an inline-array element, or a
`Vec<T>` element. The reference aliases the root owner's storage; it is not a
copy of the projected value.

```rust
struct Inner { a: i64, b: i64 }
struct Outer { inner: Inner, note: i64 }

fn add(left: &mut i64, right: &mut i64) -> Unit ! {panic} {
    *left = *left + *right;
}

let mut outer = Outer { inner: Inner { a: 3, b: 4 }, note: 10 };
add(&mut outer.inner.a, &mut outer.inner.b);
let note = &outer.note;

let mut values: Vec<i64> = [1, 2, 3];
let element = &mut values[1];
*element = *element + 5;
```

- Field places carry the same structural identity as nested slice subviews.
  Two references to structurally disjoint fields or to distinct constant
  indices of one array/vector may be live in the same expression; the root
  binding stays an ancestor capability and cannot be moved, dropped, replaced,
  or passed while either loan can still be used. A runtime index is
  conservative: all dynamic indices of one base conflict.
- `&mut` requires a mutable root binding or an exclusive reference root. A
  shared root is never upgraded. A record with borrowed fields remains
  read-only for whole-record borrowing; owned metadata of such a record is not
  mutated through `&mut Record`.
- An owning field (`Box`, `Vec`, `Bytes`, `String`) is referenced through the
  same allocation handle as a direct `&mut` borrow, so `Box.set`, `Vec.push`,
  `Vec.set`, and the read builtins keep working through the projected
  reference. Moving or dropping the root while that reference is live is
  rejected.
- Nested record references are projected in place: `&mut outer.inner` is an
  exclusive reference to the inline inner record, and a later `r.a = ...` writes
  the parent's storage. Reading a field of a `&Record` parameter and returning
  it as `&Field` is accepted when the parameter's declared lifetime outlives
  the result (the finite, non-recursive `reference_reaches_type` rule).
- Every runtime index is checked once when the reference is created; an
  out-of-bounds index panics in both backends. The owner is loaned until the
  reference's checked last use, so a later vector growth cannot invalidate the
  element address.
- A temporary aggregate or owning handle used as the borrowed place is given
  hidden backing storage declared in the enclosing lexical block, but its
  initializer runs at the operand's source evaluation point: inside an
  argument list, a short-circuit operand, a branch, or a loop condition. The
  declaration only reserves storage; initialization is tracked at runtime, so
  a skipped operand never evaluates or drops it. Re-evaluating one loop
  iteration's temporary releases the previous value before storing the new
  one. The hidden owner is dropped at block end after every checked
  reference's last use, or earlier on break/continue/return/panic, exactly
  once. A projection is never turned into a copied reference, and the hidden
  owner is never duplicated.

### Dereference reads and writes

A checked `*p` read copies only a non-owning, non-linear referent; copying an
owning payload or a linear obligation is rejected. `*p = value` requires an
exclusive reference and replaces the referent once: an old affine payload is
destroyed before the new value is stored, while a linear referent is rejected.
Owning handles keep their dedicated operations (`Box.set`/`Box.reuse`,
`Vec.push`/`Vec.set`/`Vec.clear`) rather than reinterpreting a handle word as a
payload.

### Mutable text boundary

`&mut str` remains rejected at declaration. The exact design issue is that a
text view is validated UTF-8 and byte positions are not scalar boundaries; an
unrestricted byte write could create invalid UTF-8. A sound `&mut str` needs an
operation that replaces one whole Unicode scalar with another whose UTF-8
encoding has the same byte length (or a validated re-encoding that moves the
view), not a raw byte store. That operation is not part of the current text
fragment.

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
  text-view type. Exclusive owner references (`&mut Box`, `&mut Vec`, `&mut
  Bytes`, `&mut String`) may also be stored and returned from a matching
  `&mut` parameter; a shared source is never upgraded.
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
## Reference fields in records

A nominal record may store a direct shared or exclusive reference field:

```rust
struct Holder<'a> { point: &'a Point, note: i64 }
struct MutHolder<'a> { point: &'a mut Point, note: i64 }
```

- Every reference field must name a declared record lifetime directly. A
  reference supplied only through an alias or generic substitution has no
  field provenance and is rejected.
- Construction checks the source's actual lifetime against the declared field
  lifetime, and rejects a shared source for an exclusive field. A `&mut`
  reference field is affine and must be destructured before use; projecting it
  as a value is rejected rather than duplicating the exclusive capability.
- Projecting a reference field from an owning record yields a checked
  reference whose loan retains the field's origins, mutability, and split
  labels. Nested records and reference containers extend the same per-field
  path. A shared reference field, shared slice field, or `&str` field may also
  be read through `&Record`; the projection aliases the record's stored
  pointer and keeps the pointed-to owner loaned. Exclusive reference fields
  and mutable slice fields are still rejected through a shared record
  reference rather than copying an exclusive capability.
- Reference fields participate in record construction, destructuring, helper
  returns, callable parameters/results, and task captures exactly like slice
  fields. Mixed owning metadata is dropped once; the reference descriptor is
  inert.

## Reference element containers

`Box<&'a T>`, `Box<&'a mut T>`, `Vec<&'a T>`, `Box<&'a str>`, and
`Vec<&'a str>` may store a direct reference or text element. A reference
element carries a checker-only lifetime annotation (`Type::Annotated`) with the
same runtime representation as the element; the annotation never appears in a
user-visible expression type. Text elements keep their four-word view
representation while their declared lifetime travels in the same annotation.

- `Box.new`, `Box.read`, `Box.take`, vector literals, `Vec.get`, and `Vec.at`
  preserve the element leaf. Reading a shared reference is a copy; an
  exclusive element cannot be copied out (`Box.read` rejects it) and must be
  moved with `Box.take`. Vectors admit only shared elements because a vector
  read copies.
- A container element may itself be a nominal borrowed record
  (`Vec<Holder<'a>>` and `Box<Holder<'a>>`). Every borrowed field of the record
  is a separate element leaf addressed relative to the element, so construction,
  `Vec.get`/`Vec.at`, `Vec.push`/`Vec.set`, `Vec.clear`, `Box.new`/`Box.read`/
  `Box.take`, `Box.set` through `&mut`, records containing the container, and
  direct or indirect calls all preserve the owners behind those fields. A
  borrowed record element must satisfy each declared field lifetime exactly like
  a record value. `AllocBox`/`AllocVec` continue to reject every borrowed
  element because their allocator-owned storage carries no element provenance.
- Container provenance is tracked exactly like a record's per-field
  provenance: the owner stays loaned while the container or a read element is
  live, and replacing or dropping the owner is rejected. For a borrowed-record
  element the leaves are relative field paths; for a direct reference or text
  element they collapse to the element root.
- A borrowed record or reference container returned by `loop { break value; }`
  retains the provenance of every possible break result, including nested loops
  and assignment. Break results cannot borrow storage declared inside the loop.
  Each break snapshots its leaves before later branch checking changes local
  metadata.
- Direct `Box.set` replacement releases the previous element's owner loans from
  the box and installs the new element's leaves. A previously read element keeps
  its own independent loans; replacement cannot invalidate that element.
- Reference vectors retain the union of every possible element source after
  literals, `push`, and `set`; updating one index does not prove that an old
  source is absent from other indices. This is conservative: source loans end
  after `clear`, destruction, or the vector's checked last use, rather than
  after a particular replacement. A read reference keeps its own source loan.
  Borrowed-record vectors use the same union, per field path.
- Fallible reserve of a reference vector remains rejected because general
  borrow-carrying `Result` payloads are unsupported; `Vec.reserve` preserves
  reference-vector provenance without a sum-type boundary.
- A record may store a reference container. Because owner references require a
  direct local receiver, destructure the container field into a local before
  borrowing it for `Box.read`/`Vec.get`.
- Containers may appear in function parameters/results and in arrows. The
  declared element lifetime travels in the callable's leaf list and is related
  to the caller's actual element provenance at every direct or indirect call.

## Mutable owner references and container writes

`&mut Box<T>`, `&mut Vec<T>`, `&mut Bytes`, and `&mut String` are checked owner
references with the same one-word runtime representation as their shared form:

```rust
fn replace<'a>(b: &mut Box<&'a Point>, p: &'a Point) -> Unit ! {panic} {
    Box.set(b, p);
}

fn add<'a>(v: &mut Vec<&'a Point>, p: &'a Point) -> Unit ! {alloc, panic} {
    Vec.push(v, p);
}
```

- `Box.read`, `Vec.len`/`get`/`at`, `Bytes.get`/`len`, and `String` read
  builtins accept a `&mut` receiver by reborrowing it shared for the call.
- `Box.set(reference, value)`, `Vec.push`, `Vec.set`, `Vec.clear`, and
  `Vec.reserve` accept `&mut` receivers and update the caller's allocation in
  place. Vector growth writes the new handle back into the caller's slot.
  `Box.set` replaces a reference or copyable payload only; an owning payload
  must be replaced with `Box.reuse` on an owned box.
- A reference written into a container whose element type declares a lifetime
  must outlive that lifetime. Writing `&'b T` into `Vec<&'a T>` requires a
  declared or inferred `'b: 'a` relation; using the same lifetime, or a bound,
  satisfies it. An unannotated local container keeps the union of its element
  sources instead.
- At a call, the callee may write any reference argument whose lifetime can
  flow into the container's declared element lifetime. The caller conservatively
  merges those loans into the container binding, so replacing, moving, or
  dropping a written owner after the call is rejected. A block-local owner
  written into a longer-lived outer container is rejected at block exit.
- `Vec.try_reserve` through `&mut`, `&mut str`, and mutable owner borrows of
  temporaries, fields, or index results remain explicit exclusions.

## Reference-valued callables

Arrow parameters and results may be `&'a T` / `&'a mut T` in addition to slice
views and borrowed records:

```rust
fn apply<'a>(f: fn<'b>(&'b Point) -> &'b Point ! {panic}, p: &'a Point) -> &'a Point ! {panic} {
    f(p)
}
```

- The arrow must bind every reference lifetime. A result needs a reference or
  borrowed-field source whose lifetime outlives it; an exclusive result needs
  an exclusive source. Named functions, lambdas, and stored callables obey the
  same contract, and indirect calls freshen the source provenance exactly like
  direct calls.
- A lambda may take reference, borrowed-record, reference-container, or
  borrowed-`TaskExit` parameters. A lambda may return a reference derived from
  one call parameter (or one borrowed field); returning a reference derived
  from a captured local remains a checked rejection.

## Borrowed scope results and TaskExit boundaries

`Task.scope` may return a borrowed record, and the conventional
`TaskExit<T>` may travel across function and callable boundaries:

```rust
fn make<'a>(window: Window<'a>) -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
    Task.scope(fn() -> TaskExit<Window<'a>> ! {alloc, panic, suspend} {
        Task.join(Task.spawn(fn() -> Window<'a> ! {panic, suspend} { window }))
    })
}
```

- A scope result keeps the scope closure's capture-result provenance. Its
  original storage stays loaned until the returned record or `TaskExit` value
  is consumed; block-local storage cannot escape.
- `TaskExit<T>` leaves are payload-relative, so matching `Completed(value)`
  rebinds the same per-field origins in the caller. Passing the value through a
  helper or callable keeps those origins live and still rejects replacing the
  owner while the joined value is used.
- A child task still cannot return a borrowed `TaskExit<T>`, and a lambda or
  task cannot hide a borrowed `TaskExit<T>` in its environment: match it in the
  scope that joined it before capturing it.
- `Task.scope` cannot return a reference element container directly; return
  the borrowed record it was built from, or keep the container lexical.

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
  function body is inspected for returned values rooted in parameters or in
  local bindings derived from them. A direct name, field projection (including
  nested field paths), slice of one parameter, or a destructuring binding
  resolves the result. A multi-lifetime record therefore supports per-field
  inference: returning `two.first` selects `'a` even when the same record also
  carries `'b`.
- When the body can return borrows from several distinct input lifetimes, the
  result receives a fresh anonymous internal lifetime that is outlived by every
  contributing source. The result is therefore an intersection/shortest
  contract: every source owner stays loaned through the result's last use, the
  result cannot be named as a caller lifetime, and a call site selects the
  shortest provable actual lifetime when it can prove an order (`'b: 'a`) and
  otherwise keeps the anonymous identity. This is conservative but sound: no
  branch source is forgotten.
- Local `let` destructuring and simple aliases propagate a parameter or field
  lifetime to the new binding before result inference runs. `let Pair { left,
  right } = pair;` and nested `let Outer { inner } = outer; let Inner { left,
  right } = inner;` therefore contribute `'a` and `'b` exactly like direct
  field projections. A binding with no unique candidate contributes nothing,
  so an unrecognized path still reports an explicit annotation error rather
  than guessing.
- A body that returns a helper call follows the helper's declared result
  source: an explicit result lifetime selects the helper parameter carrying
  that lifetime, and an elided helper result must have one unambiguous input
  borrow. The corresponding caller argument is inspected recursively, so
  `fn alias(a: &[T], b: &[T]) -> &[T] { tail(a) }` infers the result from `a`.
- When an explicit result lifetime is not already related to a returned direct
  parameter borrow, the function's outlives bounds are inferred (`source:
  result`) and closed transitively. Calling such a function requires the same
  relation between the caller's actual lifetimes; validation reuses the normal
  call-site outlives check. Inference through local destructuring bindings now
  feeds this same path, so `let child = &mut b[1..]; child` infers `'b: 'a` for
  an explicit `'a` result instead of requiring a source rewrite. Selecting a
  different field lifetime of a multi-lifetime record still requires an
  explicit bound, and a result lifetime longer than the returned source is
  rejected rather than inferred.
- No variance annotations, no recursive row/lifetime unification, and no
  inference through arbitrary function-returning-local chains. A value returned
  through an unsupported binding still needs an explicit bound or annotation.

## Lifetime constraints and decidability

Result inference is a finite constraint closure over the lifetimes declared by
one function:

- Each returned value contributes a source constraint `source outlives
  result`. Record element results contribute one constraint per declared leaf.
- An explicit result lifetime receives only constraints from a parameter's own
  declared lifetime. An elided multi-source result receives constraints from
  every contributing parameter or record-field lifetime and is represented by
  an internal anonymous lifetime.
- Constraints are edges in a directed graph `(longer, shorter)`. The checker
  closes the graph transitively and rejects a constraint that would invert an
  already-declared edge (`result outlives source`), so a longer source can never
  be relabelled as a shorter result.
- The decision procedure is a reachability query on at most the number of
  declared lifetimes of that function. There are no lifetime variables
  generated after signature lowering, no row variables, and no recursive types,
  so closure terminates and each call-site proof is a finite reachability
  check. Ambiguous or unprovable relations fail closed with an explicit error.
- This is not a principal unification algorithm for arbitrary recursive
  lifetime constraints, variance, higher-kinded rows, or interprocedural
  constraint solving. Those remain outside the subset.

### Slice-view element places

`&s[i]` and `&mut s[i]` address one element of a slice view `s`, including
through a field of a record element (`&mut s[i].y`). The view may be a local,
a parameter, or one side of a `Slice.split_at_mut` pair, over an inline array,
a `DynArray`, a record's `DynArray` field, or a `Vec<T>`.

```rust
fn last_mut<'a>(s: &'a mut [i64]) -> &'a mut i64 ! {panic} {
    let n = Slice.len(s);
    &mut s[n - 1]
}

let mut xs: [i64; 3] = [1, 2, 3];
let view: &mut [i64] = &mut xs[..];
let (left, right) = Slice.split_at_mut(view, 1);
let p = &mut left[0];
let q = &mut right[1];      // the opposite split side: no conflict
*p = *p + *q;
```

- **Loans.** An element reference narrows the view's capability exactly like
  a subview. It roots at the view's owners, not at the view binding, so the
  owner stays loaned until the element reference's checked last use, even
  after the view binding is dead or out of scope. It keeps the view's
  `split_at_mut` side, so references into opposite sides coexist while two
  references into one view (or one side) are aliasing errors, as is using the
  view while an exclusive element reference is live.
- **Mutability.** `&mut s[i]` needs an exclusive `&mut [T]` view; a shared
  view is never upgraded. Owning, linear, view, and reference elements are
  rejected.
- **Results.** A `&'a [T]` or `&'a mut [T]` parameter backs a returned `&'a T`
  or `&'a mut T` (or a reference to a field inside the element). A shared view
  cannot back an exclusive result, and a local view's element cannot escape
  the frame.
- **Runtime checks.** The index is checked against the view's runtime length
  when the reference is created, so the operation needs `panic`. A `&[i64]`
  over `Bytes` has byte-sized elements and no word-sized element address;
  creating an element reference into one panics in both backends.
- **Representation.** Native code computes `data + index * stride` from the
  view descriptor. The reference evaluator keeps the view and the index and
  reads or writes through the view's own storage, so writes are visible to the
  owner in both backends.

## Remaining deliberate limits

- `&mut str` and `Vec.try_reserve` through `&mut Vec<T>` remain outside the
  subset; each is an explicit, tested rejection. Two element references into
  one view conflict even at distinct constant indices. `&mut Bytes`/`&mut String` provide read access but no mutating
  builtins. Temporary owners, record fields, and array/vector indices are
  supported through hidden storage or real element addresses as described
  above. A record with borrowed fields is still not mutated as a whole.
- A child task cannot return a borrowed `TaskExit<T>` (rejected when the
  `Task<TaskExit<...>>` result type is formed), and a lambda or task cannot
  capture a borrowed `TaskExit<T>` in its environment. Match it in the scope
  that joined it before hiding it in a callable or child task.
- `&record.field` is supported for copyable, owning, and nested record fields.
  Shared reference, shared slice, and text fields remain readable through
  `&Record`; a slice field is sub-sliced with `&record.view[..]` or `&mut
  record.view[..]`, and one element of it is addressed with `&s[i]` (see
  above). A place reference into a container element whose type owns storage
  remains an explicit rejection.
  Outlives bounds are not part of a record declaration, so a projected
  reference borrows the whole record binding.
- Containers of borrowed records are supported for `Box` and `Vec`; `AllocBox`
  and `AllocVec` reject every borrowed element because their allocator-owned
  storage has no per-element provenance. Inline arrays of borrowed records
  remain rejected.
- Disjoint-field reasoning is structural and path-based, not a general range or
  alias algebra. Merged record values lose field identity.
- Capture-result lambdas cannot mix environment and parameter origins, and
  cannot be coerced or passed on unless the target contract is exactly
  compatible.
- Result inference is a finite constraint closure over one function's declared
  lifetimes, not principal unification for recursive lifetime constraints,
  variance, or row variables.
- The analysis remains path-insensitive and conservative. Both backends and
  the runtime are trusted implementation components.

## Review fixes and scope slice results

A slice returned from `Task.scope` retains the scope closure's capture-result
provenance. Its original storage remains borrowed through the returned view's
last use, and block-local storage cannot escape. Borrowed-record scope results
and borrowed `TaskExit` values across function boundaries keep the same
per-leaf provenance and are checked until their last use.

A borrowed `TaskExit<T>` cannot be hidden in a closure/task environment: match
it within the joining scope. Reading a stored reference for a field access is
a reborrow, while passing it as a call argument retains the child loan through
later argument evaluation. Multiple shared arguments are allowed; overlapping
exclusive arguments, including two uses of one stored `&mut`, are rejected.
These rules have dedicated native/reference and rejection regressions in
`tests/borrowing_safety.rs`.
