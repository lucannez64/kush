# Borrowing, lifetimes, and exclusive slice views

Status: implemented checked borrowing, mutable-view, disjoint-split,
scoped borrowed-closure-capture, conservative signature lifetime elision,
explicit function outlives bounds, and
lifetime-parameterized records with shared or exclusive slice fields and
checked mixed owning metadata for the executable subset. This is a small,
explicit lifetime system with conservative escape rules and a checked
capability-ancestry model. It is not Rust's full lifetime inference, and it is
not a formal soundness proof; the compiler, evaluator, Cranelift lowering, and C
runtime remain trusted.

The system covers:

- explicit lifetime parameters in function signatures, written `<'a, 'b>`;
- conservative elision for a single input borrow: `fn tail(&[T]) -> &[T]`;
- borrowed immutable slice returns `-> &'a [T]` tied to caller storage;
- borrowed mutable slice returns `-> &'a mut [T]` tied to an exclusive mutable
  parameter;
- mutable and shared sub-views derived from an existing view or owner;
- retained-parent reborrows: `tail_mut(&mut parent[1..])` suspends `parent`
  rather than consuming it, and restores it after the child's checked last use;
- checked loan ancestry through helper calls, branches, blocks, and loops;
- non-lexical release of local view loans at their checked last use;
- exclusive `&mut [T]` views over inline arrays, `Vec<T>`, and `Bytes`;
- checked disjoint mutable splits: `let (left, right) =
  Slice.split_at_mut(view, mid);`;
- can be captured by a **scoped borrowed-capture closure**: a lexical
  `once fn(...)` that borrows one or more immutable `&[T]` or exclusive
  `&mut [T]` views and must be called (or dropped) inside the same scope.
- `Slice.set(view, index, value)` writes through a mutable view.
- records with declared lifetimes and shared or exclusive slice fields:
  `struct Window<'a, T> { view: &'a [T], start: i64 }` and
  `struct Writer<'a> { view: &'a mut [i64] }`, including local construction,
  checked destructuring, shared copies, move-only exclusive fields, helper
  returns, multiple distinct field lifetimes, and mixed `Box`/`Vec`/`Bytes`
  metadata that is moved and freed exactly once;
- a call-scoped nominal-record reference subset: `&self`/`&mut self` methods,
  `self: &Self`/`self: &mut Self`, and ordinary `&Record`/`&mut Record`
  parameters, with copyable field reads, copyable field writes through exclusive
  references, and checked loan retention through later arguments;
- nominal-record reference **returns** tied to a caller reference parameter,
  including shared/mutable elision, outlives bounds, and reborrow through
  helper calls; stored shared/exclusive reference locals, implicit use
  reborrow, and explicit `&*p`/`&mut *p` reborrows are checked. Records may
  store direct shared/exclusive reference fields and `&str` fields, and
  `Box<&T>`/`Vec<&T>`/`Box<&str>`/`Vec<&str>` element containers carry explicit
  element lifetimes;
- borrowed records in function-arrow parameters and results, scoped closure
  captures, capture-derived slice/record results, and structured-task captures
  from scope-external storage; reference-valued arrow parameters/results and
  borrowed `Task.scope`/`TaskExit<T>` boundaries are checked too;
- nested record-field subviews and structurally disjoint mutable field loans
  for direct local records;
- checked `&place`/`&mut place` references to nested and owning record fields,
  inline-array elements, `Vec<T>` elements, and hidden temporary owners, with
  real storage identity, source-order temporary initialization (including
  lazy short-circuit and loop-condition evaluation), structural disjointness
  for constant indices, and last-use release;
- general `*p` reads for non-owning referents and `*p = value` replacement for
  exclusive references, destroying an old affine payload exactly once.

See [expanded borrowing contracts](borrowing-extensions.md).

See also [borrowed and mixed records](borrowed-records.md),
[immutable slice operations](slices.md), [ownership and cleanup](ownership.md),
and [structured async](async.md).

## Signature syntax

Lifetimes are declared before ordinary generics:

```rust
fn tail<'a>(view: &'a [i64]) -> &'a [i64] ! {panic} {
    view[1..]
}

fn tail_mut<'a>(view: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
    &mut view[1..]
}

fn pick_mut<'a>(
    left: &'a mut [i64],
    right: &'a mut [i64],
    flag: Bool,
) -> &'a mut [i64] ! {panic} {
    if flag { left } else { right }
}

fn fill<'a>(view: &'a mut [i64], value: i64) -> Unit ! {panic} {
    let mut index = 0;
    while index < Slice.len(view) {
        Slice.set(view, index, value);
        index = index + 1;
    }
}
```

Lifetime names are lexically distinct from type, natural-const, grade, and
effect generics. They are erased at runtime and add no value representation,
allocation, or effect. A lifetime parameter must be declared, must be unique,
and may not reuse a type/natural/grade/effect generic's name.

### Explicit outlives bounds

A function lifetime binder may declare outlives bounds:

```rust
fn shorten<'long: 'short, 'short>(view: &'long [i64]) -> &'short [i64] ! {panic} {
    view
}

fn shorten_mut<'long: 'short, 'short>(
    view: &'long mut [i64],
) -> &'short mut [i64] ! {panic} {
    view
}
```

`'long: 'short` means storage borrowed for `'long` outlives storage borrowed
for `'short`. A binder may list several bounds with `+`, as in
`<'long: 'middle + 'short, ...>`. The relation is reflexive and transitive, so
`<'long: 'middle, 'middle: 'short, 'short>` also permits returning `&'long [T]`
as `&'short [T]`.

The accepted subset is deliberately explicit:

- a bound may name only a lifetime declared in the same function list; an
  unknown name, duplicate parameter, duplicate bound, or cyclic pair is a
  diagnostic (mutually bounded names would be one lifetime), while a self
  bound `'a: 'a` is accepted by reflexivity;
- records and type aliases do not accept lifetime bounds; those declarations
  keep exact lifetime agreement;
- a borrowed result lifetime `'r` is accepted when some parameter lifetime
  `'p` appears on a matching slice or borrowed field and `'p: 'r`; the reverse
  direction is rejected, so a result may be shortened but never widened;
- an exclusive `&mut [T]` result still requires an exclusive parameter (or
  exclusive mutable record-field leaf) whose lifetime outlives the result;
  shared storage is never upgraded;
- borrowed record construction, record returns, and nested record fields also
  accept a source lifetime that outlives the declared field lifetime. Direction
  stays per field, so `Two<'short, 'long>` cannot be built from
  `(&'long, &'short)`.

A missing relation may also be inferred. When an explicit result lifetime is
not already outlived by a returned direct parameter borrow, the function gains
an inferred `source: result` bound, closed transitively with any declared
bounds. The inference is limited to direct parameter lifetimes: selecting a
different field lifetime of a multi-lifetime record remains an explicit error,
and a result lifetime longer than the returned source is rejected. A body that
delegates to a helper follows the helper's declared result source, so an elided
multi-input result remains inferable through helper chains that return the
slice directly or through a projected field of the helper's structural result.
`wrap(a).view` follows only the projected field's own source; another input's
owner is not retained, so that owner may be mutated or dropped while the result
is live. Recursive declarations use the same per-field summaries. A recursive
edge unions every possible source that can reach the result through that edge,
so passing an unrelated parameter along the edge does not by itself retain it.

At a call site the caller must establish the callee's relation; the checker
never trusts an annotation. Every callee lifetime mentioned by an argument is
instantiated to the actual caller label (or a stable anonymous identity for
local storage), and for every declared pair `'a: 'b`, including transitive
pairs, every actual for `'a` must outlive every actual for `'b` under the
caller's own declared bounds. Two borrows of the same storage satisfy the
relation reflexively. The same instantiation descends through nested structural
fields: an inner callee binder adopts the caller's actual label, while two named
inner labels that bind one callee lifetime must still be identical. A caller
lifetime outlives storage owned by the caller's own frame (non-parameter locals
that hold no borrow), so
`pair(outer, &local[..])` is accepted; the reverse is not, because a local owner
cannot outlive a caller parameter. Two distinct local owners cannot establish a
non-reflexive relation, and a view merged from several sources is not treated
as frame-owned when any source is a parameter.

Returned provenance is not narrowed to the declared result name. Origins are
unioned from every parameter lifetime that outlives the result, so a shortened
view still keeps every possible source owner borrowed. If several caller
lifetimes can flow into one result and none provably outlives the others, the
result receives an anonymous internal identity: it may be used locally but
cannot be returned as a caller lifetime.

```rust
fn first<'long: 'short, 'short>(
    long: &'long [i64],
    short: &'short [i64],
) -> &'short [i64] ! {panic} {
    long // shorten the longer source to the declared result
}

fn forward<'long: 'short, 'short>(
    long: &'long [i64],
    short: &'short [i64],
) -> &'short [i64] ! {panic} {
    first(long, short) // the caller proves 'long: 'short from its own signature
}
```

See [examples/lifetime-bounds.kush](../examples/lifetime-bounds.kush) for a
runnable shared, mutable, transitive, helper and record version.


### Conservative signature elision

An input borrow may omit its lifetime. Each elided input borrow receives a fresh
compiler-internal identity, so independent anonymous inputs are never merged.
A borrowed slice result may also omit its lifetime when the input side names
exactly one distinct borrow lifetime:

```rust
fn tail(view: &[i64]) -> &[i64] ! {panic} {
    view[1..]
}

fn tail_mut(view: &mut [i64]) -> &mut [i64] ! {panic} {
    &mut view[1..]
}

fn reborrow(view: &mut [i64]) -> &[i64] ! {panic} {
    &view[1..]
}

fn pick<'a>(left: &'a [i64], right: &'a [i64], flag: Bool) -> &[i64] ! {panic} {
    if flag { left } else { right }
}
```

The rules are deliberately local to the signature:

- an elided result is inferred only when there is exactly one distinct input
  borrow lifetime;
- repeated copies of the same explicit lifetime (`&'a [T]` twice) count as one
  candidate;
- two or more distinct input lifetimes, anonymous or named, make an elided
  slice result ambiguous. The diagnostic points at each candidate input and
  asks for a shared explicit lifetime on the returned input and the result;
- no borrowed input at all is an error; a result cannot invent a caller
  lifetime;
- non-borrowed parameters do not create lifetime candidates;
- borrowed owner-reference inputs (`&Box<T>`, `&Vec<T>`, `&Bytes`) participate
  conservatively in ambiguity, but they cannot supply slice provenance, and
  owner-reference results remain forbidden;
- the function body is never inspected to choose or unify a lifetime, and
  independent input roots are never unified;
- an explicit annotation must still name a declared lifetime present on a
  matching parameter, and an exclusive result must still derive only from
  exclusive inputs;
- transparent type aliases are not inspected for elision. A parameter written
  through an alias does not contribute a syntactic borrow candidate, and a
  result written through an alias is not treated as a syntactic borrowed slice
  result. Spell the borrow on the parameter or result directly.

A function that returns `&[T]` or `&mut [T]` must:

1. annotate the result with an explicit lifetime (`-> &'a [T]` or
   `-> &'a mut [T]`) or use the conservative elision above;
2. bind the resulting lifetime to at least one slice parameter whose declared
   lifetime is the result lifetime or outlives it through explicit bounds;
3. for `&mut [T]`, bind it to at least one exclusive `&'a mut [T]` parameter (or
   exclusive mutable record-field leaf) whose lifetime outlives the result;
4. return only storage derived from a parameter whose lifetime outlives the
   result, with an exclusive capability chain for a mutable result.

Returning `&Box<T>`, `&Vec<T>`, or `&Bytes` remains unsupported: owner-reference
results are still call-scoped, because their current native representation is a
stack snapshot of the owner handle rather than a stable address.

## Checked capability ancestry

The checker tracks more than a flat set of owners for each view local. A view
records:

- its **roots**: the owned storage slots (array/`Vec`/`Bytes` locals) or slice
  parameters whose storage it ultimately borrows;
- its **ancestry**: the immediate parent view, every ancestor view, and those
  roots;
- its **mutability**: shared `&[T]` or exclusive `&mut [T]`.

Deriving a child records the parent capability in the child's ancestry. That is
what distinguishes a legitimate parent-child reborrow from a competing alias:

```rust
fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} { &mut s[1..] }

let mut values: [i64; 4] = [1, 2, 3, 4];
let child = tail_mut(&mut values[..]);      // values is suspended
let grandchild = tail_mut(&mut child[..]);  // child is suspended
Slice.set(grandchild, 0, 9);
print_i64(Slice.get(grandchild, 0));        // 9
print_i64(Slice.get(child, 0));             // child restored
print_i64(values[2]);                       // values restored after child's last use
```

Rules for creating a child:

- a shared child may be derived from a shared or exclusive parent; deriving a
  shared child from an exclusive parent **suspends** that parent;
- an exclusive child may be derived only from an exclusive parent (or directly
  from a mutable owner); shared storage is never upgraded;
- the immediate parent and its ancestors are the permitted capability path;
- any other live view of the same root conflicts: an exclusive child requires
  exclusive access to every root, and a shared child cannot coexist with an
  exclusive view of that root;
- ordinary disjoint ranges are not inferred. Two mutable subviews written as
  separate ranges remain rejected. The sole sibling exemption is the checked
  pair produced by `Slice.split_at_mut`, described below.

While a child is live, a suspended parent is not a second capability:

- a mutable parent is suspended by **any** live child, shared or exclusive;
- a shared parent is suspended only by an exclusive child;
- a suspended parent cannot be read, written, moved, dropped, replaced, passed
  to a call, used as a builtin receiver, or narrowed again;
- the parent and the ultimate owner become usable again after the terminal
  child's checked last use.

Multiple shared views of the same shared owner or parent may coexist. They
temporarily forbid moving or replacing the owner and forbid creating an
exclusive view of it, but reading through each shared view is allowed.

## Explicit reborrows and consuming calls

Ordinary passing of a mutable view moves the capability:

```rust
fn consume(view: &mut [i64]) -> Unit ! {panic} { Slice.len(view); }

let parent: &mut [i64] = &mut values[..];
consume(parent);            // parent is consumed
// Slice.len(parent);       // rejected: use after move
```

An explicit `&mut parent[..]` argument derives a child capability for the call.
The caller keeps the parent, but it is suspended by the call and by any returned
view that names the same input lifetime:

```rust
fn tail_mut<'a>(s: &'a mut [i64]) -> &'a mut [i64] ! {panic} { &mut s[1..] }

let parent: &mut [i64] = &mut values[..];
let child = tail_mut(&mut parent[..]); // explicit reborrow; parent retained
// Slice.len(parent);                  // rejected while child is live
Slice.set(child, 0, 7);
print_i64(parent[1]);                  // allowed after child's last use
```

A call result inherits capability ancestry from the arguments whose declared
lifetime matches the result lifetime. A mutable result requires that every
matching parameter and argument be exclusive. A shared result may derive from a
mutable parameter by narrowing; the mutable ancestor is then suspended while the
shared result is live.

## Scoped borrowed closure captures

A lambda may capture immutable or exclusive slice views. Such a lambda is a
**scoped once callable**: it has the same two-word `once fn(...)` runtime
representation, allocates its environment, and may be called at most once. The
borrow remains tied to the original owner storage; the environment stores only
the four-word view descriptors and never owns the array, `Vec`, or `Bytes`.

```rust
fn main() -> i64 ! {alloc, panic} {
    let mut values: [i64; 3] = [1, 2, 3];
    let view: &mut [i64] = &mut values[..];
    let bump = fn(by: i64) -> Unit ! {panic} {
        Slice.set(view, 0, Slice.get(view, 0) + by);
    };
    bump(41);
    values[0] // 42: the call consumed the closure and released the loan
}
```

The surface is intentionally narrow:

- a borrowed-capture lambda may be built only as the direct initializer of a
  `let`, or as the immediate callee of an indirect call;
- the resulting local may only be called. It cannot be copied, moved to another
  binding, returned, passed to an ordinary or generic function, stored in a
  record/enum/array/vector/box/union, adapted by a representation-changing
  conversion, or captured by another closure or task;
- an implicit drop at the end of its lexical scope is allowed. It releases the
  closure environment and the borrow, and never drops the borrowed owner;
- constructing one requires `alloc` and `panic`, because the environment is a
  real allocation. There is no fake no-allocation claim;
- a borrowed-capture lambda cannot be coerced to a union or a non-`once`
  function type. A same-layout `once fn(...)` annotation is allowed; a
  representation-changing adapter would store the closure and is rejected.

A mutable scalar local is captured the same way. The environment stores the
address of the caller's stack binding instead of a copied value, so a lambda
assignment writes the caller's location. The capture is a scoped capability:
the environment cannot outlive that binding, and the location is loaned until
the closure's checked last call or scope end. A lambda that writes the capture
takes an exclusive loan; a read-only lambda takes a shared loan, so unrelated
reads remain allowed while writes are rejected. The pointer is never an owner;
dropping an uncalled closure or calling it frees only the environment cell.
Returning, storing, passing, adapting, or sending such a closure to a task is
rejected exactly like a borrowed slice capture. Calling a writing lambda
invalidates proof facts about the captured scalar's old value; a read-only
lambda call preserves them.

Capturing a mutable view **moves** the capability into the closure. Capturing a
shared view adds another shared alias but keeps the same owner-move and
exclusive-borrow restrictions. While the closure is live and still callable:

- an exclusively captured view is moved, so its old name cannot be used again;
  shared captures retain aliases rather than consuming the original view;
- every captured parent, ancestor, and owner cannot be moved, dropped,
  replaced, or exclusively borrowed;
- shared owners may still be read through unrelated shared views, exactly as
  with ordinary shared views;
- split-side labels are combined, so closures over opposite sides of one
  checked `Slice.split_at_mut` pair may coexist and be used in either order.

A closure that mixes shared and exclusive captures is conservative at the
aggregate level: while it is live, every captured owner is treated as
exclusively borrowed, even if one particular capture was shared. Splitting that
precision per captured origin is not implemented.

The backward liveness fixed point includes borrowed-capture closure locals. The
loan ends at the closure's checked last call, at an explicit scope end, or when
an earlier `return`, `?`, `break`, or branch makes it dead. Consuming the closure
by a call therefore restores owners and parents; an uncalled closure keeps them
suspended until its lexical scope ends. A closure that is never used at all
still owns only its environment, so dropping it cannot invalidate an owner.

The closure may capture views derived from parameters, including a function's
own borrowed slice parameters. A nested lambda may capture the enclosing
closure's slice parameter; the nested callable is checked in the same way.

## Borrowed and mixed records

Records may declare erased lifetimes before ordinary generics and store shared
`&'a [T]` or exclusive `&'a mut [T]` slice fields. They may also carry ordinary
owned metadata whose payload contains no borrow, such as `Box<T>`, `Vec<T>`,
`Bytes`, or an owning record/enum. This is a raise of the previous "no stored
views" boundary, not a general record-lifetime system:

```rust
struct Window<'a, T> {
    view: &'a mut [T],
    start: i64,
}

fn window<'a>(view: &'a mut [i64]) -> Window<'a, i64> ! {} {
    Window { view: view, start: 0 }
}

fn first<'a>(window: Window<'a, i64>) -> &'a mut [i64] ! {panic} {
    let Window { view, .. } = window;
    view
}
```

Lifetime arguments (`Window<'a, i64>`) are a distinct erased category from type,
natural, grade and effect arguments. They add no runtime word, tag, allocation
or effect. Each borrowed field must name a declared record lifetime. The checker
keeps per-field provenance (lifetime, mutability, origins, split labels) through
construction, destructuring, calls and returns, so a field from `'b` cannot be
returned as a field or slice declared `'a`, and shared storage cannot be returned
as `&mut`.

A record containing only shared fields and copyable metadata remains copyable. A
record containing any exclusive field, directly or through a nested record, is
affine/move-only transitively. An exclusive field cannot be copied out by direct
projection; destructure the record first. Mixed records move their owned fields
exactly once and free only those owned fields, never a borrowed owner. Enum,
union, `Vec`/`Box`/array storage of a borrowed record, function-value use, generic
type-argument crossing, closure/task capture and self-reference remain rejected.
See [borrowed and mixed records](borrowed-records.md) for the exact contract.

Borrowed record locals participate in the same backward last-use analysis as
slice views. Field aliases, copies and destructured views retain the owner until
their checked last use; loops, branches, early exits, `?`, later call arguments
and same-task suspension are accounted for. Construction evaluates fields left
to right, including reordered record temporaries, so an earlier field's loan
protects its owner while later fields/arguments run.

## Checked disjoint mutable splits

One mutable capability may be divided into two simultaneous mutable siblings
only through a checked split:

```rust
let (left, right) = Slice.split_at_mut(parent, mid);
```

This is a restricted borrow-pair form, not a storable tuple value. It must be
the initializer of a `let` whose pattern is exactly two distinct simple names.
The pair cannot be annotated, declared `let mut`, returned as a pair, stored in
a record, array, vector, box, or enum, passed as a value, or captured. The
individual children remain ordinary views and may be returned through a
matching parameter lifetime. The receiver may be
a mutable slice-view local or an explicit `&mut owner[..]` /
`&mut parent[..]` reborrow. The midpoint is evaluated exactly once, then checked
as `0 <= mid <= Slice.len(receiver)`; the two views are exactly `[0, mid)` and
`[mid, len)`. A bad midpoint panics under the `panic` effect.

The split is checked provenance, not an unchecked range claim. Both children
record the same split group and opposite sides. A descendant inherits its
parent's side, and a borrowed call result inherits only side assumptions shared
by every argument whose declared lifetime contributes to the result. The only
sibling conflict exemption is when two live views have opposite sides of the
same checked group. No other pair of overlapping-range siblings is allowed,
and an independent root alias is still rejected. Parent and owner suspension is
unchanged: the whole parent is unusable while either child, or any descendant of
either child, is live. Using both children through ordinary calls, explicit
reborrows, nested builtins, branches, loops, and same-task suspension is allowed
when they remain disjoint.

A view may read its own length while computing a subview's bounds, for example
`&mut left[0..Slice.len(left)]`. This reads only the reserved capability's
metadata. Moving the receiver, writing through it, or creating a competing view
inside those bounds remains rejected.

```rust
fn bump(a: &mut [i64], b: &mut [i64]) -> Unit ! {panic} {
    Slice.set(a, 0, Slice.get(a, 0) + 1);
    Slice.set(b, 0, Slice.get(b, 0) + 10);
}

let mut values: [i64; 4] = [1, 2, 3, 4];
let (left, right) = Slice.split_at_mut(&mut values[..], 2);
Slice.set(left, 0, 10);
bump(&mut left[..], &mut right[..]);
print_i64(values[0]); // 11
print_i64(values[2]); // 13
```

A split result does not become a general range algebra. Two separately written
mutable slices over the same owner are still rejected even when their literal
ranges are disjoint, and the checker does not infer anything from arithmetic
relationships between unrelated ranges.

## Returned-view provenance

Returning a reborrow of an input lifetime may name that input lifetime:

```rust
fn narrowed<'a>(view: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
    tail_mut(view) // the result and argument both carry 'a
}

fn local_child<'a>(view: &'a mut [i64]) -> &'a mut [i64] ! {panic} {
    let child = &mut view[1..];
    child // allowed: every root is a parameter with lifetime 'a
}
```

The checker rejects a returned view when:

- it borrows a local owner, stack local, temporary, or local block storage;
- its lifetime is not declared on a matching slice parameter;
- a mutable result derives from a shared parameter or a shared child view;
- any root behind a returned local child view is not a matching parameter;
- the body tail would outlive an owner declared in the same lexical block.

Return provenance checks both the input lifetime and the mutability of the whole
ancestry, not only the result type.

## Last-use release and control flow

View loans are not tied to the textual block end. The compiler runs a backward
liveness fixed point over the checked IR for slice-view locals. A loan remains
active exactly while some alias is live:

```rust
let view: &[i64] = &values[..];
print_i64(Slice.len(view));
values = Vec.push(values, 20); // view is dead here
```

The analysis accounts for aliases, both branches of `if`, match arms and guards,
short-circuit right operands, early returns, `?`, `break`/`continue`, calls, and
task suspension points. In particular, a textually last use inside a loop does
not release the loan if a later iteration can still use the view. The loop head
is a fixed point; only a view that is dead on every continuing and exiting path
stops loaning its owner.

The analysis is intentionally conservative at boundaries it cannot model
precisely: an unreachable or terminating branch may keep a loan live, and a
view captured in a complex nested expression remains live through that
expression. Slice views are single-assignment: rebinding a view local is
rejected, so its checked ancestry is fixed at its `let`. Holding a loan longer
only rejects programs; it never permits an owner move while a view is live.

Moving, dropping, replacing, or passing an owner by value while a view is live is
rejected. Reading an owner through a new shared borrow is allowed while only
shared views exist. A child cannot be used after its owner or ancestor is moved
or dropped, because such a move or drop is itself rejected while the child lives.

Last-use release does not end a loan while an evaluated argument still holds the
view. Slice arguments retain shared or exclusive loans through all later
argument evaluation and the call itself, including indirect calls and nested
blocks. For example, `consume(view, { owner = replacement; 0 })` is rejected
even if the view has no later source-level uses. Temporary views obey the same
rules: neither `f(&mut owner[..], &owner[..])` nor two simultaneous mutable
arguments borrowing the same owner are allowed, unless they are the two
opposite sides of one checked `Slice.split_at_mut` pair.

## Exclusive mutable views

`&mut [T]` creates a move-only capability over copyable elements:

```rust
fn fill<'a>(view: &'a mut [i64], value: i64) -> Unit ! {panic} {
    let mut index = 0;
    while index < Slice.len(view) {
        Slice.set(view, index, value);
        index = index + 1;
    }
}

let mut numbers: [i64; 3] = [0, 0, 0];
fill(&mut numbers[..], 7);
print_i64(numbers[0]); // 7
```

The viewed owner must be a mutable local (`let mut`). While an exclusive view is
live and not suspended:

- no second shared or exclusive view of the same root may be created outside
  its capability path;
- the owner cannot be moved, dropped, replaced, or read directly through its
  name or a new `&owner` borrow;
- the exclusive view cannot be copied or retained as an alias.

`Slice.len`, `Slice.get`, `Slice.try_get`, `Slice.at`, and `Slice.set` reborrow
an exclusive view for that call, so a fill loop can read and write through the same view. Passing
the view to an ordinary function transfers the capability; use an explicit
`&mut view[..]` child or a borrowed-return helper to retain the parent.

A builtin receiver remains reserved during evaluation of its index and value
arguments. Nested slice builtins may reborrow that same receiver, as in
`Slice.set(view, i, Slice.get(view, i) + 1)`: the nested read completes before
the outer write. This does not permit moving the receiver to an ordinary call,
replacing its owner, or creating another view of the owner in those arguments.

`Bytes` remains a byte buffer: `&mut bytes[..]` has type `&mut [i64]`, and
`Slice.set` writes the low byte of each value. Values outside `0..=255` panic.
`Slice.get`/`Slice.set` bounds checks need the `panic` effect; `Slice.try_get`
returns `Option<T>` and needs no `panic` effect.

## Lifetime-aware callable types

A function arrow type may bind its own lifetimes and borrow slice views:

```rust
fn measure(values: &[i64], f: fn(&[i64]) -> i64 ! {panic}) -> i64 ! {panic} {
    f(values)
}

fn apply<'x>(
    f: fn<'a>(&'a [i64]) -> &'a [i64] ! {panic},
    values: &'x [i64],
) -> &'x [i64] ! {panic} {
    f(values)
}
```

The arrow is polymorphic over its lifetimes: every call instantiates them
afresh from the arguments, exactly like a call to a named function. Rules:

- Lifetimes in an arrow must be bound by that arrow (`fn<'a, 'b: 'a>(...)`);
  an arrow cannot borrow for an enclosing function's lifetime. Bounds follow
  the same syntax and checks as function bounds.
- An unnamed slice parameter gets its own fresh lifetime. An unnamed slice
  result is elided only when the parameters name exactly one lifetime.
- A slice result must be outlived by some slice parameter, and an exclusive
  `&mut [T]` result needs an exclusive parameter that outlives it.
- Only slice views may be borrowed. Owner references and borrowed records stay
  direct-call only.

A **call through a value** applies the arrow's contract: callee bounds must be
established by the caller, and a slice result keeps every argument that can
flow into it borrowed. Inhabitants never return their own captures: lambdas
cannot return slices, and slice-returning values are named functions (or
synthesized adapters around them, which are checked against the contract).

**Substitution (variance).** A value fits an arrow when its contract is
implied by the arrow's. The arrow's lifetimes are fixed; each lifetime of the
value is instantiated by the arrow lifetimes in the same parameter positions
(and the arrow's result lifetime for the value's result). Then every bound of
the value must follow from the arrow's bounds, and every value parameter that
can flow into its result must sit at an arrow position whose lifetime outlives
the arrow's result. So `fn second<'l: 's, 's>(l: &'l [T], s: &'s [T]) -> &'s [T]`
fits `fn<'a>(&'a [T], &'a [T]) -> &'a [T]`, but a function returning its second
input does not fit `fn<'a, 'b>(&'a [T], &'b [T]) -> &'a [T]`. Arrow types are
compared up to renaming of lifetimes. Diagnostics print arrow lifetimes as
`'a`, `'b`, ... in order of first use. The rule applies contravariantly to
callable parameters of callables.

See [borrowed-callables.kush](../examples/borrowed-callables.kush).

## Representation and no-allocation guarantee

A shared or exclusive slice is still the private four-word
`(data pointer, length, stride, byte-elements flag)` representation.

- A `Vec`/`Bytes` view points into the existing heap storage.
- A view returned from a helper passes those words back; it does not point into
  a temporary callee snapshot.
- An inline array local is pinned to a private stack cell the first time a view
  of it is created. The native backend reads and writes that cell so `&mut`
  writes are visible through the owner. The reference evaluator uses a shared
  host cell for the same purpose.
- Creating, sub-slicing, splitting, reading, writing, moving, or dropping a
  view allocates no program heap storage and has no `alloc` effect. Mutable
  views are not counted as allocations. A split pair is two ordinary four-word
  views plus checker-only provenance; there is no runtime tag, range object, or
  hidden heap tuple.
- Returned sub-views and split children adjust pointer, length, stride, and byte
  flags; they never copy the backing storage.
- A borrowed shared record is its ordinary inline record layout: one
  discriminator word and the fields in declaration order. Each slice field is an
  existing four-word descriptor. Copies copy descriptors only; lifetime
  arguments add no representation. See
  [borrowed and mixed records](borrowed-records.md).

`#[noalloc]` functions may take either kind of view, derive children, split a
mutable view, call the slice operations, and return shared or exclusive slices
tied to their parameters. A `#[nosuspend]` function may hold and return views; it
simply cannot suspend while doing so.

## Task suspension

A view or borrowed-record local may live across `Task.yield`, `Task.join`, and
other same-task suspension points. The task stack and its pinned array cells are
retained until the task reaches a normal exit, and the owner cannot move while
the view is live. Suspension does not release a loan early. A scoped
borrowed-capture closure may also be held and called across same-task
suspension. Scope bodies and spawned children may borrow slice views from
outside the scope, which outlive the scope's final join; see
[scoped borrowing](async.md#scoped-borrowing). Borrowed records and
borrowed-capture closures still cannot be captured by a task, and no borrow can
be returned across a task boundary.

## Deliberate remaining limitations

- Elision is limited to a borrowed slice result whose input borrows name
  exactly one distinct lifetime. Borrowed record parameters contribute one
  candidate per field lifetime, and arrows/lambdas count record leaves. When a
  function result has several input candidates, the body may resolve them when
  its return positions are rooted in exactly one parameter lifetime or one
  named record field path; several return-position lifetimes are rejected, not
  unified. A helper call in the returned position follows the helper's
  declared result source. Missing outlives bounds between a direct parameter
  lifetime and an explicit result lifetime are inferred and checked at each
  call site. Inference through local destructuring bindings and general
  unification are still absent; those require explicit annotations.
- References may be returned when tied to a reference parameter. Shared and
  exclusive `&Box<T>`, `&Vec<T>`, `&Bytes`, and `&String` results are
  supported; records may store shared reference fields, shared slice fields,
  and text fields, and `Box<&T>`/`Vec<&T>`/`Box<&str>`/`Vec<&str>` reference
  elements. Shared reference and text fields are readable through `&Record`.
  Stored reference locals, explicit reborrows, and `&record.field` place
  references are supported, including returning a field reference from a
  reference parameter. A mutable place reference requires a mutable root or an
  exclusive reference root; a record with borrowed fields is not mutated as a
  whole. `&mut str` remains unsupported because unrestricted byte mutation can
  invalidate UTF-8; a sound operation would have to replace complete Unicode
  scalars with unchanged encoded length. Place references into slice-view
  elements (`&s[i]`, `&mut s[i]`) root at the view's owners; see
  [borrowing-extensions.md](borrowing-extensions.md#slice-view-element-places).
  Containers of borrowed records remain unsupported.
- Dynamic disjoint-range reasoning is limited to `Slice.split_at_mut` pairs.
  There is no general range algebra, no arbitrary tuple of views, and no
  storage or forwarding of a split pair itself. Two separately written
  disjoint ranges remain rejected.
- A split pair cannot be decomposed across control-flow branches or stored in a
  record. Its two names must bind at the `let`, and each name is a normal
  single-assignment move-only view afterward.
- Split-side provenance is conservative through branch-selected views and
  helper results: when the checker cannot prove one side, it rejects a
  potentially overlapping sibling instead of guessing.
- No stored views in enums, arrays, vectors, boxes, or unions. Records are the
  sole stored-view exception. A borrowed record cannot be stored in an
  enum/union/array/vector/box or passed through an ordinary generic type
  parameter, except as a child task result inside the conventional
  `TaskExit<T>` wrapper produced by `Task.join`. It may be captured by a scoped
  closure or by a scope body/child task when its leaves derive from storage
  outside the scope. A borrowed-capture closure cannot escape its lexical
  `let` binding and cannot be passed to a higher-order helper.
- Record fields may be shared or exclusive slice views plus ordinary owned
  metadata that cannot hide a borrow. Borrowed owner references, streams, unions,
  callables, task handles, linear fields, and `Box`/`Vec`/array storage of a
  borrowed record remain rejected. Direct projection of an exclusive field or of
  a nested record containing one is rejected as a value; derive a subview with
  `&mut record.field[..]` instead. Structurally disjoint field subviews of one
  local record may coexist, while the whole record stays suspended for moves.
  Self-referential record construction remains rejected.
- Arrow types describe borrowed slice parameters/results and borrowed record
  field leaves. A capture-derived result is described by the scoped closure's
  capture contract, not by an ordinary arrow; the checker rejects capture
  escapes instead of erasing one. Capturing lambdas may return borrowed slices
  and records only from exactly one capture origin; parameter and capture
  origins cannot be mixed.
- Slice destructuring patterns remain array-only; there is no richer borrowed
  or runtime-slice pattern matching.
- Arrow types may relate slice lifetimes and record field lifetimes they bind
  themselves; they cannot mention an enclosing function's lifetimes, inferred
  local identities, or owner references.
- No higher-kinded or generic lifetime parameters, no outlives bounds on
  records or aliases, no variance annotations on records, and no
  lifetime integration with dependent proofs. Function outlives bounds are the
  explicit, checked subset described above; they are not inferred. Arrow
  bounds are checked the same way at calls through a value.
- No general NLL inference for owner references; only slice-view locals use the
  backward last-use analysis.
- The ancestry analysis is path-insensitive and conservative. It is not a
  formal proof. Both backends and the runtime are trusted implementation
  components.


The finite outlives relation is implemented by the standalone [lifetime graph
and SCC solver](lifetime-graph.md), including cycle and failed-call diagnostics.
The documented inference limits above still apply.
