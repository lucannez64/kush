# Borrowed records, mutable fields, and mixed ownership

Status: implemented borrowed-record milestones for the executable subset.
Records may declare erased lifetime parameters and store shared `&'a [T]` or
exclusive `&'a mut [T]` slice fields. A later call-scoped milestone adds
`&self`/`&mut self` receivers and ordinary `&Record`/`&mut Record` parameters;
its explicit boundaries are described below. They may also carry ordinary owned
metadata such as `Box<T>`, `Vec<T>`, `Bytes`, or an owning record/enum whose
payload contains no borrow. Construction, field access, destructuring, copying,
passing, returning and cleanup keep field-level provenance and ownership checked
against caller storage.

The subset is deliberately narrow. A record that contains any exclusive borrow
is affine and move-only, even when it owns no heap storage. A record containing
only shared borrows and copyable metadata stays copyable. Containers, unions,
callables, task captures, generic type-parameter crossing and self-reference
remain rejected. This is an engineering milestone, not a formal soundness proof;
the compiler, evaluator, Cranelift lowering and C runtime remain trusted.

See also [borrowing and lifetimes](lifetimes.md),
[ownership and cleanup](ownership.md), [slice operations](slices.md),
[enum storage](enums.md) and [structured async](async.md).

## Syntax

Lifetimes are declared before ordinary type parameters. A borrowed field must
name one of the record's declared lifetimes:

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

Lifetime arguments and runtime type arguments are separate categories. In
`Window<'a, i64>`, `'a` is an erased lifetime identity and `i64` is the ordinary
type argument. Lifetimes must precede type/natural arguments. They are not
runtime types, values, proof terms, tags or allocation; a record's inline layout
contains only its ordinary fields.

Supported record forms:

- explicit lifetime parameters on `struct` declarations and transparent
  `type` aliases;
- one or more shared `&'a [T]` or exclusive `&'a mut [T]` slice fields, each
  written directly with a lifetime declared on the record;
- ordinary copyable metadata: `i64`, `Bool`, `Unit`, non-owning enums, inline
  arrays of copyable data, and nested records that are themselves ordinary
  copyable data or borrowed records;
- ordinary type parameters, natural-const parameters, nested borrowed records,
  and lifetime-parameterized type aliases;
- owning metadata that cannot hide a borrow: `Box<T>`, `Vec<T>`, `Bytes`, and
  ordinary owning records or enums whose payload contains no borrowed type and
  no linear obligation;
- explicit type arguments, an expected type, or conservative inference for a
  local literal.

```rust
struct Inner<'a> { view: &'a mut [i64] }
struct Outer<'a> { inner: Inner<'a>, note: i64 }

fn outer<'a>(view: &'a mut [i64]) -> Outer<'a> ! {} {
    Outer { inner: Inner { view: view }, note: 3 }
}
```

Mixed ownership is checked, not erased:

```rust
struct BufferView<'a> {
    view: &'a [i64],
    token: Box<i64>,
    start: i64,
}

fn make<'a>(view: &'a [i64]) -> BufferView<'a> ! {alloc, panic} {
    BufferView { view: view, token: Box.new(5), start: 2 }
}
```

`BufferView` moves its owned `token` exactly once and its borrowed `view` keeps
the caller's storage loaned. Dropping it frees only `token`; it never frees the
array, `Vec`, or `Bytes` storage behind `view`.

## Provenance contract

The checker tracks each borrowed record value per field leaf:

- the field's declared erased lifetime (`'a`, `'b`, ...);
- the capability origins behind the field (caller parameters, local owners and
  their descended views);
- split-side assumptions, exactly as for ordinary slice views;
- whether the field is shared or exclusive.

Deriving a field view carries the field's origins, mutability and split labels;
it does not copy the backing array, `Vec` or `Bytes` storage. A record parameter
is an external aggregate: each borrowed field starts with the parameter itself
as its origin and the lifetime declared by the parameter's instantiated field
type.

A returned record or slice is accepted only when every borrowed leaf has the
declared result lifetime and every origin is a parameter carrying that lifetime.
An exclusive leaf requires an exclusive parameter or an exclusive record-field
leaf with the same lifetime. Local owner storage, block temporaries and owner
references cannot be returned. Two fields with distinct lifetimes stay distinct:
swapping them in a record literal, or returning `two.second` where `&'a [i64]`
is declared, is rejected. At a call boundary the callee's declared lifetime
names are instantiated from the actual argument fields; origins from every
matching field are unioned, never flattened into a different declared lifetime.

```rust
struct Two<'a, 'b> {
    first: &'a [i64],
    second: &'b mut [i64],
}

fn first<'a, 'b>(two: Two<'a, 'b>) -> &'a [i64] ! {} {
    let Two { first, .. } = two;
    first
}
```

A mutable field cannot be copied out by direct projection. The restricted form
is explicit destructuring first:

```rust
let window = Window { view: &mut values[..], start: 0 };
let Window { view, start } = window; // moves the affine record
Slice.set(view, 0, 9);
```

`window.view` for an exclusive field is rejected with a diagnostic asking for
this destructuring step. That is the deliberate checked-extraction rule: it
prevents a second copy of an exclusive descriptor from existing while the record
value is still available.

## Affinity, copies and mixed ownership

- A record with only shared slice fields and copyable metadata is copyable. Copying
  copies the four-word descriptors, never the backing storage.
- A record containing any exclusive borrow, directly or through a nested record,
  is affine/move-only transitively. It is not made copyable merely because its
  owning-layout flag is false.
- A record containing `Box`, `Vec`, `Bytes`, or an owning record/enum moves and is
  cleaned up like any other affine owner. Its owned fields are released exactly
  once; borrowed descriptors are released without touching their owners.
- Moving an owned field directly out of a record remains restricted. Destructure
  first, then consume the owned binding.

## Destructuring, field aliases, and split siblings

Destructuring transfers each field's provenance and mutability to the binding.
A nested record can be destructured one level at a time. `let Window { view,
start } = window;` moves an affine record; a wildcard or omitted owning field is
dropped once on the selected arm.

While a record, a field alias, or a descendant view is live, the parent/caller
owner is suspended. A shared field alias keeps the owner borrowed; an exclusive
field alias keeps it exclusively suspended. The owner becomes usable again after
the terminal alias's checked last use.

Checked split siblings remain per-field. Opposite sides of one
`Slice.split_at_mut` pair may be stored in two record fields and later extracted
as disjoint mutable views. The record does not flatten those sides into a broad
sibling exemption; each field leaf keeps its own split labels.

## Borrowed record receivers and reference parameters

This milestone adds a deliberately first, call-scoped reference subset for
nominal records. It is not general `&T`/`&mut T` support.

```rust
struct Point { x: i64, y: i64 }

impl Point {
    fn sum(self: &Self) -> i64 ! {panic} { self.x + self.y }
    fn shift(&mut self, by: i64) -> Unit ! {panic} {
        self.x = self.x + by;
        self.y = self.y + by;
    }
}

fn peek(p: &Point) -> i64 ! {panic} { p.x }
fn bump(p: &mut Point) -> Unit ! {panic} { p.x = p.x + 1; }
```

Supported:

- `self: &Self`, `self: &'a Self`, `&self`, `self: &mut Self`,
  `self: &'a mut Self`, and `&mut self` on inherent and trait methods whose
  concrete target is a nominal record;
- automatic receiver borrowing for `owner.method()` when the methods are
  declared with those receiver forms, with the receiver evaluated exactly once;
- ordinary function parameters `&Record` and `&mut Record`, called with
  `helper(&owner)` / `helper(&mut owner)`;
- reading scalar and copyable fields through a shared reference, including
  fields of nested copyable records and inline-array indexing;
- replacing scalar/copyable, non-owning fields through an exclusive reference;
- shared aliases of one owner; exclusive loans are exclusive;
- loans retained through all later arguments of the enclosing call and released
  at its checked completion;
- owning records: borrowing never moves, copies, or frees their owned metadata,
  and normal cleanup still runs exactly once.

Rejected deliberately:

- borrowing a temporary, field, index result, or any expression other than a
  direct local binding;
- storing `&Record`/`&mut Record` in a `let`, returning it, capturing it in a
  closure/task, or placing it in a record, tuple, array, union, container, box,
  vector, or callable value;
- calling a borrowed method through an existing reference, or upgrading a
  shared reference to an exclusive one;
- reading or replacing an owning or linear field through a reference, including
  `Box`/`Vec`/`Bytes` metadata;
- reading a borrowed slice field through a record reference; destructure the
  owning record or use the slice view directly;
- mutable receivers or mutable field writes on a record that contains a
  borrowed field, or any field containing an exclusive slice leaf;
- borrowing enums, borrowed-record metadata, self-referential records, or using
  references as generic/type-class evidence that could erase their loans;
- moving, dropping, replacing, or (for exclusive loans) reading the owner while
  its loan is live.

The `&mut Record` field-write form handles only values whose cleanup is trivial
and whose type cannot own storage. Owning-field replacement is not enabled
because the old field's deterministic cleanup and alias restrictions are not
fully modeled in this subset.

Internally, the reference evaluator pins a record local in a shared storage cell
when it is borrowed, exactly as inline arrays are pinned for mutable slices. The
native backend pins nominal-record locals to stack storage. A reference is one
machine word pointing at that storage; lifetime arguments add no word, tag, or
allocation. Reads load the current field, and writes through `&mut Record`
update the same cell/stack slot observed by the caller. Neither backend copies
an owning record while a reference is live.

## Borrows follow the value until its checked last use

Record locals take part in the same backward liveness fixed point as slice
views. A loan lasts while the record, a field alias, or a destructured field can
still be used. Loops, branches, short circuits, early returns, `?`, helper
results and same-task suspension retain the loan; a textual last use inside a
loop does not release it if a later iteration can use the field.

Earlier call arguments and record fields keep their owners borrowed through all
later arguments/fields, including direct and indirect evaluation, reordered
record temporaries, and later fields that return or propagate `?`.

## Representation and effects

A record layout remains one inline discriminator word followed by its ordinary
fields in declaration order. A slice field uses the existing private four-word
`(data pointer, length, stride, byte-elements flag)` descriptor. Lifetime
arguments add no word, tag, allocation, suspension or effect. A record field view
points at the original inline-array stack cell or `Vec`/`Bytes` heap storage; a
helper returns the descriptors and any owned fields.

Creating, copying, destructuring, passing or dropping a borrowed record allocates
no program storage. Constructing a `Box`, `Vec` or `Bytes` metadata field carries
the usual `alloc`/`panic` effects; moving or dropping an already constructed
record does not allocate. Inline-array owners are pinned exactly as with an
ordinary slice view. Normal allocation diagnostics must balance on both the
reference evaluator and native execution.

## Cleanup and exits

Owned metadata participates in the ordinary deterministic cleanup rules. A
partial constructor, `return`, `?`, `break`, `continue`, guard or overwritten
record cannot silently leak or double-free an owned field. Reordered record
literals evaluate in source order into temporaries and build in layout order;
those temporaries are moved or cleaned on every exit path.

Reading a shared or copyable field from a local owning record observes that
local without creating a second owner. Nested place projections follow the
same rule. The record retains its owned fields until it is moved or cleaned up.
Record patterns accept a final `..` (with an optional trailing comma); omitted
fields retain their ordinary checked cleanup and linearity rules.

Borrowed record storage itself is inline. There is no hidden allocation,
reference counting or garbage collection for the record or its lifetime
arguments. A record containing an owned field is not an owner of its borrowed
owners.

## Deliberate limitations

- `&Record`/`&mut Record` are call-scoped only. There is no general `&T` or
  `&mut T` lifetime system, no stored references, no reference reborrow
  ancestry, and no reference-returning methods or functions.
- Borrowed receivers are only for nominal records. Enums, borrowed records with
  an exclusive receiver, and records containing borrowed or exclusive leaves
  are rejected or restricted as described above.
- A mutable slice field may only be extracted by destructuring first. Direct
  mutable field projection, direct field sub-slicing, and partial direct moves of
  owning fields are rejected.
- A record with a borrowed field cannot be `#[linear]`, cannot contain a linear
  field or an owned payload with a linear obligation, and cannot contain a
  stream, union, callable, task handle or `Box`/`Vec` of a borrowed record.
  Metadata exclusions also apply inside nominal records/enums and owned
  `Box`/`Vec` payloads; wrapping a forbidden field does not bypass them.
- No records with a borrowed field may be stored in containers, unions, enums,
  callable environments or tasks. Borrowed records are lexical values. A
  `Box`/`Vec`/array of a borrowed record stays rejected even when `Box`, `Vec`,
  `Bytes` or an owning enum is allowed as record metadata.
- No self-referential records: constructing `R { owner: value, view:
  &value[..] }` (or the reverse order) is rejected by the ordinary move and loan
  checks.
- Outlives bounds are supported only on executable function signatures. Record
  and alias lifetime parameters keep exact agreement; no variance annotations,
  higher-kinded lifetimes, or lifetime inference from function bodies.
- No general per-field lifetime polymorphism inside function-pointer types.
  Callable arrows deliberately reject borrowed records.
- Elided slice-field lifetimes are not inferred; write `&'a [T]` or
  `&'a mut [T]` with a declared lifetime. Signature result elision remains the
  conservative slice rule.
- The analysis is path-insensitive and conservative. It is an engineering
  milestone, not a proof; both backends and the runtime are trusted.
