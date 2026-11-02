# Borrowed slices, including exclusive mutable views

`&[T]` is a scoped shared view and `&mut [T]` is an exclusive move-only view over
an inline array `[T; N]`, an owned `Vec<T>`, an owned `Bytes`, or another
shared or exclusive slice view. A view stores a private four-word representation
`(data pointer, length, element stride, byte-elements flag)`. Views perform no
program-heap allocation: vector/byte-buffer storage is pointed at directly, while
an inline array local is pinned once to a private stack cell so the view has a
stable address and mutable writes are visible through the owner. Sub-slicing any
view and dropping it allocate and copy nothing; indexing a copyable element
copies only that element.

Explicit function lifetimes and checked borrowed returns are described in
[lifetimes.md](lifetimes.md). Shared views use last-use loan release; mutable
views are exclusive capabilities whose children suspend the parent until the
child's last use.

```rust
fn sum(view: &[i64]) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = 0;
    while i < Slice.len(view) {
        acc = acc + Slice.get(view, i);
        i = i + 1;
    }
    acc
}

fn main() -> Unit ! {io, panic} {
    let values: [i64; 5] = [10, 20, 30, 40, 50];
    let middle: &[i64] = &values[1..4];
    print_i64(Slice.len(middle));
    print_i64(middle[0]);
    print_i64(sum(middle[1..]));
}
```

Run `cargo run -p kush -- run examples/slices.kush`.

## Surface operations

- `&owner[..]`, `&owner[start..]`, `&owner[..end]`, and
  `&owner[start..end]` create a view. Omitting `start` means `0`; omitting
  `end` means the owner's current length. A bare `owner[start..end]` is also
  accepted, but the `&` form mirrors Rust.
- `view[start..end]` sub-slices an existing view and keeps the same element
  type and backing storage. Sub-slices are flattened, not nested handles.
- `Slice.len(view)` returns the number of elements for shared and mutable views.
- `Slice.get(view, index)` and `view[index]` copy one element after a runtime
  bounds check. They require the `panic` effect.
- `Slice.try_get(view, index)` copies one element and returns the conventional
  `Option<T>` (`None` for a negative, empty, or out-of-bounds index, including
  `i64::MAX`; `Some(value)` otherwise). It has no effects of its own: it never
  panics, allocates, or suspends. The view and index expressions are still
  evaluated normally, so their effects are preserved.
- `Slice.set(view, index, value)` writes a copyable element through an exclusive
  `&mut [T]` view after a runtime bounds check. It requires `panic` and rejects a
  shared `&[T]` view.
- `let (left, right) = Slice.split_at_mut(view, mid);` creates two checked,
  disjoint exclusive siblings over `[0, mid)` and `[mid, len)`. The pair is a
  restricted `let` form, not a storable value. See
  [lifetimes.md](lifetimes.md#checked-disjoint-mutable-splits).
- `Slice.at(view, index, _)` copies one element without a runtime check. The
  call needs an erased proposition such as
  `{ 0 <= index && index < Slice.len(view) }`; the arithmetic solver proves it
  from contextual facts, and the discharged certificate is re-checked.
- Dynamic indexing of an inline array, `array[index]`, lowers to a whole-array
  view plus a checked element read. It requires `panic`. A constant in-range
  index is still projected at compile time and does not need `panic`.
- `Slice.len(...)` may appear in erased propositions. As with `Bytes.len` and
  `Vec.len`, the term is tied to the slice-view local and its fact version.

```kush
enum Option<T> { None, Some(T) }

let view: &[i64] = &values[..];
match Slice.try_get(view, index) {
    Option.Some(value) => print_i64(value),
    Option.None => print_i64(-1),
}
```

Only copyable element types can be indexed or copied. Views over arrays, vectors,
bytes, or slices whose elements own resources or are linear are rejected, since
this interface cannot move an element out through a slice view.

`Bytes` stores bytes, so `&bytes[..]` has type `&[i64]`; each element is the
numeric byte value `0..=255` and the runtime stride is one byte. Inline arrays
and `Vec<T>` use the element's private word width as their stride.

## Effects and bounds

- `Slice.len` and `Slice.try_get` have no effects. `Slice.try_get` preserves
  the effects of its view and index arguments.
- `Slice.get`, `Slice.set`, `Slice.split_at_mut`, `view[index]`, dynamic
  `array[index]`, and a range whose bounds are not compile-time constants
  require `panic`.
- `&array[..]` and compile-time-valid constant array ranges are checked while
  compiling and need no `panic`.
- Out-of-bounds checks are real: the reference evaluator returns a `panic:`
  diagnostic and native code aborts. `Slice.at` is only for a proved bound; an
  internal failure there is a compiler bug.
- Construction and element reads allocate nothing. A `#[noalloc]` function may
  take `&[T]` or `&mut [T]`, call the slice operations, sub-slice views, and
  return a view tied to a parameter lifetime.

## Ownership and lifetime boundary

Binding a shared view to a local extends a loan on the owner while that view or
any alias can still be used. A checked backward liveness fixed point releases
the loan at the last use rather than only at block end:

```rust
let mut values: Vec<i64> = Vec::new();
values = Vec.push(values, 10);
{
    let view: &[i64] = &values[..];
    print_i64(Slice.len(view));
} // the loan ends here
values = Vec.push(values, 20); // allowed
```

While a loan is live the owner cannot be moved, dropped, or replaced:

```rust
let view: &[i64] = &values[..];
values = Vec.push(values, 20); // rejected
```

Copying a shared view to another immutable binding is allowed and adds a second
alias; the owner is released only after every alias's checked last use. Passing a
view to a function is call-scoped unless the function declares a matching
lifetime and returns a borrowed view. A helper's borrowed return is tied to the
caller's original storage, not to callee temporaries. The checker also rejects:

- returning a shared view without a resolvable result lifetime (explicitly
  annotated, or conservatively elided from one distinct input borrow), or with a
  lifetime not bound to a slice parameter;
- returning a view of a local owner or temporary;
- storing a view in a `Box`, `Vec`, fixed array, or enum; a record may store
  shared `&'a [T]` fields only when it declares the field lifetimes (see
  [borrowed and mixed records](borrowed-records.md));
- matching a view, assigning it to a `let mut` slice binding, or capturing it
  by a closure outside the scoped borrowed-capture form described below;
- a view that would escape the lexical scope of its owner (for example a block
  tail that borrows an array declared inside that block);
- a `break` value of slice type;
- creating a view of an owning/linear element array.

A scoped borrowed-capture `once fn` may hold a shared or exclusive view, but only
as a direct `let` initializer or immediate callee. It must be called or dropped
inside that scope; it cannot be moved, returned, stored, passed to another
function, or captured by a task. While it is callable it keeps the same
parent/owner suspension as the view it captured. See
[lifetimes.md](lifetimes.md#scoped-borrowed-closure-captures).

An exclusive `&mut [T]` view is move-only. While it is live and not suspended,
the owner cannot be read, moved, dropped, replaced, shared-borrowed, or viewed a
second time. Mutable views cannot be copied or stored in data; capturing one in
a scoped closure moves the capability into that closure.
`Slice.len`/`get`/`try_get`/`at`/`set` reborrow the capability for that call;
passing the view to an ordinary function transfers it.

A mutable view may be narrowed with `&mut parent[1..]`, and a function may return
`&'a mut [T]` when the result lifetime is tied to an exclusive parameter. The
parent is retained and suspended while the child is live, then becomes usable
again at the child's checked last use. A shared child `&parent[..]` may be
derived from an exclusive parent and suspends it too; shared storage is never
upgraded to mutable.

`Slice.split_at_mut` is the one way to obtain simultaneous disjoint exclusive
siblings. The midpoint is checked at runtime, both children inherit the
parent's suspension, and their descendants retain the split side. The exemption
from sibling conflicts applies only to descendants of opposite sides of the
same checked split. Two independently written mutable ranges over one owner are
still rejected, even when their literal bounds look disjoint.

These rules are deliberately conservative. There is no general lifetime
inference beyond the single-input signature elision described in
[lifetimes.md](lifetimes.md#conservative-signature-elision), no borrowed
owner-reference returns, and no general disjoint-range inference. The checker
rejects an unsupported escape rather than assuming it is safe.

## Runtime models

The reference evaluator keeps a host-side shared cell for an inline array once a
view aliases it, or a borrowed `Vec`/`Bytes` heap handle otherwise. It does not
copy vector/byte-buffer heap storage and counts no program allocation for a view.
The native backend pins an inline array local to a private stack cell so views
point at the real local storage; `Vec`/`Bytes` views point directly into the
owner's buffer. The four-word slice representation is a private ABI detail.
Returned views and split children carry the same pointer/owner provenance back
to the caller; splitting adjusts only the two views' starts and lengths.

## Remaining limitations

- `&mut [T]` is supported, including mutable sub-views, mutable borrowed
  returns tied to explicit lifetimes, and checked `Slice.split_at_mut` pairs.
  General dynamic range reasoning and storage of split pairs remain
  unsupported.
- Borrowed slice returns use explicit lifetime annotations or conservative
  single-input elision. Borrowed owner references (`&Box`, `&Vec`, `&Bytes`)
  still cannot be returned.
- Views cannot be stored in data other than a declared-lifetime record with
  shared or exclusive slice fields, and cannot be carried through union
  alternatives. There is no general lifetime inference beyond single-input
  slice-result elision, and function arrow types do not describe borrows.
- Slice patterns with `..` are still array-only and require exact lengths; a
  runtime slice cannot be destructured.
- Only copyable elements can be read. Moving an owning element out of a view
  would require a distinct API.
- `Bytes` has a byte-oriented model; there are no typed packed slices beyond
  `&[i64]` byte values.
- Slice views cannot be union alternatives, so a view cannot escape its lexical
  owner through a heterogeneous union. See [subtyping.md](subtyping.md).
- `Slice.get` and indexing still panic out of bounds; `Slice.try_get` is the
  fallible option-returning read. `Slice.at` remains the proof-only unchecked
  read. `Slice.try_get` accepts the exact conventional
  `enum Option<T> { None, Some(T) }` shape in either declaration order, like
  the `Result` and `TaskExit` conventions; a malformed `Option` is rejected.
  The `Option` declaration must be visible in the caller's scope (for example
  through `use std.option.Option`); another module's private `Option` is never
  selected as a fallback.
- Explicit const-generic length specialization and symbolic array lengths are
  implemented for inline arrays (see
  [dependent-indices.md](dependent-indices.md)); a length that is genuinely
  runtime-dependent is still rejected rather than becoming a dynamic inline
  layout, so use `Vec<T>` or a `&[T]` view in that case.
- `Slice.at` proofs are integer difference constraints over named slice locals.
  They do not transport equality through runtime data or work on arbitrary
  slice expressions.
- No implicit coercion from `[T; N]` to a slice; a view must be created
  explicitly. There is no implicit conversion from a `Vec<T>`/slice to a
  fixed-length array either.
