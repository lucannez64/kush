# Runtime-sized inline arrays

Status: implemented for owned inline storage with a compile-time capacity and a
runtime length, contextual literals, equality, shared and exclusive slice views
over the live prefix (including views through a record field), and
length-checked patterns, in the reference evaluator and the Cranelift backend.
Runtime-length arrays `[T; n <= C]`, whose length is bound to an immutable
`i64` runtime index, use the same storage and add length proofs; see
[below](#runtime-length-arrays-t-n--c).

```rust
fn main() -> i64 ! {panic} {
    let mut a: DynArray<i64, 4> = DynArray.new::<i64, 4>();
    let mut i = 0;
    while i < 3 {
        a = DynArray.push(a, i * 10);
        i = i + 1;
    }
    DynArray.len(&a) + DynArray.get(&a, 0) + DynArray.get(&a, 2)
}
```

The capacity is a compile-time natural; only the length is dynamic. The value
is inline: no heap allocation and no hidden pointer to a dynamic stack frame.

## Surface API

```rust
DynArray.new::<T, capacity>()        -> DynArray<T, capacity> ! {}
DynArray.push(a, value)              -> DynArray<T, capacity> ! {panic}
DynArray.set(a, index, value)        -> DynArray<T, capacity> ! {panic}
DynArray.pop(a)                      -> (DynArray<T, capacity>, T) ! {panic}
DynArray.len(&a)                     -> i64 ! {}
DynArray.get(&a, index)              -> T ! {panic}   // T must be copyable
```

`DynArray.new` starts with length zero. `DynArray.push` evaluates the array,
then the element, checks `length < capacity`, stores the element at the current
length, increments the length, and returns the same inline storage. `set`
checks `index < length` and overwrites one initialized copyable slot without
changing the length. `pop` checks `length > 0`, clears the last slot, decrements
the length, and returns the array together with the removed copyable value.
`len` and `get` borrow the array for the duration of the call. `get`, `set`, and
`pop` copy copyable elements; owning, linear, and view elements are rejected
instead of being copied or duplicated.

`==` and `!=` compare two `DynArray<T, capacity>` values of the same type by
runtime length and live elements. Elements must be one-word comparable values:
`i64`/fixed-width integers, `f32`/`f64`, `Bool`, or `Char`. A length mismatch is
unequal without reading a slot. Floats compare numerically, so `NaN != NaN` and
`-0.0 == 0.0` follow the language's scalar `==`. Owning, linear, view, and
multi-word elements are explicit equality rejections; narrow with `DynArray.len`
and `DynArray.get` instead.

## Literals

A contextual inline-array literal constructs a `DynArray` when the expected type
is `DynArray<T, capacity>`:

```rust
let a: DynArray<i64, 4> = [10, 20, 30];
let empty: DynArray<i64, 2> = [];
```

The literal's element count becomes the runtime length, and its static count
must not exceed the capacity; a longer literal is a compile-time diagnostic.
The literal is checked as the same construction sequence as `new` followed by
one `push` per element. Because the count is statically bounded, every reused
push guard is unreachable, so a literal does not require the `panic` effect and
cannot overflow at run time. Owning elements are accepted and a partially
constructed literal is destroyed as an owning prefix if element evaluation
fails. Elements follow the same non-borrow, non-linear, non-task rule as
`DynArray<T, capacity>` itself.

## Slice views

`&a[..]` and `&a[start..end]` produce the ordinary shared slice type `&[T]` over
the live prefix. `&mut a[..]` and `&mut a[start..end]` produce `&mut [T]`; they
require a `let mut` owner and are exclusive capabilities. The owner must be a
direct local binding (or another slice view); a `DynArray` field of a direct
local record may also be viewed:

```rust
let a: DynArray<i64, 4> = [10, 20, 30];
let all: &[i64] = &a[..];
let middle: &[i64] = &a[1..3];
Slice.len(all) + Slice.get(middle, 0)
```

```rust
let mut a: DynArray<i64, 4> = [10, 20, 30];
{
    let view: &mut [i64] = &mut a[1..3];
    Slice.set(view, 0, 7);       // writes a[1] in place
}
let b: &[i64] = &a[..];
```

The descriptor's length is the runtime length word, not the capacity; native
lowering points at the pinned inline storage and reads the live length. An
explicit range is checked against the runtime length in both backends and
requires `panic`; the unchecked `&a[..]` form always covers exactly the live
prefix. Ownership treats the view like any other slice view: the owner cannot be
moved, dropped, assigned, pushed, set, popped, or read while the view is live,
and a view cannot escape the owner's lexical scope. Releasing the view at the
end of its block restores the owner for later mutation. Two exclusive views of
the same owner, or a shared and an exclusive view, cannot coexist. Views over
owning or linear elements are rejected because element reads would copy an
owner. `Slice.set` requires `&mut [T]`; it checks the runtime length and writes
exactly one initialized slot.

A view through a record field (`&r.a[..]`, `&mut r.a[..]`, including nested
fields such as `&mut r.inner.a[1..]`) aliases the record's inline storage. The
record may be:

- a direct local binding, which both backends pin; an exclusive field view
  requires `let mut` on the record;
- a record reference (`h: &Holder`, `h: &mut Holder`, a stored reference, or
  a reference to a `Vec` element), which views the referent in place; an
  exclusive view needs `&mut`, and a shared reference is never upgraded. A
  `&'a Holder` parameter backs a returned `&'a [T]` field view;
- a temporary or call result (`&make().xs[..]`), which is hoisted into hidden
  storage for the enclosing block; the view cannot escape that block, and the
  hidden record's owning fields are dropped exactly once at block end.

```rust
fn tail<'a>(h: &'a Holder) -> &'a [i64] ! {panic} { &h.xs[1..] }
fn bump(h: &mut Holder) -> Unit ! {panic} {
    let view: &mut [i64] = &mut h.xs[1..];
    Slice.set(view, 0, 70);
}
```

The field loan (through the reference's own loan, for a reference root) blocks
replacing or mutating the record or the field while the view is live, and two
exclusive views of one field conflict.

## Patterns

A `match` on a `DynArray<T, capacity>` may use length-checked slice patterns:

```rust
match a {
    [] => 0,
    [x] => x,
    [x, y] => x + y,
    [first, ..rest] => first + DynArray.len(&rest),
    _ => 99,
}
```

`[]`, `[x]`, `[x, y]` require exactly that live length. A `..` matches any
remaining length, and patterns after it match the trailing live elements,
counted back from the runtime length:

```rust
match a {
    [first, .., last] => first + last,          // needs length >= 2
    [..mid, 9] => DynArray.len(&mid),           // last element is 9
    [x, ..mid, y, z] => x + y + z,
    _ => 0,
}
```

`..rest` additionally binds the middle as a fresh `DynArray<T, capacity>`
containing copies of the elements between the prefix and the suffix (the
original capacity bound is kept). A pattern has at most one `..`, and its
prefix plus suffix may not exceed the capacity. Element sub-patterns are
ordinary patterns, so literals, tuples, fixed arrays, records, enum variants,
and nested `DynArray` patterns all work elementwise, and guards may fall
through to a later arm. Elements must be copyable one-word or concrete values,
so owning, linear, and view elements cannot be matched by value. The runtime length is not a finite variant tag, so a match
over `DynArray` must end in an unguarded catch-all; the ordinary exhaustiveness
check rejects anything else.

## Runtime-length arrays `[T; n <= C]`

A runtime-length inline array names its length with an immutable runtime `i64`
binding and states a compile-time capacity:

```rust
fn pick(n: i64, i: i64, erased ok: { 0 <= i && i < n && n <= 8 }) -> i64 ! {} {
    let a: [i64; n <= 8] = Array.fill(n, 7);   // proved 0 <= n <= 8: no check
    a[i]                                       // proved 0 <= i < n: no panic
}

fn sum_all(n: i64, erased ok: { 0 <= n && n <= 8 }) -> i64 ! {panic} {
    let a: [i64; n <= 8] = Array.fill(n, 2);
    let mut i = 0;
    let mut acc = 0;
    while i < n {
        acc = acc + a[i];   // the read is proved; only the checked `+` needs panic
        i = i + 1;
    }
    acc
}
```

This follows the spec's storage rule (section 12): the layout is static, and the
runtime-varying length is carried with the storage. Runtime-sized stack
allocation remains unavailable, as section 10 requires.

Semantics:

- **Length binder.** `n` must name an immutable `i64` parameter or `let` local
  in scope. `let mut n` is rejected: the value the type talks about may never
  change. The capacity `C` is an ordinary compile-time length expression.
- **Layout.** Exactly the `DynArray<T, C>` layout: word zero holds the runtime
  length, which always equals `n`, followed by `C` inline slots. The same
  capacity and 32-word limits apply, the same element restrictions apply (no
  borrows, views, tasks, or linear values), and nothing is allocated.
- **Type identity.** The binder is part of the type. `[i64; n <= 8]`,
  `[i64; m <= 8]`, `[i64; n <= 4]`, and `DynArray<i64, 8>` are four different
  types, so two values of one type always have the same length. There is no
  implicit conversion between them.
- **Construction.** `Array.fill(n, value)` copies one copyable value into the
  first `n` slots; the capacity comes from the expected type or from
  `Array.fill::<T, C>(n, value)`. When the facts in scope prove
  `0 <= n && n <= C`, construction has no check and needs no effect. Otherwise
  it checks the bound at run time and requires `panic`. A contextual literal
  `[e1, ..., ek]` builds a runtime-length array only when the facts prove
  `n == k`; there is no runtime fallback for literals. Literal elements may
  own resources.
- **Drop.** Exactly the `DynArray` rule: the first `n` slots are destroyed
  once, and slots past the length are never read or dropped.
- **Indexing.** `a[i]` copies a copyable element. When the facts prove
  `0 <= i && i < n`, the read is proof-based and needs no `panic` effect;
  otherwise it is a checked read that requires `panic`, like dynamic indexing
  of `[T; N]`. Native code keeps its bounds trap on the proved path as a
  defensive check that can never fire.
- **Views.** `&a[..]`, `&a[start..end]`, and `&mut` forms behave as for
  `DynArray` and cover exactly `n` elements. A view bound directly to a local
  (`let v = &a[..]`) also records the fact `Slice.len(v) == n`, so
  `Slice.at(v, i, _)` can be proved from facts about `n`.
- **Other operations.** `DynArray.len`, `DynArray.get`, `DynArray.set`, `==`,
  `!=`, and `match` patterns work as for `DynArray`; a `..rest` binding is a
  plain `DynArray<T, C>`. `DynArray.push` and `DynArray.pop` are rejected
  because they would change the length.
- **Signatures and calls.** A parameter or result type may be a runtime-length
  array, or a direct `&`/`&mut` reference to one, whose binder is an earlier
  `i64` parameter of the same function. At each call the actual argument for
  that parameter must be the name of an immutable `i64` binding; the callee's
  binder is replaced by the caller's, so `fn f(n: i64, a: [i64; n <= 8])`
  called as `f(k, b)` requires `b: [i64; k <= 8]`, and the result of
  `fn make(n: i64) -> [i64; n <= 8]` called as `make(k)` has type
  `[i64; k <= 8]`. Generic functions, methods, and trait items cannot mention
  runtime-length arrays in their signatures.
- **First-class functions.** Lambda signatures and `fn`/`once fn` types cannot
  mention runtime-length arrays, and a function whose signature does cannot be
  used as a value. An indirect call cannot substitute the caller's binder, so
  allowing it would let two calls produce one type with two lengths.

Plain `[T; n]` with a runtime `n` stays a compile-time diagnostic, which now
suggests `[T; n <= C]`.

Why this is sound: a value of type `[T; n <= C]` can only be created by a
construction that establishes `length == n` for the current value of `n`, or by
a call whose binder was replaced by a caller binding with the same value. `n`
cannot be reassigned. The language has no deferred local type inference
(`Vec.new()` needs an annotation and lambdas declare their result types), so a
binding declared outside `n`'s scope can never be given a type that mentions
`n`. Values from two activations of one binder (two loop iterations or two
recursive calls) can therefore never meet at one type. Proof-based reads use
only facts about the binder that is in scope.

## Layout and lifetime contract

The checked layout is:

```text
word 0:                 runtime length (0..=capacity)
words 1 .. 1 + capacity: inline element slots
```

- `capacity` is `1..=31` and `1 + capacity * width(T) <= 32` words; exceeding
  either bound is a layout diagnostic.
- Elements cannot be borrows, slice views, borrowed records, task handles, or
  linear obligations. This keeps every slot a concrete inline value and makes
  `DynArray` representable in registers, locals, aggregates, and returns.
- Words at or beyond the runtime length are uninitialized by construction and
  are never read, copied, or dropped. The native drop procedure guards each
  capacity slot with `length > slot`; the reference evaluator drops only its
  item list. An owning prefix is released exactly once, as the allocation
  stats and native/reference tests show.
- A `DynArray` value may be moved, assigned, passed, and returned. Because its
  storage is inside the value, there is no escaping stack slot. Shared views
  borrow the pinned inline storage and are limited to the owner's lexical
  lifetime; they cannot be stored in data.
- Pushing past `capacity` is a runtime panic in both backends. There is no
  silent growth and no fallback allocation.

## Limits

This is not an unbounded `[T; n]` with a runtime `n`, not a dynamically sized
stack allocation with a hidden layout descriptor, and not a general dependent
array. The capacity is always a compile-time `Nat`; the length is a runtime
word. A runtime array length without a capacity, such as `[i64; n]`, remains
an explicit diagnostic that suggests `[T; n <= C]`; use `Vec<T>` for an owned
container of unbounded length. Runtime-length arrays cannot appear in generic
function, method, trait, or foreign signatures, in `fn` types, or in lambda
signatures, and a signature may only use them as a whole parameter/result or
behind one reference. There is no element-wise owning move beyond
push/pop of copyable values, and no borrowed element pattern. `Vec<T>` remains the growable owning container and `&[T]` the borrow
for arbitrary lengths.

The implementation is checked by `crates/kush/tests/advanced_types_effects.rs`
with positive push/get/literal/view/pattern/equality execution,
native/reference agreement, owning-prefix cleanup, capacity overflow,
out-of-bounds reads and writes, runtime view bounds, mutable-view aliasing
rejections, field-view aliasing/write-back, owner moves/drops while a view is
live, pattern fallthrough/exhaustiveness/owning-element rejections, and layout
rejection.
