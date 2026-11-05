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
so owning, linear, and view elements cannot be matched by value.

Matching a shared borrow (`match &a { ... }`, or a `&DynArray<T, C>` /
`&[T; n <= C]` parameter) binds element references instead of copies, so
owning elements can be matched without moving them:

```rust
let a: DynArray<Box<i64>, 4> = [Box.new(10), Box.new(20), Box.new(12)];
match &a {
    [first, .., last] => Box.read(first) + Box.read(last),   // first: &Box<i64>
    _ => 0,
}
```

An element name binds `&T` into the array's slot, `_` and `..` ignore
elements, and over copyable elements a `..rest` binds a `&[T]` view of the
middle while other sub-patterns (literals, tuples, records, variants) test
copies. Over owning, linear, or view elements only names, `_`, and an unnamed
`..` are accepted. The bindings are shared views rooted at the array's owners:
the array cannot be moved, replaced, or mutated while one is live, and they
cannot outlive the array's scope. Only slice patterns and `_` are accepted for
a borrowed scrutinee; borrows of other types are still not matchable.

Matching an exclusive borrow (`match &mut a { ... }` on a `let mut` array or
field, or a `&mut DynArray<T, C>` / `&mut [T; n <= C]` parameter) binds
`&mut T` per named element and `&mut [T]` for `..rest`:

```rust
fn swap(p: &mut i64, q: &mut i64) -> Unit ! {} { let t = *p; *p = *q; *q = t; }

let mut a: DynArray<i64, 4> = [3, 4, 5];
match &mut a {
    [x, .., y] => swap(x, y),                 // two disjoint &mut i64
    _ => {},
};
match &mut a {
    [x, ..rest] => { *x = *x + 1; Slice.set(rest, 0, 9); },
    _ => {},
};
```

The bindings are pairwise-disjoint loans, like the two sides of
`Slice.split_at_mut`: each binding gets its own split group, so two bindings
(and references derived from them, such as `&mut rest[0]`) may be used and
passed to one call together, while every other access to the array (a read,
a view, `&mut a` again, `DynArray.push`/`set`, a move, or a write through the
reference the array came from) waits for the last use of every binding. A
binding may leave the match; it still cannot outlive the array's scope. A
`&mut` parameter scrutinee is reborrowed, so the parameter is usable again
after the bindings' last use. As with `&mut s[i]`, elements must be
non-owning, non-linear, non-view values: an exclusive reference to an owning
element is rejected. By-value sub-patterns (literals, tuples, records,
variants) test copies of a snapshot taken when the match starts, so a guard
that writes through a binding and then fails does not change what later arms
test; a name may be bound only once, and the same
slice-pattern-or-`_` arm rule applies. The runtime length is not a finite variant tag, so a match
over `DynArray` must contain an unguarded catch-all: `_`, a binding, or a
pattern that is only `..` / `..rest`. The ordinary exhaustiveness check rejects
anything else.

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
  of `[T; N]`. The array may be a local or behind a `&` or `&mut` reference.
  Facts about a local stop applying once `&mut` of it is taken, since writes
  through the reference are invisible to the solver. Native code keeps its bounds trap on the proved path as a
  defensive check that can never fire.
- **Views.** `&a[..]`, `&a[start..end]`, and `&mut` forms behave as for
  `DynArray` and cover exactly `n` elements. A view bound directly to a local
  (`let v = &a[..]`) also records the fact `Slice.len(v) == n`, so
  `Slice.at(v, i, _)` can be proved from facts about `n`.
- **Other operations.** `DynArray.len`, `DynArray.get`, `DynArray.set`, `==`,
  `!=`, and `match` patterns work as for `DynArray`; a `..rest` binding is a
  plain `DynArray<T, C>`. `DynArray.push` and `DynArray.pop` are rejected
  because they would change the length.
- **Signatures and calls.** A parameter or result type may mention a
  runtime-length array anywhere the call site can rewrite it: as the whole
  type, behind `&`/`&mut`, or inside `Vec`, `Box`, tuples, fixed and inline
  arrays, generic records and enums, structural rows, and unions (for
  example `v: &Vec<[i64; n <= 4]>` or `-> Pair<[i64; n <= 4]>`). Each binder
  must be an earlier `i64` parameter of the same function (any `i64`
  parameter for the result). The callee is compiled once, so the
  rebuilt signature type must keep its exact layout. A call is rejected when
  the caller's binders would change a union in it: two members becoming one
  type (`[i64; n <= 4] | [i64; m <= 4]` called as `f(k, k, ...)`, or
  `T | [i64; n <= 4]` with `T = [i64; k <= 4]`), one member absorbing another
  as a width subtype, a union inside a generic record or enum merging, or
  members swapping positions (union member order follows internal type
  identities, so this last case can reject a call with distinct binders;
  avoid unions of runtime-length arrays in signatures when it does). At each call the actual argument for
  that parameter must be the name of an immutable `i64` binding; the callee's
  binder is replaced by the caller's, so `fn f(n: i64, a: [i64; n <= 8])`
  called as `f(k, b)` requires `b: [i64; k <= 8]`, and the result of
  `fn make(n: i64) -> [i64; n <= 8]` called as `make(k)` has type
  `[i64; k <= 8]`. Generic functions, impl methods, and trait items follow
  the same rule: generic inference reads the element type and capacity from
  a runtime-length argument (`fn first<T, C: Nat>(n: i64, a: [T; n <= C])`),
  and a method call substitutes its explicit arguments' binders (the receiver
  is never a binder). A trait and its impl must spell the binder with the
  same parameter name. A trait whose method mentions a runtime-length array
  is not object-safe: a `dyn` call has no static callee to substitute into.
  Foreign signatures cannot mention runtime-length arrays.
- **Recursive instances.** A type argument may not mention a length binder
  of the function being instantiated, as in `go::<[i64; n <= 4]>(...)` inside
  `go`. Each activation has its own `n`, so such an instance would give a
  value built with the outer `n` the inner `n`'s type.
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
container of unbounded length. `Vec<T>` remains the growable owning container
and `&[T]` the borrow for arbitrary lengths. Further limits:

- Runtime-length arrays cannot appear in foreign signatures, `fn` types,
  lambda signatures, methods of a trait used as a `dyn` object, or inside a
  `dyn` or `fn` type in any signature (a call through a type alias that
  expands to one is rejected).
- A trait and its impl must spell a length binder with the same parameter
  name.
- A call is rejected when the caller's binders would change the layout of a
  union in the callee's signature; this can reject a call with distinct
  binders when union members would swap positions.
- A recursive instance cannot take a type argument that names the function's
  own length binder.
- There is no element-wise owning move beyond push/pop of copyable values.
- An exclusive (`&mut`) borrowed pattern cannot bind owning, linear, or view
  elements, and its bindings suspend the whole array (or the record the array
  is a field of), even for disjoint fields of that record. A `&mut [T]`
  result cannot be returned from a `&mut DynArray` parameter.

The implementation is checked by `crates/kush/tests/advanced_types_effects.rs`
and, for generic/method/trait and nested signatures and exclusive patterns,
`crates/kush/tests/runtime_length_extensions.rs`,
with positive push/get/literal/view/pattern/equality execution,
native/reference agreement, owning-prefix cleanup, capacity overflow,
out-of-bounds reads and writes, runtime view bounds, mutable-view aliasing
rejections, field-view aliasing/write-back, owner moves/drops while a view is
live, pattern fallthrough/exhaustiveness/owning-element rejections, and layout
rejection.

## Review

An independent review of the runtime-length array, pattern, slice-element
place, and field-view work found two soundness holes and five smaller issues.
All are fixed, and each has a regression test (`review_*` in
`crates/kush/tests/advanced_types_effects.rs`):

1. A write through a `&mut Record` parameter (`*h = ...`, `h.field = ...`)
   was accepted while a view, element reference, or borrowed-pattern binding
   derived from `h` was live, which could free a matched box. Such writes now
   wait for the derived borrow's last use.
2. A local whose address was taken by `&mut` kept its arithmetic facts (for
   example a loop counter's `0 <= i`), so `Slice.at` could read outside the
   slice. Such a local now leaves the fact system, and `&mut x` in a loop body
   counts as a write of unknown direction.
3. A borrowed match used directly as an outer arm's result was falsely
   rejected; its scrutinee loan now ends with the match.
4. A reference returned from one `split_at_mut` side conflicted with an
   element reference into the other side; call results now keep the side.
5. Diagnostics and limits: two length binders with one name are named apart in
   a mismatch, a literal argument for a runtime-length parameter gets the
   length-proof message, `[..rest]` alone is exhaustive, and `a[i]` works
   through `&mut [T; n <= C]`.

A second independent review covered the extensions (generic, method, trait,
and nested signatures, and exclusive patterns) over five rounds plus a
focused re-check, with local builds. It found seven soundness bugs, each
fixed with a regression test in `crates/kush/tests/runtime_length_extensions.rs`:

1. A recursive call whose type argument named the function's own length
   binder (`go::<[i64; n <= 4]>` inside `go`) gave a value of the outer
   length the inner activation's type. Such instances are rejected; the check
   also covers inherited trait defaults, whose per-impl copy has its own
   binding, and binders inside `dyn` trait arguments.
2. Rebinding a signature type at a call could change its layout: union
   members merged (`f(k, k, ...)` on `[i64; n <= 4] | [i64; m <= 4]`),
   swapped positions, absorbed a width subtype, or merged inside a generic
   record or enum. The rebuilt type must now be isomorphic to the callee's.
3. A type alias expanding to `dyn Tr<[i64; n <= 4]>` hid the binder from
   call-site substitution, so the callee's binder leaked into the caller's
   type. Binder walks now see `dyn` arguments, and such calls are rejected.

Smaller results: recursive calls forwarding their own binder were briefly
falsely rejected by an intermediate fix and are accepted again, and a guard
that writes through an exclusive binding does not change what later arms
test (documented).
