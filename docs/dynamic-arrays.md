# Runtime-sized inline arrays

Status: implemented for owned inline storage with a compile-time capacity and a
runtime length, contextual literals, equality, shared and exclusive slice views
over the live prefix (including views through a record field), and
length-checked patterns, in the reference evaluator and the Cranelift backend.

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
record must be a direct local binding, so both backends can pin it; a temporary,
call result, or reference-based record place is rejected. The field loan blocks
replacing or mutating the record while the view is live, and an exclusive field
view requires `let mut` on the record.

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

`[]`, `[x]`, `[x, y]` require exactly that live length. A trailing `..` matches
any remaining length; `..rest` additionally binds the tail as a fresh
`DynArray<T, capacity>` containing copies of the remaining elements (the
original capacity bound is kept). Literal sub-patterns are checked elementwise,
and guards may fall through to a later arm. Only a trailing rest is supported;
a suffix after the rest is an explicit rejection. Elements must be copyable
one-word or concrete values, so owning, linear, and view elements cannot be
matched by value. The runtime length is not a finite variant tag, so a match
over `DynArray` must end in an unguarded catch-all; the ordinary exhaustiveness
check rejects anything else.

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

This is not `[T; n]` with a runtime `n`, not a dynamically sized stack allocation
with a hidden layout descriptor, and not a general dependent array. The capacity
is always a compile-time `Nat`; the length is a runtime word. A runtime array
length in a type annotation such as `[i64; n]` remains an explicit diagnostic:
use `Vec<T>` for an owned runtime-sized container or `DynArray<T, capacity>` for
inline storage with a static bound. There is no element-wise owning move beyond
push/pop of copyable values, no view of a `DynArray` inside a reference-based
record place, no suffix after a `..` pattern, and no recursive/borrowed element
pattern. `Vec<T>` remains the growable owning container and `&[T]` the borrow
for arbitrary lengths.

The implementation is checked by `crates/kush/tests/advanced_types_effects.rs`
with positive push/get/literal/view/pattern/equality execution,
native/reference agreement, owning-prefix cleanup, capacity overflow,
out-of-bounds reads and writes, runtime view bounds, mutable-view aliasing
rejections, field-view aliasing/write-back, owner moves/drops while a view is
live, pattern fallthrough/exhaustiveness/owning-element rejections, and layout
rejection.
