# Runtime-sized inline arrays

Status: implemented for owned inline storage with a compile-time capacity and a
runtime length, contextual literals, and shared slice views over the live
prefix, in the reference evaluator and the Cranelift backend.

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
the live prefix:

```rust
let a: DynArray<i64, 4> = [10, 20, 30];
let all: &[i64] = &a[..];
let middle: &[i64] = &a[1..3];
Slice.len(all) + Slice.get(middle, 0)
```

The descriptor's length is the runtime length word, not the capacity; native
lowering points at the pinned inline storage and reads the live length. An
explicit range is checked against the runtime length in both backends and
requires `panic`; the unchecked `&a[..]` form always covers exactly the live
prefix. Ownership treats the view like any other slice view: the owner cannot be
moved, dropped, assigned, pushed, or popped while the view is live, and a view
cannot escape the owner's lexical scope. Releasing the view at the end of its
block restores the owner for later mutation. Views over owning or linear
elements are rejected because element reads would copy an owner. A mutable
`&mut [T]` view of a `DynArray` is not provided; use the checked `DynArray.set`
write instead.

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
is always a compile-time `Nat`; the length is a runtime word. Patterns over a
`DynArray` are rejected explicitly: the runtime length is not a static variant
tag, so use `DynArray.len` and `DynArray.get`. There is no `DynArray` equality,
mutable view, or element-wise owning move beyond push/pop of owning values.
`Vec<T>` remains the growable owning container and `&[T]` the borrow for
arbitrary lengths.

The implementation is checked by `crates/kush/tests/advanced_types_effects.rs`
with positive push/get/literal/view execution, native/reference agreement,
owning-prefix cleanup, capacity overflow, out-of-bounds reads, runtime view
bounds, view/owner loan rejections, explicit pattern rejection, and layout
rejection.
