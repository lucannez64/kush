# Runtime-sized inline arrays

Status: implemented for owned inline storage with a compile-time capacity and a
runtime length, in the reference evaluator and the Cranelift backend.

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
DynArray.len(&a)                     -> i64 ! {}
DynArray.get(&a, index)              -> T ! {panic}   // T must be copyable
```

`DynArray.new` starts with length zero. `DynArray.push` evaluates the array,
then the element, checks `length < capacity`, stores the element at the current
length, increments the length, and returns the same inline storage. `len` and
`get` borrow the array for the duration of the call, so a view into the dynamic
storage cannot escape the lexical scope of its owner. `get` copies a copyable
element; owning, linear, and view elements are rejected instead of being copied.
There is no `pop`, `set`, or slice view yet.

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
  storage is inside the value, there is no escaping stack slot. Borrows are
  limited to the `len`/`get` call and cannot be stored in data.
- Pushing past `capacity` is a runtime panic in both backends. There is no
  silent growth and no fallback allocation.

## Limits

This is not `[T; n]` with a runtime `n`, not a dynamically sized stack allocation
with a hidden layout descriptor, and not a general dependent array. The capacity
is always a compile-time `Nat`; the length is a runtime word. There is no
`DynArray` literal, pattern, equality, view, `pop`, `set`, or element-wise owning
move. `Vec<T>` remains the growable owning container and `&[T]` the borrow for
arbitrary lengths.

The implementation is checked by `crates/kush/tests/advanced_types_effects.rs`
with positive push/get execution, native/reference agreement, owning-prefix
cleanup, capacity overflow, out-of-bounds reads, and layout rejection.
