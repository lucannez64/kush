# Grade-zero runtime erasure

Status: implemented for executable `let`/assignment bindings. `@[0]` is both a
use restriction and an erasure annotation: the initializer is still evaluated
because Kush is strict, but no runtime local, store, read, cleanup slot, or
allocation is emitted for the binding. Every runtime observation remains a
compile-time error.

## Initializer effects are preserved by contract

An erased binding does not erase its initializer's effects:

```kush
fn main() -> i64 ! {io, panic} {
    let value: i64 @[0] = { print_i64(7); 1 };
    42
}
```

Both backends print `7` and exit with status `42`. The initializer is evaluated
in source order, may panic, may allocate, and may perform I/O exactly as an
ordinary expression. Allocation diagnostics remain balanced:

```kush
fn main() -> i64 ! {alloc, panic} {
    let value: i64 @[0] = Box.take(Box.new(9));
    42
}
```

This records one allocation and one deallocation in both the reference evaluator
and native execution. Erasure removes the *binding*, not the computation that
produced its value.

## Storage and backend behavior

- Native lowering evaluates the initializer, consumes its temporary resource,
  and emits neither a store nor a local activation. Because the binding is never
  read or assigned again, no native stack slot is materialized for it.
- The reference evaluator evaluates and consumes the initializer, then skips
  `store_local`, activation, and the frame's cleanup list for the slot. Its frame
  is a fixed-size host vector, not program-visible storage.
- Assignment to an erased binding evaluates the replacement for effects and
  does not store it.
- `@[0]` on an owning or intrinsically linear value remains rejected: silently
  discarding storage is never allowed. Use an owning `@[1]` contract instead.
- A custom algebra's zero element (`@[Algebra.Zero]`) is erased the same way.
- Parameter `@[0]` bindings keep their ABI slot because the argument already
  exists at the call boundary; the callee still cannot read, move, or borrow it.
  This is a use restriction, not an ABI rewrite. Result `@[0]` remains rejected.

## Guarantees and non-guarantees

Guaranteed:

- no runtime observation of the erased binding;
- initializer effects and their order preserved;
- allocation/deallocation balance and backend agreement;
- no source-level storage or cleanup required for the binding.

Not claimed:

- removal of an argument already passed across the ABI;
- elimination of computation inside the initializer;
- a runtime check or tag for erased bindings;
- erasure of proof terms beyond the existing erased-parameter mechanism.

## Tests

`crates/kush/tests/grade_zero_erasure.rs` covers observable I/O, allocation
balance, custom-algebra zero, rejection of reads/derivations, acceptance of the
zero-use form, and rejection of owning zero grades in both backends.
