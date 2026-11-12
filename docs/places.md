# Constants, places and two-phase borrows

Status: implemented (2026-11-12), motivated by the
[Game Boy emulator example](../examples/gameboy/README.md). Tests:
`crates/kush/tests/places_and_constants.rs`, plus the reworded rejections in
`borrowed_methods.rs`.

These additions make state held in records and containers as direct to use as
locals. None of them adds a new ownership rule: each one is spelled in terms of
the borrows the language already checks, and is described below by what it
means.

## Module-level constants

```kush
pub const SCREEN_WIDTH: i64 = 160;
const ZERO: u8 = 0x80;
const BOTH: u8 = ZERO | 0x10;
```

A constant is a parameterless function marked constant. Each use of its name
(`ZERO`, or `machine.ZERO` from another module) is replaced by its value
expression, checked at the use against the declared type. A literal therefore
compiles to that literal, in every backend. A value that refers to its own
constant, directly or through others, is rejected.

The value is checked where it is used, so its effects are the using function's:
`const MASK: u8 = 1 << 3;` needs `panic` at each use, as the shift itself
would.

## Element access on places

`place[index]` reads an element of a `Vec<T>` or `Bytes` place, including a
field reached through a reference (`m.memory[i]` with `m: &Machine`). It is
the same checked read as `Vec.get(&place, index)` / `Bytes.get(&place, index)`:
the field is borrowed in place, never moved out.

`place[index] = value` writes one copyable element of:

- a `Vec<T>` local, field, or `&mut Vec<T>`: the write is
  `Vec.set(&mut place, index, value)`;
- an inline array or an exclusive `&mut [T]` view: `Slice.set(&mut place[..], index, value)`.

The index and then the value are evaluated first, into hidden locals; only then
is the place borrowed for the write. So `m.memory[i] = m.a` is accepted: the
value reads `m` before the write borrows it. Writing a `Bytes` place by index is
rejected with a pointer to `Slice.set` on a byte view, or to `Vec<u8>`.
Elements that own resources or are linear cannot be replaced this way.

## Field assignment on `let mut` records

`cpu.halted = false` on a `let mut` record local writes that field through an
exclusive borrow of the local, exactly as through an explicit `&mut` receiver;
the same field rules apply (copyable, non-owning, non-borrowed fields). The
value is evaluated before the borrow, so `cpu.a = cpu.a + 1` is accepted. A
field of an immutable binding still cannot be assigned. The prover forgets
what it knew about the local's fields after such a write.

## Methods on fields and through references

A `&self` or `&mut self` method may be called:

- on a field, including a field that owns storage: `m.cartridge.load(address)`
  borrows `m.cartridge` in place, as `&m.cartridge` would;
- through an existing reference: `c.bump()` with `c: &mut Counter` reborrows
  `c`, as passing it to an ordinary function does. A `&mut self` method through
  a shared reference is rejected.

Read-only builtin methods (`len`, `get`, `at`, `copy`, ...) on an owning field
borrow it in place too (`m.memory.len()`), and the mutating `Vec` builtins
`push`, `set`, `clear` and `reserve` on a field update it in place through
`&mut` (`log.items.push(x)`). A by-value method on an owning field is still
rejected: it would move the field out of its record.

## Fields inside owning fields

A field of a field that owns storage is still a place through a reference:
`m.apu.powered` reads, and `m.apu.step = 0` writes, a scalar of the `Apu`
record that `m: &mut Machine` holds, although `Apu` owns vectors. Only the
final field is read or written; moving an owning field out
(`o.inner.log` as a value) is still rejected.

## Disjoint owning fields

Two exclusive borrows of different fields of one record may be live at once,
also when the fields own storage and also through a reference:
`apu.sequence(&mut m.apu, &mut m.io)`. The same field twice is still an
alias and rejected. (Before, a field that owns storage was loaned as its whole
record.)

## Two-phase exclusive borrows in calls

Passing an exclusive reference (`m`, `&mut x`, `&mut m.field`) has no side
effect, so a call may take it after its other arguments are evaluated. When
another argument reads the same root, as in `push(m, m.pc)`, the arguments
that are not plain places are evaluated first, in their written order, into
hidden locals; the reference is taken last. Without this the reborrow would be
live while `m.pc` is read, and the read would be rejected.

This applies to ordinary calls, method calls and the `Vec` builtins. Arguments
with effects keep their relative order. A call whose early argument is itself a
reference or view is left as written, since a hidden local cannot carry its
lifetime.

## Records without size limits

A nominal record (`struct`) has no limit on its width, its number of fields,
or the words it takes as a by-value argument. Its cost is in by-value copies,
which the program chooses: pass a large state by reference. Other inline
layouts (arrays, tuples, enums, unions, structural records) keep their 32-word
limit.
