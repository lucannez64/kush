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

## Length-refined fields

Tests: `crates/kush/tests/length_refined_fields.rs`.

A `Vec` field may promise a minimum length:

```kush
const SIZE: i64 = 0x2000;
struct Machine { vram: Vec<u8> where len >= SIZE, log: Vec<u8> }

fn read(m: &Machine, address: u16) -> u8 ! {panic} {
    let at: i64 = Int.convert(address);
    if address < 0x8000 { return 0xFF; }
    if address < 0xA000 { return m.vram[at - 0x8000]; }   // no run-time check
    0xFF
}
```

`N` is a compile-time integer (a literal, a constant, or arithmetic on them).
The promise is kept three ways:

- **Construction checks it once.** Building the record checks the vector's
  length (a `panic` if it is short), so the record literal needs `panic`.
- **Nothing can shorten the field.** `place.clear()` is rejected, and so is
  `&mut place`, since the borrower could shorten it. Elements are written with
  `place[i] = value`; `push`, `set` and `reserve` stay allowed, and
  `place.replace(other)` swaps in another vector after checking its length.
- **Accesses use it.** `place[i]` asks the prover for `0 <= i && i < N` from
  the facts at that point: branch conditions, early returns, masks
  (`x & 0x1FFF` is at most `0x1FFF`), the range of a narrower integer
  (`Int.convert(b)` for a `u8` is `0..=255`), loop conditions, `ensures`
  clauses of called functions and erased ranges on parameters
  (`erased inside: { 0 <= at && at < 0x1FFF }`, proved by every caller). A
  proved read is a plain load and a proved write a plain store; anything else
  keeps the ordinary run-time check, so the program means the same either way.

Facts the prover keeps for this, all checked by certificates like every other
proof:

- a branch that never falls through (`if c { touch(m); return; }`) does not
  erase facts after the `if`, even when it wrote values;
- a `while` loop without `break` exits with its condition false and every
  value at its loop-head version (`while i < n { .. }` gives `i >= n`);
- in a condition that writes nothing, a conjunct the prover cannot read (an
  element read, a call) no longer hides its siblings: in
  `while at > 0 && v[at - 1] > x { .. }` the body knows `at > 0`;
- a call argument without a linear form (an element read) is still a value
  of its parameter type, so `ensures { result == value }` on
  `fn wide(value: u8) -> i64` gives the caller `0 <= result <= 255`.

## Swapping a vector out of a place

`place.replace(new)` (or `Vec.replace(&mut v, new)`) stores `new` in a `Vec`
place and returns the vector it held. Only the two handles move; no element
is copied. It works on fields through references, where moving the field out
is not allowed, and on length-refined fields, where `new`'s length is checked
first. The Game Boy core uses it to lend its finished screen and sound to the
front end without copying them.

`KUSH_PROOF_REPORT=1 kush check` prints how many element accesses were proved
and how many keep a check; `KUSH_PROOF_REPORT=verbose` also lists every access
into a length-refined field that was not proved, with its file and line.

In the Game Boy example, refining video RAM, work RAM, OAM, high RAM, the
screen, the sprite list and wave RAM proves 118 accesses (all memory-bus reads
and writes and every per-pixel access of the renderer). Running 3600 frames of
a commercial game takes 4.9 s instead of 6.6 s with Cranelift; with LLVM's
optimiser the time is unchanged (about 1.2 s), as it already hoists most of
those checks. The I/O registers stay checked: `apu` borrows them as
`&mut Vec<u8>`, which a refined field cannot lend.
