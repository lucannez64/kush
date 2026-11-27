# 9. Proofs

Kush has two proof systems that do not yet talk to each other
([proof-systems.md](../proof-systems.md)). **Arithmetic facts** are proved
automatically about the running program; the **logical kernel** checks
explicit proofs about mathematical values. Planned (decided, P-A): the kernel
goes behind the arithmetic facts, so a kernel lemma can discharge what the
solver cannot (PROOF-*), and the kernel checks the solver's certificates
(FND-PROOF-TRUST).

## Arithmetic facts

A proposition `{ ... }` is a combination (`&&`, `||`, `!`, `!=`) of linear
integer comparisons over locals, parameters, constants, `Bytes.len(x)` /
`Slice.len(x)` / `Vec.len(x)`, record field paths and enum tests. Products of
two variables, `/`, `%` and floats are outside the fragment.

### Erased preconditions

An `erased` parameter is a proof obligation for the caller. The caller writes
`_` and the compiler proves it from the facts known at the call: branch
conditions, guards, loop conditions, early exits, earlier preconditions and
`ensures`. Proofs have no run-time representation.

```kush eval
fn digit(n: i64, erased q: { 0 <= n && n < 10 }) -> i64 ! {} { n + 48 - 48 }

fn main() -> Unit ! {io} {
    let x = 7;
    if x >= 0 && x < 10 {
        print_i64(digit(x, _));
    }
}
```

```output
7
```

```kush reject
fn digit(n: i64, erased q: { 0 <= n && n < 10 }) -> i64 ! {} { n }
fn main() -> i64 ! {} { let x = 12; digit(x, _) }
// error: cannot prove
```

```kush reject
fn nonneg(x: i64, erased q: { x >= 0 }) -> i64 ! {} { x }
fn square(a: i64, erased q: { 0 <= a && a <= 100 }) -> i64 ! {} {
    let s = a * a;
    nonneg(s, _)
}
fn main() -> i64 ! {} { square(3, _) }
// error: cannot prove 'x >= 0'
```

When the prover fails, the fix today is a run-time check that establishes
the fact (`if s >= 0 { ... }`); a hand-written proof cannot be supplied
(planned: PROOF-LEMMAS).

### Checks the prover removes

Indexing (`a[i]`, `v.get(i)`) and checked arithmetic keep a run-time check
unless the facts prove it unnecessary. `Slice.at(v, i, _)`,
`Bytes.at(b, i, _)` and `Vec.at(v, i, _)` *require* the proof and never
check. `KUSH_PROOF_REPORT=1` prints how many accesses were proved and
checked; `kush fuzz` generates inputs aimed at the checks that remain
([proof-fuzz.md](../proof-fuzz.md)). `KUSH_KEEP_PROVED_CHECKS=1` builds
a program as if its proofs removed nothing (the proofs are still checked),
to measure what they buy ([benchmarks/proofs](../../benchmarks/proofs/README.md)).

```kush eval
fn third(v: &[i64]) -> i64 ! {} {
    if v.len() > 2 { Slice.at(v, 2, _) } else { 0 }
}

fn main() -> Unit ! {io} {
    let a: [i64; 3] = [1, 2, 3];
    print_i64(third(&a[..]));
}
```

```output
3
```

### Postconditions and invariants

`ensures` clauses state facts about the result; they are proved at every
return and given to every caller. `ensures result => { P }` and `ensures
!result => { P }` describe a `Bool` result, and `ensures Variant(x) => { P }`
an enum result. A predicate (a `Bool` function with exactly a `result` and a
`!result` clause) may be used inside propositions.

```kush eval
fn clamp(x: i64) -> i64 ! {} ensures { 0 <= result && result <= 255 } {
    if x < 0 { 0 } else if x > 255 { 255 } else { x }
}

fn byte(n: i64, erased q: { 0 <= n && n <= 255 }) -> i64 ! {} { n }

fn main() -> Unit ! {io} {
    print_i64(byte(clamp(300), _));
}
```

```output
255
```

A `while` loop may state an invariant, proved on entry and preserved by the
body: `while i < n invariant { 0 <= i && i <= n } { ... }`.

### Length-refined vectors

A `Vec` field or `&Vec` / `&mut Vec` parameter may promise a minimum
length, `data: Vec<u8> where len >= 64`. Construction checks it once,
nothing can shorten the vector, and indexing uses it as a fact
([places.md](../places.md#length-refined-fields)).

### What is trusted

The solver's certificates are rechecked by `facts::verify`. The compiler's
fact collection (which facts hold at each point) and `facts::verify` are
trusted alongside the kernel.

## The logical kernel

`total fn`, `total enum`, `prop` and type aliases are checked by a dependent
type theory: universes `Type<u>`, an impredicative `Prop` with proof
irrelevance, dependent functions, `Nat` with induction and large literals,
`Eq<A, x, y>` with `refl`, transport and `J`, and positive indexed data with
dependent elimination ([kernel.md](../kernel.md)). Logical definitions have
no run-time code; they are erased.

```kush
type ConstantNat<n: Nat> = Nat;

total fn add_step(n: Nat, acc: Nat) -> Nat ! {} { Nat.succ(acc) }

total fn add(n: Nat, m: Nat) -> Nat ! {} {
    Nat.induct(ConstantNat, m, add_step, n)
}

total fn two_plus_three() -> Eq<Nat, add<2, 3>, 5> ! {} {
    refl::<Nat>(5)
}

fn main() -> i64 ! {} { 0 }
```

Every argument is explicit: there are no implicit arguments, no proof
search and no tactics in the compiler. Recursion goes through eliminators.

An executable function may take a kernel proposition as an erased
parameter. Run-time `i64`, `Bool` and `Unit` values may appear in it as
symbols; the caller passes a named proof, never `_`:

```kush eval
total fn zero_is_zero() -> Eq<i64, 0, 0> ! {} { refl::<i64>(0) }

fn keep(n: i64, erased same: Eq<i64, n, n>) -> i64 ! {} { n }

fn main() -> Unit ! {io} {
    let five: i64 = 5;
    print_i64(keep(five, refl::<i64>(five)) + keep(0, zero_is_zero()));
}
```

```output
5
```

The kernel cannot state facts about machine arithmetic, and a kernel proof
cannot discharge an arithmetic precondition:

```kush reject
total fn t() -> Eq<i64, 0, 0> ! {} { refl::<i64>(0) }
fn f(x: i64, erased q: { x >= 0 }) -> i64 ! {} { x }
fn main() -> i64 ! {} { f(5, t()) }
// error: an erased argument must be '_'
```
