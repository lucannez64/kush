# Lifetime variance: design

Status: design only. This document defines the lifetime-only variance algebra,
the constructor table, the lifetime-aware subtype judgment, its composition
with ownership provenance, the finite variance-inference fixed point, the
compiler integration sequence, and the positive/negative checks for plan node
`LT-VARIANCE-DESIGN`. It does not implement the feature and does not close
`LT-VARIANCE`. Recursive lifetime inference (`LT-RECURSIVE`), lifetimes in row
variables (`LT-ROWVARS`), and borrowed structural results (`LT-STRUCT-RESULT`)
remain separate nodes; this document only fixes the interfaces they must use.

The design is grounded in the current implementation:

- `Type::Annotated(usize, u32)` and the erased-label carriers
  (`crates/kush/src/executable.rs:24`, `:56-60`);
- the erased-shape judgment `Types::subtype` / `atom_subtype`
  (`crates/kush/src/runtime_types.rs:3160`, `:3188`);
- structural width/depth subtyping (`:3264`);
- callable subtyping and `BorrowSig::usable_as`
  (`:3374`, `:352`);
- ownership provenance and mutable write paths
  (`crates/kush/src/ownership.rs:402`, `:468`, `:515`, `:2234`, `:2605`);
- the finite outlives solver (`crates/kush/src/lifetimes.rs:6`, `:19`, `:149`).

## 1. What the compiler has today

There are currently **two disjoint mechanisms**:

1. **Erased-shape subtyping.** `Types::subtype` is a boolean relation over
   interned runtime types. It deliberately erases labels:
   - `Annotated(inner, label)` strips the label and compares `inner`
     (`runtime_types.rs:3199-3204`);
   - `Ref`/`RefMut` compare pointees by *mutual* subtype, i.e. invariance
     (`:3210-3220`);
   - `Box`/`Vec`/`ArenaBox`/`AllocBox`/`AllocVec` compare pointees by mutual
     subtype, i.e. invariance (`:3225-3235`);
   - record-to-record comparison goes through `same_erased_shape`, which
     compares the definition, consts, and type arguments but **never**
     `Enum.lifetimes` (`:1349-1415`);
   - structural conversions require exact type equality for retained borrowed
     leaves (`:3282-3288`);
   - arrow subtyping is contravariant in parameters, covariant in the result,
     with effect-row inclusion, grade contracts, and `BorrowSig::usable_as`
     (`:3374-3410`).

2. **Ownership-side call and return checks.** The ownership pass builds
   `CallLifetime` from the callee's `BorrowSig`, maps declared parameter
   lifetimes to actual argument leaves (`call_mapping`, `ownership.rs:1908`),
   validates the callee's outlives bounds (`validate_call_bounds`, `:1874`),
   and records the result provenance (`apply_call_lifetime`, `:1945`). Returned
   borrowed records are checked field by field against the declared result
   type (`check_return_record`, `:3257`). Mutable container writes are checked
   by `apply_mutable_container_effects` (`:2234`): a value written into a
   `&mut Vec<&'a T>` must outlive the declared element lifetime.

The second mechanism is a partial lifetime judgment. It runs at **call and
return boundaries**, and it is driven by `BorrowSig` leaves and `field_lifetimes`,
not by a general type relation. It does not run for:

- `let`/assignment coercions between two record types with different labels;
- record-field and container-element subtype coercions that are not calls
  (record-literal construction checks direct field labels separately);
- function-value coercions where the parameter/result record labels are erased
  by `function_subtype`;
- structural conversions (which are safe but exact today);
- union injections (unions cannot contain borrowed leaves; see below).

The erased relation also accepts record-to-record conversions with **no label
relation at all**: `Window<'short>` is an erased subtype of `Window<'long>`
because `same_erased_shape` ignores `Enum.lifetimes`. In some paths the
ownership pass compensates by retaining the loan, but that is an ownership-side
invariant, not a type-level one. The design makes the relation explicit and
requires every coercion to carry a witness.

### Label carriers

Lifetime labels are not uniformly present in `Type`. The design must respect
the existing carriers:

| Position | Carrier | Source |
| --- | --- | --- |
| direct function parameter view/reference | `Function::parameter_lifetimes[i]` | `executable.rs:291` |
| direct function result view/reference | `Function::result_lifetime` | `executable.rs:293` |
| record direct borrow field | `Enum::field_lifetimes[i]` | `runtime_types.rs:82` |
| record/enum lifetime arguments | `Enum::lifetimes` | `runtime_types.rs:75` |
| reference element inside `Box`/`Vec`/array | `Type::Annotated(inner, label_id)` | `executable.rs:56-60`, `runtime_types.rs:3443` |
| callable slice/record contract | `BorrowSig::{parameters,result,parameter_leaves,result_leaves}` | `runtime_types.rs:210-235` |
| callable outlives bounds | `BorrowSig::bounds` | `runtime_types.rs:235` |

`Type::Ref`, `Type::RefMut`, `Type::Slice`, `Type::SliceMut`, and `Type::Str`
do **not** store their own lifetime. A bare `&'a T` local's lifetime is tracked
by ownership (`Loan`, `view_roots`, `retain_loan`), not by the type. This is why
the variance judgment cannot be a simple recursive function over `Type`: it
must combine the type walk with the carrier table above.

## 2. Two judgments, one refinement

Define two relations:

- `A ≤e B` — the existing erased-shape subtype (`Types::subtype`).
- `Δ ⊢ A ≤ₗ B ⇝ W` — the new lifetime-aware judgment, where `Δ` is a finite
  outlives constraint set and `W` is a witness.

**Refinement invariant.** `Δ ⊢ A ≤ₗ B ⇝ W` may be accepted only if `A ≤e B`.
The implementation calls `subtype` first as a necessary condition; the label
walk only adds constraints. Conversely, `≤ₗ` is strictly stronger than `≤e`
whenever a borrowed leaf is present. For borrow-free types, `≤ₗ` is defined to
coincide with `≤e`, so existing programs and tests without borrowed leaves are
unaffected.

**No-fallback invariant.** If `A` or `B` contains a borrowed leaf and the label
walk cannot produce a witness, the conversion is rejected. It may not fall back
to `≤e`, and it may not drop a label, invent a label, or skip an owner loan.

**Witness.** `W` is a finite map

```text
W : Label × Label → {+, -, =}
```

where `W(λs, λt) = +` means `Δ ⊨ λs : λt` (the source label outlives the
target label), `W(λs, λt) = -` means `Δ ⊨ λt : λs`, and `W(λs, λt) = =` means
the labels must be the same identity after alpha-renaming. A map keyed by the
pair, not a function from source labels, is required: contravariant positions
and union alternatives can relate one source label to several target labels,
and every such obligation must hold.

When the same pair occurs at several positions, the position variances are
**joined** with the lattice of §3.1 (`+ ⊔ - = =`, `+ ⊔ = = =`,
`- ⊔ = = =`). A `+`/`-` pair therefore becomes `=` and is checked as identity;
that is conservative (mutual outlives would also be sound, but identity is
decidable and does not depend on a cycle in `Δ`). A pair is never rejected
merely because it occurs at two positions; the joined obligation is checked
once.

The witness is checked once, after the whole type walk: `Δ ⊨ λs : λt` for every
`+` pair, `Δ ⊨ λt : λs` for every `-` pair, and label identity after
alpha-renaming for every `=` pair, plus the ownership checks in §8. This avoids
the current split where `function_subtype` and `BorrowSig::usable_as` compute
independent mappings that can disagree.

## 3. Lifetime-only variance algebra

### 3.1 Lattice

```text
V = { *, +, -, = }
```

with the order `* ⊑ + ⊑ =`, `* ⊑ - ⊑ =`. Read `*` as "parameter unused",
`+` as covariant, `-` as contravariant, `=` as invariant. Invariance is the
most restrictive element; bivariance is the least.

Join (used for multiple occurrences in one declaration):

```text
* ⊔ v = v
+ ⊔ + = +        - ⊔ - = -        + ⊔ - = =
+ ⊔ = = =        - ⊔ = = =        = ⊔ = =
```

Composition (outer position `v₁`, inner position `v₂`):

```text
* ∘ v = *        v ∘ * = *                 // no occurrence
= ∘ v = =        v ∘ = = =                 // invariance absorbs
+ ∘ + = +        + ∘ - = -                 // sign multiplication
- ∘ + = -        - ∘ - = +
```

Composition distributes over join:

```text
v ∘ (v₁ ⊔ v₂) = (v ∘ v₁) ⊔ (v ∘ v₂)
```

These laws are the standalone property tests in §10.2. They are the only
algebra the implementation needs; there is no separate "variance annotation"
syntax and no user-written variance.

### 3.2 Judgment rules

`Δ ⊢ A ≤ₗ B ⇝ W` walks the interned type graph with a visited set and the
existing depth bound (32, as in `same_erased_shape`). At each node it adds
pairs according to the constructor table in §4. The position variance `v`
is threaded: the root is `+` (a value position), and each constructor composes
its own variance with the incoming `v` (`v ∘ v_ctor`). At a contravariant
position the sub-judgment is run with the operands swapped and its pairs are
re-oriented to the whole judgment's source/target, flipping the polarity; the
result is the same as adding `(λA, λB, -)` at the leaf. At a leaf:

- `v = +`: record the pair `(λA, λB)` with polarity `+`; require
  `Δ ⊨ λA : λB` later.
- `v = -`: record the pair `(λA, λB)` with polarity `-`; require
  `Δ ⊨ λB : λA` later.
- `v = =`: record the pair `(λA, λB)` with polarity `=`; require
  `λA = λB` after alpha-renaming.
- `v = *`: no pair. A leaf at a `*` position means the occurrence analysis
  was wrong; default to `=` and reject conservatively.

For a nominal record or enum instance, the walk compares `Enum.lifetimes`
componentwise using the variance table, maps each direct `field_lifetimes[i]`
pair at the field position, and recurses into the field types. For an
`Annotated(inner, label)` element it maps `label` at the current position and
recurses into `inner`; the annotation itself is neutral. For a callable it maps
`BorrowSig::{parameters,result,parameter_leaves,result_leaves}` and then
threads the same witness through the parameter/result `≤ₗ` checks (§6.1).

`None` is a distinguished **elided/unknown** label, not a wildcard:

- `None ↦ None` adds nothing (no named obligation; the loan is still tracked by
  origins).
- `Some(λ) ↦ None` is accepted only when `A == B` exactly (a no-op, no
  conversion). Otherwise it is rejected: erasing a label would skip the loan
  relation.
- `None ↦ Some(λ)` is rejected: a relation cannot be invented.

Anonymous/internal labels (`<local N>`, `<anon N>`, `<inferred N>`) are rigid.
A named label may be related to an internal label only when the internal label
is a fresh local whose owner the ownership pass can prove; otherwise the
conversion is rejected. Internal labels are never generalized or renamed by
variance.

### 3.3 Direction examples

For a covariant record:

```kush
struct Window<'a> { view: &'a [i64] }

fn shorten<'long: 'short, 'short>(w: Window<'long>) -> Window<'short> ! {panic} { w }
```

`Window` is `+` in `'a`; the judgment adds `('long, 'short, +)`, and `Δ` has
`'long: 'short`. Accepted. The reverse (`Window<'short>` to `Window<'long>`)
requires `'short: 'long`, which is not implied; rejected.

For a contravariant position (function parameter), the outer arrow flips the
direction and the record's own variance composes:

```kush
fn install(f: fn(Window<'long>) -> i64 ! {panic}) -> Unit ! {panic} { ... }
fn short_cb(w: Window<'short>) -> i64 ! {panic} { ... }

// short_cb may be installed where a long-window callback is expected,
// given 'long: 'short.
```

`fn(Window<'short>) ≤ fn(Window<'long>)` requires
`Window<'long> ≤ Window<'short>` (contravariant parameter), which is
`('long, 'short, +)`. Accepted. The reverse direction requires
`'short: 'long` and is rejected.

## 4. Constructor table

`v_ctor` is the variance of the constructor in the relevant parameter. `+a`
means the constructor's own lifetime argument (the one carried by
`field_lifetimes`/`Annotated`/`BorrowSig`), not a `Type` field.

| Constructor | Lifetime positions | Type/pointee positions | Rule and reason | Boundary |
| --- | --- | --- | --- | --- |
| `&'a T` (`Ref`) | `+a` | `+T` | shared read-only borrow: a longer borrow and a narrower pointee are usable as shorter/wider | none |
| `&'a mut T` (`RefMut`) | `+a` | `=T` | shortening a unique borrow is safe; changing the pointee through an exclusive borrow is not (write-then-read hostile case) | pointee invariant |
| `&'a [T]` (`Slice`) | `+a` | `+T` | shared slice: covariant element | none |
| `&'a mut [T]` (`SliceMut`) | `+a` | `=T` | unique slice: lifetime may shorten, element type may not change | element invariant |
| `&'a str` (`Str`) | `+a` | — | text view; no element type | no `&mut str` |
| `Box<T>`, `ArenaBox<T>`, `AllocBox<T>` | — | `+T` (lifetime positions only) | owned exclusive storage; no alias can mutate through a shared value | type-argument variance unchanged |
| `Vec<T>`, `AllocVec<T>` | — | `+T` (lifetime positions only) | owned exclusive storage; mutation requires `&mut`, which is invariant | type-argument variance unchanged |
| `[T; N]` | — | `+T` | owned/copy inline array | none |
| `Option<&'a T>` (niche enum) | `+a` | `+T` | single reference payload; shared | optional `&mut` is `+a`, `=T` |
| nominal record `R<'a,...; T,...>` | computed | computed | product of fields; each field is a `+` position, then compose with the field constructor | `=` if any field occurrence is invariant; `=` if unknown |
| nominal enum `E<'a,...; T,...>` | computed | computed | sum of variants; every variant field is `+`, then compose | borrowed payloads are restricted (see below) |
| structural row `struct { ... }` | field-wise | field-wise | borrowed leaves exact until `LT-ROWVARS`/`LT-STRUCT-RESULT` | conservative |
| transparent alias | expands | expands | alias expansion is exact substitution; no variance at the alias boundary | no alias variance annotations |
| `fn`/`once fn` | arrow-bound | params `-`, result `+` | standard arrow variance; `BorrowSig` handles the lifetime contract | positional alpha-renaming only |
| `DynObj` | — | `=` | open dispatch; payload is owned and `TraitArguments` has no lifetimes (`executable.rs:3479`) | no lifetime variance |
| foreign `#[foreign]` | — | `=` | opaque one-word host handle (`runtime_types.rs:106`) | no lifetime variance |
| union `A \| B` | — | member-wise | `UnionType` alternatives are concrete **non-borrowed** value types (`runtime_types.rs:174-180`), so no lifetime leaves occur inside | existing erased rules |
| `Never`, scalars, `Bytes`, `String`, `Arena`, `Allocator` | — | — | no borrowed leaves | unchanged |

Notes:

- **The `+T`/`=T` column is about lifetime labels nested in `T`, not about
  type-argument covariance.** This node wires only lifetime parameters. A
  `+T` entry composes the variance of a lifetime label that appears inside
  `T` (for example `&'a Window<'b>`); it does not make `Vec<i64>` a subtype of
  `Vec<i64 | Bool>`. Type-argument variance remains the existing invariant
  rule (`docs/subtyping.md:287`) and is a separate node.
- **Records are products, not automatically covariant.** The record's variance
  in a parameter is the join of the occurrence variances of its fields. A field
  is a `+` position, but a field type such as `&'a mut [&'a [T]]` composes
  `+ ∘ = = =`, so the record is invariant in `'a`. A naive "records are
  covariant by field" rule is unsound here.
- **Nominal record lifetime parameters are currently `+` or `=` only.** A
  record with borrowed fields rejects callables (`has_forbidden_record_metadata`,
  `runtime_types.rs:4971`), and a declared record lifetime must be used by a
  borrowed field (`:3744-3765`). Since every admitted borrowed field is
  `&'a ...` or a nested borrowed record, the occurrence variance is `+`,
  unless a `&mut` pointee makes it `=`. The `-` case is exercised by function
  arrows and transparent aliases to arrows, not by nominal records today. The
  algebra supports `-` so a future node that admits callables in borrowed
  records does not need a new table.
- **Enums.** Non-`TaskExit` enums may carry a borrowed payload only as a
  lexical optional reference (`runtime_types.rs:3826-3858`): exactly one empty
  variant and one single-reference variant. That shape has one lifetime
  argument and one reference payload, so the payload label is
  `Enum::lifetimes[0]`. It is treated as `+a` (shared) or `+a`/`=T` (optional
  `&mut`). `TaskExit<T>` carries its borrow through the generic argument `T`;
  the enum has no lifetime parameters, so `TaskExit` is invariant in `T` in this
  node and the existing call-boundary provenance handles the payload.
  If the implementation cannot recover the payload-to-label association for a
  non-record enum, it must default that enum to `=` rather than guess.
- **Aliases are transparent.** `expand_alias` substitutes declared lifetime
  parameters exactly (`runtime_types.rs:2826-2900`). The judgment sees the
  expansion. An alias lifetime parameter that is unused is `*` (no relation);
  this is the main legitimate "unused" case, because records reject unused
  lifetime parameters.
- **Unions cannot hide a borrow.** `UnionType` members are non-borrowed, so a
  union never contains a lifetime leaf. Union subtyping stays the existing
  member-wise erased relation. A future node that admits borrowed union members
  must extend this table; this design does not.
- **Dyn and foreign are invariant.** `DynObj` has no lifetime arguments and its
  payload is owned; retagging is already rejected in `coerce`
  (`executable.rs:15240`). A foreign resource is an opaque one-word handle with
  a synthetic `I64` field; a phantom lifetime would let the handle outlive its
  owner. Both are `=` (exact) and have no lifetime leaves.

### Grades and effects are unchanged

The variance table has no entry for `parameter_grades`, `result_grade`, or
`effects`. The callable judgment keeps:

- effect-row inclusion `source.effects & !target.effects == 0`
  (`runtime_types.rs:3378`);
- exact `result_grade` (`:3395`);
- `grade_contract_compatible` (`:4680`);
- `linear`/`once` restrictions (`:3382-3390`).

Lifetime variance is checked **in addition to** those rules, never instead of
them. Existing grade/effect tests remain the regression.

## 5. Hostile substitution examples

Each example is a concrete reason a flat or naive table is unsound. These are
the negative tests in §10.1.

### 5.1 `&mut` pointee covariance (write-then-read)

```kush
struct Point { x: i64, y: i64 }

fn evil<'a>(b: &mut Box<&'a Point>, short: &'a Point) -> Unit ! {panic} {
    Box.set(b, short);
}

let mut long: Box<&'long Point> = ...;
evil(&mut long, short_lived); // short_lived: &'short Point
// if &mut Box<&'a Point> were covariant in 'a, the box would hold a
// &'short Point while `long` still promises &'long Point.
```

The correct rule is `&'a mut T`: `+a`, `=T`. The pointee is invariant. The
same attack applies to any future `&mut &'a T` shape; the current admitted
mutable owner references are `&mut Box<T>`, `&mut Vec<T>`, `&mut Bytes`,
`&mut String`, and `&mut Record` (`docs/borrowing-extensions.md:406-425`).

### 5.2 `&mut Vec<T>` covariance (push-then-read)

```kush
fn push_short<'a>(v: &mut Vec<&'a [i64]>, s: &'a [i64]) -> Unit ! {panic} {
    Vec.push(v, s);
}

let mut v: Vec<&'long [i64]> = ...;
push_short(&mut v, short_lived); // short_lived: &'short [i64]
// if &mut Vec<T> were covariant in T, v would contain a short view typed 'long.
```

`Vec<T>` is `+T` as a **value**; `&mut Vec<T>` is `=` in `T` because `&mut`
is invariant in its pointee. A flat table that says only "Vec covariant" misses
the composition.

### 5.3 Record with an invariant field

```kush
struct Nested<'a> { views: &'a mut [&'a [i64]] }
```

The outer `&mut [T]` contributes `+a`; its element type `&'a [i64]` is
invariant under the mutable slice (`=T`). Composing the outer `+` with the
element's `=` gives `+ ∘ = = =`, so `Nested` is invariant in `'a`, not
covariant. A naive "records covariant by field" rule would accept
`Nested<'long> ≤ Nested<'short>` and then allow writing a short element through
the mutable slice and reading it back as long, the same hostile case as 5.1 one
level down. (The exact admitted field shapes are the existing mutable-slice
subset; the composition rule is the point.)

### 5.4 Erased record labels

```kush
struct Window<'a> { view: &'a [i64] }

fn erase<'short, 'long>(w: Window<'short>) -> Window<'long> ! {panic} { w }
```

`same_erased_shape` accepts the type-level return because it ignores
`Enum.lifetimes`; the current ownership pass may still reject this particular
body through `check_return_record` (`ownership.rs:3257`), which compares the
returned provenance to the declared result leaves. The point is that the
type-level relation does not establish `'short: 'long`; the same coercion in a
`let` binding (`let w2: Window<'long> = w;`) has no leaf check, which is the
gap `≤ₗ` closes. `≤ₗ` adds `('short, 'long, +)` and requires
`'short: 'long`, which is false when `'long` is a caller lifetime that outlives
`'short`, so `≤ₗ` rejects the body and the `let`.

### 5.5 Container of borrowed elements

```kush
let v: Vec<&'long [i64]> = ...;
let w: Vec<&'short [i64]> = v;
```

Erased `Vec` invariance compares the pointees mutually, and the `Annotated`
element labels are stripped, so the conversion is accepted with no relation.
`≤ₗ` composes `Vec`'s `+` with the shared reference's `+` and requires
`'long: 'short`. Every element's loan origins must be preserved; the vector is
moved, not copied. (`Vec<Window<'a>>` is not admitted today: `Box`/`Vec` of a
borrowed record is rejected. The same composition applies once that shape is
admitted.)

### 5.6 Function parameter variance with a record

```kush
fn take(f: fn(Window<'short>) -> i64 ! {panic}) -> i64 ! {panic} { f(...) }

fn long_cb(w: Window<'long>) -> i64 ! {panic} { ... }
take(long_cb); // rejected: requires 'short: 'long
```

`fn(Window<'long>) ≤ fn(Window<'short>)` requires
`Window<'short> ≤ Window<'long>`, i.e. `'short: 'long`. The composition of
arrow contravariance with record covariance is the whole point; flipping the
record variance instead of the arrow position would wrongly accept this.

### 5.7 Union alternatives with conflicting labels

Unions cannot contain borrowed leaves today, so this is a forward-looking
objection for `LT-ROWVARS`/future union extensions: if one alternative maps
`'a` to `'x` and another maps `'a` to `'y`, accepting only the first would let
the second alternative escape. The witness is a pair-keyed map; every
alternative's obligations are joined into it, and a `+`/`-` pair becomes `=`
and must then be satisfied as identity.

### 5.8 Callable alpha-binding

```kush
fn apply<'x>(
    f: fn<'a>(&'a [i64], &'a [i64]) -> &'a [i64] ! {panic},
    x: &'x [i64],
) -> &'x [i64] ! {panic} { f(x, x) }

fn second<'l: 's, 's>(l: &'l [i64], s: &'s [i64]) -> &'s [i64] ! {panic} { s }
// second fits the arrow: 'l and 's both map to 'a, and 'l: 's is reflexive.
```

A naive string comparison of the source's `'l`/`'s` with the target's `'a`
would reject an alpha-equivalent arrow. `BorrowSig::canonical_with_leaves`
(`runtime_types.rs:257`) numbers labels `#0`, `#1`, ... in first-use order, and
the judgment compares after canonicalization.

### 5.9 Higher-rank result flow

```kush
fn first<'l, 's>(l: &'l [i64], s: &'s [i64]) -> &'l [i64] ! {panic} { l }
// fits fn<'a, 'b>(&'a [i64], &'b [i64]) -> &'a [i64]

fn second<'l, 's>(l: &'l [i64], s: &'s [i64]) -> &'s [i64] ! {panic} { s }
// does not fit fn<'a, 'b>(&'a [i64], &'b [i64]) -> &'a [i64]:
// the result is tied to the second input, so the caller would need 'b: 'a,
// which the target arrow does not declare.
```

This is the existing `usable_as` result-flow rule
(`runtime_types.rs:352-460`): every source parameter that can flow into the
source result must map to a target lifetime outliving the target result. The
design keeps it and extends it to record result leaves. It is a **sound but
incomplete** approximation, not a principal higher-rank algorithm.

### 5.10 Owner-loan skipping

```kush
let mut owner = [1, 2, 3];
let w: Window = Window { view: &owner[..] };
let w2: Window<'short> = w;   // label shortened; loan origins {owner} must stay live
owner = [4, 5, 6];            // must stay rejected while w2 is live
```

If a lifetime-only coercion released the loan because the target label is
shorter, the owner write would be accepted while `w2` still points into the old
storage. The witness must carry the source leaf's origins to the target leaf;
the loan is retained until the target value's last use.

### 5.11 Elided target label

```kush
fn f(w: Window) -> Unit ! {panic} { ... } // record field labels are declared,
                                          // but a container element may be elided
let v: Vec<&[i64]> = ...;                 // element label is None
let w: Vec<&'long [i64]> = v;             // rejected: None -> Some cannot be invented
```

Treating `None` as a wildcard would erase the element label and skip the loan.
`None` is only compatible with `None` (or with an exact no-op).

## 6. Callable alpha-binding and higher-rank limits

### 6.1 Canonicalization and the single witness

`BorrowSig` is canonical: `canonical_with_leaves` numbers labels in first-use
order over parameters, result, parameter leaves, and result leaves
(`runtime_types.rs:257-340`), and alpha-equivalent arrows intern to one
`FunctionType` (`:249-256`). The new judgment:

- alpha-renames both arrows before comparing; free labels from the enclosing
  scope are rigid and are related by `Δ`, not renamed;
- threads the **same** `W` through `BorrowSig::usable_as` and the
  parameter/result `≤ₗ` checks. `function_subtype` must not compute one map for
  the types and another for the contract.

Today `BorrowSig` stores only canonical names and `canonical_with_leaves`
discards the source names. The clean integration is a side table
`function_labels[id] : Vec<String>` (canonical `#i` to the user's name) kept
**outside** `FunctionType`/`FunctionKey`, so alpha-equivalent arrows still
intern to one type. A recomputation from the parameter/result types in the same
first-use order is possible but fragile; the side table is preferred.

`capture_result` (`BorrowSig::capture_result`, `runtime_types.rs:232`) stays
**exact-match only**. A closure result borrowed from its environment is not
expressible by an ordinary arrow; the existing check
(`usable_as`, `:354-357`) is preserved and no variance is applied to capture
indices or paths.

### 6.2 Limits

The design does **not** implement full higher-rank subtyping and does not claim
principal types. Explicit limits:

1. **Positional only.** Source arrow lifetimes are instantiated by target
   arrow lifetimes at the same parameter positions, plus the target result for
   the source result (`usable_as`). There is no permutation, interleaving, or
   reordering of binders.
2. **Same binder count.** Alpha-renaming only; a conversion cannot add or
   remove arrow lifetime binders.
3. **No meet/shortest-of-several results.** A result tied to the shorter of
   two inputs has no principal lifetime in this fragment; it is rejected rather
   than approximated. The existing "several return-position lifetimes are
   rejected, not unified" rule (`docs/lifetimes.md:716-730`) is unchanged.
4. **No arrow-bound inference.** Arrow lifetimes and bounds must be declared;
   the checker does not infer a principal contract.
5. **No higher-kinded lifetimes.** Lifetimes are not higher-kinded parameters
   of records or aliases beyond the declared parameters; an arrow may bind its
   own lifetimes, but a record cannot abstract over a lifetime constructor.
6. **No capture variance.** `capture_result` is exact.
7. **No principal unification.** If the source contract is not implied by the
   target contract, the conversion is rejected; the checker does not search
   for a principal instantiation.

These are conservative boundaries, not a claim of completeness. A future
`LT-RECURSIVE` node may infer more outlives edges, but it must still respect
the same arrow binder discipline.

## 7. Finite variance inference

### 7.1 Occurrence graph

For each declaration `d` (record, enum, alias) and each **lifetime** parameter
`p` in this node, define a node `(d, p)`. Walk `d`'s fields (or the alias body
after expansion) with a position variance, starting at `+` for a product field:

- a direct occurrence of `p` in a borrow label adds the current position
  variance as a self-edge;
- a field of type `d'<..., p', ...>` adds an edge `(d, p) -> (d', p')` labeled
  `v_pos`, the position variance at which `d'` occurs; the fixed-point update
  then composes that label with the current estimate for `d'`'s parameter;
- a field of type `&'a mut T` adds `+` for the outer label `a` and `=` for any
  label inside `T`;
- an occurrence through `DynObj`, a foreign type, an opaque alias, a const/
  effect generic, or a shape the analysis cannot classify adds a self-edge
  labeled `=` (invariant). It never adds `+` or `-`;
- a parameter with no occurrence stays `*`.

### 7.2 Fixed point and SCC

The lattice is finite and has height 3. Initialize every node to `*`, then
iterate

```text
var(d, p) = var(d, p) ⊔ (label ∘ var(d', p'))
```

to the least fixed point. A deterministic worklist ordered by
`(BindingId, parameter_index)` terminates in at most `3 × |nodes|` effective
updates per node; with a worklist it is `O(edges × 3)` updates. The solution is
deterministic because joins are commutative/associative and the iteration order
is sorted.

Strongly connected components matter for mutually recursive declarations
(`A<'a> { b: Box<B<'a>> }`, `B<'a> { a: Box<A<'a>> }`). Process the
condensation in reverse topological order and iterate inside each SCC. The
existing Kosaraju decomposition in `lifetimes.rs` (`:6-126`) can be shared as a
generic SCC helper, but its **outlives reachability semantics must not be
conflated with the variance lattice fixed point**: the variance solver adds no
edges to the outlives graph and the outlives solver knows nothing about
variance. Keep them as two separate passes that share only the SCC utility.

Recursive types converge from `*`: `struct List<T> { next: Box<List<T>> }`
starts `*`, the first update gives `+`, and the second is stable. A recursive
occurrence that also appears invariantly elsewhere joins to `=`. (The same
fixed point applies to a lifetime parameter; a recursive *borrowed* record is
currently rejected because `Box`/`Vec` of a borrowed record is not admitted, so
this example is an algebra illustration.)

### 7.3 Defaults

- **Unused** (no occurrence): `*`. Safe to ignore; any instantiation is
  allowed and no witness pair is produced.
- **Unknown/opaque** (dyn, foreign, unclassifiable, non-converged cycle):
  `=`. Never default to `+` or `-`; unknown covariance is the unsound default.
- **Direct occurrence**: the composed position variance (`+` for a product
  field, `=` under a `&mut` pointee).
- **Record lifetime parameter with no borrowed leaf**: rejected at declaration
  (`runtime_types.rs:3744-3765`), so `*` is not reachable for nominal records.
  `*` is reachable for alias parameters, type parameters, and enums that
  declare an unused lifetime parameter (the record-only unused check does not
  run for enums).
- **Non-record enum whose payload-to-label association cannot be recovered**:
  `=` (conservative), not `+`.

The table is computed once after all definitions are lowered and cached by
`(BindingId, parameter_index)`. It is a property of the declaration, not of a
use site; there is no per-call variance inference.

### 7.4 Record/enum generic parameter inference

At a call or coercion, a record/enum lifetime argument is part of the type
(`Enum::lifetimes`). The judgment relates the actual argument's label to the
declared parameter's label according to the table:

- covariant: the actual may be longer; the result's label is the actual label,
  and a later use at a shorter label is checked again;
- invariant: the actual label must be identical after substitution, or related
  by the function's declared bounds;
- contravariant: only reachable through arrows/aliases today; the direction
  flips as in §3.3.

Type parameters remain **first-order and invariant** in this node. The existing
`infer` path unifies a type parameter to an exact type and rejects two
arguments that disagree (`executable.rs:23672-23690`). The design does not
relax that to `T` covariance; `Vec<i64>` to `Vec<i64 | Bool>` stays rejected
(`docs/subtyping.md:287`). The only change is that a lifetime label **inside**
an inferred type argument is carried along and related by `≤ₗ`, not erased.
If the same type parameter is inferred from two arguments with different
labels, the existing exact-equality rule rejects the inference; the user must
specialize explicitly. This is conservative but sound, and it keeps type
inference out of the variance node.

An unused lifetime parameter cannot be solved from arguments. If it appears in
the result, the call is ambiguous and requires an explicit lifetime argument;
the checker does not invent one.

## 8. Ownership provenance and mutable write paths

The type-level witness is necessary but not sufficient. The ownership pass must
discharge it against actual loans.

### 8.1 Label preservation

For every accepted `Δ ⊢ A ≤ₗ B ⇝ W`:

- every borrowed leaf of `A` at path `p` with label `λ` and mutability `m` has
  a corresponding leaf of `B` at the same path with label `λ'` and the same
  mutability, unless the leaf is dropped by an explicit width conversion;
- `(λ, λ', v)` is in `W` for the variance `v` at that path;
- no leaf is added, no mutability is changed, and no label is replaced by an
  unrelated one.

A width conversion may drop a borrowed field only when it **moves** the source
value and releases the loan exactly at the conversion. Dropping a borrowed
field is safe in principle (a view can be forgotten), but a copy that leaves the
source alive would create a second capability; the conversion must consume it.
Linear/dyn fields remain rejected as today (`runtime_types.rs:3292-3304`).

### 8.2 Loan preservation

The witness is attached to the checked expression (a `Coerce` node or a side
table keyed by expression pointer, like `call_views`/`call_origins` in
`ownership.rs:4990-5010`). For each leaf pair:

- the target leaf's provenance origins are the source leaf's origins (or a
  superset); no origin is dropped;
- the target label's loan is retained until the target value's last use, via
  the existing `retain_loan`/`hold_record` machinery;
- a shared downgrade (`&mut T` to `&T`) consumes the exclusive capability: the
  source value is moved, the exclusive loan is not duplicated, and the shared
  result keeps the same origins until its last use. The existing
  `RefMut(a) ≤ Ref(b)` rule (`runtime_types.rs:3218`) is preserved only under
  this condition;
- a coercion may not create a new loan, release a live loan without consuming
  the value, or extend any loan's lifetime.

### 8.3 Mutable write paths

There are two write paths:

1. **Existing container writes.** `apply_mutable_container_effects`
   (`ownership.rs:2234`) checks that a value written through
   `&mut Vec<&'a T>` outlives the declared element lifetime `'a`. The design
   keeps this rule and feeds it the **declared** target label from the witness,
   not a variance-shortened label. Since `&mut Vec<T>` is invariant in `T`,
   the element label cannot be shortened through the mutable reference; the
   write check sees `'a` unchanged.
2. **Record-field writes (future).** Record field writes through `&mut Record`
   are currently limited to scalar/copyable, non-owning fields, and mutable
   writes on a record containing a borrowed field are rejected
   (`docs/borrowed-records.md:177-246`). When that subset is widened, the same
   rule must apply: writing `&'b [T]` into a field declared `&'a [T]` requires
   `'b: 'a`, and the written loan is merged into the record's provenance. The
   design specifies the rule now; it does not claim the write path is enabled.

### 8.4 Reborrow is not variance

An explicit reborrow (`&mut parent[..]`, `Slice.split_at_mut`) creates a
**child capability** with its own roots and loan, and suspends the parent
(`check_view_creation`, `ownership.rs:2875`). It is not a subtype coercion.
Lifetime covariance may shorten a `&'a mut T` **value** when it is moved, but
it never creates a child, never keeps the parent usable, and never changes the
parent's declared label. Conversely, reborrow never relies on variance to
justify a label change; it derives a fresh child with a shorter lifetime and
its own provenance. Conflating the two would either silently move the parent
(if covariance were used for reborrow) or create an alias (if reborrow were
used for a move).

### 8.5 Return and call boundaries

`check_return_record` (`ownership.rs:3257`) and `apply_call_lifetime` (`:1945`)
already check borrowed leaves at returns and calls. The design does not replace
them; it makes the type-level witness agree with them:

- the call boundary's `call_mapping` maps declared labels to actual labels; the
  same relation is used by the argument `≤ₗ` check, so there is one mapping,
  not two;
- the return boundary's `check_return_record` compares the returned provenance
  to the declared result leaves; the body's coercions already carry the
  witness, so a return cannot launder a label that the body accepted;
- a function value coercion's `BorrowSig::usable_as` and the parameter/result
  `≤ₗ` checks share the witness, so a record label inside a callable cannot be
  mapped two ways.

## 9. Compiler integration sequence

This is the implementation order for `LT-VARIANCE`; this document does not
perform it.

1. **Variance data.** Add `LifetimeVariance { Bivariant, Covariant,
   Contravariant, Invariant }` and a `VarianceTable` keyed by
   `(BindingId, usize)`. No behavior change in this step.
2. **Occurrence collection.** In `runtime_types.rs`, walk each record/enum/
   alias definition's fields with a position variance, expand aliases first,
   and record direct, nested, and unknown occurrences. Unknown → `=`.
3. **Fixed point and SCC.** Implement the finite lattice solver from §7,
   preferably as a small module that reuses the SCC decomposition style of
   `lifetimes.rs`. Cache the result; assert determinism in a unit test.
4. **`≤ₗ` core.** Add `Types::lifetime_subtype(&self, actual, expected,
   delta) -> Option<Witness>` next to `atom_subtype`. It first calls the
   existing `subtype`; then walks labels with the carrier table. It must not
   change `subtype`'s behavior for borrow-free types.
5. **Callable refactor.** Add `BorrowSig::usable_as_with(&self, target, delta,
   witness) -> bool` (or return the extended witness) and keep `usable_as` as a
   compatibility wrapper during migration. `function_subtype` calls the
   parameter/result `≤ₗ` checks and `usable_as_with` with the same witness; a
   pair that fails its joined obligation rejects. Add the canonical-to-source label side table
   from §6.1 outside `FunctionType`/`FunctionKey`.
6. **Coercion sites.** In `executable.rs`, route `expect` (`:15173`),
   `coerce` (`:15231`), `coerce_struct` (`:15390`), `nested_field_coercion`,
   `coerce_block`, union inject/repack, `coerce_function` (`:15855`), `let`/
   assignment/return/argument/record-field/array/vector-literal checks through
   `≤ₗ` with the current `Δ` (the function's `lifetime_bounds` plus inferred
   bounds). Record the witness on the `Coerce` node or in a side table.
   `arrow_rep_change` (`:15828`) is unchanged: lifetime-only variance never
   changes representation.
7. **Ownership.** In `ownership.rs`, make `CallLifetime`/`call_mapping`
   consume the witness; make `apply_call_lifetime` validate `Δ`; make
   `apply_mutable_container_effects` use the declared target label; attach the
   witness to `retain_loan`/`check_owner_access`; release dropped leaves
   exactly at the width conversion. Extend `RecordProvenance` with the leaf
   label path only if needed; do not duplicate the existing `Loan` data.
8. **Diagnostics.** Reuse `LifetimeGraph::explain_missing`
   (`lifetimes.rs:149`) for a missing `λs: λt`; add distinct messages for an
   invariant-position change, a relabel without a proved relation, a dropped
   borrowed leaf without a move, an unsatisfied joined witness pair, and the
   higher-rank limit. Include the field/leaf path and constructor chain
   (`Window.view`, `Vec element`, `fn parameter`, `&mut pointee`).
9. **Tests.** Add the §10 tests to the existing suites. The standalone algebra
   tests (composition laws, fixed-point determinism, `≤ₗ ⊆ ≤e`) are separate
   from the compiler integration tests.
10. **Plan.** `LT-VARIANCE-DESIGN` (this document) → `LT-VARIANCE` (steps
    1–9) → `LT-ROWVARS`/`LT-STRUCT-RESULT` (borrowed rows) → `LT-REVIEW`.
    `LT-RECURSIVE` remains separate; it may consume the `Δ`/witness interface
    but does not change the variance table.

## 10. Tests

### 10.1 Compiler tests

Positive (must accept):

1. `Window<'long> → Window<'short>` with `'long: 'short` (record covariance).
2. `Vec<&'long [i64]> → Vec<&'short [i64]>` with `'long: 'short`
   (`Vec` covariance composed with shared-reference covariance).
3. `Box<&'long [i64]> → Box<&'short [i64]>` with `'long: 'short`.
4. `&'long mut [i64] → &'short mut [i64]` as a moved value, with
   `'long: 'short` (lifetime covariance, not reborrow).
5. `fn(Window<'short>)` used where `fn(Window<'long>)` is expected, with
   `'long: 'short` (contravariance composed with covariance).
6. `second` fits `fn<'a>(&'a [i64], &'a [i64]) -> &'a [i64]` (alpha-binding).
7. An alias with an unused lifetime parameter (`type Tag<'a> = i64`) accepts
   any label; no loan is created.
8. `&mut T → &T` downgrade with the exclusive capability consumed.
9. A container write of a `&'b [T]` into `&mut Vec<&'a [T]>` with `'b: 'a`.
10. A record literal whose field view outlives the declared field lifetime.
11. Structural width conversion dropping an extra borrowed field, with the
    loan released by the move.
12. `Maybe<'long> → Maybe<'short>` for the optional-reference enum shape, if
    the implementation enables non-record enum covariance; otherwise this is a
    negative regression for the conservative default.

Negative (must reject):

1. `Window<'short> → Window<'long>` without `'short: 'long`.
2. `&mut Box<&'long Point> → &mut Box<&'short Point>` (invariant pointee,
   hostile 5.1).
3. `&mut Vec<&'long [T]> → &mut Vec<&'short [T]>` (invariant pointee,
   hostile 5.2).
4. `Nested<'long> → Nested<'short>` for
   `Nested<'a> { views: &'a mut [&'a [i64]] }` (hostile 5.3).
5. `fn erase<'short, 'long>(w: Window<'short>) -> Window<'long>` (hostile 5.4).
6. `Vec<&'short [i64]> → Vec<&'long [i64]>` (hostile 5.5).
7. `long_cb` used where `fn(Window<'short>)` is expected (hostile 5.6).
8. `second` used where `fn<'a, 'b>(&'a [T], &'b [T]) -> &'a [T]` is expected
   (hostile 5.9).
9. A `let` coercion that shortens a label but drops the owner loan, followed by
   an owner write (hostile 5.10).
10. `Vec<&[i64]> → Vec<&'long [i64]>` (elided to named, hostile 5.11).
11. A closure with `capture_result` coerced to a different arrow (existing
    rejection; regression).
12. A `DynObj` or foreign handle relabelled by a phantom lifetime.
13. `Vec<i64> → Vec<i64 | Bool>` (type-argument invariance; regression,
    `docs/subtyping.md:287`).
14. A structural conversion that changes a retained borrowed leaf's label or
    mutability (existing exact rule; regression).

### 10.2 Standalone algebra tests

- Composition is associative and distributes over join for all 4×4×4 inputs.
- Join is commutative, associative, idempotent, and has `*` as identity and
  `=` as top for the `+`/`-` sublattice.
- `v ∘ * = *` and `v ∘ = = =` for every `v`.
- Fixed point on hand-written graphs: unused → `*`, direct → `+`, `&mut`
  pointee → `=`, mixed `+`/`-` → `=`, mutual recursion → same result under
  every worklist order.
- `≤ₗ ⊆ ≤e`: every accepted lifetime witness has an erased-shape acceptance.
- Witness consistency: a `+`/`-` pair joins to `=` and is accepted only when
  the labels are identical; a one-to-many relation with all obligations
  satisfied is accepted.

### 10.3 Regression suites

`crates/kush/tests/subtyping.rs`, `lifetimes.rs`, `callable_lifetimes.rs`,
`borrowed_records.rs`, `borrowing_extensions.rs`, `borrowing_safety.rs`,
`review_regressions.rs`, and the `examples/borrowed-callables.kush` comparison.
The existing 1,179-test gate (per `docs/lifetime-graph.md`) remains the
acceptance baseline for the implementation node.

## 11. Conservative boundaries and non-claims

- **Lifetime-only.** This node does not change type-argument variance.
  `Box<T>`/`Vec<T>` are covariant only in lifetime positions; `Vec<i64>` to
  `Vec<i64 | Bool>` stays rejected. Type covariance would require union
  representation work and is a separate node.
- **No variance annotations in source.** Variance is a declaration property
  computed from field occurrences. Unknown → invariant; unused → bivariant.
- **No principal or higher-rank subtyping.** Only the positional
  alpha-renaming rule of `usable_as`; no permutation, no binder-count change,
  no meet/shortest-of-several result, no arrow-bound inference, no principal
  unification.
- **No recursive lifetime inference.** `LT-RECURSIVE` is separate. The
  interface is `Δ` plus the witness; this design does not solve recursive
  signature constraints.
- **No lifetimes in row variables.** Structural rows keep borrowed leaves
  exact until `LT-ROWVARS`/`LT-STRUCT-RESULT`. A bare `..` erases extra fields
  and releases their loans; `..r` is monomorphized to the exact residual row.
- **No borrowed structural results.** Still rejected as today.
- **Unions cannot contain borrowed leaves.** `UnionType` members are
  non-borrowed; union variance is the existing erased relation.
- **Dyn and foreign are invariant.** No lifetime arguments; a phantom lifetime
  is rejected.
- **Capture results are exact.** No variance for `capture_result`.
- **No borrowed-record callable fields.** Records with borrowed fields reject
  callables, so nominal record lifetime variance is `+` or `=` today; the `-`
  case is only reachable through arrows/aliases.
- **No source-level `&mut str`.** Unchanged.
- **Not a soundness proof.** The analysis is path-insensitive and
  conservative; both backends and the runtime remain trusted. The design makes
  the invariants explicit and testable, not proven.

## 12. Soundness objections to a naive table

A flat table of the form "Box/Vec covariant, `&mut` invariant, fn parameters
contravariant, records by field" is underspecified and, read literally, unsound.
The concrete objections:

1. **Variance is positional, not per-constructor.** `&mut` invariant in its
   pointee and `Vec` covariant as a value compose to `&mut Vec<T>` invariant in
   `T`. A table that lists only `Vec`'s variance misses this (hostile 5.2).
2. **`&mut` is covariant in its own lifetime but invariant in its pointee.**
   A table that says "`&mut` invariant" rejects valid shortenings; one that
   says "`&mut` covariant" accepts the write-then-read attack (hostile 5.1).
   Reborrow must not be used to justify either direction.
3. **Records are products of field occurrences.** A record with a
   `&'a mut [&'a [T]]` field is invariant in `'a`, not covariant (hostile 5.3).
   A record with a callable field `fn(&'a T)` would be contravariant; the
   current subset rejects callables in borrowed records, but the table must
   still derive the variance rather than assume covariance.
4. **Erased shape is not a lifetime judgment.** `same_erased_shape` ignores
   `Enum.lifetimes`, so it accepts `Window<'short> ≤ Window<'long>` with no
   relation. A table layered on `subtype` must not treat erased acceptance as
   sufficient (hostile 5.4).
5. **Two independent mappings are unsound.** If `function_subtype` maps the
   parameter/result types one way and `BorrowSig::usable_as` maps the contract
   another way, a label can be related in two directions. The witness must be
   a single pair-keyed map (hostile 5.8, §6.1).
6. **Contravariance needs a relation, not an inverse function.** Inverting a
   functional map loses one-to-many relations and can silently drop an
   obligation. The witness is a pair-keyed map (§2).
7. **Union alternatives are universal.** A value may be any alternative, so
   every alternative's label obligations must hold; accepting one alternative's
   mapping is unsound (hostile 5.7).
8. **Elided labels are not wildcards.** Treating `None` as "any lifetime"
   erases the label and skips the loan (hostile 5.11).
9. **Unknown must default to invariant.** Defaulting an unclassifiable
   occurrence to covariant is unsound; defaulting it to `=` is conservative.
   Unused may be `*`, but only after proving no occurrence.
10. **Dropping a borrowed leaf requires a move.** Width subtyping can drop a
    field, but a copy that leaves the source alive creates a second capability.
    The conversion must consume the value and release the loan.
11. **A shared downgrade must consume the exclusive capability.** Otherwise
    `&mut T → &T` can duplicate the capability and create aliasing.
12. **Lifetime covariance is not reborrow.** Using variance to implement
    reborrow moves the parent or creates an alias; using reborrow to implement
    a move leaves the parent usable. They are separate operations (§8.4).

## 13. Unresolved questions

1. **Type-parameter variance.** Should `LT-VARIANCE` also make `Box`/`Vec`
   covariant in type arguments, or strictly lifetime positions? This design
   recommends lifetime-only; type covariance needs union representation work
   and is not claimed. The parent should confirm the plan node's "Box/Vec
   covariant" shorthand means lifetime positions.
2. **Non-record enum covariance.** Should the optional-reference shape be
   covariant in its single lifetime argument, or stay invariant until the
   payload-to-label association is stored explicitly? The design defaults to
   invariant when the association is unknown; the optional-reference case is
   the only candidate for `+`.
3. **Borrowed structural leaves.** Should `≤ₗ` relax the exact-equality rule
   for retained borrowed structural fields, or keep it exact until
   `LT-ROWVARS`/`LT-STRUCT-RESULT`? This design keeps it exact.
4. **Dropped borrowed fields.** Auto-release on a width move, or reject and
   require an explicit destructure? The design proposes auto-release with a
   move; the implementation must prove no alias remains.
5. **`BorrowSig` label table.** Add the canonical-to-source side table, or
   recompute the type-level map in canonical order? The design recommends the
   side table outside `FunctionType`/`FunctionKey` to preserve interning.
6. **Anonymous labels.** How should `<local N>`/`<anon N>` participate in
   variance and diagnostics? The design treats them as rigid and only relates
   a named label to a fresh local when the ownership pass can prove the owner.
7. **`TaskExit<T>` payload.** Invariant in `T` (this design) or a special
   covariant rule for the borrowed task result? The existing call-boundary
   provenance already handles the payload; invariance is conservative.
8. **Diagnostics surface.** Should variance polarity and the witness be
   printed in `Types::name`/diagnostics, or kept internal? The design
   recommends internal, with path-and-constructor messages only.
9. **Recursive variance and `LT-RECURSIVE`.** The variance solver shares SCC
   decomposition but not outlives reachability. Confirm the parent wants a
   shared generic SCC helper rather than a second copy.

## 14. Checks and review scope

This is a design document. **No build, test, Clippy, formatting, or Boat run
was performed for it**, and no compiler code was changed. The checks below are
the proposed acceptance gate for `LT-VARIANCE`, not results:

- standalone algebra tests from §10.2 (composition laws, fixed point,
  `≤ₗ ⊆ ≤e`, witness consistency);
- the positive/negative compiler tests from §10.1 in the existing suites;
- the existing lifetime, borrowing, subtyping, callable, and review-regression
  suites as the baseline;
- a source review that every `subtype` call site which can see a borrowed leaf
  is routed through `≤ₗ`, that `BorrowSig::usable_as` and the type-level walk
  share one witness, and that ownership retains every mapped loan.

The design is conservative and path-insensitive. It is not a formal soundness
proof, and it does not claim that the feature is implemented. The trusted
components (both backends and the runtime) are unchanged.

## References

| Topic | Source |
| --- | --- |
| `Type` including `Annotated`, `Ref`, `RefMut`, `Slice`, `SliceMut`, `Str`, containers | `crates/kush/src/executable.rs:24-140` |
| `Annotated` documentation (checker-only, container element) | `crates/kush/src/executable.rs:56-60` |
| `Enum` fields: `lifetimes`, `field_lifetimes`, `borrowed`, `mutable_borrow` | `crates/kush/src/runtime_types.rs:66-107` |
| `BorrowSig` and canonicalization | `crates/kush/src/runtime_types.rs:210-340` |
| `BorrowSig::usable_as` | `crates/kush/src/runtime_types.rs:352-460` |
| `same_erased_shape` | `crates/kush/src/runtime_types.rs:1349-1415` |
| `subtype` / `atom_subtype` | `crates/kush/src/runtime_types.rs:3160-3262` |
| `structural_subtype` | `crates/kush/src/runtime_types.rs:3264-3310` |
| `same_representation` | `crates/kush/src/runtime_types.rs:3315-3345` |
| `function_subtype` | `crates/kush/src/runtime_types.rs:3374-3410` |
| reference label interning and `annotate_container_element` | `crates/kush/src/runtime_types.rs:3423-3465` |
| record field lifetime lowering and unused-parameter rejection | `crates/kush/src/runtime_types.rs:3640-3770` |
| enum borrowed-payload restriction | `crates/kush/src/runtime_types.rs:3826-3858` |
| `grade_contract_compatible` | `crates/kush/src/runtime_types.rs:4680-4697` |
| `has_borrow` / `has_mutable_borrow` / `contains_linear` / `contains_dyn_object` | `crates/kush/src/runtime_types.rs:4938-5090` |
| `borrow_leaves` | `crates/kush/src/runtime_types.rs:5234-5300` |
| `expect` / `coerce` / `coerce_struct` / `coerce_function` | `crates/kush/src/executable.rs:15173-15880` |
| `Function::parameter_lifetimes` / `result_lifetime` / `lifetime_bounds` | `crates/kush/src/executable.rs:269-298` |
| `TraitArguments` (no lifetimes) | `crates/kush/src/executable.rs:3479-3486` |
| `Loan` / `RecordProvenance` | `crates/kush/src/ownership.rs:402-510` |
| `CallLifetime` / `call_mapping` / `validate_call_bounds` / `apply_call_lifetime` | `crates/kush/src/ownership.rs:515-545`, `:1847-2020` |
| `apply_mutable_container_effects` | `crates/kush/src/ownership.rs:2234-2312` |
| `check_owner_access` / loan suspension | `crates/kush/src/ownership.rs:2580-2660` |
| `check_return_record` | `crates/kush/src/ownership.rs:3257-3310` |
| `CONTAINER_LEAF` and container provenance | `crates/kush/src/ownership.rs:20`, `:1472-1630` |
| outlives solver and diagnostics | `crates/kush/src/lifetimes.rs:6-243` |
| erased subtyping documentation | `docs/subtyping.md:113-118`, `:287-289`, `:500-510` |
| arrow variance documentation | `docs/functions.md:285-310` |
| callable lifetime substitution | `docs/lifetimes.md:622-672` |
| lifetime limitations | `docs/lifetimes.md:716-793` |
| borrowed-record limitations | `docs/borrowed-records.md:177-246`, `:295-340` |
| solver status and remaining variance node | `docs/lifetime-graph.md:49-58` |
| spec variance statement | `docs/spec-v0.1.md:184` |
| plan nodes | `plan/plan.json` `LT-VARIANCE-DESIGN`, `LT-VARIANCE`, `LT-ROWVARS`, `LT-STRUCT-RESULT`, `LT-RECURSIVE`, `LT-REVIEW` |
