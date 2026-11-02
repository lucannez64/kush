# Algebraic subtyping

Status: implemented for the executable value fragment. This is a normalized,
coercion-producing subtype system over concrete runtime types, not the complete
dependent/graded algebraic language in the [v0.1 design](spec-v0.1.md#6-algebraic-subtyping).
Unsupported combinations are rejected explicitly.

```sh
cargo run -p kush -- check examples/subtyping.kush
cargo run -p kush -- eval examples/subtyping.kush
cargo run -p kush -- run examples/subtyping.kush
```

The example prints `21, 20, 4, 39, 3, 21, 4, 42`. The executable tests include a
native/reference comparison of the example and of owning-union repacking.

## Types

A union is written `A | B`; an intersection is written `A & B`. Intersection
binds more tightly than union, and `@[grade]` binds more tightly than either, so
a grade on all of a union needs parentheses:

```rust
fn f(value: i64 | Bool) -> i64 ! {panic} { ... }
fn g(value: (Box<i64> | Bytes) @[1]) -> i64 ! {panic} { ... }
fn h(value: (i64 | Bool) & i64) -> i64 ! {} { value }
```

Union alternatives may be any supported concrete value type: `i64`, `Bool`,
`Unit`, `Bytes`, `Box<T>`, `Vec<T>`, inline arrays, nominal records/enums, and
first-class callable types (`fn(...)`, `once fn(...)`, and
`linear once fn(...)`), including `#[linear]` ones. Nested unions are flattened.
Intersections are normalized by distribution and disjointness: clauses with no
common runtime inhabitant become `Never` and disappear from the union. There is
no fabricated inhabitant for a false intersection.

The same-enum fragment remains zero-cost. These are still bit-per-variant masks
over the nominal enum layout:

```rust
Op.Mul | Op.Div
(E.A | E.B) & E       // E.A | E.B
```

A heterogeneous union such as `i64 | Bool` or `Box<i64> | Bytes` has a runtime
discriminator word plus storage for its widest alternative. Arrays, records,
enums, boxes, and vectors containing union values use that layout recursively.
Union width remains subject to the existing 32-word inline layout limit, and a
union has at most 16 normalized alternatives. Exceeding either budget is a
diagnostic, never a silent approximation.

Normalization is deterministic and commutative/associative/idempotent:

```text
A | A = A                       A & A = A
A | Never = A                   A & Never = Never
A <: A | B                      A & B <: A
E.A | E.B = (E.A | E.B)         // one variant mask, not a tagged union
A | B = B                when A <: B
A & (B | C) = (A&B) | (A&C)
```

The implementation sorts alternatives, merges same-enum masks, removes
duplicates, drops `Never`, and applies subtype absorption. Intersection is
distributed over union; the supported non-callable atoms have no structural
refinement other than enum variant masks, so each nonempty non-callable atom
pair either stays equal or narrows to a variant mask. Other non-callable atom
pairs are disjoint.

Callable atoms are normalized by arrow subtyping. A narrower arrow absorbs into
a wider one. Two distinct but mutually subtype arrows (for example an
unannotated parameter grade and `@[many]`) are representation-equivalent and
normalize to one deterministic representative rather than both absorbing into
`Never`; the representative prefers the more permissive unannotated contract.
Incomparable callable intersections remain an explicit diagnostic; there is no
overloaded-function representation.

## Subtyping and conversions

The checked subtype relation includes:

- reflexivity, `Never <: A`, and normalized union/intersection laws;
- variant-mask inclusion: `E.A <: E`, `E.A <: (E.A | E.B)`;
- atom-to-union and union-to-wider-union inclusion.

`i64` and `Bool` do not implicitly convert to one another. Numeric conversion is
still explicit. Nominal records are invariant, and `Box<T>`/`Vec<T>` are
invariant in `T`: `Vec<i64>` is not a subtype of `Vec<i64 | Bool>`. Tests reject
that conversion.

When source and target have the same layout (for example a variant mask used as
its full enum), the expression keeps its precise type and no runtime work is
generated. When representations differ, checking inserts an explicit, checked
`Coerce` node:

- **Inject** writes the target alternative tag and copies the payload words,
  padding unused words with zero.
- **Repack** remaps each source alternative tag to a deterministic target tag
  and copies the active payload only.

Coercions never allocate, never duplicate an owner, and never create a type
test from a pointer. They are used by annotated `let` bindings, assignment,
function arguments and returns, constructor/record fields, array/vector
literals, `if`/`match` joins, and generic specialization/inference. Widening a
subset union to a larger union repacks it; passing the same union unchanged
costs nothing.

Callable alternatives obey the same rules with one ABI restriction. Injecting a
callable atom into a union alternative uses a checked arrow conversion when the
representation changes (for example a pure `fn` into a `once fn` alternative
gets a null-environment thunk). A union-to-union repack copies a callable
payload only when the calling convention and every parameter/result
representation agree. Otherwise the conversion is rejected with an explicit
diagnostic; there is no raw function-pointer relaundering.

Conversion is coherent: tag order comes from the normalized, sorted alternative
list, so the same subtype judgment always produces the same target tag.

## Case analysis and narrowing

A heterogeneous union is narrowed with a type pattern:

```rust
fn describe(value: i64 | Bool | Box<i64>) -> i64 ! {panic} {
    match value {
        i64 @ n => n,
        Bool @ flag => if flag { 1 } else { 0 },
        Box<i64> @ boxed => Box.take(boxed),
    }
}
```

`Type @ pattern` tests the union discriminator and applies `pattern` to the
narrowed payload. The binder has the member type, so it can be used, moved, or
matched further. This includes callable alternatives:
`once fn(i64) -> i64 ! {panic} @ f => f(41)` calls through the narrowed
per-signature ABI. A record or enum pattern can narrow directly when exactly one
union alternative has that shape:

```rust
match value {
    Pair { left, right } => left + right,
    Shape.Line(n) => n,
    Shape.Dot => 0,
    i64 @ n => n,
}
```

If several union alternatives share one generic enum/record definition, the
short form is rejected as ambiguous; write `Option<i64> @ o => ...` (or another
explicit member type) first. Arrays and vectors are narrowed with their full
type, for example `[i64; 2] @ xs => ...` and `Vec<i64> @ vs => ...`. Field access,
indexing, `Slice`, `Vec`, `Box.read`, and `Box.take` require the value to be
narrowed first; they do not implicitly inspect a union.

Matching is exhaustively checked over the normalized alternatives. A union arm
covers one alternative; a wildcard covers every remaining alternative. Guards do
not contribute coverage. Unreachable union arms are rejected. A variant pattern
outside the scrutinee's variant mask is rejected rather than treated as a dead
branch. Payload bindings keep the same ownership rules as ordinary enum/record
patterns: moving a union value into a match transfers the active payload, and
ignored affine payloads are dropped.

## Ownership, grades, slices, and drop

- A union is owning if any alternative can own storage, and linear if any
  alternative is linear. Such a union moves rather than copies even when the
  active alternative is copyable. A copyable union (`i64 | Bool`) remains
  copyable. A `linear once fn(...)` alternative makes the whole union linear,
  so it must be consumed by a match or call and cannot be implicitly dropped.
- `@[1]` on an owning union has the same consumption obligation as any other
  owning value. `@[0]`, `@[n>1]`, and `@[many]` are rejected for owning unions.
  A wildcard over a linear alternative is rejected; bind and consume it.
- Generated cleanup dispatches on the tag and traverses only the active
  alternative. Inactive payload words are kept zero by construction and are
  never interpreted as pointers.
- Borrowed references, slice views, and lifetime-parameterized borrowed or mixed records
  cannot be union alternatives. This
  prevents a view from escaping its owner's lexical scope through a union.
  Slice construction and lifetime checking are otherwise unchanged; the
  existing `&[T]` rules still apply.
- Union coercions allocate nothing, so they are legal under `#[noalloc]`.
  Owning-union construction that calls `Box.new`, `Vec.push`, or `Bytes.from`
  still carries the existing `alloc`/`panic` effects.

## Explicit boundary

Implemented and tested:

- heterogeneous scalar, owning, record, enum, array, and vector unions;
- nested unions and normalized union-to-union widening/repacking;
- same-enum variant-mask unions/intersections with the zero-cost layout;
- distributive intersections and empty-intersection `Never`;
- exhaustive type-pattern matches, guards, and unreachable-arm diagnostics;
- branch/match joins, annotated lets, assignment, calls, returns, `?` cleanup,
  and generic specialization with coerced union arguments/results;
- native/reference agreement for union layout, injection, repacking, matching,
  and active-alternative drop;
- arrow subtyping for named function values, explicit generic specializations,
  noncapturing lambdas, effect-polymorphic arrows, affine once closures, and
  linear-once closures, including union parameter/result repacking through
  checked adapters and pure/noalloc rejection of allocating adapters;
- callable heterogeneous union alternatives, including coherent normalization,
  injection, union-to-union repacking, type-pattern narrowing, and
  active-alternative cleanup of uncalled once environments;
- deterministic canonical representatives for distinct but mutually subtype
  arrows, while incomparable callable intersections remain explicit errors.

Deliberately unsupported, with explicit diagnostics:

- **Structural record/width subtyping:** source declarations are nominal and the
  executable IR has no anonymous row/structural record type. A record is
  invariant; two different record declarations are disjoint.
- **Function subtyping:** arrow subtyping is implemented for first-class
  function values (`fn(...)`, owning `once fn(...)`, and `linear once fn(...)`),
  with contravariant parameters, covariant results, effect-row inclusion
  (including instantiated `<e: Effects>` rows), grade-contract checks, and
  checked representation-changing adapters. See
  [functions.md](functions.md). Different arrow types still have no fabricated
  common function intersection. Callable values may be union alternatives, but
  a union-to-union repack that would change a callable ABI is rejected rather
  than relaundered.
- **Borrowed captures and linear captures:** linear captures are supported via
  the distinct `linear once fn(...)` mode. Slice views may be captured only by a
  scoped borrowed-capture `once fn` that is called or dropped locally; the
  arrow type carries no borrow, so returns, storage, helper passing, unions,
  adapters, and task captures are rejected. Slice-returning function values are
  not supported.
- **Borrowed unions and mutable slices in unions:** excluded by the union-member
  restriction above. Slice functions may return shared or mutable views with
  checked explicit or conservatively elided lifetimes, but a view cannot escape
  through a union alternative.
- **Indexed/dependent unions and principal algebraic inference:** runtime type
  aliases (including unions) are elaborated transparently, but inference
  through a union that mentions an unbound type variable asks for explicit
  `::<...>` specialization instead of guessing. Array length variables are a
  separate compile-time fragment described in
  [dependent-indices.md](dependent-indices.md).
- **Structural equality or ordering on union values:** no union equality; match
  a member and compare the narrowed scalar.
- **Implicit numeric widening:** not part of subtyping.

These are representational or design boundaries, not claims that general
algebraic subtyping is complete. The dependent/grade interaction and a formal
coherence/soundness proof remain future work, as noted in [grades.md](grades.md)
and the [v0.1 research gates](spec-v0.1.md#6-algebraic-subtyping).
