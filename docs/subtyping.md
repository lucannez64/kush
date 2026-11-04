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

## Structural records

An anonymous structural record type is written `struct { a: i64, b: Bool }`.
It has no nominal declaration and no module-level name. Fields are stored in a
**canonical row**: sorted by field name, independent of source order. Two
occurrences with the same field names and value types therefore intern to one
layout, and the runtime order is deterministic.

A record value (nominal or structural) is a subtype of a structural record when
every target field is present in the source with a subtype-compatible type.
Width subtyping drops source fields that the target does not mention. Dropping
is a real runtime conversion, not a pointer reinterpretation:

- target fields are copied into canonical order;
- source fields absent from the target are cleaned up exactly once, in reverse
  declaration order;
- an omitted field that carries a linear obligation is rejected, because the
  target cannot consume it;
- fields that are already at the target representation are copied directly;
- a retained field may itself need a nested structural width conversion or an
  atom-to-union injection; both are checked recursively and still allocate
  nothing. A nested union-to-union repack needs its own control flow and is
  rejected explicitly, so bind/convert that field before the structural
  coercion;
- a retained callable field whose arrow representation changes is rebuilt
  through a generated checked adapter. The source callable is moved into the
  adapter environment exactly once, so a `once` or `linear once` field keeps
  its single consumption and cleanup obligation. Creating that environment
  allocates, so the enclosing conversion requires `{alloc, panic}`. A
  pure-to-pure conversion that changes a parameter or result representation
  stays rejected: a pure arrow has no environment in which to carry the
  adapter. Convert such a field explicitly first;
- an atom-to-union injection of a callable field is allowed only when the
  calling convention and parameter/result representations are unchanged.

Borrowed leaves are invariant. A structural conversion cannot change an
`&[T]` into `&mut [T]`, drop the mutability of a view, or relabel a borrowed
record leaf. Mutability follows the underlying `&[T]`/`&mut [T]` types, which
are already invariant under `subtype`. Owning affine fields may be erased by
width subtyping; they are dropped exactly once by the conversion. The runtime
conversion is available in the reference evaluator and the native backend and
allocates nothing.

```rust
struct Wide { b: i64, a: i64, extra: Box<i64> }

fn sum(v: struct { a: i64, b: i64 }) -> i64 ! {panic} {
    v.a + v.b
}

fn main() -> i64 ! {alloc, panic} {
    sum(Wide { b: 20, a: 22, extra: Box.new(1) }) // 42, extra dropped
}
```

A structural record literal is written with the same row syntax:

```rust
let r = struct { b: 20, a: 22 };
let sum = match r { struct { a, b } => a + b };
```

Fields are evaluated in source order but stored in the canonical name-sorted
row. A structural pattern matches any record that has the named fields; omitted
fields and `..` are dropped by the ordinary pattern cleanup rules. When exactly
one record alternative of a union has all named fields, the structural pattern
narrows that alternative directly; several such alternatives require an
explicit `Type @ pattern`.

A retained field may now itself change representation, including a nested
structural width conversion, atom-to-union injection, and a nested
union-to-union repack. The repack is a checked tag remap; it copies only the
active payload and never duplicates an owner.

A structural type may end with `..`, as in `struct { x: i64, .. }`. This is an
**erased open-row contract**: the annotation accepts any record that has every
named field with a compatible type, and fields the annotation does not mention
are dropped once at the call boundary by the ordinary checked width
conversion. The callee therefore sees exactly the named canonical row; extra
fields are not preserved and cannot be returned or forwarded. A dropped field
that carries a linear obligation, a borrow leaf that would change
mutability/labels, and any other representation-changing rule above still
apply. Empty open rows such as `struct { .. }` are accepted as a record-shaped
parameter with no inspected fields.

A named tail `..r` is a **true row variable**, not an erased annotation:

```rust
fn keep<r>(v: struct { x: i64, ..r }) -> struct { x: i64, ..r } ! {panic} { v }
```

`r` is an ordinary type parameter used in row position. At each call the
checker binds it to the argument's **residual canonical row**: the actual
record fields not named by the structural pattern. The function is then
monomorphized once per concrete residual row, so its parameter and result are
the exact full row (named fields plus residual). Unmentioned fields are
preserved across the call, including owning, linear, and borrowed leaves; the
function may read, move, return, or consume them without erasing their
obligations. A residual `struct { token: Token }` with a linear `Token` stays
linear, and closing the result back to `struct { x: i64 }` is rejected because
dropping `token` would lose its obligation. Borrowed residual fields keep their
per-field loan through the call, so an exclusive borrow or replacement of the
owner while the row value is live is rejected. Row binding recurses through
nested structural fields, so `struct { inner: struct { a: i64, ..r } }` binds
`r` to the nested residual row. One row variable must receive the same residual
row from every parameter; disagreeing residuals are an explicit diagnostic, and
an inferred row variable cannot be left unbound. Unlike an erased `..`, a row
variable is type information, so a function that mentions it in its result must
be called with a record argument (or an explicit structural row
specialization) that determines the tail.

The canonical row is interned from complete field descriptors: name, runtime
type, and the outer borrow label of a direct `&'a [T]`, `&'a mut [T]`, or
`&'a str` field. Rows that differ only in `'a` versus `'b` are different checker
types, although their runtime layout is identical. Residual inference projects
those descriptors from the actual record, so a borrowed field keeps its label
through `..r`; one row variable must receive the same complete residual row,
including labels, from every parameter. A call site with a different label gets
its own specialization rather than reusing the first call's binder environment.
Retained borrowed fields stay invariant under a structural conversion: a
concrete source label must match the target label exactly. An unlabelled
literal or a fresh inferred identity may acquire the target annotation only
through the ordinary checked coercion, which keeps the value's actual origins.

A row variable may also appear in an impl header:

```rust
impl<r> Tag for struct { x: i64, ..r } {
    fn tag(self: Self) -> i64 ! {panic} { self.x }
}
impl<r> struct { n: i64, ..r } {
    fn double(self: Self) -> i64 ! {panic} { self.n * 2 }
}
```

Dispatch matches only anonymous structural rows (nominal records still keep
their own identity and must be coerced explicitly), binds `r` to the residual
row, and instantiates the method for that concrete receiver. Overlap and
specialization are decided by the named-field rows: an open header with more
named fields is more specific, incomparable open headers are a declaration-time
coherence error, and an open header and an exact structural header follow the
ordinary concrete-over-generic rule. A bare `..` impl header has no parameter
to bind the residual row and remains an explicit rejection.

Borrowed structural **results** remain an explicit boundary: although a
specialized row now carries its fields' erased borrow labels, structural rows
declare no lifetime parameters that could be related to the caller's outlives
bounds, so returning `struct { view: &[i64], ..r }` is rejected. The view may
travel through a row-variable parameter and be read or consumed inside the
call, but a caller-owned structural result must be a nominal record with
declared lifetimes.

**Field renaming** is an explicit conversion, written with `from`:

```rust
let narrow = wide as struct { b: i64 from a, flag: Bool };
```

The target row keeps its own canonical names; `from` selects the source field
for that target field. Each source field may be used at most once, unmentioned
fields are dropped by the ordinary checked cleanup, borrowed leaves keep the
same invariance rule, and a missing source field is an error. Only the explicit
`value as struct { ... }` cast accepts `from`: a `from` in a general parameter
or return annotation is rejected. Renaming is top-level only; nested target
fields still match by name. A target field with no `from` matches the source
field of the same name.

**Structural equality** is available for structural records whose leaves are
copyable scalars (integers, `Char`, `Bool`, `Unit`) or nested structural records
of them:

```rust
if a == b { ... }   // field-by-field, both operands evaluated once
```

Both operands must have the same canonical row. The implementation compares the
record words directly in the native backend and the materialized field values in
the reference evaluator, including nested rows and both `==` and `!=`. Floating
point leaves are excluded because their equality is numeric (`-0.0 == 0.0`,
NaN) while the inline representation compares raw words; owning, borrowed,
union, callable, and nominal leaves are excluded so equality never moves or
inspects an opaque payload. Narrow a union member and compare scalars, or match
fields explicitly, for those cases.

A structural row may also be an inherent or trait impl receiver:

```rust
impl struct { x: i64, y: i64 } {
    fn sum(self: Self) -> i64 ! {panic} { self.x + self.y }
}

trait Tag { fn tag(self: Self) -> i64 ! {panic}; }
impl<T> Tag for struct { value: T } {
    fn tag(self: Self) -> i64 ! {panic} { 42 }
}
```

Structural impl headers match **one exact canonical row**: field names and
types must agree, with generic type parameters allowed in field positions.
They deliberately do not match nominal records implicitly, so a nominal impl
and a structural impl of the same trait are disjoint and coherence stays
decidable. A nominal value reaches a structural impl only after an explicit
width coercion to that row. Open rows are rejected in impl headers because
width compatibility there would make dispatch depend on the call site's row.

Structural records support named row variables, explicit field renaming, and
equality over comparable leaves, but they are still not a general
row-polymorphic record calculus. There is no row subtraction, row alias, or
first-class row value; a row variable must be monomorphized by a concrete
argument row. A bare `..` is erased, while `..r` preserves the residual row. The
residual-row equality rule means a row variable cannot be solved from two
parameters with different tails. Structural impl dispatch is exact-row or
named-row-pattern; a bare `..` impl header is not accepted. Borrowed structural
results remain rejected.

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

## Contextual and algebraic inference

The checker no longer guesses the first union alternative that has the right
shape. Two related mechanisms accumulate constraints instead:

1. **Contextual literals.** For an inline-array, vector, or tuple literal whose
   expected type is a union, every matching alternative is considered. The
   literal is checked under each candidate element/tuple type and must be
   accepted by exactly one. Zero survivors report the first candidate's real
   type error; several survivors are an explicit ambiguity requesting an
   annotation or `::<...>` specialization. `Vec.new()`/`Vec.with_capacity` with
   an ambiguous union of `Vec<T>` alternatives are rejected rather than
   choosing one unchecked element type.
2. **Generic calls through a union actual.** First-order matching distributes a
   declared pattern over every union member that constrains a type/natural
   variable. Every member that binds a variable must agree. Disagreement is a
   diagnostic naming the variable and both bindings; no alternative is silently
   preferred. A bare type variable still captures the whole normalized union,
   because that is the principal binding for `id<T>(x: T)`.

The supported inference fragment is deliberately first-order and bounded:

- matching is structural over the declared generic pattern (named data, `Box`,
  `Vec`, arrays, tuples, arrows, aliases) and never runs user code;
- union distribution is recursive at inferred positions, with at most the
  normalized 16 alternatives per position;
- a declared union pattern with exactly one bare unbound type variable and a
  concrete fixed part, such as `T | i64`, binds `T` to the residual actual
  alternatives not covered by the fixed part. This is a decidable
  residual-union rule, not row subtraction. If every alternative is already
  covered by the fixed part, the residual is not unique and the call is
  rejected rather than defaulting;
- a union pattern with several bare unbound type variables, such as
  `T | U | i64`, partitions the residual alternatives with a bounded
  backtracking search (4096 steps per pattern). Every variable must receive at
  least one residual alternative; alternatives already covered by the concrete
  or previously solved fixed part stay with the fixed part and are never
  redistributed. The search order is canonical: residual alternatives keep
  their normalized order and are assigned to variables in declaration order.
  Ordinary inference takes the first canonical partition;
- **cross-parameter backtracking** is bounded and deterministic. If a later
  parameter rejects the partition committed for an earlier one, `infer`
  replays the entire accumulated constraint list from the base substitution,
  enumerating partition choices in lexicographic order. The replay budget is
  4096 complete attempts; exhausting it is an explicit diagnostic. Parameters
  that mention a tentatively partitioned or row-bound variable are checked
  without committing to the tentative expected type, so the replay can
  reconsider instead of failing during contextual checking. The search changes
  only type/row bindings; a literal whose own typing needs a later expected
  type remains the usual explicit-annotation boundary;
- row variables participate in this same first-order unification. A pattern
  tail `..r` binds the actual residual canonical row, recursively through
  nested structural fields. This is recursive row unification for the
  monomorphized fragment, not row subtraction or row aliasing: a row variable
  must receive the same residual row from every parameter;
- **principal result for the decidable fragment.** The single-variable residual
  rule (`T | i64` over a finite normalized union) is principal: the residual is
  the unique set of actual alternatives not covered by the fixed part. A
  multi-variable partition is not principal in general; ordinary inference and
  replay choose the first canonical partition that satisfies every parameter.
  When exactly one partition survives, that result is determined by the
  constraints, and a completely unconstrained or symmetric case is reported as
  ambiguous or as an unbound parameter instead of being guessed;
- conflicting or incomparable evidence is always an error, never a silently
  chosen arm; explicit annotations/specialization are the escape hatch;
- type inference does not infer unions from unconstrained literals: an empty
  vector still needs an annotation;
- **indexed/dependent unions remain an explicit boundary.** Indexed enums,
  runtime-indexed union alternatives, and dependent type families are not
  inferred from a union actual in this executable fragment. A union of the same
  generic constructor with different arguments (for example
  `Option<i64> | Option<Bool>`) is not collapsed to `Option<i64 | Bool>`:
  the constructor is invariant, so that would be unsound. Such calls require
  an explicit `::<...>` specialization.

This is a decidable bounded fragment with a precise boundary, not a complete
principal algebraic subtyping algorithm. Indexed/dependent unions, row
subtraction/aliasing, and unbounded cross-parameter search are outside it.

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

- **Structural record limits:** anonymous `struct { ... }` rows support width
  subtyping, canonical reordering, recursive nested structural rows,
  atom-to-union field injection, nested union-to-union repacking, checked
  callable-field adapters, erased `..` open-row annotations, named `..r` row
  variables that preserve unmentioned fields, explicit top-level field renaming
  through `value as struct { target: T from source }`, structural equality over
  comparable leaves, structural literals and patterns, and exact-row or
  named-row-pattern structural impl headers, as described above. Remaining
  boundaries: nested (non-top-level) field renaming, row subtraction/aliasing,
  first-class row values, a bare `..` in an impl header, and borrowed structural
  results. Nominal records remain invariant with respect to other nominal
  records and do not match structural impl headers implicitly.
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
  aliases (including unions) are elaborated transparently. Contextual literals
  and first-order generic matching accumulate constraints over the finite union
  row as described above. Multi-variable union patterns use a bounded canonical
  partition search, and a bounded cross-parameter replay can reconsider an
  earlier partition. Row variables add recursive residual-row unification.
  The single-variable residual rule is principal; multi-variable partitions are
  deterministic but not principal, and indexed/dependent unions, row
  subtraction/aliasing, and unbounded search remain explicit-specialization
  boundaries. Array length variables are a separate compile-time fragment
  described in [dependent-indices.md](dependent-indices.md).
- **Structural equality or ordering on union values:** no union equality; match
  a member and compare the narrowed scalar.
- **Implicit numeric widening:** not part of subtyping.

These are representational or design boundaries, not claims that general
algebraic subtyping is complete. The dependent/grade interaction and a formal
coherence/soundness proof remain future work, as noted in [grades.md](grades.md)
and the [v0.1 research gates](spec-v0.1.md#6-algebraic-subtyping).
