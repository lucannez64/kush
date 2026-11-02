# General usage-grade inference

Status: implemented for the executable subset. Inference solves a set of
simultaneous equations over natural grades or a declared finite grade algebra.
It is deliberately not a principal grade solver: anything outside the fragment
below stays an explicit `::<...>` specialization error, and an unknown grade is
never guessed as one.

## Solving model

All equations contributed by the current inference site are collected first:

- a direct call contributes one equation for each argument whose expression has
  a known exact grade, pairing the declared parameter grade with that grade;
- a function value contributes equations from the expected arrow's concrete
  parameter and result grades.

The solver then repeatedly looks for an equation in which exactly one binder is
still unsolved, substitutes the already-known binders, and solves that binder.
Solutions are substituted into every other equation, so a later equation may
depend on an earlier binder. Every candidate is checked against all evaluable
equations; a disagreement is a conflict error rather than a silent choice. If a
pass makes no progress, the remaining binders are unresolved and the call site
reports an explicit-specialization error. Bindings that occur in an underlying
runtime type (parameter type, element type, stored field, or underlying result
type) are never inferred.

## Natural fragment

The declared expression is built from natural literals, `many`, known grade
variables, `+`, `*`, and parentheses. For one binder, let `e(g)` be the value
with that binder set to `g` and every other leaf concrete.

- **Affine equations** (`e` has at most one occurrence of the binder) are solved
  exactly: `e(g) = e(0) + (e(1) - e(0)) * g`. A unique natural solution exists
  when the slope is nonzero and divides the offset.
- **Repeated occurrences** such as `G + G`, `G * G`, or `(G + 1) * G` are
  accepted when `e(1) > e(0)` and the target is finite. Every such expression
  has nonnegative integer coefficients with at least one positive degree term,
  so `e(g) >= g` for every `g >= 1`. Therefore no solution can exceed the
  target, and enumerating `0..=target` is complete. The solver accepts exactly
  one solution and rejects zero or several.
- The enumeration budget is 100,000 candidates. A finite target above that
  bound is outside the fragment instead of causing an unbounded compile-time
  search. Evaluator overflow above the target terminates the search, because
  the expression is monotone in the binder.
- A bare `@[G]` may be solved directly from any expected grade, including
  `many`.
- A `many` target does not produce a finite solution for a composite
  expression; only the bare-binder case is defined.

Still outside the fragment and rejected rather than guessed:

- zero-slope expressions such as `G * 0` or `G * many` (every or no binder
  value satisfies them);
- ambiguous equations with several solutions (`G * 0 = 0`, or a multivariate
  equation such as `G + H = 3` with no other constraint);
- non-divisible equations such as `G * 2 = 1`;
- targets above the enumeration budget;
- arbitrary multivariate Diophantine systems: the solver only propagates
  single-unknown equations. It makes no general decidability or completeness
  claim.

## Finite-algebra fragment

When the expected grade is a declared algebra element, or the expression
contains element leaves, the binder ranges over that algebra's validated finite
carrier. The solver evaluates the entire expression with the full table
semantics for every element (at most 64) and accepts the result only when
exactly one element satisfies the target. Two or more solutions stay explicit.
Expressions mixing unrelated algebras are outside the fragment.

Custom-algebra `one` is not silently equated with the builtin exactly-once
observation: a copyable result bound from `@[Algebra.One]` keeps that algebra
element as its local grade, so an idempotent one (`one + one = one`) means
"at least one observation in this algebra", not builtin `@[1]`. Builtin `@[1]`
continues to mean exactly one physical observation. A declaration whose zero
and one are the same element is rejected because erasure and observation would
be indistinguishable.

## Direct calls

A direct call infers a grade parameter when an argument is an expression with a
known exact grade and the corresponding parameter grade mentions the binder:

```kush
fn twice<G: Grade>(x: i64 @[G]) -> i64 ! {panic} { x + x }

fn main() -> i64 ! {panic} {
    let x: i64 @[2] = 21;
    twice(x)                 // G inferred as 2
}
```

Only explicitly annotated bindings (or value positions that preserve one, such
as a block tail, `if/else` with equal grades, or a coercion) provide evidence.
An unannotated argument does not default to `@[1]`. Multiple argument
constraints are solved simultaneously and must agree. Composite parameter
grades such as `x: i64 @[G * G]` work in the natural fragment. A grade parameter
that only occurs in the result of a direct call still needs explicit
specialization, because a direct call supplies no expected grade for its result.

## Function values

A generic function used as a value is checked against the expected arrow. The
arrow's concrete parameter and result grades are constraints:

```kush
fn four<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} { x + x + x + x }
fn apply(f: fn(i64 @[4]) -> i64 ! {panic}) -> i64 ! {panic} { f(10) }

fn main() -> i64 ! {panic} { apply(four) }    // G = 2
```

Several binders may be solved together. In

```kush
fn combine<G: Grade, H: Grade>(x: i64 @[G + 1], y: i64 @[H + G]) -> i64 ! {panic} { ... }
fn apply(f: fn(i64 @[3], i64 @[5]) -> i64 ! {panic}) -> i64 ! {panic} { ... }
```

`G + 1 = 3` determines `G = 2`, then `H + G = 5` determines `H = 3`, regardless
of the binder declaration order.

## Tests

`crates/kush/tests/grade_inference.rs` covers direct-call parameter inference,
composite parameters, simultaneous multi-binder constraints, repeated and
nonlinear natural equations, ambiguity rejection, budget/ungraded boundaries,
function-value parameter inference, finite-algebra enumeration, composite
copyable result inference, underlying-type occurrences, and native/reference
agreement. `crates/kush/tests/result_grade_inference.rs` keeps the earlier
result-contract and alias cases. `crates/kush/tests/grade_algebras.rs` covers
custom-algebra one/zero observability.
