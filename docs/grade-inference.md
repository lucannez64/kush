# General usage-grade inference

Status: implemented for the executable subset. This extends the earlier
bare-result-only inference rule with a small, explicit solver. It is not a
principal grade solver and it never guesses an unknown grade.

## Decidable fragment

Inference works on one usage-grade binder of a generic function or function
value at a time. A declared grade expression is accepted by the solver only
when all of the following hold:

- the binder occurs **exactly once** in the expression;
- every other leaf is already concrete (a natural, `many`, or a grade variable
  bound by the current specialization);
- the expression is built from natural literals, `many`, `+`, `*`, and
  parentheses;
- a concrete expected grade exists at that position.

Under these conditions the expression is affine in the binder:

```text
e(g) = e(0) + (e(1) - e(0)) * g
```

The checker evaluates the expression at `0` and `1`, computes the slope, and
accepts a target `t` only when `t - e(0)` is nonnegative and divisible by the
slope. The candidate is then re-evaluated with the full grade evaluator, so
overflow checking and operator rules are never bypassed. A bare `@[G]` may also
be solved as `many` from an expected `@[many]`.

The following stay outside the fragment and are rejected rather than guessed:

- repeated occurrences such as `G + G` or `(G + 1) * G`;
- zero-slope expressions such as `G * 0` or a constant expression that happens
  to mention the binder;
- non-divisible equations such as `G * 2 = 1`;
- a binder that occurs in an underlying runtime type (parameter type, element
  type, stored field, or underlying result type);
- conflicting constraints from two positions (`@[2]` here and `@[3]` there);
- any binder for which no position supplies an expected grade.

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
constraints must agree. Composite parameter grades such as `x: i64 @[G * 2]`
work in the same single-occurrence fragment. A grade parameter that only occurs
in the result of a direct call still needs explicit specialization, because a
direct call supplies no expected grade for its result.

## Function values

A generic function used as a value is checked against the expected arrow. The
arrow's concrete parameter and result grades are constraints:

```kush
fn four<G: Grade>(x: i64 @[G * 2]) -> i64 ! {panic} { x + x + x + x }
fn apply(f: fn(i64 @[4]) -> i64 ! {panic}) -> i64 ! {panic} { f(10) }

fn main() -> i64 ! {panic} { apply(four) }    // G = 2
```

Result contractions compose with the earlier alias forwarding:

```kush
fn make<G: Grade>() -> Box<i64> @[G + 1] ! {alloc, panic} { Box.new(1) }
fn apply(f: fn() -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
    Box.take(f())
}
// G + 1 = 1  =>  G = 0
```

`G * 2 = 1`, `G + G`, and extra unconstrained binders are rejected with the
usual explicit-specialization diagnostic. Explicit `::<...>` specialization
remains available and unchanged.

## Tests

`crates/kush/tests/grade_inference.rs` covers direct-call parameter inference,
composite parameters, conflicts, ungraded arguments, function-value parameter
inference, composite copyable result inference, unsolvable/ambiguous equations,
underlying-type occurrences, and native/reference agreement.
`crates/kush/tests/result_grade_inference.rs` keeps the earlier result-contract
and alias cases, updated for the solver.
