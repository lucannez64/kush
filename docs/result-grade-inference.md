# Result-grade inference for generic function values

Status: implemented for the executable subset. This milestone adds one narrow
inference rule and permits grade arguments in result-contract alias expansion.
The rule is now a special case of the [general grade inference](grade-inference.md)
solver. Effect constraints are a separate future milestone and are not part of
this work.

## Scope

A generic function used as a first-class value may leave a usage-grade
parameter implicit when **all** of the following hold:

- the expected type is an arrow (`fn(...)` or `once fn(...)`);
- that arrow declares the concrete result-transfer contract `@[1]`;
- the grade parameter is used **only** as the entire outer result grade, as in
  `-> Box<i64> @[G]`;
- the parameter does not occur in any parameter type or parameter grade, and
  does not occur in the underlying result type (including nested grade
  expressions).

In that case the checker binds `G = 1` and specializes the function value with
the existing instance machinery. The inferred specialization is validated by
the same result-contract checks (`validate_result_contract`) and must fit the
expected arrow by exact result-grade subtyping. Nothing about the runtime
representation or ABI changes.

```kush
fn make<G: Grade>(n: i64) -> Box<i64> @[G] ! {alloc, panic} {
    Box.new(n)
}

fn apply(f: fn(i64) -> Box<i64> @[1] ! {alloc, panic}) -> i64 ! {alloc, panic} {
    Box.take(f(42))
}

fn main() -> i64 ! {alloc, panic} { apply(make) }   // G inferred as 1
```

Explicit specialization remains available and unchanged:

```kush
apply(make::<1>)
```

## Alias forwarding

Transparent aliases are expanded before the result contract is read, so a
grade argument may be forwarded through one or more alias layers in a result
position:

```kush
type Handle<G: Grade, T> = Box<T> @[G];
type Forward<G: Grade, T> = Handle<G, T>;
type Nested<G: Grade, T> = Forward<G, T>;

fn make<G: Grade>(n: i64) -> Nested<G, i64> ! {alloc, panic} { Box.new(n) }
fn apply(f: fn(i64) -> Handle<1, i64> ! {alloc, panic}) -> i64 ! {alloc, panic} {
    Box.take(f(42))
}
```

`executable::expand_result_aliases` and `Types::expand_result_alias` substitute
grade arguments structurally, exactly like type and natural arguments, and the
substituted grade expression is evaluated by `result_contract` (or by the
callable-arrow result lowering) afterwards.

Grade arguments in aliases are **only** accepted in these result-contract
positions. Ordinary alias lowering in a parameter, stored field, nested
non-result type argument, or local type still rejects them with:

```text
grade parameters are not part of runtime type aliases
```

This keeps a grade from entering a runtime type where its transfer meaning
cannot be tracked.

## Preserved rejections

The following remain errors:

- indirect-call grade inference for a binder with no expected parameter or
  result grade, or outside the decidable natural/finite-algebra fragment (see
  [general grade inference](grade-inference.md));
- ambiguous equations, zero-slope expressions, and non-divisible equations;
- a grade parameter that also appears in a parameter type or in the underlying
  result type;
- an extra grade parameter that cannot be determined by the expected equations;
- an expected arrow with no result contract, or no expected arrow at all;
- result grades other than exactly `@[1]`, or `@[0]` on a copyable result,
  whether written directly or through an alias argument;
- owning/linear `@[0]` results, and `@[0]` parameters on owning/linear values;
- task results and effect-constraint inference (unchanged/out of scope).

Copyable and borrowed results may carry an explicit `@[1]` must-use contract;
see [copyable result transfer](copyable-result-transfer.md). Inference of that
contract is still governed by the same single bare outer result-grade rule.

## Tests

The focused suite is `crates/kush/tests/result_grade_inference.rs`. It covers
the positive inference path, explicit specialization, alias forwarding and
nesting, native/reference execution agreement, and the negative cases listed
above.
