# 10. Usage grades

Planned change (decided, G-B, after the foundation work): grades become
graded modal types, with order and subgrading, grades in types and results,
and infinite carriers ([grades-assessment.md](../grades-assessment.md)).
This chapter describes the current, narrower behavior.

## What a grade means today

`T @[g]` on a function parameter or a `let` binding fixes **exactly** how many
times the binding is observed on every path that returns normally. Grades
are compile-time only.

| Grade | On a copyable value | On an owning or linear value |
| --- | --- | --- |
| none | unrestricted | moved at most once (affine) |
| `@[0]` | never observed; the binding is not stored | rejected |
| `@[1]` | observed exactly once | consumed exactly once (linear) |
| `@[n]`, `n ≥ 2` | observed exactly `n` times | rejected |
| `@[many]` | unrestricted | rejected |

```kush eval
fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }

fn main() -> Unit ! {io, panic} {
    print_i64(twice(21));
}
```

```output
42
```

Exact means exact, also across branches:

```kush reject
fn f(x: i64 @[2]) -> i64 ! {} { x }
fn main() -> i64 ! {} { f(1) }
// error: the annotation requires exactly 2
```

```kush reject
fn f(c: Bool, x: i64 @[2]) -> i64 ! {panic} { if c { x + x } else { x } }
fn main() -> i64 ! {panic} { f(true, 1) }
// error: exact grade @[2] must match on every normally surviving path
```

Grades may not appear on fields, type arguments or array elements:

```kush reject
struct S { x: i64 @[1] }
fn main() -> i64 ! {} { 0 }
// error: they are not allowed on stored fields
```

## Result contracts

`-> T @[1]` is the only result grade. On an owning or linear result it hands
the caller a linear obligation; on a copyable result it makes the result
must-use.

```kush eval
fn make(n: i64) -> Box<i64> @[1] ! {alloc, panic} { Box.new(n) }

fn main() -> Unit ! {io, alloc, panic} {
    let b = make(41);
    print_i64(Box.take(b) + 1);
}
```

```output
42
```

## Grade expressions, parameters and algebras

Grades are naturals, `many`, `+`, `*`, and abstract parameters `G: Grade`
(given with `::<...>` when they cannot be inferred from an explicitly graded
argument). A `grade algebra` declares a finite carrier (at most 64 elements)
with `add` and `mul` tables; the compiler checks the semiring laws by
enumeration ([grade-algebras.md](../grade-algebras.md)). Algebras have no
order, so they express exact counting only: a value graded with a "secret"
element of a two-element algebra can still be printed.
