# Effect-sensitive demand for graded arguments

Status: **design, decided** (GRADE-EFFECT-DEMAND). It specifies a precise
demand rule, compares it with today's conservative rule and with hoisting, and
decides not to adopt it now. Nothing in the checker changes; one diagnostic
node is added.

Input, used as a guide only: Torczon, Suárez Acevedo, Agrawal,
Velez-Ginorio and Weirich, [Effects and Coeffects in
Call-By-Push-Value](https://doi.org/10.1145/3689750) (OOPSLA 2024,
[extended version](https://arxiv.org/abs/2311.11795)). In its call-by-value
translation an argument is a computation that runs once and *returns* a
value; only that value is subject to the parameter's grade. That is the shape
of the precise rule below. No result transfers: Kush's grade pass is not that
calculus and has no mechanized semantics.

## 1. Today's rule

`grades.rs` checks a call argument `e` under `multiplier × demand(param)`,
where `demand` is `1` for an unannotated or `@[0]` parameter and `r`
otherwise (grade-model.md section 3: `max(1, r)` for effects, `r` for
observations). *Every* use of a copyable binding anywhere in `e` is scaled,
even a use whose value never reaches the argument's result. Checked on
2026-11-05 with `fn twice(v: i64 @[2]) -> i64 ! {panic} { v + v }`:

| Program | `x` | Today |
| --- | --- | --- |
| `twice({ print_i64(x); 5 })` | `@[1]` | rejected, "used 2 time(s)" (x is read once) |
| `twice({ print_i64(x); 5 })` | `@[2]` | **accepted** (x is read once, counted 2) |
| `let t = { print_i64(x); 5 }; twice(t)` | `@[1]` | accepted (hoisted) |
| `twice(x + 1)` | `@[1]` | rejected, "used 2 time(s)" (value flows) |
| `twice(id(x))` | `@[2]` | accepted |

## 2. The precise rule

Split the uses of a tracked binding `x` inside an argument `e` passed at
demand `r`:

- a **value use** may reach the value `e` returns: the tail of a block, an
  operand of an operator whose result is the tail, an argument of a call whose
  result is the tail, a capture of a closure that is the tail, a borrow
  (`&x`) anywhere in `e` (the view may be stored), a write into a local that is
  later read by a value use, a match scrutinee whose arms return values;
- an **effect use** is every other use: a statement-position call whose result
  is discarded (`print_i64(x);`), a `let` whose binder is never read by a
  value use, a condition whose branches return values independent of `x`.

Counting: a value use counts `max(1, r)` as today; an effect use counts `1`
(algebra `one` for custom algebras), because the argument is evaluated exactly
once. The classification is a backward dependency analysis over the checked
`Expr` of the argument, conservative in the unknown direction: anything the
analysis cannot classify (mutable locals written through references, loops
that carry values, nested handlers or performs) is a value use, i.e. today's
count. At `r ∈ {0, 1}` both counts are 1, so the rule only differs for
`r = n ≥ 2`, `many`, and algebra elements other than zero and one.

This is a *value-dependency* analysis rather than an effect analysis: whether
`e` performs effects does not matter, only whether `x` reaches the returned
value. Purity would only matter for an optimization that removes the
evaluation, which decision 2 of grade-model.md forbids.

## 3. Comparison

| | Today (conservative) | Precise rule | Hoisting |
| --- | --- | --- | --- |
| `twice({ print_i64(x); 5 })`, `x: @[1]` | rejected | accepted | write `let t = { print_i64(x); 5 }; twice(t)`: accepted today |
| same, `x: @[2]` | accepted | **rejected** (used 1 of 2) | n/a |
| `twice(x + 1)`, `x: @[1]` | rejected | rejected | n/a (a genuine value use) |
| implementation | none | a dependency analysis inside `grades.rs`, the pass that already carries exact-count, loop and early-exit rules | none |

Hoisting is always available. Kush evaluates arguments left to right before
the call and every argument is evaluated exactly once, so rewriting
`f(a, g({ s; v }))` to `let t1 = a; s; let t2 = g(v); f(t1, t2)` preserves
order, effects and cleanup. The precise rule therefore adds convenience, not
expressiveness.

## 4. Decisions

1. **Keep today's rule.** It is sound and a strict over-approximation; every
   program it rejects for an effect use can be hoisted by the programmer.
2. **Do not adopt the precise rule now.** It would reject programs accepted
   today (the `x: @[2]` row), which is a user-visible behaviour change that
   needs explicit user approval, and it adds a dependency analysis to the
   grade pass for a convenience case. Revisit only if real programs show
   frequent hoisting of effect-only uses, and then with the user's approval of
   the compatibility change shown in section 3.
3. **Improve the diagnostic instead.** When an exact-grade violation is
   caused only by uses that are syntactically in statement position of a
   block argument under demand `r ≥ 2`, the error suggests hoisting that block
   before the call. This changes diagnostic text only.

## 5. Follow-up nodes

- **GRADE-DEMAND-HINT** (S): the hoisting suggestion of decision 3, with
  tests that the suggestion appears for statement-position uses, does not
  appear for value uses (`twice(x + 1)`), and that accepted/rejected verdicts
  are unchanged.
