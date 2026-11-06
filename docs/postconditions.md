# Postconditions (`ensures`)

Status: implemented (ENSURES, 2026-11-06; syntax approved by the user).
Tests: `crates/kush/tests/postconditions.rs`.

A function may promise facts about its result. The checker proves each
promise at every value the function returns, and every caller receives it as
a fact about that call's result.

```kush
enum Decision { Accept(i64), Reject }

fn decide(x: i64, limit: i64) -> Decision ! {}
    ensures Accept(v) => { v == x && x <= limit }
    ensures Reject => { x > limit }
{
    if x <= limit { Decision.Accept(x) } else { Decision.Reject }
}

fn is_accepted(d: Decision) -> Bool ! {}
    ensures result => { d is Accept }
    ensures !result => { d is Reject }
{
    match d { Decision.Accept(_) => true, Decision.Reject => false }
}

// A theorem about a composition: proved, not tested.
fn never_over(x: i64) -> Bool ! {} ensures { !result } {
    if x > 100 { is_accepted(decide(x, 50)) } else { false }
}
```

## Syntax

Clauses follow the effect row, before the body:

| Clause | Meaning |
| --- | --- |
| `ensures { P }` | `P` holds of every returned value |
| `ensures result => { P }` | a `Bool` result that is `true` satisfies `P` |
| `ensures !result => { P }` | a `false` result satisfies `P` |
| `ensures V(a, b) => { P }` | an enum result of variant `V` satisfies `P`, with `a`, `b` naming its payload |

`P` is a proposition of the `{ .. }` fragment
([runtime indices](runtime-indices.md) 4a: linear integer comparisons,
`Bool` atoms, `&&`, `||`, `!=`, `!( .. )`) whose terms may be parameters,
`result`, guard binders, field paths such as `facts.has_pin` or `p.revision`,
and `value is Variant`. `is` exists only inside `ensures`.

## Predicates in propositions (ENSURES-PREDICATES)

A proposition may call a *predicate*: a function returning `Bool`, with no
type or erased parameters, that has exactly one `ensures result => { P }` and
one `ensures !result => { !(P) }` (or `P` written as `!(Q)` with
`!result => { Q }`). The call `pred(a, b)` then means `P` with `a`, `b` for
the parameters, in goals and hypotheses alike; predicates may call other
predicates.

```kush
fn first_ok(f: Facts) -> Bool ! {}
    ensures result => { !f.has_pin && bound(f) }
    ensures !result => { !(!f.has_pin && bound(f)) }
{ !f.has_pin && bound(f) }

fn plan(f: Facts) -> Decision ! {}
    ensures First(r) => { first_ok(f) && r == f.revision }
    ..
```

Each call in a clause is checked where the clause is declared: the callee
must be such a predicate (the `!result` clause is compared syntactically with
the negation of the `result` clause, so the pair defines the call exactly),
arguments must be names or field paths, and a predicate may not use itself.

## Checking a function

The body is checked as usual. Every returned value is a *return point*: the
tail of the body, the tails of `if`/`else` branches, `match` arms and blocks
in return position, and every `return e`. At each one, each clause is proved
from the facts that reach that point (branch conditions, `match` arms, earlier
postconditions, erased preconditions). The proof is a certificate re-checked
by the independent verifier, like every other obligation. Parameters denote
their values on entry.

Restrictions, each a diagnostic:

- `?` cannot leave a function with postconditions (match and return
  explicitly);
- a function without a body (foreign, trait declaration) or a `total`
  definition cannot declare `ensures`;
- a lambda's returns are its own: it does not see the enclosing function's
  postconditions.

Postconditions are partial correctness: they hold *if* the function returns.
A recursive call may use the function's own postcondition.

## Using a postcondition

Each direct call of a function with postconditions gets a fresh symbolic
identity for its result. Its clauses become facts about that identity and the
actual arguments, as `!guard || P`:

- `let d = decide(n, 10)` binds `d` to the identity;
- `match d { Decision.Accept(v) => .. }` adds `d is Accept` in that arm and
  binds `v` to the payload, so `v == n && n <= 10` is known there;
- `if is_accepted(d) { .. }` adds the `result => ..` fact in the branch;
- a call nested as an argument (`is_accepted(decide(x, 50))`) passes its
  identity on.
- a method call `value.method(args)` is a call with the receiver as its
  first argument (ENSURES-METHODS): `match l.decide(7) { .. }` and
  `if l.allows(x) { .. }` know the method's clauses about `self` and `x`.

- a call in the right operand of `&&` or `||` keeps its facts after the
  expression, guarded by the condition under which it ran:
  after `a && f(x)`, the caller knows `!a || (facts of f(x))`;
- `let b = condition` records that `b` holds exactly when the condition
  does, so `let bound = p && q; if bound { .. }` knows `p` and `q`.

An argument that is not a local, a field path, a call result, a struct literal
(in declaration order) or a linear expression is unknown to the facts; atoms
mentioning it are dropped from the caller's hypothesis, which only weakens it.

## Terms

The prover's terms gain *paths* (`facts.rs`, `Term::Path`): a root (a local at
a version, or one call's result) followed by record field offsets, an enum
tag, or a variant payload offset. A path term carries its type's range
(`0..=1` for a `Bool`, `0..variants-1` for a tag). Assignment to a local
invalidates its paths; field writes only happen through `&mut` references,
which already make the local opaque to the prover.

## Soundness review (2026-11-06)

An adversarial review found false facts reaching code that ran; each is now
rejected and has a regression test (`review_regressions_for_postconditions`):

- a unit result returned implicitly (no tail, or an `if` without `else` in
  return position) is now a return point;
- a `Bool` goal is never weakened: an unknown part of `a && f(x)` makes the
  postcondition unstatable instead of dropping `f(x)`;
- a branch join drops the aliases of locals replaced on either path, and a
  loop drops the facts and aliases of every local it reassigns (not only
  scalars);
- any exclusive borrow (`&mut x`, `&mut x.field`, a `&mut self` method
  receiver, a mutable slice) makes its root local opaque to the facts, and a
  reference is never a value root, so writes through `&mut` cannot leave stale
  facts;
- a dropped hypothesis is skipped instead of being recorded as `false`;
- a foreign `Bool` result is normalised to 0 or 1 natively, matching the
  range the prover assumes;
- `IntOp::Unchecked` wraps like the machine operation in the evaluator too,
  so a wrong proof could never make the two backends disagree.

## Limits

- An exclusive reference parameter (`&mut T`) cannot be mentioned in a
  postcondition. A shared one (`&T`, including `self: &Self`) can
  (ENSURES-REFS): it denotes its referent, which cannot change while the
  reference is usable, so `l.max` means the referent's field in the body, in
  the clause and at the caller, where `&l` stands for `l` itself. An
  exclusive borrow of the owner still makes it opaque.
- `match` on a `Bool` with `true`/`false` arms does not record the condition;
  use `if`.
- Hypotheses wider than 32 cases are dropped (sound, weaker).
