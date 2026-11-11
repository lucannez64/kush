# Postconditions (`ensures`)

Status: implemented (ENSURES, 2026-11-06; syntax approved by the user).
Tests: `crates/kush/tests/postconditions.rs`.

Proof usability additions (2026-11-11, tests in
`crates/kush/tests/proof_usability.rs`): [well-founded recursion and
`decreases`](#recursion-and-decreases), [guards on a path](#syntax),
[length terms](#lengths), [struct update](#struct-update) and
[readable proof failures](#proof-failures). The `decreases` clause and the
`path is Variant(..) =>` guard are new syntax and still need the user's
approval; the recursion check and the length facts need a soundness review.

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
| `ensures path is V(a, b) => { P }` | the enum at `path` (from `result` or a parameter, e.g. `result.effect`) of variant `V` satisfies `P`, with `a`, `b` naming its payload |
| `decreases { m }` | after the clauses: the measure that justifies recursive calls (see below) |

`P` is a proposition of the `{ .. }` fragment
([runtime indices](runtime-indices.md) 4a: linear integer comparisons,
`Bool` atoms, `&&`, `||`, `!=`, `!( .. )`) whose terms may be parameters,
`result`, guard binders, field paths such as `facts.has_pin` or `p.revision`,
and `value is Variant`. `is` exists only inside `ensures`.

A guard on a path names the payload of an enum inside a record result,
which a plain proposition cannot:

```kush
fn step(d: Driver, e: Event) -> Transition ! {}
    ensures result.effect is Insert(permit) => { permit.epoch == d.epoch }
```

### Lengths

`Vec.len(x)`, `Bytes.len(x)`, `Slice.len(x)`, `String.len(x)` and
`Str.len(x)` are linear terms when `x` is a parameter, `result`, a guard
binder or a field path (`&x` is accepted as in code):

```kush
fn push1(v: Vec<i64>) -> Vec<i64> ! {alloc, panic}
    ensures { Vec.len(result) == Vec.len(v) + 1 }
{ Vec.push(v, 1) }
```

The prover knows the length of a value that is moved or bound (`let w = v`),
returned by a call with a length postcondition, stored in a record field at
construction, or built by `Vec.push`/`Bytes.push` (one more), `Vec.new`,
`Vec.with_capacity`, `Vec.clear`, `Bytes.with_capacity`, `Bytes.clear`
(zero), `Vec.reserve` (unchanged) or a bytes literal. A reassigned local has
a new length; a local borrowed with `&mut` has none. Contents are not
modelled: there is no equality of two `Bytes` or `String` values.

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
A recursive call may use the function's own postcondition, provided the
recursion is shown to end.

## Recursion and `decreases`

A postcondition proved with the help of a recursive call is an induction, and
an induction needs a well-founded order. Without one this was accepted:

```kush
fn f(x: i64) -> i64 ! {} ensures { result > x && result < x } { f(x) }
```

`f` never returns, so the clause says nothing, but it reads as a theorem.
Every call that receives postcondition facts and closes a cycle of functions
using each other's postconditions must now make progress:

- **A direct self-call without `decreases`** is accepted when one argument is
  a strict part of the same parameter's value on entry (a payload or field
  reached by `match`, possibly through `Box.take`), or is an integer proved
  at least 0 and smaller than that parameter on entry. Values are finite
  trees (boxes are uniquely owned, record layouts are finite), so a strict
  part is strictly smaller.
- **With `decreases { m }`**, where `m` is a linear integer expression over
  the parameters, each such call must prove
  `0 <= m(arguments) < m(parameters on entry)`. Mutual recursion needs a
  `decreases` on every function of the cycle; the callee's measure of the
  arguments is compared with the caller's measure on entry.

```kush
fn count(items: List) -> i64 ! {} ensures { result >= 0 } {
    match items {
        List.Nil => 0,
        List.Cons(_, rest) => count(Box.take(rest)),   // a part of `items`
    }
}

fn upto(i: i64, n: i64) -> i64 ! {} ensures { result >= 0 }
    decreases { n - i }
{
    if i >= n { 0 } else { upto(i + 1, n) }
}
```

The cycle is found on mentions, a superset of direct calls: an edge `a -> b`
exists when the body of `a` names `b` and `b` has postconditions.

What this does **not** cover: loops, panics, and calls of functions without
postconditions. A function whose `while` never ends still satisfies its
clauses vacuously; the check only makes proofs *by recursion* well-founded.
A function that is meant to diverge on some inputs must do so with a loop,
not with a recursive call that uses its postcondition.

## Struct update

`Path { field: value, ..base }` builds a record whose unwritten fields are
read from `base`:

```kush
Driver { stage: Stage.Done, restored: true, ..d }
```

`base` is a local or a field path (bind anything else with `let` first), is
written last, and must leave at least one field to copy. The result is built
in declaration order, so it stays visible to the postcondition facts
(`result.n == d.n` is known for a copied `n`). A copied field cannot own heap
data (the ordinary rule against moving an owned field out of a record); a
written field can.

## Proof failures

A failed proof lists the known facts in source terms: record fields and
variants by name (`d.stage is Done`, `!t.driver.restored`), call results by
callee (`step(..).effect is Complete`), lengths as `len(x)`, the value of a
local before a reassignment as `old(x)`, and a pair of opposite inequalities
as an equality. Facts that only restate a type's range are omitted.

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

- Termination is checked for recursion only (see above).
- Length facts stop at `&mut` borrows, `Vec.pop`, `Vec.set`, slices of a
  vector (`&v[a..b]` has its own, unrelated length) and the length of a field
  read through a borrow (`Vec.len(&q.items)`).
- `Path { ..base }` with no written field is not parsed; it is a copy.

- Method calls (`value.method()`) do not yet receive postcondition facts;
  only direct calls of named functions do.
- `match` on a `Bool` with `true`/`false` arms does not record the condition;
  use `if`.
- A struct literal whose fields are written out of declaration order is
  checked through temporaries that the facts do not see.
- Hypotheses wider than 32 cases are dropped (sound, weaker).
