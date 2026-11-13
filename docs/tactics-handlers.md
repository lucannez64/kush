# A prover whose tactics are effect handlers (design)

Status: **implemented** in [examples/tactics](../examples/tactics/README.md)
(plan node TACTICS-HANDLERS; design approved 2026-11-13). Section 7 records
where the implementation departs from the design. Builds on
[Kernel in Kush](kernel-in-kush.md) (section 5, the tactic API) and
[multishot capabilities](multishot-capabilities.md).

*A proof assistant in a few hundred lines of Kush: tactics are ordinary
functions, backtracking is resuming a continuation twice, and every proof is
checked by a kernel written in Kush.*

## 1. The demo

An example package, `examples/tactics`, depending on `examples/kernel`
(illustrative output):

```text
$ kush run --manifest-path examples/tactics/Kush.toml -- "(A -> B) -> (B -> C) -> A -> C"
goal:    (A B C : Prop) -> (A -> B) -> (B -> C) -> A -> C
proof:   fun A B C (h1 : A -> B) (h2 : B -> C) (h3 : A) => h2 (h1 h3)
search:  9 choices, 4 backtracks, depth 3
kernel:  checked by the Kush kernel
```

Goals are formulas of propositional logic over atoms `A`..`Z` with `->`, `&`,
`|` and parentheses, closed by quantifying over their atoms as `Prop`s. A
formula with no intuitionistic proof (Peirce's law) answers "no proof up to
depth N". `&` and `|` are data families declared to the kernel at start-up
(`And`, `Or` with their constructors and eliminators), so proofs use the
kernel's ordinary data rules.

## 2. Effects

| Effect | Kind | Served by |
| --- | --- | --- |
| `Choose: i64 -> i64` | multishot, through `cap multi Choose` | the search handler |
| `Fail` | `Choose` with no alternatives: `perform op(0)` | the same handler |
| `Goal: Query -> i64 ! {alloc, panic}` | declared, tail-resumptive | the engine handler, which owns the kernel |

- **`Choose`.** `perform op(n)` returns one of `0..n`. The handler is
  depth-first backtracking: it resumes with `0`, `1`, ... and returns the
  first result that is a proof (a store id, `>= 0`); if none is, it returns
  the failure value. This is the multishot capability of Phase 1: the
  continuation runs through the recursive tactic functions, and each
  alternative starts from its own copy of their live values.
- **`Fail`** is a choice among zero alternatives: the handler resumes
  nothing and returns the failure value, so the search backtracks to the
  last choice with alternatives left. It cannot be a separate effect: a
  search may hold only one multishot capability (a perform through an outer
  multishot handle inside an inner handle's body is rejected), and `multi
  fn` tokens are pure, so an abortive `Fail` could not leave through them.
- **`Goal`** is every question a tactic asks about a goal and every term it
  builds: `Whnf(context, t)`, `Defeq(context, a, b)`, `Hypothesis(context,
  i)`, `Extend(context, t)`, `Pi`, `Lam`, `App`, `Var`, ... The handler is
  a lambda capturing `&mut Kernel`; it answers in place (tail-resumptive),
  so it costs a call, and it is installed outside the search, where it
  serves performs from every resumed branch (checked by a spike: a
  `&mut`-capturing tail-resumptive handler under a `cap multi` handle).
  Errors come back as negative codes.

The answer type of the search is `i64`: a proof term's store id, or the
failure value. Every value a tactic keeps across a choice is a store id
(terms, and contexts as interned lists), so it is copyable, as multishot
requires. The store only grows, so ids from an abandoned branch stay valid;
the engine may rewind the store between top-level goals.

## 3. Proof scripts are Kush programs

A tactic is a function `fn(op: cap multi Choose ! {..}, context: i64, goal:
i64, depth: i64) -> i64 ! {Goal, ..}` that returns a proof of `goal` in
`context`. Combinators are ordinary control flow around `perform op(n)`:

```text
fn auto(op: cap multi Choose ! {panic}, context: i64, goal: i64, depth: i64)
    -> i64 ! {Goal, alloc, panic} {
    if depth == 0 { return fail(op); }
    let head = whnf(context, goal);
    if is_pi(head) {                        // intro: always safe, no choice
        let body = auto(op, extend(context, domain(head)), codomain(head), depth);
        return lam(domain(head), body);
    }
    match perform op(3) {                   // which rule?
        0 => assumption(op, context, goal),
        1 => apply_hypothesis(op, context, goal, depth - 1),
        _ => split_or_case(op, context, goal, depth - 1),   // &, |
    }
}
```

`assumption` chooses a hypothesis and fails unless its type is
definitionally equal to the goal; `apply_hypothesis` chooses a hypothesis
`h : A1 -> .. -> An -> B` with `B` equal to the goal and proves each `Ai`
recursively. The driver runs `auto` with depths 1, 2, ... (iterative
deepening), counts choices and backtracks, and finally asks the kernel to
check the closed proof term against the closed goal: the search may build
any term, and only the kernel's verdict is trusted.

Tactics cannot be first-class values (a function with a `cap` parameter is
never a function value), so combinators are functions that call tactics by
name; the scripts in the example are such functions.

## 4. Pieces

- `src/formula.kush`: the formula parser and the closed goal term.
- `src/engine.kush`: the kernel set-up (`Prop` data families `And`/`Or`),
  the `Goal` query enum and its handler.
- `src/tactics.kush`: `fail`, `assumption`, `intro`, `apply_hypothesis`,
  `split`, `cases`, `auto`.
- `src/printer.kush`: named printing of goals and proofs (`A B C`, `h1`..).
- `src/main.kush`: the command line; `tests/main.kush`: package tests.
- `crates/kush/tests/tactics.rs`: runs the package tests and a set of
  tautologies and non-theorems natively, checking each proof with the Rust
  kernel too (through the exchange format), so a bug in the Kush kernel
  cannot make a wrong proof pass unnoticed.

## 5. Limits

- Propositional logic only (implication, conjunction, disjunction); no
  quantifier instantiation, no unification or metavariables.
- The evaluator's nesting budget is small, so the package tests and the
  demo run natively.
- One multishot capability per search (section 2).

## 6. Decisions asked for

1. The three effects as in section 2, with `Fail` as `Choose(0)`.
2. The kernel owned by a tail-resumptive `Goal` handler; tactic state made of
   store ids only.
3. Propositional logic with `->`, `&`, `|` as the demo's scope, and the Rust
   kernel as a second checker in the tests.

## 7. As built

- The demo's output is in the package README; proofs of all the formulas in
  `crates/kush/tests/tactics.rs` are found in milliseconds natively, and the
  Rust kernel accepts each of them (`--kcore`).
- Module names: `tactics.state` (effects, queries, handler logic),
  `tactics.search` (tactics), `tactics.prover` (handlers, deepening),
  `tactics.formula`, `tactics.show`. `tactics.printer` would clash with the
  kernel's `printer` module (imports cannot be renamed yet).
- `Goal` queries are an enum of integer payloads; the eliminators are built
  by the engine as `ElimAnd(h, G)`, `ElimOr(h, G)`, `ElimFalse(h, G)`.
  `And` and `Or` are eliminated through a motive whose value is the
  continuation type (`(P -> Q -> G) -> G`), because a `prop` family's
  branches bind its parameters afresh.
- Statistics are counted on the tactic side (`choose` reports each choice
  through `Goal`), since the search handler captures nothing.
- `kush eval` is not supported for the demo: the evaluator's nesting budget
  is too small for the search; tests and the demo run natively.
