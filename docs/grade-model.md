# Mixed linear and graded semantics: model and erasure obligations

Status: **design specification** (RES-GRADE-MODEL). It states the semantics
Kush already implements as a two-zone judgement, lists the proof obligations a
soundness argument would have to discharge, and records decisions. It makes no
soundness claim, and none is transferred from the papers below. Implementation
of the follow-up work is tracked by the plan nodes in the last section.

Inputs, used as guides for *which obligations exist*, not as theorems:

- [A Mixed Linear and Graded Logic, CSL 2025](https://doi.org/10.4230/LIPIcs.CSL.2025.32):
  a logic with a linear context and a graded context related by modalities,
  with a categorical model. Its useful lesson for Kush is that the two kinds of
  hypotheses obey *different* structural rules and must be kept apart; a
  single "multiplicity" does not describe both.
- [A Graded Modal Dependent Type Theory with a Universe and Erasure,
  ICFP 2023](https://doi.org/10.1145/3607862): a formalized erasure theorem for
  grade-zero positions. Its calculus is pure and terminating; Kush is strict
  and effectful, so the theorem's *shape* (erasure commutes with evaluation)
  is the obligation, but its statement must change (effects of erased
  computations are kept).
- [Linear Haskell, POPL 2018](https://arxiv.org/abs/1710.09756): arrow
  multiplicity is not the same thing as a closure's invocation count.

## 1. The question

What are the contexts, structural rules, substitution rule and erasure map of
Kush's grade fragment, such that

1. copyable must-use (`T @[1]` on a copyable `T`) and owning linearity
   (`@[1]` on an owner, `#[linear]` data, `linear once fn`) stay distinct;
2. grade zero is erasure of *storage and ABI*, never of computation or
   effects;
3. every place the implementation already enforces (grades.md,
   grade-zero-erasure.md, grade-algebras.md, linear-task-results.md,
   copyable-result-transfer.md, effect-state-machines.md) is an instance of a
   stated rule, and every rule has a hostile test?

## 2. Two-zone judgement

```text
Γ ; Δ ⊢ e : T ⊣ Γ'        Γ  graded zone:  x :_r T   (T copyable, r ∈ R)
                           Δ  linear zone:  x : T @o  (T owning or intrinsically
                                                      linear; o ∈ {affine, oblig})
```

- `R` is a semiring with `0`, `1`, `+`, `*`: the builtin naturals extended with
  `many`, or a validated finite algebra (zero ≠ one, laws checked by
  enumeration). An unannotated copyable binding has grade `many`.
- The **graded zone** counts *observations* of copyable values. It is the
  "graded context" of the mixed logic.
- The **linear zone** tracks *ownership*: each owner is consumed at most once
  (`affine`) or exactly once (`oblig`: `@[1]` on an owner, `#[linear]`,
  `linear once fn`, linear task handles). It is the "linear context", with
  Kush's affine weakening added for `affine` entries (implicit drop).
- A value moves from Δ to Γ only by *consumption producing a copyable result*
  (`Box.take` of a `Box<i64>`): the owner is used once, the result may then be
  used under any demand. Nothing moves from Γ to Δ.

Output context `Γ'` records remaining counts; the implementation computes it
as the grade pass's per-path counts, and Δ's evolution is the ownership pass
(moves, drop flags, resource slots).

### Structural rules

| Rule | Graded zone Γ | Linear zone Δ |
| --- | --- | --- |
| Weakening (discard) | only grade `0` and `many` (and an algebra element `w` with `w + 0 = w` that the annotation allows); exact `n ≥ 1` must be met on every normal path | `affine`: yes, with an implicit drop (cleanup emitted); `oblig`: never, on any normal exit |
| Contraction (duplicate) | yes, counts add: `x :_{r+s}` splits into `x :_r` and `x :_s` | never |
| Exchange | yes | yes (evaluation order is left to right and fixed, but the *context* is unordered) |
| Borrow | an observation of the view, not of the owner (grades.md) | a loan, not a consumption; one borrow plus one move satisfies `@[1]` |

### Paths

Sequential composition adds counts; alternatives (`if`, `match`, `&&`/`||`
right operand, guards) must agree on exact grades; loop heads are invariants
(counts at every back edge equal the head); early exits (`return`, `?`,
`break`, `continue`, region exits of suspended bodies) check every pending
obligation in both zones. These are the implemented rules; the model adds
nothing.

## 3. Substitution and demand

**Rule (scaling).** If `Γ₁ ; Δ₁ ⊢ a : A` and `Γ₂, x :_r A ; Δ₂ ⊢ b : B`, then
`r·Γ₁ + Γ₂ ; Δ₁ ⊎ Δ₂ ⊢ b[a/x] : B` **provided** `Δ₁` is empty or `r = 1`.

- `r·Γ₁` is the call-demand composition of grades.md (`twice(x)` under `@[2]`
  costs `x` two observations). `0 · many = 0` and `n · many = many` (`n > 0`)
  are required for the rule to hold with strict evaluation: an argument to an
  `@[0]` parameter is still evaluated once, which is why grades.md assigns it
  demand **1**, not 0. This is the first place where Kush departs from the
  pure calculus: **the demand on an evaluated argument is `max(1, r)` for
  effects and `r` for observations of its copyable result.**
- The side condition `Δ₁ empty or r = 1` is the mixed logic's separation: an
  owner cannot be substituted where it could be duplicated or discarded.
  Kush implements it as "consuming uses count once even under a larger
  demand" plus the rejections of owners at `@[0]`, `@[n ≥ 2]` and `@[many]`.

**Arrows.** `fn(A @[r]) -> B @[s]` carries the parameter grade (scaling of the
argument) and a result contract `s ∈ {ungraded, 1, 0}`. `once`/`linear once`
is a property of the *closure's own invocation count*, a Δ-zone fact about
the callable value, independent of `r` (Linear Haskell's distinction).
Arrow subtyping is therefore checked on two independent axes
(functions.md, "Arrow subtyping"): parameter grades (equal for a finite
contract; an unannotated or `@[many]` target accepts any source demand; an
`@[0]` source may stand for an ordinary parameter only through a physical
adapter) and the closure mode (`fn` ≤ `once fn` ≤ `linear once fn` as a
*target*: an affine callable may be used where the caller promises exactly one
call, but `linear once` never widens to `once`).

## 4. Erasure

ICFP 2023 proves that erasing grade-zero positions commutes with evaluation
for a pure terminating calculus. Kush's statement is different and is the
obligation to discharge:

```text
|let x :_0 = a; b|      = a ; |b|        -- a still runs, its value is dropped
|f(a :_0, c)|           = a ; |f|(|c|)   -- left-to-right order kept
|fn ... -> T @[0] {b}|  = fn ... -> Unit {|b|; ()}
```

**E1 (effects kept).** For every program `p`, `eval(|p|)` performs the same
I/O, allocation, panics and divergence as `eval(p)`, in the same order.

**E2 (no observation).** No erased variable occurs in `|b|` (the checker
rejects every read, move, borrow, capture, match, or proof-free use).

**E3 (physical agreement).** Wherever two logical arrow types are
subtype-related but differ physically in erased positions, a checked adapter
reconciles the ABIs (`fn(i64 @[0]) -> T` used as `fn(i64) -> T`); the reverse
is rejected. This includes dynamic dispatch, task bodies and resumption
tokens.

**E4 (no erased obligations).** Erasure is never applied to Δ-zone `oblig`
entries: `@[0]` on a linear owner, an owning result, or an owning parameter
is rejected. An `affine` owner may be erased only as "evaluate and drop at
the binding site", which preserves allocation balance.

**E5 (proof erasure is separate).** `erased`/`prop` positions are the kernel's
mechanism: they admit only immutable machine scalars as indices and never a
graded or owning value. Naming an `@[0]` scalar in an erased type is a
compile-time observation, not a runtime use.

**E6 (custom algebras).** `@[Algebra.Zero]` is erased like `@[0]` only
because zero ≠ one is enforced; an algebra whose one is idempotent keeps its
own observation semantics (grade-algebras.md) and does not mean "exactly one
physical observation".

## 5. Boundaries with the rest of the language

| Boundary | Obligation | Current behaviour (checked 2026-11-05) |
| --- | --- | --- |
| Non-tail effect handler, one-shot token | the frame is consumed exactly once, so Γ counts and Δ obligations in the frame are preserved | `let once: i64 @[1] = 5; let a = perform Ask(0); a + once` accepted, balanced; using `once` zero times after the perform rejected |
| Multishot token | resumption duplicates the frame: only grade-`many` copyable slots allowed | `@[1]` live across a multishot perform rejected ("owned, linear, or graded and cannot be copied") |
| Owner across a perform | Δ entry moves into the frame and out exactly once | `Box<i64> @[1]` consumed after a perform accepted, allocations 2/2 |
| `@[0]` across a perform | erased slot is never captured; observation still rejected | reading an `@[0]` local after a perform rejected |
| Demand through higher-order calls | `x :_1` passed to `@[2]` costs 2 | rejected ("used 2 time(s)") |
| Tasks and cancellation | a completed payload with an obligation is delivered as `Completed`, never dropped | implemented (linear-task-results.md) |
| Borrowed views | observation of the view, not the owner; views over owning elements do not exist | implemented (grades.md) |

## Evidence (GRADE-OBLIG-TESTS, GRADE-ARROW-AXES)

`crates/kush/tests/grade_obligations.rs` has one test per obligation of
sections 2-5: Γ weakening (only `0`/`many`) and contraction, Δ weakening
(affine drop versus `@[1]`, `#[linear]` and `linear once` obligations) and no
contraction, exchange, borrows, paths (alternatives, early return, loop
heads), scaling at `r = 0, 1, n, many` and the owner side condition, E1-E6,
and the one-shot, multishot, erased-slot and task boundaries. Every positive
program runs in the evaluator and natively with balanced allocations; every
hostile program is pinned to the diagnostic of its obligation.

The arrow audit (same file) found the two axes already independent in
`function_subtype`: the closure-mode check (`linear` source needs a `linear`
target) runs before and regardless of the parameter-grade check, and the
erased-position adapter is only reached after both pass. Hostile programs
try to widen `linear once fn(i64 @[0])` to `once`/`fn` directly, through a
grade change to `@[1]`, through a two-step coercion, through a join with an
affine closure, and through a generic identity; all are rejected, and the
legitimate adapters (erased parameter to a `linear once` target, affine
erased closure to `once`) keep exactly-once calls and balanced cleanup. No
code change was needed. One documented consequence of section 3: an
unannotated target parameter is demand 1 and the callee may copy it, so
`apply(twice, a)` with `a: i64 @[1]` is accepted exactly as `dup(a)` with
`fn dup(x: i64)` is; an exact target (`fn(i64 @[1])`) rejects `@[2]`.

## 6. Decisions

1. **Two zones, never merged.** Copyable `@[1]` (Γ, must-observe) and owning
   linearity (Δ, must-consume) remain different judgements with different
   diagnostics. No surface or internal change may identify them.
2. **Erasure is binding/ABI erasure.** Kush will not erase computations at
   grade 0. Any future optimization that removes an initializer must prove it
   pure and terminating by other means; the grade is not that proof.
3. **No multiplicity-polymorphic arrows.** `once`/`linear once` stays a
   closure-mode fact separate from parameter grades. Grade-polymorphic
   function *values* stay out of scope until a design shows the adapter story
   for erased positions under polymorphism (E3).
4. **No transferred soundness claim.** The papers fix the list of obligations
   (structural rules per zone, scaling substitution, erasure commuting with
   evaluation); Kush's evidence is per-obligation hostile tests in both
   backends, not a citation.
5. **Effect-sensitive demand stays conservative.** The `max(1, r)` effect
   demand and the "side-effecting block under high demand is counted under
   that demand" rule remain; a precise version needs an effect analysis and is
   a separate node (decided in [effect-sensitive demand](grade-effect-demand.md):
   kept conservative).

## 7. Follow-up nodes

Added to `plan/plan.json`:

- **GRADE-OBLIG-TESTS** (M): one test module that names each obligation of
  sections 2-4 (weakening/contraction per zone, scaling with `r = 0, 1, n,
  many`, E1-E6) and pins a positive and a hostile program for each in both
  backends with balanced allocations; include the handler/multishot/task rows
  of section 5.
- **GRADE-ARROW-AXES** (S): audit arrow subtyping and adapters so the
  parameter-grade axis and the closure-mode axis are checked independently
  (section 3), with hostile programs that try to widen `linear once` through
  a grade change or an erased-position adapter.
- **GRADE-EFFECT-DEMAND** (M, research): specify an effect-sensitive demand
  rule (section 3 departure, decision 5) and decide whether hoisting is
  enough; no implementation before the design.
