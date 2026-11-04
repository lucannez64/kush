# Integer refutation

The erased arithmetic fragment `{ ... }` is discharged by `crates/kush/src/facts.rs`.
Comparisons become integer inequalities

```text
sum coefficient * term <= bound
```

over runtime scalar locals and buffer lengths. The first search is
Fourier–Motzkin elimination over exact rationals with a Farkas-style
certificate. That rational relaxation is complete for rational feasibility but
not for integer feasibility: `2*x <= 1` allows `x = 1/2`, and the system
`2*x == 1` has no integer solution at all. This document describes the bounded
integer fallback that closes that gap and the independent check that every
proof must pass.

## Goal and initial system

To prove a goal `c*x <= d`, the checker refutes the initial system

```text
hypotheses  +  (integer negation of the goal)
```

The integer negation is `-c*x <= -d - 1`, because every admitted term is
integer-valued. The hypotheses are branch conditions, guards, loop conditions,
early exits, erased arithmetic parameters, lengths, and assignment/version
facts as described in [runtime-indices.md](runtime-indices.md#4a-arithmetic-proof-search).

The rational search runs first and keeps its existing behaviour: the final
Farkas conflict must use the goal negation with a positive multiplier. If that
fails, the integer fallback starts from the full initial system. Its search may
also refute the hypotheses alone when they are inconsistent; that is sound
because the goal then holds vacuously.

## Certificate rules

A certificate is a recursive refutation. It is checked without re-running the
search:

```text
refutation = Trivial
           | Farkas { steps: [constraint], multipliers: [i128], denominator: i128 }
           | Cut    { steps: [constraint], multipliers: [i128], divisor: i128,
                      result: constraint, then: refutation }
           | Branch { variable: term, threshold: i128,
                      left: refutation, right: refutation }
```

- `Trivial` is accepted only when the goal has no terms and its bound is
  non-negative, so the goal is a true constant.
- `Farkas` requires every step to be present in the current context, every
  multiplier to be non-negative, `denominator > 0`, the weighted coefficients to
  cancel exactly, and the weighted bound to be negative. The multipliers are
  numerators over the denominator; the denominator itself only shows the exact
  rational weights and does not weaken the check.
- `Cut` requires every step to be present in the current context and every
  multiplier to be a non-negative integer. The verifier recomputes
  `sum multipliers[i] * steps[i]`, checks that the gcd of the resulting integer
  coefficients is exactly the recorded `divisor` (and `divisor > 1`), and checks
  that `result` is that combination with every coefficient divided by the
  divisor and the bound rounded down:
  `bound.div_euclid(divisor)`. This is the Chvátal–Gomory rule: if all
  coefficients are multiples of `g`, the left side is a multiple of `g` for
  every integer assignment, so it can be at most `g * floor(bound / g)`.
  The verifier then checks `then` with `result` added to the context.
- `Branch` requires `left` to be refuted in the context plus
  `variable <= threshold` and `right` to be refuted in the context plus
  `variable >= threshold + 1`, encoded as `-variable <= -threshold - 1`. Every
  integer value satisfies exactly one side, so both refutations cover the whole
  integer space. The verifier rejects `Term::Zero` as a branch variable and
  rejects a threshold whose successor or negation overflows.

A cut with a bound divisible by its divisor is just the combination divided by
its gcd, so the search does not emit it: it adds no strength over the rational
system. The verifier accepts any valid rounding, including such a no-op, but the
search filters them to keep certificates small.

## Search

After the rational `prove_with` fails, `prove_integer` runs the following
bounded search on the initial system:

1. Try a complete rational refutation of the system (any negative constant
   consequence, not only one using the goal negation).
2. Generate rounding cuts from single constraints and from pairwise sums of two
   constraints. Pair sums matter when a term only cancels after addition, for
   example `(x + y <= 1) + (x - y <= 0)` gives `2*x <= 1`, whose cut is
   `x <= 0`. Add up to the cut budget, retry the rational refutation, and repeat
   for at most two rounds.
3. If the system is still not refuted, choose a variable and an integer
   threshold `t`. Candidate thresholds are `0`, the Euclidean split points
   `bound / coefficient` of constraints mentioning the variable, and for
   single-term constraints also the adjacent integers. Recursively refute
   `variable <= t` and `variable >= t + 1`. A branch succeeds only when both
   sides produce certificates.

The recursion is depth-first. Budget exhaustion in either side abandons that
candidate and leaves the obligation unproved; it never turns an incomplete
search into a proof.

## Budgets

These are work limits, not completeness claims. They are deliberately small
because the fallback runs only after the rational search has already failed.

| Limit | Value |
| --- | --- |
| Integer search depth | 4 |
| Integer search nodes | 48 |
| Cut rounds per node | 2 |
| Cuts per search | 8 |
| Pairwise cut combinations examined | 64 |
| Distinct terms in an integer system | 16 |
| Constraints in an integer system | 128 |
| Branch candidates attempted per node | 8 |
| Thresholds per variable | 6 |

The rational search keeps its existing independent budgets: 64 distinct terms,
4096 rows, and 200000 bound pairs. All coefficient arithmetic is checked; an
overflow aborts the search rather than wrapping.

## Soundness and limits

The checker only accepts a certificate after re-verifying every Farkas
combination, every cut rounding, and both sides of every branch against the
recorded hypotheses and the integer negation of the goal. A tampered
multiplier, divisor, rounded result, branch threshold, or non-member step is
rejected. When the fragment or a budget cannot establish the obligation, the
compiler reports the existing "cannot prove" diagnostic with the known facts;
it does not guess.

Deliberate limits:

- no nonlinear products, division, modulo, floats, or casts;
- cuts are generated from single constraints and pairwise sums, not from the
  full Chvátal–Gomory closure or a general integer programming solver;
- branch-and-bound is shallow and node-limited, so it is not a complete integer
  Presburger decision procedure;
- systems wider than 16 terms or 128 constraints are left to the rational
  search and otherwise rejected;
- runtime terms are `i64` and lengths; mathematical unbounded naturals remain a
  separate kernel fragment.

## Tests

`crates/kush/tests/integer_refutation.rs` covers tight scaled goals, parity
equations, double-sided tight bounds, two-variable parity, pairwise combination
cuts, independent certificate checking, genuinely feasible rejections, and the
term-budget rejection. The unit tests in `crates/kush/src/facts.rs` additionally
tamper with cut divisors, rounded results, branch thresholds, and Farkas
multipliers, verify budget exhaustion returns no proof, and exercise the branch
fallback with cuts disabled. Positive programs are compared between the
reference evaluator and the native backend.
