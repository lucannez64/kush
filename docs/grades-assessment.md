# Are grades under-developed or not useful?

Status: **decided**: option G-B, after the foundation work (user, 2026-11-24). Decision input for plan node FND-GRADE-DECIDE
([foundations-review.md](foundations-review.md) section 5). Every behavior
below was checked against the release compiler on 2026-11-24.

## 1. Answer

Graded types are a useful idea. Kush implemented the least useful part of them.

What Kush has is an **exact count of observations of a binder**: a parameter
or `let` graded `@[2]` must be read exactly twice on every path. Graded types
earn their place elsewhere: as **upper bounds** that can be weakened, carried
**inside types and data**, propagated **through results**, over carriers such
as **security levels, intervals or real numbers**. Kush has none of those four
properties, so the uses graded types are known for cannot be written. The
problem is the slice that was built, not the idea.

## 2. What exists

- `T @[g]` on a function parameter, a simple `let`, and (only `@[1]`) a result
  ([grades.md](grades.md)).
- Grades: naturals, `many`, `+` and `*`, abstract `G: Grade` parameters, and
  user algebras with finite carriers (at most 64 elements) whose semiring laws
  are checked by enumeration ([grade-algebras.md](grade-algebras.md)).
- An inference solver for grade parameters over that fragment
  ([grade-inference.md](grade-inference.md)), grade-zero erasure of bindings
  ([grade-zero-erasure.md](grade-zero-erasure.md)), and `@[1]` result
  contracts for owners and copyable values.
- About 2,500 lines in `grades.rs`, grade handling throughout `executable.rs`,
  about 2,800 lines of grade tests, 1,400 lines of grade docs.
- Users: showcase examples only. std, the Game Boy, JSON, OTP and the kernel
  port write no grade.

## 3. Probes

| Program | Result | Why it matters |
| --- | --- | --- |
| `fn f(x: i64 @[2]) -> i64 { x }` | rejected: "used 1 time(s) … requires exactly 2" | grades are exact, not "at most"; the spec (7.1) says at most |
| `if c { x + x } else { x }` with `x: i64 @[2]` | rejected: paths must agree exactly | no join or weakening across branches |
| `struct S { x: i64 @[1] }` | rejected: not allowed on fields, type arguments, arrays | a grade cannot travel with data |
| `fn f<G: Grade>(x: i64 @[G])` called as `f(1)` | rejected: cannot infer `G` | polymorphism needs explicit `::<>` |
| algebra `Sec { Lo, Hi }`; `fn leak(s: i64 @[Sec.Hi]) -> i64 { s }`; `print_i64(leak(pin))` | **accepted, prints 1234** | a "secret" grade does not stop a leak |

## 4. What graded types are used for, and what each needs

| Use | Example | Needs | Kush today |
| --- | --- | --- | --- |
| Must-use results | a returned token must be handled | exactly-once on results | yes (`-> T @[1]`) |
| Linearity / ownership | a file closed once | exactly-once on owners | yes, but ownership and `#[linear]` already do it |
| Erasure | a value used only in types | grade 0 | yes for bindings; `erased` already covers proofs |
| Usage budgets | a callback called at most `n` times | upper bounds (ordered semiring), subgrading | **no**: exact only |
| Information flow | secrets never reach public output | a lattice with an order, grades on results and data | **no**: no order, results only `@[1]`, no fields; the leak above compiles |
| Differential privacy (DP-GRADES) | a query spends at most ε | real or rational sensitivities, scaling through function results (Fuzz, Duet) | **no**: finite carriers only, no grades on results |
| Resource or cost bounds | at most `k` allocations | grades composed through calls and results | **no** |

The two rows Kush supports are the two that overlap with mechanisms it already
has. The rows that would be new (budgets, information flow, privacy, costs)
all need at least one missing property.

## 5. What a useful version needs

1. **Order and subgrading.** An algebra declares `≤`; `@[g]` means "at most
   `g`"; a value graded `g` may be used where `h ≥ g` is allowed; branches
   take the join. This turns exact counting into bounds.
2. **Grades in types.** A graded type former usable in fields, type
   arguments and results (`Box`-like `T @[g]` as a type, or Granule's
   `[] g A`), with introduction and elimination rules. This lets a grade
   travel with data, which information flow and privacy need.
3. **Grades on results and arrows.** A function's result grade depends on its
   argument grades (`sensitivity(f(x)) = 2 · sensitivity(x)`).
4. **Infinite carriers.** Naturals with order, intervals, non-negative
   rationals for ε, and lattices; constraints solved by a decision procedure
   rather than enumeration (Granule uses an SMT solver). The rational
   Fourier–Motzkin search in `facts.rs` could serve linear constraints.
5. **Interaction rules** with ownership, borrowing, effects and erasure, which
   the spec lists as a research gate (7.1) and
   [grade-model.md](grade-model.md) only begins.

Of today's code, the syntax, algebra declarations, law checking and the
counting pass could be reused; the exact-match rule and the binder-only
placement would be replaced.

## 6. Options

### G-A. Remove now, redesign later if wanted

Delete copyable grades, user algebras, the grade solver and grade-zero binding
erasure. Linearity becomes a property of types (`#[linear]` data, linear
callables); must-use results become an attribute or a `#[linear]` result type.
DP-GRADES is dropped, or reopened later as a new design built on section 5.
Removes most of `grades.rs` (2,500 lines; the part that tracks linear
obligations moves to ownership), its 2,800 lines of tests, and one of the three
linearity spellings.

### G-B. Upgrade to graded modal types

Implement section 5 as a designed feature, then DP-GRADES and an
information-flow library on top. Large, and it is research: no systems language
ships graded modal types with ownership and borrowing today.

### G-C. Freeze

Keep everything as it is, add nothing, unify only the linearity spellings.
Costs nothing now, but the code keeps being touched by every change to the
checker (the reference and inference work in sections 1 and 6 of the review)
without any user.

## 7. Recommendation

G-A, unless differential privacy or information flow is a showcase you want
soon. In that case G-B is the honest route, because it has to replace the
exact-count rule that today's code is built on. The web framework already
handles injection with plain types (`Html` escaping in
[web.md](web.md)), so information flow alone does not require graded types.
