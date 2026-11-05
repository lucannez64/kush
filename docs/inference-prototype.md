# Bounded multi-bound polymorphic inference: prototype evaluation

Status: **research prototype, evaluated** (RES-INFERENCE-PROTOTYPE). The
prototype is the isolated crate `crates/infer-proto` (`kush-infer-proto`); the
compiler does not depend on it. Its corpus is
`crates/infer-proto/tests/corpus.rs` (run `mbx test -p kush-infer-proto`;
`target/debug/examples/corpus` prints every result). This document records
what it showed and what Kush will and will not adopt.

Input: [When Subtyping Constraints Liberate (SuperF), POPL 2024](https://doi.org/10.1145/3632890).
SuperF infers first-class polymorphism by keeping *several* lower and upper
bounds per type variable instead of unifying, with a termination heuristic.
It is a type-inference algorithm for its own calculus; it is not a lifetime
solver and says nothing about representations, ownership, grades or effects.

## 1. What the prototype implements

- A lambda calculus with `int`, `bool`, arrows carrying an effect row
  (`io`, `alloc`, `panic` bits), `let`, `if`, and annotations.
- Multi-bounded type variables with level-based let-polymorphism
  (Simple-sub's `constrain`/`extrude`/instantiate, the core SuperF builds on).
- Effect rows as a lattice: each arrow has an effect variable whose lower
  bound grows; annotated rows are fixed upper limits.
- **Annotation escape hatch:** `(lam (f : (forall (a) T)) body)` gives a
  first-class polymorphic parameter, instantiated freshly at each use and
  checked against rigid variables at each call; `(ann e T)` checks a
  monotype.
- **Deterministic budgets:** a step budget over every solver operation and a
  recursion-depth budget (512); exhaustion is `Failure::Budget`, never
  success.
- **Kush fit check:** the type of the program *and of every binding* is
  coalesced (variable bounds folded into unions/intersections, arrow bounds
  merged) and classified as `Direct` (a Kush type), `NeedsUnionCoercion`
  (only expressible as a Kush union of distinct representations), or
  `Unrepresentable` (recursive types, intersections of distinct concrete
  types).

Deliberately missing: records, ownership, lifetimes, grades, effect-row
generalization (instances of a let-bound function share its row), and
co-occurrence simplification of variables.

## 2. Corpus results

| Program (abbreviated) | Result | Fit |
| --- | --- | --- |
| `λx. x`, apply, compose | `'a -> 'a`, ... | Direct |
| `let id = λx. x in if id true then id 1 else 2` | `int` | Direct |
| `let inc = λx. add x 1 in inc 41` (no parameter annotation) | `int` | Direct |
| `λf. λx. f (f x)` | `(('a2 \| 'a3) -> ('a3 & 'a4)) -> ('a2 -> 'a4)` | Direct only after unifying variables (not done) |
| `λc. if c then 1 else true` | `bool -> (int \| bool)` | NeedsUnionCoercion |
| `λf. if f true then f 1 else 0` (unannotated "rank 2") | `((int \| bool) -> (bool & 'a)) -> int` | NeedsUnionCoercion |
| same with `f : ∀a. a -> a` | `<∀> -> int`; applying to `λx. x` gives `int`; to `λx. add x 1` is rejected | Direct |
| `λx. print x` | `int ->{io} int` | Direct |
| that, annotated pure | rejected: effects exceed the annotated row | |
| `λx. x x`, `let w = λx. x x in w w` | accepted by the solver with a recursive type | Unrepresentable (checked per binding) |
| `1 2`, `if 1 ...`, unbound names | type errors | |

Budget behaviour (`p_{k+1} = λy. p_k (p_k y)` with `p_0 = λx. λg. g x x`):
2 levels use 724 steps, 4 levels 1,775,072 steps, 6 levels exhaust a
2,000,000-step budget; 40 levels hit the depth budget. The milder chain
`f_{k+1} = λy. f_k (f_k y)` grows about 4x per two levels and hits the depth
budget at 8 levels. Without the depth budget, 10 levels overflowed the
native stack in the first version: a step budget alone is not enough.

## 3. Findings

1. **The practical win is local, rank-1.** Everything Kush already expresses
   with explicit generics infers with no annotation, and so do unannotated
   lambda parameters used at one type: Kush requires every lambda parameter
   and result to be annotated today.
2. **Subtyping joins silently introduce representation changes.** Where HM
   would reject (`if c then 1 else true`) or force polymorphism, multi-bound
   inference answers with a union. In Kush a union of distinct
   representations is a *checked coercion with a runtime repack* at each
   injection, and a function used through a wider domain needs an adapter.
   An inference engine that inserts these silently changes cost and layout
   behind the programmer's back.
3. **Unannotated "first-class polymorphism" mostly becomes union
   monotypes.** The rank-2 example is accepted without annotation, but at
   type `(int | bool) -> bool`, not `∀a. a -> a`: a different program (an
   `int -> int` argument is now rejected at the call, and `id` is used through
   a union adapter). Real polymorphism still needs the annotation, and in
   Kush a polymorphic *value* would need a uniform representation or
   dictionary passing, which conflicts with monomorphized code and the
   private ABI.
4. **Recursive types must be rejected at every binding,** not only in the
   final type: `let w = λx. x x in w w` has an ordinary result type.
5. **Readable Kush signatures need variable merging** (co-occurrence
   simplification). Without it `λf. λx. f (f x)` prints as unions and
   intersections of variables instead of `fn twice<T>(f: fn(T) -> T, x: T)`.
6. **Budgets must bound both work and depth,** and let-polymorphism over
   bound sets is exponential in realistic nesting (4 levels already cost
   1.7M steps), so any integration must be local (per function or per
   lambda), never whole-program.
7. **Effects fit; grades and ownership do not.** Effect rows are a lattice
   and flow like types (lower bounds join, annotations cap). Grades are a
   semiring with exact-use obligations (grade-model.md): a join of `@[1]` and
   `@[2]` is not a valid grade for either path, so grades stay with the
   existing exact solver (grade-inference.md). Ownership and lifetimes are
   not subtyping inference problems in this sense and remain with the
   lifetime solver; nothing here replaces it.

## 4. Decisions

1. **Do not integrate a general SuperF/Simple-sub solver** into the checker.
   Kush keeps explicit generics, its principal finite union inference
   (subtyping.md) and explicit specialization for grades and multiple row
   variables.
2. **No first-class polymorphic values** in the executable language. The
   `forall` annotation escape hatch is recorded as the only sound route if
   that ever changes, and it needs a representation design first.
3. **Adopt one narrow extension:** inference of unannotated *lambda
   parameter, result and effect* types, local to one function, accepted only
   when every binder coalesces to a `Direct` Kush type with no inserted union
   coercion and no recursive type, within fixed step and depth budgets; any
   other outcome asks for the annotation it is missing. Unions remain
   available, but only by annotation.
4. Integration criteria for that extension (all required): representation
   (no implicit union coercion or adapter), effects (inferred rows must equal
   what an annotation would demand; no row generalization), grades (lambda
   parameters inferred as ungraded; graded parameters still annotated),
   ownership (an inferred parameter type never decides between owning and
   borrowed: owning/borrowed/`once` types must come from use sites that fix
   them, otherwise annotate), determinism (budget exhaustion is a diagnostic).

## 5. Follow-up nodes

Added to `plan/plan.json`:

- **I-PROTO-SIMPLIFY** (S): add co-occurrence simplification/variable
  merging to the prototype and re-run the corpus; required before
  I-LAMBDA-INFER can promise readable diagnostics.
- **I-LAMBDA-INFER** (L): the narrow extension of decision 3 in the checker,
  with the criteria of decision 4, positive/rejection/parity/cleanup tests
  and a corpus of real Kush lambdas.
