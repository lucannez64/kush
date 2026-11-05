# Research translated into Kush work

This document replaces the broad adoption claims from the research discussion
with checked applicability boundaries. Published semantics for another calculus
are design inputs, not a proof of Kush's implementation. The immediate compiler
change is RES-HANDLER-ELIDE; the other nodes below remain research/design work.

## Immediate change: handler-free paths

[Zero-Overhead Lexical Effect Handlers, OOPSLA 2025](https://doi.org/10.1145/3763177)
([author paper](https://cs.uwaterloo.ca/~yizhou/papers/zero-oopsla2025.pdf))
separates efficient mainline execution from rarer exceptional effects. Its
translation is for lexical handlers; it is not a generic promise of free
frequent resumptions or an instruction to replace dynamic lookup.

Kush currently pays for `kush_handler_depth` at every generated function entry
and loop setup, and `kush_handler_restore` at returns and loop exits. When the
function has no local `HandlerPush`, those operations cannot clean up a local
frame: there is no such frame. Each generated callee remains responsible for
restoring its own local handlers. A checked runtime foreign boundary must obey
the existing runtime protocol; arbitrary corruption of the handler stack is
not made safe by this optimization.

The native backend now scans the checked body with the exhaustive
`Expr::for_each_child` walker. It includes guards, conditions, initializers and
capture operands; callback bodies are compiled and analyzed separately. A
function containing any local handler push keeps the original function and
loop bookkeeping. Otherwise it omits the depth snapshot/restore operations.
Dynamic lookup, handler push/pop, effect rows, capture ownership, task isolation
and continuation semantics are unchanged. Source review also confirms the
scalar callback inliner admits only constants/inputs/bitwise expressions, so
it cannot introduce an unseen handler push after this analysis. Release/drop
callbacks run through separately compiled functions with their own restoration
obligations. This is a local optimization inspired
by the paper's mainline-cost goal, **not an implementation of Zero Lexa**.

Tests require absent depth/restore relocations in handler-free functions and
retained relocations in handler-owning ones, for default/release codegen.
Behavioral tests cover ancestor-handler visibility across loop exits and a
callee's early return not leaking its handler into its caller. Existing handler,
cancellation and owning-environment regressions remain required. The acceptance
gate is full fmt/test/strict Clippy on Boat; performance claims require a
separate measured cohort, not the paper's benchmark numbers.

## Borrowing: operational semantics before extra permissiveness

[Tree Borrows, PLDI 2025](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
models Rust aliasing behavior, including unsafe interactions. A tree-shaped
loan graph alone does not make Kush an implementation of Tree Borrows. The
paper does not supply Kush with a static borrow checker or automatically
validate its generated loads/stores and foreign boundary.

RES-BORROW-MODEL must define an explicit supported mapping: allocations,
reference identities, reads/writes, reborrows, parent freezing, invalidation
and protected calls. Add shared/mutable sibling, nested reborrow, failed
write/read, and FFI-boundary traces. Classify differences as deliberate static
restrictions versus semantic disagreements. Interior mutability, raw-pointer
escape hatches and new optimizer alias assumptions wait for their own design.
Do not add no-alias metadata merely because references are arranged as a tree.

## Grades: separate usage, ownership and relevance

[A Mixed Linear and Graded Logic: Proofs, Terms, and Models, CSL 2025](https://doi.org/10.4230/LIPIcs.CSL.2025.32)
provides a categorical account of mixed linear and graded structure.
[A Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized,
ICFP 2023](https://doi.org/10.1145/3607862) is a relevant formalized erasure
reference. Neither transfers a theorem directly to native Kush programs.

RES-GRADE-MODEL must map the actual contexts and substitution rules: copyable
must-use observations, owning exact-use transfer, grade-zero initialization
with preserved effects, physical ABI erasure, and linear task cancellation.
Custom finite semiring law checks are not by themselves the full modality or
ordered-usage semantics of either paper. Require explicit weakening/contraction,
substitution and extraction obligations, plus hostile examples at every boundary.
Do not identify `@[1]` on a copyable value with owning linearity, erase an
effectful initializer, or promise backend correctness from a frontend calculus.
Category theory is a model for these distinctions, not a request for a new
monadic wrapper in the source language.

## Inference: a bounded experiment, not a replacement theorem

[When Subtyping Constraints Liberate, POPL 2024](https://doi.org/10.1145/3632890)
([author paper](https://lptk.github.io/files/superf-popl24-preprint.pdf))
introduces SuperF for first-class polymorphism with multi-bounded constraints
and a termination heuristic. This is not a Rust-like lifetime-inference
algorithm or a drop-in replacement for Kush's algebraic runtime types.

RES-INFERENCE-PROTOTYPE should use an isolated positive/negative corpus,
explicit annotations as an escape hatch, deterministic budgets and witness
constraints. Require compatibility with representation-changing coercions,
effects, grade obligations and owner provenance before proposing integration.
The initial lifetime variance and recursive-summary work remains independently
specified; its scopes do not expand because SuperF accepts more type programs.

## Layout: justify erased representation distinctions

[Unboxed data constructors, POPL 2024](https://doi.org/10.1145/3632893)
([author manuscript](https://arxiv.org/abs/2311.07369))
provides a useful direction for constructor representation analysis and bounded
recursive expansion. RES-UNBOX-CERT must enumerate valid payload bit patterns
and prove alternative representations disjoint before removing tags. Test
nested variants, null-like sentinels, NaNs, chars, owning payloads and recursive
expansion refusal. Existing niche encodings, drop glue and foreign layouts are
contracts; the paper is not permission to unbox arbitrary Kush unions.

## Handler design beyond the immediate optimization

RES-EFFECT-CAPABILITY should compare explicit lexical capabilities with Kush's
current lexical direct handlers and dynamically resolved declared operations.
These semantics differ. A lexical-only optimization must not change which
handler a called function observes. Preserve missing-handler effects, owned
frames, task inheritance barriers, one-shot use and cleanup before evaluating
new lookup/stack-switching strategies. The OOPSLA 2025 approach targets
exceptional/rare paths; evaluate effect-heavy cases separately before choosing
a representation. Non-tail/multishot work stays in E-CPS-* and its validation gate.

## Original recommendations: integer proofs and implementation discipline

[The Omega Test, Supercomputing 1991 / CACM 1992](https://www.cs.umd.edu/~pugh/papers/omega.pdf)
is directly relevant to the existing P-CUTS and runtime-index disjointness work.
Keep inexpensive interval/difference/rational reasoning first; add a bounded
integer fallback with independently checked certificates. Current `facts.rs`
verifies rational multiplier certificates, so integer rounding/cutting or
branching needs explicit new certificate rules and tampering tests. An Omega
implementation does not become sound merely by citing an exact algorithm:
checked arithmetic, integer negation, overflow, scope/version identity and
budget exhaustion must remain conservative. Unknown must never mean disjoint.
No new solver is implemented by this turn; P-CUTS remains the existing node,
not a duplicate research checkbox claiming that gap is closed.

[Retrofitting Effect Handlers onto OCaml, PLDI 2021](https://arxiv.org/abs/2104.00250)
informs one-shot frame/stack ownership and cleanup tests for E-CPS-DESIGN.
Its stack-segment implementation is an alternative design input, not the same
thing as Kush's planned explicit state-machine IR. Compare both strategies
against Cranelift stack maps, cancellation, Rust/C calls and continuation
ownership before deciding. Do not infer multishot safety from one-shot results.

[Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism,
ICFP 2013](https://arxiv.org/abs/1306.6032) is a reference for ordered contexts
and annotation discipline. Its completeness applies to its own declarative
calculus, not Kush's region/ownership/grade/effect combination. Use it when
specifying an explicitly bounded polymorphic inference extension, not as an
existing lifetime algorithm. Region-based memory inference likewise concerns
a distinct allocation/type discipline; solver structure alone does not justify
borrow provenance or unrestricted polymorphic recursion in Kush.

[Linear Haskell, POPL 2018](https://arxiv.org/abs/1710.09756) is another input
to RES-GRADE-MODEL: arrow multiplicity and a closure's permitted invocation count
are different concepts. Review linear argument transfer, captured obligations
and higher-order reuse before proposing multiplicity-polymorphic arrows. The
current `once fn` contract should not be replaced on a superficial analogy.

## Category-theoretic effect semantics

[Parametric Effect Monads and Semantics of Effect Systems, POPL 2014](https://doi.org/10.1145/2535838.2535846)
([author publication/abstract](https://group-mmm.org/~s-katsumata/research.html))
is a reference for a semantic account of sequential effect composition and
subeffecting. RES-EFFECT-CAPABILITY must specify the actual algebra of Kush's
row sets, sequential execution, handler discharge and effect inclusion; a
bitset union implementation is not itself a proof of a parametric-effect-monad
model. A model is useful for stating preservation obligations, not a mandate to
rewrite direct-style source programs with explicit monadic wrappers. Borrowing
may also benefit from semantic models, but categorical terminology alone does
not validate a static loan rule or native alias optimization.

## Correcting the fixed-point claim

The side discussion's rule “may origins use a least fixed point, must
requirements use a greatest fixed point” does **not** determine Kush's algorithm.
Our [recursive design](recursive-lifetime-design.md) represents accumulated
requirements as sets that grow by union: both possible origins and required
constraints therefore use monotone **least** fixed points under subset order.
A greatest-fixed-point formulation would need a different domain/order and a
separate derivation. Final signature validation is not automatically a greatest-
fixed-point computation. An unseeded recursive cycle must not invent origins,
preconditions, lifetime equality or nontermination facts to validate itself.

The [variance design](lifetime-variance-design.md) similarly uses direct
occurrence seeds and a finite sign-set lattice. The mathematical tool here is
explicit abstract domains, monotone transfer functions and checked witnesses;
terminology alone adds no new guarantee or accepted program.

## Execution priorities

First land and verify the local handler-free optimization. Continue the already
planned lifetime variance/context work and recursive summaries under their
reviewed contracts. The operational borrow mapping and grade-model audit can
inform their tests without replacing those contracts. Larger inference, handler
and unboxing changes need their own design evidence and measured acceptance
gates; they remain open nodes rather than a claim that all papers are adopted.


## Validation of this first action

The local advanced type/effect suite passed 75 tests. The new codegen test
passed for default/release objects, and two new behavior tests passed against
the reference evaluator and both native modes. The full integrated Boat gate
passed **1,182 tests**, formatting and strict workspace/all-target Clippy.
The sandbox was stopped afterwards. No workload timing or claimed percentage
speedup accompanies this change; generated-call elimination is the measured
codegen property. Other research nodes remain open.


The immediate borrowing subset audit is recorded in the [operational loan
contract](borrow-model-contract.md), with focused baseline regressions in
`lifetime_integration_baseline.rs`. A formal Tree Borrows simulation is still
not claimed. Active implementation work now prioritizes LIFE's variance,
recursive-summary and row/result dependency chains; unrelated research changes
remain open and do not block that chain.

## Research node deliverables

The four remaining research nodes are closed by design documents, each
stating its decisions and adding follow-up implementation nodes to the plan:

- RES-GRADE-MODEL: [grade model](grade-model.md) (two-zone judgement,
  scaling substitution, erasure obligations E1-E6).
- RES-EFFECT-CAPABILITY: [effect capabilities](effect-capabilities.md)
  (second-class lexical capabilities beside unchanged dynamic handlers; row
  algebra obligations).
- RES-INFERENCE-PROTOTYPE: [inference prototype](inference-prototype.md) and
  the isolated `crates/infer-proto` corpus (adopt only local lambda
  annotation inference).
- RES-UNBOX-CERT: [unboxing certificates](unboxing-certificates.md)
  (checked value-set disjointness, expansion stops at indirections).

Follow-up research nodes:

- GRADE-EFFECT-DEMAND: [effect-sensitive demand](grade-effect-demand.md)
  (precise value-flow rule specified; kept conservative because hoisting is
  always enough and the precise rule would reject accepted programs).
- E-ABORT-DESIGN: [abortive handlers](abortive-handlers.md) (return-path
  propagation reusing the `?` cleanup, no native unwinding).

No theorem from the cited papers is claimed for Kush.
