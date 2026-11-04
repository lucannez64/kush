# Design: recursive lifetime summaries

Status: the direct-call, static-method, borrowed-record and required-precondition
fragments are implemented in `crates/kush/src/executable/recursive_lifetimes.rs`.
Indirect/dynamic boundaries remain explicit-contract limits. Source baseline:
`3a58acc` with the method, record-result and `R[f]` extensions in this branch.

## Problem and current boundaries

`Functions::instance` in `executable.rs` caches a concrete function signature
and queues its body. Its current body-origin seed follows a bounded set of
syntactic returns/aliases; it does not solve mutually recursive borrowed-result
contracts. `InstanceKey` already distinguishes runtime types, grades, natural
and effect arguments, with a 256-instance limit. `Signature`/`BorrowSig` carry
parameter/result lifetimes, per-field borrow leaves and closed outlives bounds.
`BorrowSig::canonical` alpha-renames visible labels; ownership's call mapping
instantiates them from actual provenance and validates caller obligations.

`lifetimes.rs` solves finite *outlives edges already supplied*. Its lifetime
SCCs must not be confused with the *call graph SCCs* proposed here. Repeatedly
calling that solver on an unseeded recursive function cannot discover where
its result borrows from. This design adds origin-summary equations, not merely
another pass of transitive closure.

## Initial supported fragment

Infer lifetime contracts only for a finite set of concrete instances whose
runtime parameter/result shapes are already known. Direct calls and statically
resolved methods participate. A function may have multiple parameter/record
leaf lifetimes and multiple result leaves. Existing declared output shape,
mutability, grades, effects, erasure and ownership modes remain fixed.
For newly inferred recursive contracts, a result is tied to named input leaves
or to a fixed anonymous intersection of them. A separate free output-only
lifetime binder needs an existing explicit boundary contract; this first
fragment does not invent its quantification or infer a caller's choice for it.

Indirect calls use their already checked arrow contract as an external summary.
Foreign calls, open dynamic dispatch, task boundaries, closure capture-result
contracts and unresolved generic calls require their existing explicit checked
contracts; do not guess an inferred callee set. If an inferred recursive result
needs an unsupported origin channel, reject with an annotation/boundary message.
An explicit boundary can compose with a supported SCC without itself being
inferred. When a boundary's contract permits several input origins for a result,
retain all of them; do not turn its single printed result lifetime into evidence
for one chosen owner. Lazy dynamic member registration cannot silently change a frozen SCC.
Polymorphic recursion that creates more than the existing finite instance limit
keeps its explicit rejection. This is not higher-rank lifetime inference.

## Summary domain and judgments

Assign stable IDs to each instance and each borrow leaf using parameter index
plus typed field path. Scalar lifetime names alone do not identify owner roots.
For every result leaf `r`, track a **may-origin set** `O[f,r]` of input leaves
from which any normal return can derive. Also track a finite set `R[f]` of
required input-lifetime outlives pairs and provenance-backed derivations for
each fact. Mutable capability and field/split ancestry remain separate data;
a lifetime relation never proves two owners disjoint.

Keep three things separate:

- **Assumptions:** rigid bounds explicitly declared for this function/boundary.
- **Requirements:** preconditions its implementation and calls impose on callers.
- **Guarantees:** possible result origins actually justified by body flow.

An inferred requirement may become an exported precondition for an inferable
function, but must not be inserted into local assumptions to prove itself.
Explicit trait/override/function-value contracts cannot be silently strengthened.
Every use must validate the finalized contract. For each possible result origin,
the instantiated origin must outlive that result's actual use. Unioning possible
origins retains every corresponding owner loan; it does not select the first
origin or assert that their lifetimes are equal.

The domain is a finite product of powersets. Facts only grow under subset order;
join is union. There is no subtraction, heuristic lifetime guessing, or fresh
region allocation on each iteration. Anonymous intersection identities are
allocated once per instance/result slot, not during transfer. Keep one minimal,
deterministically selected derivation per fact to bound witness storage.

## Equations and fixed point

1. Gather reachable concrete instances and call sites without publishing inferred
   signatures as final. Construct a signature-independent finite borrow-flow
   representation with provisional lifetime slots. Normal type/effect/grade
   checking still applies. Unresolved borrow compatibility is an obligation,
   not permission to emit executable IR.
2. Seed direct input borrows, reborrows and field projections from established
   owner provenance. Reject local/temporary escape through the ordinary ownership
   rules. Control-flow alternatives union their origins; CFG loops use the same
   monotone finite flow discipline. Do not treat an unresolved call as a value
   with empty (therefore unrestricted) provenance.
The final validation must preserve ownership's `actual_outlives` judgment,
including its existing distinction between caller-storage lifetimes and local
frame lifetimes. Raw graph reachability is not a replacement for lexical owner
scope checks or a way to promote a frame-local origin into a caller result.

3. For a call `f -> g`, substitute each input origin named in `O[g,r]` through
   that call site's actual argument-leaf mapping; union the resulting roots
   into the corresponding caller result flow. Propagate `R[g]` through lifetime
   substitution into `R[f]`, preserving all actual alternatives, not one chosen
   argument. Compose through helpers and recursive calls identically.
4. Condense the concrete call graph into SCCs and process callees before callers.
   Within an SCC, use a deterministic worklist until no origin/requirement set
   grows. Reschedule callers when a callee fact changes. Declaration/traversal
   order must not affect the result. Discovery of a new concrete instance or
   direct edge invalidates the affected SCC ordering before publication.
5. Validate explicit contracts and caller obligations against the stabilized
   summaries; instantiate anonymous intersections consistently with existing
   call rules. Then recheck/finalize bodies and arrows using frozen signatures.
   Adapters, callable interning and native/evaluator lowering happen only after
   finalization. No executable program may retain provisional metadata.

Borrow-leaf paths are slots in the already bounded signature representation,
not arbitrary recursively expanded heap paths. If recursion would keep extending
a symbolic field path, summarize to the existing conservative root set or reject
that fragment; never grow the summary universe during iteration. Container
contents use the existing finite per-leaf may-provenance abstraction, not one
symbol per runtime element.

Let `P` be the total finite input-leaf count, `Q` result-leaf count and `N` input
lifetime names per instance. Each summary adds at most `P*Q` origin facts plus
`N*N` requirements; multiply over the bounded instance set. The monotone
worklist therefore terminates when the instance/shape universe is fixed.
Implementation must also impose a documented aggregate work/fact budget and
return a checked diagnostic on exhaustion. Never return a partial summary as
success. This bound concerns inference, not termination of user programs.

## Recursive seeds, ambiguity and annotations

A base branch returning input `a` seeds the SCC. Mutually recursive forwarding
then propagates that origin. If another reachable return can use `b`, both
origins must appear. For example, for existing slice syntax:

```kush
fn left<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { a } else { right(a, b, true) }
}
fn right<'a, 'b>(a: &'a [i64], b: &'b [i64], stop: Bool) -> &[i64] ! {panic} {
    if stop { b } else { left(a, b, true) }
}
```

This is a proposed inference test, not a claim of current acceptance. Both
result slots conservatively retain both owners because the design is path
insensitive; scalar arguments such as `true` do not prune a callee's summary.
An explicit result tied to only `a` needs a justified `b: a` requirement or
must be rejected at a rigid contract boundary.

A recursion-only cycle with no independently justified result origin must not
bootstrap the statement “the result can borrow from any input.” Require an
explicit result contract, or reject unsupported inference. Do not infer `Never`
or non-returning behavior from the absence of a seed: termination analysis is
outside this design. An explicitly annotated recursive forwarding function can
be checked parametrically against its contract, with each body independently
validated and no local-origin escape permitted.

There is no unique named lifetime for several incomparable origins. Retain an
anonymous intersection where the existing rules support it; otherwise request
an annotation. Do not collapse distinct universally quantified parameters into
one lifetime because they occur in the same recursive SCC. Declared cyclic
bounds retain the current rejection; inferred mutually forcing equality must
request one explicit shared binder rather than silently merging public binders.

“Principal” means only the least conservative fact solution of these fixed
finite may-flow equations under the specified abstraction. It is not a principal
source type, a most permissive lifetime scheme or a general unification theorem.

## Diagnostics and implementation sequence

Retain source spans for return-origin seeds, call-substitution edges and unmet
requirements. A diagnostic should show the required relation, the recursive
call chain that propagated it, and the input/result leaf path. Cap witness
length and summarize repeated SCC traversals. Preserve the primary error span
and deterministic ordering. Distinguish an unseeded cycle, an unsupported
boundary, a rigid-contract conflict and resource-budget exhaustion.

Implement as separate integrated steps:

1. Provisional summary IDs and explicit discovery/freeze states. Assert no
   backend/arrow cache consumes an unresolved signature.
2. Nonrecursive helper composition with origin and obligation witnesses.
3. Call-graph SCC worklist and stable anonymous result IDs.
4. Final contract validation, body replay and cache invalidation.
5. Diagnostics, budgets, adversarial tests and independent soundness review.

The existing `pending` body queue is not itself an SCC inference scheduler.
Keep this machinery separate from the finite outlives-graph API and reuse that
API only for validating/closing justified finite bounds.

## Required acceptance and hostile tests

- Direct and mutual recursion, helper chains, self recursion with a base origin;
  permute declarations and worklist order and require identical summaries/errors.
- Several normal-return roots, nested record/container result leaves, and input
  permutation on recursive calls. Every reachable source owner remains loaned.
- A local or temporary returned only on a recursive path remains rejected;
  mutable duplicates and capability upgrades remain rejected.
- No-seed cycles cannot manufacture origins, lifetime equality or `Never`; an
  unrelated explicit-result call in the body is not returned evidence.
- Erased proof parameters, including ones before or between borrowed runtime
  parameters, do not shift the selected call argument.
- Acyclic unsupported channels and unmapped summary field paths are rejected
  instead of becoming empty origins; an explicit contract keeps the supported
  acyclic path usable.
- A caller that lacks a newly inferred requirement is rejected even if checked
  before the callee; exact trait and arrow contracts cannot be strengthened.
- Calls through explicit arrows/boundaries retain existing guarantees; unknown
  targets and growing polymorphic recursion fail explicitly when unsupported.

## Implementation status

Source baseline: `a6f0263` (prepared HEAD). The recursive summary chain is
implemented as `crates/kush/src/executable/recursive_lifetimes.rs` and is solved
once in `check_program` before any body is checked. Its finite domain, lattice,
call substitution, local binding/assignment flow, SCC worklist, budget, and
diagnostics are live code, not design scaffolding. A signature, callable arrow,
or ownership judgment therefore observes the frozen summary; provisional
metadata is never published to a backend.

Implemented in this fragment:

- Stable origins are a runtime parameter index plus a source field path. The
  origin set is a power set of those leaves; join is union and facts only grow.
  Call substitution maps a runtime index back through the callee's source
  parameter list, so an erased proof position never shifts the selected
  argument. The same explicit source-position mapping is used by the syntactic
  helper-result seed.
- Direct static calls and statically resolved method calls compose through
  helpers, self recursion, and mutual recursion. A method receiver is the
  implicit source argument at position zero; erased proof positions after it are
  skipped by source position, never by runtime index into the AST argument list.
  Receiver-type dispatch uses the syntactically known local/parameter type (or a
  unique method name), so dynamic dispatch and builtin methods remain
  boundaries. Local `let` aliases, record destructuring, field projections,
  record literals, blocks, branches, and matches carry origins; assignments are
  folded to a local fixed point. Input permutations on recursive calls keep
  every actual alternative.
- Call-graph condensation is separate from the outlives solver. Iteration and
  diagnostics are sorted by declaration name plus binding for deterministic
  results under declaration permutation. The aggregate budgets are checked
  errors instead of partial summaries: 250,000 analysis steps, 16,384 origin
  facts, and exactly 64 local fixed-point passes. Exhausting a pass budget asks
  for an explicit result lifetime and never returns the last partial walk.
- A result summary is now a map from result field path to origin set. A
  borrowed-record result such as `Pair<'a, 'b>` therefore keeps an independent
  leaf for each borrowed field, while a root slice/text/reference result keeps
  the empty path. A whole-record origin contributes to every declared borrowed
  field, and an unmapped result path is a checked diagnostic rather than an
  empty origin set.
- An unsupported result channel is stored in the solved summary, not discarded.
  Indirect calls, dynamic dispatch, loop/performed results, and tasks keep an
  `unknown` fact keyed by result path, so an unsupported owned field does not
  contaminate a borrowed sibling. An elided multi-input declaration is rejected,
  and a caller of an explicit-result boundary still sees the preserved `unknown`
  rather than an empty origin set. A single-input or no-input acyclic
  declaration keeps its existing more specific diagnostic because its result
  lifetime is already determined by the ordinary rule.
- Elided borrowed result shapes are recognized by their written borrow shape,
  not by whether a named lifetime is printed (`&[T]` mentions no lifetime but is
  still borrowed). The public helper-result seed and the summary mapping agree
  on source argument positions.
- An elided multi-source result becomes the existing anonymous intersection
  lifetime with bounds from every contributed input. Unioning origins retains
  every owner loan; a branch join now keeps the shortest provable common view
  lifetime rather than dropping to `None`, which lets explicit recursive
  contracts use their propagated `b: a` precondition.
- A cycle with several independent direct input lifetimes and no base origin is
  rejected with the recursive call chain. The exemption for an explicit-result
  boundary is evidence-based: every returned result path must be the boundary
  call. An unrelated explicit-result call elsewhere in the body does not seed
  the cycle. A single unambiguous elided input keeps the existing parametric
  elision, and an explicit result contract remains parametric forwarding
  validated by ownership, including no-base cycles. Inference never invents
  `Never`, lifetime equality, or a fresh label per iteration.
- Result-derived bounds are exported on the recursive declaration and checked at
  every caller. An independent required-precondition summary `R[f]` is also
  computed by the same least fixed point: explicit callee outlives bounds are
  substituted through actual argument leaves, and an argument written into
  another argument's `Vec`/`Box` container contributes the element-lifetime
  requirement. Callers missing a newly inferred requirement are rejected even
  when checked before the callee. A frozen function value carries both the
  result-derived and `R[f]` bounds, so an unconstrained arrow cannot silently
  erase them.
- Newly inferred record-result bounds and `R[f]` requirements are published only
  for a declaration that is in, or reachable from, a recursive call-graph SCC.
  An acyclic declaration that no recursive path uses keeps its existing rigid
  contract, and explicit declared outlives bounds, trait/impl methods and arrows
  are never strengthened by this pass.
- Every solved origin must map to a declared input lifetime. A missing field
  path is rejected with a checked diagnostic that asks for an explicit result
  lifetime; it is never silently omitted from the summary.
- Local/temporary escape, mutable capability upgrades, grade/effect checks, and
  the existing 256-instance cap are unchanged. Callers are revalidated by the
  ordinary ownership pass after bodies are checked.

Remaining limits, deliberately not claimed as complete:

- Direct static calls and statically resolved methods participate. Indirect
  calls, dynamic dispatch, builtin method results, effect-operation results,
  loop results, and tasks remain unsupported boundaries. Their `unknown` fact is
  preserved in the solved summary; an elided multi-input result is rejected
  with an explicit-contract request (or must route through a direct checked
  function), and an acyclic caller of an explicit boundary cannot read the
  channel as empty provenance.
- Per-field result summaries cover nominal borrowed records and their nested
  borrowed fields. Owned reference containers (`Box<&T>`, `Vec<&T>`) keep their
  existing declared-lifetime inference rather than becoming per-field records.
- `R[f]` propagates explicit callee bounds and the `Vec.push`/`Box.set`
  container-write relation. A container write reached only through a builtin
  method on a non-parameter local, or a requirement that names a field path the
  caller does not expose, stays at the existing explicit-contract/ownership
  diagnostic. Requirement publication is limited to recursive/reachable
  declarations as described above; an acyclic helper keeps its rigid contract.
- Method dispatch in the summary uses syntactic receiver type names, not full
  type inference. An ambiguous receiver type that does not resolve to exactly
  one concrete impl method remains an `unknown` boundary.
- Summaries are solved per declaration. Lifetime labels do not vary with type
  substitution in the supported fragment, so concrete instances map the same
  stable parameter-leaf IDs onto their own frozen labels. Instance-specific
  discovery of new borrowed field shapes is outside this fragment.
- Polymorphic recursion past the existing instance limit keeps its explicit
  rejection. Variance and subtype interaction is a separate track; this module
  does not change `runtime_types` subtype or variance rules. A branch join of
  two record-result arms may carry compiler-internal call result labels; those
  are opaque to the invariant-label identity check and are validated by
  ownership provenance instead.

Gate used for this stage:

```text
mbx test -p kush --test recursive_lifetimes -j2
mbx test -p kush --test lifetimes --test borrowed_records \
  --test borrowing_references --test borrowing_extensions --test task_borrows -j2
mbx test -p kush --test borrowed_methods --test slices --test subtyping \
  --test lifetime_variance --test traits --test review_regressions \
  --test advanced_types_effects -j2
```

`LT-RECURSIVE` remains open for the indirect/dynamic boundary extensions and a
fully general `R[f]` beyond the container-write/explicit-bound fragment. The
direct-call, static-method, borrowed-record and required-precondition chain above
is implemented and tested; `LIFE` keeps only the broader inference items that
are outside this module.

- Stable anonymous IDs, signature/cache replay, deep SCCs, exhaustion diagnostics
  and deterministic witnesses. No provisional metadata survives finalization.
- Reference/native agreement and balanced cleanup for accepted programs,
  cancellation/early-exit regressions where explicit task contracts are composed.

The [variance design](lifetime-variance-design.md) is not a hard implementation prerequisite for this first fragment:
existing invariant/substitution rules suffice. More permissive nested container
or arrow coercions must wait for LT-VARIANCE and use its lifetime-aware judgment,
not erased-shape compatibility.


Research clarification: accumulating may-origins and required preconditions
both grow by union in this design, so both use a least fixed point. A general
may/must slogan or categorical interpretation does not select a greatest fixed
point for these equations. See [research actions](research-actions.md).

## Independent review follow-up

An independent soundness review of the method, per-field and `R[f]` extension
found no accepted program that outlives an owner, aliases mutably, or reads
freed memory. It found four defects, fixed with regressions in
`tests/recursive_lifetimes.rs`:

- **Non-convergent unsupported relays.** A recursive call relaying a callee's
  unsupported channel wrapped its witness text again on every pass, so the
  fixed point never converged and source order changed the diagnostic. A
  relayed fact is now wrapped at most once and never preferred over a root
  cause (`Unsupported::relayed`).
- **Generic receivers.** A receiver typed by a generic binder or alias
  (`id(b).pick(..)`) matched an unrelated impl of the same name. Receiver
  names now count only when they resolve to a concrete data declaration;
  anything else is the explicit-contract boundary.
- **Whole-record identity helpers.** A callee returning a whole parameter
  merged every argument field owner into every result field, producing false
  cross-field bounds. The argument's per-field leaves now map to the same
  result fields.
- **Inherent methods and `R[f]`.** Inferred requirements are now exported for
  inherent methods. Trait impl, generic impl and default methods keep their
  exact contracts.

The branch-label check also now excuses only the slot whose own label is
compiler-internal, instead of every slot when any label was internal.
