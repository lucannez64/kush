# Design: recursive lifetime summaries

Status: design only for LT-RECURSIVE-DESIGN. No new programs are accepted by
this document. LT-RECURSIVE remains an implementation task. Source baseline:
`edb9e6e` (finite graph/SCC solver and diagnostics integrated).

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
- No-seed cycles cannot manufacture origins, lifetime equality or `Never`.
- A caller that lacks a newly inferred requirement is rejected even if checked
  before the callee; exact trait and arrow contracts cannot be strengthened.
- Calls through explicit arrows/boundaries retain existing guarantees; unknown
  targets and growing polymorphic recursion fail explicitly when unsupported.
- Stable anonymous IDs, signature/cache replay, deep SCCs, exhaustion diagnostics
  and deterministic witnesses. No provisional metadata survives finalization.
- Reference/native agreement and balanced cleanup for accepted programs,
  cancellation/early-exit regressions where explicit task contracts are composed.

The [variance design](lifetime-variance-design.md) is not a hard implementation prerequisite for this first fragment:
existing invariant/substitution rules suffice. More permissive nested container
or arrow coercions must wait for LT-VARIANCE and use its lifetime-aware judgment,
not erased-shape compatibility.
