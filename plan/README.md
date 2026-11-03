# Reading and executing the Kush plan

`plan.json` is a dependency graph, not a schedule or a reconstruction of commit
history. The viewer's numbered dependency order is one valid topological sort:
it prefers completed nodes, then shallow dependency depth, then JSON file order.
Neither depth nor file order measures importance, risk, or user value. Independent
nodes can swap positions without changing the graph's meaning. “Ready” means
only that recorded prerequisites are done; it does not mean “do this next.”

## Recommended execution sequence

This is a proposed practical sequence for the remaining compiler backlog,
not additional hard dependency edges. User-requested project work can interrupt
it. Finish and validate a coherent feature rather than starting every design
node that happens to be shallow.

1. **Establish the working gate:** `OPS-STEP-GATE`; remove only verified finished
   worktrees (`OPS-WORKTREES`). Cleanup can happen independently and must preserve
   unmerged work. Use focused tests during implementation and the full Boat gate
   for integration. Soundness changes need a review before their feature closes.
2. **Make lifetime behavior explicit:** `LT-GRAPH → LT-SOLVER → LT-DIAG`, preserving
   today's accepted/rejected programs first. This supplies a stable basis for
   subsequent lifetime extensions; recursive inference and variance are separate
   expansions, not prerequisites for every existing reference operation.
3. **Finish concrete borrowing features vertically:** slice-element places
   (`R-SLICE-PLACE-*`), borrowed-record mutation (`R-BREC-*`), then runtime-index
   disjointness (`R-IDX-*`). Each includes checker, backend, hostile tests and
   review. `A-PLACE-VIEW` follows working slice places. Handle TaskExit provenance
   as its own reviewed feature, not a side effect of a lifetime refactor.
4. **Improve everyday trait-object use:** projected mutable/consuming receivers
   and explicit early associated bindings. Temporary/owned receiver views require
   a settled owner-lifetime contract. Multi-trait objects are a separate project;
   they need not block shipping the smaller improvements.
5. **Expand inference and proofs:** indexed unions and bounded partition
   inference, then closure lifetime/live-capture proof invalidation. Integer
   refutation (`P-CUTS`) is an independent solver project, not something grades
   completion alone makes implementation-ready.
6. **Extend storage:** runtime-length array design/type/storage/views and richer
   patterns. These tracks can run independently where their actual prerequisites
   are satisfied; they should not delay earlier correctness improvements.
7. **Generalize continuations:** the `E-CPS-*` state-machine project, followed by
   non-tail callees and multishot. Set exit/cleanup semantics in the design and
   validate them at every stage; don't interpret the late `E-CONTROL` node as
   permission to defer return/cancellation cleanup safety until the end.

`&mut str` starts with a language/API decision, not an assumed obligation to add
arbitrary byte mutation. Recursive lifetime inference, variance, multi-trait
objects and multishot remain separate larger milestones. Their exact order is a
priority decision, not something a topological sort can determine.

## Graph corrections and audit limits

- Added `R-SLICE-PLACE-TESTS` and made reference-area review depend on it.
- `A-PLACE-VIEW` now depends on working slice-place backends, rather than loan
  rules alone: this is an end-to-end feature, not just its checker design.
- Final completion now includes `OPS-STEP-GATE` and this plan clarification.
- Completed core nodes summarize capabilities; their empty dependency lists do
  not claim those systems were historically independent or fully general.
- Area-closing review nodes are final integration reviews. They do not replace
  per-feature safety reviews and tests.

This is a targeted consistency pass, not certification of every future design
edge. In particular, design discussion need not wait for all implementation
prerequisites: `R-TASKEXIT-DESIGN → LT-SOLVER` currently records a sequencing
choice as if it were a hard prerequisite. Reassess it when starting that feature;
we have not removed it on speculation. Likewise consuming projected dispatch
needs partial-move ownership rules; its current edge from mutable dispatch is
not a sufficient specification of those rules.

Use `scripts/plan.py` to update status/dependencies and record new evidence.
When implementing a node, revisit its prerequisites against the current source;
add missing design/test work instead of treating “ready” as proof of feasibility.
