# Finite lifetime graph, solver and diagnostics

The compiler's declared and body-inferred outlives relations now share a
standalone implementation in `crates/kush/src/lifetimes.rs`. This completes
plan steps LT-GRAPH, LT-SOLVER and LT-DIAG for the existing finite constraint
language; it does not complete the broader lifetime-inference area.

An edge `a -> b` means that `a` outlives `b`. Nodes retain their exact names,
including compiler-generated anonymous labels. Iterative Kosaraju decomposition
finds strongly connected components without recursive compiler-stack growth.
The condensation graph is acyclic; reachability through it gives the least
transitive relation containing the supplied edges. No new assumption is added
to satisfy a caller. Queries retain implicit reflexivity, and exported closure
sets preserve the old convention: explicit self edges and self edges justified
by cycles are retained, isolated reflexive pairs are not materialized.

Declared bounds keep their existing front-end rules: undeclared names and
duplicates are rejected, a self bound is accepted, and a nontrivial declared
cycle remains rejected with the same main diagnostic. Internally decomposing
cycles is not a language change that permits mutually bounded declarations.
Inferred constraints use the same solver; ownership still separately checks
the actual owner roots, mutability, escape, and every returned origin.

Diagnostics now attach a deterministic cycle witness from declaration edges.
A failed call constraint attaches either an explanation that no outgoing bound
is established or a known outlives chain and the required unreachable endpoint.
This is not a proof of what annotation a user should add: the caller must
justify the bound. Call diagnostics currently receive an already-closed bound
set, so a displayed edge may summarize a transitive chain; they do not preserve
source spans for every original inferred constraint. Existing primary error
messages and source spans remain unchanged.

## Checks and review scope

The standalone tests compare every directed four-node graph without self edges
(4,096 graphs) against an independent Warshall closure. Separate cases cover SCC
identity, anonymous names, deterministic path witnesses, missing constraints,
and empty graphs. Compiler integration tests check cycle witnesses and missing
call-bound notes; the existing lifetime/borrowing suites remain the acceptance
and rejection regressions. Integration uses the full Boat gate.

The source review checks that both former closure loops route to the new solver,
that SCC closure introduces exactly reachable pairs, that declared-cycle rejection
still occurs before a signature is accepted, and that notes only describe a
failure rather than changing the successful ownership path. This is a limited
in-session review and exhaustive small-graph testing, not an independent review
or a soundness proof.

Recursive inference across function SCCs, variance rules, lifetimes in row
variables, borrowed structural results and principal unification remain separate
plan nodes. This solver solves supplied finite outlives edges; it does not claim
to infer those missing contracts. Reachability output can still be quadratic in
the number of lifetime names because callers currently consume a materialized
closure set.

Final validation: full Boat gate passed **1,179 tests**, formatting and strict
workspace/all-target Clippy. Standalone solver tests and Clippy also passed
locally. No recursive inference or variance node is closed by this result.
