# Borrowed structural rows and results: integration contract

This design covers LT-ROWS-DESIGN, the interface between LT-VARIANCE,
LT-ROWVARS and LT-STRUCT-RESULT. The design stage removed no rejection;
LT-STRUCT-RESULT now implements the borrowed-result gate described here. It is
independent of unfinished effect, proof, layout and general polymorphism work.

## Observed implementation gap

This section records the pre-LT-ROWVARS gap; LT-ROWVARS closed it and
LT-STRUCT-RESULT builds the result gate on the repaired metadata.

`Types::structural` in `runtime_types.rs` interns rows using only sorted
`(field name, Type)` pairs and initializes every `field_lifetimes` entry to
`None`. Bare slice/reference types do not include their outer lifetime in
`Type`, so lowering an explicit field such as `view: &'a [i64]` loses the
annotation even when the AST named it. The result checker in
`Functions::instance` correctly rejects a returned borrowed leaf with no label.

`Types::lower` expands a structural row tail through `structural_row`, which
also exposes only names and types. The impl-header and ordinary call inference
paths in `executable.rs` construct residual rows with `types.structural`; those
paths can likewise lose labels even after direct annotation lowering is fixed.
Structural literals have a further challenge: their actual provenance is known
from expression origins, not just their expected type.

These are metadata losses, not reasons to weaken the final owner-origin check.
The work is complete only when labels and actual origins survive every path,
not when a single return example starts type-checking.

## Canonical row representation

A checked field descriptor must carry name, runtime type and the outer borrow
label where that label is not represented inside the type. Nested field and
container metadata must remain reachable through the existing borrow-leaf walk.
Sort the complete descriptors together by field name. Never sort field types
separately from labels or origins. Duplicate field names remain an error.

Intern checker metadata with the full descriptors, including exact lifetime
identities and mutability carried by types. Physical layouts may coincide,
but rows differing in `'a` versus `'b` must not collapse to one checker type.
Keep runtime representation and nominal/structural identity rules unchanged.
Anonymous/internal labels are rigid; interning must not invent equality.

An unannotated literal cannot acquire a trustworthy label merely by copying
its expected type's label. The expected label is an obligation. Actual roots
and borrow capabilities still come from the field expression. An existing
exact no-op or checked elision may recover a label from provenance; an unknown
must remain unresolved/rejected if that evidence is absent.

## Row-tail inference and substitution

Provide a metadata-preserving row view alongside the existing erased/name-type
view, and use it for:

- direct structural annotation lowering and row-tail expansion;
- residual-row inference at ordinary calls and impl-header matching;
- repeated occurrences of the same row variable in several parameters;
- construction of the resulting specialized parameter/result shape;
- callable parameter/result borrow-leaf metadata and exact coercions.

A row specialization needs its lifetime/binder environment, not just a
runtime layout key. When a generic row is used at several call sites, labels
from the first call cannot leak into later specializations. Canonicalized
callable contracts require occurrence-specific maps as specified by
[lifetime variance](lifetime-variance-design.md). Rigid labelled fields may
only relate through the checked lifetime witness, never erased shape equality.

A repeated row variable must match a compatible complete residual row under
those rules. Do not silently union origins or choose a common lifetime to make
an ambiguous type argument infer. Existing layout and instance budgets remain
in effect. Residual field paths must be rebased by the exact source-to-target
field mapping, not kept as source field indices after erasure/reordering.

## Result acceptance gate

A borrowed structural result may be accepted only after all its leaves have
resolved signature labels or a supported existing checked inferred identity.
For each possible leaf origin, validate:

1. its root is caller-owned storage admitted by the signature, not a local,
   hidden temporary, dropped container, dead scope or child-task frame;
2. the actual origin outlives the required result lifetime under the current
   lifetime and lexical rules;
3. an exclusive result has an exclusive input capability with preserved
   ancestry, not an upgrade from shared storage or a duplicated mutable leaf;
4. every alternative from branches, loops and helper/call results is retained,
   and every corresponding caller owner remains loaned until result last use.

Use the same `borrow_leaves` paths for signature metadata, call mapping,
construction, destructuring and result validation. A structural type's claimed
field annotation is never itself evidence of its value's origin.

Retained borrowed fields stay exact under structural conversion in the initial
fragment, as the variance design specifies. Existing checked width coercions
keep their path/drop semantics. Forgetting a shared source copy does not
release another copy's loan; exclusive fields may not be copied. Direct
structural owner-reference fields remain rejected unless their place/reference
metadata is separately admitted and tested. Do not conflate adding slice
result labels with generalizing all reference storage.

## Staging and validation

First add metadata-preserving interning and row views without removing the
result gate. Then carry descriptors through residual-row inference and callable
construction. Only after those paths and variance witnesses are integrated
should LT-STRUCT-RESULT enable supported borrowed result forms. Finalize with
independent review plus the integrated Boat gate before LT-REVIEW/LIFE close.

## Implementation status

LT-ROWVARS stages 1-2 are implemented (2026-11-04) and LT-STRUCT-RESULT
implements the borrowed structural result gate (2026-11-04).

- `runtime_types::RowField` is the canonical field descriptor: name, lowered
  runtime type, and the outer borrow label erased from a direct view. The
  structural interning cache is keyed by the complete name-sorted descriptors,
  so rows that differ only in `'a` versus `'b` are distinct checker types while
  their runtime layout and canonical field order are unchanged. Direct
  structural annotations lower their label through the current lifetime
  substitution instead of discarding it.
- `Types::structural_row_fields` (structural layouts) and
  `Types::record_row_fields` (any instantiated record) expose the metadata-
  preserving view. `Types::lower` row-tail expansion, ordinary call residual
  inference, repeated-row-variable checks, and impl-header matching in
  `executable.rs` use that view. `Types::structural_row` remains the erased
  `(name, type)` convenience view for layout-only consumers.
- A row specialization is still a concrete structural `Type`, now including
  labels, so `InstanceKey` and the impl-instantiation cache separate call sites
  with different labels. No canonical-label map is attached to the interned
  row type; each specialization constructs its own parameter/result shapes from
  the resolved substitution. Residual fields are sorted by their canonical
  target names and coercions map them by source field name, not by retained
  source indices.
- Call occurrences instantiate declared callee lifetimes from structural field
  labels before argument coercion. Repeated invariant occurrences must agree;
  separate calls resolve independent maps, while caller labels remain rigid.
- Unlabelled structural annotations and casts retain known source field labels,
  including nested retained rows, so an intermediate annotation cannot erase an
  invariant obligation. Local bindings keep that refined checked row.
- Structural conversion keeps retained borrowed leaves invariant: a concrete
  source label must equal the target label. An unlabelled literal or an
  opaque/fresh inferred label may acquire the target annotation only through
  the ordinary checked coercion, which retains the value's actual origins.
- Borrowed structural **results** are accepted through the same
  `borrow_leaves` paths as nominal borrowed records. The blanket
  `contains_borrowed_structural` rejection is gone. `Functions::instance`
  requires every result leaf to name a signature label that a parameter carries
  (relaxing the declared-name set only for rigid `..r` specialization labels
  and elided input identities), and the ownership pass then validates each
  actual origin: `check_return_record` requires a caller-owned parameter root
  carrying the declared field label, matching mutability with preserved
  ancestry, all branch/loop/call alternatives merged into the same leaf, and
  the caller's owners loaned until the result's last use.
- A field annotation is an obligation, never origin evidence. For lifetime
  obligations, a structural field's erased outer borrow is covariant like any
  other shared/exclusive view (a longer source satisfies a shorter declared
  result label), while retained **named** borrowed labels stay exact under an
  actual structural conversion. An unlabelled or opaque source leaf may acquire
  the target annotation only through the ordinary checked coercion, which keeps
  the value's actual origins; this rule now applies through nested structural
  rows as well. Nested nominal invariance is still composed through the
  declaration variance table.
- Supported elision: an unlabelled borrowed field in a structural result is
  resolved from the function's single distinct input borrow lifetime, mirroring
  ordinary slice-result elision and including one elided input's fresh checked
  identity. Zero or several distinct input lifetimes is an explicit rejection.
  An arrow type has no body, so its structural fields must name an arrow-bound
  lifetime.
- An elided multi-input root result may follow a projected field of a helper's
  structural result. The recursive summary stores one leaf per result field, so
  `wrap(a).view` contributes only the projected field's origin and leaves an
  unrelated argument's owner free to be mutated or dropped. Direct static calls
  and statically resolved methods compose; indirect calls, dynamic dispatch,
  effects, loops and tasks keep explicit contracts. A recursive edge unions
  every possible source that can reach the result through that edge.
- Call-site instantiation of callee lifetime binders descends through nested
  structural fields. A nested structural argument's unlabelled inner leaves may
  acquire the callee's labels through the checked conversion, and the ownership
  pass still validates every actual origin. Two named inner labels bound to one
  callee lifetime remain an invariant-identity error.

Coverage is in `crates/kush/tests/lifetime_rowvars.rs` and
`crates/kush/tests/lifetime_struct_results.rs`: direct annotation labels,
residual borrowed reads, distinct call-site labels, matching repeated rows,
impl-row identity results, owner mutation/drop while a residual loan is live,
reordered nonzero source indices, label invariance through unlabelled
intermediates, alpha-renamed call binders, repeated-binder conflicts, projected
structural helper results (including recursive per-field summaries), nested row
arguments with distinct caller labels, and the full result matrix below.
Positive cases are checked by the reference evaluator and the native backend
(default and release codegen) with balanced allocation statistics.

Deliberate limits left for later nodes:

- Structural **literals** remain unlabelled in their own checked type: an
  unannotated literal does not copy its expected type's label, because its
  field provenance has no declared identity. An explicit structural annotation
  or a callee row conversion may supply the label through the checked
  conversion, which retains the field's actual origins.
- An elided borrowed field in a structural **parameter** has no signature
  identity. A `..r` result field elided the same way is therefore an explicit
  rejection rather than an invented equality; annotate the parameter field.
- A borrowed structural row behind an owned container needs an explicit field
  label in the result signature; result elision only descends through
  structural fields, not containers.
- Direct structural owner-reference fields (`owner: &'a T`) stay an explicit
  rejection at row interning; only slice/text views and borrowed records are
  admitted.
- The row fragment remains finite and first-order: no row unification with
  outlives-related but distinct labels, no general binder inference, and no new
  width/drop behavior for borrowed fields.

The test matrix must include:

- A named slice parameter returned in a labelled structural field; a nominal
  borrowed input narrowed/reordered into a structural result; nested structural
  fields with distinct input lifetimes; mixed owning metadata cleanup.
- A row variable preserving extra borrowed fields through identity/projector
  helpers, with several call sites using different owners and label identities.
  Repeated rows and callable arguments/results must not mix binder environments.
- Owner mutation/drop after a returned row, block-local and temporary escapes,
  local storage hidden behind a field annotation, shared-to-exclusive upgrades,
  duplicate mutable fields and exclusive return from a shared source.
- Width conversion and field reordering retaining only the correct roots,
  while any surviving source copy keeps its own loans. Include nonzero source
  indices and nested container leaves to catch positional provenance bugs.
- Branch/loop-selected origins, direct/indirect helper composition and actual
  signature substitution. Test supported unlabelled elision and explicit
  rejection when the needed lifetime relation cannot be recovered.
- Default/release native/reference agreement and balanced owned metadata cleanup
  for positive cases, plus existing borrowing safety and row inference regressions.

No new higher-rank, open-world, effect-handler or arbitrary type-argument
inference is required for this finite metadata contract. Unsupported general
forms retain explicit diagnostics rather than being silently accepted.
