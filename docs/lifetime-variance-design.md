# Design: lifetime variance

Status: design only for LT-VARIANCE-DESIGN; LT-VARIANCE remains unimplemented.
Reviewed against `edb9e6e` and the current `runtime_types.rs`, `ownership.rs`,
`executable.rs` and `lifetimes.rs`. This document incorporates and corrects the
initial delegated proposal (commit `6601d5b`). Its decisions below supersede
that proposal's open questions. No new compiler acceptance is claimed.

## Scope and current integration points

This milestone changes compatibility of **lifetime positions**, not general
runtime type-argument subtyping. It does not make `Vec<i64>` compatible with
`Vec<i64 | Bool>`, repack elements, add higher-rank syntax, or change layouts.

Current `Types::atom_subtype` (`runtime_types.rs`) erases annotation labels,
compares reference/container pointees in both directions, and compares nominal
records by erased shape. `structural_subtype` requires exact retained borrowed
field types. `function_subtype` checks parameter contravariance, result
covariance, effects, grades and `BorrowSig::usable_as`. Ownership independently
maps actual roots/labels at calls, validates outlives bounds, retains returned
loans, and checks mutable writes. These are complementary checks; erased type
compatibility alone is not evidence of lifetime compatibility. This observation
is an integration requirement, not a claim of a reproduced current soundness bug.

Labels are carried in several places: signature parameter/result metadata,
record field labels and lifetime arguments, `Type::Annotated` container
metadata, canonical `BorrowSig` leaves, and actual ownership loans. Bare
`Type::Ref`/`Slice` values do not contain their own region identity. Therefore
`lifetime_subtype(actual: Type, expected: Type)` is **not a sufficient API**.

Use checked type views containing the runtime `Type`, its occurrence-specific
label environment/binder classification, and leaf-path correspondence. A
proposed judgment is `Delta |- A_view <=life B_view => Witness`; it requires
existing erased-shape compatibility and additionally proves every lifetime
obligation. For borrow-free types it preserves existing behavior. For borrowed
values, missing metadata is an unresolved obligation or checked rejection,
never permission to fall back to erased compatibility.

## Variance algebra and finite inference

Use four elements: unused `*`, covariant `+`, contravariant `-`, invariant `=`.
Represent them as sign sets: empty, `{+}`, `{-}`, `{+,-}` respectively.
Join is set union; `*` is bottom, `=` is top, and `+ join - = =`.
Composition takes every pair of signs and multiplies their directions:
`+*+ = +`, `+*- = -`, `-*+ = -`, `-*- = +` (here `*` between operands means
composition, not the unused element). In unambiguous functional notation:

- `compose(unused, v) = compose(v, unused) = unused`.
- `compose(invariant, v) = compose(v, invariant) = invariant` **only when
  `v != unused`**.
- Composition is associative and distributes over join on both sides.

This sign-set definition resolves the unused/invariant corner case explicitly;
“invariance absorbs everything” would be wrong when there is no occurrence.
Standalone implementation tests must enumerate all four-element combinations.

For every declaration and lifetime parameter, collect a **constant seed** from
its direct occurrences and edges to the parameters of nested declarations.
Solve equations of the form:

```
variance[d,p] = seed[d,p]
             join UNION(compose(position[e], variance[target[e]]))
```

Direct occurrences are seeds, not self-edges whose contribution depends on an
initially unused estimate. Start all estimates at unused and join seeds, then
process declaration SCCs callee-first with a deterministic worklist. A purely
recursive occurrence with no seed stays unused in this abstraction; it does
not spontaneously become covariant. For example `List<T> { next: Box<List<T>> }`
has no independently observed `T`; adding a `value: T` field supplies a positive
seed. Actual admissibility of a source declaration remains a separate checker
rule, including existing unused-lifetime rejection on records.

The lattice has at most two strict ascents per parameter, so each source node
can trigger at most two change notifications per outgoing dependency after
initialization. This bounds worklist updates by a constant times graph size,
not the cost of lowering or repeatedly walking syntax. Unknown/opaque occurrences
supply invariant seeds, never guessed covariance. Exhaustion or inability to
construct the finite occurrence graph is a diagnostic, not a successful partial
table. Cache by declaration and parameter slot, not by call site.

The variance fixed point is separate from the outlives reachability solver and
from call-graph origin inference. Initially keep its SCC traversal local and
well tested; extracting a shared SCC utility is optional refactoring, not a
prerequisite or permission to reuse the wrong transfer semantics.

## Constructor rules

The following table describes positions **inside already shape-compatible
types**. A positive pointee position propagates variance of lifetime labels
nested there; it does not enable general pointee/type representation changes.

| Constructor | Own borrow lifetime | Nested lifetime positions |
| --- | --- | --- |
| shared `&T`, shared slice | covariant | covariant |
| exclusive `&mut T`, exclusive slice | covariant | invariant pointee/element |
| `&str` | covariant | none; no new `&mut str` support |
| owned `Box<T>`, `Vec<T>` | none | covariant where borrowed contents are currently supported |
| owned tuples/inline arrays/DynArray | none | field/element covariance only for currently admitted borrowed forms |
| nominal record | computed | join of field occurrences composed through their constructors |
| callable | binder-aware | parameters contravariant, result covariant |
| transparent alias | expanded | composition through the expansion |
| structural row | field-aware | retained borrowed leaves stay exact initially |
| optional-reference enum | explicit mapping required | invariant initially |
| `TaskExit<T>` | existing boundary contract | no new payload variance initially |
| task handle, capture-result environment, dyn object, foreign handle, opaque/custom allocator storage | existing checked contract | exact/conservative; no new borrowed payload capability |

`Box`/`Vec` of borrowed records already exist: their per-field element loans
must be included. Arena/custom-allocator/array forms that reject a particular
borrowed payload today continue to reject it. A table entry never overrides a
payload-admissibility check. More general enum payload support is also separate.

Records are not automatically covariant: a lifetime nested in a writable
pointee is invariant. A lifetime in `&'a mut T`'s outer borrow can shorten while
lifetimes inside `T` stay invariant. An owned `Vec<&'long T>` can move to a
shorter compatible lifetime; `&mut Vec<&'long T>` cannot change the vector's
element lifetime because a caller could then insert a short-lived reference
into storage still promised to be long-lived.

Unknown or unused type parameters do not acquire new runtime type covariance.
For lifetime-only metadata, unused is accepted only when no occurrence has
been proved; absence caused by a failed type walk is unknown, not unused.

## Witnesses, binders and provenance

Record a finite relation keyed by **source/target label pairs and leaf paths**,
with joined polarity for each pair. One source label may relate to multiple
target labels; all obligations must hold. At positive positions require source
outlives target, at negative positions require target outlives source, and at
invariant positions require identical binder identity after valid substitution.
Do not accept a merely one-way outlives relation in an invariant position.

Apply contravariance exactly once: either carry signed positions over source/
target views, or swap operands and normalize witnesses back to root orientation.
Do not swap operands and then flip the same obligation a second time. Mutable
capability, owner roots, split identity and source-to-target field remapping
remain independent required evidence; a region inequality proves no disjointness.

`BorrowSig::canonical_with_leaves` interns alpha-equivalent contracts using
canonical labels. **Do not attach one canonical-to-source label map to an
interned function-type ID**: different source occurrences can share that ID.
Keep the map on a checked callable occurrence/instantiation (including source
span and enclosing binder environment), outside `FunctionKey`. Nested callable
occurrences need their own environments. Preserve bound-versus-free binder
classification before canonicalization; free enclosing lifetimes are rigid,
and only bound names may be alpha-renamed. Where this distinction is absent,
reject the new conversion rather than guessing it from printed names.

Parameter/result type checks and `BorrowSig::usable_as` must consume the same
occurrence environment and pair relation. Preserve the current positional
contract-instantiation rule, including supported many-source-to-one-target
mappings whose obligations all hold. Do not add an unrelated “same number of
printed names” restriction or pretend such specialization is alpha-renaming.
No new general higher-rank subtyping or binder inference is added. Tests should
use current arrow syntax; mathematical binder examples are not proposed grammar.

Unlabelled (`None`) leaves are not wildcard regions. First recover their
existing checked occurrence/provenance information where available. A relation
not recoverable from that metadata cannot be invented, erased, or generalized.
This preserves ordinary supported elision without treating unknown as `'static`.
Internal/anonymous identities remain rigid; their established outlives edges and
ownership's lexical `actual_outlives` rules may be used, but variance creates
no new equality, lifetime, owner, or bound. Existing anonymous-intersection
results remain supported under their current rules; variance adds no general
principal meet/join or new arrow result inference.

## Ownership and mutation integration

A lifetime witness is necessary, not sufficient. Every coercion must retain
all possible source owners for each surviving target leaf. Preserve container
element provenance and structural source-to-target path remapping even when
runtime representation is unchanged. Moving an owned container consumes its
source; shortening a label never releases a live target loan early.

Exclusive lifetime shortening as a move consumes the original capability.
Reborrow is a separate operation with parent/child loan ancestry and a parent
freeze. Existing `&mut -> &` conversion remains an explicit checked downgrade,
not arbitrary leaf-mutability variance. The ordinary witness otherwise preserves
leaf mutability and must not create or duplicate an exclusive capability.

Mutable container/record writes are checked against the **declared destination
label**, not a temporarily shortened read label. Assignment must retain new
origins and release old ones only under existing sound replacement rules.

Do not introduce new automatic borrowed-field dropping as part of this node.
Existing checked structural width coercions retain their current path/drop
rules, including correct preservation of loans held by a surviving source copy.
New unsupported cases require explicit destructuring. Forgetting a shared view
is safe in principle, but forgetting one copy does not end another copy's loan.
Never widen this into permission to copy an exclusive field or discard a linear
obligation. Retained borrowed structural leaves remain exact until row-specific
work has a separately reviewed provenance contract.

Capture-result contracts stay exact. Optional-reference enums stay invariant
until their payload-to-label mapping is explicit and tested. `TaskExit` keeps
its existing scoped call/join provenance rules without new payload variance.
These choices settle scope, rather than leaving implementation to choose a
more permissive table implicitly.

## Compiler integration and acceptance gate

1. Add the lifetime variance lattice, direct-occurrence seeds and finite
   declaration dependency graph. Unit-test the algebra and fixed point first.
2. Add checked type views and occurrence-specific binder/label environments.
   Preserve callable interning; prohibit use of a missing environment as proof.
3. Add the lifetime-aware witness judgment as a refinement of erased shape,
   using current outlives/lexical evidence. Cache only with the full contextual
   key, or do not cache contextual proofs. A shape-only type ID is insufficient.
4. Route argument, return, let/assignment, record/container construction and
   callable conversions through the judgment. Integrate owner/path witnesses;
   keep unsupported structural/enum/dyn cases conservative. Audit every shape-
   subtype call site that can handle a borrow; no fallback is permitted.
5. Reconcile callable contracts with the same witness and keep grade/effect/
   erasure/linearity rules unchanged. Add path-oriented diagnostics: required
   direction, invariant constructor, and missing bound. Polarity metadata stays
   internal; do not change `Types::name` or imply runtime representation changes.
6. Run positive and hostile tests, full integration gate and soundness review
   before closing LT-VARIANCE. Recursive implementation can start independently
   using today's invariant rules, but any later nested lifetime coercion must
   use this judgment and only finalized recursive signatures.

Required tests include:

- Exhaustive algebra tables (including unused/invariant), seeded/unseeded
  recursive declaration graphs, order independence and unknown defaults.
- By-value shortening of shared/exclusive borrows and supported owned containers;
  reverse lifetime extension must fail without proof. Preserve all owner loans.
- `&mut Box<&T>` / `&mut Vec<&T>` write-then-read attacks; mixed occurrences
  in records; nested invariant positions and shared downgrade alias attacks.
- Function parameter direction, result direction, alpha-equivalent occurrence
  maps, many-to-one mappings, and two distinct source environments sharing an
  interned callable type. Reject free/bound capture and double polarity flips.
- Existing anonymous intersections and elision must not regress; unknown labels
  cannot acquire an arbitrary named lifetime. No closure-environment laundering.
- Borrowed-record containers, field reordering, width coercions with a source
  copy still live, owner mutation after a label conversion, and destination-
  declared-label checks on writes. Preserve current conservative payload limits.
- Optional-reference enum, TaskExit and structural exactness regressions; type-
  argument representation changes, grade/effect/linear contract changes and
  unsupported higher-rank cases remain rejected.
- Reference/native agreement and balanced cleanup for accepted executable cases;
  existing lifetime, borrowing, callable, subtyping and review-regression suites.

This is an engineering design and test contract, not a soundness proof. No
compiler build, runtime test or Boat run is evidence for this document: only
source review and finite-algebra sanity checks apply at the design stage.

## Relation to recursive lifetime inference

See [recursive lifetime design](recursive-lifetime-design.md). Both designs
separate assumed constraints from evidence and required obligations. Variance
checks a conversion using an already justified context; recursive inference
computes finite origin/requirement summaries, then freezes and revalidates them.
Neither may manufacture an outlives assumption to prove its own success.

The first recursive fragment does not depend on implementing this variance
extension. Variance must not read provisional recursive signatures, and recursive
inference must not use erased-shape acceptance as a substitute for lifetime-
aware conversion once that conversion is enabled. SCC decomposition mechanics
may eventually be shared; solver meanings and proof obligations remain separate.
