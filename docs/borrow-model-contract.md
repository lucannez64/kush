# Kush loan model: operational contract for lifetime work

This is the RES-BORROW-MODEL subset mapping and trace specification, not an
implementation of Rust Tree Borrows or a formal soundness theorem. It supplies
review obligations for LIFE without depending on unfinished effects or layouts.
It does not authorize new raw pointers, alias metadata, interior mutability or
relaxation of existing rejection rules.

## State and evidence

Treat each owner allocation/pinned local as a storage identity. A reference or
view carries a set of possible origins, each with a root, typed projection or
range, mutability, and checked capability ancestry. Region labels describe
signature relations; they do not identify the storage root. Two equal labels
are not evidence that two capabilities alias, nor are distinct labels evidence
that they are disjoint.

A derived borrow creates a child capability rooted in its parent's storage.
The child region cannot exceed the parent's available storage/lifetime. Shared
access can coexist where the current rules permit it. An exclusive child
suspends conflicting parent/sibling accesses until its checked last use; a
shared-to-exclusive upgrade is rejected. Disjoint structural fields, constant
indices and established split identities keep their existing explicit proofs.
Unknown dynamic index/range relationships remain conflicting, not disjoint.

Ending one view's use does not invalidate another live shared copy. In the
current checker an assignment from a view can be represented as a derived view:
its parent binding may not be dropped while that child remains live. This is a
conservative static restriction; independent shared borrows of the owner need
not retain one another's binding. The baseline tests distinguish these cases. A mutable
view is not copyable. Moving an owning carrier transfers its leaf provenance;
dropping it releases only that carrier's obligations, not another value's loans.
Owner mutation, replacement, drop or move must conflict with every retained
loan whose storage can overlap. Physical pool reuse must not make a stale root
look like a new live allocation.

## Required access traces

Each trace describes a checked-language obligation; it is not an oracle for
Rust unsafe code or permission to run an invalid access in native code.

| Trace | Required outcome |
| --- | --- |
| owner -> two independent shared borrows -> drop first -> mutate owner -> use second | reject owner mutation; the second borrow keeps its loan |
| shared parent view -> derived view by assignment -> drop parent -> use child | current checker rejects parent drop; do not relax this silently |
| shared parent and derived view -> last child use -> parent drop -> owner mutation | accept when all checked loans have ended |
| owner -> exclusive parent -> exclusive child -> access overlapping parent -> use child | reject parent access while child remains live |
| same sequence, child last use then parent access | accept when the current last-use rules release the child |
| exclusive root -> two proven disjoint field/split children -> writes to each | accept; destroying/replacing the whole root while either child is live rejects |
| stored exclusive reference passed twice to one call | reject overlapping child capabilities; sequential calls may reuse the reference |
| borrowed record -> field-reordering structural coercion -> retained leaf -> owner replacement | reject replacement using the retained field's remapped root |
| borrowed container -> clear/replace payload -> previously extracted live leaf | the extracted leaf still keeps its own loan; do not release it with the container |
| branch-selected return or recursive summary with possible origins A and B | retain both roots, even if one result lifetime name is printed |
| borrowed result with an explicitly long annotation but a block-local actual root | reject; the annotation cannot manufacture caller-owned storage |
| temporary owner initialized in a skipped operand | no initialization, access, drop or loan is observed |
| early exit after temporary initialization or handler/task capture | initialized owners clean up once; no returned leaf may outlive storage |

Existing regression coverage includes `borrowing_safety.rs`,
`borrowing_references.rs`, `callable_lifetimes.rs`, `lifetimes.rs` and the
structural/row tests in `advanced_types_effects.rs`. These names identify test
families, not a claim that every future variance/recursive combination has
already been tested. LT-VAR-TESTS, LT-REC-TESTS and the row-result gate must
instantiate the relevant traces at their new boundaries.

## Static analysis versus an operational alias model

[Tree Borrows, PLDI 2025](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
provides a Rust aliasing semantics with permission transitions and protected
accesses, especially important for unsafe interactions. Kush's current checker
has a conservative capability ancestry and last-use model. There is no claimed
bijection between these states and Tree Borrows states such as reserved,
active or disabled, and no current semantic implementation of its protectors.
A tree-shaped data structure is not that correspondence.

For a future mapping, define a simulation from checked accesses to operations
on the chosen semantic model. Prove preservation of allocation identity,
projections, parent suspension, callback protection, destruction and reuse.
Classify safe patterns rejected by the static checker as deliberate restrictions;
do not treat a semantic model accepting a pattern as sufficient evidence to
accept it statically. At foreign boundaries, raw host code remains trusted;
unsupported pointer retention is not validated by the signature alone.

Do not emit stronger alias attributes or reorder accesses based on this document.
Any such optimization needs its own precise generated-code assumptions and
counterexample tests, then a proof/validation against the selected alias model.

## LIFE-specific checks

Variance witnesses relate labels but must preserve the root/path set. Mutable
writes validate the declared destination lifetime, not a shortened temporary
read label. Callable source/target label environments are occurrence-specific;
alpha-equivalent interned arrows can still refer to different actual owners.

Recursive summaries accumulate possible origins and caller requirements. They
must not assume a requirement to justify itself or bootstrap a seedless cycle.
Final ownership checking still validates the actual roots at every return and
call after signatures stabilize. No provisional summary is an access proof.

Structural row interning, residual-row inference and field remapping preserve
labels and leaf paths together; source copies retain their own loans. See
[lifetime row contract](lifetime-rows-design.md). Final integration must test the
composition of all three mechanisms rather than only their isolated happy paths.

This contract completes the immediate subset audit and trace plan. A formal
simulation, Tree Borrows interpreter, raw-pointer support and optimizer alias
proofs are not completed by it. The scope is a precise operational review
contract for current checked Kush and the upcoming LIFE changes.


Validation: the five focused `lifetime_integration_baseline` tests and strict
Clippy passed on Boat. The accepted last-use case also compares reference,
default native and release native execution. This is focused baseline evidence,
not a full-suite result for the upcoming delegated implementations. The initial
probe confirmed a conservative derived-view parent-drop restriction; tests and
this contract preserve it rather than claiming Rust-style view-copy semantics.
