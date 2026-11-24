# Staging runtime implementation notes

Implementation notes for typed staging. The design contract and its
restrictions are in `docs/staging.md`.

## Current implementation

- `Code<F>` is an opaque nominal record with a private `$graph: Bytes` field;
  `F` is a reusable callable type retained in the nominal instantiation.
  Existing aggregate ownership/drop code makes the graph affine.
- `Code.clone(&code)` explicitly clones its serialized graph.
- Quote checking uses the ordinary callable checker and stage-aware resolved
  binding identities. Lift/splice operands are evaluated once, in source
  order, at construction. `quote_holes` maps source occurrences to captured
  parameter slots during template checking. `quote_splices` maps splice
  occurrences to typed, unobservable placeholder functions.
- Graphs use KUSHCD01 (closed), KUSHCD02 (scalar captures) and KUSHCD03
  (tagged captures). Words are little-endian u64. Each graph contains its
  checked template's function index, then (when captured) a capture count.
  V3 scalar tag 0 has a word; code tag 1 has a placeholder index, nested
  graph length and bytes; owned text tag 2 has its length and bytes.
- Scalars preserve their raw word bits. Bytes/String lifts copy contents;
  generated uses allocate independent copies, requiring alloc/panic in F.
- `staging::prepare` keeps original staged signatures behind Never stubs and
  creates parameterless generation entries returning the expected Code<F>.
  Their effect row is restricted to alloc/panic.
- `staging::materialize` runs checked generation entries, orders staged
  dependencies (rescanning after each dependency is materialized), decodes
  graph nodes and specializes typed IR. Captured scalars become constant
  arguments, owned text copies become literal expressions, and splices
  become references to independently instantiated callable fragments.
  Affected helper functions are cloned so distinct instances never rewrite
  one another. Abort propagation, ownership and grades are rechecked before
  a dependent generator may invoke a newly materialized function.
- Suspension lowering is postponed until all staged declarations are ready.
- Nested quote traversal tracks stage levels; e.g. a generated function can
  construct Code for a later staged declaration, with double lift moving an
  earlier-stage value across both levels.

Targeted tests in `tests/staging.rs` cover evaluator/native recursive power,
independent scalar specializations, nested stages and owned text/float lifting.
The owned-text test also checks LLVM. The whole compiler gate must pass before
committing these changes.

## Checks and limits

- Declarations parameterized by unconstrained types and effect rows are
  checked in a separate pass using distinct opaque affine types, even when
  all concrete calls happen to select the same type, and with every effect
  row the binder bounds allow (`generic_quotation_cases`). A lifted opaque
  value keeps its type during quotation checking. Its representation is
  checked and encoded in the concrete specialization. Trait-bound, grade and
  natural binders are checked per instantiation, like ordinary generics,
  plus the value-independent declaration checks in `check_generic_quotes`.
  Stage scope validation covers every declaration.
- Generic staged declarations specialize their initializers along with their
  callable signatures. Initializers can request further stage specializations.
  Staged declarations keep erased proof and shared length preconditions at
  call sites. Mutable length refinements are proved by
  `check_length_preservation` over the generated body and every function it
  reaches; staged postconditions are rejected.
- Staged exports link through the ordinary native ABI on Cranelift and LLVM.
- Ordinary nested closures take their own copies of lifted text in AOT and
  runtime templates. AOT also specializes splices inside nested closures.
- The generator budget counts heap-backed buffers, vectors and boxes, plus
  every arena chunk and arena payload a generator requests. Arena charges are
  never credited back. Custom allocator contexts are rejected by the
  generator sandbox because their storage is not accounted for.
- Regressions cover fuel and memory exhaustion, panic, effect rejection,
  affine reuse, ill-typed holes, private-module splices and exact grade transfer.
- Native lowering interns byte constants by content as it reaches each body.
  The native power example contains neither the generating functions nor
  their serialized graphs. The mixed AOT and runtime test checks that two
  literals sharing a source span keep their distinct values.
- The Tree-sitter query highlights contextual `quote fn` and the existing
  attribute rule covers `#[staged]`. The parser's lambda span begins at
  `fn` so annotation edits preserve the quotation boundary.
- Runtime `Code.compile` / `Code.call` have a checked interface and reference
  evaluator implementation in the current worktree. `CompiledCode<F>` is an
  affine opaque owner; calls hold its borrow through argument evaluation.
  Evaluator artifacts retain a checked program snapshot and share the caller's
  heap, allocation budget, I/O and task control state. Newly instantiated
  functions are ownership/grade checked without re-elaborating existing bodies.
  Callable-containing results are conservatively rejected to prevent artifact
  addresses escaping their owner. The check includes opaque dynamic objects
  and allocator contexts and follows references and containers.
- The Linux x86-64 Cranelift backend emits checked machine-code recipes and
  relocation metadata. The runtime copies code and lifted values into bounded
  RW storage, links the splice targets and symbols, then publishes the entry
  after changing the populated pages to RX. Tests cover independent recursive
  splices, specialization from standard input, lifted buffer copies, owner
  cleanup during panic unwinding, allocation refusal, mapping failure and
  permission failure.
- Runtime splices currently require immediate calls in the quotation because
  first-class functions cannot express the compiled owner's lifetime. An
  LLVM build hands each recipe to LLVM as usual and also compiles it with
  Cranelift for the image; the LLVM backend writes the image's function and
  data addresses as `ptr` fields of packed constants, and capture slots have
  names so a recipe in another partition can reach them. The tests run every
  runtime-staging program under both backends. The compiler registers checked
  quotation templates by function identity. Native lowering queues a recipe
  only when a reachable body contains that template's graph literal, so
  templates used only at compile time are not emitted. LLVM AOT staging has
  independent coverage.

## Runtime validation

- Tests cover scalar and aggregate values, grade-zero and exactly-once
  arguments, owning buffer returns, and a view tied to a call argument.
- The nested runtime test repeatedly compiles, calls and drops both stages.
  Independent OS threads repeatedly compile the same checked template with
  separate scalar captures and owners. A suspended compiled call resumes
  after another task compiles, calls and drops its own artifact. These cases
  have evaluator and Cranelift coverage, as do immutable sharing of a single
  compiled owner through a borrowed slice and cancellation of a suspended call.
- A native runtime fault test supplies an out-of-bounds relocation and verifies
  that linking returns ENOTSUP, never publishes executable pages, and releases
  both the mapping and the remaining allocations.
- Relocations: the recipe table encodes Abs8, X86PCRel4, X86CallPCRel4,
  X86CallPLTRel4 and X86GOTPCRel4 against functions, data, function offsets
  and capture slots. Any other kind or target is encoded as 255, and
  `kush_stage_patch` fails on it, so `Code.compile` returns an error before
  any page becomes executable. Schema lookup accepts only recipes the
  executable lowered.

## Runtime measurements

An optimized Cranelift build on the Ryzen 5 PRO 5675U specialized a function
that XORs its input with a lifted scalar. Across five runs, the median of
2,000 generate/compile/call/drop iterations was about 112 µs per iteration.
The median of one million calls through one retained owner, including the loop
and checksum, was about 4.9 ns per call. A separate run observed 56 bytes of
linked code, constants, and relocation slots passed to `mprotect` before page
rounding.
