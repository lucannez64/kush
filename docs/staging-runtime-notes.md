# Staging runtime implementation notes

Working notes for the active, user-approved staging goal. These are not a
completion claim. The design contract remains in `docs/staging.md`.

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

## Remaining correctness work

- Universal validation of unused generic quotation templates; current generic
  instantiations use the ordinary lazy monomorphization checker, while stage
  scope validation covers even uninstantiated definitions. Do not claim all
  generic templates are checked yet.
- Staged declarations currently reject generics, ensures, erased proof parameters
  and length-refined parameters explicitly; remove these restrictions only
  with correct checking and negative regressions. Ordinary grade-zero runtime
  parameters are supported and forwarded as Erased values by specialization.
- Nested ordinary callable templates with owned captures/splices currently
  produce an explicit unsupported diagnostic. Nested quotation stages work.
- Arenas and custom allocator contexts are explicitly rejected by the generator
  sandbox until their storage is accounted for. Current heap accounting covers
  ordinary heap-backed buffers/vectors/boxes.
- Add fuel, memory, panic, effect, affine reuse, bad-hole and hygiene regression
  coverage, including private-module splices and exact grade transfer.
- Remove compile-time-only generation work from final native artifacts without
  discarding template identities still needed by runtime code construction.
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
  addresses escaping their owner; review dynamic-object/allocator results too.
- The Linux x86-64 Cranelift backend emits checked machine-code recipes and
  relocation metadata. The runtime copies code and lifted values into bounded
  RW storage, links the splice targets and symbols, then publishes the entry
  after changing the populated pages to RX. Tests cover independent recursive
  splices, specialization from standard input, lifted buffer copies, owner
  cleanup during panic unwinding, allocation refusal, mapping failure and
  permission failure.
- Runtime splices currently require immediate calls in the quotation because
  first-class functions cannot express the compiled owner's lifetime. LLVM
  runtime compilation returns ENOTSUP. The compiler registers checked
  quotation templates by function identity. Pruning unreachable recipes,
  auditing additional relocation cases and validating concurrent use remain
  open. LLVM AOT staging has independent coverage.

## Runtime follow-up

- Cover nonzero exact usage contracts across the compiled call ABI. Tests
  cover scalar and aggregate values, grade-zero arguments, owning buffer
  returns and a view whose lifetime is tied to a call argument.
- The nested runtime test repeatedly compiles, calls and drops both stages.
  Independent OS threads repeatedly compile the same checked template with
  separate scalar captures and owners. A suspended compiled call resumes
  after another task compiles, calls and drops its own artifact. These cases
  have evaluator and Cranelift coverage. Cross-thread owner sharing, cancellation
  of suspended compiled calls, and relocation failure still need coverage.
- Audit code graph schema discovery and symbol relocation against all forms
  emitted by the native backend. Unrecognized relocations fail compilation.
- Benchmark compilation latency, generated image sizes and steady-state calls.
