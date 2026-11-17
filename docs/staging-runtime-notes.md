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
- Update Tree-sitter/editor grammar support for staged declarations and quote
  syntax. Parser lambda spans now start at fn, not quote, so tools that edit
  lambda annotations preserve their surrounding stage boundary.
- Runtime Code.compile and owner-bound calls are NOT implemented yet. Do not
  close STAGING-RUNTIME or STAGING-JIT.

## Runtime implementation direction to evaluate

An in-process native linker for checked template machine code can reuse the
existing native backend without embedding a subprocess compiler or an IR
interpreter in the resulting program. Source quotations provide the finite
native template schemas; runtime generators build arbitrary graphs of those
schemas and runtime constant values.

1. Add a nominal, opaque compiled-code owner carrying F. Its native
   representation owns executable storage and has exactly-once release;
   the evaluator owns an instantiated checked-program snapshot.
2. `Code.compile(code)` consumes its graph and returns a fallible compiled
   owner. `Code.call(&owner, args...)` retains the owner borrow for the whole
   call and checks F's arguments, effects, grades and mutation summaries.
   Do not expose a standalone function pointer. Initially reject callable or
   borrowed results that could escape the owner's lifetime unless their
   provenance is represented correctly.
3. Prepare native recipe functions from the checked template IR. Runtime
   parameters retain F's ABI; captured scalar/text values are immutable
   artifact data references; splice placeholders become relocations to
   compiled child fragments. Emit actual native template bodies, not a
   closure trampoline or a per-call graph interpreter.
4. Capture native bytes and relocations from Cranelift compilation. The
   current backend uses PIC. Handle its call, data/GOT and absolute
   relocation forms explicitly; return unsupported errors for other forms.
   `CodeModule::define_function` and the loop around `context.func` compilation
   are the likely integration points. Symbol addresses can be emitted in an
   object data table, retaining access to local Kush function symbols without
   exporting them all as C APIs.
5. Allocate a bounded, contiguous artifact writable and non-executable;
   copy code/data, resolve relocations (including near thunks for far function
   calls), then publish only after changing to read/execute. Never map RWX.
   Keep constants and every child fragment alive under the same owner.
6. The reference evaluator may instantiate and interpret the same typed graph
   as the semantic oracle. Native runtime compilation must generate executable
   memory in process and must not spawn cc/kush/clang or invoke the evaluator.
7. Test runtime-input specialization, repeated compile/call/drop, sharing and
   suspension where supported, unwinding, owner escape rejection, mapping
   permissions, and allocation/relocation/mprotect failure cleanup. A test C
   shim can override mmap/mprotect/munmap via ordinary link objects to observe
   publication and inject failures without changing the public API.

This direction still needs implementation and verification. It must preserve
normal ABI/ownership semantics for aggregate parameters/results; do not mark
it done for a scalar-only demonstration.

### Runtime details worth retaining

- A Code.call intrinsic should keep the borrowed compiled owner as a direct
  argument until the actual call. Loading an unowned Fn pointer in an earlier
  callee subexpression could let argument evaluation drop the owner before
  invocation. Do not introduce that lifetime gap.
- The native backend currently sets is_pic=true. Recipes need explicit GOT/data
  handling as well as call relocations. Far calls can use nearby r11 jump
  thunks without disturbing System V argument registers; far data references
  require copied constant data or GOT slots, not executable jump thunks.
- A compiler-emitted symbol-address table can reference local object functions
  and data while itself having an exported name. Keep module FuncId/DataId
  distinct from the executable function indices stored in graph bytes.
- Scalar captures can become immutable artifact data loads. Text captures need
  borrowed buffer-handle slots plus immutable buffer storage; generated uses
  still copy them into new owning buffers. Verify the actual runtime buffer
  header layout before implementing this.
- The whole graph and any placeholder-dependent helper copies should belong
  to one artifact. Resolve child-fragment calls directly within that artifact.
  Existing named helpers may remain references to binary-lifetime symbols.
- A runtime result containing a callable or borrowed artifact storage must not
  outlive the compiled owner. Reject such results until provenance is modeled;
  owning data and independently serialized Code graphs can be returned safely.
- A reference-evaluator artifact may own a checked executable snapshot. Use
  erased Read/Write trait-object types for nested evaluator calls, otherwise
  repeatedly nesting generic &mut R/&mut W types can cause infinite Rust
  monomorphization. Share heap/statistics/host access and preserve fuel limits.
