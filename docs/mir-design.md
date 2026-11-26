# A typed control-flow-graph IR (design draft)

Status: **approved** (plan node FND-MIR-DESIGN, 2026-11-25). The user took
every recommendation in section 7. Implementation starts with FND-MIR.

Motivation: [foundations-review.md](foundations-review.md) section 8. The
checker produces a tree, and five passes walk that tree separately. Every
language feature is therefore implemented twice, once in the evaluator and
once in native lowering. Borrows are checked on the tree's lexical
structure, and the LLVM backend only ever sees Cranelift instructions.

## 1. What exists today

```text
source -> parse -> resolve -> check (executable/, 42k lines before the split)
       -> checked tree: Executable { functions: [Function { locals, body: Block }] }
          ExprKind has about 100 variants
       -> gpu::check, multishot::check
       -> suspend::mark_abort_calls
       -> ownership::check   (8.4k lines: moves, drops, loans, linearity)
       -> grades::check      (2.5k lines: usage grades)
       -> suspend::lower     (4.0k lines: handled bodies become state machines)
       -> eval.rs            (9.9k lines: tree interpreter)
       -> native.rs          (11.9k lines: tree to Cranelift)
          -> native/llvm.rs  (2.5k lines: Cranelift IR to LLVM IR)
```

Costs of the tree, in order of how much they hurt:

- **Two implementations of each feature.** `eval.rs` and `native.rs` each
  interpret every `ExprKind`. Each new feature needs both, and differential
  tests guard the agreement.
- **Lexical borrow checking.** A borrow lives for a block, a full
  expression or a call. Liveness-based borrows, references inside tuples,
  generics and enums, and two-phase borrows all need flow-sensitive facts
  (FND-BORROWCK, FND-REF-*), which a tree walk can only approximate.
- **Suspension by reconstruction.** `suspend::lower` rebuilds the rest of a
  body structurally for each suspension point, through blocks, branches and
  loops. On a CFG, the rest of the body after a point is simply a set of
  blocks.
- **LLVM without types.** The LLVM backend translates Cranelift IR, so it
  never sees ownership or aliasing (FND-LLVM-DIRECT).

## 2. The IR

Rust MIR is the model, minus what Kush does not have (lifetimes are already
solved by the checker, and there is no trait resolution at this stage).

```text
Body      = { locals: [Local], blocks: [Block], span }
Local     = { ty: Type, grade, span, name? }          -- today's Local, unchanged
Block     = { statements: [Statement], terminator: Terminator }
Place     = Local + [Projection]
Projection= Field(offset, ty) | Index(Operand) | ConstIndex(n)
          | Deref | Variant(tag) | Subslice(start, end)
Operand   = Copy(Place) | Move(Place) | Constant(value, ty)
Rvalue    = Use(Operand) | Binary(op, Operand, Operand, Checked|Proved(cert))
          | Unary(op, Operand) | Aggregate(kind, [Operand])
          | Ref(Shared|Exclusive, Place, Loan) | Len(Place)
          | Cast(kind, Operand, ty) | Closure(function, [Operand])
Statement = Assign(Place, Rvalue) | StorageLive(Local) | StorageDead(Local)
          | Check(Operand, Panic, span)       -- a run-time check that panics
          | Fact(cert)                        -- a proved obligation, for reports
Terminator= Goto(b) | Switch(Operand, [(value, b)], otherwise)
          | Call { callee, args, destination, next, unwind }
          | Drop { place, next, unwind }
          | Return | Unreachable | Panic(kind, span)
          | Perform { operation, payload, destination, resume, unwind }
          | HandlerEnter { frame, next } | HandlerExit { frame, next }
```

The tree's IDs and layouts stay as they are: types, function indices,
layout IDs, certificates and spans keep their current meaning, so passes
that do not move to the CFG can keep reading them.

Each statement and terminator carries a span, so panics and diagnostics
point where they point today.

## 3. What each consumer needs from it

| Consumer | Needs |
| --- | --- |
| Ownership and drops (today's `ownership.rs`) | Move paths over places; drop elaboration with drop flags for conditionally moved values; `StorageDead` at scope ends. |
| Borrow checker (FND-BORROWCK) | A `Loan` on every `Ref`; liveness of each loan over the CFG; the conflict rules from [borrow-model-contract.md](borrow-model-contract.md); two-phase borrows as a `Ref` whose activation is its first use. |
| Grades | Uses counted per place along each path (G-B, later). |
| Suspension (`suspend.rs`) | `Perform` terminators; liveness at each one; the blocks after a point become its continuation. |
| Evaluator | One small interpreter over places, statements and terminators. Panic messages are unchanged. |
| Native (Cranelift) | Blocks map to Cranelift blocks; places to loads and stores with the existing layouts; `Proved` operations and `Fact`s drop their checks; `unwind` edges become the existing panic test after each call. |
| LLVM (FND-LLVM-DIRECT) | The same, emitted directly; `Exclusive` references and owners give `noalias`, and proved ranges give `!range`. |
| Reports (`KUSH_PROOF_REPORT`, fuzz) | `Check` and `Fact` with their obligations, as `record_obligation` records them today. |

## 4. Building it

The checker keeps producing the tree; a new pass `mir::build` lowers each
checked function to a `Body`. Expressions become temporaries, `&&`, `||`,
`if`, `match`, loops and `?` become branches. `break` and `return` become
gotos through the drops of the scopes they leave. Handled bodies become
`HandlerEnter`, the body's blocks, and `HandlerExit`. An abortive `perform`
becomes a call that exits to the handler's block.

A later step can move checking itself to produce the CFG. It is not needed
for any node in the plan.

## 5. Unwinding

A panic unwinds to a catch boundary today: a thread-local word, tested
after every call (PANIC-UNWIND-NATIVE). On the CFG this becomes explicit:
every `Call`, `Drop` and `Perform` has an `unwind` edge to a cleanup block
that drops what is live and continues unwinding. Native code can keep the
test after each call and branch to that edge, so nothing changes at run
time. What it gains is that cleanup becomes ordinary IR, checked and
optimized like the rest.

## 6. Migration

Each step keeps the whole suite green, and both paths run side by side
until the tree path is deleted:

1. **FND-MIR**: `mir::build`, a text dump (`kush mir FILE`), and native
   code from the MIR behind `KUSH_MIR=1`. Every native test runs on both
   paths; the tree path stays the default until they agree everywhere.
2. **FND-MIR-EVAL**: the evaluator runs the MIR. The tree evaluator stays
   as a differential oracle for one release, then goes.
3. **FND-LLVM-DIRECT**: LLVM from the MIR; the Cranelift-to-LLVM
   translation goes.
4. **FND-BORROWCK**: loans and their conflicts on the MIR, with
   `ownership.rs`'s lexical rules as the oracle until the traces of
   borrow-model-contract.md all agree. Then the reference rework
   (FND-REF-*) builds on it.
5. Suspension lowering moves to the CFG with FND-HANDLERS-ONE, which needs
   `Perform` as a terminator anyway.

### Where FND-MIR stands

The first slice (FND-MIR-CORE) is in `crates/kush/src/mir.rs`:

- `mir::build` covers functions whose locals and values are one-word
  scalars (integers, floats, `char`, `bool`, `()`): arithmetic, the
  integer builtins with a one-word result (including arithmetic the
  checker proved in range, which carries no check), assignments, `if`,
  `match` on literals with guards, `while`, `loop` with `break` values,
  `continue`, `return`, direct calls, `print_i64` and `panic`. Any other
  function is reported with the first construct the builder does not
  cover.
- `mir::verify` checks blocks, locals and operand types.
- `kush mir FILE` prints the text form; `kush mir FILE --stats` prints the
  coverage. The parser reads the text back, and `tests/mir.rs` checks that
  every body built from the examples verifies and round-trips.
- Native code is lowered from the MIR only (FND-MIR-DEFAULT deleted the
  tree lowering). A function the builder does not cover is a build error
  when a build reaches it. The leaf operations are the helpers the tree
  path used.

FND-MIR-AGGREGATES added records and enums that own nothing and hold no
borrow. A record or enum is a run of words, so a place is a local plus at
most one field (a word offset and a type), however deeply the source
nests. `aggregate` builds a variant, and `match` compiles variant,
literal and or-patterns to switches on words, following each variant's
tag or niche.

FND-MIR-OWNED added boxes, vectors, `Bytes`, `String` and records and
enums that own them. Every drop is now in the MIR:

- Each checked resource that owns something gets a drop flag (a `bool`
  local) and a value local. These are the tree path's tracked words and
  activation flags, made explicit. An expression's owned result sets its
  flag. The parent that takes ownership (a call, a constructor, a `let`,
  an assignment, a `return`, a matching arm) clears it, exactly where the
  tree path calls `consume`.
- The end of a scope, a reassignment, `break`, `continue` and `return`
  drop each resource whose flag is set: a `switch` on the flag, then a
  `drop` terminator.
- A matching arm owns its scrutinee. Bindings take their parts, and the
  parts under `_` are dropped.
- A function with owned resources has one cleanup block. Every call,
  `panic` and checked statement unwinds to it. It drops every live
  resource and ends in `resume`. Native code jumps there wherever the tree
  path ran `unwind_exit`.

A local's resource is dropped from the local itself, so a value replaced
through `&mut` is the one dropped. Other resources are dropped from their
own value local.

FND-MIR-REFS (first part) added references:

- A place may go through the reference held in a local: `*_p.off:ty` is
  the words of type `ty` at word `off` of the pointee.
- Assignments target places, so writes through references are ordinary
  assignments. A write replacing an owned pointee drops the old value
  first.
- `&place` takes an address the way the tree path does. A whole local
  uses its pinned storage, or a snapshot when it was never pinned, and a
  field adds its offset to the local's address.

The second part added views, inline arrays and builtins:

- `view` builds a slice or text view of an array local (aliasing its
  storage when it has a stable address), a `&Vec`, `&Bytes`, `&String`,
  an array value or another view, with an optional range check.
- Every builtin call target is a `call builtin N` terminator. Native code lowers it through the same `call_target`
  dispatch as the tree path. Each body lists its builtins. The text form
  declares each one as `builtin N = "<json>";`, which is their exact
  serde form, and reads it back (FND-MIR-TEXT-BUILTINS).
- The tree path's loop optimizations (vector push shadows, deferred
  proofs of element accesses) key their facts on tree expressions, so the
  MIR path calls builtins without them. Porting them is part of
  FND-MIR-DEFAULT.

FND-MIR-CALLABLES added function values and the values that change
representation:

- `fn_value F(captures)` builds a code pointer and, for a closure, an
  owned environment laid out as on the tree path. A by-reference capture
  stores the local's address.
- `call indirect` calls a `fn` or `once fn` value with the tree path's
  ABI.
- Closure bodies are covered too. The native frame setup already loads
  their captures into locals.
- `coerce N(value)` applies the body's Nth coercion: union injection and
  repacking, structural record coercions, `dyn` boxing and upcasts, and
  callable adapters. Like builtins, coercions are listed per body and
  declared in the text form as `coercion N = "<json>";`.
- Union patterns test the member tag word, then the member's words.

FND-MIR-EFFECTS covered the effect machinery that remains after
`suspend::lower`, which still runs on the tree before the MIR is built
(decision 4):

- **Continuations:** continuation functions activate their parameters at
  their slots. `multi fn` values push their environment on the
  continuation stack, and calls through them mark and restore it.
- **Regions:** a region is an exit block plus a finish block that calls
  the finish callable.
- **Tasks:** a `task` rvalue runs spawn, scope, catch, yield, cancel and
  join through helpers shared with the tree path.
- **Handler stack:** a `runtime` rvalue manages the handler and
  continuation stacks (push, pop, redirect, depth, marks, dynamic
  performs). In functions that install handlers, loops and regions restore
  the handler depth on their exits.
- **Aborts:**
  - An abort scope lands in a block that runs its handler.
  - `AbortExit` jumps there.
  - `AbortPerform` raises the abort and leaves with the `abort`
    terminator.
  - `AbortCall` dispatches a set abort word to the scope it names, or
    propagates it.

FND-MIR-BUILTINS finished the ordinary values:

- Recursive enums (through boxes) are covered. The type check treats a
  type it is already checking as covered.
- `?` is a switch on the tag word. The error branch builds the function's
  error variant and returns through the usual cleanup.
- Box reads are two loads through places. A proved byte read is `byte_at`.
  I/O handles are one-word values.

What remains outside the MIR, apart from effects, is listed on
FND-MIR-SHAPES. So far, that node has moved these into the MIR:

- **Allocators and arenas:** an `alloc` rvalue covers allocator values
  and contexts, arenas, allocator boxes and vectors.
- **Box reuse and fallible allocation:** the same rvalue covers
  `Box.reuse`, `Box.reuse_grow`, box writes, `try_new`, `try_reuse`,
  `Bytes.try_with_capacity` and the fallible allocator and arena
  forms. These share their native code with the tree path.
- **Erased arguments:** an erased argument is a zero constant of its
  type.
- **Runtime-length arrays:** an `array` rvalue covers `DynArray` and
  `[T; n <= C]` operations (new, push, fill, set, pop, equality).
  - Array patterns test the array's words in the subject, at any depth.
    Suffix elements and the rest come from `array` operations on the
    array.
  - In a match through a reference, element names bind slot addresses
    and the rest binds a view.
  - A view of a stored array (a borrowed local or a record field) is a
    `dynarray` view source that aliases its storage.
- **In-place maps:** a `map` rvalue runs `Vec.map` with the tree path's
  loop. For each callback, it records the function a capture-free
  function value calls, so native code can still inline it.

- **Structural equality:** `struct_eq` and `struct_ne` compare two
  records or enums field by field.

- **Staging calls:** `StageCompile` and `StageEntry` are now ordinary
  builtin calls like the rest.

Every function in the test suite builds a MIR body. The loops the tree
path optimized are covered by the passes of section 8.

FND-MIR-DROP-FLAGS (`mir/drop_flags.rs`) runs on every built body:

- A forward dataflow over normal and unwind edges computes each drop
  flag's value. Drop flags are boolean temporaries that are only assigned
  constants and only tested by `switch`.
- The dataflow is path-sensitive: a test of a known flag only reaches the
  branch it takes, and a block's unwind target sees the values before
  each statement that can panic (a flag assignment or a copy cannot).
- Each test whose outcome is known becomes a `goto`, and flags that are
  no longer tested lose their assignments.

On normal paths a flag test survives only where a value was moved on some
paths but not others. The shared unwind cleanup is reached from points
where the flags differ, so it keeps its tests. Specializing the cleanup
per call site would remove those too; that is not done.

FND-MIR-DIRECT-INIT and FND-MIR-COPY-PROP remove the builder's
temporaries:

- **Direct init:** a `let` takes its initializer's value as soon as it
  exists, so the initializer is not tracked as a resource (no cleanup
  copy, no drop flag). A temporary defined just before (by the last
  statement, or by the call that enters the block) is retargeted to the
  binding.
- **Copy propagation** (`mir/copy_prop.rs`, after the drop flags):
  - `x = move t` folds into `t`'s definition in the same block, or into
    the call that enters it, when `t` has no other use and nothing in
    between touches `x`.
  - A single-use `t = copy x` becomes a direct read of `x`, when nothing
    in between assigns `x`.
  - Jumps through empty `goto` blocks go straight to their target, and
    blocks the entry does not reach (folded cleanups) are removed.
- Locals whose address is taken are never involved, and the temporaries
  cleanup reads have two uses, so drop elaboration and unwinding are
  unchanged. The loop passes read their patterns through either form.
- A function with two `let x = Bytes.from(..)` and a print goes from 25
  blocks to 11.

## 7. Decisions

Taken on 2026-11-25:

1. **Unwinding**: explicit `unwind` edges and cleanup blocks in the IR
   (section 5). They make the evaluator and both backends share one
   cleanup implementation.
2. **Drops**: drop elaboration in the MIR, with drop flags for values moved
   on some paths only. The borrow checker needs the same move paths.
3. **Representation**: non-SSA places as in Rust MIR. Kush has fields,
   indices and references to projections, and Cranelift and LLVM build SSA
   themselves.
4. **Suspension**: `suspend::lower` moves to the CFG with FND-HANDLERS-ONE.
   Until then, `Suspendable` regions are lowered on the tree before the MIR
   is built.
5. **Text form**: a stable, parseable text form for MIR dumps, used in
   tests the way the kernel exchange format is.
6. **Loop optimizations** (FND-MIR-DEFAULT): rewritten as MIR passes
   (section 8), not carried over from the tree path. Taken by the user.
7. **Evaluator** (FND-MIR-EVAL): a word-level machine over the MIR with
   native's data layouts (section 9), not an interpreter over the tree
   evaluator's structured values. Taken by the user.

## 8. Loop optimizations on the MIR

The tree path optimizes `while` loops in four ways. Each reads tree
expressions and lowers the loop body more than once:

| Optimization | When | Tree code |
|---|---|---|
| Upper-bound facts: `i < v.len()` drops the upper bound check of `v[i]` | `Speed` | `upper_bounds`, `slice_out_of_bounds` |
| Slice-layout versioning: a copy of the loop where the view `v` has whole consecutive elements | `Speed` | `lower_checked_while` |
| Push shadows: a vector's length and capacity in variables across `v = v.push(e)` | `Speed` and LLVM | `lower_while`, `vec_push` |
| Deferred overflow checks (`native/deferred.rs`) | `defers_overflow()` | `lower_deferred_while` |

All four now exist on the MIR. `mir::optimize` runs them in that order
on every body a build lowers, and `kush mir FILE` with build flags prints
the result. FND-MIR-DEFAULT then deleted the tree lowering:
`native/deferred.rs` keeps only the deferral modes and constants.

The MIR versions are passes over a built body, run before native
lowering. Each writes its result into the body, so the text form shows
it and tests can check it without compiling.

**Loops (`mir/loops.rs`, FND-MIR-LOOPS).**
- Dominators over the normal edges. A back edge's target is a loop
  header; its natural loop is the set of blocks that reach the back edge
  without passing the header.
- Each loop gets a preheader: a block whose only successor is the header,
  inserted when the header has several entries from outside.
- A loop is *counted* when:
  - its header tests `c = i <op> bound` and switches on `c`;
  - `i` is assigned once in the loop, `i = i + k` (or `-`, checked or
    unchecked) with a constant `k > 0`, in a block that every iteration
    runs (it dominates every back edge);
  - the bound's operands are constants, locals the loop does not assign,
    or lengths of such locals.
- Versioning clones a loop's blocks. The preheader then branches on a
  guard to the original or the copy. Both copies share the exits and the
  unwind cleanup.

**Upper-bound facts (FND-MIR-BOUNDS).**
- A forward must-analysis of facts `i < len(v)`. A fact is made on the
  taken edge of a header test against a slice length, and an assignment
  to `i` or `v` kills it. Copies of a local into temporaries carry the
  local's facts while the local is unchanged.
- A slice element call whose index and view carry a fact is marked
  `below`. Native code then keeps only the sign check, as the tree path
  does.
- Status: `mir/bounds.rs` marks the calls (text form `call builtin N
  below(...)`) in `Speed` builds. Unlike the tree path, it also uses the
  tests of `if` branches, not just loop conditions.

**Slice-layout versioning (FND-MIR-SLICE-VERSION).**
- Applies to a small counted loop over `i < v.len()`: a view `v` the loop
  does not assign, and a body under the tree path's budget with no nested
  loop.
- The guard is `v.stride == 8 * width && v.bytes == 0`. The fast copy's
  entry assigns those two words their constant values. That is a no-op
  at run time, but it lets the code generator treat them as constants in
  the loop.
- Status: `mir/slice_layout.rs` versions loops in `Speed` builds. The
  guard is two chained switches, and the copy's entry is a block that
  stores the constants.

**Push shadows (FND-MIR-PUSH-SHADOWS).**
- Applies to vector locals that a loop touches only as
  `v = Vec.push(move v, e)`. The loop records them as shadowed.
- Native code loads the length and capacity once at the preheader. At
  each push in the loop it updates them, and it reloads the capacity
  after a growth, as the tree path does.
- Status: `mir/push_shadows.rs` runs in LLVM `Speed` builds. The
  preheader assigns two `i64` locals from the new `buffer length` and
  `buffer capacity` rvalues. Each push is a
  `call builtin N shadow _len _cap(...)`, which reads and updates those
  locals. The pass prints the tree path's `KUSH_TRACE_SHADOWS` report.
  With this port, only deferred overflow checks still send functions with
  `while` loops to the tree path.

**Deferred overflow (FND-MIR-DEFERRED).**
- The analysis of `native/deferred.rs` moves to the MIR:
  - The expression trees become chains of single-assignment
    temporaries.
  - An operation is *exact*, keeping its immediate check, when its value
    reaches a switch, an index or a counter. That is a backward walk over
    the definitions of the operands.
  - A certified bound is a tree over the definitions of temporaries. The
    leaves are operands that are not certified operations.
- The transform versions the loop into a deferred chunk and the checked
  loop, and emits the chunk's frame as MIR:
  - the sticky word and the leaf magnitude words;
  - the chunk limit and the proof that its accesses are in range;
  - the certificate after the chunk;
  - the replay of the entry state when the certificate fails.
- Deferred arithmetic is an `Rvalue::Deferred` with a mode (exact,
  certified or accumulate) and the sticky local it ORs an exact overflow
  into. The frame's computations are `loop` rvalues: magnitude, chunk
  limit, access ranges, the certificate, and the views that rule a chunk
  out. Accesses the chunk proved in range are `call builtin N proved`.
- `native/deferred.rs` and the tree versions are deleted once the MIR
  passes cover the optimization-shape tests in `tests/llvm_backend.rs`.
- Status: `mir/deferred.rs` runs when `defers_overflow()` holds. It
  passes `tests/deferred_overflow.rs` and the planner's
  `KUSH_TRACE_DEFERRED` reasons in `tests/llvm_backend.rs`.
  - The chunk copy's header tests the counter against the limit directly,
    as the tree path's `chunk_test` does.
  - Deferred loops skip slice-layout versioning: the chunk is already
    specialized to the views' layout.
  - Native code reuses the tree path's helpers: `deferred_i64`,
    `chunk_limit`, `ranges_outside` (split out of `accesses_outside`) and
    `magnitude_bound`.
  - In the chunk copy, proved (unchecked) narrow arithmetic becomes
    wrapping arithmetic. Its proof may rest on a deferred operation whose
    overflow is not reported yet, and narrow values must stay canonical,
    as the tree path ensured inside a deferred loop.

## 9. The evaluator as a word-level machine

FND-MIR-EVAL replaces `eval.rs`, the interpreter over the checked tree,
with a machine that runs MIR bodies (decision 7). The machine is a
word-level model of a native build: values are the words native code
uses, with the same layouts, and the runtime's data structures (buffer
headers, vector blocks, the handler stack) are the ones `runtime/kush.c`
keeps. A program therefore has one meaning, defined by its MIR, and the
evaluator is a checked model of what native code does with it.

**Memory.**
- Memory is a set of allocations, each a byte array. Heap allocations
  come from the runtime's allocation functions; a stack allocation holds
  the locals of a frame whose address is taken (native's pinned locals).
- A pointer is a word `(allocation + 1) << 32 | offset`. Native code only
  adds offsets to pointers, and the machine does the same.
- Every load and store checks that the allocation is live and that the
  access lies inside it. A failure is an internal error of the machine,
  not a Kush panic: a checked program never does it. This is the check a
  native build cannot make.
- Code pointers are words in their own range (`1 << 62 | function`), so a
  function value is the word native code stores.

**Execution.**
- The call stack is explicit: a frame has its body, its block and
  statement, and its locals' words. A task is its own stack, so a task can
  suspend in the middle of a call and the scheduler can switch to another.
  The machine never recurses on the Rust stack for a Kush call.
- Bodies are built once per function with `mir::build`, without the loop
  passes: those are code-generation choices, not semantics.
- A panic follows the body's `unwind` edges through its cleanup blocks,
  frame by frame, as native unwinding does. At the root it ends the run
  with the panic's diagnostic, keeping today's messages.
- The `allocation-stats` report counts what `kush.c` counts, so the
  evaluator's report and a native build's agree.

**The runtime.** Each builtin the MIR calls (`call builtin N`, `alloc`,
`array`, `runtime`, `task` and the other rvalue groups) gets a Rust
implementation over machine memory, written from the native lowering
(`call_target` and its helpers) and the `kush.c` function it calls.

**Checking it.** Until SWITCH:
- `tests/machine.rs` compared the two evaluators on the examples and on
  targeted programs.
- `KUSH_MACHINE_CHECK=1` ran the machine after every tree evaluation in
  a process. A difference in output, result, panic message or stats was
  an error, so the whole test suite was a differential test.
  `KUSH_MACHINE_REPORT=FILE` listed the constructs the machine stopped at.
- Runs limited by a computation budget were not compared: the two
  evaluators count different steps.

**Plan.** The work lands in steps. Until the last one, the tree evaluator
stays the default, and tests compare the two on every program the machine
covers:

| Node | Scope |
|---|---|
| FND-EVAL-MACHINE | Memory, frames, statements and terminators, scalar arithmetic and checks, records and enums, calls, panics and unwinding, boxes and drops, `print`, the stats report, and a differential test against the tree evaluator |
| FND-EVAL-BUFFERS | `Vec`, `Bytes`, `String`, slices, `str`, runtime-length arrays, views, `Vec.map` |
| FND-EVAL-CALLABLES | Function values, closures and their environments, `dyn` objects, unions and coercions |
| FND-EVAL-EFFECTS | Handlers, aborts, continuations and `multi fn`, tasks, threads, channels |
| FND-EVAL-RUNTIME | Allocators and contexts, arenas, standard I/O, host operations (replayed in check mode) |
| FND-EVAL-HOST | Host calls and the `std.sys` shims run on the machine itself: the host layer moves out of `eval.rs` |
| FND-EVAL-STAGING | `Code.compile` and calls of compiled code: frames that run another program's functions |
| FND-EVAL-SWITCH | `Executable::evaluate` runs the machine; `eval.rs` is deleted |

**Status.** MACHINE, CALLABLES and BUFFERS are done. Buffers have the
layouts of `kush.c`: a `Bytes` or vector handle points at `[length,
capacity, data...]`, and a view is `[data, length, stride, byte flag]`. A
buffer's allocation has the runtime's size class (16-byte classes up to
1024 bytes), so growth that fits the class keeps the allocation, as
`kush_buffer_grow` does. The machine runs 40 examples as the tree does. A
program that uses tasks waits for EFFECTS: the tree and native run its
`main` as a task, which the stats count.

RUNTIME is done. Arenas and user allocators keep `kush.c`'s layouts and
counts; the user's callbacks (allocators, growth hooks, arena strategies)
are nested calls, and a panic in a release callback or a strategy aborts.
In check mode the tree's reads and writes, and its host and `std.sys`
calls, are recorded call by call and replayed to the machine, so effects
that cannot happen twice (a file write, a clock, a process) happen once.
Reads and writes of the standard streams run on the machine itself
through the replayed input and output.

EFFECTS is done; the machine runs 46 examples as the tree does, and only
`Code.compile` (STAGING) is left in the suite.
- Every call is a frame on the stack. A call's return site is a call
  terminator, a statement that called (a `perform`, a `Vec.map`
  callback), or the rest of a builtin, a continuation that takes the
  result and may call again; a site can also catch a panic out of the
  call (a task scope's epilogue). Runtime callbacks (allocators, release
  and growth hooks, arena strategies, unwind cleanups) still run to their
  result inside their operation: their effect rows cannot suspend, and
  the scheduler refuses a switch inside one.
- Handlers, aborts and the continuation stack follow `kush.c`, including
  a function's handler-depth restore on every way out. For continuation
  environments the tree counts each one and `kush.c` the 64 KiB chunks;
  the machine counts as `kush.c`, so check mode does not compare the
  stats of a run that pushes one.
- Tasks, threads and channels follow the tree evaluator's scheduler (its
  FIFO order and its two counted allocations per task, where `kush.c`
  counts three): each task has its own stacks, a blocking operation
  suspends with the rest of its work, and a task's panic is raised at its
  join. In check mode a host call records how often it yielded (a
  descriptor wait polls and yields), and the machine yields as often.

STAGING is done. `Code.compile` returns another program (the program and
its generated functions); the machine keeps each artifact, a frame records
the program whose function it runs, and a code word carries its program
above the function index, so a function value made in compiled code calls
back into it. In check mode the machine now covers every program the
suite runs.

HOST is done. The host calls and the `std.sys` shims live in
`crate::host`, on plain bytes and scalars: an evaluator presents a call's
arguments through `HostArgs` (scalars, borrowed buffers, buffers to fill
and put back, owned buffers a failed call consumes), and both evaluators
call the same code. The standard streams and `kush_sys_wait_ready` stay
with each evaluator: the machine's wait polls for up to 1 ms and suspends
its task in between, as the tree yields. Outside check mode the machine
runs host calls itself (`machine::evaluate_with_host`); in check mode it
still replays the tree's, so their effects happen once.

SWITCH is done: `Executable::evaluate` and its variants (`evaluate.rs`)
run the machine, and `eval.rs`, the differential tests and check mode are
gone. Compile-time generators (`#[staged]`) run on it too, in a generation
mode: no runtime compilation, and an allocation budget (1024 live
allocations or 64 MiB with arena chunks) checked between steps and before
an arena chunk is made. `evaluate_with_alloc_budget` bounds fallible
allocation attempts as the tree did (`Box.try_new`, a growing
`Box.try_reuse` or `Vec.try_reserve`, `Bytes.try_with_capacity`,
`Arena.try_alloc` with a fresh chunk, `Code.compile`). Differences from the
tree: continuation environments count as `kush.c` counts them (64 KiB
chunks, not one per environment), and there is no call-depth limit (the
tree stopped at 128 nested calls; the machine's stacks are explicit).

## 10. LLVM from the MIR (FND-LLVM-DIRECT)

**Today.** The native lowering (`Generator` in `native.rs` and
`native/from_mir.rs`, about 10,000 lines) builds Cranelift IR: about 800
instruction calls over some 70 operations, plus blocks, variables, stack
slots and signatures. The LLVM backend (`native/llvm.rs`) translates the
finished Cranelift IR into textual LLVM IR. It sees untyped words: pointer
provenance is rebuilt from how values are used, and aliasing facts reach it
only through a side channel (the memory class carried as a source location,
and the exclusive-pointer parameters it infers).

**Decision 8: one lowering behind an instruction-builder trait.** The
lowering is written once, against a trait `Emit` with two implementations:
Cranelift's `FunctionBuilder`, and a builder that writes typed LLVM IR as it
goes. Nothing is lowered twice, and the translator is deleted at the end.
(The alternative, a second MIR-to-LLVM emitter, would lower every builtin
twice: the duplication FND-EVAL just removed from the evaluator.)

**The trait.**
- The handles are Cranelift's entity types (`ir::Value`, `ir::Block`,
  `Variable`, `ir::StackSlot`, `ir::FuncRef`, `ir::SigRef`,
  `ir::GlobalValue`, `ir::Inst`): plain indices an implementation numbers
  as it likes, so the lowering keeps its types and only its builder is
  generic. Value types are Cranelift's `ir::Type` (the integer, float and
  vector types the lowering uses).
- One method per operation the lowering uses, with Cranelift's names and
  argument order (`iadd`, `icmp_imm_s`, `load`, `brif`, `call`, ...), so
  migrating a call site is mechanical: `self.builder.ins().iadd(a, b)`
  becomes `self.e.iadd(a, b)`.
- Block and variable management (`create_block`, `switch_to_block`,
  `append_block_param`, `block_params`, `declare_var`, `def_var`,
  `use_var`, `seal_all_blocks`), stack slots, and function and data
  references.
- Facts the Cranelift builder ignores and the LLVM builder uses: a value's
  pointer provenance where the lowering knows it (an address of a MIR place,
  a handle the runtime returns), a load's or store's memory class, and a
  function's exclusive (`&mut`) pointer parameters from its MIR signature.

**The LLVM builder.** Every value has its LLVM type when it is made; a value
that is an address is kept as a `ptr` (`getelementptr` for offsets), so
LLVM sees real pointers without reconstructing them. `&mut` parameters are
`noalias`; memory classes become alias scopes, as the translator does now.
Block parameters become `phi` nodes; variables are SSA-renamed as Cranelift's
builder does (or lowered to `alloca` and left to `mem2reg`).

*As built (FND-LLVM-BUILDER).* `native/llvm_builder.rs` writes the text as
the lowering calls it. Variables are SSA-renamed as Cranelift's builder does
it (FND-LLVM-FACTS; `alloca`s left to `mem2reg` first, which ordered loop phis
differently and cost 7% in a vectorized loop). A value's pointer form is
rebuilt at each access the way the translator does it: `base + offset`
becomes a `getelementptr`. `native/builder.rs` is an enum over the two
builders, so `Generator` is instantiated once and
`CodeModule::function_builder` picks the backend per function. A staging
recipe still builds with Cranelift (the staging runtime copies its machine
code) and goes through the translator; `KUSH_LLVM_TRANSLATE` selects the
translator for every function, for comparison.

**Steps.**

| Node | Scope | Done when |
|---|---|---|
| FND-LLVM-EMIT | The `Emit` trait and its Cranelift implementation; `Generator` and the helper builders call it (still Cranelift-only) | the suite passes, the generated code is unchanged |
| FND-LLVM-GENERIC | `Generator` and the helpers generic over `Emit` (handles as associated types) | the suite passes |
| FND-LLVM-BUILDER | The typed LLVM builder; `--backend llvm` uses it, the translator stays for comparison | both backends pass the suite and check-reference |
| FND-LLVM-FACTS | Pointer provenance, `noalias` and alias scopes from the MIR | LLVM benchmarks at least as fast as with the translator |
| FND-LLVM-SWITCH | The translator (`llvm.rs`'s Cranelift reader) is deleted | the suite passes; benchmarks recorded |
