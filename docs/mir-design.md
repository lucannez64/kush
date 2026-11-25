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
- With `KUSH_MIR=1` (or `CodegenOptions::mir`), native code is lowered
  from the MIR for every covered function and from the tree for the rest.
  The leaf operations share the tree path's helpers.

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
- Every builtin call target except staging is a `call builtin N`
  terminator. Native code lowers it through the same `call_target`
  dispatch as the tree path. Each body lists its builtins, and the text
  form prints their definitions as comments. Reading the text back takes
  the table from the program. Printing builtins in full is
  FND-MIR-TEXT-BUILTINS.
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
  named by index in the text form.
- Union patterns test the member tag word, then the member's words.

`multi fn` values, continuations and suspension wait for FND-MIR-EFFECTS.

FND-MIR-BUILTINS finished the ordinary values:

- Recursive enums (through boxes) are covered. The type check treats a
  type it is already checking as covered.
- `?` is a switch on the tag word. The error branch builds the function's
  error variant and returns through the usual cleanup.
- Box reads are two loads through places. A proved byte read is `byte_at`.
  I/O handles are one-word values.

What remains outside the MIR, apart from effects, is listed on
FND-MIR-SHAPES.

The flags are dynamic everywhere, as on the tree path. Removing the ones
a dataflow pass can decide statically is FND-MIR-DROP-FLAGS.

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
