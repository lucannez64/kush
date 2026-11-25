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
