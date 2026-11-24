# Foundations review (2026-11-24)

Status: **accepted**. The user asked for every finding below to be addressed.
The work is the `FND-*` nodes in `plan/plan.json`. Decisions marked *open* need
the user's answer before their implementation nodes start.

The review read the spec, status, roadmap, research, borrow, grade, function
and effect documents, read the compiler, and ran small probe programs against
the release compiler. Every memory-safety probe (dangling slice returns,
aliased `&mut`, moving a borrowed box, borrows escaping a block, consuming
match guards) was rejected, so the checked core is conservative. The problems
below are about structure and expressiveness, and each grows with every new
feature.

## 1. One reference type with lifetimes in types

Today `Type` has six reference forms: `Slice`, `SliceMut`, `Str`, `StrMut`,
`Ref`, `RefMut` (`crates/kush/src/executable.rs`, `enum Type`). Lifetimes live
in side tables (`reference_labels`, per-function `parameter_lifetimes`), not in
the type. Every position that may hold a reference (tuple, generic argument,
enum payload, closure, task, arrow) is therefore enabled one at a time, and
about 460 diagnostics mark positions that are not yet enabled. Probes:

```text
let t = (r, 2);            // "tuples cannot store references"
pick::<&str>(s.as_str())   // "cannot be passed through an ordinary generic type parameter"
```

Change: one type constructor `&'a T` / `&'a mut T`, where `T` may be `[E]` or
`str`, with lifetime variables as ordinary type parameters. Borrow checking runs
as a region/loan dataflow over a control-flow-graph IR (section 8) instead of
the capability-ancestry walk in `ownership.rs`. The per-position rejections are
then deleted rather than lifted one by one. The checked behavior in
[borrow-model-contract.md](borrow-model-contract.md) stays the acceptance test.

## 2. Reusable capturing closures

`fn(...)` cannot capture and `once fn(...)` can be called once, so
`map(v, fn(x) { x + k })` is rejected even when `k` is an `i64`
([functions.md](functions.md)). Change: a callable kind that may be called many
times. First with copied copyable captures (no new borrow rules), then with
borrowed captures bounded by a lifetime once section 1 lands.

## 3. Effects: fewer mechanisms, less noise

- Every function must spell a row, private helpers included. Of 1,967
  signatures in examples and std, 1,028 contain `panic` and 745 are `! {}`.
- `#[noalloc]` / `#[nosuspend]` only check the function's own row, which a
  row without `alloc` / `suspend` already guarantees ([gpu.md](gpu.md)).
- A perform finds its handler through lexical `handle`, the dynamic stack of a
  declared `effect`, a `cap` capability, a multishot token, or an abortive
  handler; tasks are a separate stackful scheduler and `suspend` is not a
  handler.

Decisions (user, 2026-11-24):

- E1: private functions infer their row; public functions still declare it.
  Done (FND-ROWS-INFER): a private free function may omit `! {..}`; methods,
  foreign, exported, staged and `#[gpu]` functions and functions with effect
  parameters still declare theirs. FND-EFFECT-ROWS dropped the written rows
  of 646 private functions in std and the examples (`main` keeps its row).
- E2: `panic` is no longer an effect; any function may panic. Done
  (FND-ROWS-PANIC): naming `panic` in a row is an error, every call tests
  for an unwinding panic, a panic in an allocator release or arena strategy
  aborts, and a handler whose only failure is a panic is pure, so it is
  dynamically visible.
- E3: `#[noalloc]` and `#[nosuspend]` are removed; the row is the contract.
  Done (FND-ROWS-ATTRS).
- E4: lexical capabilities are the one handler model; a declared effect becomes
  an implicit capability parameter.
- E5: tasks (`Task.scope`, `spawn`, `yield`, `join`, `cancel`) move to std on
  top of handlers, and `suspend` becomes a handled effect.

## 4. One proof story, one trust base

The dependent kernel (`Eq`, `J`, `Prop`, `total fn`) is used by showcase
examples only. std relies on `erased q: { ... }` linear-arithmetic facts
(137 uses), discharged by `facts.rs` with its own certificate checker. Spec
section 5.2 says certificates are checked by the trusted kernel, which is not
what happens. Runtime indices in the kernel admit only `i64`, `Bool`, `Unit`.

Decision P1 (user, 2026-11-24): option P-A of
[proof-systems.md](proof-systems.md). Refinement facts stay the everyday
surface and the kernel goes behind them, in stages: name both trusted checkers
now; integers in the kernel and translation of `{ ... }` propositions; kernel
lemmas cited where the solver fails; certificates checked by the kernel.

## 5. Grades and linearity

Grades on copyable values (`x: i64 @[2]`), grade algebras, the grade solver,
grade-zero erasure and effect demand have no use in std, the Game Boy, JSON or
OTP code. Linearity is spelled three ways: `#[linear]` types, `@[1]` on owners,
`linear once fn`. Decision G1 (user, 2026-11-24): option G-B of
[grades-assessment.md](grades-assessment.md), later. Grades are upgraded to
graded modal types (order and subgrading, grades in types, grades on results,
infinite carriers) after the reference and inference work, and DP-GRADES builds
on that. Until then the current exact-count grades stay as they are. G2: the
single linearity spelling is chosen in the graded-modal design, since `@[1]`
may remain the spelling.

## 6. Inference

Expected types do not reach call arguments and generic arguments are not
inferred from reference arguments:

```text
let v: Vec<i64> = Vec.push(Vec.new(), 7);   // "cannot infer the element type"
pick(s.as_str())                            // "cannot infer type parameter 'T'"
```

Change: bidirectional checking with unification variables for generic
arguments, so expected types propagate into arguments and constructors.

## 7. Standard library shape

- `v.push(3)` resolves to the consuming `Vec.push(v, x) -> Vec`, so it moves
  `v` ("cannot borrow a moved owner"); code writes `v = v.push(x)`.
- `std.text` works on `&Bytes`, not `String` / `&str`; `==` on strings is
  rejected.
- Errors are `Result<_, i64>` codes.

Change: `&mut self` collection methods as the method-syntax default, a text API
on `&str`, string equality, typed error enums.

## 8. Compiler structure

- `executable.rs` was 42k lines and `expr_expected_unchecked` alone 2,411
  (FND-SPLIT-EXEC: now 6.8k lines plus 33 modules under `executable/`, and
  about 1,000 lines for the expression checker).
- Each feature is implemented in the reference evaluator and in native
  lowering.
- The LLVM backend translates Cranelift IR, so it never sees types or aliasing.
- The 4,400-line C runtime was a string literal in `native.rs` (now
  `crates/kush/runtime/kush.c`, FND-RUNTIME-C).

Change: split the checker into modules; add a typed CFG IR between checking and
code generation that the borrow checker, evaluator and both backends consume;
emit LLVM from that IR; move the runtime into its own `.c` file.

## 9. Documentation

There are 95 documents, mostly milestone logs with test counts and remote-gate
notes. `spec-v0.1.md` predates handlers, tasks, traits and staging;
`effect-capabilities.md` still says nothing is implemented. Change: one current
language reference; milestone history moved out of the design documents.

## 10. Order of work

Open feature nodes (GPU, web, session types, JIT, differential-privacy grades,
semver contracts) add more positions to the special cases of sections 1 and 2.
Nodes whose design depends on a pending decision now depend on that decision.
The foundation order is: split the checker and add the CFG IR, uniform
references and the new borrow checker, reusable closures, inference, then the
effect/grade/proof simplifications and the std API.
