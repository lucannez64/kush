# One handler model: declared operations as implicit capabilities

Status: **accepted** (FND-HANDLERS-ONE; decisions D1-D4 taken by the user
on 2026-11-27, section 8). Decided direction:
[foundations-review.md](foundations-review.md) section 3, E4: lexical
capabilities are the one handler model, and a declared effect becomes an
implicit capability parameter. The plan node asks that existing programs keep
the handlers they observe; section 4 lists the three places where they would
not, and section 8 the decisions taken for them.

## 1. Today

A `perform` finds its handler in one of five ways:

| Mechanism | Lookup | Where |
| --- | --- | --- |
| Lexical `handle Op` (any operation) | innermost enclosing `handle` in the same function, statically | checker |
| Declared `effect Op`, perform in a called function | innermost frame for `Op` on the per-task dynamic stack (`DynamicPerform`, `kush_handler_lookup`) | runtime search |
| Explicit capability `cap Op` / `perform op(x)` | the activation the capability names: a code pointer, or a trampoline into its dynamic frame for capturing handlers | static |
| Multishot across calls, `cap multi Op` | the activation's frame on the continuation stack | static |
| Abortive `effect F: P -> Never`, perform in a called function | innermost dynamic frame for `F`; the abort word then addresses that activation | runtime search |

Around the dynamic stack sit rules of its own: a function snapshots the
stack depth on entry and restores it on every exit; a resumed one-shot
continuation runs under a *redirect* frame that hides frames the handler
pushed around `resume`; a spawned task inherits the innermost contiguous
run of copyable noncapturing frames; a consumed `once` frame still stops the
search. The machinery is `HandlerPush`, `HandlerPop`, `HandlerDepth`,
`HandlerRestore`, `HandlerRedirect` and `DynamicPerform` in the executable IR
and the MIR, nine `kush_handler_*` functions in `runtime/kush.c`, a handler
vector in the MIR evaluator, and resumable entries keyed by operation
(`EntryKey::Operation`) next to those keyed by capability
(`EntryKey::Capability`).

Declared operations are rare in programs (13 declarations: the Game Boy core,
`examples/tactics`, `examples/multishot.kush` and `benchmarks/effects`) and
common in tests (about 170).

## 2. The model

Every `handle` activation is a capability. A function that may perform a
declared operation receives that operation's capability from its caller, as
a parameter the program does not write.

1. **Implicit parameters.** For each declared operation `Op` in a function's
   row (written, inferred, or instantiated for a row variable), the function
   takes a hidden parameter of type `cap Op ! {h}`, where `h` is the row
   declared on the operation (`effect Op: P -> R ! {h}`). Hidden parameters
   follow the written ones, in operation-id order. A row without declared
   operations adds nothing, so most functions are unchanged.
2. **Perform by name.** `perform Op(x)` uses the innermost `handle Op`
   enclosing it in the same function, else the hidden parameter. Lexical
   first, as today.
3. **Calls.** A call passes, for each declared operation of the callee's
   row, the caller's current capability for it, chosen by rule 2 at the call
   site. Rows already require this to exist: a callee whose row has `Op` can
   only be called where `Op` is in the caller's row or discharged by an
   enclosing `handle Op`.
4. **Function values, closures, trait methods.** An arrow type's row decides
   its hidden parameters, and the caller supplies them at each call. A value
   is never bound to a handler when it is created (call-time binding;
   decision D1). Using a function with fewer declared operations where the
   arrow type allows more goes through an adapter that drops the extra
   capabilities, like the existing row and union adapters.
5. **Row variables.** Effect-polymorphic functions are already specialized
   per instantiated row, so `apply<e>` specialized at `e = {Op}` takes `Op`'s
   capability and passes it to its argument.
6. **Handlers** run with the capabilities of their `handle` site (a
   declared operation's handler is pure today, so this concerns lexical
   handlers whose rows name declared operations; today they are already kept
   out of the in-place path so that they do not see the body's handlers).
7. **Continuations** hold capabilities like any other live value. Resumed
   code therefore performs through the capabilities it had at the perform
   point, and frames the handler installs around `resume` are not visible to
   it (decision D2).
8. **Builtins that call back** (vector callbacks, `Task.scope`,
   `Task.spawn`, `Task.catch`) receive an adapter closure that holds the
   call site's capabilities for the callback's declared operations. The
   builtin calls it within its own extent, so this is the same as binding at
   the call. Thread bodies already may not have declared operations.
9. **Tasks.** A spawned task gets each capability whose handler is copyable
   and noncapturing; any other operation in its row gets a capability that
   panics when performed (decision D3).
10. **Entry points** (`main`, exported and test functions) have no caller to
    supply capabilities: a declared operation in their row is a compile error
    (decision D4).

The explicit surface stays as it is: `handle Op as op`, `cap Op ! {e}` and
`perform op(x)` are the same capabilities, named. A handler with effects
beyond the operation's declared row stays capability-only (`as op`, no
implicit discharge), for the same reason as today: an implicit capability's
type is fixed by the declaration.

## 3. Why observed handlers stay the same

Today a perform of `Op` in function `f` finds the innermost active frame for
`Op`, which was pushed by some activation of `handle Op` in a function `g`.
Between `g` and `f` the stack holds calls `g -> f1 -> ... -> f`. Each `fi`
either has `Op` in its row (it calls a function whose row has `Op`) or
discharges `Op` with a `handle Op` around that call, in which case that
`handle` is a newer activation, contradicting innermost. So every function
on the path has `Op` in its row, and under rule 3 each passes the capability
it received, which is the one `g` passed: the same activation. This is the
argument of evidence passing for effect handlers (Xie and Leijen,
"Generalized Evidence Passing for Effect Handlers", ICFP 2021), which Koka
uses to compile dynamically scoped handlers without a search.

The argument needs the path to consist of calls whose rows are checked.
Where it does not, the cases are:

| Case | Today | Model |
| --- | --- | --- |
| function value, closure, trait object | frame active at the call | capability passed at the call (rule 4): same |
| builtin calling back | frame active during the builtin | adapter holding the call site's capabilities (rule 8): same |
| resumed one-shot continuation | redirect hides frames pushed around `resume` | captured capabilities (rule 7): same |
| resumed multishot continuation | frames pushed around `resume` stay visible | captured capabilities: **changes** (D2) |
| spawned task | contiguous run of copyable noncapturing frames | per operation (rule 9): **changes** (D3) |
| consumed `once` frame | second perform panics | same flag in the activation's cell: same |
| capability-only handler (`as op` with effects) | not pushed, does not discharge `Op` | provides no implicit capability: same |
| multishot handler, callee performs by name | rejected | rejected: same |
| no handler at all | run-time panic | compile error at the entry point: **changes** (D4) |

Probes run on 2026-11-26 with the current compiler, evaluator and native
backend agreeing:

| Program | Today | Model |
| --- | --- | --- |
| `f: fn(i64) -> i64 ! {Ask}` passed to a function that installs its own `handle Ask` and calls `f` | the callee's handler (101001) | same |
| a lexical handler re-handles `Tag` around a one-shot `resume`; the resumed code calls a function performing `Tag` | outer `Tag` (15) | same |
| the same with a multishot `resume` | the `Tag` installed around `resume` (25) | outer `Tag` (15) |
| a task performs `Ask` (copyable handler) under a capturing `Log` handler | panic: the `Log` frame is a barrier | `Ask`'s handler (11) |
| `main` with `Ask` in its row performs it | run-time panic | compile error |
| a multishot handle whose body calls a function performing `Ask` by name | rejected | rejected |

## 4. What changes

- **D2, multishot.** One-shot resumption already hides frames the handler
  pushed, and the suite pins that as the intended deep semantics
  (`review_resumed_code_does_not_see_frames_the_handler_pushed`: resumed code
  is handled "exactly as when the performs are written lexically").
  Multishot resumption is the listed exception in effect-handlers.md
  ("frames a multishot handler installs around its `resume` calls remain
  visible to the resumed code"). Under the model it follows the one-shot
  rule. No test found pins the multishot behaviour.
- **D3, tasks.** Only programs that panic today change: a task now performs
  an operation whose handler is inheritable even when an unrelated capturing
  handler was installed inside it. Keeping the contiguous-run rule exactly
  would need the order of all active activations at the spawn, which is the
  stack this design removes. FND-TASKS-ON-HANDLERS (E5) moves tasks onto
  handlers later and may revisit the rule.
- **D4, missing handlers.** A program whose `main` (or exported or test
  function) has a declared operation in its row is rejected instead of
  panicking when it performs. Run-time "no active handler" panics remain only
  for a consumed `once` handler performed twice and for a task performing an
  operation it did not inherit.

## 5. Representation

- **Capability value:** the address of the activation's handler cell, a
  stack slot of the function containing the `handle`: code pointer,
  environment, flags (one-shot consumed, reusable copy, kind). This is
  today's dynamic frame without the operation id, and today's abort payload
  buffer is the same slot, so the abort word (the activation's address) is
  unchanged. A capability is still second-class (section 3.2 of
  effect-capabilities.md): it is passed and forwarded, never stored, and
  continuations that hold it run nested inside the activation's region (the
  E-CPS-BORROW argument), so no cell is read after its activation ends.
- **Perform:** load the code and environment from the cell and call; for a
  consumed `once` cell, panic. A tail-resumptive noncapturing handler costs
  one load more than today's bare-code-pointer capability. EFF-CAP-PERF
  measured a capability perform in a called function at 4.5 to 4.7 ns
  against 6.7 to 7.3 ns for the dynamic lookup it replaces.
- **Alternative not chosen:** one hidden pointer to an evidence vector
  (Koka's representation) instead of one parameter per operation. It costs a
  copy of up to twelve words per `handle` and an indexed load per perform,
  and its resumable entries would be keyed by vector slot. Per-operation
  parameters reuse the existing `cap` parameter path unchanged, and real rows
  are small (the Game Boy core has three operations).

## 6. Lowering

- The checker resolves every by-name perform and every call to a capability
  operand (rule 2 and rule 3) instead of producing `DynamicPerform`; hidden
  parameters are recorded in `Function::capability_parameters` like written
  `cap` parameters, after row inference has settled.
- Resumable entries keep only `EntryKey::Capability(slot)`: an await point of
  a declared operation under a non-tail handler is an await point of the
  callee's capability parameter, which EFF-CAP-RESUME-CALLS already builds.
  `suspend::performs` (the per-operation coloring) is replaced by the
  existing `capability_performs`.
- Abortive performs address the capability's activation directly; the
  `AbortCall` wrapping and the abort word are unchanged.
- Removed: the dynamic stack (`HandlerPush`, `HandlerPop`, `HandlerDepth`,
  `HandlerRestore`, `HandlerRedirect`, `DynamicPerform` in the executable IR
  and the MIR), the `kush_handler_*` runtime functions and per-task frame
  arrays, the evaluator's handler vector, depth snapshots in function
  epilogues, the capturing-capability trampoline (`capability_thunk`) and
  the private operation ids. Task spawn copies the inheritable capabilities
  instead of a stack suffix.

## 7. Steps

| Node | Scope | Done when |
| --- | --- | --- |
| HANDLERS-ONE-PARAMS | hidden capability parameters for direct calls of named functions; by-name performs through them; resumable entries keyed by capability only | suite passes on both backends and the evaluator with the dynamic stack still present but unused for direct calls |
| HANDLERS-ONE-VALUES | function values, closures, trait objects, row-variable specializations, widening adapters | suite passes; probes of section 3 give the "Model" column |
| HANDLERS-ONE-BUILTINS | callback builtins, `Task.scope`/`spawn`/`catch`, task inheritance (D3), entry-point rule (D4) | suite passes; task and entry tests updated |
| HANDLERS-ONE-ABORT | abortive performs through capabilities | abortive tests pass with allocation balance |
| HANDLERS-ONE-DELETE | remove the dynamic stack from IR, MIR, runtime and evaluator; multishot rule (D2); docs/reference chapter 7 | suite and check-reference pass; `benchmarks/effects` and the Game Boy frame time no slower |

### As built: HANDLERS-ONE-PARAMS

`crate::suspend::implicit` runs first in `suspend::lower`, after ownership
and grades. It does not change the checker: it works on the checked IR.

- A function that may perform declared resumptive operations it does not
  handle (the `performs` analysis) gets a copy, `f::capabilities`, that takes
  one more parameter per such operation, after the written ones in
  operation-id order. The copy receives them past its locals through
  `parameter_slots` and lists them in `capability_parameters`.
- In a copy, a `DynamicPerform` with no enclosing `HandlerPush` of its
  operation becomes a call through the parameter.
- A direct call of such a function under a `handle` of one of its
  operations, or from a copy, calls the copy. Per operation it passes the
  innermost enclosing handler when that is a noncapturing `fn` with the
  operation's arrow, the caller's own parameter, or else a trampoline that
  performs through the dynamic stack (capturing handlers stay in their
  frames until HANDLERS-ONE-DELETE).
- An await point under a handler with code after `resume` resumes the copy
  through `EntryKey::Capability` when the copy performs through that
  parameter; otherwise (it reaches the operation only through a function
  value) it stays keyed by the operation, which keeps the existing
  rejection.
- Function values, trait objects, tasks and entry points still call the
  original function, which performs through the dynamic stack
  (HANDLERS-ONE-VALUES and -BUILTINS).

### As built: HANDLERS-ONE-VALUES

- An arrow type whose row names declared resumptive operations takes their
  capabilities after its written parameters. A function value of that type
  (named function, lambda, closure or adapter) is a copy keyed by the
  function and those operations, and every `CallIndirect` passes them like a
  direct call. Lambdas and closures are copied like named functions, through
  `parameter_slots`.
- The checker treats a different set of declared resumptive operations in two
  arrows as a representation change (`arrow_rep_change`), so widening goes
  through the existing pure, once and closure adapters. A `fn` value of
  unknown origin has no environment for an adapter and is rejected, like
  other representation-changing conversions of dynamic pure function values
  (reference chapter 7).
- Arrows whose set of operations reaches code that calls values without
  capabilities keep the dynamic stack: handler values, `Task.scope`,
  `Task.spawn` and vector callbacks, builtin and foreign arguments, and
  values of functions with a special parameter layout. They move in
  HANDLERS-ONE-BUILTINS.
- Trait objects and closed-world union calls dispatch with direct calls of
  their members, so each member of a key becomes a copy taking the union of
  the members' operations, and the dispatch passes them. A member that
  performs operations but cannot be copied keeps that dispatch on the
  dynamic stack.

### As built: HANDLERS-ONE-BUILTINS (in progress)

- D4: `main` with a declared operation in its row is rejected. Test entry
  points were already covered (the generated `main` has the fixed row
  `{io, alloc, suspend}`), and exported functions must have the empty row.
- Task bodies: the checker requires a written lambda for `Task.scope`,
  `Task.catch` and `Task.spawn`, so no adapter closure is needed. The lambda
  becomes a copy that receives its row's capabilities as closure captures
  after its own, supplied where the builtin is called, and the builtin
  receives it at a clone of its arrow without capability parameters. A
  function that spawns such a task needs the capabilities too
  (`performs_with(.., true)`). A spawned task keeps a noncapturing handler's
  capability even under a capturing handler (D3); a capturing handler is
  passed as the trampoline, which finds no frame in the new task.
- Still on the dynamic stack: `VecMap` callbacks (copyable `fn` values with
  no environment, called by the map loops), function arguments of other
  builtins, and handler values whose rows name declared operations
  (rule 6).

## 8. Decisions (user, 2026-11-27)

- **D1. A function value gets its handler at the call.** It is today's
  behaviour and what an implicit capability parameter means; binding at
  closure creation would store a frame address in a closure and needs closure
  lifetimes (FND-REF-DESIGN). Explicit `as op` capabilities cover the cases
  that want lexical capture.
- **D2. Multishot resumed code stops seeing handlers installed around
  `resume`**, as one-shot already does. This removes the documented exception
  and the redirect-like mechanism it would need.
- **D3. Tasks inherit per operation**: a task may use a handler when that
  handler can be shared with it. Only programs that panic today change.
- **D4. A declared operation in an entry point's row is a compile error.**
  Nothing can handle it, so the run-time panic becomes a static check.
