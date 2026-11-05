# Handled bodies as resumable state machines (design)

Status: **implemented** for lexical performs (E-CPS-IR through E-CONTROL).
Sections 1-13 are the design as written for E-CPS-DESIGN; section 14
describes what was built and where it departs from the design, and why.
The handler fragment is described in [effect handlers](effect-handlers.md).

## 1. Where we start

Today a handled body supports:

- a **tail** `perform`, lowered to an identity resumption token with no
  allocation;
- exactly **one non-tail** `perform`, which must be the whole value of a
  top-level statement. The rest of the body is re-checked from source as a
  `linear once fn(R) -> R` closure (`resumption_continuation` in
  `executable.rs`). It captures every local the suffix *mentions*, by value,
  and rejects mutable, borrowed, reference, task and `@[0]` captures;
- **dynamic** performs in called functions, which are tail-resumptive only:
  `resume` is the identity on the operation result.

What cannot be expressed: a second `perform`, a `perform` inside an expression,
a loop, or a branch, `return`/`?` across a resumption, and non-tail resumption
of a callee's perform.

The closure trick does not generalise. A continuation for a perform inside a
loop must contain "the rest of this iteration, then the loop again, then the
rest of the body"; that is not a source suffix. A second perform needs a
continuation inside a continuation. The fix is to stop building continuations
from source and instead compile the handled body once, as a **resumable state
machine**: a heap frame that holds the values live across suspension points,
plus a step function that runs from one suspension point to the next.

## 2. Decision: explicit state machines, not stack segments

Two strategies were compared (the research note in
[research actions](research-actions.md) asks for this comparison).

**Stack segments** ([Retrofitting Effect Handlers onto OCaml, PLDI 2021](https://arxiv.org/abs/2104.00250)).
Run each handled body on its own stack segment; a `perform` switches back to
the parent segment, and `resume` switches in again. The native runtime already
has stackful coroutines (`ucontext`) for tasks, so the mechanism exists.

**Explicit state machines** (selective CPS of the handled body, in the style of
C#/Rust generators). The compiler computes the live set at every suspension
point, stores it in a frame, and emits a step function with one entry state
per resumption point.

| Concern | Stack segments | State machines |
| --- | --- | --- |
| Reference evaluator | Needs a thread or its own CPS per continuation; parity with native is a second implementation | Same checked IR runs in both backends |
| Ownership of values held by a suspended continuation | Invisible to the checker (they are machine stack slots); cleanup of an abandoned continuation needs unwinding, which Kush does not have (panic aborts) | Every held value is a typed frame slot; the ownership pass checks moves into and out of the frame, and each state has an exact drop list |
| Multishot | Requires copying a stack that may contain interior pointers (pinned locals, borrows); OCaml forbids it in the core for this reason | Copy the frame when every slot is copyable; reject otherwise |
| Memory per handle | One stack segment; fixed size with a guard page, or relocatable stacks, which Cranelift and C frames cannot support | One frame sized by the live set (often a few words) |
| Borrows held across a perform | Raw stack addresses; validity depends on the segment never moving | Rejected at first (section 6); a later relaxation is a checked rule |
| Dynamic resumption across arbitrary calls | Free: any frame on the segment is captured | Needs effectful callees to be compiled as resumable ("coloring", section 9) |
| Rust/C frames between perform and handler | Would be captured and resumed; unsound for C code that is not reentrant | Cannot happen: a C frame is never part of a frame chain |
| Cancellation of tasks | A suspended segment pins a task stack until resumed | Unaffected: a frame is ordinary heap data owned by a token |

**Decision.** Use explicit state machines for the whole E-CPS chain and for
dynamic resumption (E-CALLEE-COLOR, E-DYN-RESUME). The only real advantage of
stack segments is dynamic resumption without coloring; Kush rows already mark
exactly which functions can perform a declared operation, so coloring is
static and cheap to compute. If E-PERF shows that colored callees cost too
much, stack segments may be revisited as a native-only fast path for one-shot
dynamic resumption, but only behind the same checked semantics.

## 3. Semantics that the state machine must preserve

The state machine changes the implementation, not the meaning:

- **Deep handlers.** `resume(x)` runs the rest of the handled body until it
  finishes, including any later performs, which call the handler again
  *inside* that `resume`. The value of `resume(x)` is the body's final result.
  This matches today's non-tail behaviour.
- **One-shot by default.** The token is `linear once fn(R) -> R ! {}`; a
  multishot `fn(R) -> R` token remains available only when the frame is
  copyable (E-MULTISHOT-COPY).
- **Evaluation order.** Operands are evaluated left to right; a perform inside
  an expression suspends after the operands to its left have been evaluated
  and before those to its right.
- **Effects.** The continuation's effects are the body's effects and are
  required at the `handle` site, as today.
- **Tail fast path.** A body whose only performs are in tail position keeps the
  identity token and allocates nothing (E-CPS-PARITY).

## 4. Pipeline

```text
check (types, rows)            -- unchanged surface; performs anywhere in the body
  -> ANF of handled bodies     -- E-EXPR: every perform becomes `let t = perform Op(v);`
  -> Suspendable IR node       -- E-CPS-IR: the checked body plus its suspension points
  -> ownership + grades        -- checks the body *as written*, with suspension rules
  -> suspension liveness       -- E-CPS-LIVENESS: live set and frame layout per point
  -> state-machine lowering    -- E-CPS-FRAME: frame type, step function, drop glue
  -> eval / native             -- E-CPS-EVAL / E-CPS-NATIVE: four small primitives
```

The key choice is **check first, lower after**, as with closure conversion.
The ownership and grade passes see the body in its natural structured form,
where moves, loans and last uses are already well understood. They add one
rule at each suspension point (section 6). The lowering then runs on checked
IR and is trusted to preserve what was checked; it is covered by parity and
cleanup tests in both backends, not by re-running the checker on generated
code. Re-checking a generated `loop { match state { .. } }` would need
partially initialized records and flow-sensitive slot liveness, which the
checker does not model.

## 5. IR

### 5.1 Before lowering (E-CPS-IR)

```rust
/// A handled body that can suspend. Produced by the checker for every
/// `handle` whose body contains a non-tail perform of its operation.
ExprKind::Suspendable {
    operation: usize,        // the handled operation
    handler: usize,          // hidden local holding the handler value
    body: Block,             // checked body; performs appear as Suspend
    result: Type,            // body result = operation result type R
    multishot: bool,         // handler asked for the copyable token
}

/// One suspension point inside a Suspendable body, always in ANF position:
/// the whole value of a `let` or expression statement.
ExprKind::Suspend {
    point: usize,            // index of this suspension point, 1..=n
    payload: Box<Expr>,      // already coerced to the handler parameter type
}
```

`Suspend` has the operation result type. The ANF pass (E-EXPR) guarantees that
every `Suspend` is a statement value. A `Suspend` may sit inside `if`, `match`
arms and loop bodies; it may not sit inside a lambda (a lambda is a separate
function, and its performs go through the dynamic stack or its own handle).

### 5.2 After lowering (E-CPS-FRAME)

The lowering replaces a `Suspendable` by:

1. a **frame type**: a compiler-generated nominal record
   `Frame#k { state: i64, s0: T0, s1: T1, ... }`;
2. a **step function** `step#k(frame: &mut Frame#k, input: R) -> Step#k`,
   where `Step#k` is `Yield(P) | Done(R)` and `P` is the handler parameter type;
3. **drop glue** `drop#k(frame)` that drops exactly the slots initialized in
   the frame's current state;
4. at the `handle` site, a driver (section 7).

Four primitives are added to both backends; everything else is existing IR
(`Loop`, `Match` on an integer, `Project`, assignment, `Return`):

| Primitive | Meaning |
| --- | --- |
| `FrameNew(k)` | Allocate an uninitialized `Frame#k` with `state = 0`; charged as one allocation |
| `FrameLoad(f, slot)` | Move a slot's value out; the slot becomes uninitialized for drop glue |
| `FrameStore(f, slot, v)` | Move a value into an uninitialized slot |
| `FrameFree(f)` | Release the frame storage; every slot must already be uninitialized |

`FrameLoad`/`FrameStore` are moves, never copies of owned values. Copyable
slots may be read with a plain `Project` when the lowering knows the slot is
not needed again.

## 6. Checking rules at a suspension point

The ownership and grade passes treat `Suspend` as a call that may run arbitrary
handler code, with the following extra rules. All of them are conservative;
section 11 lists the intended relaxations.

1. **Live values move into the frame.** Every local live after the suspension
   point (E-CPS-LIVENESS) is part of the frame. Ownership treats this as "moved
   out and restored". Linear obligations and `@[1]` grades are preserved,
   because the frame is consumed exactly once by a one-shot token. An `@[0]`
   value is erased and occupies no slot.
2. **No live borrow across a suspension.** A slice view, `&str`, reference,
   borrowed record, reference container, borrowed-capture closure, or task
   handle that is live after a suspension point is rejected with a diagnostic
   naming the value and the perform. A loan that ends before the perform is
   fine. Reason: the frame moves the continuation's data to the heap and the
   handler runs in between, so today's loan model (lexical, stack-rooted) does
   not cover it.
3. **Pinned locals.** A local whose address is taken (`pinned`) and that is live
   across a suspension point is rejected, because a reference to it could only
   be live across the suspension too (rule 2), and moving it to the frame would
   change its address. A pinned local whose references all end before the
   perform does not need a frame slot for its address: it is stored by value.
4. **Mutable locals.** `let mut` locals are allowed in the frame; this lifts
   today's restriction. A local the *handler* can write (a scalar captured by
   reference by the handler closure, `apply_handler_writes`) is rejected if it
   is live across the suspension, since the frame would hold a stale copy.
5. **Facts.** Arithmetic facts about frame slots survive a suspension: the
   frame is private to the body and the handler cannot reach it. Facts about
   locals the handler may write are bumped (version change), exactly as after
   a call that writes them. Today's blanket reset inside the continuation
   becomes unnecessary.
6. **Linear operation results.** A linear `R` stays rejected for non-tail
   handlers, as today; the token's result would duplicate the obligation.
7. **Effects.** A suspendable body requires `alloc` for its frame unless the
   frame is empty (section 8.3), and `panic` as today.

## 7. Driving the machine

For `handle Op with h { body }`, with `h: fn(P, linear once fn(R) -> R) -> R`:

```text
f = FrameNew(k)                    -- state 0
drive(f, unit_input) =
    match step#k(&mut f, input) {
        Done(r)  => { FrameFree(f); r }
        Yield(p) => h(p, token(f))  -- token owns f
    }
token(f)(x) = drive(f, x)          -- linear once; consuming it moves f
```

- The token is an ordinary `linear once` closure whose environment is the
  frame, so the existing closure ABI, linearity checking and environment
  drop rules apply unchanged.
- A handler that never resumes is rejected by linearity, so a frame is always
  driven to `Done` and freed there. The drop glue is still generated and used
  by multishot frames (a copy that is never resumed), by E-CONTROL exits, and
  by cancellation of a task that holds an unresumed copyable token.
- **Stack depth.** Deep handlers nest one handler call per perform:
  `drive -> h -> token -> drive -> h -> ...`. A body that performs `n` times
  uses `O(n)` native stack while the handler code after `resume` is pending.
  This is inherent to deep handlers with code after `resume`, and matches
  today's semantics. For the common **tail-resumptive handler**
  (`fn(x, resume) { resume(g(x)) }`), `token` and `drive` are emitted with
  Cranelift's `tail` calling convention so `h -> token -> drive` does not grow
  the stack (Cranelift 0.135 supports `CallConv::Tail` and `return_call`). The
  evaluator implements the same chain with an explicit loop. E-PERF measures
  both and adds a test with at least 10^6 performs in a loop.

## 8. Lowering details (E-CPS-FRAME)

### 8.1 States

State 0 is entry. Each `Suspend { point: i }` gives state `i`: "resume after
point `i`, with the operation result as `input`". The step function is

```text
step#k(f, input) =
    loop {
        match f.state {
            0 => { <code from entry to the first suspension reached> }
            1 => { <bind the perform-1 result from input>; <code to the next suspension> }
            ...
        }
    }
```

Code between suspension points is emitted structurally:

- **Straight-line code and `if`/`match` without a suspension** stay as they
  are, inside one state.
- **A branch that contains a suspension** is split: the code after the branch
  becomes a join state `j`, each arm ends with `f.state = j; continue`, and a
  suspension inside an arm stores live values, sets `f.state = i`, and returns
  `Yield(p)`.
- **A loop that contains a suspension** becomes a head state: the loop
  condition (if any) is evaluated at the head state, the body's tail jumps
  back to it, and `break`/`continue` targeting this loop become state
  transitions (E-CONTROL). Loops without a suspension stay native loops.
- **Locals in states.** A local that is not live across any suspension point is
  an ordinary local of the step function and is never in the frame.

### 8.2 Frame layout

E-CPS-LIVENESS computes, for every suspension point `i`, the set `L(i)` of
locals live after it, using the existing backward analysis in `ownership.rs`
(`block_live`/`expr_live`, currently instantiated for view locals only)
instantiated for all locals, with loop fixed points. A loop head state also
gets the live set at the loop head. The frame has one slot per local in the
union of these sets; slots are not overlapped between states in the first
implementation (overlap by interval colouring is a later size optimization).

Each state `s` has an **initialized-slot set** `I(s)` = the live set at the
point where the machine stops in that state. Drop glue is
`match state { s => drop every owned slot in I(s) }`. Copyable slots have no
drop.

### 8.3 Empty frames

If no local is live across any suspension point, the frame is just the state
word. When there is also exactly one suspension point, the frame is not
needed at all and the existing capture-free continuation (a noncapturing `fn`,
multishot allowed) is kept. This preserves today's allocation behaviour for
capture-free bodies.

### 8.4 Evaluation in the reference evaluator (E-CPS-EVAL)

The evaluator implements the four primitives directly: a frame is a heap value
holding a `Vec<Option<Value>>` plus the state, `FrameLoad` takes the value out
(`None` afterwards), and `FrameFree` asserts every slot is `None`. That
assertion turns a lowering bug into an internal error in tests instead of a
silent leak, which is why the evaluator is the reference.

### 8.5 Native lowering (E-CPS-NATIVE)

The frame is one `kush_alloc` block: the state word followed by the slots at
their usual widths. `FrameLoad`/`FrameStore` are loads/stores at fixed
offsets. The step function is an ordinary Cranelift function; the state switch
is a `br_table`. `drive` and `token` use the `tail` calling convention
(section 7). The frame is freed by `kush_free` in `drive` on `Done`.

## 9. Callee coloring and dynamic resumption

E-CALLEE-COLOR and E-DYN-RESUME extend the same machinery across calls.

- A function whose effect row contains a declared operation `D` is
  **colored for `D`**. Coloring is a fixed point over the call graph using the
  rows that already exist; it needs no new annotation.
- A colored function gets a second, **resumable entry**: its body lowered as a
  state machine whose suspension points are its own performs of `D` *and*
  every call to another colored function (an "await" of the callee's machine).
  The callee's frame is stored in a slot of the caller's frame, so a captured
  continuation is a chain of frames owned by the token.
- The **direct entry** is kept and used whenever the innermost active handler
  for `D` is tail-resumptive, so code under such handlers pays nothing. A
  `handle` with a non-tail handler for `D` calls the resumable entries of
  colored callees in its body.
- **Indirect calls.** A function value whose arrow row contains `D` must also
  be callable resumably. The evaluator knows the target function index. Native
  code maps a direct entry address to its resumable entry through a sorted
  table emitted at link time; an indirect call in resumable code looks it up.
  Values of arrow types without declared operations are unaffected.
- **Tasks.** A task boundary remains an isolation boundary: a non-tail handler
  frame is never inherited by a child task, as capturing frames are today.

## 10. Multishot (E-MULTISHOT-COPY, E-MULTISHOT-DECL)

A multishot token copies the frame (and, for E-MULTISHOT-DECL, the whole frame
chain) before each resumption. It is accepted only when every slot in every
state is copyable. Any owned or linear slot keeps the token one-shot, and
asking for a multishot token is an explicit rejection that names the slot.
Single-shot results are never used to justify multishot safety.

## 11. Intended relaxations, not in the first implementation

- **Borrows of outer storage across a suspension.** The token is a lexical,
  non-escaping capability (it cannot outlive the `handle`), so a view of
  storage owned *outside* the handled body could be held across a perform with
  the handle's extent as its region. This needs the frame slot to carry the
  loan, like a borrowed record field, and the token to be classed as a scoped
  borrowed-capture closure. It is a separate node once the basic machine works.
- **Slot overlap** by liveness interval colouring.
- **Stack-segment fast path** for one-shot dynamic resumption, only if E-PERF
  shows that coloring is too costly.

## 12. Worked example

```rust
effect Ask: i64 -> i64;

fn main() -> i64 ! {alloc, panic} {
    handle Ask: i64 -> i64 with fn(x: i64, resume: linear once fn(i64) -> i64 ! {}) -> i64 ! {} {
        resume(x * 10)
    } {
        let mut total = 0;
        let mut i = 0;
        while i < 3 {
            let a = perform Ask(i);   // point 1, inside a loop
            total = total + a;
            i = i + 1;
        }
        total
    }
}
// 0 + 10 + 20 = 30
```

Live after point 1: `total`, `i` (and the bound result `a`, which is a local
of state 1 only). Frame: `{ state, total: i64, i: i64 }`, all copyable, so a
multishot token would also be allowed. States:

```text
state 0: total = 0; i = 0; f.state = 2; continue
state 2 (loop head): if !(i < 3) { return Done(total) }
         store total, i; f.state = 1; return Yield(i)
state 1: load total, i; a = input; total = total + a; i = i + 1;
         f.state = 2; continue
```

The handler is tail-resumptive, so with `tail` calls the three performs run in
constant native stack.

## 13. Obligations per node

| Node | Delivers | Must test |
| --- | --- | --- |
| E-CPS-IR | `Suspendable`/`Suspend`, produced for every handled body with a non-tail perform; existing single-perform bodies produce them too | Checker output for today's accepted programs is unchanged in behaviour |
| E-CPS-LIVENESS | Live set per suspension point; rules 2–4 of section 6 | Rejections: view, reference, task handle, pinned local, handler-written local live across a perform; acceptance when the loan ends before it |
| E-CPS-FRAME | Frame type, step function, drop glue, driver | Balanced allocations; every owned slot dropped once on every exit state |
| E-CPS-EVAL | Primitives in the evaluator, with the empty-frame assertion | All existing handler tests through the new path |
| E-CPS-NATIVE | Primitives, `br_table` dispatch, `tail` calls | Same tests natively; 10^6 tail-resumptive performs without stack growth |
| E-CPS-PARITY | Old continuation code removed; tail identity and capture-free paths kept | Same tests pass; no allocation for tail and capture-free bodies |
| E-EXPR | ANF of performs in operands, conditions, call arguments, `&&`/`\|\|` | Evaluation order observed through output; short-circuit skipping a perform |
| E-MULTI-PERFORM | Several suspension points, branches and loops | Performs in both arms of an `if`, in a loop, nested loops |
| E-CONTROL | `break`/`continue`/`return`/`?` as state transitions | Early exit drops every live owned slot once; `return` from the enclosing function through a resumption |
| E-CALLEE-COLOR / E-DYN-RESUME | Resumable entries, frame chains, address table | Non-tail handler resumed across two levels of calls; direct entry still used under tail handlers |
| E-MULTISHOT-* | Frame copy | Copyable frames resumed several times; owned slot rejection |

The independent review (E-REVIEW) should in particular try to observe a value
twice or never through a frame: every owned slot must leave the frame exactly
once, through a `FrameLoad`, a drop, or a copy that is itself dropped.

## 14. As built

The pipeline of section 4 is implemented as designed: the checker produces
`ExprKind::Suspendable`/`ExprKind::Suspend`, an ANF step
(`executable/anf.rs`) puts every point in statement position before
ownership, ownership and grades check the structured body (a `Suspend` wraps
the ordinary handler call, so it is checked exactly like one), and
`crate::suspend` lowers it afterwards. Three details differ from sections 5,
7 and 8.

**One frame per suspension point, not one frame per handle.** The frame of a
point is the environment of a `linear once` closure over that point's
continuation function, holding exactly `L(i)`. `FrameNew`/`FrameStore` are the
closure construction (captures are moves), `FrameLoad` is the closure
prologue, `FrameFree` is the existing environment release on call, and the
drop glue is the existing closure drop glue. Reasons:

- the token needs a closure environment anyway (the handler receives an
  ordinary `once fn` value), so a separate persistent frame would cost one
  more allocation per handle, not fewer;
- each environment holds only that point's live set, so there are no
  uninitialized slots, no per-state initialized-slot sets, and no
  "every slot must be empty" assertion to maintain: ownership of every value
  is a move into exactly one environment and a move out of it;
- both backends already run closures, so parity is by construction and the
  only new primitives are `Region`/`RegionExit` (below) and a per-function
  `parameter_slots` map that lets a continuation keep the enclosing
  function's slot numbering;
- a capture-free point is a plain code pointer, so the capture-free and
  multishot-capture-free paths keep allocating nothing.

The cost is one environment allocation per suspension that has live values,
instead of one per handle plus one token environment per suspension.

**Code before the first suspension runs in place.** The handled body stays in
the enclosing function as a `Region`; a point becomes
`RegionExit(handler(payload, token))`, which evaluates the handler call,
drops the region's active resources, pops dynamic handler frames installed
inside the region, and leaves the region with the handler's result. Only the
code after a point lives in continuation functions. This keeps today's
behaviour for code before the perform: writes to outer locals are visible
after the handle, and borrows of outer storage that end before the first
perform need no rule at all. The continuation of point `i` is rebuilt
structurally from the path to the point: the rest of each enclosing block
(earlier `let` slots are re-declared so their lexical cleanup is unchanged),
the taken branch of an `if`/`match`, and for an enclosing loop
`{ let mut first = true; loop { if first { first = false; rest } else
{ [if !cond { break }] body } } }`, so `break`/`continue` keep their targets.
Each continuation body is itself a `Region`.

**Tail-resumptive handlers never suspend.** A handler written as a lambda at
the `handle` whose only use of the token is `resume(e)` in tail position
(through `if`/`match`/blocks/`return`) computes `h(p, k) = k(e)`. Every
perform of such a handler uses the identity token and continues in place,
anywhere in the body (expressions, loops, `return`, `?`), with no allocation
and constant native stack. This replaces the `tail` calling-convention plan of
section 7: there is no handler-to-token-to-driver chain to turn into tail
calls. Non-tail handlers still nest one handler activation per perform, which
is inherent (section 7).

**Checking rules as implemented** (`crate::suspend`, after ownership):

1. `L(i)` is a backward liveness over the checked IR (loops to a fixed
   point), restricted to the handled body; grade-zero locals are erased and
   never captured.
2. A local in `L(i)` whose type holds a borrow (view, text, reference,
   borrowed record, task handle) is rejected. A pinned local whose references
   end before the point is captured by value.
3. A local the handler writes through its capture is rejected if it is in
   `L(i)`.
4. A local of the enclosing function that is not copyable and is in `L(i)` is
   moved into the continuation; it is rejected if the function uses it after
   the `handle`. A continuation that writes a local of the enclosing function
   (assignment or mutable borrow) is rejected if the function reads it after
   the `handle`, because the continuation works on its own copy.
5. A capturing continuation requires `{alloc, panic}` at the handle.
6. `return`, `?`, and `break`/`continue` to a loop outside the body are
   rejected in continuation code (code reachable after a point). They are
   allowed before the first point (they run in place) and anywhere under a
   tail-resumptive handler. Section 13 asked for `return` through a
   resumption; it is not implemented because the handler activation that
   called `resume` is still on the stack and has code after the call, and
   Kush has no unwinding that could abandon it and drop its live values.
7. A non-tail perform inside the body of a nested non-tail handler or a
   nested declared-operation handler is rejected (multi-prompt capture).
