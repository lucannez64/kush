# Proof-directed fuzzing (PROOF-FUZZ)

Status: design approved 2026-11-13 (native engine); implementation in progress.

*Every check is either proved or attacked.* The checker removes a run-time
bounds or overflow check when the facts in scope prove it can never fail
([runtime-indices.md](runtime-indices.md)). Every check it cannot remove stays
in the program as a possible panic. `kush fuzz` takes exactly those checks as
its targets, generates inputs aimed at each one, and reports for every check
whether it was proved, broken (with a minimized reproduction), survived an
attack, or was never reached.

## 0. Where things stand

What exists today, and what this design has to add:

- `KUSH_PROOF_REPORT=1` prints two counts: element accesses proved in bounds
  and accesses checked at run time (`executable.rs`, end of checking).
  `KUSH_PROOF_REPORT=verbose` also prints `file:line:column` of each unproved
  access, but only for accesses into **length-refined** fields
  (`Vec<u8> where len >= N`). An access into a plain `Vec` is counted and not
  listed, and **overflow checks are neither counted nor listed**: when
  `Facts::in_range` fails (OVERFLOW-ELIDE) the operation simply requires
  `panic`.
- Measured on the current tree:

  | example | target | bounds proved | bounds checked | listed by `verbose` |
  |---|---|---|---|---|
  | `examples/gameboy` | `src/main.kush` | 353 | 88 | 0 |
  | `examples/gameboy` | `tests/main.kush` | 106 | 41 | 0 |
  | `examples/kernel` | `src/main.kush` | 0 | 102 | 0 |
  | `examples/kernel` | `tests/main.kush` | 0 | 96 | 0 |

  So the report that the pitch names does not yet list a single target in
  either showcase. Step 1 below fixes that.
- The prover is not an SMT solver. It is Fourier–Motzkin elimination with
  Farkas certificates plus a bounded integer fallback (cuts and branching,
  [integer-refutation.md](integer-refutation.md)). A failed search returns
  "not established", never a model.
- The reference evaluator (`eval.rs`) reports every panic as a `Diagnostic`
  carrying the span of the failing expression: `panic: checked arithmetic
  failed` at the operator, `panic: index out of bounds` at the access. It has
  a per-run step budget (`eval_fuel`) and takes standard input as a
  `&mut dyn Read`. It can therefore run a compiled program many times
  in-process and name exactly which check failed.
- `kush test` discovers `#[test]` functions and appends a generated `main` to
  the in-memory test source (`project/test.rs`); each test runs in its own
  process. There is no property-testing or fuzzing support.
- Preconditions are erased proposition parameters
  (`erased inside: { 0 <= register && register < 0x80 }`); a caller passes `_`
  and the checker must prove the proposition at the call. Results carry
  `ensures`, loops carry `invariant`. There is no `requires` keyword.

## 1. User-facing workflow

```sh
kush fuzz [FILTER] [--manifest-path <Kush.toml>] [--locked]
          [--runs N] [--time SECONDS] [--seed N]
          [--list] [--report] [--save] [--json]
```

`kush fuzz` checks the project, collects every **obligation** (run-time check)
the prover did not discharge, and attacks each one. `FILTER` is a substring of
the qualified function name (`apu.`, `reader.skip`), as in `kush test`. Illustrative output (not a real run):

```text
$ kush fuzz reader
attacking 23 unproved checks in 9 functions of kernel (seed 0)

FOUND  bounds   kernel.reader.skip            src/reader.kush:81:12
       check    0 <= at && at < src.len()
       input    src = b"", at = 0              (minimized from 37 bytes, 214 runs)
       suggest  `erased in_text: { 0 <= at && at <= src.len() }` on skip;
                every caller then has to prove it (3 callers, 2 prove it)
survived  12 checks reached, none failed (closest: index == len - 1)
unreached  2 checks  (src/reader.kush:140:9, :151:17)
no generator  0 checks

result: 1 found, 12 survived, 2 unreached, 8 proved; exit 1
```

Flags:

- `--runs N` (default 2000) is the run budget **per targeted function**;
  `--time SECONDS` caps the whole session. Whichever ends first stops it.
- `--seed N` (default 0) makes a session fully deterministic: same tree, same
  seed, same report. A fuzzer whose CI output changes run to run is not
  useful in a test suite.
- `--list` prints the obligations with their kind, function, location, goal and
  generator status, without running anything (the "what would be attacked"
  view, and what `KUSH_PROOF_REPORT=verbose` becomes).
- `--report` prints the proved-or-attacked table of section 4 after the run.
- `--save` writes each minimized reproduction into the project (section 3).
  Without it `kush fuzz` writes nothing outside `target/kush/fuzz/`.
- `--json` prints one JSON object per obligation, for editors and CI.

Exit status: 0 when nothing was found, 1 when at least one counterexample was
found, 2 for usage or compile errors. This matches `kush test`.

**Why `kush fuzz`.** It is the word users already know (`cargo fuzz`, `go test
-fuzz`), and it sits next to `kush check` and `kush test` as a project
command. The alternatives were `kush attack` (matches the slogan but reads as a
security tool) and `kush test --fuzz` (`kush test` builds one ordinary
binary per test with no inputs; fuzzing needs one instrumented binary run
thousands of times, and a report about obligations, not tests). The
slogan's vocabulary is kept in the output: each check ends up *proved*,
*found*, *survived* or *unreached*.

## 2. How inputs reach each obligation

### 2.1 Making obligations first-class

The checker records an `Obligation` for every check it leaves in place, in a
table on `Executable` next to `bounds_proved`/`bounds_checked`:

```text
Obligation {
    id,                       // stable within one compilation
    kind: Bounds { refined_length: Option<i64> }
        | Overflow { op: + | - | *, ty }
        | Division | Shift,    // always checked today; listed for completeness
    span,                     // the span the evaluator's panic carries
    function,                 // instance index and qualified name
    goal,                     // "0 <= index && index < 0x2000", "the result stays in range"
    hypotheses,               // the linear facts in scope, pretty-printed
    terms,                    // which goal terms are parameters, parameter lengths, or locals
}
```

All four `bounds_checked += 1` sites and the `None => c.require(PANIC, span)`
branch of the arithmetic check push one. `KUSH_PROOF_REPORT=verbose` prints the
whole table (kind, function, location, goal), so the report lists every check
the fuzzer will attack, overflow included. A test pins that the number of
recorded bounds obligations equals `bounds_checked`.

### 2.2 The options

**A. Fuzz the enclosing function's parameters directly.** For a function `f`
that contains obligations, synthesize a harness that decodes `f`'s arguments
from a byte tape and calls `f`. Generators come from the parameter types:
integers of every width, `Bool`, `Bytes`, `Vec<T>` and arrays of generatable
`T`, records and enums field by field, `&T`/`&mut T` by generating a `T` into
a local and borrowing it. Generic functions are attacked at the instances the
program already uses. Integer and length choices are biased by a **dictionary**
taken from the obligation itself and the function's facts: the type's
minimum and maximum, 0, ±1, every constant in the goal and the hypotheses, and
±1 around each (`0x2000`, `0x1FFF`, `0x2001` for a `where len >= 0x2000`
field). Preconditions are respected by construction: the harness evaluates
each erased proposition parameter as a guard, `if !(0 <= at && at < 0x80) {
return; }`, then passes `_`, and the checker proves the call like any other.
Inputs that a precondition rules out are therefore never counted as
counterexamples.

Strengths: reaches most obligations in a few runs, because they sit at depth
one; works with no user code; every obligation gets a local verdict. Weakness:
a counterexample is *local*. The function can fail on inputs no caller ever
passes (`skip(src, -1)`). Section 3 handles that honestly instead of calling
it a bug.

**B. Coverage guidance.** Record which obligations a run reached and how
close each came to failing, and keep inputs that reach a new obligation or get
closer. The **margin** is `min(index, length - 1 - index)` for bounds, and for
overflow the number of bits between the exact result and the nearest end of
the type's range. That is libFuzzer's "value profile" idea, but over the exact
checks we care about rather than every comparison. Two places can measure it:

- the reference evaluator already evaluates every checked access and
  operation and knows its span, so an observer on `Evaluator` would get the
  signal with almost no code. It is about two orders of magnitude slower than
  native code, though, which matters for deep `#[fuzz]` entries such as a
  Game Boy running a ROM;
- an instrumented native build. Today native panics cannot be attributed:
  `kush_panic` prints one fixed message, inline checks trap, and deferred
  overflow moves the panic to the end of a chunk on purpose
  ([deferred-overflow.md](deferred-overflow.md)). So this needs a fuzz build
  mode (section 2.3).

**C. Seed from the failed proof's model.** There is no SMT model: the search
returns no witness. The bounded integer fallback could be extended to return
the integer point at a feasible leaf of its case split. That point is over the
prover's *abstraction* of the program, though: opaque values, dropped
nonlinear facts and fresh `x & mask` terms are unconstrained there. Its
parameter values make a good seed; it is not evidence. If a run seeded from
such a point does *not* fail, the prover was missing a fact that the program
does have, and the obligation is a lemma candidate (section 3).

### 2.3 Recommendation

**A + B in an instrumented native build, and C later as an optional seed.**

- **Fuzz build mode.** `kush fuzz` builds one native executable with the
  Cranelift backend (LLVM's longer compile time buys nothing here) and a
  `fuzz` code-generation flag:
  - deferred overflow is off, so a check panics where it is written;
  - every recorded obligation is compiled as an explicit test before the
    operation: compute the margin inline and call
    `kush_fuzz_check(id, margin)`. The runtime keeps a static table of hit
    counts and smallest margins per obligation id. A negative margin records
    the id as the failure, writes the table and aborts. The original check
    then never fires for an obligation, so the failure is always attributed;
  - any other panic (allocation, I/O, a check that is not an obligation)
    still goes through `kush_panic`, which in a fuzz build writes the table
    with "unattributed panic" before aborting;
  - at normal exit the table is written too. It goes to the file named by
    `KUSH_FUZZ_OUT`, as a fixed binary layout the driver reads back.
  Ordinary builds are unchanged: without the flag none of this is emitted.
- **One binary, many runs.** All harnesses for the session are appended to
  the in-memory sources (as `kush test` does) and the generated `main`
  dispatches on `argv[1]`, the harness number. The driver runs the binary once
  per input with the tape on standard input and a wall-clock timeout
  (a timeout counts as "survived, too slow", not a find). Process start-up is
  about a millisecond, so a few thousand runs per function take seconds. A
  fork server can come later if start-up dominates.
- The reference evaluator stays the oracle for the tests of this feature: a
  test may replay a found input under `kush eval` and check that it panics at
  the same span.
- Harness per targeted function `f`, placed in `f`'s own module so private
  functions are reachable:

  ```text
  fn __fuzz_f() -> Unit ! {io, alloc, panic} {
      let mut tape = fuzz.Tape.stdin();
      let src = tape.bytes(64);
      let at = tape.i64();
      if !(0 <= at && at <= src.len()) { return; }   // f's erased precondition
      let _ = f(&src, at, _);
  }
  ```

  The tape decoder is a small `std.fuzz` module written in Kush. An exhausted
  tape yields zeros, so every byte string is a valid input and mutation never
  produces a rejected one.
- Mutations: byte flips, insert or overwrite with a dictionary value, integer
  ±1, copy a chunk, splice two corpus inputs. The corpus keeps an input when it
  reaches a new obligation or improves an obligation's smallest margin
  (option B). A run budget is split across the function's obligations; one
  that is already reached with margin 0 and has not failed is retired early.
- `#[fuzz]` entries for deep state. Some obligations sit behind state that no
  generator can build: the Game Boy's `Machine` holds a linear window and an
  audio device. For those, a project can declare entries in its test target,
  shaped like `cargo fuzz` targets:

  ```text
  #[fuzz]
  fn random_rom(input: &Bytes) -> Unit ! {alloc, panic} {
      let mut m = machine.headless(rom_from(input));
      machine.step_n(&mut m, 2000);
  }
  ```

  They are compiled into the same binary and use the same corpus. Every obligation they
  reach counts toward coverage, and their findings are *entry-level* (real)
  counterexamples by construction.
- Option C is a later sub-node: return the fallback's feasible point and add
  its parameter values to that function's initial corpus.

Cost: the instrumentation is one inline comparison and one call per
obligation, and only in fuzz builds. The work is in the Cranelift backend
(the checked-operation and `Vec` access lowerings) and in the C runtime
(`kush_fuzz_check`, the table, the panic hook). The LLVM backend does not need
the mode.

## 3. What a counterexample produces

**Minimization.** While the same obligation id still fails, shrink the tape:
delete chunks, then move each decoded integer toward 0 or the nearest
dictionary value, then shorten each decoded `Bytes`/`Vec`. The result is
decoded once more and printed as source values.

**Classification.** A counterexample is one of:

1. **Entry-level bug.** Found through a `#[fuzz]` entry, or in a `pub`
   function of the entry package whose preconditions the input satisfied.
   Reported as `FOUND ... bug`.
2. **Local counterexample.** Found in a private function. Nothing yet says a
   caller can pass that input. It is reported as `FOUND ... local`, with the
   suggestion to turn the check into a precondition. Applying it moves the
   obligation to the callers: each caller then proves it (the check is gone,
   proved one level up) or it becomes a new unproved obligation in the
   caller, which the next `kush fuzz` attacks there. Repeating this pushes the
   obligation outward until it is proved or reaches a boundary where it is a
   real bug.

**Suggestions**, chosen from the obligation's `terms`:

- every goal term is a parameter or a parameter's length: suggest an erased
  precondition with exactly the goal (`erased in_text: { 0 <= at && at <
  src.len() }`);
- a goal term is the result of a call: suggest an `ensures` on that callee
  stating the range the obligation needs;
- a goal term is a loop variable: suggest the `invariant` that gives the
  bound;
- a `Vec` field is indexed by a constant range: suggest a length refinement
  (`where len >= N`), which is how the Game Boy proves its memories.

**Reproduction.** For a target reachable from the test target (a `pub`
function, or a `#[fuzz]` entry), the reproduction is a `kush test` case:

```text
#[test]
fn fuzz_reader_skip_1() -> Unit ! {alloc, panic} {
    // kush fuzz: bounds check src/reader.kush:81:12, seed 0
    let src = Bytes.from_text("");
    let _ = reader.skip(&src, 0);
}
```

`--save` appends it to the test target, under one `// --- kush fuzz ---`
marker so it is easy to review or delete. A private target cannot be called
from the test target, so its minimized tape is saved under
`fuzz/regressions/<module>.<function>/<obligation hash>` instead. `kush fuzz`
replays every saved regression before it generates new inputs, so a fixed
bug stays fixed. Without `--save`, the test text is printed and nothing is
written.

**Survived checks are lemma candidates.** A check that was reached many times
with margin 0 but never failed is probably true, so the prover was missing
something. `kush fuzz --report` lists such checks with the goal and the
hypotheses the prover had, so the missing fact (often an `ensures` on a helper
or a loop invariant) is visible.

## 4. Proved-or-attacked coverage

Every obligation ends in exactly one state:

| state | meaning |
|---|---|
| proved | discharged by the checker; no run-time check |
| found | at least one counterexample (bug or local) |
| survived | reached at least `R` times (default 100) without failing |
| unreached | generators and entries never reached it |
| no generator | its function's parameters cannot be generated, and no `#[fuzz]` entry reached it |

*Proved or attacked* means `proved + found + survived`. The other two states are
the gap, and the report names them. `--report` prints one row per function
that has any check, then a total per package:

```text
function                      checks proved found survived unreached no-gen
kernel.reader.skip                 3      0     1        2         0      0
kernel.store.get                   2      0     0        2         0      0
gameboy.apu.square_period          1      0     0        1         0      0
...
package kernel                   102     14     3       71        10      4   87% proved or attacked
```

`--json` carries the same data for every obligation, so CI can fail when the
percentage drops.

## 5. Showcase demo

The demo is the loop *report → attack → prove*, on code that was written
before this feature existed:

1. **Kernel.** Today, 0 of its 102 accesses are proved. Its reader functions
   take `(src: &Bytes, at: i64)`, ideal for direct generation. Run `kush fuzz`
   and expect local counterexamples at `at < 0` and `at > src.len()`. Apply
   the suggested preconditions, re-run, and show how many checks are now
   proved in their callers. Then add a `#[fuzz]` entry that parses arbitrary
   bytes as a term and checks it. Any entry-level find is a real reader bug;
   if none is found, report the survived count.
2. **Game Boy.** 353 accesses are proved; 88 remain, plus the overflow checks
   the new report will list. Add one `#[fuzz]` entry that runs a random 32 KiB
   ROM through the plain cartridge for a few thousand instructions on a
   headless machine. Report the coverage table, and either a real issue with
   its reproduction or "every remaining check survived N attacks". The
   native engine is what makes thousands of emulated instructions per run
   affordable.

The README of each example gets the before and after numbers. The demo is
honest either way: "no counterexample in N runs, these K are unreached" is
a result too.

## 6. Tests

New suites in `crates/kush/tests/`:

- `proof_obligations.rs`: each obligation kind is recorded with the right
  kind, span, function and goal; proved checks are not recorded; bounds
  obligations equal `bounds_checked`; overflow obligations disappear exactly
  where `overflow_elision.rs` expects elision.
- `proof_fuzz.rs`:
  - an instrumented native binary reports the failing obligation id, and
    the same input under `kush eval` panics at that obligation's span;
    margins for bounds and overflow are computed correctly; a build without
    the fuzz flag emits no instrumentation;
  - generators: every supported type round-trips through the tape; length
    refinements and dictionary constants appear; a precondition guard is
    respected (no counterexample violates it); unsupported parameters report
    `no generator`;
  - planted bugs are found and minimized to the expected values (an
    off-by-one index, an `i64` overflow at `MAX`, a `u8` overflow);
  - a check that is true but unproved ends `survived`; one behind an
    impossible branch ends `unreached`;
  - the same seed gives byte-identical output; a timeout is not a find;
  - the printed reproduction compiles and fails under `kush test`; `--save`
    regressions are replayed;
  - CLI: exit codes 0/1/2, `--list`, `--json`, the filter.
- Unit tests in the new `fuzz` module for the mutators, the shrinker and the
  coverage table.
- One small demo smoke test on a copy of the kernel reader with a fixed seed
  and a small budget, so the showcase cannot silently rot.

## 7. Implementation steps (plan sub-nodes)

1. **PF-OBLIGATIONS**: obligation table in the checker;
   `KUSH_PROOF_REPORT=verbose` lists all kinds, including overflow;
   `proof_obligations.rs`.
2. **PF-INSTRUMENT**: Cranelift fuzz build mode: obligation ids in the IR,
   inline margins, `kush_fuzz_check`, the runtime table, `KUSH_FUZZ_OUT`,
   deferred overflow off; tests that an instrumented binary reports the
   right id and margins and that ordinary builds are unchanged.
3. **PF-HARNESS**: `std.fuzz` tape decoder; harness synthesis for directly
   generatable parameters, with precondition guards.
4. **PF-ENGINE**: `kush fuzz` command: seeds, mutation, corpus, budgets,
   `--list`, exit codes.
5. **PF-SHRINK**: minimization, classification, suggestions, reproduction
   text, `--save` and regression replay.
6. **PF-ENTRIES**: `#[fuzz]` entries.
7. **PF-COVERAGE**: the proved-or-attacked table, `--report`, `--json`.
8. **PF-DEMO**: kernel and Game Boy runs, README numbers.
9. **PF-SEED** (optional): candidate points from the integer fallback as
   seeds.

## Non-goals

- Fuzz instrumentation in the LLVM backend, and a fork server.
- Fuzzing floats, function values, linear resources or effect handlers as
  parameters; they show as `no generator` and are reached through `#[fuzz]`
  entries.
- Treating a survived check as proved. Only the checker proves; the fuzzer
  only attacks.
