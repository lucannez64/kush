# Proof-directed fuzzing (PROOF-FUZZ)

Status: implemented (PF-OBLIGATIONS through PF-DEMO, 2026-11-13); seeding from the prover (PF-SEED) is not.

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
          [--runs N] [--time SECONDS] [--seed N] [--jobs N]
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
- `--jobs N` (`-j N`, default half the cores) fuzzes that many functions at
  once. It changes only the time a session takes, not its report.
- `--list` prints the obligations with their kind, function, location, goal and
  generator status, without running anything (the "what would be attacked"
  view, and what `KUSH_PROOF_REPORT=verbose` becomes).
- `--report` prints the proved-or-attacked table of section 4 after the run.
- `--save` writes each minimized reproduction into the project
  (section 3).
  Without it `kush fuzz` writes nothing outside `target/kush/fuzz/`.
- `--json` prints one JSON object per check instead of the text report, for
  editors and CI.

Every flag above is implemented; seed inputs for entries come from
`fuzz/corpus/<entry>/`.

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
    with "unattributed panic";
  - a fuzz build ends a panic with `_exit(134)` instead of `abort()` and
    sets `RLIMIT_CORE` to 0: with a system core handler, every panicking
    input cost about 40 ms (0.8 s with the kernel example's 1 GiB stack);
  - at normal exit the table is written too. It goes to the file named by
    `KUSH_FUZZ_OUT`, as a fixed binary layout the driver reads back.
  Ordinary builds are unchanged: without the flag none of this is emitted.
- **One binary, many runs.** All harnesses for the session are appended to
  the in-memory sources (as `kush test` does) and the generated `main`
  dispatches on `argv[1]`, the harness number. The driver runs the binary once
  per input with the tape on standard input and a wall-clock timeout
  (a timeout counts as "survived, too slow", not a find). The timeout is 2 s
  until a harness finishes a run, then ten times its slowest finished run
  (at least 100 ms): an input that makes a quick function loop, such as a
  huge size, costs little. Process start-up is about a millisecond, so a few
  thousand runs per function take seconds
  (the whole kernel example: 6 s to build, 5 s for 300 runs of each of its
  12 harnesses). A fork server can come later if start-up dominates.
- **Harnesses run in parallel** (`--jobs N`, default half the cores), as do
  the minimizations of their findings. Each harness has its own random
  stream (derived from the seed and its number) and its own coverage, and
  the results are folded in harness order, so a session is the same for any
  number of jobs.
  The generated sources are written to `target/kush/fuzz/harnesses.kush`
  for reading when a harness behaves unexpectedly.
- Seeds (all zeros, then each scalar set to each dictionary value) always
  join the corpus; a mutant joins it when it reaches a site for the first
  time or lowers a site's smallest margin. Sites in generated code are
  never counted.
- The reference evaluator stays the oracle for the tests of this feature: a
  test may replay a found input under `kush eval` and check that it panics at
  the same span.
- Harness per targeted function `f` (`fuzz/harness.rs`), appended in
  memory to `f`'s own module so private functions are reachable. It takes
  the decoded values, applies `f`'s preconditions as guards and calls it:

  ```text
  pub fn __kush_fuzz_3(src: Bytes, at: i64) -> Unit ! {panic} {
      if !(0 <= at && at <= Bytes.len(&src)) { return; }   // f's erased precondition
      let _ = skip(&src, at, _);
  }
  ```

  A synthetic root module (`<package>.kush_fuzz_entry`) replaces the entry
  file, which it can still import as an ordinary module. Its `main` reads
  the tape from standard input and decodes the arguments of harness
  `argv[1]`. The layout is fixed per harness: each scalar has its own
  little-endian bytes at a fixed offset, each collection a two-byte length
  there (`minimum + n % 65`, where `minimum` comes from a `where len >= N`
  refinement); the elements of the collections follow. Bytes past the end
  of the tape read as zero, so every byte string is a valid input, and the
  driver can place a dictionary value at a known offset.
  Supported parameters: integers of every width and `Bool` by value,
  `Bytes` and `Vec<scalar>` by value, `&` or `&mut`, and `&[scalar]`.
  Anything else (records, enums, generics, effects other than `io`,
  `alloc` and `panic`) is reported as `no generator` with the parameter
  that blocks it. A harness that does not check, for example because the
  result is linear and cannot be discarded, is dropped with the checker's
  message as its reason, and the rest are rebuilt.
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

  Implemented (PF-ENTRIES): an entry is any `#[fuzz] fn name(input:
  &Bytes) -> Unit` in the test target (the checker accepts the attribute
  like `#[test]`; other shapes are listed as `no generator`). Its input is
  up to 65535 bytes (what its two-byte length addresses; large seeds are
  how the kernel's tables are made to grow), and two more mutations suit text: deleting or repeating
  a run of bytes. Every site an entry reaches is shown, wherever it is; its
  findings are bugs, and their reproductions are tests in the test target
  that call the entry. Files in `fuzz/corpus/<entry>/` are seed inputs, run
  first: random bytes rarely get through a parser (the kernel's reader
  accepts nothing a mutation of nothing produces; seeded with four `kush
  core` dumps of the repository's examples, it reaches 77 checks).
- The root imports every target module through a generated *relay* module
  (`<package>.kush_fuzz_relay_N`) that only forwards calls: Kush has no
  import aliases, two modules may share their last name, and the test
  target's module is called `main`, like the root's `main` function.
- The root's input buffer is sized for the longest tape of any harness,
  and the driver trims tapes to their layout's length: `read_all` fails on
  input longer than its buffer, which silently dropped every input above
  256 bytes in the first version.
- Option C is a later sub-node: return the fallback's feasible point and add
  its parameter values to that function's initial corpus.

Cost: the instrumentation is one inline comparison and one call per
obligation, and only in fuzz builds. The work is in the Cranelift backend
(the checked-operation and `Vec` access lowerings) and in the C runtime
(`kush_fuzz_check`, the table, the panic hook). The LLVM backend does not need
the mode.

## 3. What a counterexample produces

Implemented in `fuzz/shrink.rs` (PF-SHRINK).

**Minimization.** While the same obligation site still fails (at most 300
runs), work on the decoded values rather than the bytes: make each
collection empty, then half as long, then one element shorter; then move
every number to zero if that still fails, otherwise bisect between zero and
its value. The result is the smallest failing input in that order: `v = [],
i = 0` for an off-by-one index, `x = 255` for a `u8` increment.

**Classification.** A counterexample is one of:

1. **Bug.** Found through a `pub` function (or, with PF-ENTRIES, a
   `#[fuzz]` entry) with the input satisfying its preconditions. Reported as
   `kind bug: reached through a public function`.
2. **Local counterexample.** Found through a private function: nothing yet
   says a caller can pass that input. Reported as `kind local`, with the
   suggestion to turn the check into a precondition. Applying it moves the
   obligation to the callers: each caller then proves it (the check is gone,
   proved one level up) or it becomes a new unproved obligation in the
   caller, which the next `kush fuzz` attacks there. Repeating this pushes the
   obligation outward until it is proved or reaches a boundary where it is a
   real bug.

**Suggestions**, from the checked expression and the parameters of the
function the check is in:

- an element access `c[i]` where `c` and `i` are parameters: `erased
  in_bounds: { 0 <= i && i < Vec.len(c) }` (or `Bytes.len`, `Slice.len`)
  and reading with `Vec.at(c, i, _)`. A plain `c[i]` stays checked even
  under that precondition; `.at` is the form that uses it;
- `a + b`, `a - b`, `c * a`, `-a` over parameters and constants: `erased
  fits: { MIN <= a + b && a + b <= MAX }` with the type's range. Both are
  tested: applied to the function, the check disappears and the callers
  prove the precondition;
- a product of two values: the prover does not reason about it; bound each
  factor and keep the product checked;
- an operand that is not a parameter (a local, a call's result, a field):
  the prover has no fact bounding it there, so state it with an `ensures` on
  the function that computes it, a loop `invariant`, or an earlier check;
- a field without a stated length: a length refinement (`where len >=
  N`), which is how the Game Boy proves its memories;
- division: `erased nonzero: { d != 0 }` (division keeps its run-time
  check); shifts: the amount must be below the width.

**Reproduction.** For a `pub` function outside the entry file, the
reproduction is a `kush test` case, printed under the finding:

```text
#[test]
fn fuzz_next_line_2() -> Unit ! {io, alloc, panic} {
    // kush fuzz: overflow check at src/lib.kush:2:40
    let x: i64 = 9223372036854775807;
    let _ = lib.next(x);
}
```

`--save` appends it to the test target, after one
`// --- kush fuzz: reproductions ---` marker, and adds the `use` of the
function's module if it is missing; a test already present is not added
again. A private function cannot be called from the test target, so its
minimized tape is saved as `fuzz/regressions/<module>.<function>/<hash>.tape`
instead. `kush fuzz` replays every saved input of the selected functions
before it generates new ones (shown as `saved input`), so a fixed bug stays
fixed. Without `--save`, nothing is written.

**Survived checks are lemma candidates.** A check that was reached many times
with margin 0 but never failed is probably true, so the prover was missing
something. `kush fuzz --report` lists such checks with the goal and the
hypotheses the prover had, so the missing fact (often an `ensures` on a helper
or a loop invariant) is visible.

## 4. Proved-or-attacked coverage

Implemented (PF-COVERAGE). The checker records every check it discharges
(element accesses proved in bounds, arithmetic proved in range) next to the
obligations, so each check of the program ends in exactly one state:

| state | meaning |
|---|---|
| proved | discharged by the checker; no run-time check |
| found | at least one counterexample (bug or local) |
| survived | reached at least once, never failed |
| unreached | generators and entries never reached it |
| no generator | its function's parameters cannot be generated, and no harness reached it |

*Proved or attacked* means `proved + found + survived`; the other two states
are the gap. "Survived" counts a check reached once; `--json` gives each
check's hit count and smallest margin, so CI can demand more. `--report`
prints one row per function that has any check (a function whose checks
were all proved is included; generic instances count under their function),
then the package total. Checks inside the standard library are not the
package's and are left out (an entry reaches many it never exercises fully),
unless one of them failed:

```text
function                          checks  proved  found  survived  unreached  no-gen
kernel.word                            2       0      0         2          0       0
kernel.check.infer_step                4       1      0         0          0       3
...
package kernel                       310      78      4         9          8     211  29% proved or attacked
```

`--json` prints one object per check instead of the text report: function,
file, line, column, kind, goal, state, and for attacked checks the hits,
smallest margin and finding (input, suggestion, test), so CI can fail when
the percentage drops.

## 5. Showcase demo

The loop *report → attack → prove*, on code written before this feature
existed (PF-DEMO, 2026-11-13, `--runs 1000 --report`, seed 0):

| | checks | proved | found | survived | unreached | no generator | proved or attacked |
|---|---|---|---|---|---|---|---|
| Game Boy, functions only | 481 | 262 | 6 | 22 | 12 | 179 | 60% |
| Game Boy, with entries | 535 | 262 | 4 | 177 | 39 | 53 | 83% |
| kernel, functions only | 310 | 78 | 4 | 9 | 8 | 211 | 29% |
| kernel, with entries | 369 | 78 | 4 | 152 | 36 | 99 | 63% |

(Totals grow with entries because the checks of `impl` methods and test
helpers they reach are counted.)

1. **Game Boy: one real bug, found and proved away.** `cartridge.title`
   read the header at `0x134..0x144` with no length check, and `main` calls
   it before `cartridge.kind` rejects short files: a 9-byte file crashed the
   emulator (`panic: checked arithmetic, memory, or I/O failure`, core
   dumped). `cartridge.ram_size` had the same unchecked read, though only
   reached after `kind`'s check. Both now return early when the file is too
   short and read with `Vec.at(rom, i, _)`, so the prover discharges those
   accesses instead of the program checking them; a regression test pins
   it. Two entries (`random_program`, `random_cartridge`, seeded with four
   minimal headers) reach the CPU, video, sound and bank controllers; 177
   checks survived their attack.
2. **Game Boy: four local counterexamples**, in private helpers given
   values no caller passes (`ppu.shade` with a palette index above 3,
   `cpu.mask` with a shift of 8, `apu.analog` with a level near 2^62).
3. **Kernel: no bug; four local counterexamples** in reader helpers
   (`skip`, `atom_end`, `word`) given a negative offset or `start =
   i64::MIN`. Pushing them outward needs `0 <= at` facts across the reader
   (`ensures { result >= 0 }` on every parser), left as follow-up work.
   Two entries (`read_any`, `check_any`) read arbitrary bytes as an exchange
   file; random bytes never pass the reader, so their seeds are `kush core`
   dumps of two examples. 152 checks survived.

Run time on this machine (12 cores, so 6 jobs, with a development build of
`kush`): 80 seconds for the Game Boy (68 harnesses), 11 seconds for the
kernel. One harness at a time with a 2 s timeout, it was about 5 minutes and
30 seconds; most of the difference is `cartridge.mbc5`, whose every run
mirrors the image to 8 MiB (100 ms), now spread over the jobs, and
`cartridge.mirrored`, whose huge sizes now time out at ten times its
slowest finished run instead of after 2 s.

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
