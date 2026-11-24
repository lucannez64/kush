# Validation records

Test counts, gate runs and review notes that used to sit in the design
documents, moved here unchanged (FND-DOC-HISTORY). Each entry names the
document it came from. Counts and gates are as of the day they were written;
"Boat" was the remote build machine, which is no longer used.

## From [basic-values.md](../basic-values.md)

The final full Boat run passes 602 tests, formatting and Clippy with warnings
denied. The generic-trait/generic-method stage adds eighteen tests for
concrete specializations, trait-argument identity and arity, bounded helpers,
contract alpha-equivalence, generic nominal impl targets, borrowed-record
receivers, loan retention, cross-module visibility, owning cleanup, and
native/reference agreement; see [traits.md](../traits.md). Root review added regression coverage for the String conversion
boundary after the initial 528-test implementation; the float stage added nine
tests, including native/reference differential printing, conversion boundaries,
aggregate/callable storage, lexer/projection regressions, and erased-index
rejections; the borrowed-text stage adds thirteen tests covering views,
substrings, boundaries, allocations, loans, helpers/outlives, loops/branches,
`#[noalloc]`/`#[nosuspend]`, later arguments, native agreement, and every
documented escape rejection. The static trait/method stage adds sixteen tests
covering inherent and trait dispatch, bounded generic helpers, receiver order,
owned moves and cleanup, erased evidence, lifetime returns, visibility,
duplicates/ambiguity, exact contracts, and rejected unsupported forms; see
[traits.md](../traits.md). The borrowed-receiver stage adds seventeen tests for
shared inspection and exclusive updates in both backends, ordinary `&Record`
helpers, owning-record cleanup, nested records and arrays, linear/owning
borrows, trait contracts and disambiguation, bounded generic helpers,
`#[noalloc]`/`#[nosuspend]` contracts, and alias/move/field/escape rejections;
see [borrowed records](../borrowed-records.md).

## From [compact-layouts.md](../compact-layouts.md)

records the 1,152-test full Boat gate, matched before/after controls, explicit

## From [json.md](../json.md)

The full Boat workspace suite passes 474 tests, formatting and Clippy. JSON
regressions cover

## From [lifetime-graph.md](../lifetime-graph.md)

 Integration uses the full Boat gate.

## From [lifetime-graph.md](../lifetime-graph.md)

The source review checks that both former closure loops route to the new solver,
that SCC closure introduces exactly reachable pairs, that declared-cycle rejection
still occurs before a signature is accepted, and that notes only describe a
failure rather than changing the successful ownership path. This is a limited
in-session review and exhaustive small-graph testing, not an independent review
or a soundness proof.

## From [lifetime-graph.md](../lifetime-graph.md)

Final validation: full Boat gate passed **1,179 tests**, formatting and strict
workspace/all-target Clippy. Standalone solver tests and Clippy also passed
locally. No recursive inference or variance node is closed by this result.

## From [grades.md](../grades.md)

Final root validation passes 618 workspace tests, formatting and Clippy on
Boat. Three additional regression tests cover hidden control-flow returns,
returns inside `?` operands and later assignments that must not erase an
earlier return obligation.

## From [llvm-backend.md](../llvm-backend.md)

- `KUSH_BACKEND=llvm cargo test --workspace` replays the entire suite on the
  LLVM backend: 1,708 tests pass on both backends and with `KUSH_BACKEND=llvm-release` (LLVM 18.1.3, 2026-11-11).

## From [allocator-pool.md](../allocator-pool.md)

Compiler `528a804` passes the full Boat gate (1,149 tests, formatting, strict
Clippy). Local direct C checks also cover alignment and marker state, fallible
pool hits, growth and both retention bounds. The stable logical stats format
is unchanged; physical byte expectations reflect the 16-byte header.

## From [borrow-model-contract.md](../borrow-model-contract.md)

Validation: the five focused `lifetime_integration_baseline` tests and strict
Clippy passed on Boat. The accepted last-use case also compares reference,
default native and release native execution. This is focused baseline evidence,
not a full-suite result for the upcoming delegated implementations. The initial
probe confirmed a conservative derived-view parent-drop restriction; tests and
this contract preserve it rather than claiming Rust-style view-copy semantics.

## From [niche-layouts.md](../niche-layouts.md)

## Validation checkpoint

The full Boat workspace gate passed **1,164 tests**, formatting, and strict
all-target Clippy. The sandbox was stopped afterwards. Local focused checks
also passed the two instantiated-layout assertions and ten integration tests;
each accepted integration program ran in the evaluator and native backend
with both default and release code generation. Existing integer, string,
slice, async and linear-task regressions passed locally during development.
The example prints `42`, `42`, `65` in evaluator and native release execution.

Logs: `/tmp/kush-niche-layout-integration.log`,
`/tmp/kush-niche-layout-final.log`, `/tmp/kush-boat-niche-first.log`.
