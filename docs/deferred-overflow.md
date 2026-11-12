# Deferred overflow checks

Kush integer arithmetic panics on overflow, and that does not change. What
changes is *when* a hot loop finds out. The LLVM backend enables this by
default (`--no-deferred-overflow` turns it off; `--deferred-overflow` turns it
on for Cranelift, where it is correct but gains little).

## The problem

A panic branch after each operation is cheap in scalar code. In a loop it is an
early exit with a side effect, and that stops the loop vectorizer. Rust release
builds avoid the cost by not checking. Rust built with `-C overflow-checks=yes`
runs the same scalar loop Kush used to.

A flag that makes arithmetic wrap is not an option for Kush: the checker
derives facts from arithmetic (`let j = i + 1` proves `j == i + 1`), and proved
indices become unchecked loads. Wrapping would make those proofs false.

## The transformation

For an innermost counted loop with no observable effects, the panic moves to
the end of a bounded chunk of iterations. A panic aborts the process, so
"panic at iteration 5" and "panic a little later" cannot be told apart if
nothing observable happens in between. Two things this rests on, stated
plainly: the memory a deferred loop writes (`Slice.set`) is private to the
process until the loop is done, so a few thousand extra element writes
before the abort are not observable; and overflow, bounds and division
panics all print the same message, so an overflow reported in place of a
later bounds or division panic of the same chunk looks the same (the one
other message, for stack exhaustion, cannot arise in a deferred loop, which
contains no calls). Per-cause panic messages, or a loop
writing memory another process maps, would need this revisited.

There are two modes, chosen per operation (`native/deferred.rs`).

**Exact.** The operation wraps and ORs its exact overflow bit into a sticky
word tested after the loop. Until the first overflow every value equals the
checked execution's value, so the sticky word is set exactly when the checked
loop would have panicked. Add and subtract use plain bit operations, which
vectorize. This mode needs no replay, so it also covers loops that update a
slice in place, and all narrow and unsigned kinds.

**Certified.** Signed 64-bit `+`, `-`, `*` wrap with no test at all. The loop
instead ORs a magnitude word (`v ^ (v << 1)`) for every *leaf* operand, that
is, every operand that is not itself a certified operation. An operand whose
type already bounds it is not tracked: a byte read is below `2^8`, and a
narrow integer widened with `Int.convert` is within its type's range
(narrow values stay canonical in deferred loops, property 3 below). The
number of reduction steps is not counted in the loop (that would be a vector
reduction of its own): it is bounded afterwards by the iterations the chunk
ran, which the counter's distance from its start gives exactly (a deferred
loop has no `break`), plus one, times the reduction operations in the body.
After the loop each leaf has a `u` with `|leaf| <= 2^u`, and bounds follow
from the expression structure:

```text
u(a + b) = u(a - b) = max(u(a), u(b)) + 1
u(a * b) = u(a) + u(b)
u(prefix sums of acc) = max(u(acc at entry), u(step operands)) + bits(step count)
```

If every certified result has `u <= 62` and no exact-mode operation of the
chunk set the sticky word, nothing overflowed (the sticky word is tested
after the certificate, so the argument is about the first overflow of
either kind). Proof for the certified part: take the
first certified operation that overflows in the checked execution. Everything
before it is exact, so its operands are exact and were observed by the
magnitude words; its mathematical result is then at most `2^62`, which fits.

If a bound is too large, nothing is concluded. The state at the start of the
chunk is restored and the rest of the loop runs with ordinary checks, which
either panics at the right operation or produces the exact result. (It does
not go back to chunks: data large enough to fail a certificate is usually
large throughout, and replaying every chunk would do the work twice.) This
is why a reduction
whose every prefix must be checked (`[MAX, 1, -5]` panics although the total
fits) still behaves exactly as before.

A reduction `acc = acc + e` is the important case. Its exact overflow bit
depends on the running sum, which would serialize the loop; the certificate
depends only on the operands and the count, so the loop becomes independent
reductions LLVM can vectorize. A chain with the accumulator leftmost,
`acc = acc + a - b * 3`, is one reduction with one term per operation: every
intermediate value (`acc + a`) is itself a prefix sum of the terms, so the
same bound covers it, and an intermediate overflow still fails the
certificate even when the chain's total would fit. Read as `(acc + a) - b*3`
without this, the running sum would be a tracked operand, which ties each
iteration to the last and keeps the loop scalar.

## When a loop qualifies

Deferring pays only where LLVM then vectorizes the loop: a scalar loop with
sticky overflow words is slower than one with branches, and every deferred
loop costs compile time. So a loop is deferred only if all of these hold
(`KUSH_TRACE_DEFERRED=1` prints the reason per loop that is not):

- It is an innermost `while`, with no `continue` and no `break` (LLVM 18
  does not vectorize a loop with an early exit).
- It is counted over an integer: `while i < bound { ...; i = i + c; ... }`
  (or `<=`, or `>`/`>=` with `i = i - c`), `c` a positive constant, exactly
  one update of `i` at the top level of the body (anywhere in it; accesses
  after it are proved with the counter one step on), and a bound made of
  constants, locals the loop does not assign, container lengths, and
  arithmetic on those. A step the checker has proved cannot overflow counts
  as well.
- Every element index is the counter, or the counter plus or minus a
  constant. Anything else is a gather, a scatter or a dependence between
  iterations.
- Its body contains only scalar locals, arithmetic, comparisons, `if`,
  integer and float builtins, and `Slice`/`Vec`/`Bytes` length and element
  reads, plus `Slice.set` through an exclusive view. No calls, I/O,
  allocation, drops, borrows, effects, division or remainder (x86 has no
  64-bit vector division), or proved unchecked reads (`Slice.at`, `Vec.at`).
- On baseline x86-64 (SSE2), also no store or checked arithmetic under a
  condition and no byte-buffer reads. These vectorize, but SSE2's blends and
  its widening of bytes to words cost more than the checks they replace
  (measured 0.65 and 0.67 times the speed of the checked loop). With
  `--target-cpu native` (AVX-512 here) the same loops ran 2.8 to 2.9 times
  faster, so they are deferred there.
- Without a native 64-bit vector multiply (anything but `--target-cpu
  native` on an AVX-512DQ machine), not a loop that multiplies two
  non-constant operands and would track two or more operands per iteration.

Two more conditions are tested when the loop is reached, because they depend
on values: every slice the loop reads or writes must be laid out as
consecutive whole elements (a `Bytes` viewed as `&[i64]` is not), and (below)
written and read views must not overlap. A loop that fails either runs with
ordinary checks. `KUSH_TRACE_DEFERRED` cannot report this: the decision is
made at run time.

## Bounds checks

A bounds check inside a loop is an early exit to the panic, and LLVM does not
vectorize a loop with one unless it can prove the check never fails, which it
can only for the slice whose length is the bound, and only for `i` itself.
A deferred chunk instead proves all of its accesses in range before it runs.
Every index is `counter + k` for a constant `k`. At the top of every
iteration of the chunk the counter lies between its value at the chunk's
start and the bound (the loop condition holds there). The counter's single
update is a top-level statement of the body, so each access comes either
before it in every iteration, where the counter is in that range, or after
it in every iteration, where the counter has moved by exactly one step; an
access after the update is treated as `counter + k ± step`. So every index
of an access lies in a range computed once. If any range reaches below zero or past its
container's length (or computing it overflows), the rest of the loop runs
with ordinary checks, which panic at the right access. Otherwise the chunk's
reads and writes are emitted without checks: `Slice.get` as `Slice.at`,
`Vec.get` as a direct load instead of a runtime call, `Bytes.get` as a byte
load, `Slice.set` without its range test.

This is a proof made at run time from exact values only. The counter is
never deferred (it feeds the loop condition), nor is the bound, nor is
any index; container lengths cannot change in the loop (it may not assign a
non-scalar local, and stores go only through exclusive slices). So property
2 below still holds: no access depends on a deferred operation.

## What is generated

The loop body is lowered twice, as an ordinary loop over a slice is:

- the deferred chunk, specialized to the plain layout of every slice it
  touches, its accesses proved;
- the rest of the loop with ordinary checks, for everything rare: views
  that overlap or a slice with another layout (the whole loop), accesses not
  provably in range (from that chunk on), and a chunk whose certificate
  failed (from its entry state).

A chunk runs while the counter is short of a limit computed at its start:
the bound, or 65,536 steps on if that comes first (saturating at the end of
the counter's range). That gives LLVM a loop with a single counted exit.
Every chunk starts at one header, so the chunks form a single ordinary loop.

An earlier version lowered the body up to eight times (one copy per reason,
each in two layouts), and a later one three times; on the generated
6,400-line program in `benchmarks/build-scale` each copy cost about 5 ms of
LLVM time per loop. The larger function can still cost an inlining
decision: a small loop function called with a byte view as `&[i64]` runs the
ordinary-checks copy, and measured 1.7 times slower than with
`--no-deferred-overflow`, where it was inlined and specialized to its
caller.

The certificate counts leading zeros of `word | 1`. That gives the same
bound, and the operand is visibly non-zero. Otherwise, on a target without a
cheap leading-zero count, LLVM's code generation puts a branch around each
count and rescans the whole function every time it does: with a few hundred
deferred loops inlined into one function, that pass alone took two thirds of
the build.

## Why the speculative run is safe

After an overflow that has not been reported yet, the loop is computing with
wrong values. Four properties make that harmless.

1. **Bounded delay.** The loop runs in chunks of at most 65,536 iterations.
   Each chunk has its own sticky word, certificate and replay state, and is
   checked when it ends. An overflow is therefore reported within one chunk,
   however long the loop would have run and whatever the wrong values do to
   its control flow (they cannot affect it: the counter and the bound are
   exact). A checked loop that panics in its first iteration and a deferred
   one differ by at most a fraction of a millisecond of work.
2. **No access depends on a deferred value.** The checker's proofs may use
   "this operation did not overflow" or "this value has its type's range" as
   hypotheses. A deferred operation breaks exactly those, so a loop
   containing a proved unchecked read (`at`) is not deferred. Every access in
   a deferred chunk is checked, either at run time per element or, as
   described under "Bounds checks", once per chunk from exact values.
3. **Values stay canonical.** A deferred narrow operation yields its wrapped
   result, and arithmetic the checker proved in range is wrapped as well
   inside a deferred loop. Every narrow value therefore keeps the
   sign- or zero-extended form the rest of the lowering assumes (a narrow
   signed division, for example, has no `MIN / -1` guard because canonical
   operands cannot need one).
4. **Everything else that can panic still panics immediately.** Reaching such
   a panic with wrong values means an overflow already happened, and the
   checked loop would have panicked too.

In addition, every operation feeding a loop condition, an `if` condition, the
left side of `&&`/`||` or an index keeps its immediate check, transitively
through locals. This keeps the speculative run on the checked run's path in
the common case, which keeps certificates from failing needlessly; safety
does not depend on it.

Certified mode additionally requires that a replay sees the memory the first
attempt saw: the loop may store only through exclusive slices (`&mut [T]`) it
never reads, and a loop that stores may read only slices (one that stores
nothing may also read vectors and byte buffers). The borrow rules make two distinct
views disjoint, but the replay does not lean on that: before the loop the
address range of every written slice is compared with that of every read
slice, and a loop whose ranges overlap runs with ordinary checks. In-place
updates fall back to exact mode, which needs no replay.

One cost rule applies. Without a native 64-bit vector multiply (anything but
`--target-cpu native` on an AVX-512DQ machine), a loop that multiplies two
non-constant operands and would track two or more operands per iteration is
faster with ordinary checks, so it keeps them.

## What it costs and gains

Per iteration, exact mode adds three bit operations to an add or subtract;
certified mode adds two operations and an OR per tracked operand, and nothing
per arithmetic operation. A failed certificate costs one wasted chunk, after
which the loop runs at the speed of ordinary checks. Operands near `2^62`, or
long reductions of large values, take that path; values whose magnitude
times the trip count stays far below `2^63` never do.

Speed of each loop shape against `--no-deferred-overflow`, called out of line
on 4,096 elements 200,000 times (median of five, ms):

| Loop | Baseline, deferred | checked | Native, deferred | checked |
| --- | ---: | ---: | ---: | ---: |
| `acc + s[i] * 3`, bound `Slice.len(s)` | 205 | 346 | 69 | 325 |
| the same, bound in a local | 210 | 486 | 88 | 515 |
| `acc + a[i] + b[i] * 3` | 379 | 520 | 154 | 618 |
| `acc + s[i + 1] - s[i]` | 273 | 449 | 128 | 494 |
| `acc + Vec.get(v, i) * 3` | 206 | 392 | 82 | 371 |
| `acc + convert(w[i]) * 3`, `w: &[i32]` | 166 | 377 | 81 | 372 |
| `acc + Bytes.get(b, i) * 3` | not deferred | 235 | 88 | 254 |
| `if s[i] > 511 { acc + s[i] }` | not deferred | 320 | 101 | 327 |

Before the bounds checks were proved per chunk, only the first row
vectorized; the others ran as scalar loops with sticky words, often slower
than the checked loop.

On the `checked-loops` benchmark (see [llvm-backend.md](llvm-backend.md)) the
checked sum went from 260 ms to 170 ms and scale-then-sum from 1105 ms to
554 ms, against 265 ms and 784 ms for Rust with overflow checks, and 84 ms and
458 ms for Rust without. With `--target-cpu native` the three kernels are
within 3% to 35% of unchecked Rust.

## Status

`tests/deferred_overflow.rs` compares the reference evaluator with every
native configuration on programs chosen to hit each path: successful
certificates, failed certificates that replay, prefix overflow with a fitting
total, exact mode in place, narrow and unsigned kinds, mixed modes in one
loop, values that steer control, effects inside the loop, loops that are
not counted, every way an access can fall outside its container (a bound
past the end, a shorter second slice, offsets below zero and past the end,
counting down, vectors and byte buffers, steps larger than one, within one
chunk and across many), reduction chains overflowing in the middle,
type-bounded operands, and chunk limits at the ends of the counter's range.
`tests/llvm_backend.rs` checks which loops the planner defers on each
target. A panic must be the panic message followed by SIGABRT; any other
signal fails the test. The full suite also passes with deferral enabled on
LLVM.

A fifth independent review (2026-11-12), of the per-chunk bounds proofs,
found that accesses after the counter's update were proved with the
counter one step short: a chunk read and wrote one step past its container,
into a neighbouring vector or unmapped memory. Fixed as described under
"Bounds checks"; the reproducers are
`accesses_after_the_counter_update_see_it_moved`. Its differential
fuzzing of about 3,700 other generated loops found no difference.

An independent review (2026-11-11) differential-tested about 8,000 generated
loop programs without finding a difference, and then broke the first version
by reasoning about what the argument left out. It found an out-of-bounds read
through a proved index whose proof depended on a deferred operation, an
arithmetic trap from a non-canonical narrow value reaching a division, and
loops that ran for 2^62 iterations or forever where the checked build panics
at once. Properties 1 to 3 above are the fixes; the seven reproducers are
tests (`review_*`). Later qualification rules stopped deferring five of
those seven programs altogether, so the bounded-delay property has its own
test on a loop that still qualifies
(`a_long_loop_reports_its_overflow_at_once`). The certificate arithmetic itself held up.

That review did not audit the borrow checker, and deferral no longer needs
it to: the replay checks disjointness itself (above). The `noalias` facts of
the LLVM backend do rest on the exclusivity of `&mut [T]`;
`tests/view_exclusivity.rs` holds the attempts at an aliasing pair that the
checker must refuse, and slice views cannot be passed to foreign code at
all. `--no-deferred-overflow` gives the plain checked code.

Not covered: `loop`/nested loops as a unit, `Vec.map_in_place` callbacks with
checked arithmetic, reductions over narrow or unsigned kinds (they use exact
mode and stay scalar), loops with proved unchecked reads, and loops
containing calls, even to pure functions.
