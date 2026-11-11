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
before the abort are not observable; and every panic prints the same
message, so an overflow reported in place of a later bounds or division
panic of the same chunk looks the same. Per-cause panic messages, or a loop
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
is, every operand that is not itself a certified operation. The number of
reduction steps is not counted in the loop (that would be a vector reduction
of its own): it is bounded afterwards by the iterations the chunk started
times the reduction operations in the body. After the loop each leaf has a `u` with `|leaf| <= 2^u`, and
bounds follow from the expression structure:

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
chunk is restored and that chunk runs again with ordinary checks; the loop
then goes on in deferred chunks, which either panics at
the right operation or produces the exact result. This is why a reduction
whose every prefix must be checked (`[MAX, 1, -5]` panics although the total
fits) still behaves exactly as before.

A reduction `acc = acc + e` is the important case. Its exact overflow bit
depends on the running sum, which would serialize the loop; the certificate
depends only on the operands and the count, so the loop becomes independent
reductions LLVM can vectorize.

## When a loop qualifies

All of these must hold, otherwise the loop keeps immediate checks
(`KUSH_TRACE_DEFERRED=1` prints the reason per loop):

- It is an innermost `while`, with no `continue`.
- It is counted over an integer: `while i < bound { ...; i = i + c; ... }`
  (or `<=`, or `>`/`>=` with `i = i - c`), `c` a positive constant, exactly
  one update of `i` at the top level of the body, and a bound made of
  constants, locals the loop does not assign, container lengths, and
  arithmetic on those. A step the checker has proved cannot overflow counts
  as well.
- Every element index is the counter, or the counter plus or minus a
  constant. Anything else is a gather, a scatter or a dependence between
  iterations; such a loop stays scalar, where a deferred check costs more
  than the branch it replaces (measured: up to 48% slower).
- Its body contains only scalar locals, arithmetic, comparisons, `if`,
  `break`, integer and float builtins, and bounds-checked `Slice`/`Vec`/`Bytes`
  length and element reads, plus `Slice.set` through an exclusive view. No
  calls, I/O, allocation, drops, borrows, effects, or proved unchecked reads
  (`Slice.at`, `Vec.at`).

## Why the speculative run is safe

After an overflow that has not been reported yet, the loop is computing with
wrong values. Four properties make that harmless.

1. **Bounded delay.** The loop runs in chunks of 65,536 iterations. Each
   chunk has its own sticky word, certificate and replay state, and is
   checked when it ends. An overflow is therefore reported within one chunk,
   however long the loop would have run and whatever the wrong values do to
   its control flow. A checked loop that panics in its first iteration and a
   deferred one differ by at most a fraction of a millisecond of work.
   A chunk whose upward counter starts negative runs with ordinary checks
   instead; the branch that decides this is also what
   lets LLVM see that the counter stays non-negative across chunks and drop
   the lower bounds check, without which nothing would vectorize.
2. **No access depends on a proof.** The checker's proofs may use "this
   operation did not overflow" or "this value has its type's range" as
   hypotheses. A deferred operation breaks exactly those, so a loop
   containing a proved unchecked read is not deferred, and every memory
   access in a deferred loop is bounds-checked at run time.
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
never reads, and may read only slices. The borrow rules make two distinct
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
per arithmetic operation. A failed certificate costs one extra pass over that
chunk, with ordinary checks, and nothing after it. A chunk whose upward
counter starts negative runs once, with ordinary checks. Operands near `2^62`, or long reductions of large values, take that path
every time and are slower than plain checking; values whose magnitude times
the trip count stays far below `2^63` never do.

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
loop, values that steer control, effects inside the loop, and loops that are
not counted. A panic must be the panic message followed by SIGABRT; any other
signal fails the test. The full suite also passes with deferral enabled on
LLVM.

An independent review (2026-11-11) differential-tested about 8,000 generated
loop programs without finding a difference, and then broke the first version
by reasoning about what the argument left out. It found an out-of-bounds read
through a proved index whose proof depended on a deferred operation, an
arithmetic trap from a non-canonical narrow value reaching a division, and
loops that ran for 2^62 iterations or forever where the checked build panics
at once. Properties 1 to 3 above are the fixes; the seven reproducers are
tests (`review_*`). The certificate arithmetic itself held up.

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
