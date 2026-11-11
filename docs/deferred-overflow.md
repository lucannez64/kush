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
the loop exit. A panic aborts the process, so "panic at iteration 5" and
"panic when the loop finishes" cannot be told apart if nothing observable
happens in between.

There are two modes, chosen per operation (`native/deferred.rs`).

**Exact.** The operation wraps and ORs its exact overflow bit into a sticky
word tested after the loop. Until the first overflow every value equals the
checked execution's value, so the sticky word is set exactly when the checked
loop would have panicked. Add and subtract use plain bit operations, which
vectorize. This mode needs no replay, so it also covers loops that update a
slice in place, and all narrow and unsigned kinds.

**Certified.** Signed 64-bit `+`, `-`, `*` wrap with no test at all. The loop
instead ORs a magnitude word (`v ^ (v << 1)`) for every *leaf* operand, that
is, every operand that is not itself a certified operation, and counts
reduction steps. After the loop each leaf has a `u` with `|leaf| <= 2^u`, and
bounds follow from the expression structure:

```text
u(a + b) = u(a - b) = max(u(a), u(b)) + 1
u(a * b) = u(a) + u(b)
u(prefix sums of acc) = max(u(acc at entry), u(step operands)) + bits(step count)
```

If every certified result has `u <= 62`, nothing overflowed. Proof: take the
first certified operation that overflows in the checked execution. Everything
before it is exact, so its operands are exact and were observed by the
magnitude words; its mathematical result is then at most `2^62`, which fits.

If a bound is too large, nothing is concluded. The loop's entry state is
restored and the loop runs again with ordinary checks, which either panics at
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
- It is counted: `while i < bound { ...; i = i + c; ... }` (or `<=`, or
  `>`/`>=` with `i = i - c`), `c` a positive constant, exactly one update of
  `i` at the top level of the body, and a bound the loop does not change.
- Its body contains only scalar locals, arithmetic, comparisons, `if`,
  `break`, integer and float builtins, and `Slice`/`Vec`/`Bytes` length and
  element reads, plus `Slice.set` through an exclusive view. No calls, I/O,
  allocation, drops, borrows, or effects.

Within such a loop, three rules keep the speculative execution well behaved
after an overflow that has not been reported yet:

1. **Control never depends on a deferred value.** Every operation feeding a
   loop condition, an `if` condition, or the left side of `&&`/`||` keeps its
   immediate check, transitively through locals. Together with the counted
   shape this fixes the trip count; a loop that relies on an overflow panic to
   stop is not counted and is left alone.
2. **Indices never depend on a deferred value**, by the same transitive rule,
   so a statically proved unchecked access never sees a wrapped index.
3. **Everything else that can panic still panics immediately.** Reaching such
   a panic with wrong values means an overflow already happened, and the
   checked loop would have panicked too.

Certified mode additionally requires that a replay sees the memory the first
attempt saw: the loop may store only through exclusive slices (`&mut [T]`) it
never reads. In-place updates fall back to exact mode.

One cost rule applies. Without a native 64-bit vector multiply (anything but
`--target-cpu native` on an AVX-512DQ machine), a loop that multiplies two
non-constant operands and would track two or more operands per iteration is
faster with ordinary checks, so it keeps them.

## What it costs and gains

Per iteration, exact mode adds three bit operations to an add or subtract;
certified mode adds two operations and an OR per tracked operand, and nothing
per arithmetic operation. A failed certificate costs one extra pass over the
loop. Operands near `2^62`, or long reductions of large values, take that path
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
not counted. The full suite also passes with deferral enabled on LLVM.

The soundness argument above has not had the independent hostile review the
borrow checker received. The property it relies on outside this module is the
exclusivity of `&mut [T]` views. Until it has been reviewed,
`--no-deferred-overflow` gives the plain checked code.

Not covered: `loop`/nested loops as a unit, `Vec.map_in_place` callbacks with
checked arithmetic, reductions over narrow or unsigned kinds (they use exact
mode and stay scalar), and loops containing calls, even to pure functions.
