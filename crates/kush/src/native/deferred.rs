//! Deferred overflow checks for counted loops.
//!
//! Kush integer arithmetic panics on overflow. A panic branch after every
//! operation is cheap for scalar code, but it stops LLVM from vectorizing a
//! loop: each iteration has an early exit with a side effect. Rust release
//! builds avoid the problem by not checking; Kush keeps the check and moves
//! it.
//!
//! For an innermost counted loop without observable effects, the panic is
//! deferred to the loop exit, in one of two ways.
//!
//! **Exact.** The operation wraps and ORs its exact overflow bit into a
//! sticky word tested once after the loop. Until the first overflow every
//! value equals the checked execution's value, so the sticky word is set
//! exactly when the checked loop would have panicked. This needs no replay,
//! so it also applies to loops that update a slice in place.
//!
//! **Certified.** Signed 64-bit `+`, `-` and `*` simply wrap, with no
//! per-operation test at all (an exact test would keep multiplications
//! scalar, and the test of a reduction `acc = acc + e` depends on the running
//! sum, which serializes the loop). Instead the loop ORs a magnitude word for
//! every *leaf* operand, i.e. every operand that is not itself a certified
//! operation, and counts reduction steps. After the loop those give, for each
//! leaf, a `u` with `|leaf| <= 2^u` over all iterations, and bounds follow
//! structurally:
//!
//! ```text
//! u(a + b) = u(a - b) = max(u(a), u(b)) + 1      u(a * b) = u(a) + u(b)
//! u(prefix sums of acc) = max(u(acc at entry), u(operands)) + bits(count)
//! ```
//!
//! If every certified result has `u <= 62`, none overflowed: take the first
//! operation that would overflow in the checked execution; all its inputs
//! are still exact and were observed by the magnitude words, so its result
//! is bounded by `2^62`, a contradiction. If a bound is too large nothing is
//! concluded; the loop state is restored and the loop is replayed with
//! ordinary checks. Replay requires that the loop reads no memory it writes:
//! it may only store through exclusive slices it never reads.
//!
//! Both are unobservable: a panic aborts the process, and the loop performs
//! no I/O, calls, allocation or ownership transfer. What keeps the
//! speculative execution well behaved after an overflow that has not been
//! reported yet:
//!
//! * **Bounded delay.** The loop runs in chunks of `CHUNK` iterations, each
//!   with its own sticky word, certificate and replay state. Whatever wrapped
//!   values do to the loop, it stops and reports within one chunk.
//! * **No proof-dependent access.** The checker's proofs may use "this
//!   operation did not overflow" as a hypothesis, so a loop with a proved,
//!   unchecked read (`Slice.at`, `Vec.at`) is not deferred. Every memory
//!   access in a deferred loop is bounds-checked at run time.
//! * **Canonical values.** A deferred narrow operation yields its wrapped
//!   result, and proved-in-range narrow arithmetic is wrapped too, so every
//!   narrow value stays in the form the rest of the lowering assumes.
//! * **Everything else that can panic still panics immediately**, which is
//!   the outcome the checked loop would have had.
//!
//! In addition the loop must be counted over an integer with a bound made of
//! constants, locals and lengths, and every value feeding a loop or branch
//! condition or an index keeps its immediate check. That keeps the
//! speculative run on the checked run's path in the common case; safety does
//! not rest on it.
//!
//! The analysis and the loop transform are a MIR pass (`mir/deferred.rs`,
//! FND-MIR-DEFERRED). This module keeps what native lowering of the result
//! uses: the modes of a deferred operation and the two constants.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Mode {
    /// Wrap and record the exact overflow bit.
    Exact,
    /// Wrap; the result is validated by the loop's certificate.
    Certified,
    /// A certified reduction step `acc = acc +/- e`.
    Accumulate,
}

/// A certified result may be at most `2^LIMIT` in absolute value.
pub(super) const LIMIT: i64 = 62;

/// A deferred loop reports after at most this many iterations.
pub(super) const CHUNK: i64 = 1 << 16;
