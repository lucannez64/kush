# Borrowing, traits, grades, effects, and memory milestone

Reviewed implementation: `29674d27592f0d40d585b86f8a97d0f45ccfc9f6`.
Validation and review completed on 2026-11-02. These are bounded additions, not
complete implementations of every remaining language feature.

## Implemented additions

- Noncapturing lambdas returning shared/exclusive slices from one slice input,
  with checked elision, indirect-call provenance, and split-side metadata.
- Inherited default trait method bodies with per-impl substitution and exact
  override contracts; see [traits](traits.md).
- Bare result-only grade inference from an expected `@[1]` arrow and transparent
  grade-parameterized result aliases; see [result grades](result-grade-inference.md).
- Concrete effect exclusion constraints for executable function/method binders,
  including checked generic `noalloc`/`nosuspend`; see [effects](effect-constraints.md).
- Capacity-preserving vector clear, checked reserve, and explicit interleaved
  effectful map chains; see [vector reuse](vector-reuse.md).
- Bounded native small-block pooling, normal-exit drain, and optional physical
  pool diagnostics with unchanged logical counters; see [allocator pool](allocator-pool.md).

## Validation

The full corrected Boat gate passed formatting, 681 automated tests, and Clippy
with warnings denied. The uploaded 173-file source tree was hash-verified before
checks. The existing sandbox was stopped after the run. No billing settings
changed. Boat access was independently authenticated and verified from the
current development PC; the previous host is no longer required.

An independent DeepSeek V4.1 Flash review found no confirmed blocking defects.
It read high-risk allocator, vector, dispatch, effect, grade, and borrowing paths
and ran six focused probes using a binary newer than the reviewed source:

1. Narrow a vector through an explicit map chain, then get/push elements.
2. Clear and refill a vector of multi-word owning records.
3. Clear and refill a vector of enums with owning payloads.
4. Cross a function boundary with a narrowed vector, then reserve/push/get.
5. Reject a forbidden allocating specialization of a constrained default method.
6. Repeatedly allocate/grow/clear byte buffers, checking pool hits and exit drain.

Accepted probes agreed between native and reference execution, including the
logical allocation counters; the forbidden specialization was rejected. The
review did not rerun the full suite and is not a formal soundness proof.

## Remaining boundaries

General borrowing and borrowed-record callable/task support, associated types
and blanket impls, custom grade algebras, copyable-result transfer, cancellation
cleanup of linear results, effect handlers/general solvers, and automatic
fusion of arbitrary effectful callbacks remain outside this milestone.

Allocator header markers check internal invariants; they cannot reliably detect
invalid pointers or stale handles after reuse. Memory safety relies on compiler
ownership checks. The reference evaluator has a bounded vector budget that the
native runtime does not impose. Direct nested-record field borrows also remain
restricted. Pooling adds a 32-byte allocation header and has no benchmarked
performance or memory superiority claim.
