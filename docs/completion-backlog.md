# Full five-area completion backlog

Baseline: `10d9588`, implementation `29674d2`, 681 tests/fmt/Clippy passed on
Boat and independent review reported no blocking findings. The user requested
completion of the five areas below, rather than another milestone described as
complete while features remain. Every unchecked item is still outstanding.
Implementation and review must establish each item's precise supported contract;
changing a diagnostic or deleting an explicit rejection is not completion.

## Borrowing

- [ ] General shared/exclusive reference support, including escape and reborrow contracts.
- [ ] Broader sound lifetime inference.
- [ ] Capturing lambdas returning borrowed slices with represented provenance.
- [ ] Borrowed records in callable parameters/results/captures.
- [ ] Borrowed records in structured tasks with checked scope ownership.
- [ ] Nested record-field borrows and disjoint-field loans.

## Traits

- [ ] Associated types and constants with checked projection/substitution.
- [ ] Generic and blanket implementations with coherent overlap rules.
- [ ] Trait objects and checked dynamic dispatch/object safety.
- [ ] Specialization with an explicit deterministic coherence contract.

## Grades and linear resources

- [ ] General grade inference beyond bare result-only expected-arrow inference.
- [ ] User-defined grade algebras with validated laws and decidable checking boundaries.
- [ ] Copyable exact-use result transfer across every control-flow/discard position.
- [ ] Grade-zero runtime erasure with relevance/effect guarantees.
- [ ] Cancellation cleanup of linear resources and linear task results.

## Advanced types and effects

- [ ] Structural record subtyping and representation-changing coercions.
- [ ] Broader algebraic subtype inference with documented decidability boundaries.
- [ ] Effect handlers and checked resumption ownership.
- [ ] General row constraints beyond concrete exclusions.
- [ ] Broader runtime-dependent proofs with mutation/version tracking.
- [ ] Runtime-sized inline arrays with checked lifetime/storage layout.

## Memory and optimization

- [ ] Automatic fusion where effect/order/termination analysis proves equivalence.
- [ ] Widening reuse with explicit allocation/capacity guarantees.
- [ ] Custom allocators and lifetime-safe allocator ownership.
- [ ] Fallible allocation/reuse with exact cleanup on all failure paths.
- [ ] Reproducible performance and physical-memory benchmarks.

Arbitrary effectful callback interleaving is not semantics-preserving: callback
output, panic, and scheduling order can differ. Existing explicit map chains
select that order deliberately. Automatic fusion must prove equivalence rather
than silently changing the language's evaluation semantics.

## Completion evidence

Each item needs positive and rejection tests, native/reference agreement where
applicable, exact cleanup checks for owning values, documentation of semantics,
and integration checks. Code must be committed and independently reviewed.
This list is not a promise that all requirements have a general decidable or
single-day implementation; unresolved design conflicts remain visible here.
