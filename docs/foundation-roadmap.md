# Dependency-first foundations

Implementation proceeds in bounded milestones, retaining the existing rejection
boundaries until the necessary ownership and runtime rules are implemented.

| Foundation | Enables | State |
| --- | --- | --- |
| Static traits and user-defined methods | Shared checked protocol-like code without vtables or runtime dispatch | Implemented for borrowed receivers, generic traits with explicit type/`Nat`/`Grade` specializations, inherent and trait methods (including generic methods), concrete impls, bounded generic helpers with exact alpha-equivalent contracts, and inherited default method bodies with per-impl `Self`/trait-argument substitution. Remaining: associated items, blanket/generic impls, trait-object dispatch, and override specialization |
| Allocation-preserving buffer reset and bounded chunk reads | Repeated stream processing, incremental parsing, reusable file buffers | Implemented: Bytes.clear and IO.read_chunk |
| Lifetime bounds, variance and callable borrow contracts | General borrowed higher-order helpers, then borrowed scoped task captures | Implemented for slices: function outlives bounds, lifetime-aware arrow types with checked substitution, calls through values. Scoped task captures of slice views implemented. Noncapturing lambdas returning slices implemented with single-slice-input lifetime elision. Next: capturing slice-returning lambdas; borrowed records in callables and tasks |
| Result-position grades (`-> T @[1]`) | Linear resource factories and resource transfer across function boundaries | Implemented for exactly `@[1]` on owning or intrinsically linear results; threaded through generics, lambdas, arrows, traits/methods, aliases, adapters, loops, `?`, and aggregates. Bounded inference of a bare result grade from an expected @[1] arrow and grade-parameterized result aliases are implemented; see [result grades](result-grade-inference.md). Remaining: general grade inference, custom grade algebras, copyable-result transfer, grade-zero erasure, cancellation-time linear cleanup |
| Effect-row exclusion constraints | Effect-polymorphic noalloc/nosuspend helpers | Implemented for concrete forbidden-effect sets on function/method binders; every specialization is checked. No row subtraction, handlers, or general solver. See [constraints](effect-constraints.md) |
| Vector capacity reuse and explicit map chains | Repeated vector processing and defined interleaved effectful pipelines | Implemented: Vec.clear, Vec.reserve, Vec.map_chain_in_place. See [vector reuse](vector-reuse.md) |
| Bounded native allocator pool | Physical small-block reuse without changing logical allocation contracts | Implemented for size classes through 1024-byte payloads, at most 1 MiB retained physical storage, and normal-exit drain. See [allocator pool](allocator-pool.md) |
| Owned file handles and close/error contracts | Filesystem applications and todo persistence | Future work; depends on resource transfer design |
| Stable foreign-call ABI and safe wrappers | Reusing Managements dependencies and native platform libraries | Future work; depends on representation and resource contracts |
| Readiness polling and scheduler wakeups | Nonblocking I/O, then networking | Future work; chunked input alone remains blocking |
| Incremental JSON state machine | Documents larger than a whole-input buffer | Future work; can use chunked input |

The first streaming milestone has a runnable example in
[stream-copy.kush](../examples/stream-copy.kush). It does not add filesystem,
network, FFI, general lifetimes or asynchronous I/O support. Those remain
separate milestones with their own checking and validation requirements.

Validation: the streaming milestone passes 478 workspace tests, formatting and
Clippy on Boat. Reference tests verify a single allocation and no buffer
growth across repeated reads, short reads, EOF and failures. Native/reference
output comparisons cover binary input and input larger than the buffer.
