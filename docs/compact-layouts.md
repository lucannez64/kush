# Compact native records and vectors

Nonempty nominal structs have no runtime discriminator. Their native words are
exactly their fields in declaration order. For example, `struct Node { id: i64,
revision: i64 }` occupies 16 payload bytes rather than 24. A real enum still
needs its tag. Empty structs, tuple layouts, anonymous structural rows, inline
arrays, dynamic arrays and opaque foreign resources retain their existing ABI.
These are compiler-private representations, not a C or Rust aggregate ABI.

The checker supplies each pattern's physical tag presence and field offsets.
Native construction, matching, field access, coercion and cleanup use the same
layout rule. The reference evaluator keeps its abstract constructor identity,
but resolves word offsets using that rule. Nested first fields can now share
an offset of zero; reference assignment also checks the replacement's type
before deciding which nested field to replace.

Ordinary native `Vec<T>` storage starts with length and capacity (16 bytes).
Element width comes from the monomorphized `T` at every runtime operation; it
is no longer stored once per allocation. Maps, including narrowing/widening
maps, produce a new static element type. Subsequent reads, growth, slices,
place references and destruction use that type's width. The evaluator's
physical-capacity model uses the same 16-byte header for fallible-growth
budget decisions. Stateful user-allocator `AllocVec` has a separate protocol
and retains its own metadata.

This leaves the existing 16-byte allocation header, padding and bounded pool
unchanged. It does not erase ownership, borrow checks, effects or fallible
allocation semantics. A smaller value can legitimately need fewer physical
growths; layout-dependent failure-injection tests must select sizes that still
cross the intended boundary.

`tests/record_layout.rs` covers nested zero-offset writes, owning first fields
through enum patterns and structural conversion, and record vectors compacted
into scalars. Existing borrowing, traits, allocator, vector and memory tests
exercise the shared ABI paths. Validation and measured results are recorded
with the benchmark checkpoint rather than inferred from field sizes alone.

For an application-level comparison, the JSON memory harness also supports
`--inline-metadata`, removing `Box<Node>` explicitly in both languages. This
is not an automatic box-elimination optimization: boxed controls remain
available and separately measured.
