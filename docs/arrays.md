# Fixed-length inline arrays

`[T; N]` carries a literal nonnegative length in its type. An array literal in an
array context must have exactly that many elements of the expected type.

```rust
#[noalloc]
fn pair() -> [i64; 2] ! {} { [20, 22] }

fn main() -> i64 ! {panic} {
    let values = pair();
    values[0] + values[1]
}
```

Run `cargo run -p kush -- run examples/arrays.kush` to print 42.

Arrays are inline values and construction/indexing do not allocate. Passing and
returning them uses the existing aggregate ABI. The current layout includes a
private tag word and is limited to 32 words including nested elements.
A length is a compile-time expression: integer literals, `N: Nat` const
parameters, admitted total logical computations, and checked
`+`/`-`/`*`/`/`/`%` over those, such as `[i64; (1 + 1) * 2]`,
`[T; N]`, or `[i64; add<1, 1>]`. Lengths and constant indices are evaluated
without running arbitrary runtime code; negative, overflowing, unbound, or
runtime-dependent lengths are rejected. Explicit specialization and length
inference from array arguments are supported, for example
`fn identity<T: Type, N: Nat>(xs: [T; N]) -> [T; N]`. Empty arrays and nested
arrays work. An annotation or expected return/argument type selects an inline
array; an unannotated literal continues to construct a vector.

See [dependent array lengths](dependent-indices.md) for the exact length
grammar, inference rules, symbolic lengths in generic data, and the alias
interaction.

Constant integer indexing is checked during compilation. A dynamic index
`values[index]` lowers to a checked view read and requires the `panic` effect;
it is bounds-checked at run time in both execution models. Either form copies
the element, so owned or linear elements cannot be indexed. Move them through
exact-length destructuring instead:

```rust
let owners: [Box<i64>; 2] = [Box.new(20), Box.new(22)];
let [left, right] = owners;
Box.take(left) + Box.take(right)
```

Array ownership is structural. Dropping an array recursively destroys its owned
elements; linear elements require consumption. Early returns and partial literal
construction use the existing ownership tracking. Arrays cannot store borrowed
references, slice views, or borrowed or mixed records (keep a
lifetime-parameterized record in a lexical value; see [borrowed records](borrowed-records.md)), and
slice patterns remain exact-length array
destructuring without named rest captures. There is no implicit conversion
between different lengths or to/from vectors.

Immutable `&[T]` views over arrays, vectors, and byte buffers are supported;
see [borrowed slices](slices.md) for sub-slicing, checked/proof-based access,
and their lexical lifetime rules.

This adds concrete length-indexed storage, compile-time const length
parameters, symbolic lengths in generic records/enums/aliases, checked
kernel-normalized length/index computation, and explicit specialization or
narrow length inference. Runtime-sized inline arrays (for example a function
returning `[T; n]` for a runtime `n`) remain rejected rather than lowering to an
unsafe dynamic stack layout; use `Vec<T>` or an immutable `&[T]` view instead.
General dependent propositions over runtime values and proof-based dynamic
indexing over arbitrary array expressions also remain out of scope. See
[dependent array lengths and indices](dependent-indices.md).
