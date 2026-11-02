# User-defined grade algebras

Status: implemented for the executable subset. A `grade algebra` declaration
introduces a finite carrier with explicit total `add` and `mul` tables. The
checker validates the semiring laws by exhaustive enumeration before any
annotation may use the algebra; it never assumes a law.

## Syntax

```kush
algebra Usage {
    elements { None, Once, Twice }
    zero = None;
    one = Once;
    add {
        None + None = None, None + Once = Once, None + Twice = Twice,
        Once + None = Once, Once + Once = Twice, Once + Twice = Twice,
        Twice + None = Twice, Twice + Once = Twice, Twice + Twice = Twice,
    }
    mul {
        None * None = None, None * Once = None, None * Twice = None,
        Once * None = None, Once * Once = Once, Once * Twice = Twice,
        Twice * None = None, Twice * Once = Twice, Twice * Twice = Twice,
    }
}
```

An annotation names an element with a dot path:

```kush
fn main() -> i64 ! {panic} {
    let x: i64 @[Usage.Twice] = 21;
    x + x
}
```

The declaration is program-global by simple name in this subset. Duplicate
algebra names, duplicate element names, unknown elements, missing or repeated
table rows, and a wrong `zero`/`one` are rejected.

## Semantics

- `elements` is the finite carrier.
- `add` and `mul` must be total on the carrier; every ordered pair must appear
  exactly once.
- `zero` is the additive identity and `one` is the multiplicative identity.
- The checker verifies commutativity and associativity of both operations,
  distributivity of `*` over `+`, the two identities, and zero annihilation.
- Usage counting is performed in the declared algebra: a local graded by an
  element accumulates observed uses through `add`, and call-demand composition
  uses `mul`. An exact obligation compares the accumulated element with the
  annotated element on every normal path.
- `@[Algebra.One]` is accepted as a result-transfer contract (owning or
  must-use copyable), because it is the algebra's multiplicative identity.
  `@[Algebra.Zero]` is the algebra's zero and is subject to the same
  observation restriction as builtin `@[0]`.
- Grade inference currently solves builtin finite/natural equations only.
  Custom-algebra grades are accepted with explicit specialization; a custom
  target is outside the affine solver rather than being guessed.
- Elements are compile-time metadata. They add no runtime representation, tag,
  allocation, ABI change, or runtime check.

The finite enumeration is the decidable checking boundary: tables are bounded
by a finite carrier and law checking is cubic in the number of elements.
Non-finite carriers, carrier laws that cannot be enumerated, and custom
comparison/joins beyond the declared semiring are not supported.

## Allocation and static descriptions

The lowered algebra tables are static compiler metadata. They are leaked once
per compiled program so a `Grade` stays `Copy` and can carry its display names
and tables. This is compiler-process memory, not program runtime memory; no
allocation appears in `--stats` and program allocation counts are unchanged.

## Tests

`crates/kush/tests/grade_algebras.rs` covers a saturated three-level algebra in
both backends, algebra elements as parameter and result contracts, exact-use
failures, bare/unknown element names, missing and repeated table rows,
identity/law violations, duplicate declarations, and malformed declarations.
