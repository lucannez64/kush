# Arbitrary-precision naturals: `std.natural`

Status: implemented (STD-BIGNAT). [`std.natural`](../crates/kush/std/natural.kush)
provides the numerals of the logical kernel ([kernel.md](kernel.md)) to Kush
programs, first of all the [kernel written in Kush](kernel-in-kush.md), which
must read, compare and print the same literals as the Rust kernel.

The representation matches `crates/kush/src/natural.rs`: little-endian base
10^9 limbs in a private `Vec<i64>`, zero with no limbs and a nonzero top limb
otherwise, so every value is canonical. A value has at most `max_digits()`
(4096) significant decimal digits, the Rust kernel's budget.

```rust
use std.natural;
use std.natural.Natural;

let n = match natural.parse(&Bytes.from("18446744073709551616")) {
    Result.Ok(n) => n,
    Result.Err(code) => return code,
};
let m = natural.successor(&n)?;          // ERANGE (34) past the digit budget
match natural.predecessor(&m) { Option.Some(p) => .., Option.None => .. }
natural.compare(&n, &m);                 // -1, 0 or 1
io.write(io.stdout(), &natural.format(&m));
```

| Function | Result |
| --- | --- |
| `zero()`, `from_i64(v)` | a natural; `from_i64` of a negative value is `ERANGE` |
| `parse(&Bytes)` | `Result<Natural, i64>`: one or more ASCII digits, leading zeros allowed, no sign; `EINVAL` (22) for anything else, `ERANGE` (34) past the budget |
| `format(&n)`, `format_into(out, &n)` | decimal digits, no leading zeros |
| `successor(&n)` | `Result<Natural, i64>`, `ERANGE` past the budget |
| `predecessor(&n)` | `Option<Natural>`, `None` at zero (no saturation) |
| `compare`, `equal`, `is_zero`, `digits` | comparisons and the decimal digit count |
| `to_i64(&n)` | `Option<i64>`, `None` when it does not fit |
| `work(&n)` | the limb count (at least 1), the unit the kernel charges numeric work in |
| `copy(&n)` | an independent copy; a `Natural` owns its limbs and moves |

This is exactly the arithmetic the kernel needs. There is no addition,
multiplication or division yet; they would be added here when a client needs
them.

Tests: `crates/kush/tests/std_natural.rs` runs every operation on both
backends against the Rust `Natural`, over limb boundaries, the `i64` edges,
values of several limbs and the digit budget, and checks that every
allocation is freed.
