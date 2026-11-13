# Arbitrary-precision naturals: `std.natural`

Status: implemented (STD-BIGNAT). [`std.natural`](../crates/kush/std/natural.kush)
provides the numerals of the logical kernel ([kernel.md](kernel.md)) to Kush
programs, first of all the [kernel written in Kush](kernel-in-kush.md), which
must read, compare and print the same literals as the Rust kernel.

The representation matches `crates/kush/src/natural.rs`: little-endian base
10^9 limbs in a private `Vec<i64>`, zero with no limbs and a nonzero top limb
otherwise, so every value is canonical. There is no digit limit, as in the
Rust kernel: values are bounded by memory, and the kernel bounds its own work
with fuel charged per limb.

```rust
use std.natural;
use std.natural.Natural;

let n = match natural.parse(&Bytes.from("18446744073709551616")) {
    Result.Ok(n) => n,
    Result.Err(code) => return code,
};
let m = natural.successor(&n);
match natural.predecessor(&m) { Option.Some(p) => .., Option.None => .. }
natural.compare(&n, &m);                 // -1, 0 or 1
io.write(io.stdout(), &natural.format(&m));
```

| Function | Result |
| --- | --- |
| `zero()`, `from_i64(v)` | a natural; `from_i64` of a negative value is `ERANGE` |
| `parse(&Bytes)` | `Result<Natural, i64>`: one or more ASCII digits, leading zeros allowed, no sign; `EINVAL` (22) for anything else |
| `format(&n)`, `format_into(out, &n)` | decimal digits, no leading zeros |
| `successor(&n)` | `n + 1` |
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
values of several limbs and values far past the old 4096-digit budget, and checks that every
allocation is freed.
