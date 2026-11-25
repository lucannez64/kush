# `std.bincode`: a bincode 1.x-compatible binary codec

Plan node STD-BINCODE. Source:
[`crates/kush/std/bincode.kush`](../crates/kush/std/bincode.kush), tests:
[`crates/kush/tests/std_bincode.rs`](../crates/kush/tests/std_bincode.rs).

Rust's `bincode` crate was marked unmaintained in January 2026
(RUSTSEC-2025-0141); its 1.3 default ("legacy") wire format is stable, so
`std.bincode` implements exactly that format in Kush, letting Kush programs
exchange values byte-for-byte with Rust programs on `bincode::serialize` /
`bincode::deserialize`.

## Wire format

| Value | Bytes |
| --- | --- |
| `u8..u64`, `i8..i64` | fixed width, little-endian two's complement |
| `Bool` | one byte, 0 or 1 |
| `Char` | u32 LE scalar value |
| `Option` | u8 tag (0 = `None`, 1 = `Some`) + payload |
| `Result` | u8 tag (0 = `Ok`, 1 = `Err`) + payload |
| enum | u32 LE variant index + fields |
| `str`, `String`, `Bytes`, sequences, maps | u64 LE length + elements |
| tuples, structs | fields in declaration order |

Kush has no 128-bit integers and floats have no bit access, so `u128`/`i128`
do not exist here and `f32`/`f64` are not encodable bit-exactly.

## API shape

Encoding appends to a `Bytes` buffer, consume-and-return like `Bytes.push`:
`put_u8`..`put_i64`, `put_bool`, `put_char`, `put_len` (the u64 length prefix),
`put_variant` (the u32 enum index), `put_bytes`, `put_str`, and the generic
`put_option` / `put_result`, which take the element encoder as a
`fn(Bytes, T) -> Bytes ! {alloc}`.

Decoding walks a `Decoder<'a>` cursor (a record holding `&'a Bytes` and a
position) through `&mut`: every read advances the cursor and returns
`Result<T, Error>`, so truncated or malformed input is an `Err`, never a
panic. Tuples cannot hold borrowed records in Kush, which is why the cursor
is mutated in place instead of being returned in a pair.
`take_bytes`/`take_str` reject a length larger than the remaining input
(`BadLength`) instead of allocating it. `bincode.finish(&d)` rejects trailing
bytes, matching bincode's default. Structs and enums are encoded by a
user-written function per type (fields in order; variant index via
`put_variant`; `Option`/`Result` via the u8 tag from `take_tag`), since Kush
has no derive macros.

Reads use the checked `Bytes.get` after one range check per value, so decode
functions carry no proof obligations (same idiom as `std.json`).
