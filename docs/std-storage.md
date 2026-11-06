# Storage building blocks: `std.file`, `std.crc32`, `std.bytemap`

Added for the `kush-kv` store (plan nodes STD-FILE, STD-CRC32, STD-BYTEMAP).

- [`std.file`](../crates/kush/std/file.kush): a `#[linear]` open file with
  positioned `read_at`/`write_at`, `sync` (`fsync`), `truncate`, `size`,
  `close` and `sync_dir`. The checker rejects a file that is not closed on
  every path, closed twice, dropped, or built outside the module. Host calls
  and errno values are in [host-api.md](host-api.md#open-files-stdfile).
  Tests: `crates/kush/tests/std_file.rs`.
- [`std.crc32`](../crates/kush/std/crc32.kush): CRC-32 (IEEE). `of` and
  `update` take a byte range whose bounds are an erased precondition
  (`0 <= start <= end <= Bytes.len(data)`), so callers prove the range and
  the loop reads bytes with `Bytes.at`, without bounds checks.
- [`std.bytemap`](../crates/kush/std/bytemap.kush): `Map<V>` from byte keys
  to copyable values; open addressing with linear probing, FNV-1a, and
  tombstones; keys live in one arena that is compacted when removed keys
  dominate. Operations that change the map consume and return it. Iterate
  with `next_slot`, `key_into` and `value_at`.
  Tests: `crates/kush/tests/std_crc_bytemap.rs` (against `HashMap`).

Speed comes from proofs, not from removing checks: the CRC loop reads bytes
and table entries with `Bytes.at`/`Vec.at` (the table index is `x & 255`),
and map probes read one slot record with `Vec.at` after one range check per
probe. Measured in the kush-kv microbenchmark (200 000 operations, release,
2026-11-06): CRC of an 80-byte record 358 → 151 ns, map insert 791 → 491 ns,
map lookup 364 → 197 ns, against the first versions with checked reads.

Limits: the reference evaluator rebuilds a vector on each `Vec.set`, so map
workloads there must stay small (tests run large ones natively); `bytemap`
values must be copyable.
