# Struct update syntax (`S { f: v, ..base }`)

Status: implemented (STRUCT-UPDATE, 2026-11-06; Rust semantics approved by
the user). Tests: `crates/kush/tests/struct_update.rs`,
`crates/kush/tests/field_privacy.rs`.

```kush
struct Config { retries: i64, verbose: Bool, name: Bytes }

fn louder(c: Config) -> Config ! {} {
    Config { verbose: true, retries: c.retries + 1, ..c }
}
```

A record literal may end with `..base`. The fields it names get the written
values; every other field comes from `base`, which must be a value of the same
struct type (not a reference) and is consumed. `S { ..base }` with no fields
is allowed. `..base` must come last and takes no trailing comma; type
arguments come from the base, so `S.<T> { .., ..base }` is rejected.

- **Order.** `base` is evaluated first (into a temporary unless it is a local
  variable), then the field values in source order, then `base` is consumed.
  A field value may therefore read the base: `retries: c.retries + 1, ..c`.
- **Ownership.** The kept fields move from the base into the new record. A
  replaced owned field of the base is dropped. A replaced linear field is
  rejected (the base's value would be discarded unseen); a linear field that
  is kept moves into the new record.
- **Privacy.** Like a full literal, an update outside the struct's module
  needs every field to be `pub` (FIELD-PRIVACY, [projects.md](projects.md)).
- **Facts.** The prover knows each field of the result: a replaced field
  equals its value and a kept field equals the base's field. `let x = S { .. }`
  (a plain literal or an update) records `x.f` for every scalar field,
  including fields of nested literals, so postconditions such as
  `ensures { result.a == s.a + by && result.b == s.b }` are proved.

Lowering: `{ let t = base; let v1 = e1; ..; match t { S { f1: old, g: k, .. } =>
S { f1: v1, g: k, .. } } }` in the checked IR, so ownership, both backends and
the cleanup rules see ordinary lets and a one-arm match.
