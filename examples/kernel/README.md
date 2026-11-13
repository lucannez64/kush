# The Kush kernel in Kush

*Kush checks its own kernel.* A port of the dependent logical kernel
(`crates/kush/src/kernel.rs`) to Kush, in the spirit of Lean4Lean. Design:
[docs/kernel-in-kush.md](../../docs/kernel-in-kush.md).

Status: the term store, reader and printer (KIK-STORE). Type checking comes
next (KIK-SUBST, KIK-NORMAL, KIK-CHECK).

```sh
kush core ../induction.kush > induction.kcore        # Rust: dump a checked module
kush run --manifest-path Kush.toml -- print induction.kcore   # Kush: read and print it back
kush test --manifest-path Kush.toml
```

- `src/store.kush`: the hash-consed store. Every object is an interned list
  of `i64` cells, so equal objects have equal ids and ids never move.
- `src/term.kush`: term, level, natural, name and list objects; levels are in
  the Rust kernel's canonical form.
- `src/reader.kush`, `src/printer.kush`: the
  [exchange format](../../docs/kernel-exchange.md), printed exactly as the
  Rust side prints it.
- `src/main.kush`: the command line.

The Rust test `crates/kush/tests/kernel_in_kush.rs` runs the package tests
and checks that every exchange file dumped from the example corpus prints back
byte for byte.
