# The Kush kernel in Kush

*Kush checks its own kernel.* A port of the dependent logical kernel
(`crates/kush/src/kernel.rs`) to Kush, in the spirit of Lean4Lean. Design:
[docs/kernel-in-kush.md](../../docs/kernel-in-kush.md).

Status: the term store, reader and printer (KIK-STORE), binder operations
(KIK-SUBST), reduction (KIK-NORMAL) and type checking (KIK-CHECK). It checks
every declaration of the corpus files without data families and gives the
same answers as the Rust kernel on them and on a file of typing cases, most
of them rejections; data families come next (KIK-DATA).

```sh
kush core ../induction.kush > induction.kcore        # Rust: dump a checked module
kush run --manifest-path Kush.toml -- check induction.kcore      # Kush: check and answer every item
kush run --manifest-path Kush.toml -- print induction.kcore      # Kush: read and print it back
kush run --manifest-path Kush.toml -- normalize induction.kcore  # Kush: answer normalize queries
kush kernel induction.kcore                                      # Rust: the same answers
kush test --manifest-path Kush.toml
```

- `src/store.kush`: the hash-consed store. Every object is an interned list
  of `i64` cells, so equal objects have equal ids and ids never move.
- `src/term.kush`: term, level, natural, name and list objects; levels are in
  the Rust kernel's canonical form.
- `src/reader.kush`, `src/printer.kush`: the
  [exchange format](../../docs/kernel-exchange.md), printed exactly as the
  Rust side prints it.
- `src/subst.kush`: shifting, substitution, parallel rewriting of outer
  binders and universe instantiation, as one traversal that skips closed
  subterms (each term records its free-variable range) and visits each shared
  subterm once per binder depth.
- `src/engine.kush`: the kernel state (store, global environment, step and
  nesting budgets).
- `src/normal.kush`: weak head and full normalization: beta, delta at the
  reference's universe levels, numerals, lazy `NatElim`, `Transport` and `J`
  on `refl`, and constructor reduction of `IndElim`.
- `src/check.kush`: inference, checking and the lazy conversion check
  (proof irrelevance, eta, numerals against `succ`), and `define`.
- `src/error.kush`: kernel error codes.
- `src/main.kush`: the command line.

The Rust test `crates/kush/tests/kernel_in_kush.rs` runs the package tests
and checks that every exchange file dumped from the example corpus prints back
byte for byte.
