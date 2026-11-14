# The Kush kernel in Kush

*Kush checks its own kernel.* A port of the dependent logical kernel
(`crates/kush/src/kernel.rs`) to Kush, in the spirit of Lean4Lean. Design:
[docs/kernel-in-kush.md](../../docs/kernel-in-kush.md).

Status: done (plan node KERNEL-IN-KUSH). The kernel checks every
declaration of the example corpus, including indexed data families, `prop`
families and dependent elimination, and gives the same answer as the Rust
kernel on every item of the corpus, of its mutants, of hand-written typing and
data cases, and of seeded generated terms (`scripts/kernel-diff.sh`). It also
checks a specification of its own syntax (`spec/scoped.kush`), and its
substitution is tested against that specification.

```sh
kush core ../induction.kush > induction.kcore        # Rust: dump a checked module
kush run --manifest-path Kush.toml -- check induction.kcore      # Kush: check and answer every item
kush run --manifest-path Kush.toml -- print induction.kcore      # Kush: read and print it back
kush run --manifest-path Kush.toml -- normalize induction.kcore  # Kush: answer normalize queries
kush kernel induction.kcore                                      # Rust: the same answers
kush test --manifest-path Kush.toml
```

- `src/store.kush`: the hash-consed store. Every object is an interned list
  of `i64` cells, so equal objects have equal ids and ids never move;
  `mark`/`rewind` free everything created since a mark.
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
  (eta, numerals against `succ`, and proof irrelevance, tried last because it
  is the only step that infers types), `define`, and `define_data` with
  `IndElim` typing.
- `src/data.kush`: telescope construction for data families (positivity
  occurrences, level instantiation, branch and constructor types).
- `src/error.kush`: kernel error codes.
- `src/api.kush`: the interface for clients such as a tactic engine:
  checking, reduction and conversion in a context, `abstract` and
  `instantiate`, and inspectable failures.
- `src/main.kush`: the command line.
- `spec/scoped.kush`: a specification of the kernel's syntax in the logical
  fragment: well-scoped terms `Tm<n>`, renaming, weakening and substitution
  typed so that they preserve scope, and their equational lemmas (up to
  `subst0(shift t, u) = t`). Both the Rust kernel and this kernel check it.

## Proved or attacked

`kush fuzz` ([proof fuzzing](../../docs/proof-fuzz.md)) attacks every check
the prover leaves in place. Each function with such a check is called
directly, the store and the kernel built by `store.new()` and `engine.new()`
(their fields are private, so only their constructors make them). Two
`#[fuzz]` entries in `tests/main.kush` read arbitrary bytes as an exchange
file, which reaches the checks a fresh kernel and random ids cannot:
`read_any`
prints what it read, `check_any` admits and answers every item. Random
bytes alone never get through the reader, so they are seeded from
`fuzz/corpus/`: `kush core` dumps of six examples (among them `universes`
for universe levels, `finite-proofs` and `logical-data` for inductive
families), 700 definitions (enough to grow the name table) and a
9000-step recursion (enough objects to rebuild the store's table).

```sh
kush fuzz --runs 1000 --report     # about 1 minute 30 seconds
```

Of 316 checks (standard-library checks are not counted), 78 are proved and
222 attacked: 95% proved or attacked (29% without the entries or the record
generators). Nothing reached through the entries failed. The 43
counterexamples are local: reader helpers (`skip`, `atom_end`, `word`)
called directly with a negative offset or with `start = i64::MIN`, and
store, term and normalizer functions given object ids a fresh store does
not hold. Turning the reader's into proofs needs `0 <= at` facts across the
reader (an `ensures { result >= 0 }` on each parser), which is left for
later.

The Rust test `crates/kush/tests/kernel_in_kush.rs` runs the package tests
and checks that every exchange file dumped from the example corpus prints back
byte for byte.
