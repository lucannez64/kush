# Kernel exchange format

Status: implemented (KIK-EXCHANGE). A small canonical S-expression syntax for
kernel terms, declarations and queries. The Rust kernel writes and answers it;
the [kernel written in Kush](kernel-in-kush.md) reads and answers it too, so
the two kernels can be compared with a text diff. Implementation:
`crates/kush/src/exchange.rs`; tests: `crates/kush/tests/kernel_exchange.rs`.

```sh
kush core examples/induction.kush > induction.kcore   # dump a checked module
kush kernel induction.kcore                           # answer it with the Rust kernel
```

`kush core` checks the file (logic-only files with the logical checker; files
with executable code through the executable checker's logical half,
`kush::executable::logical_module`), then prints the admitted environment in
admission order, one declaration per line, followed by a `normalize` query for
every definition (universe parameters instantiated at level 0). `kush kernel`
reads any exchange file, starts from an empty kernel, and prints one line per
item. Neither command adds anything to the trusted kernel: the dump is a
printer, and the answers go through the ordinary checking API.

## Syntax

An atom is a maximal run of bytes other than whitespace, `(`, `)` and `;`. `;`
starts a comment to the end of the line. Names are atoms (`List::Cons`,
`add#12`); they are never confused with keywords because a global is always
written `(global NAME ...)`.

```text
level ::= N | (u I) | (succ level) | (max level level ...)

term  ::= (var I) | (global NAME level...) | (sort level) | prop
        | (pi A B) | (lam A b) | (app f a)
        | nat | zero | (succ t) | (lit N)
        | (natelim motive zero step value)
        | (eq A x y) | (refl A x)
        | (transport A x y motive proof value)
        | (eqelim A x y motive refl proof)
        | (indelim DATA motive (branch...) scrutinee)
        | (scalar i64|Bool|Unit) | (i64 N) | (bool true|false) | unit

item  ::= (def NAME LEVELS TYPE VALUE)
        | (data NAME LEVELS type|prop (PARAM...)
              (ctor NAME (LOCAL...) (FIELD...) (RESULT...)) ...)
        | (check TERM TYPE) | (infer TERM) | (normalize TERM)
```

`(var I)` is a zero-based de Bruijn index, as in the kernel. `LEVELS` is the
number of universe parameters, referred to as `(u 0)`, `(u 1)`, .... A `data`
item is the `IndexedDataSpec` that admits the family; the family's universe is
recomputed by the kernel, not read. `(lit N)` is an arbitrary-precision
natural; `(lit 0)` reads as `zero`.

The printer is canonical: levels are printed from their canonical form (so
`(max 1 (succ (u 0)))` prints as `(succ (u 0))`), numerals are compact, and
every item is one line. Printing is the identity on a dump, which the tests
check over the example corpus.

## Answers

| Item | Answer line |
| --- | --- |
| `def`, `data` | `ok NAME`, `reject NAME` or `budget NAME` |
| `check` | `ok`, `reject` or `budget` |
| `infer` | `: TYPE` (normalized) or `reject` / `budget` |
| `normalize` | `= TERM` or `reject` / `budget` |

A rejected declaration is not admitted, so later items that use it are
rejected as well. `budget` means the kernel ran out of steps or nesting depth:
not a verdict. Error messages are deliberately not part of the answer, since
two implementations may report different first errors; the comparison is on
verdicts and normal forms. Malformed input (bad syntax, unknown forms, wrong
arity, nesting deeper than 1024) is an error of the command, not a verdict.
