# A prover whose tactics are effect handlers

*Tactics are ordinary Kush functions, backtracking is resuming a
continuation twice, and every proof is checked by a kernel written in Kush.*
Design: [docs/tactics-handlers.md](../../docs/tactics-handlers.md).

```text
$ kush run --manifest-path examples/tactics/Kush.toml -- "(A -> B) -> (B -> C) -> A -> C"
goal:    (A B C : Prop) -> (A -> B) -> (B -> C) -> A -> C
proof:   fun A B C (h1 : A -> B) (h2 : B -> C) (h3 : A) => h2 (h1 h3)
search:  128 choices, 100 backtracks, depth 3
kernel:  checked by the Kush kernel

$ kush run --manifest-path examples/tactics/Kush.toml -- "~(A | B) -> ~A & ~B"
goal:    (A B : Prop) -> ~(A | B) -> ~A & ~B
proof:   fun A B (h1 : ~(A | B)) => intro (fun (h2 : A) => h1 (left h2)) (fun (h3 : B) => h1 (right h3))
search:  154 choices, 107 backtracks, depth 3
kernel:  checked by the Kush kernel

$ kush run --manifest-path examples/tactics/Kush.toml -- "((A -> B) -> A) -> A"
goal:    (A B : Prop) -> ((A -> B) -> A) -> A
proof:   none up to depth 8
```

Formulas use the atoms `A`..`Z`, `->`, `&`, `|`, `~` (`~A` is `A -> False`),
`False` and parentheses; the goal quantifies over the atoms. Peirce's law
has no intuitionistic proof, so none is found. With `--kcore` the program
prints the connectives and the proof as a
[kernel exchange file](../../docs/kernel-exchange.md), which the Rust kernel
checks too: `kush kernel proof.kcore`.

## How it works

Two handlers run the search (`src/prover.kush`):

- **`Choose`**, a multishot capability (`cap multi Choose`,
  [docs/multishot-capabilities.md](../../docs/multishot-capabilities.md)).
  `perform op(n)` returns one of `0..n`; the handler resumes the rest of the
  search once per alternative and returns the first proof. A dead end is a
  choice among no alternatives, `perform op(0)`, so the handler returns to
  the last choice with alternatives left.
- **`Goal`**, a tail-resumptive handler that owns the Kush kernel
  ([examples/kernel](../kernel/README.md)). Every question a tactic asks
  (weak head normal form, definitional equality, a hypothesis's type) and
  every term it builds goes through it. Tactics therefore hold only store
  ids, plain integers, which each resumption copies.

The tactics (`src/search.kush`) are plain functions: `assumption`, `apply`
(a hypothesis whose conclusion is the goal, proving its premises), `cases`
(eliminate a hypothesis `P & Q`, `P | Q` or `False` into the goal),
`either` (one side of a disjunction), and `auto`, which introduces and
splits eagerly and chooses among the others. The driver deepens the search
from depth 1 to 8. The search may build any term; only the kernel's check of
the closed proof against the closed goal is trusted.

- `src/state.kush`: the kernel set-up (`And`, `Or` and `False` as `prop`
  data), the `Goal` queries and their handler, and the eliminator terms.
- `src/search.kush`: the tactics.
- `src/prover.kush`: the two handlers and iterative deepening.
- `src/formula.kush`: the formula reader.
- `src/show.kush`: printing goals and proofs with names (`cases h` and
  `absurd h` abbreviate the eliminator terms).
- `src/main.kush`: the command line; `tests/main.kush`: package tests.

`crates/kush/tests/tactics.rs` runs the package tests, proves a list of
tautologies, checks every proof with the Rust kernel as well, and checks that
non-theorems (Peirce's law, excluded middle, double-negation elimination)
have no proof.

```sh
kush test --manifest-path examples/tactics/Kush.toml
```
