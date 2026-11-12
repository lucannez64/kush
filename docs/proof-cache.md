# Proof search speed and the proof cache

Almost all of the front end's time on a typical project is linear-arithmetic
proof search (`facts.rs`): a few thousand small systems for overflow elision,
index proofs and postconditions. On `benchmarks/checked-loops`, checking took
730 million instructions, 90% of them in that search; parsing was under 1%
and ownership checking about 1%.

Two things changed that. Neither changes what a valid proof is: every
certificate is still checked by the same verifier.

## A faster search

Measured as instructions for `kush check` on `benchmarks/checked-loops` with
nothing remembered: 730 M before, 228 M after.

- **Unprovable goals stop early.** Most range questions ("can `a + b`
  overflow?") have no proof, and showing that used to mean exhausting the
  rational and integer search budgets. The search now first tries to exhibit
  an integer point that satisfies every row (`has_integer_point`). A system
  with such a point has no refutation of any kind, so the search can stop.
  Finding a point is a heuristic; accepting one is exact, since it is checked
  against every row.
- **Unrelated facts are left out.** Rows only combine through a shared term,
  so a refutation lies within one connected component of the system. The
  rational search runs per component, and the integer search separates the
  rows connected to the goal from the rest. Most facts in scope have nothing
  to do with a given goal.
- **Elimination rows are sorted vectors** merged in one pass, not trees.

The documented size limits (terms and rows per system, integer terms) still
apply to the whole system. The elimination pair budget and the integer node
and cut budgets now apply per part, so a search can succeed where the joint
one ran out of budget. When a system has several contradictions, the one
found first can differ from before, because parts are tried in order of their
first row. A search result is now checked before it is returned (a
combination whose multipliers overflow is not a proof), so an uncheckable
contradiction in one part no longer hides a good one in another. `facts::tests` compares the component search with plain elimination
on 400 generated systems and checks that a reported integer point never
coincides with a refutation.

## The cache

`proof_cache.rs` remembers the outcome of each system on disk, so later builds
of any project by the same compiler skip the search: 228 M instructions
without it, 86 M with it (about 20 ms).

### What is stored, and why it cannot make the checker unsound

- The key is a 128-bit hash of the system with its terms renamed to their rank
  in term order. Elimination depends only on that order and on row order, so
  two systems with the same key are searched identically.
- For a rational refutation the entry holds only which rows were combined and
  with what multipliers. On a hit the certificate is rebuilt from the
  *current* rows and checked (`refutes`: positive denominator, non-negative
  multipliers, no overflow, all terms cancel, negative bound). If it does not
  check, the search runs as if there were no entry and its outcome replaces
  the entry. Every certificate is also verified against the real context at
  the end of checking, exactly as before.
- For the integer fallback only failures are stored; a proof is always
  searched again.
- A stored "no proof" is the one thing taken on trust. A wrong one (file
  damage that survives the per-record checksum, or a hash collision) could
  reject a program that should be accepted. It cannot accept one.

Entries are tied to the exact compiler binary (path, size, modification time),
because another solver version may find different proofs within its budgets.

### Files and controls

The cache is `$XDG_CACHE_HOME/kush/proofs-v1` (default
`~/.cache/kush/proofs-v1`), one append-only file per compiler binary, private
to the user, the same rules as the runtime cache; neither the directory nor
the file is used if it is a symlink or not what it should be. A file over
4 MiB is started over, only the 32 most recently used files are kept, and a
file with a damaged record (a build killed mid-write) is cut back to its
intact prefix the next time it is opened.

| Variable | Meaning |
| --- | --- |
| `KUSH_NO_PROOF_CACHE` | Do not read or write the cache. |
| `KUSH_PROOF_CACHE=dir` | Use another directory. |

Results are identical with and without the cache; only the time differs. The
first build with a new compiler binary pays the full search once.
`KUSH_NO_PROOF_CACHE` turns off the files; outcomes are still remembered
within one compiler process.

The binary is identified by path, size and modification time. A different
compiler installed over the old one with all three unchanged would inherit
its entries, which could reject a provable goal until the directory is
cleared; it could not accept an unprovable one.
