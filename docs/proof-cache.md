# Proof cache

Almost all of the front end's time on a typical project is linear-arithmetic
proof search (`facts.rs`): a few thousand small Fourier–Motzkin systems for
overflow elision, index proofs and postconditions. Most belong to library code
that does not change between builds. On the two benchmark projects it was 80
of 86 ms and 48 of 55 ms.

`proof_cache.rs` remembers the outcome of each system on disk, so later builds
of any project by the same compiler skip the search. `kush check` on
`benchmarks/checked-loops` goes from 86 ms to 20 ms.

## What is stored, and why it cannot make the checker unsound

- The key is a 128-bit hash of the system with its terms renamed to their rank
  in term order. Elimination depends only on that order and on row order, so
  two systems with the same key are searched identically.
- For a rational refutation the entry holds only which rows were combined and
  with what multipliers. On a hit the certificate is rebuilt from the
  *current* rows and checked by the same `verify_farkas` used elsewhere. If it
  does not verify, the search runs as if there were no entry.
- For the integer fallback only failures are stored; a proof is always
  searched again.
- A stored "no proof" is the one thing taken on trust. A wrong one (file
  damage that survives the per-record checksum, or a hash collision) could
  reject a program that should be accepted. It cannot accept one.

Entries are tied to the exact compiler binary (path, size, modification time),
because another solver version may find different proofs within its budgets.

## Files and controls

The cache is `$XDG_CACHE_HOME/kush/proofs-v1` (default
`~/.cache/kush/proofs-v1`), one append-only file per compiler binary, private
to the user, never followed through a symlink, the same rules as the runtime
cache. A file over 16 MiB is started over, and only the 32 most recently used
files are kept.

| Variable | Meaning |
| --- | --- |
| `KUSH_NO_PROOF_CACHE` | Do not read or write the cache. |
| `KUSH_PROOF_CACHE=dir` | Use another directory. |

Results are identical with and without the cache; only the time differs. The
first build with a new compiler binary pays the full search once.
