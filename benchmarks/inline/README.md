# Direct call inlining (NATIVE-INLINE)

`policy-predicates.kush` is the VELA client share policy written like the Rust
crate (small predicate functions); `policy-written-out.kush` has the
conditions written out in `plan`. Both run 10^8 decisions and print the
checksum and picoseconds per decision.

```sh
kush build policy-predicates.kush -o /tmp/p --release                     # inlining on
kush build policy-predicates.kush -o /tmp/p-off --release --no-inline-calls
/tmp/p; /tmp/p-off
```

Results and the other benchmarks: `docs/native-optimizations.md`.
