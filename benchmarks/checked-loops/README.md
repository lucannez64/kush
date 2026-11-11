# Checked loops: Kush versus Rust on LLVM

Three array kernels in which every `+`, `-` and `*` is overflow-checked in
Kush: a sum, a dot product, and a scale into a second array followed by a sum.
The Rust program is the same code, built with and without
`-C overflow-checks=yes`. It measures what
[deferred overflow checks](../../docs/deferred-overflow.md) recover.

```sh
kush build --manifest-path benchmarks/checked-loops/kush/Kush.toml -o kush-llvm --release --backend llvm
kush build --manifest-path benchmarks/checked-loops/kush/Kush.toml -o kush-immediate --release --backend llvm --no-deferred-overflow
rustc --edition 2024 -C opt-level=3 -C panic=abort benchmarks/checked-loops/rust/main.rs -o rust
rustc --edition 2024 -C opt-level=3 -C panic=abort -C overflow-checks=yes benchmarks/checked-loops/rust/main.rs -o rust-checked

# elements, repetitions, kernel (0 sum, 1 dot, 2 scale then sum)
./kush-llvm 4096 200000 0
```

Every variant must print the same number for the same arguments. The inputs
are small mixed-sign values, so nothing overflows and every certificate holds.
Results from one machine are in
[docs/llvm-backend.md](../../docs/llvm-backend.md#measurements); they are
workload-specific, not a language ranking.
