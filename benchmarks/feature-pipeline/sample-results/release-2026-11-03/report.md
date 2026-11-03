# Native release optimization ablation

Host: AMD Ryzen 5 PRO 5675U with Radeon Graphics; pinned CPU 11; 7 samples after two warmups.

Workload: 2097152 elements × 4 batches. Fresh processes and shuffled implementation order.

| Build | Median wall ms | Median peak RSS KiB |
|---|---:|---:|
| Kush / default | 161.274 | 18576 |
| Kush / speed only | 157.479 | 18556 |
| Kush / callback inlining only | 77.645 | 18616 |
| Kush / release (speed + inlining) | 74.736 | 18588 |
| Rust CLIF O3 / manual fusion | 61.495 | 18772 |
| Rust CLIF O3 / iterator chain | 192.774 | 18800 |

## Separate phase probes

| Build | Initialize ms | Transform ms | Checksum ms |
|---|---:|---:|---:|
| kush-default | 52.272 | 92.521 | 13.752 |
| kush-release | 49.171 | 7.801 | 15.944 |
| rust-manual | 29.618 | 16.781 | 9.563 |

Phase probes contain explicit clock calls, use shuffled order, and run in separate binaries. Their medians need not sum to end-to-end medians. Finalization/output/startup are outside those phases.

Both Rust and Kush use Cranelift, with different frontends/settings/standard libraries. RSS is process residency, not live payload. This ablation does not rerun the safety matrix; correctness, safety and ABI validation are covered by the native_release test target and the full compiler gate. See docs/native-optimizations.md and the benchmark README for eligibility and limitations.
