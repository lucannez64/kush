# Native release optimization ablation

Host: AMD Ryzen 5 PRO 5675U with Radeon Graphics; pinned CPU 11; 7 samples after two warmups.

Workload: 2097152 elements × 4 batches. Fresh processes and shuffled implementation order.

| Build | Median wall ms | Median peak RSS KiB |
|---|---:|---:|
| Kush / default | 159.136 | 18604 |
| Kush / previous release | 74.841 | 18548 |
| Kush / speed only | 125.054 | 18616 |
| Kush / callback inlining only | 76.159 | 18568 |
| Kush / release (speed + inlining) | 38.340 | 18616 |
| Rust CLIF O3 / manual fusion | 60.913 | 18796 |
| Rust CLIF O3 / iterator chain | 194.556 | 18816 |

## Separate phase probes

| Build | Initialize ms | Transform ms | Checksum ms |
|---|---:|---:|---:|
| kush-default | 48.199 | 93.064 | 11.590 |
| kush-previous-release | 49.476 | 7.955 | 15.898 |
| kush-release | 18.576 | 8.298 | 7.188 |
| rust-manual | 29.708 | 16.737 | 9.673 |

Phase probes contain explicit clock calls, use shuffled order, and run in separate binaries. Their medians need not sum to end-to-end medians. Finalization/output/startup are outside those phases.

Both Rust and Kush use Cranelift, with different frontends/settings/standard libraries. RSS is process residency, not live payload. This ablation does not rerun the safety matrix; correctness, safety and ABI validation are covered by the native_release test target and the full compiler gate. See docs/native-optimizations.md and the benchmark README for eligibility and limitations.

## C runtime cache build timings

Same compiler and release source, seven shuffled samples per mode on CPU 11.
Warm runtime cache: **236.747 ms** median; cache disabled: **1040.929 ms**.
The initial cold-cache build took 1088.139 ms (one sample, not a median).
Execution checks are outside the build timer. See `build-time.json` for raw
samples, command, compiler/source hashes and scope. No Kush object/checker
cache is involved; warm builds still check and compile the source and link.

The previous-release binary hash matches the archived release-2026-11-03
cohort, and the generated workload source hash is unchanged. Comparison
controls were rerun together, rather than compared across separate sessions.
