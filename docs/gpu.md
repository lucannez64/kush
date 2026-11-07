# GPU functions written in Kush

Status: design approved by the user 2026-11-07 (GPU-DESIGN). GPU-SUBSET is
implemented: the `#[gpu]` attribute, `GpuBuf<T>`, `GpuBuf.len/get/set`, and
the checked subset below (`crates/kush/src/gpu.rs`, tests in
`crates/kush/tests/gpu_subset.rs`). Nothing runs on a GPU yet: `Gpu.run`,
the evaluator loop, WGSL output and the Vulkan runtime are later nodes. Plan nodes: GPU-SUBSET, GPU-WRITE-DISJOINT,
GPU-EVAL-ORACLE, GPU-WGSL-EMIT, GPU-PANIC-FLAG, GPU-RUNTIME, GPU-SCOPE,
GPU-PARITY.

Goal: data-parallel code written in checked Kush runs on any Vulkan GPU, with
the same results as the reference evaluator and with Kush's panic, ownership
and effect rules intact. Cranelift has no GPU target, so `#[gpu]` functions get
a second backend; the CPU side stays on Cranelift.

## Example

```kush
#[gpu]
fn saxpy(id: u32, a: f32, x: &GpuBuf<f32>, y: &mut GpuBuf<f32>) -> Unit ! {panic} {
    GpuBuf.set(y, id, a * GpuBuf.get(x, id) + GpuBuf.get(y, id));
}

fn main() -> Unit ! {io, alloc, panic} {
    let dev = match Gpu.open() {                // Result<GpuDevice, i64>
        Result.Ok(d) => d,                      // released on drop
        Result.Err(_) => { return; },
    };
    let xs: Vec<f32> = ..;
    let ys: Vec<f32> = ..;
    let x = Gpu.upload(&dev, &xs[..]);          // GpuBuf<f32>, released on drop
    let mut y = Gpu.upload(&dev, &ys[..]);
    Gpu.run(&dev, saxpy, GpuBuf.len(&y), 2.0, &x, &mut y);
    let out: Vec<f32> = Gpu.download(&dev, &y);
}
```

## The `#[gpu]` subset (GPU-SUBSET)

The check is an allowlist over the checked IR, run before ownership: an
expression form, builtin or type it does not list is rejected, so a new
compiler feature never reaches the GPU backend by accident. CPU code may not
call a `#[gpu]` function, take it as a function value, or use `GpuBuf.*`.
Until GPU-SCOPE adds `Gpu.run`, `#[gpu]` functions are checked but never run;
the native backend compiles them as unreachable CPU code.

`#[gpu]` joins `#[noalloc]`, `#[nosuspend]` and `#[test]` in the function
attribute list (`executable.rs`). The checker rejects, with an exact
diagnostic, anything outside this subset:

| Allowed | Rejected |
| --- | --- |
| `i32`, `u32`, `f32`, `Bool`, `Unit` | `i64`/`u64`/`f64`/8- and 16-bit kinds (no WGSL equivalent; `f16` later) |
| tuples and records of allowed types | `Box`, `Vec`, `Bytes`, `String`, `&str`, arenas, allocators |
| payloadless enums and `match` on them | enums with payloads (later: tag + fields struct) |
| `let`, `let mut`, `if`, `while`, `loop`, `break` | closures, function values, `dyn`, traits with dynamic dispatch |
| calls to other `#[gpu]` functions | calls to non-`#[gpu]` functions, foreign calls, recursion (WGSL forbids it) |
| statically dispatched trait methods that are `#[gpu]` | generic functions in v1 (monomorphized later) |
| effect row within `{panic}` | `io`, `alloc`, `suspend`, declared operations, handlers |

- **Entry functions** are the ones passed to `Gpu.run`. The first parameter is
  `id: u32`. The others are scalars or records of scalars (sent as a uniform
  block), `&GpuBuf<T>` (read-only storage) or `&mut GpuBuf<T>` (read-write
  storage).
- **Helper functions** take only scalar values. WGSL allows storage-buffer
  pointers only on the entry point unless an extension is enabled, so only the
  entry function receives buffers in v1.
- A `#[gpu]` function cannot be called from CPU code; `Gpu.run` is the only way
  in. The evaluator runs it through the same entry point (see below).
- Integer literals take their contextual type as today. A literal that would
  default to `i64` inside a `#[gpu]` function is an error that asks for an
  annotation.

## Buffers

`GpuBuf<T>` is a device buffer of `T ∈ {i32, u32, f32}` stored packed, 4 bytes
per element (CPU values use one 64-bit word each, so `upload` and `download`
convert). It is an owned resource like `Box`: affine, freed on drop, never
copied. `Bool` and records are not host-shareable in WGSL; records in buffers
come later with explicit layout rules.

CPU side: `Gpu.upload(&dev, &[T]) -> GpuBuf<T>`,
`Gpu.zeroed(&dev, n: i64) -> GpuBuf<T>`,
`Gpu.download(&dev, &GpuBuf<T>) -> Vec<T>`, `GpuBuf.len(&buf) -> i64`. There is
no element access on the CPU side.

GPU side, mirroring `Slice`: `GpuBuf.len(b) -> u32`, `GpuBuf.get(b, i) -> T`,
`GpuBuf.set(b, i, v)` (only through `&mut`). The index is `u32` or `i32`; a
negative or out-of-range index panics.

## Dispatch (GPU-SCOPE)

v1 is synchronous: `Gpu.run(&dev, f, n, args...)` records the dispatch, submits
it, and waits on its fence before returning. Its borrows are ordinary call
borrows, so the existing ownership rules already stop the CPU from touching a
buffer while the GPU uses it, and prevent passing the same buffer as `&` and
`&mut`. Passing one buffer twice as `&` is allowed (two read-only bindings).

- `n: i64` invocations run, with `id` covering `0..n` exactly. The generated
  WGSL entry uses a fixed workgroup size (64), dispatches `ceil(n / 64)`
  groups (split across dimensions past the 65535 limit) and returns early when
  `id >= n`, so user code never sees an out-of-range `id`. `n` above `u32::MAX`
  panics on the CPU side.
- `Gpu.run` needs `{io, alloc, panic}` on the caller.
- Later (still under GPU-SCOPE): a `Gpu.scope` that queues several dispatches and
  waits once, with the scope holding the loans like `Thread.scope` does, plus
  waiting as a `suspend` point for cooperative tasks.

## Disjoint access (GPU-WRITE-DISJOINT)

Invocations run in parallel in any order. Two rules make every result
independent of that order:

1. A `&mut GpuBuf` is read and written only at index `id`, where `id` is the
   entry parameter, never reassigned. Reads at other indices would race with
   the invocation that owns them, so they are rejected too.
2. A `&GpuBuf` can be read at any index.

v1 accepts only the literal `id`. Later versions can accept any index the
`R-IDX-DISJOINT` facts prove injective in `id` (`id + k`, `2 * id + 1` with
uniform `k`), and atomic buffers (`GpuBuf<Atomic32>`) for reductions, which
make results depend on the order the same way CPU `Atomic` does.

These rules also make the evaluator's sequential loop (below) a correct
reference: any order gives the same buffers.

## Failures (GPU-PANIC-FLAG)

GPU code cannot unwind or abort. Every check Kush does on the CPU is kept:
integer overflow, division by zero, `MIN / -1`, shift range, buffer bounds, and
explicit `panic`. The lowering is:

- Each dispatch gets a hidden `failure` storage buffer `{ code: atomic<u32>,
  site: u32 }`. The first failing invocation stores its code and source site
  with `atomicCompareExchangeWeak`.
- A failing check sets a per-invocation `private` flag and returns a dummy
  value. After every call to a helper, the generated code checks the flag and
  returns, so the invocation does no more writes.
- After the fence, `Gpu.run` reads the failure buffer and, if it is set, raises
  an ordinary Kush panic with the site's message. Buffer contents after a
  panic are unspecified; the panic ends the program as usual.

`Int.wrapping_*` stays available for code that wants WGSL's native wrapping.

## Floating point

Kush `f32` on the CPU is strict IEEE-754. WGSL is looser, and the doc commits
to the difference instead of hiding it:

- `+`, `-`, `*`, comparisons and conversions are correctly rounded in both.
- Division, `sqrt`, `%` and other built-ins have a WGSL error bound (division
  is 2.5 ULP). Parity tests compare these with a ULP tolerance.
- The GPU may flush subnormals to zero, and NaN or infinity results are
  indeterminate in WGSL. `is_nan`/`is_infinite` are rejected in `#[gpu]` code
  in v1, since they cannot be relied on.
- `a * b + c` must not be fused into one FMA. GPU-WGSL-EMIT has to confirm that
  the SPIR-V path marks arithmetic `NoContraction`, or document the difference.

## Lowering (GPU-WGSL-EMIT)

1. After checking, collect each entry passed to `Gpu.run` and the `#[gpu]`
   helpers it reaches (acyclic, already checked).
2. Emit WGSL text: records and tuples become structs; payloadless enums become
   `u32` tags; `match` becomes `switch` or `if` chains; checked operations
   expand into their tests and failure paths; entry parameters become bindings
   in group 0 (uniform block, then buffers in order, then the failure buffer).
3. Parse and validate the WGSL with `naga`, and translate it to SPIR-V at
   compile time. A validation error is a compiler bug and is reported as an
   internal error with the generated source.
4. Embed the SPIR-V in the executable as read-only data.
   `kush build --emit-wgsl` writes the WGSL for inspection.

Emitting WGSL text instead of building naga IR directly keeps the backend
readable and debuggable; naga still gives a full validation pass.

## Runtime (GPU-RUNTIME)

The native runtime is C compiled by the compiler with `cc`. To keep that, the
GPU runtime is C over Vulkan, loaded with `dlopen("libvulkan.so.1")` on the
first `Gpu.open`, so programs that do not use the GPU, and machines without
Vulkan, are unaffected. It is compiled in only when the program uses `Gpu`
(a `KUSH_HAS_GPU` define, like `KUSH_HAS_THREADS`).

- `Gpu.open` picks the first compute-capable device and returns `Err` when
  Vulkan or a device is missing.
- Pipelines are created on the first `Gpu.run` of each entry and cached in the
  device.
- Upload and download go through a host-visible staging buffer and convert
  between 64-bit words and 4-byte elements.
- CI and Boat use Mesa's lavapipe (software Vulkan), so every test runs without
  GPU hardware.

## Reference evaluator (GPU-EVAL-ORACLE)

`kush eval` runs `Gpu.run` as `for id in 0..n { f(id, args...) }` on CPU-side
copies of the buffers, with strict IEEE `f32`, and the same panic messages.
`Gpu.open` always succeeds there. Because of the disjoint-access rules, this
one order is a correct reference for every GPU order (atomics excepted).

## Testing (GPU-PARITY)

- Checker: every rejected construct has a hostile test with its diagnostic.
- Emitter: every test program's WGSL passes naga validation.
- Parity: native (lavapipe) output equals `kush eval` output exactly for
  integers and `+ - *` floats, within ULP bounds for division and built-ins.
- Failures: out-of-bounds, overflow and division by zero in an entry and in a
  nested helper give the CPU panic message.

## Out of scope for v1

Workgroup shared memory and barriers, subgroups, textures and graphics,
multiple queues, async dispatch, `f16`/`f64`, buffers of records, CUDA/PTX,
Metal without MoltenVK, and proving that GPU loops terminate (a hung shader is
stopped by the driver's watchdog).

## Decisions

Approved 2026-11-07:

1. **Overflow:** `#[gpu]` code keeps the CPU's checked arithmetic;
   `Int.wrapping_*` is the opt-out.
2. **Thread id:** the entry's first parameter `id: u32`.
3. **Vector types:** deferred to the `SIMD` plan node, so CPU and GPU share
   one design.
4. **Runtime:** C over Vulkan, loaded with `dlopen`.
5. **No device:** `Gpu.open(): Result<GpuDevice, i64> ! {io}`, so programs can
   fall back to the CPU. The evaluator always returns `Ok`.
