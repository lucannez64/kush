# Native Rust/C interop

Status: implemented and tested for the Linux x86-64 native backend. Kush checks
the Kush side of every boundary; a foreign library is trusted code. Kush does
not verify that foreign code is memory safe, does not track pointer provenance,
and does not protect against a library that violates its declared ABI.

## Trust boundary

Checked on the Kush side:

- the foreign symbol is a bounded C identifier and is called directly, never
  used as a first-class value;
- the signature is restricted to the bridge ABI below; foreign functions are
  concrete, monomorphic, and have no erased proof parameters;
- every foreign call requires the `io` effect in its declared row, so host side
  effects are visible at every call site;
- an opaque `#[foreign("release")]` resource is affine (or linear with
  `#[linear]`), is moved at most once, and generated drop glue calls its release
  symbol exactly once. Passing the resource by value transfers ownership to the
  foreign callee, which must then release it; passing `&Resource` only borrows
  the handle for the call;
- a `Result<T, i64>` foreign result is lowered through a status code and an out
  slot; Kush code must handle `Ok` and `Err` like any other checked `Result`.

Not checked and explicitly documented as trusted:

- foreign memory safety, buffer bounds, pointer validity, thread safety, and
  the foreign release function's correctness;
- whether a foreign function retains a borrowed pointer past the call;
- whether a foreign function mutated bytes outside the supplied `&mut Bytes`
  range (Kush has no mutable byte-slice view in this milestone).

The reference interpreter rejects every foreign call with a clear
`native backend` diagnostic instead of executing or guessing host behavior.

## Declaration syntax

```kush
enum Result<T, E> { Ok(T), Err(E) }

// One opaque host-owned handle. release must be the exact C symbol.
#[foreign("example_hasher_release")]
struct Hasher {}

foreign "example_add" fn add(a: i64, b: i64) -> i64 ! {io};
foreign "example_sha256" fn sha256(data: &Bytes) -> Result<Bytes, i64> ! {io};
foreign "example_new" fn new() -> Hasher ! {io};
foreign "example_update" fn update(h: &Hasher, data: &Bytes) -> Result<i64, i64> ! {io};
```

Foreign declarations end in `;`, have no body, cannot be `total`, cannot be
generic, and cannot appear in an impl or trait. A resource declaration is an
opaque struct with no fields and one release-symbol attribute. Its handle is not
constructible from Kush source; only a foreign call can produce one.

## Bridge ABI v1

| Kush side | C ABI |
| --- | --- |
| `i8`/`u8`/`i16`/... | matching `int8_t`/`uint8_t`/... |
| `f32`/`f64` | `float`/`double` |
| `Bool` | `int32_t` (0 or 1) |
| `&str` | `const uint8_t *, int64_t` (validated UTF-8 only at generated Rust shims; the C ABI is bytes) |
| `&Bytes`, `&String` | `const uint8_t *, int64_t` (existing byte-contiguous storage, no copy) |
| `Bytes` result | `int64_t` handle to a Kush-owned byte buffer |
| `Hasher` / `&Hasher` | `int64_t` opaque handle (`void *` on the wire) |
| release symbol | `void release(int64_t handle)` |

The release symbol receives the one-word handle directly; it must release the
foreign allocation exactly once and tolerate a zero handle (generated drop glue
only calls it for a live affine value, but the C example guards zero anyway).
| `Result<T, i64>` | `int64_t status`; `0` = `Ok`, non-zero = `Err(status)`; non-Unit `T` is written through a trailing `int64_t *out` |

For a fallible non-Unit result the C signature is
`int64_t symbol(params..., int64_t *out)`. A direct result returns the scalar or
handle. Integers in the out slot are sign/zero-extended; float words contain
raw IEEE-754 bits; a `Bytes` out word is a `KushBytes *` handle.

Deliberately unsupported, with an exact diagnostic rather than a guess:

- arbitrary records/enums/unions, Rust internal ABI, borrowed returns, function
  pointers, `&mut [T]` excluding `Bytes`/`String`, and inline `&[u8]` arrays.
  Inline `u8` arrays store one checked word per element, not contiguous bytes;
  passing that pointer to C would be wrong, so those types are rejected.
- `Result` errors other than `i64` (the status channel is `i64`).

## Generated Rust adapters

`kush::interop::AdapterSpec` emits a self-contained Rust file with:

- one `#[unsafe(no_mangle)] extern "C"` shim per declared function;
- `catch_unwind` at every boundary. A fallible shim maps `Err(String)` to
  status `1` and a caught panic to status `2`; the message is retrievable via
  the generated `kush_bridge_last_error(out, capacity)` symbol. An infallible
  shim records the panic and aborts instead of returning a half-written value;
- pointer/length checks for borrowed buffers, UTF-8 validation for `&str`, null
  handle checks, and canonical one-word encodings;
- one release shim per resource that consumes `Box::from_raw` exactly once;
- `kush_bytes_from` calls (resolved from the Kush runtime in the final binary)
  for owned `Bytes` results.

The Rust implementation remains ordinary safe code. See
`examples/rust-adapter/` for a complete crate using the existing `sha2` 0.10
dependency: `src/ffi.rs` is generated, `src/bridge.rs` is hand-written safe
Rust, and `sha256.kush` is the checked Kush program. Build and run:

```sh
cd examples/rust-adapter
kush run

```

Expected output includes the SHA-256 hex of `abc` twice, then `42`, `0`, `1`,
`2`. The `0` is the live resource count after the owned `Hasher` was released
exactly once; `1`/`2` are a checked `Err` and a contained panic status.

## Build and project-manifest integration

Library API:

- `kush::native::LinkSpec { objects, libraries, library_dirs, system_libraries }`
  is validated before files are written or `cc` starts.
- `kush::native::build_with_options(&checked, &output, stats, &links)` passes
  every path as one `cc` argument and every system library as one `-l` name. A
  failed link leaves an existing output intact.
- `kush::native::LinkSpec::from_project_native(root, libraries, library_paths,
  cargo_manifests)` maps the merged project manifest fields.

Concrete mapping for `project::manifest::NativeOptions`:

| Manifest field | `LinkSpec` mapping |
| --- | --- |
| `libraries = ["kushffi"]` | `system_libraries` -> `-lkushffi` |
| `libraries = ["vendor/libfoo.a"]` (contains a path separator or a `.a`/`.o`/`.so`/`.dylib` suffix) | `libraries` absolute path, resolved against the project root |
| `library-paths = ["vendor"]` | `library_dirs` -> `-L<dir>` |
| `cargo-manifests = ["adapters/foo/Cargo.toml"]` | built with `cargo build --release --lib --message-format=json`; the emitted `.a` is appended to `libraries`; `pthread` and `dl` are added once for Rust std staticlibs |

Project build and test commands now collect these inputs from the root package
and its dependencies and call `build_with_options`. The core mapping is:

```rust
let links = crate::native::LinkSpec::from_project_native(
    &project.root,
    &project.package.native.libraries,
    &project.package.native.library_paths,
    &project.package.native.cargo_manifests,
)
.map_err(|error| Failure::new(error.message))?;
crate::native::build_with_options(&checked, &output, options.stats, &links)
    .map_err(|error| Failure::new(program.sources.render(&error)))?;
```

`from_project_native` invokes no shell and validates bare library names.
`cargo-manifests` explicitly opts into Cargo builds, including dependency
resolution according to Cargo.toml/Cargo.lock. Set `CARGO_NET_OFFLINE=true`
when offline behavior is required. Rust adapters use a separate
`target/kush-adapter` directory with two build jobs; they never write into the
compiler's mbx target. Project tests compute link inputs once before running
selected tests; listing tests does not build adapters.

Manifest fragment:

```toml
[native]
libraries = ["kushffi"]
library-paths = ["vendor/native"]
cargo-manifests = ["adapters/rust-adapter/Cargo.toml"]
```

`library-paths` and `cargo-manifests` are already canonicalized by
`manifest::resolve_native`; `from_project_native` tolerates absolute paths.

## Tests

`crates/kush/tests/ffi.rs` covers:

- declaration rejection (missing `io`, unsupported types, generics, function
  values, malformed release symbols/attributes);
- `Result` error-channel validation;
- reference-interpreter rejection;
- a real C static library round trip for scalars, `&Bytes`, owned `Bytes`,
  checked `Result` status, borrowed opaque resources, and exactly-once release;
- paths containing spaces, failed-link output preservation, and `-l` flag
  injection rejection;
- generated Rust shim compilation with `rustc`, checked errors, caught panic
  status `2`, owned byte results, and resource release;
- the project-manifest mapping, including a freshly built Cargo staticlib;
- generator rejection of malformed symbols and Rust paths.

## Remaining boundaries

- Host OS APIs (filesystem, argv/env, clocks, processes, networking) are the
  host worker's area; this bridge only links and calls supplied native code.
- The CLI has a small isolated `build --link <archive>` / `--link-lib <name>`
  hook for examples; the project workflow should use the library API above.
- Foreign callbacks into Kush, C variadics, structs by value, and ownership
  transfer of a resource into a foreign function and back are not implemented.
- Async/task suspension across a foreign call is not supported.

## Foreign effect and cleanup contracts

Only `io` is mandatory on foreign imports. Additional `alloc`, `panic`, or
`suspend` effects are author-declared and checked at Kush call sites; Kush
cannot inspect the external implementation to verify them. A `#[noalloc]` or
`#[nosuspend]` caller therefore relies on the imported contract, not on a proof
about C/Rust code. Blocking OS work and cooperative task suspension are distinct.
Foreign release hooks are trusted cleanup and their internal effects are not
inferred from Rust `Drop`; they must not unwind across the ABI or retain a
released handle. Panic containment requires Rust adapters built with
`panic = "unwind"`; a `panic = "abort"` crate cannot return a caught-panic status.

Borrowed foreign results, owned Bytes inputs, and Unit inputs are rejected.
Opaque resources always occupy one checked word, including in aggregates and
fallible result slots. Cargo artifacts are selected by the requested manifest
and staticlib target, not dependency emission order. Link input paths starting
with `-` or `@` are rejected, and package-native library paths cannot escape
their package through absolute paths or `..`.
