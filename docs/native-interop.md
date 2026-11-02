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

`kush::interop::AdapterSpec` emits a self-contained Rust item sequence with:

- one `#[unsafe(no_mangle)] extern "C"` shim per declared function;
- `catch_unwind` at every boundary. A fallible shim maps `Err(String)` to
  status `1` and a caught panic to status `2`; the message is retrievable via
  `<support-prefix>_last_error(out, capacity)`. An infallible shim records the
  panic and aborts instead of returning a half-written value;
- `<support-prefix>_last_error_bytes(out)` for Kush code. It returns status `0`
  and writes an owned Kush `Bytes` handle for the latest message, `1` when there
  is no error, `2` for a null out pointer, and `3` when the runtime cannot
  allocate the buffer. The generated Kush module declares this as
  `last_error() -> Result<Bytes, i64>`, so error text is callable without a
  writable byte view;
- pointer/length checks for borrowed buffers, UTF-8 validation for `&str`, null
  handle checks, and canonical one-word encodings;
- one release shim per resource that consumes `Box::from_raw` exactly once;
- `kush_bytes_from` calls (resolved from the Kush runtime in the final binary)
  for owned `Bytes` results.

The support prefix is configurable through
`AdapterSpec::generate_with_options(AdapterOptions { support_symbol_prefix })`.
`kush bindgen` derives it deterministically from the Kush module path, so two
generated adapters can be linked into one executable without colliding on the
error helpers. The generated file contains only items: no `#![inner]`
attributes. It works as a normal module file and through `include!` inside a
module.

Generated adapters require `panic = "unwind"` so the boundary can report status
`2`. A `panic = "abort"` build fails at compile time with an explicit
`compile_error!` instead of silently aborting the process later.

The Rust implementation remains ordinary safe code. See
`examples/rust-adapter/` for a complete crate using the existing `sha2` 0.10
dependency: `Bridge.toml` is the source of truth, `src/ffi.rs` and
`src/sha256_adapter.kush` are generated, `src/bridge.rs` is hand-written safe
Rust, and `sha256.kush` is the checked Kush program.

```sh
cd examples/rust-adapter
kush bindgen Bridge.toml
kush run
kush test
```

Expected `kush run` output is the SHA-256 hex of `abc` twice, then `42`, `0`,
`1`, `requested adapter failure`, `2`, and
`kush_example_boom panicked: example adapter panic`. The `0` is the live
resource count after the owned `Hasher` was released exactly once; `1`/`2` are
a checked `Err` and a contained panic status. `kush test` runs two project tests
covering hashing/error text and exactly-once release. The Rust panic hook still
prints the expected message on stderr; unwinding is contained and the program
exits successfully.

### `kush bindgen`

```sh
kush bindgen <Bridge.toml> [--check]
```

The configuration is strict TOML. Unknown tables and fields are errors; paths
are resolved relative to the configuration file and may not be absolute or use
`..`. A complete declaration has this shape:

```toml
[adapter]
module = "app.generated"             # generated Kush module header
rust-output = "src/ffi.rs"           # generated Rust items
kush-output = "src/generated.kush"   # generated public Kush module

[[resource]]
name = "Hasher"                      # Kush resource type
rust-type = "crate::bridge::Hasher"  # safe Rust type stored behind the handle
release-symbol = "kush_example_hasher_release"

[[function]]
name = "sha256"                      # Kush function name
symbol = "kush_example_sha256"       # exact exported C symbol
rust-path = "crate::bridge::sha256"  # safe Rust function
fallible = true                      # Rust Result<T, String>
parameters = [{ name = "data", type = "bytes" }]
result = "bytes"
```

Parameters use exactly one of:

| Form | Kush parameter | Rust parameter |
| --- | --- | --- |
| `{ name = "x", type = "i64" }` (also `i8`/`i16`/`i32`/`u8`/`u16`/`u32`/`u64`/`f32`/`f64`/`bool`) | scalar | scalar |
| `{ name = "x", type = "text" }` | `&str` | `&str` |
| `{ name = "x", type = "bytes" }` | `&Bytes` | `&[u8]` |
| `{ name = "x", resource = "Hasher" }` | `&Hasher` | `&Hasher` |

Results are `"unit"`, a scalar type, `"bytes"` (Rust `Vec<u8>` to an owned Kush
`Bytes`), or `{ resource = "Hasher" }`. With `fallible = true` the Kush
declaration becomes `Result<T, i64>` and the Rust function must return
`Result<T, String>`. Owned text results are deliberately not inferred: return
bytes and encode explicitly.

Generator validation rejects unknown keys, malformed or reserved symbols,
duplicate resource/function names, duplicate generated C parameters, undeclared
resources, Rust keywords and `_` in generated Rust names, and collisions with
the generated `last_error` accessor, `kush_out`, `<name>_data`, and `<name>_len`
parameter slots. The names `last_error`, `kush_bytes_from`, and the derived
support helper symbols are reserved.

Generated files start with a marker. `kush bindgen` refuses to replace an
existing file without that marker and refuses output symlinks. Writes use a
temporary file in the destination directory followed by a rename. `--check`
writes nothing; it reports each missing or changed output and exits non-zero
when the generated files are stale. Outputs are deterministic for the same
configuration. Paths and arguments are passed as filesystem paths, never
through a shell.

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
- generator rejection of malformed symbols and Rust paths, Rust keywords,
  `_`, duplicate resources, `kush_out`, and generated `_data`/`_len` slots.

`crates/kush/tests/bindgen.rs` covers the declarative workflow:

- strict config parsing, unknown keys, reserved/generated symbol collisions,
  duplicate names/symbols/resources, and output/config path collisions;
- `--check` drift without writes, deterministic regeneration, unmarked-file
  refusal, and output/parent symlink refusal;
- a paths-with-spaces project that generates both files, compiles the generated
  Rust staticlib, builds/runs the Kush program, and runs two project tests;
- a two-adapter link where each generated file has distinct error helpers and
  one adapter is compiled through `include!` inside a module;
- a `panic = "abort"` build that is rejected with the explicit compile error.

## Remaining boundaries

- Host OS APIs (filesystem, argv/env, clocks, processes, networking) are the
  host worker's area; this bridge only links and calls supplied native code.
- The CLI has a small isolated `build --link <archive>` / `--link-lib <name>`
  hook for examples; the project workflow should use the library API above.
- Foreign callbacks into Kush, C variadics, structs by value, borrowed foreign
  results, mutable byte views, and ownership transfer of a resource into a
  foreign function and back are not implemented.
- `kush bindgen` supports safe function paths and safe high-level glue, not
  arbitrary Rust ABI/type compatibility. The foreign implementation remains
  trusted code; Kush does not prove its memory safety.
- Async/task suspension across a foreign call is not supported.
