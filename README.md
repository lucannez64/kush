<img src="assets/icon.svg" width="64" height="64" alt="">

# kush

A functional systems language exploring dependent types, algebraic subtyping,
graded ownership, and direct-style cooperative tasks.

See the [core implementation and integration status](docs/core-status.md).

Read the [v0.1 language specification](docs/spec-v0.1.md) for the proposed syntax,
semantics, research gates, and implementation milestones.

Kush has a working native compiler on Linux x86-64 using Cranelift. It supports
functions, recursion, checked fixed-width integers (`i8`/`i16`/`i32`/`i64` and
`u8`/`u16`/`u32`/`u64`), Unicode `Char`, Booleans, inline tuples with positional
projection and destructuring, validated UTF-8 `String` values over owning byte
buffers, immutable borrowed `&str` text views with checked byte-offset
substrings and explicit owning copies, `f32`/`f64` IEEE values, local mutation,
generic inline
enums, nested exhaustive matching, Result propagation, unique owning boxes,
owning byte buffers, explicit lifetime parameters with conservative
single-input slice-result elision, explicit checked function outlives bounds
(`<'long: 'short, 'short>`) for shared/mutable slice and borrowed-record
returns, checked borrowed `&'a [T]`
and `&'a mut [T]` returns, capability-ancestry loans with parent suspension and
last-use restoration, mutable sub-views and retained reborrows, exclusive
`&mut [T]` slice views with `Slice.set` and the fallible `Slice.try_get`,
lifetime-parameterized records storing shared `&'a [T]` or exclusive
`&'a mut [T]` fields, with per-field provenance, checked destructuring, shared
copies, move-only exclusive fields, mixed `Box`/`Vec`/`Bytes` metadata, checked
helper returns and deterministic cleanup, call-scoped nominal-record
`&self`/`&mut self` receivers and ordinary `&Record`/`&mut Record` parameters
with copyable field reads and exclusive copyable-field writes, statically
dispatched traits with generic type/`Nat`/`Grade` specializations, generic
methods with checked monomorphization, and inherited default method bodies
with per-impl `Self`/trait-argument substitution,
scoped `once fn` closures capturing
borrowed slice views for local calls, first-class named/generic function
values, explicitly typed
noncapturing lambdas, owning once-consuming closures, effect-polymorphic
higher-order functions with inferred or explicit effect rows, callable union
alternatives, linear-once closures that transfer captured linear obligations,
checked arrow subtyping, deterministic cleanup, checked unique-box reuse,
allocation-preserving in-place vector transforms with conservative pure-map
fusion, allocation diagnostics, bounded synchronous stdin/stdout I/O, and a
direct-style cooperative structured-task system with `Task.scope`, explicit
`Task.spawn`, `Task.yield`, `Task.join`, `Task.cancel`, cancellation check
points, and a `suspend` effect. Requires Rust 1.95+ and `cc`.

```sh
cargo run -p kush -- run examples/first.kush
# Prints 42, 720, 42 on separate lines.

cargo run -p kush -- build examples/first.kush -o target/first
./target/first

cargo run -p kush -- run examples/borrowed-records.kush
# Prints 10, 20, 5 on separate lines.
cargo run -p kush -- run examples/mutable-borrowed-records.kush
cargo run -p kush -- run examples/mixed-borrowed-records.kush
cargo run -p kush -- run examples/borrowed-methods.kush
cargo run -p kush -- run examples/tuples.kush
cargo run -p kush -- run examples/strings.kush
cargo run -p kush -- run examples/borrowed-text.kush
cargo run -p kush -- run examples/floats.kush
# Linear resource factories and `@[1]` result contracts; prints 20, 21, 21, 7, 42.
cargo run -p kush -- run examples/linear-resources.kush
```

A separate dependent-type kernel checks total logical functions, universes,
compact arbitrary-precision naturals, induction, equality proofs/transport/full
`J`, positive user-defined indexed data with checked dependent elimination,
constructor-local finite indices, a `Prop` sort, and proof irrelevance for
checked propositions. Executable programs may contain those total definitions;
the kernel checks them, audits relevance, and erases them before runtime
lowering. Closed erased logical propositions and open propositions depending on
earlier erased proof binders can be used as executable proof parameters. The
executable language also has modules, generic functions, records, vectors,
fixed-length inline arrays with const-dependent lengths, loops, erased
arithmetic obligations, natural/abstract usage grades plus owning `@[1]` result
contracts, effect-row parameters,
transparent generic type aliases, and normalized heterogeneous union/intersection
types (including callable alternatives), and symbolic `i64`/`Bool`/`Unit`
runtime indices in erased proofs. See the [steps
1–6 milestone and its limitations](docs/milestone-1-6.md), the [implemented
grade rules](docs/grades.md), the [algebraic subtyping
boundary](docs/subtyping.md), [dependent array lengths and compile-time
indices](docs/dependent-indices.md), [runtime scalar proof
indices](docs/runtime-indices.md), [user-defined logical
data](docs/logical-data.md), [propositions and proof
irrelevance](docs/propositions.md), and [borrowed and mixed
records](docs/borrowed-records.md).
Runtime-sized inline arrays, general dependent propositions over arbitrary
mutable runtime
values, large elimination from user propositions, broader
relevance rules,
user-defined graded modalities, general grade inference, structural record
subtyping, effect handlers and general row constraints, full algebraic subtype
inference, general automatic effectful fusion, nonblocking task
I/O, forced cancellation unwinding, and LLVM remain future work. See
[checked reuse and allocation diagnostics](docs/reuse.md) for the implemented
storage-reuse fragment, [vector capacity reuse and explicit effectful map chains](docs/vector-reuse.md),
[bounded native allocator pooling](docs/allocator-pool.md), [memory-completion contracts](docs/memory-completion.md)
for justified automatic fusion, widening/fallible reuse, the built-in arena
allocator, and the reproducible benchmark harness, and [structured async and cooperative
cancellation](docs/async.md) for the task system.

An interactive [todo terminal app](docs/todo.md) is available in
[examples/todo.kush](examples/todo.kush): add, toggle, delete and filter tasks
with commands followed by Enter. It redraws an ANSI board and keeps tasks for
the current session.

The reusable [JSON parser](docs/json.md) in `std.json` supports owned values,
Unicode strings and exact number text. [examples/json.kush](examples/json.kush)
is a stdin-to-stdout JSON minifier with structured parse errors.

```sh
printf '(1 + 2) * -3\n' | cargo run -p kush -- run examples/calc.kush
# A multi-file calculator; prints -9.
printf '12 + 3 * 10\n' | cargo run -p kush -- run examples/expression-stdin.kush
# Reads stdin and prints 42.
cargo run -p kush -- run examples/expression-parser.kush
# Parses 12 + 3 * 10 into an owning AST and prints 42.
cargo run -p kush -- run examples/bytes.kush
cargo run -p kush -- run examples/slices.kush
cargo run -p kush -- run examples/lifetimes.kush
cargo run -p kush -- run examples/lifetime-bounds.kush
cargo run -p kush -- run examples/mutable-slices.kush
cargo run -p kush -- run examples/mutable-splits.kush
cargo run -p kush -- run examples/borrowed-closures.kush
cargo run -p kush -- run examples/borrowed-pipeline.kush
cargo run -p kush -- run examples/mutable-borrowed-records.kush
cargo run -p kush -- run examples/mixed-borrowed-records.kush
cargo run -p kush -- run examples/borrowed-methods.kush
cargo run -p kush -- run examples/grades.kush
cargo run -p kush -- run examples/subtyping.kush
cargo run -p kush -- run examples/functions.kush
cargo run -p kush -- run examples/effectful-functions.kush
cargo run -p kush -- run examples/traits.kush
cargo run -p kush -- run examples/generic_traits.kush
cargo run -p kush -- run examples/default-methods.kush
cargo run -p kush -- run examples/dependent-arrays.kush
cargo run -p kush -- run examples/ownership.kush
cargo run -p kush -- run examples/reuse.kush --stats
cargo run -p kush -- run examples/async.kush
cargo run -p kush -- run examples/results.kush
cargo run -p kush -- check examples/first.kush
cargo run -p kush -- eval examples/first.kush
cargo run -p kush -- check examples/induction.kush
cargo run -p kush -- check examples/large-naturals.kush
cargo run -p kush -- run examples/logical-data.kush
cargo run -p kush -- run examples/finite-proofs.kush
cargo run -p kush -- parse examples/parser.kush --ast
```

See [inline arrays](docs/arrays.md),
[basic values and method syntax](docs/basic-values.md),
[static traits and user-defined methods](docs/traits.md),
[borrowed text views and checked substrings](docs/borrowed-text.md),
[dependent array lengths and indices](docs/dependent-indices.md),
[runtime scalar proof indices](docs/runtime-indices.md),
[borrowed slices and mutable views](docs/slices.md),
[borrowing and lifetimes](docs/lifetimes.md),
[bounded standard-stream I/O](docs/stdio.md),
[byte buffers and the expression parser](docs/bytes.md),
[owning boxes and borrowing](docs/ownership.md),
[checked reuse and allocation diagnostics](docs/reuse.md),
[memory completion: fusion, reuse, fallible allocation, arenas, benchmarks](docs/memory-completion.md),
[structured async and cooperative cancellation](docs/async.md),
[usage grades](docs/grades.md),
[first-class functions and closures](docs/functions.md),
[bounded effect exclusion](docs/effect-constraints.md),
[runtime enums and Result](docs/enums.md),
[the executable subset and native backend](docs/executable.md),
[implemented grammar](docs/frontend.md), and
[kernel rules and supported logical subset](docs/kernel.md),
[logical data and dependent elimination](docs/logical-data.md), and
[propositions, proof irrelevance, and erasure](docs/propositions.md).

Development checks:

```sh
cargo fmt --all -- --check
cargo test --workspace --offline
cargo clippy --workspace --all-targets --offline -- -D warnings
```

## Project workflow

A local project uses a documented `Kush.toml` with an entry point and local path
dependencies, a deterministic `Kush.lock`, project-level check/build/run/test
commands, per-test process isolation and filtering, and a conservative formatter
that preserves comments and strings:

```sh
kush new hello
cd hello
kush check
kush run
kush test
kush fmt --check
kush lsp
```

Single-file commands are unchanged. See [project workflow, tests, formatting,
and editor support](docs/projects.md) for the manifest and module layout,
lockfile rules, `#[test]`/`std.test` assertions, `--locked`, program-argument
forwarding after `--`, formatter limits, the VS Code extension, and the
validated native bridge manifest fields. `kush lsp` is a stdio language server
with project-aware diagnostics, lexical go-to-definition, and the existing
whitespace-only formatter; see [language-server.md](docs/language-server.md) for
its protocol surface and limits (no completion, hover, rename, references,
semantic tokens, incremental sync, or type-directed method resolution).

Reuse safe Rust crates without hand-written wrappers through a strict
`Bridge.toml`:

```sh
kush bindgen Bridge.toml          # generate Rust shims + Kush module
kush bindgen Bridge.toml --check  # fail on drift, write nothing
```

The [Rust adapter example](examples/rust-adapter) reuses `sha2` through
`kush run` and `kush test`. See [native interop](docs/native-interop.md) for the
schema, supported ABI, cleanup/error/panic behavior, and exact limits.

The [OTP TUI recreation](examples/otp-tui) is a complete session-based terminal
application: Kush controls the UI and CLI while generated Rust adapters reuse
RustCrypto and crossterm. It includes TOTP/HOTP, hidden URI entry, navigation,
clipboard requests, headless codes, RFC vectors, and pseudo-terminal tests.

The standalone [project demo](examples/project-demo) exercises a local module, a
local dependency, tests, and formatting.

For dependency-first development priorities, see the [foundation roadmap](docs/foundation-roadmap.md).
The [streaming copy](examples/stream-copy.kush) example uses `IO.read_chunk` and
`Bytes.clear` to reuse one buffer for input larger than its capacity.

Bounded [result-grade inference and result aliases](docs/result-grade-inference.md)
are available: an expected `@[1]` arrow can determine a bare result-only grade
parameter. Parameter-grade inference and a general grade solver remain outside
this subset.
