# First executable subset

Kush can now compile a checked value-language subset to a Linux x86-64 native executable
using Cranelift. It also has an independent reference evaluator for this subset.
The [logical kernel](kernel.md) remains available separately. This is a first
working compiler, not full conformance to the [v0.1 design](spec-v0.1.md).

## Build and run

Requirements: Rust 1.95 or newer, Linux x86-64, and `cc` with the system C headers
and linker. Cranelift dependencies are pinned to 0.135.0 in Cargo.lock/Cargo.toml.
The compiler needs these dependencies downloaded on a new machine; once cached,
Cargo commands also support `--offline`.

```sh
cargo run -p kush -- check examples/first.kush
cargo run -p kush -- eval examples/first.kush
cargo run -p kush -- run examples/first.kush
cargo run -p kush -- build examples/first.kush -o target/first
./target/first
```

The example prints:

```text
42
720
42
```

It parses two ASCII digit codes into `42`, computes `factorial(6)`, and exercises
local mutation through control flow. This is a tiny parsing function, not yet a
file parser or a self-hosted compiler. The newer
[expression parser](bytes.md) reads text bytes and builds an owning AST.

`check` selects executable checking if the file contains an ordinary `fn` or an
enum declaration. Otherwise it uses the existing logical checker. When executable
checking is selected, every `total fn` and logical type alias in the program is
submitted to the logical kernel first and then erased; runtime code cannot call
or read those definitions. Erased parameters may use the arithmetic `{ ... }`
fragment or a logical proposition such as `Eq<Nat, 0, 0>`, including open
propositions depending on earlier erased kernel binders or immutable machine
scalar indices (`i64`, `Bool`, `Unit`), with named checked proof terms at the
call. Transparent executable type aliases (including arrays, unions,
and generic aliases) are elaborated separately and add no runtime work. `build`,
`run`, and `eval` always require the executable subset. Unsupported features
produce diagnostics.

`run` builds in a temporary directory, executes the native program with inherited
standard streams/current directory, and removes its build files after exit.
`eval` executes the checked IR in the bounded reference evaluator. There is no
fallback from native execution to interpretation.

`build` requires an explicit `-o` destination. Object generation and linking
finish before the destination is atomically replaced; source/check/link failures
leave an existing destination intact. The CLI rejects using the source file as
its output. The temporary build directory is private on Unix. Paths are passed
as process arguments without shell interpolation. The built executable can run
independently of Cargo and the Kush compiler, with the system C runtime available.

## Supported language

```rust
fn twice(x: i64) -> i64 ! {panic} {
    x * 2
}

fn main() -> Unit ! {io, panic} {
    let mut value = twice(21);
    if value == 42 { value = value + 1; }
    print_i64(value);
}
```

The executable checker supports:

- Monomorphic ordinary functions with explicit value signatures and effect rows.
- `i64`, the fixed-width `i8`/`i16`/`i32`/`u8`/`u16`/`u32`/`u64` types,
  Unicode `Char`, `Bool`, `Unit`, inline tuples of 2–16 elements, validated
  UTF-8 `String`, and finite inline enums, including parameters/returns.
  Both `Unit` and `()` denote the unit type; `()` is its value.
  See [basic values](basic-values.md).
- Generic enum definitions, unit/tuple constructors, nested payloads, exhaustive
  enum patterns, and conventional `Result` propagation; see [enums.md](enums.md).
- Anonymous tuple expressions, positional `.N` projection, nested tuples,
  destructuring, generic inference, union/callable element coercions, and
  tuple-aware early-exit checking.
- Type-directed receiver spellings for existing builtin operations
  (`bytes.len()`, `values.push(x)`, `text.scalar_at(i)`, integer
  `wrapping_add`/`checked_add`/conversions, and similar). Statically dispatched
  inherent and trait methods, bounded `T: Trait` helpers, and explicit
  `receiver.Trait.method(...)` qualification are documented in
  [traits.md](traits.md). `dyn Trait` uses a checked closed-world union for
  finite member sets and a fixed two-word dynamic fat object with a checked
  per-member method table for open/generic member sets and nominal fields; both
  support owned, shared, mutable, and stored borrowed dispatch.
- Forward calls, current-module-qualified calls, and ordinary general recursion.
- Immutable/mutable single-name locals, optional local type annotations, shadowing,
  assignment, nested blocks, tail expressions, and early `return`.
- Checked fixed-width `+`, `-`, `*`, `/`, `%`, bitwise operators, shifts, and
  negation; integer comparisons; `Char` comparisons;
  scalar equality/inequality; Boolean `!`, `&&`, and `||`.
- `if`/`else` and `match` expressions with guards, nested enum patterns,
  integer/Boolean literals, typed binding alternatives, and wildcards.
- `print_i64(value)` and `panic()` builtins.
- Opaque `Stdin`/`Stdout` values and bounded, recoverable standard-stream I/O;
  see [stdio.md](stdio.md).
- Unique boxes, owning byte buffers, affine moves, recursive owning enums,
  explicit lifetimes, conservative single-input slice-result lifetime elision,
  checked shared and mutable borrowed slice returns,
  capability-ancestry sub-view reborrows, exclusive mutable slice views,
  lifetime-parameterized records with shared or exclusive slice fields and
  checked mixed owning metadata, deterministic
  cleanup, and `noalloc`/`nosuspend` function contracts;
  see [ownership.md](ownership.md), [lifetimes.md](lifetimes.md),
  [borrowed records](borrowed-records.md), and [bytes.md](bytes.md).

Function bodies evaluate left-to-right. `&&`/`||` short-circuit. A match evaluates
its scrutinee once, then tries patterns and guards in source order. Guards use
that captured value; they can affect other mutable scalar locals.
A branch-local catch-all binding is immutable and cannot escape its arm.

Bool matches must cover both values or have an unguarded catch-all. Integer
matches need an unguarded catch-all. A guarded arm does not establish coverage.
Completely unreachable arms/patterns are rejected. Type agreement between match
arms and if branches is checked, allowing a returning/aborting branch to have no
normal result. An if without else has Unit as its missing branch.

For statement blocks before an expression beginning with a unary operator, use
an explicit semicolon to avoid parsing the operator as part of that block-valued
expression: `if condition { return 1; }; -1`.

Direct and indirect calls of first-class functions are supported, including
named functions, explicit generic specializations, explicitly typed
noncapturing lambdas, owning once-consuming capturing closures, scoped
borrowed-capture `once fn` closures, function-typed
parameters/results/locals, and checked arrow subtyping. See
[functions.md](functions.md). Destructuring lets, records, Box/Bytes/Vec
ownership, inline arrays with compile-time const lengths, shared and exclusive
slice views, borrowed slice returns, lifetime-parameterized records with shared or exclusive
slice fields and mixed owning metadata, and aliases, generic functions, natural and explicitly specialized
abstract [usage grades](grades.md), transparent generic type aliases, and
normalized unions are implemented. See
[dependent array lengths](dependent-indices.md) and
[borrowed records](borrowed-records.md).
General borrowed `str`/substring views,
runtime-sized `[T; n]` layouts (the separate `DynArray<T, capacity>`
subset is documented in [dynamic-arrays.md](dynamic-arrays.md)), direct mutable/owning
record field moves, linear or stream/callable/union metadata in mixed records,
general lifetime inference beyond signature elision,
traits, arbitrary FFI, and attributes
other than `noalloc`/`nosuspend` are not implemented in this subset. Structured
tasks and cooperative cancellation are described in [async.md](async.md).
Floating-point values are implemented for one-word `f32`/`f64` arithmetic,
comparisons, explicit conversions, printing, and aggregate/callable storage; see
[basic values](basic-values.md). Floats remain ineligible as erased machine
indices.

## Arithmetic and effects

Each fixed-width integer literal must fit its contextual kind (`i64` by
default). A directly negated literal can represent that kind's minimum.
Logical `Nat` and its arbitrary-precision literals
remain in the logical checker; they are not silently converted to machine values.
Arithmetic is checked for the operands' width in every build. Explicit
`Int.convert` (lossless), `Int.try_convert` (range-checked `Option`),
`Int.truncate` (two's-complement truncation), wrapping/saturating/checked
operations, and `Char` conversions are listed in [basic values](basic-values.md).

Width overflow, division/remainder by zero, signed minimum divided/remaindered by
`-1`, and negating signed minimum abort rather than wrap. Checks remain present in
native development builds. The reference evaluator reports the corresponding
source diagnostic. Directly negated valid constants are already known safe;
other arithmetic operations conservatively require `panic`, even for expressions
such as `1 + 2`. Constant proofs/check elimination are future work.

Executable rows currently accept `alloc`, `io`, and `panic`, without arguments or
duplicates. Each operation must fit the enclosing function's declared row. Calls
use the callee's **declared** effects, even when its current implementation could
be more precise. This supports recursion without trusting body inference across
an interface. Unreachable short-circuit branches are still checked conservatively.

The initial builtins are:

```rust
fn print_i64(value: i64) -> Unit ! {io, panic};
// panic() aborts; it does not return a normal value.
```

`print_i64` writes a decimal integer followed by a newline. The small C shim
formats into a fixed stack buffer and retries interrupted/partial POSIX writes.
An output failure aborts. This bootstrap helper is intentionally small; typed
filesystem APIs remain deferred. Bounded stdin/stdout operations now
return recoverable Result values through a [separate interface](stdio.md). It does not expose
user FFI or certify general allocator/resource contracts.

`panic()` and checked-arithmetic failures call the abort shim with a diagnostic
on stderr. There is no unwinding. External termination signals are outside these
language-level diagnostics. Stack/resource exhaustion is not statically bounded.

Native startup ignores SIGPIPE so recoverable byte writes can return EPIPE;
`print_i64` continues to abort on output failure.

A runnable file needs `fn main()` returning Unit or i64. Unit exits with status
0; an i64 result exits with its low eight bits, following Unix process status
conventions. A Bool result or parameters on main are rejected. Library files
without main can be checked but cannot be built/run as an executable.

## Implementation and verification

The path to native execution is:

```text
source -> lexer/parser -> lexical name resolution
       -> value type/effect and pattern checker -> private checked executable IR
       -> Cranelift SSA + checked arithmetic/control flow
       -> native object -> cc link + minimal runtime shim -> ELF executable
```

Every user function is generated by Cranelift. `cc` compiles only the fixed
runtime shim and links it with the generated object; it does not compile a C
translation of the user's program. Rust unsafe code remains forbidden in this
crate. Native output is compiler-generated machine code linked with trusted C
runtime support. The prototype now has restricted owning Box and Bytes models but is not an implementation
of the spec's complete graded ownership/resource guarantees.

Only the executable checker constructs this IR. Its local slots resolve binding
IDs rather than textual names, preserving shadowing and scopes. The backend uses
Cranelift SSA variables, branch parameters, and explicit return edges. Scalar
values use 64-bit registers; [enum layouts](enums.md) use multiple words and
caller-owned stack buffers for returns. This ABI is private
and unstable. Cranelift verifies functions during generation. Native code uses
the host's Linux x86-64 baseline configuration, not an LLVM backend.

The reference evaluator follows the same checked IR with separate execution
logic. Its default host API uses empty input; explicit I/O evaluation APIs and CLI `eval`
can supply input streams. It has a 100000-step computation budget (expressions
and I/O attempts) and a shared 128-level
call/expression nesting budget. Exhaustion is a diagnostic. These are evaluator
limits, not native execution limits or language termination claims. Ordinary
recursive functions are excluded from the proof kernel.

Implementation limits currently include 256 instances (specializations) of
one function and 1024 instances of generic functions in all, 64 parameters
per function, and 1024 local slots per function, in addition to frontend nesting/input limits
and the [enum layout/coverage limits](enums.md). No compilation-speed or runtime-performance comparison is claimed.

Tests compare native output and exit status against the reference evaluator for
arithmetic, conditionals, recursion, scalar matching, guards, mutable SSA values,
short-circuiting, argument evaluation order, and early returns. Additional tests
check type/effect errors, source preservation, output-file atomicity, and native
aborts on integer and byte-buffer failures. Standard-stream tests check
recoverable errors, partial transfers, and native/reference agreement.

Runtime enums/Result and nested pattern checking are now implemented. Unique boxes and ownership-aware cleanup are now implemented; byte buffers and a text parser example also work. Further
extensions include general containers and stronger resource guarantees. Logical proof
integration needs relevance/erasure checking before it can be connected safely
to executable code. Heterogeneous union/intersection subtyping is implemented
for value types; see [subtyping.md](subtyping.md), and first-class
[functions and closures](functions.md) have checked arrow subtyping and owning
once closures. Canonical structural record width subtyping, finite effect-row
constraints with union/subtraction, restricted one-shot effect handlers with
non-tail lexical resumption, versioned runtime proof indices with branch/loop
joins and proof-valued locals, and `DynArray<T, capacity>` are implemented
restricted fragments; see the linked documents. General nested structural
conversions, multi-prompt/dynamic/multishot handlers, open-row principal
inference, user-defined graded modalities, general fusion, forced cancellation
unwinding, nonblocking task I/O, and LLVM remain future work. The implemented
natural/abstract grade fragment is described in [grades.md](grades.md).
