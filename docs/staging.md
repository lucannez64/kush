# Typed staging

Status: design approved by the user, 2026-11-17. Implemented 2026-11-24, with
the restrictions listed at the end of this document. Scope:
STAGING-DESIGN, STAGING and STAGING-RUNTIME, independently of the web track.
The Game Boy specializer/JIT and format generators remain consumers of this
facility, with their own completion criteria.

## Contract

A generator is an ordinary Kush function that constructs typed code. It can
branch, loop, call helpers and recurse while constructing code. A quotation
is checked even when no caller runs it. Splicing composes checked code without
text substitution. Generated code passes the same ownership, grade, effect,
proof and backend checks as handwritten code. Staging does not introduce an
unchecked AST or an alternative language with weaker rules.

The implementation must support a staged interpreter, rather than merely
expanding a finite collection of literal macros. Syntax alone, constant
folding alone, a wrapper around a closure, or a subprocess compiling source
text does not close STAGING or STAGING-RUNTIME.

## Surface proposal

Start with code of callable values: `Code<F>`, where `F` is a callable type.
Putting latent effects, argument/result types and callable multiplicity in
`F` avoids silently discarding the effects of an expression quotation.

```kush
fn power(n: i64) -> Code<fn(i64) -> i64 ! {panic}> ! {alloc, panic} {
    if n == 0 {
        quote fn(x: i64) -> i64 ! {panic} { 1 }
    } else {
        let smaller = power(n - 1);
        quote fn(x: i64) -> i64 ! {panic} {
            x * splice(smaller)(x)
        }
    }
}
```

`quote fn(...) { ... }` constructs code; it does not execute the function
body. `splice(code)` is valid only within a quotation and denotes the
callable represented by `code`. It is not a call of that callable.

`lift(value)` inside a quote embeds a generating-stage value. The initial
supported values are closed immutable scalars: fixed-width integers, Bool,
Char, Unit and floats. Each has explicit bit-preserving serialization. Byte
and string lifting must copy owned storage into the generated artifact;
it must never retain pointers into the compiler or generator's heap. Add
those types as a tested implementation milestone, not a silent coercion.

There is no implicit cross-stage persistence of local variables. A name in
a quote resolves to a quoted binder or a resolved module declaration;
otherwise it is a diagnostic suggesting `lift` or `splice`. Quoted code
cannot capture a generating-stage file, connection, borrow, allocator,
resumption, task, thread, channel, or arbitrary closure.

Nested quotations have explicit stage levels. A splice lowers one level;
a lift transfers a serializable value one level. An unmatched splice, a
reference to a later stage, or an escaped quoted binder is rejected.

Expression quotations can be expressed as zero-argument function quotations.
A later shorthand must preserve its latent row and multiplicity. Do not
introduce a bare `Code<T>` expression form that forgets these properties.

## Hygiene and typing

Quotes use resolved binding identities and fresh generated identities, never
variable-name substitution. A splice keeps references to its defining module
and private declarations; the caller's identically spelled names cannot
capture them. Generated binders are fresh on every insertion, including
inserting a fragment twice. Retain originating spans and a generator/splice
trace for diagnostics.

Type-check generators and quotation templates before executing generators.
Quotation templates carry typed holes for splices and lifted constants. A
hole's expected callable type includes effects and multiplicity; normal arrow
subtyping applies. Generated instantiations are checked again after filling
holes, including ownership, exact grades, lifetimes and proof obligations.
No source text parsing is involved in filling a hole.

`Code<F>` owns its template graph and constants, is affine and cannot contain
borrowed references to the generation scope. A splice consumes its fragment;
reuse requires explicit `Code.clone(&fragment)` for a closed, copyable
callable signature. Cloning copies code data, not a captured run-time resource.
Initially reject once/linear callable signatures until their ownership rules
are implemented and tested; never erase them to a reusable function pointer.
The generated function may allocate and use owned or linear local values:
its body follows ordinary Kush rules.

Constructing a quote has `alloc` and may have `panic` for resource limits;
it does not acquire the quoted body's effects. Calling generated code has
exactly the body's declared/inferred effects. A quoted `perform` must bind
to an appropriate execution-stage handler; a generator's live handler or
capability cannot be captured by code.

## Compile-time execution

Proposed declaration spelling:

```kush
#[staged]
fn cube(x: i64) -> i64 ! {panic} = power(3);
```

The right-hand side is a generation-time expression returning a `Code<F>`
compatible with the declared callable signature. The declaration exports an
ordinary function: callers need no staging support. The syntax must be
implemented in the parser and tooling, not recognized by rewriting raw text.

The compiler evaluates the generator in a restricted instance of the
reference evaluator. Permitted generator effects are allocation and checked
panic; forbid I/O, suspension, foreign calls, process/environment access,
clock/random sources, thread/task creation and declared effects. This applies
transitively, including quoted helpers used to construct fragments. Effects
inside the resulting code are checked separately and may include I/O.

Set explicit generation fuel, recursion-depth, template-node and allocation
limits. Exhaustion and generator panics produce source diagnostics, never a
compiler crash or a partially published generated declaration. A recursive
staged-declaration dependency is a cycle error. Bound both generator work and
the materialized graph size to prevent exponential splice expansion.

The resulting checked function enters the existing evaluator, Cranelift and
LLVM paths. There is no run-time compiler dependency in an ahead-of-time
program that only uses `#[staged]` declarations. Deterministic generated IR
and generator dependencies participate in any artifact cache key.

## Runtime execution

`STAGING-RUNTIME` adds `Code.compile(fragment)`, returning a checked,
fallible compiled-function owner. Compiling consumes the fragment. Compilation
requires allocation and a distinct compiler service contract; resource or
unsupported-target failures are returned as errors. Do not report a backend
error as a user panic.

The owner keeps the generated code, constants, relocation dependencies and
compiler metadata alive. Calling through a borrowed view of the owner has
`F`'s effects. A callable view cannot outlive its owner or escape through a
returned closure. Dropping the owner releases executable storage once,
including when unwinding. There is no API that returns an unowned integer
address or a function pointer independent of the owner.

Use the native backend in process. Factor reusable lowering from object-file
emission; add an in-process linker/JIT path rather than spawning `kush`, `cc`
or another process. Resolve only checked Kush functions and existing allowed
runtime symbols, not arbitrary user-supplied symbol addresses.

Executable storage has a linear lifecycle: writable while populated and
relocated, executable while callable, released exactly once. No mapping is
writable and executable simultaneously. Failed allocation, relocation or
permission changes clean up every intermediate resource. Publication occurs
only after all writes and instruction-cache synchronization required by the
platform. Initially support the native Linux x86-64 host, diagnose other
targets, and retain an evaluator implementation of the same typed execution
contract for semantic parity tests.

Runtime generator code may use runtime inputs (e.g. ROM bytes). Its generated
artifact must be self-contained. A process-local cache is optional; it must
not change owner lifetimes or retain resources forever. Thread sharing and
concurrent compilation require separate tests before being admitted.

## Implementation and acceptance milestones

1. Parser/AST: quote, splice, lift, staged declarations, source spans and
   diagnostics. Existing files without staging keep their behavior.
2. Resolve/type-check: stage-indexed scopes, hygienic binder identities,
   callable code types, typed holes, effects and ownership; negative tests
   for every boundary above, including uninstantiated generic generators.
3. Generator evaluator: real branch/loop/recursion execution, graph
   construction and substitution, scalar then owned-text lifting, limits
   and cleanup. The public Code representation remains opaque.
4. Compile-time integration: dependency ordering, generated-body checking,
   evaluator/Cranelift/LLVM parity, exported signatures, generic helpers,
   and a power-specialization example that removes generator work from the
   final artifact. Check the generated body, not only its printed output.
5. Runtime backend: shared lowering, in-process compilation, checked symbol
   resolution, fallible publication, owner-bound calls and cleanup.
6. Runtime validation: specialize from runtime input, compare evaluator and
   generated execution, repeatedly compile/call/drop, unwind while holding
   artifacts, reject escaping callable views, verify memory permissions,
   fault-inject publication failures and check allocation balance.

STAGING closes only after milestones 1–4, including ownership/effect rejection
and resource-limit diagnostics. STAGING-RUNTIME closes only after 5–6.
A parser-only feature or a scalar-only prototype leaves the parent node open.
Benchmark compile latency, generated code size and steady-state execution
separately. Record restrictions and supported targets in this document.

## Approved design decisions

- Callable-first `Code<F>` and explicit lift instead of implicit capture.
- `quote fn`, `splice(...)`, `lift(...)` and `#[staged]` declaration spelling.
- Affine code values with explicit cloning only for reusable closed code.
- Compile-time sandbox and resource budgets.
- Runtime owner-bound callables and Linux x86-64 as the initial JIT target.

The user approved this design and autonomous implementation on 2026-11-17.
Approval covers routine implementation decisions; completion still requires
the acceptance criteria above.

## Implementation status

The parser recognizes quotation syntax, splice/lift operands and staged
function initializers structurally, retaining their original spans. These
forms use private AST call markers that cannot be written as source names;
ordinary AST visitors still traverse their operands. No source-text rewrite
or generated-source parser is involved.

`resolve_staged_program` resolves quoted templates with stage-indexed local
binding identities. It rejects implicit local captures, quoted locals used
inside an earlier-stage operand, and generated-function parameters used by
their generator initializer. Explicit lift/splice operands resolve one stage
earlier; module references retain the existing visibility checks. This
entry point resolves names only: it does not certify executable types,
ownership, generated code or safe compilation.

Executable checking now admits checked Code<F> values, explicit graph cloning,
quotes with scalar/owned-text lifts and typed splices, and nested quotation
levels. Staged declarations evaluate generators with a restricted effect row
and materialize ordinary checked native functions. Generation supports branches,
loops and recursion; the recursive power example runs in the evaluator and
Cranelift, while owned text and float lifting also have LLVM parity coverage.

The reference evaluator and Linux x86-64 Cranelift executables support
`Code.compile` and `Code.call`. The native runtime links checked machine-code
templates with graph constants and splice targets. Each compiled owner
releases its executable mapping when dropped. Compile-time generators
cannot invoke the runtime compiler. Runtime splices must be
immediately called in their own quotation. An LLVM executable carries the
same recipes, compiled by Cranelift from the same lowered functions: Kush
functions pass and return machine words in the platform C convention under
both backends, so recipes call the LLVM-compiled program directly.

Generators whose generics are unconstrained types and effect rows receive a
separate type, ownership and effect check: each type binder becomes a distinct
opaque type and each effect binder takes every row its bounds allow, when the
domain fits the specialization budget. Concrete specializations check
and encode lifted values. Generic staged declarations evaluate one initializer
per concrete specialization. Staged functions can also expose a native ABI
with `#[staged] export` on Cranelift and LLVM. Erased proof parameters and
shared length preconditions are checked at call sites. Nested closures can
own copies of lifted text, and compile-time staging specializes splices used
inside nested closures.

The [staged interpreter](../examples/staging-interpreter.kush) specializes a
fixed bytecode program and compares the generated function against the
interpreter across a range of inputs. The power example verifies that the
native executable omits the generators and their serialized code graphs.

A staged declaration with a mutable length refinement (`v: &mut Vec<T> where
len >= n`) admits its generated body only when that body, and every function
it reaches, uses operations that cannot shrink the vector.

Generators can use arenas. Arena chunks and payloads count against the same
generation budget as heap storage.

A native executable carries a machine-code recipe only for templates that a
reachable function can quote at run time. Templates used only by
`#[staged]` generators stay out of the binary.

## Restrictions

- Natural, grade and trait-bound generic binders follow the ordinary Kush
  rule for generics: each instantiation is checked, and a quotation is
  checked at every instantiation before its generator runs. An unused
  generator with such binders still gets the declaration-time checks that
  hold for every value: a fixed result type, and the effects of direct
  builtins against its row bounds. Checking it abstractly would be stricter
  than ordinary generic functions, which accept `fn third<N: Nat>(x: [i64;
  N]) { x[3] }` for N >= 4.
- `#[staged]` declarations with `ensures` are rejected. Postconditions are
  proved over source bodies, and a staged body exists only as generated IR.
- Custom allocator contexts, tasks and effect handlers are unavailable to
  compile-time generators.
- Runtime splices must be called immediately in their quotation. Runtime
  compilation supports Linux x86-64, in Cranelift and LLVM executables; the
  generated code itself is always Cranelift's.
- The runtime linker rejects any relocation kind or target it does not
  recognize, so `Code.compile` returns an error instead of publishing code.

Detailed constraints are in [the working notes](staging-runtime-notes.md).
