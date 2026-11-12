# Runtime enums, patterns, and Result

The executable subset now supports nominal enums with unit/tuple variants,
ordinary type parameters, nested inline payloads, exhaustive pattern matching,
and `Result` propagation. Both the reference evaluator and Cranelift execute
these operations. These are runtime data types; they do not add unchecked data
or new axioms to the logical kernel.

```sh
cargo run -p kush -- check examples/results.kush
cargo run -p kush -- eval examples/results.kush
cargo run -p kush -- run examples/results.kush
cargo run -p kush -- build examples/results.kush -o target/results
./target/results
```

The example prints `42`, `65`, `7`, and `99` on separate lines. It parses two digit
codes, returns a typed `ParseError`, propagates errors with `?`, and matches a
nested `Option<Result<i64, ParseError>>`.

## Declarations and construction

Enums are declared in the source file; there is no automatic Result/Option prelude
or standard-library module loader yet.

```rust
enum Result<T, E> { Ok(T), Err(E) }
enum Option<T> { None, Some(T) }
enum ParseError { InvalidDigit(i64), OutOfRange }
```

Generic parameters must be ordinary types, either unannotated or bounded by
`Type`. Indexed/GADT variant results and record-style variant payloads remain
unsupported by executable checking. Empty enums are deferred. Enums themselves
have no lifetime parameters and cannot store slice views, borrowed or mixed records, or
other stored borrows; keep such a record in a lexical value and pass it to
an enum-producing function only through an ordinary channel that does not store
the borrow. Ordinary runtime
functions remain monomorphic, but they can accept/return any supported concrete
instantiation of a generic enum.

Constructors may be qualified, such as `ParseError.InvalidDigit(65)`, or use a
unique short name, such as `Some(1)`. Ambiguous short names require qualification.
Local/global shadowing follows lexical resolution, rather than selecting a
constructor just because its spelling matches a familiar name.

Generic constructors obtain arguments from the expected type:

```rust
let value: Option<Result<i64, ParseError>> = Some(Ok(7));
```

An expected type propagates from function returns, explicit return expressions,
annotated locals, assignment targets, call/constructor parameters, and containing
if/match expressions. A later if/match branch can also use the type established
by an earlier nondiverging branch.

Without that context, supply **all** type arguments on the constructor:

```rust
let value = Result.Ok::<i64, ParseError>(7);
let empty = Option.None::<i64>;
```

Payload-based generic inference and global constraint solving are not implemented.
Constructor arity and every payload type are checked. Distinct enum declarations
remain distinct even when they have identical layouts. Instantiations such as
`Option<i64>` and `Option<Bool>` are also distinct types.

A unit variant is a value without parentheses; a tuple variant is called:

```rust
enum Example { Unit, EmptyTuple(), Value(i64) }
// Example.Unit, Example.EmptyTuple(), Example.Value(1)
```

`Unit` and `()` are supported as the unit type; `()` is its value and pattern.
Nominal enum equality is deliberately unsupported rather than silently
comparing only tags. Anonymous structural records have field-by-field `==`/`!=`
when every leaf is a copyable scalar or a nested structural row; use pattern
matching for nominal enums and for structural records with owning, borrowed,
union, nominal, or floating-point fields.

## Pattern matching

Patterns can nest variants, scalar literals, wildcards, catch-all bindings, unit,
and alternatives. Payload patterns must have the variant's exact arity and types.

```rust
match result {
    Ok(value) => print_i64(value),
    Err(ParseError.InvalidDigit(code)) => print_i64(code),
    Err(ParseError.OutOfRange) => print_i64(-1),
}
```

Alternative patterns bind the same names, with the same concrete types. Different
payload positions are supported:

```rust
enum Either { Left(i64, Bool), Right(Bool, i64) }

fn number(value: Either) -> i64 ! {} {
    match value {
        Either.Left(n, _) | Either.Right(_, n) => n,
    }
}
```

Bindings are immutable and local to their match arm, including its guard. The
scrutinee is evaluated once. Alternatives select the first matching alternative;
guards run only after a complete pattern succeeds. Payload construction and calls
retain left-to-right evaluation order. Enums without owning fields remain copyable. Enums containing boxes now move,
and their ignored/unused owned fields are reclaimed; see [ownership.md](ownership.md).
Records, unlike enums, may declare lifetimes and store shared `&'a [T]` fields;
see [borrowed and mixed records](borrowed-records.md).

Coverage uses a pattern matrix, not just a set of top-level tags. It checks nested
Boolean cases and combinations across multiple payload fields/arms. For example,
`Pair(true, _)` plus `Pair(false, true)` still leaves `Pair(false, false)` uncovered.
Integer fields need catch-all coverage because listing a few integer literals
cannot cover their domain. A guard contributes no exhaustiveness coverage.
Completely unreachable arms are rejected. Partial redundancy inside an alternative
may still be accepted; comprehensive redundancy warnings are future work.

Coverage has a 50000-unit complexity budget per match. Exhaustion reports an error;
it never treats an unproved match as exhaustive. Split/simplify complex matches
or use appropriate catch-all patterns. The regression suite compares checker
acceptance against an independently enumerated finite-domain model.

## Result propagation

`?` requires exactly the conventional generic declaration:

```rust
enum Result<T, E> { Ok(T), Err(E) }
```

The two variants may appear in either order. Each must have exactly one tuple
field referring to its corresponding type parameter; merely naming an unrelated
enum `Result` is insufficient.

```rust
fn parse_two_digits(a: i64, b: i64) -> Result<i64, ParseError> ! {panic} {
    let first = digit(a)?;
    let second = digit(b)?;
    Ok(first * 10 + second)
}
```

On `Ok(value)`, `?` produces the value. On `Err(error)`, it immediately returns
`Err(error)` from the enclosing function. The operand is evaluated once. Later
arguments/statements are skipped on the error path. The enclosing return must
also be a conventional `Result` with an **identical** concrete error type.
Its success type may differ, including having a different inline layout size.
There are no implicit error conversions, union injections, or Option propagation
in this milestone; those require later conversion rules.

Constructing/matching/propagating these value enums introduces neither `panic`
nor `io`. Existing operations/calls retain their declared effects. The bootstrap
`print_i64` helper still aborts on output failure; this milestone enables typed
application errors but does not yet provide recoverable operating-system I/O APIs.

## Layout and calling convention

Native enum values are inline sequences of 64-bit words: one tag, followed by
space for the largest variant payload. Payloads concatenate their fields;
nested enums include their own tags and payload space. Inactive words are
initialized to zero. Construction, copying, and propagation of these enum values
require no runtime heap allocation or tracing collector.

Function arguments flatten those words into the internal calling convention.
Enum results use a hidden pointer to a caller-owned, aligned, fixed-size stack
buffer; every normal return writes the entire result. If/match joins and mutable
locals use one SSA value per word. The native ABI is private/unstable and has no
`repr(C)` or arbitrary FFI guarantees.

The reference evaluator uses a separate semantic representation of variant tags
and nested field values. It does not imitate native padding/word offsets. Native
versus reference tests cover nested payloads, wide aggregates spilling past the
argument registers, return buffers, recursion, assignment joins, reordered
Result tags, alternative binding positions, and early propagation.

Layouts must be finite. Direct/mutual inline recursion is rejected. Recursive structures may now use
unique `Box<T>` indirection with the [owning subset](ownership.md).
Finite nesting such as `Wrap<Wrap<i64>>` is supported. Generic enum definitions
are structurally validated when declared, and their concrete layouts are checked
when instantiated. Non-generic enum layouts are checked even if unused.

Initial limits are 64 variants per enum, 32 words per concrete enum (256 for a
nominal record, see [places](places.md)), 32 active
layout levels, 256 concrete enum instantiations, and 128 flattened argument words
per function, alongside the existing frontend/function/local limits. Exceeding a
limit is a diagnostic. Compiler/interpreter bookkeeping may allocate in Rust;
these layouts alone do not establish the spec's general resource model. Checked
`noalloc`/`nosuspend` functions now exist for the [supported operation set](ownership.md).

Still deferred: general owning containers, record payload syntax, enum equality,
public layout controls, aliases, generic functions, general resource linearity,
runtime dependent indices, proof erasure, structural record subtyping, fusion,
and async. First-class functions and arrow subtyping are implemented separately
in [functions.md](functions.md). Boxes and restricted immutable box borrows are now implemented
separately. Heterogeneous union/intersection values are described in
[subtyping.md](subtyping.md).
