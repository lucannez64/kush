# Kush language specification v0.1

Status: design draft, 2026-10-30. No implementation conformance is claimed.

Kush is an eagerly evaluated functional systems language for application developers. It combines dependent types, algebraic subtyping, graded resource usage, explicit ownership, and checked effects. Its first target is Linux x86-64; its first substantial application is a parser/compiler.

**MUST**, **MUST NOT**, and **SHOULD** describe requirements for a conforming implementation of this draft. Examples specify proposed syntax, not currently executable programs. Sections explicitly marked **research gate** identify requirements whose full sound implementation is not yet designed. They MUST NOT be advertised as implemented guarantees.

## 1. Goals and boundaries

Kush aims to provide:

- Full dependent programming and mathematical proofs with an independently checkable logical core.
- Efficient functional APIs through ownership transfer, borrowing, and storage reuse.
- Memory and data-race safety in safe code without a required tracing collector.
- Predictable, enforceable allocation and suspension contracts.
- Exhaustive matching over ordinary and indexed enums, plus algebraic union/intersection types.
- Direct-style asynchronous I/O and structured concurrency.
- Fast development compilation through Cranelift, followed by an LLVM release backend.

The language does not promise globally optimal memory management, termination of arbitrary programs, automatic discovery of every true theorem, or identical performance to Rust. Runtime overhead, peak memory, compile time, and developer effort are separate measurements.

Macros, user-defined operator precedence, higher-kinded polymorphism, stable native ABI, general multi-shot effect handlers, distributed execution, and a full interactive tactic language are outside the first implementation milestone.

## 2. Execution model

Evaluation is strict and left-to-right for operands, call arguments, record fields, and array elements. A block's final expression is its value. Statements ending in `;` produce `Unit`. Lazy evaluation requires an explicit library abstraction.

Bindings are immutable unless declared `mut`. Assignment and mutation require exclusive access. Moving a value transfers ownership and invalidates the source binding. This rule applies equally in development and release builds.

```rust
fn square(x: i64) -> i64 ! {panic} {
    x * x
}

fn main() -> Result<Unit, AppError> ! {io, alloc, suspend, panic} {
    let source = fs.read_text("example.kush")?;
    let tokens = tokenize(source.as_str())?;
    let tree = parse(tokens.as_slice())?;
    io.println(tree.summary())?;
    Ok(())
}
```

Checked machine arithmetic may panic. A compiler can eliminate checks when it establishes their preconditions, but optimization alone cannot justify a false effect signature.

An executable function may diverge. A total logical function may not. Executable return types are partial-correctness claims: if a safe call returns normally, its result inhabits the declared type. They do not assert that it returns.

## 3. Lexical structure and syntax

Source is UTF-8. Ordinary identifiers initially use ASCII letters, digits, and `_`, and cannot start with a digit. Strings and comments accept Unicode. Identifier Unicode extensions may follow with explicit normalization rules.

- `//` introduces a line comment; `/* ... */` comments nest.
- Braces delimit blocks; whitespace is not structurally significant.
- Calls use `f(x, y)`; field access uses `value.field`.
- Generic arguments in expressions use `name::<T, n>(...)`; type positions use `Array<T, n>`.
- `()` is the `Unit` value. Tuples use `(a, b)`.
- `->` introduces a result type; `! { ... }` introduces an effect row.
- `&T` and `&mut T` denote shared and exclusive borrows.
- Modules use `module`, `use`, and `pub`; declarations are private by default.
- Attributes use `#[name]`. No user-defined syntax expansion is required.

Operator precedence, from tightest to loosest: postfix calls/indexing/field access/`?`; unary `!`, `-`, borrow; `* / %`; `+ -`; comparisons; `&&`; `||`; assignment. Comparisons do not chain. Binary arithmetic associates left; assignment associates right. Type unions use `|`; intersections use `&`, with intersection binding more tightly. Parentheses disambiguate borrows from intersections.

Public declarations MUST give parameter types, return types, and effect rows. Local inference may insert implicit arguments and resolve local types. If inference cannot decide, the compiler requests an annotation rather than changing semantics.

**Research gate:** a complete token grammar, precedence table for every pattern/type form, and grammar ambiguity tests are required before the parser is frozen. This draft fixes the syntax direction, not a complete language grammar.

## 4. Values and data types

Primitive runtime types include `Bool`, `Unit`, `Never`, fixed-width signed/unsigned integers, `usize`/`isize`, `f32`, `f64`, `Char`, and borrowed UTF-8 `str`. `String`, `Vec<T>`, and arbitrary-precision numbers are library types.

`Char` represents a Unicode scalar value. String length is measured in bytes unless an API explicitly says otherwise. Indexing a string by an arbitrary byte offset does not produce a character.

### 4.1 Records and enums

```rust
struct Span {
    start: usize,
    end: usize,
}

enum Token {
    Identifier(Span),
    Integer(i64),
    Plus,
    End,
}

enum Option<T> { None, Some(T) }
enum Result<T, E> { Ok(T), Err(E) }
```

Named records and enums are nominal. Enums are closed unless a future explicit extension mechanism is specified. Variants can carry positional or named fields. Separate tags remain distinct even if their payload types coincide.

Recursive types MUST have finite representation through indirection such as `Box`, an arena handle, or an explicit shared handle. Recursive logical data MUST additionally satisfy strict positivity.

### 4.2 Indexed enums

```rust
enum Expr<T: Type> {
    Integer(i64): Expr<i64>,
    Boolean(Bool): Expr<Bool>,
    Add(Box<Expr<i64>>, Box<Expr<i64>>): Expr<i64>,
    If(Box<Expr<Bool>>, Box<Expr<T>>, Box<Expr<T>>): Expr<T>,
}
```

Matching an indexed variant introduces the corresponding index equalities into that branch. These equalities refine branch-local types and do not escape their scope without evidence. Impossible branches can be omitted only when their impossibility is established.

### 4.3 Pattern matching

Patterns include variants, records, tuples, literals, wildcards, bindings, alternatives, fixed arrays, slices with a rest pattern, and nested patterns. Guards are Boolean expressions. Alternative patterns MUST bind the same names with compatible types and ownership modes.

```rust
match token {
    Token.Integer(0) => Zero,
    Token.Integer(n) if n > 0 => Positive(n),
    Token.Identifier(span) => Name(span),
    Token.Integer(_) | Token.Plus | Token.End => Other,
}
```

Matches MUST be exhaustive; unreachable branches receive a diagnostic. A guard does not establish coverage unless it is proven always true. For dependent matches where automatic coverage checking cannot decide, require additional evidence or an explicit remaining branch.

Guards borrow bindings until selection succeeds; they MUST NOT consume or mutate a scrutinee in a way that makes later branches invalid. Matching by value moves selected fields; matching a borrow borrows them. Ignored affine fields are dropped. Ignoring linear fields is an error.

## 5. Dependent types and logical soundness

Kush supports dependent function types, type families indexed by values, equality proofs, indexed data, and universes `Type<u>`. `Prop` contains logical propositions. Universe levels MUST prevent `Type : Type`; the initial design uses explicit levels with inferred constraints and no implicit universe cumulativity.

```rust
fn get<T: Type, n: Nat>(
    xs: &Array<T, n>,
    i: Nat,
    erased proof: i < n,
) -> &T ! {};

fn get_checked<T: Type, n: Nat>(
    xs: &Array<T, n>,
    i: Nat,
) -> Option<&T> ! {};
```

These are interface declarations. The output borrow is tied to `xs`. Here `i` is runtime relevant; `proof` is not. Runtime arithmetic on unbounded `Nat` can allocate even when proof-only arithmetic is erased. A fixed-size target array requires a representable length and successful layout checking.

The proof-required operation MUST reject a call if the obligation cannot be discharged. It MUST NOT silently insert a runtime check. The checked operation performs the documented check and returns `None` on failure. There is no implicit fallback between them.

### 5.1 Logical versus executable definitions

`total fn` defines a pure, terminating computation available for type checking and proofs. Its recursion MUST be structurally decreasing or accompanied by a checked well-founded termination argument. Logical data definitions require positivity checking.

Ordinary `fn` admits general recursion and effects. Merely calling an ordinary function cannot manufacture logical evidence. Proofs about executable code require an explicit logical model, checked correctness theorem, or another sound verified interface.

Type-level evaluation MUST NOT execute I/O, access mutable process state, consult arbitrary files, or unfold unsafe/partial implementations. Failure to normalize within an implementation resource budget is a diagnostic, never acceptance of an unverified obligation.

### 5.2 Erasure and automation

`erased` arguments are removed before runtime lowering. Runtime control flow MUST NOT depend on erased data. A proof cannot hide a file, buffer, or linear capability and thereby cause its runtime obligations to disappear. Eliminating propositions into runtime data is restricted to forms justified by the logical core, such as equality transport.

Initial automation supports definitional equality, constructor reasoning, and a documented bounded arithmetic fragment. Solver failure means “not established,” not “false.” External solvers and future tactics MUST produce proof terms or certificates checked by the trusted kernel.

No safe `admit` or unchecked theorem declaration is permitted. Imported assumptions MUST be declared and reported transitively. Foreign code and compiler optimizations do not become logical axioms merely because they execute successfully.

**Research gate:** specify the exact dependent core, universe rules, equality/elimination rules, normalization strategy, and trusted axioms. Its interaction with subtyping and grading requires a soundness argument before unrestricted combinations are enabled.

## 6. Algebraic subtyping

`A | B` denotes a union and `A & B` an intersection. Basic laws include:

```text
A <: A | B       A & B <: A
Never <: A      A | A = A      A & A = A
```

Subtype conversion MUST preserve resource obligations and be coherent: choosing a different valid elaboration path cannot change observable program behavior.

Named enum variants are not interchangeable just because their payloads overlap. Anonymous unions are normalized by type identity; `String | String` is simply `String`. Distinct semantic alternatives with the same payload require tags.

```rust
type LoadError = IoError | ParseError;
```

A function accepting `A` and producing `B` is contravariant in its input and covariant in its output, subject to compatible usage requirements and an included effect row. `&T` is covariant in `T` where lifetime rules permit. `&mut T` is invariant. Variance for user types is checked from their representation and operations.

Machine integers do not implicitly subtype one another; numeric conversion is explicit and may require evidence or return failure. Dependent index equality and subtype inclusion are distinct judgments. Invariant indices cannot be changed simply by widening a surrounding type.

Union representation may require a discriminator. Intersection types do not automatically authorize duplicating a resource or calling a linear function twice. Coercions that allocate MUST carry `alloc`; a `noalloc` context rejects them.

**Research gate:** algebraic subtyping applies first to a documented nondependent fragment. General intersections, dependent function subtyping, indexed unions, principal inference, and their interaction with grades require explicit rules. Arbitrary refinement implication is not an assumed decidable subtype test. The implementation MUST reject unsupported combinations explicitly rather than silently approximate them unsafely.

## 7. Ownership, grades, and borrowing

Every runtime resource has defined duplication and disposal permissions:

| Class | Duplication | Disposal |
| --- | --- | --- |
| Linear | Forbidden without an explicit operation | Must be explicitly consumed on every normal exit |
| Affine | Forbidden without an explicit operation | Automatic deterministic drop allowed |
| Unrestricted | Permitted by the type's duplication rules | Permitted |

Owned resources are affine by default. Small scalar types may implement compiler-checked `Copy`. A copied shared reference remains a borrow; it does not extend the owner's lifetime. Heap-backed sharing uses an explicit handle.

### 7.1 Graded modalities

The intended modality `T @[g]` controls access to a value with usage grade `g`. The initial usage algebra is the ordered semiring of natural usage bounds extended with infinity; surface grades include `0`, `1`, and `many`. Sequential use combines bounds additively, substitution composes them multiplicatively, and exclusive control-flow branches require a sound join rule.

Usage bounds alone express at-most usage. Exact consumption of a linear resource is a separate obligation, tracked across branches and normal exits. `many` does not itself make an arbitrary resource safely duplicable. A modality introduction rule must establish that sharing/duplication is permitted.

Logical grade-zero access is erased and cannot consume, retain, or duplicate runtime ownership. Type-level reasoning about a resource MUST use stable logical information, not inspect its mutable live state arbitrarily.

**Research gate:** complete graded typing rules, constraint solving, modality introduction/elimination, and interaction with dependent substitution and borrows. General user-defined grade algebras are deferred. This notation is a design interface, not a claim of a finished calculus.

### 7.2 Borrows and moves

`&T` allows temporary shared access; `&mut T` allows temporary exclusive access. An exclusive borrow excludes conflicting access. A borrow cannot outlive its owner, move an owner while still live, or escape a region that bounds it. Local lifetimes may be inferred; public APIs require explicit lifetime parameters when elision is ambiguous.

Partial moves of records are permitted only if remaining fields can be cleaned up correctly. Types with custom destruction may restrict partial moves. Raw address exposure does not weaken these rules in safe code.

```rust
let config = load_config()?;
scope {
    spawn || serve_api(&config);
    spawn || run_jobs(&config);
}
// Both tasks have completed, including cleanup, before config can be dropped.
```

Captures are checked as moves or borrows; ownership capture is not an implicit deep copy.

### 7.3 Explicit shared ownership and cycles

`Shared<T>` is a thread-local shared owning handle; `AtomicShared<T>` supports cross-thread ownership when `T` satisfies the required safety bounds. Constructing these handles may allocate. Cloning a handle is explicit and does not deep-copy its payload. Reference-count overflow MUST be handled safely, never by premature freeing.

Strong ownership cycles are not automatically collected. Cyclic relationships SHOULD use arenas and validated handles or weak references. Weak upgrade returns an option. Arena handles MUST prevent stale access after removal or arena destruction, including generation reuse/wraparound.

Safe code guarantees absence of invalid memory access, not universal absence of leaks. Strong cycles, intentionally leaked ownership, and process abort are explicit limits.

## 8. Functional updates and memory contracts

Consuming a unique input permits mutation behind a functional interface:

```rust
#[noalloc]
#[nosuspend]
fn increment_all(xs: Vec<u64>) -> Vec<u64> ! {panic} {
    xs.map_in_place(|x| x + 1)
}
```

The implementation may update existing elements. If arithmetic panics, execution aborts under the initial panic policy. No rollback is implied. Shared data MUST NOT be overwritten while observable through another owner or borrow.

Ordinary functional transformations may reuse storage opportunistically. A guaranteed in-place API MUST state capacity, uniqueness, and representation preconditions. If they cannot be established, compilation fails or the caller chooses a separately named fallible/allocating operation. There is no hidden allocation fallback under `noalloc`.

`noalloc` forbids dynamic storage acquisition on every reachable path, including transitive calls, coercions, closure environments, arbitrary-precision arithmetic, task frames, and cleanup. It does not forbid fixed-size stack storage or deallocation. Runtime-sized stack allocation is unavailable in the initial safe language. A function using a caller-provided arena can be `noalloc` only if it consumes already reserved storage without acquiring more memory; its region effects remain tracked.

`nosuspend` forbids suspension on every reachable path, including callbacks and cleanup. It does not imply that blocking I/O is absent. Neither annotation promises bounded execution time, bounded stack depth, or freedom from synchronization.

These guarantees MUST hold in both backend modes without optional optimization. Mandatory lowering and verification may establish them. A final IR verifier SHOULD detect accidental introduction of prohibited operations.

## 9. Effects and purity

Effect rows describe permitted effects, for example:

```rust
fn checksum(data: &[u8]) -> u64 ! {};
fn load(path: &Path) -> Result<Bytes, IoError>
    ! {io, alloc, suspend};
```

Initial tracked effects are `io`, `alloc`, `suspend`, `panic`, and region-indexed `state<r>`. Deallocation/refcount bookkeeping is governed by ownership and observable cleanup rules rather than being equated with allocation. FFI calls MUST declare a conservative effect contract.

Effects compose by row union. Functions with fewer effects may be used where more are allowed, provided their other type/usage rules agree. Higher-order functions use effect variables:

```rust
fn map<T, U, e: Effects>(xs: Vec<T>, f: fn(T) -> U ! e)
    -> Vec<U> ! {alloc, e};
```

`Result` failure is an ordinary return value, not an exception effect. Divergence is tracked separately as totality eligibility for the logical core; an empty effect row alone is not a termination proof.

Local mutation may be encapsulated when a region cannot escape or alias observable state. Consuming unique storage similarly permits externally pure transformations. Such encapsulation MUST NOT hide I/O, allocation, suspension, or observable destructor effects. Effects do not replace capability values: an I/O effect alone is not possession of a file handle.

Proof erasure must not erase runtime effects. Diagnostics SHOULD show a call path explaining any violated effect contract.

**Research gate:** formalize region encapsulation, callback multiplicity, and effect-row inference with subtyping and grades. Arbitrary user-defined control effects are deferred; built-in suspension does not require exposing unrestricted continuation capture.

## 10. Async and structured concurrency

Suspending calls use ordinary call syntax. There is no mandatory `async fn`/`await` distinction. The `suspend` effect propagates through calls and remains visible in public signatures and editor tooling.

```rust
fn fetch(url: &Url) -> Result<Bytes, NetError>
    ! {io, alloc, suspend} {
    let response = http.get(url)?;
    response.read_all()
}
```

`scope { ... }` owns child tasks. It cannot finish until all children terminate and complete cleanup. Spawn is explicit; an ordinary call does not implicitly start a concurrent task. Cross-thread tasks require transferable captures; shared captures require thread-safe access. Detached tasks are outside the initial safe task API.

Suspension may retain owned values and borrows in a task frame. Their lifetimes MUST cover the suspension and all subsequent use. Capturing a linear resource into a continuation cannot duplicate it. Initial internal resumptions are at-most-once; cancelling/dropping a suspended continuation invokes its cleanup obligations.

A standard task scope is fallible and exits with a result. On an unhandled child failure, it requests sibling cancellation and joins all children before returning an error. An explicit supervisor abstraction can instead collect results. Which failure wins in a race is unspecified; all resources still obey cleanup rules.

Cancellation is cooperative at documented suspension/check points. At a task boundary it produces `TaskExit<T> = Completed(T) | Cancelled`; it is not implicitly converted to an arbitrary application error. A noncooperative task may prevent its scope from exiting. Cancellation is not arbitrary thread termination and does not guarantee bounded shutdown time.

No suspension occurs during automatic destruction. Operations such as flushing, protocol close, and asynchronous rollback are explicit and run before synchronous destruction. A task owning a linear protocol token must provide a legal cancellation transition or execute within a checked cancellation-masked region with appropriate exits.

**Research gate:** define cancellation masking, linear task exits, scheduler fairness, and suspension lowering before shipping async. Stackful versus stackless representation is an implementation decision constrained by effects and lifetime safety. Task-frame allocation is charged to an explicit API and cannot disappear from `noalloc` contracts.

## 11. Errors, panic, and cleanup

```rust
fn read_settings(path: &Path) -> Result<Settings, ReadError>
    ! {io, alloc, suspend, panic} {
    let text = fs.read_text(path)?;
    parse_settings(text.as_str())
}
```

`?` on `Result<T, E>` returns the error from the enclosing result-returning function. On that return, all owned affine locals are dropped. Linear resources MUST have legal consumption paths; an early return cannot discard them. Initial propagation supports identical error types and nonallocating union injection. Other error conversions are explicit and carry their effects.

Expected failures use `Result`; absence uses `Option`. Panics represent failed assertions and other unrecoverable defects. Initial panic behavior is process abort with no promise of running destructors. Ordinary executable functions may abort even if they return a proof-shaped value; they are not accepted as logical proofs.

Affine locals drop in reverse binding order at lexical scope exit, unless moved. Record fields drop in reverse declaration order; container element order is documented by that container. Early reclamation/reuse is permitted only when it preserves observable destruction semantics. Compiler last-use analysis alone cannot reorder observable cleanup.

Automatic cleanup MUST terminate, MUST NOT suspend, allocate, or panic, and MUST NOT return a recoverable error. It may perform a documented nonblocking resource release with an appropriate effect contract; failure cannot be silently presented as successful explicit completion. User-level finalization with broader effects is an explicit method, not automatic destruction.

A linear value must be explicitly consumed on every normal, error, and supported cancellation exit. Abort is outside the normal resource-completion guarantee.

Allocation is fallible through APIs such as `Vec.try_reserve` and `Box.try_new`. Convenience infallible allocation aborts on exhaustion and includes `panic`. Logical computations do not gain unbounded implementation resources: compiler exhaustion is a diagnostic, not a theorem.

## 12. Arithmetic and representation

Machine integer operations check overflow in every build. Division by zero and signed minimum divided by `-1` are checked. Explicit methods provide wrapping, checked-result, and saturating arithmetic. Casts that may lose information return failure unless supplied a checked proof or an explicit truncation operation.

`Nat` and `Int` denote unbounded mathematical numbers. Proof-only values can erase; runtime values use allocation-capable representations. Logical arithmetic is not silently machine arithmetic.

Floating-point operations follow the target's specified IEEE behavior; algebraic reassociation is disabled by default. Fast-math requires an explicit opt-in contract. NaNs and signed zero prevent assuming ordinary mathematical equality laws for floating-point values.

Native layouts are unspecified across compiler versions. `#[repr(C)]` gives supported C-compatible layout for eligible types. Other explicit layout controls include alignment and fixed-width enum tags. Packed fields cannot be borrowed as naturally aligned references without validation or copying. Optimizations such as niche encoding MUST preserve safe observables.

`Array<T, n>` is inline storage with statically representable layout. `Vec<T>` is owned growable storage. `&[T]` is a borrowed slice. Runtime-varying lengths use a dependent package or slice rather than an unknowable by-value stack layout.

## 13. Unsafe code, FFI, and concurrency safety

`unsafe { ... }` permits specified operations, not arbitrary weakening of surrounding type checking. Raw-pointer dereference, unverified foreign calls, and unchecked representation conversions require unsafe code. Unsafe code cannot create accepted logical evidence without a separately declared trusted assumption.

Safe wrappers MUST establish pointer validity, alignment, initialization, lifetime, aliasing, thread-safety, and foreign ownership obligations. The unsafe specification must define these obligations before FFI is considered stable. Undefined behavior is reserved for documented unsafe-contract violations, not ordinary safe overflow or failed bounds checks.

An unsafe foreign declaration includes calling convention, effects, ownership transfer, callback multiplicity, and whether it retains or invokes callbacks after returning. Foreign exceptions must be caught at the boundary; unwinding across Kush frames is unsupported initially.

A Rust-like distinction between transferable values and safely shared values is required. Initial names are `Send` and `Sync`; they are compiler-checked structural properties with tightly controlled unsafe implementation escape hatches. Shared mutation requires synchronization or an abstraction proving exclusive access.

The initial safe atomic API provides sequentially consistent operations only. The concurrency memory model MUST define data races and happens-before before weaker orderings are exposed. Borrow checking is not a substitute for an atomic memory model.

## 14. Generics, modules, and compilation boundaries

Generic parameters can range over types, relevant/erased values, regions, effects, and supported grades. Trait constraints describe operations and associated types. Implementations must satisfy their declared effect and resource contracts.

Initial trait resolution is coherent: an implementation is permitted only in the module/package owning the trait or the target nominal type, and overlapping implementations are rejected. Specialization and implicit user-defined conversions are deferred.

Modules compile against explicit public signatures. Private inference details cannot alter exported effects or ownership requirements. Initial runtime generics are monomorphized; explicit dynamic interfaces may use vtables with documented allocation/layout costs. Unbounded specialization on runtime indices MUST be rejected or use a separately specified uniform representation.

The compiler MUST serialize logical interfaces and check imported proof artifacts or their trusted-kernel equivalents. Dependency hashes, compiler versions, and trusted assumptions are part of build provenance. Safe runtime code and logical trust are separate boundaries.

## 15. Compiler architecture

The planned pipeline is:

```text
UTF-8 source
  -> tokens and syntax tree
  -> names and explicit module interfaces
  -> elaborated dependent/graded/effect-checked core
  -> independently checked proof terms
  -> erasure and representation selection
  -> ownership-aware intermediate representation
  -> closure/suspension conversion and explicit memory operations
  -> mandatory resource-contract validation
  -> Cranelift initially / LLVM later
  -> object files and native linker
```

Some checks necessarily iterate during elaboration. This diagram defines responsibilities, not a requirement for exactly one pass per stage. Fusion and reuse optimization operate only where semantics permit; allocation contracts must already be justified or verified after mandatory lowering.

Both backends MUST agree on evaluation order, arithmetic checks, ABI within a build, task behavior, error propagation, and destruction. Optional optimization cannot change safe observable behavior. Cranelift is the initial implementation backend; LLVM is a later release option rather than a prerequisite.

A small reference evaluator SHOULD cover the executable core. Differential tests compare it with native backends. Proof-kernel tests, negative type/effect/ownership cases, parser fuzzing, and backend differential tests are conformance tools, not a substitute for a soundness argument.

Diagnostics SHOULD explain why a value moved, why a borrow remains live, which branch lacks linear consumption, which proof obligation failed, and which operation introduced allocation or suspension.

## 16. First application: a parser/compiler

The first end-to-end application reads a source file, tokenizes it, creates an arena-backed AST, checks a small expression language, and emits/evaluates a result. It need not initially compile Kush itself.

Suggested interfaces:

```rust
fn tokenize(source: &str) -> Result<Vec<Token>, LexError>
    ! {alloc, panic};

fn parse(tokens: &[Token], arena: &mut Arena<AstNode>)
    -> Result<NodeId, ParseError> ! {alloc, panic};

fn check(ast: &Ast, context: &Context)
    -> Result<TypedModule, TypeError> ! {alloc, panic};

fn emit(module: TypedModule) -> Result<ObjectFile, CodegenError>
    ! {alloc, panic};
```

These interfaces are non-I/O computational phases; the outer driver owns file I/O. Initial arena growth can allocate. A later bounded parser API can accept fixed-capacity storage and return `CapacityExceeded` instead of acquiring memory.

Application acceptance examples:

1. Token/AST enum matches detect missing variants.
2. Borrowed source spans cannot outlive the source buffer.
3. Stale arena handles cannot read removed nodes.
4. A proven bounds access emits no runtime bounds branch.
5. A checked access returns failure instead of invoking undefined behavior.
6. A `noalloc` transformation rejects an allocating callback or coercion.
7. A `nosuspend` compiler phase rejects a suspending callback.
8. An early `?` releases affine storage and rejects an unconsumed linear obligation.
9. A proof cannot inspect erased runtime resources or unfold a partial function.
10. Native execution agrees with the reference evaluator on successful values and documented failures.

## 17. Implementation sequence and research gates

The following sequence implements subsets of this target specification. A subset MUST state its supported features and reject the remainder explicitly.

1. Freeze lexical grammar; implement parser, modules, spans, and diagnostics.
2. Define the trusted dependent core: universes, total functions, positive data, equality, erasure, and simple proof automation.
3. Implement ordinary enums, matches, explicit effects, affine moves, borrows, cleanup, and a reference evaluator.
4. Establish the graded/dependent/ownership rules and implement a restricted, tested combination.
5. Add algebraic subtyping to a delimited fragment; validate coherence and representation costs before expanding it.
6. Lower the synchronous executable subset through Cranelift; build the first parser/compiler application.
7. Add checked reuse/fusion, contract verification, and allocation diagnostics.
8. Specify and implement structured async, cancellation, and runtime support.
9. Add LLVM and backend differential conformance; then investigate minimal-runtime/embedded profiles.

Before claiming the complete language, resolve:

- Sound interaction of dependent equality, subtype coercions, grades, and erasable proofs.
- Decidable supported fragments and explicit diagnostics at their boundaries.
- Cancellation with linear resources and nonsuspending destruction.
- Pointer/aliasing model, atomic semantics, and sound FFI wrappers.
- Preservation of memory/effect contracts through erasure and code generation.

Future kernel/embedded support must allow opting out of the standard allocator, task scheduler, operating-system I/O, and arbitrary-precision runtime arithmetic. It will be a documented platform profile, not a claim that all application libraries work without a runtime.

## 18. Research foundations

These sources motivate individual mechanisms. They do not establish soundness or performance of their combination in Kush.

- [Quantitative program reasoning with graded modal types](https://kar.kent.ac.uk/74450/) — graded modalities combined with linear and indexed types in Granule.
- [Perceus: Garbage Free Reference Counting with Reuse](https://xnning.github.io/papers/perceus.pdf) — precise reference counting, reuse, and the limits of the garbage-free result.
- [FP²: Fully in-Place Functional Programming](https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf) — stronger storage/stack guarantees for a restricted functional calculus.
- [The Simple Essence of Algebraic Subtyping](https://infoscience.epfl.ch/server/api/core/bitstreams/afe084e0-0050-4542-99c7-c499d2fe1620/content) — a foundation for algebraic subtype inference, not an off-the-shelf dependent/linear solver.
- [Structured Asynchrony with Algebraic Effects](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/05/asynceffects-msr-tr-2017-21.pdf) — structured asynchronous control using typed effects.
- [Lean reference: recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/) — separating executable partial recursion from logical computation.
- [Austral specification](https://austral-lang.org/spec/spec.html) — linear resources and borrowing as a systems-language reference.
- [Cranelift](https://cranelift.dev/) — the initial native backend.
