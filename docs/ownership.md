# Unique boxes, affine ownership, and scoped borrowing

Kush now has a first owning heap type, `Box<T>`, in both the reference evaluator
and Cranelift backend. Boxes, [byte buffers](bytes.md), and enums containing either are affine: values move
instead of being implicitly duplicated, and unused owners are reclaimed
automatically. This is a restricted ownership foundation, not the complete graded
or dependent resource system proposed in [v0.1](spec-v0.1.md). Natural and
abstract exact usage grades are documented separately in [usage grades](grades.md).

```sh
cargo run -p kush -- check examples/ownership.kush
cargo run -p kush -- eval examples/ownership.kush
cargo run -p kush -- run examples/ownership.kush
cargo run -p kush -- build examples/ownership.kush -o target/ownership
./target/ownership
```

The example prints `42`, `42`, and `6`. It borrows a box for inspection, moves it,
consumes a boxed list, and automatically destroys another list at scope exit.

## Operations and effects

```rust
let value = Box.new(42);   // Box<i64>, effects {alloc, panic}
let moved = value;         // moves ownership; value is now unavailable
let number = Box.take(moved); // i64; consumes/frees the outer box
```

- `Box.new(value)` transfers the value into a unique allocation and returns its
  owner. Pointee types are inferred from the argument or an expected `Box<T>`.
  It requires `alloc` and `panic`; allocation failure aborts. A fallible
  `Box.try_new` API is deferred.
- `Box.take(owner)` consumes a box, transfers its payload out, and releases the
  outer allocation. It does not destroy the transferred payload or allocate.
- `Box.reuse(owner, new_payload)` consumes a box, destroys its old affine
  payload exactly once after both arguments evaluate, and stores a non-wider
  new payload in the same allocation. Linear old payloads are rejected because
  reuse would drop them implicitly. See [checked reuse](reuse.md).
- `Box.read(reference)` takes an immutable `&Box<T>` and copies its payload only
  when `T` contains no owning boxes or byte buffers. Owned payloads require `Box.take` instead.
- `drop(value)` consumes a value and recursively destroys any owned contents.
  It is optional for affine values; automatic cleanup covers unused owners.

These operations require exactly one value argument. Explicit generic operation
specialization, raw pointers, user destructor hooks, and reference counting are
not provided by this interface. Box handles have no equality/address conversion
operation in safe source code.

Allocation is an effect even if its result is quickly destroyed. The executable
effect rows now accept `alloc`, `io`, and `panic`. Calls propagate their declared
effects, including allocation. Borrowing, reading copyable payloads, taking,
and destroying boxes add no allocation or suspension effect.

## Affine checking and control flow

Scalars and enums whose payloads are all copyable remain implicitly copyable.
A box is owning regardless of its pointee. `Bytes` is also owning. An enum becomes owning if any variant
contains an owning field, including through nested enum instantiations. This is
a type property: even an empty variant of an owning enum moves.

```rust
let a = Box.new(1);
let b = a;
drop(a); // error: use after move
```

All fields and call arguments evaluate left-to-right. Reusing an owner in a later
argument is rejected. Each normally returning branch must leave a value available
before it can be used after a join. A move in one possible branch makes the old
owner unavailable after that join. Returning/aborting branches do not constrain
availability on a surviving branch. Short-circuit expressions conservatively
account for the possible right-hand path.

Mutable owning locals can be reinitialized after a move. Overwriting a still-live
owner destroys its old value after the replacement expression succeeds. A
replacement that moves the old owner, such as `b = b`, transfers it without an
intermediate free. Conditional availability uses runtime cleanup flags, rather
than freeing an owner that was already moved on another path.

Owned pattern bindings receive ownership only after a guard succeeds. Guards may
borrow an owned binding but cannot consume or replace owned locals. Failed guards
leave the scrutinee intact for subsequent arms. Ignored owning fields are destroyed
when the selected pattern transfers its other fields. Unused owning arm bindings
are destroyed when the arm ends. Alternative binding names/types are still checked.

A `@[1]` owning binding is additionally linear. Moving it into an ungraded local,
assignment, constructor, or `Box.new` extends that obligation to the destination;
a wildcard/omitted field or an ungraded callee that could drop it is rejected.
Value-carrying builtins such as `Vec.push` reject a linear argument. Returning
such a value through an ungraded result of a non-linear type is rejected;
annotate the result with `@[1]`, which transfers the obligation to the caller
and requires exactly one consumption there. See
[usage grades](grades.md#result-transfer-contracts) for the full boundary.

## Borrows, lifetimes, and exclusive slice views

```rust
#[noalloc]
fn inspect(value: &Box<i64>) -> i64 ! {} {
    Box.read(value)
}

fn main() -> Unit ! {io, alloc, panic} {
    let value = Box.new(42);
    print_i64(inspect(&value));
    print_i64(Box.take(value)); // the preceding borrow has ended
}
```

Shared owner borrows remain call-scoped for `&Box<T>`, `&Bytes`, and `&Vec<T>`.
`&name` borrows an existing owned local, and a borrowed parameter can be forwarded
to another call. Returning these owner references is still rejected.

Slice views are handled by the lifetime-aware system described in
[lifetimes.md](lifetimes.md): functions may declare `'a`, return checked borrowed
`&'a [T]` and `&'a mut [T]` views tied to caller storage, and release a local
loan at its checked last use rather than only at block end. `&mut [T]` adds an
exclusive, move-only capability over an array, vector, or byte buffer. While it
is live and not suspended the owner cannot be read, moved, dropped, replaced, or
borrowed again. Mutable views can be narrowed to child views and returned from
helpers; the parent capability is suspended until the child's last use, and
shared storage cannot be upgraded to mutable. A checked
`Slice.split_at_mut` pair is the only source of simultaneous disjoint mutable
siblings: each child is an ordinary move-only view, both suspend the parent, and
the sibling exemption is limited to opposite sides of that checked split.

Records may now store shared or exclusive slice views when they declare the
field lifetimes. A record such as `struct Window<'a, T> { view: &'a [T], start:
i64 }` owns no storage: its field descriptors point at the original
array/`Vec`/`Bytes` storage. A record with `view: &'a mut [T]` is affine and
move-only transitively. Copies of shared-only records, destructuring, helper
results and field aliases retain the per-field lifetime and owner provenance
until their checked last use, and the owner cannot be moved, dropped or replaced
while any field view is live. An exclusive field must be extracted by
destructuring first; direct projection is rejected.

Mixed records may also contain `Box<T>`, `Vec<T>`, `Bytes`, or ordinary owning
records/enums whose payload contains no borrow. Their owned fields move and are
freed exactly once, while borrowed fields only keep their owners loaned. Record
lifetimes remain zero-runtime-cost and carry no hidden allocation or reference
count. Records cannot contain streams, unions, callables, task handles, linear
fields, or `Box`/`Vec`/array storage of a borrowed record; they cannot be stored
in enums/unions/containers, cross a generic type parameter, or be captured by a
closure/task. Self-reference is rejected. The exact contract and limitations are
in [borrowed and mixed records](borrowed-records.md).

A scoped borrowed-capture `once fn` is an aggregate loan holder. Capturing a
mutable view moves that capability into the closure; capturing a shared view
adds a shared alias. The closure environment owns only the view descriptors and
never the array/`Vec`/`Bytes` storage, so its drop cannot free an owner. Its
loans last until its checked last call or lexical scope end, and call consumption
or an uncalled scope-end drop releases exactly the environment allocation. A
borrowed capture cannot be moved to another local, returned, stored, passed to a
helper, or captured by a task; see [lifetimes.md](lifetimes.md) and
[functions.md](functions.md).

A mutable scalar capture is also a scoped borrow rather than an owning move.
The closure environment stores a non-owning pointer to the caller's binding.
A writing capture is an exclusive loan: the captured location cannot be read,
assigned, moved, or dropped while the closure is live. A read-only capture is a
shared loan: other reads are allowed, but a write is rejected. The loan is
tracked by the same backward last-use analysis as slice views and ends at the
closure's checked last call or lexical scope end.
The pointer is stack storage, never a heap owner; dropping an uncalled closure
or calling it releases only the environment allocation. Escaping through a
return, record, box, union, helper call, adapter, or spawned task is rejected
before either backend sees the value.

Borrow lifetimes include the remainder of argument evaluation and the call itself:

```rust
// rejected: the first argument still borrows value while the second moves it
f(&value, Box.take(value));
```

Conditional references retain loans on every possible owner. Nested calls release
temporary owner borrows when they return a non-reference result. Slice views use a
backward liveness fixed point over the checked IR, including loop back-edges,
branches, short circuits, early returns, `?`, calls, and task suspension. The
compiler also rejects moving, dropping, or replacing an owner while a relevant view
is live.

Native owner borrow handles still point to a fixed-size stack snapshot of the owner
handle; the allocation remains owned by the original binding. Slice views, by
contrast, point at the original array stack cell or vector/byte storage, including
when returned from a helper. No payload ownership is copied by a borrow.

## Recursive owning enums

```rust
enum List { Nil, Cons(i64, Box<List>) }

#[noalloc]
fn sum(list: List) -> i64 ! {panic} {
    match list {
        List.Nil => 0,
        List.Cons(head, tail) => head + sum(Box.take(tail)),
    }
}
```

Regular generic recursion such as `List<T>` referring to `Box<List<T>>` is
supported. Mutually connected finite layouts, including `Box<Wrap<List>>`, work.
The type graph reserves nominal instances before resolving their fields; a
separate layout pass rejects cycles that do not pass through a box. Boxes have
one-word handles, so their pointee's inline size does not create a layout cycle.

Direct inline recursion is still invalid. Non-regular recursive instantiations
that change their type arguments, such as `G<T>` containing `Box<G<Box<T>>>`, are
rejected. Box payloads cannot contain stored references. Ownership does not permit
constructing strong cycles: there is no handle duplication or mutable pointer
assignment API. Shared/cyclic graphs still require future arenas or explicit
sharing abstractions.

## Deterministic cleanup and early exits

Cleanup covers normal lexical scope exit, unused/discarded values, overwrites,
match bindings, function parameters, explicit returns, and `?` propagation.
Boxes inside enums are recursively destroyed according to the active variant.
Destruction releases fields deterministically and invokes no user code. It cannot
suspend or allocate. Panic still aborts the process without a cleanup guarantee.

An ownership pass marks moves and assigns a resource slot to owning locals and
owning expression results. Native lowering maintains live flags and associated
values for these slots. Moving or handing a value to a callee/constructor clears
the old slot; the destination becomes its owner. Flags are initialized for every
control-flow path and only live slots are destroyed.

Partially evaluated calls and constructors retain temporary ownership until all
arguments/fields have succeeded. For example, an earlier `Box.new(...)` is still
reclaimed if a later field executes `?` or an explicit return. Returning an owned
value clears its temporary before cleaning other resources. Error propagation
transfers the error payload and cleans unrelated live values without destroying
the returned error.

Native code uses checked `malloc`/`free` wrappers and generated type-specific drop
functions. Lifetimes come from moves and generated cleanup, not a tracing collector
or per-object reference counts. A single diagnostic allocation-balance counter
checks normal process exit; it does not decide when objects are destroyed.
Recursive drop functions can consume stack proportional to nesting. Stack-bounded
or fully in-place destruction is not guaranteed by this milestone.

The reference evaluator independently models allocations by identities in a heap
map, validates frees, and rejects live owning allocations at normal entry-function exit. Its
host API `evaluate_with_stats` reports allocation/deallocation/peak-live counts,
buffer/vector growths, successful box reuses, and compiler-selected map fusions;
these counters are not visible to Kush programs. The CLI exposes the same stable
diagnostics through `--stats` for `eval`, `run`, and `build`. See
[checked reuse and allocation diagnostics](reuse.md). Compiler/interpreter
storage uses Rust allocations and is distinct from the generated program's
memory model.

## Checked resource contracts

Executable functions may use `#[noalloc]` and `#[nosuspend]`.

- `noalloc` rejects a declared `alloc` effect, and effect checking rejects any
  allocating operation/call in its body. Taking and destroying owned data are
  allowed, including generated cleanup.
- `nosuspend` rejects a declared `suspend` effect, every reachable suspending
  call or callback, and an unconstrained effect-row variable in its signature
  (because specialization could add `suspend`). It is checked statically,
  independently of optimization. [Synchronous standard-stream I/O](stdio.md) is
  allowed and can block; see [structured async](async.md) for task suspension.

Both apply to functions, not enum declarations. Other attributes remain rejected.
These checks are independent of optimization and apply to Cranelift development
builds. They are contracts for this closed operation set, not an implementation of
polymorphic effects, arbitrary allocator/FFI contracts, or real-time guarantees.

This milestone adds a 1024-resource-slot limit per function. Existing input,
layout, parameter, local, and evaluator budgets still apply. The reference
evaluator's computation budget counts expressions, not an exact bound on recursive
destruction work. Native execution/destruction is not fuel-limited.

Still deferred: exact linear obligations beyond the implemented `@[1]`/`@[n]`
grade fragment (see [usage grades](grades.md)), general user-defined graded
modalities, shared owners, mutable owner borrows, borrowed owner-reference
returns, lifetime inference beyond conservative signature elision, stored views
outside records of declared lifetimes, direct mutable/owning record field moves,
linear or stream/callable/union metadata in mixed records, and general borrowed
callable/task captures (scoped local captures
are supported),
general disjoint-range inference beyond checked mutable split pairs, custom
destructors, fallible allocation APIs, allocator-level or widening reuse,
general effectful fusion, lifetime integration with dependent proofs, forced
cancellation unwinding/masking, and LLVM. Memory safety and performance
of the full proposed language still require the research work identified in the
specification. See [borrowing and lifetimes](lifetimes.md) for the exact
implemented subset and its rejected cases.
