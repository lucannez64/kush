# Executable language milestone: steps 1–6

The compiler now implements useful restricted subsets of the six roadmap areas.
The complete dependent/graded/algebraic language remains a research and
implementation target. This document describes the boundary of this milestone.

1. **Modules:** `use app.lexer`, qualified calls, imported items, `pub` visibility,
   file-aware diagnostics, and embedded `std.result`, `std.option`, and `std.ascii`
   modules. Files are resolved from the entry file's directory by module path.
   Re-exports and package management are deferred.
2. **Generic functions and collections:** monomorphized generic functions with
   inference or explicit `::<T>` specialization, generic records and destructuring,
   and owning `Vec<T>` storage. `Vec.new`, `with_capacity`, `push`, `len`, `get`,
   `set`, and proof-checked `at` are available. Copying reads reject owning
   elements; vectors reject linear elements. [Fixed-length inline arrays](arrays.md)
   support literal/computed constant lengths, `N: Nat` const parameters,
   symbolic lengths in generic records/enums/aliases, explicit specialization
   and narrow length inference, and constant or checked dynamic indexing.
   Shared and exclusive [slice views](slices.md) span arrays, vectors, and byte
   buffers with sub-slicing, `len`/`get`/proved `at`, exclusive `set`, explicit
   [lifetime](lifetimes.md) parameters, checked shared and mutable borrowed
   returns, capability-ancestry reborrows with parent suspension/restoration,
   and last-use loan release. Checked disjoint mutable siblings are available
   through the restricted `let (left, right) = Slice.split_at_mut(view, mid);`
   form, and scoped `once fn` closures may capture shared or exclusive slice
   views for local calls. Runtime-sized inline arrays, general disjoint-range
   inference, borrowed
   owner-reference returns, and general lifetime inference remain deferred; see
   [dependent array lengths](dependent-indices.md).
3. **Iteration and diagnostics:** `while`, `loop`, `break`, and `continue`, with
   ownership checking across repeated iterations and cleanup on exits. Break
   statements in match arms need a block, e.g. `None => { break; }`.
   Diagnostics carry notes and original multi-file source positions.
4. **Executable proofs:** erased proposition parameters such as
   `erased valid: { 0 <= index && index < Bytes.len(source) }`. Calls pass `_`
   to request discharge from contextual facts, or a named proof parameter.
   The admitted fragment is integer difference constraints; proof certificates
   are checked independently from proof search. `Bytes.at(source,index,_)` and
   `Vec.at(values,index,_)` omit runtime bounds checks only after discharge.
   Total logical definitions now coexist with executable functions: they are
   checked by the dependent kernel, audited for relevance, and erased before
   runtime lowering. An erased parameter may also name a logical type such as
   `Eq<Nat, 0, 0>`, or an open logical type depending on earlier erased kernel
   binders (for example `erased n: Nat, erased p: Eq<Nat, n, n>`); calls pass a
   checked logical proof term, which the kernel verifies with call-site
   substitution and no proof search. Immutable runtime `i64`/`Bool`/`Unit`
   values may also be symbolic indices in erased proof types (never machine
   arithmetic or evidence); see [runtime indices](runtime-indices.md). A `Prop`
   sort, positive inductive
   propositions, and proof irrelevance for `Prop` inhabitants are implemented;
   large elimination from user propositions is rejected. Propositions over
   runtime values and general relevance/irrelevance rules remain future work.
   See [the kernel boundary](kernel.md#checked-interoperability-with-executable-functions),
   [dependent array lengths](dependent-indices.md), and
   [propositions](propositions.md).
5. **Usage grades:** `T @[g]` supports natural exact multiplicities, `@[many]`,
   and compile-time grade arithmetic over a checked natural-plus-infinity
   semiring. `@[1]` preserves the original exactly-once semantics and
   diagnostics; `@[n]` copyable bindings require exactly `n` uses;
   `@[0]` forbids runtime observation and cannot discard owning/linear storage.
   Owning/linear values reject `0`, `n > 1`, and `many`. Branch joins,
   short-circuiting, `return`, `?`, loop heads, calls, and assignment are
   checked. Abstract `<G: Grade>` parameters are instantiated only by explicit
   compile-time specialization, never by runtime grade values. An explicit
   `-> T @[1]` result contract is supported for owning and intrinsically linear
   results and transfers a consumption obligation to the caller; it is static
   metadata erased at runtime and is threaded through generic functions,
   lambdas, arrow types, static trait/method contracts, aliases, adapters,
   loops, `?`, and aggregates. Other result grades and copyable results are
   rejected, and an ungraded result cannot launder a linear binding. Erased proof
   parameters remain the zero-runtime erasure mechanism. User-defined grade
   semirings, grade inference, dependent grade indices, and a formal soundness
   proof remain deferred. See [usage grades](grades.md).
6. **Algebraic subtyping:** normalized heterogeneous unions and intersections
   over the concrete value fragment, including same-enum variant subsets
   (`Op.Mul | Op.Div`), owning/scalar/record/enum unions, distributive
   intersections with `Never`, checked injection/repacking, and exhaustive
   narrowing matches written `Type @ pattern`. Same-enum masks keep their
   zero-cost layout; heterogeneous unions use a discriminator. Arrow subtyping
   for first-class function values and owning once closures is implemented in
   [functions.md](functions.md). Structural record/width subtyping remains
   blocked by the absence of a structural record representation. See
   [algebraic subtyping](subtyping.md) for the exact boundary.

## Application milestone

```sh
printf '(1 + 2) * -3\n' | cargo run -p kush -- run examples/calc.kush
# -9
printf '8 / 2 / 2 - 1\n' | cargo run -p kush -- eval examples/calc.kush
# 1
```

The calculator imports separate lexer, parser, and evaluator modules. Its lexer
uses loops, a vector of tokens, records, and proved byte access. Its parser builds
an owning recursive AST and supports parentheses, unary minus, and binary
`+`, `-`, `*`, `/`, with normal precedence and left associativity. Its evaluator
uses variant-subset parameters for multiplicative operators. Source and token
storage are freed before evaluating the AST.

Input is bounded to 4096 bytes. Lexical errors print `-100 - byte_offset`, parse
errors print `-200 - token_offset`, and division by zero prints `-300`; errors
exit with status 1. Integer overflow still aborts through checked arithmetic,
including number scanning. Recursion and recursive destruction are not
stack-bounded. This is a calculator application, not a self-hosted Kush compiler.

The milestone tests exercise specialization, record destructuring, vector loops,
proof acceptance/rejection, branch-version isolation, mutation rejection for
proof facts, linear consumption, natural/abstract grade arithmetic and
specialization, grade-zero rejection, branch/short-circuit/loop usage joins,
ownership/linearity conflicts, variant set types, module visibility, and
native/reference agreement. This is prototype validation, not a formal
soundness proof or performance comparison. The subtyping tests additionally
cover normalization laws, heterogeneous and owning unions, union
widening/repacking, narrowed matches and coverage, grade and borrow boundaries,
and native/reference agreement.
