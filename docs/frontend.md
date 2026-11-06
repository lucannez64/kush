# Initial syntax frontend

This document describes the implemented subset of the [v0.1 design](spec-v0.1.md).
It is the grammar baseline for the initial parser, not a complete Kush language
implementation. The library entry point is `kush::parse(&str)`; the result is a
source-spanned AST or the first diagnostic. Lexing/parsing use the Rust standard
library; the native backend adds Cranelift dependencies. This crate forbids unsafe
Rust.

This page retains the bootstrap grammar and parser-phase boundaries. For the
current checked executable language and features added afterward, use
[executable.md](executable.md), [lifetimes.md](lifetimes.md),
[functions.md](functions.md), and [core-status.md](core-status.md). Parser-only
acceptance is distinct from the checks performed by `check`, `eval`, and `run`.

## Run it

From the repository root, using Rust 1.95 or newer:

```sh
cargo run -p kush -- parse examples/parser.kush
cargo run -p kush -- parse examples/parser.kush --ast
cargo run -p kush -- lex examples/parser.kush
```

`parse` validates syntax only. It does **not** establish name resolution, types,
proof soundness, exhaustiveness, ownership, effects, or executability. Parsed
indexed enums remain syntax trees; executable usage grades are syntax here and
are checked later by the [executable grade checker](grades.md), not by the
logical kernel.
Separate `resolve` and `check` commands now support lexical name resolution and
a restricted logical subset; see [kernel documentation](kernel.md). `total enum`
declarations are logical data with checked constructors and dependent
elimination; ordinary `enum` declarations remain runtime data. See
[logical data](logical-data.md). A separate
[executable subset](executable.md) now supports scalar type/effect checking and
Cranelift `build`/`run` commands, plus a reference `eval` command.

Commands return exit code 0 on success, 1 for source/read/write failures, and 2
for invalid command-line arguments. File input must be UTF-8. `lex` prints token
kinds and half-open byte spans; `parse --ast` prints the Rust debug representation
of the AST. These dump formats are development aids, not stable interchange APIs.

## Lexical rules

Identifiers use `[A-Za-z_][A-Za-z0-9_]*`. Recognized keywords are `fn`, `total`,
`pub`, `let`, `mut`, `return`, `if`, `else`, `match`, `enum`, `struct`, `type`,
`module`, `use`, `erased`, `true`, and `false`. The `prop` declaration keyword is
contextual: it is recognized only at the start of a top-level declaration, so it
remains usable as an identifier or module-path segment elsewhere. `trait` and
`impl` are contextual in the same way. `Self` is recognized as a receiver type
placeholder in type position. `Type`, `Prop`, `Nat`, and effect names are
ordinary identifiers at this stage.

Whitespace is ASCII whitespace. Line comments begin with `//`; `/* ... */`
comments nest. Strings and characters accept Unicode scalar values, and escapes
`\n`, `\r`, `\t`, `\0`, `\\`, `\"`, and `\'`. Raw newlines in literals are
rejected. Character literals contain exactly one decoded scalar. The lexer
recognizes `'a` lifetime tokens separately from character literals; semantic
lifetime checks live in the executable checker. Other escapes and raw strings
are not implemented.

Integers are arbitrary-length decimal digit strings with optional single
underscores between digits. Separators are removed in the AST; original text
remains recoverable from the span. No machine-width conversion takes place.
Float literals use a decimal fraction, an exponent, or both; a `.` joins the
literal only when a digit follows and the preceding token is not `.` (so
`pair.0` and `nested.0.1` remain projections). Integer and float suffixes are
not implemented. A sign is a unary operator, or part of a signed integer
pattern; float literal patterns are rejected during parsing.

Operators use longest matching, except that `>>` is two `>` tokens to support
nested generic arguments. There are no shift operators in this subset.

## Declaration grammar

Notation: `?` means optional, `*` means repetition, and `list(X)` means a
comma-separated list with an optional trailing comma, possibly empty.

```ebnf
file        = declaration* EOF ;
declaration = attribute* "pub"? item ;
attribute   = "#" "[" identifier "]" ;
item        = "module" path ";"
            | "use" path ";"
            | "total"? "fn" identifier function_generics? "(" list(parameter) ")"
                "->" type effects (block | ";")
            | "struct" identifier function_generics? "{" list(field) "}"
            | "total"? "enum" identifier generics? "{" list(variant) "}"
            | "trait" identifier "{" trait_method* "}"
            | "impl" type "{" method* "}"
            | "impl" type "for" type "{" method* "}"
            | "type" identifier function_generics? "=" type ";" ;
trait_method = "fn" identifier function_generics? "(" list(parameter) ")"
            "->" type effects ";" ;
method      = "pub"? "fn" identifier function_generics? "(" list(parameter) ")"
            "->" type effects block ;
path        = identifier ("." identifier)* ;
generics    = "<" list(generic) ">" ;
generic     = identifier (":" type ("-" exclusion)?)? ;
exclusion   = effect ("|" effect)* | "(" exclusion ")" ;
effect      = "io" | "alloc" | "suspend" | "panic" ;
function_generics = "<" list(lifetime | generic) ">" ;
lifetime    = "'" identifier ;
parameter   = "erased"? identifier ":" type ;
field       = identifier ":" type ;
variant     = identifier payload? (":" type)? ;
payload     = "(" list(type) ")" | "{" list(field) "}" ;
effects     = "!" "{" list(type) "}" ;
```

Function, `struct`, and `type` declarations may mix lifetime binders with
ordinary generic binders; `enum` declarations take ordinary generics only.
Lifetime arguments in a named type application, such as `Window<'a, i64>`, must
precede ordinary type/natural arguments. A generic binder may carry a
`-`-separated concrete effect exclusion after an `Effects` bound, as in
`<e: Effects - alloc>`; the parser accepts it in every binder position, and the
resolver rejects it everywhere except executable function and method effect
rows. See [bounded effect exclusion](effect-constraints.md). The checked
lifetime relationships, signature elision rules, borrowed and mixed records, and
restricted split-pair `let` form are specified in [lifetimes.md](lifetimes.md)
and [borrowed-records.md](borrowed-records.md).

All function declarations currently require return types and explicit braced
effect rows, including private functions. `total` is recorded but termination is
not checked. Attributes are recorded without interpretation. Function interfaces
ending in `;` are allowed. Module headers/imports are parsed as paths; imports are
not loaded. Duplicate names, unknown attributes, and invalid module ordering are
handled by subsequent semantic passes. Payload record fields do not yet support `pub`.

## Type grammar

```ebnf
type        = intersection ("|" intersection)* ;
intersection = graded ("&" graded)* ;
graded      = borrowed ("@" "[" grade "]")* ;
grade       = product ("+" product)* ;
product     = grade_atom ("*" grade_atom)* ;
grade_atom  = integer | path | "(" grade ")" ;
borrowed    = "&" lifetime? "mut"? borrowed | type_atom ;
type_atom   = path ("<" list(lifetime | type) ">")?
            | integer
            | ("-" integer)
            | "true" | "false"
            | "(" type ")"
            | "(" ")"
            | "(" type "," list(type) ")"
            | "[" type (";" const_expr)? "]"
            | "fn" "(" list(type_parameter) ")" "->" type effects ;
type_parameter = (identifier ":")? type ;
```

Parentheses group a type; a trailing comma distinguishes a singleton tuple in
the grammar, but the executable checker rejects one-element tuples explicitly
(`()` is `Unit`).
`[T]` is a (borrowed) slice type and `[T; N]` is an inline array type. The array
length is a compile-time natural expression over integer literals, `N: Nat`
const parameters, admitted total logical applications such as `add<1, 1>`, and
checked `+`/`-`/`*`/`/`/`%`. It is parsed as a restricted expression and
evaluated while lowering an executable type (never by running runtime code).
Symbolic lengths in generic data and explicit const specialization are
implemented; a runtime-sized `[T; n]` layout is not. The separate
`DynArray<T, capacity>` builtin provides inline fixed-capacity storage with a
runtime length; see [dynamic-arrays.md](dynamic-arrays.md). Function types extend through
their return type and effect
row. Their parameters can be named, as in `fn(n: Nat) -> Eq<Nat, n, n> ! {}`;
a name binds in later parameter annotations, the return type, and effect row.
Unnamed parameters remain supported. Parentheses should delimit function types
used in unions/intersections.

General arithmetic type-level index expressions beyond the documented array length
fragment, comparison propositions such as `i < n` inside types, and symbolic
universe constraints remain unsupported. Boolean and signed integer literals in
type positions are parsed for the restricted machine-carrier indices described
in [runtime-indices.md](runtime-indices.md); they are not general type-level
values. In
particular, the proven-access example in the design spec cannot yet be parsed in
full. The parser's generic `<...>` syntax is not a complete dependent
elaboration; it supports type, grade, and `Nat` const parameters as documented in
[dependent-indices.md](dependent-indices.md). Normalized heterogeneous
union/intersection subtyping is
implemented for the executable value fragment; see
[algebraic subtyping](subtyping.md). The executable checker implements the
natural/abstract usage grades in [grades.md](grades.md); the logical checker
still rejects grades as proof-relevant types.

## Expressions and blocks

Atoms include names, integer/string/character/Boolean literals, `()`, tuples,
arrays, parenthesized expressions, and blocks. Postfix forms include calls, named
field access, indexing, slice ranges `value[start..end]`, `?`, and explicit
specialization `callee::<T, n>`. A range with omitted start/end means the
corresponding end of the value.

| Binding strength | Operators | Association |
| --- | --- | --- |
| Highest | `f(...)`, `.name`, `[...]`, `?`, `::<...>` | Left |
| Unary | `-`, `!`, `&`, `&mut` | Prefix |
| Multiplicative | `*`, `/`, `%` | Left |
| Additive | `+`, `-` | Left |
| Comparison | `==`, `!=`, `<`, `<=`, `>`, `>=` | Non-chaining |
| Boolean and | `&&` | Left |
| Boolean or | `||` | Left |
| Lowest | `=` | Right |

`a < b < c` is rejected; `a < b && b < c` is valid syntax. Parentheses permit
explicit grouping such as `(a < b) == true`. Assignment target validity, operand
types, short-circuit execution, and arithmetic overflow belong to later stages.

```ebnf
block       = "{" statement* expression? "}" ;
statement   = "let" "mut"? pattern (":" type)? "=" expression ";"
            | expression ";"
            | block_like_expression ;
if_expr     = "if" expression block ("else" (block | if_expr))? ;
match_expr  = "match" expression "{" list(arm) "}" ;
arm         = pattern ("if" expression)? "=>" expression ;
return_expr = "return" expression? ;
```

The grammar above summarizes block placement; a final unterminated expression
is the tail, while an `if`, `match`, or block expression preceding another
statement may omit its semicolon. A statement that starts with a block-like
expression (`if`, `match`, `while`, `loop`, `handle` or a block) ends at its
`}` when the next token starts a new line and is `(`, `[`, `-` or `*`: that
line is a new statement, so `if c { .. }` followed by a `(a, b)` line is not a
call. On the same line (`if c { 1 } else { 2 } - 1`), and inside a `let` value
or other expression, the operator or call still applies. A block-like
expression followed by `&` or `|` always ends there. Match arms currently require commas between
arms, including block-bodied arms. `return` without a value must be followed by
`;` or `}`. `return` with a value extends through the following expression.

Record construction, typed closures and loops are parsed. Structured tasks use
ordinary `Task.scope` and `Task.spawn` calls; their checked behavior is described
in [async.md](async.md). Tuple-number field access such as `pair.0` is parsed as
an ordinary named field whose name is the digit string; the executable checker
resolves it against an anonymous tuple layout. Calls whose callee is a field,
such as `receiver.len()`, are also parsed as ordinary field projections followed
by calls. The executable checker gives a type-directed builtin meaning to the
reserved method names documented in [basic-values.md](basic-values.md). For
other names it resolves static inherent and trait methods; the exact syntax,
precedence, and rejected forms are documented in
[traits.md](traits.md). Unsafe blocks and custom effect-handler syntax remain
outside this parser subset. Names in syntactically valid source are checked by
the subsequent resolver, not by `parse`.

## Patterns

Patterns include `_`, dotted names, literal values, signed decimal integers,
tuples, slices, constructor applications, record destructuring, alternatives,
and parentheses. Constructor/name distinctions await name resolution.

```ebnf
pattern     = pattern_atom ("|" pattern_atom)* ;
pattern_atom = "_" | literal | "-" integer
             | type "@" pattern
             | path
             | path "(" list(pattern) ")"
             | path "{" list(pattern_field) "}"
             | "(" ")"
             | "(" pattern ")"
             | "(" pattern "," list(pattern) ")"
             | "[" list(pattern | "..") "]" ;
pattern_field = identifier (":" pattern)? ;
```

A slice may contain at most one direct `..`; named rest captures are deferred.
`type "@" pattern` narrows a heterogeneous union alternative; see
[algebraic subtyping](subtyping.md). The parser backtracks over the type when no
`@` follows, so ordinary constructor, record, array, and binding patterns keep
their existing meaning.
The same pattern syntax is retained in `let` bindings, without yet checking
irrefutability. Alternative binding consistency, exhaustiveness, unreachable
arms, indexed refinements, and borrow/move semantics require semantic checking.

## Diagnostics and limits

AST spans are half-open UTF-8 byte offsets into the original file. Diagnostic
locations are one-based, counting Unicode scalars; tabs expand to four-column
stops. Terminal wide/combining-character display width is not modeled yet.
Multi-line spans show their first line. Parsing stops at the first failure;
error recovery and multiple-file source maps are future work.

Initial implementation limits are 4 MiB per source file, 100000 non-EOF tokens,
128 recursive syntax frames, and 128 operators/postfix extensions per local
expression/type chain. Nesting budgets are shared across parser routines, so
these are protection budgets rather than guaranteed counts of accepted source
parentheses. Exceeding a limit reports a diagnostic.

## Validation and next milestone

```sh
cargo fmt --all -- --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Regression coverage includes operator precedence, generic delimiters, enum and
pattern syntax, source spans, Unicode diagnostics, malformed inputs, nesting
limits, a deterministic UTF-8 mutation corpus, and CLI behavior.

Name resolution and a bootstrap logical kernel are now implemented separately;
their rules, supported subset, and remaining work are in [kernel.md](kernel.md).
Surface parsing remains separate from proof, type, or resource checking. Native
code generation now follows separate scalar semantic checking through the
[Cranelift backend](executable.md).
