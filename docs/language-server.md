# Kush language server

`kush lsp` is a small stdio JSON-RPC language server built on the existing Kush
frontend. It is not a second compiler: module loading comes from
`program::load`, names and spans from `resolve`, diagnostics from the existing
checker, and formatting from the existing whitespace formatter.

## Running

```sh
kush lsp
```

The process speaks the Language Server Protocol over stdin/stdout using
`Content-Length` framing. It does not accept extra arguments; point the editor
at a `kush` executable with the VS Code `kush.server.path` setting instead. The
server discovers `Kush.toml` from the `initialize` `rootUri`/first workspace
folder, then from the process working directory. If there is no manifest, open
files are still parsed and checked with sibling-path imports.

## Protocol surface

Implemented:

- `initialize`, `initialized`, `shutdown`, `exit`;
- `textDocument/didOpen`, `textDocument/didChange` (full synchronization;
  `textDocumentSync: 1`), `textDocument/didClose`;
- versioned `textDocument/publishDiagnostics`;
- `textDocument/definition`;
- `textDocument/formatting`;
- `textDocument/hover`;
- `textDocument/documentSymbol`;
- `textDocument/semanticTokens/full`.

Unknown requests receive JSON-RPC error `-32601`. Malformed JSON receives
`-32700` with a null id and the stream continues. Malformed or oversized headers
are reported on stderr and stop the server because the frame boundary is no
longer trustworthy. Message bodies are capped at 16 MiB and headers at 64 KiB.
Ordinary diagnostics and errors are never printed to stdout; stdout contains
only framed protocol messages. A request is accepted with a string/number id;
notifications do not receive responses.

`exit` ends the process. A normal client sequence is `shutdown` followed by
`exit`, which exits with status 0. `exit` without `shutdown` exits with status 1.
Requests before initialization receive `ServerNotInitialized`; repeated
initialization and requests after shutdown receive `InvalidRequest`. Malformed
framing exits with status 1, while clean EOF exits with status 0.
End of stdin also stops the process.

Positions use LSP's UTF-16 code units. Byte-to-position conversion counts UTF-16
units, so a non-BMP scalar such as an emoji occupies two columns, and conversion
never splits a UTF-8 scalar. A position inside a surrogate pair snaps to the
start of that scalar.

## Diagnostics

Diagnostics are computed from in-memory overlays of open documents. `didOpen`
and `didChange` never write unsaved text to disk. When a project is available,
the root entry is loaded through the project's `ModuleIndex`, so unsaved entry
text and unsaved imported modules are used together without overwriting any
file. Open documents that are not reachable from the entry are also checked as
their own root.

Each `publishDiagnostics` notification for an open document carries that
document's `version`. A `didChange` with an older version is ignored so a slow
client cannot replace newer text or publish stale diagnostics. Diagnostics for
imported project files are published even when those files are not open; such
messages omit `version`. `didClose` publishes an empty diagnostic list and
suppresses that file until a later `didOpen`, even if another open root still
imports it.

The language server calls `program` and `executable::check_program` directly,
not `project::check`. It therefore never writes or verifies `Kush.lock`, never
runs Cargo, never links or executes native code, and never executes a Kush
program during diagnostics. Standard-library modules are virtual
(`<std.result>`, ...); diagnostics for them are suppressed because there is no
real file URI to publish them against.

The checker returns its first error for a checked root, so a document may need
one correction at a time. Every open document gets this bounded check on each
change; there is no incremental compilation or background daemon.

## Go to definition

Definitions use resolver bindings and source spans:

- local variables, parameters, generic parameters, and pattern binders;
- functions, structs, enums, aliases, traits, effects, and constructor
  declarations;
- imported items and whole-module `use` paths, resolved through the loaded
  program's unit/import table;
- project module source files, including local path dependencies.

Targets must be real source files. Builtins and standard-library modules have no
source location and return `null` rather than a synthetic `file://` URI or the
first user file. A declaration target range is refined to the declaration name
when the lexer finds it; otherwise the declaration span is used.

This is lexical resolution, not a type-directed IDE index:

- impl methods are reachable only where the resolver records an explicit method
  binding; a receiver-type call that the resolver cannot bind returns `null`;
- dynamic trait-object dispatch and builtin methods have no source definition;
- imported constructors and fields are limited by the resolver's existing
  bindings;
- completion, rename, references, call hierarchy, incremental sync, and
  workspace-wide symbols are not implemented.

## Hover

Hover reuses the definition resolver internally, so what it shows is exactly
"what binds at the cursor":

- a builtin shows its surface name (`FS.write_exclusive` and friends);
- a declaration binding shows a clipped header slice of the declaration (up to
  the first `{` or `;`), rendered as `kush` markdown;
- a local variable shows its owning `let` statement;
- anything that does not resolve returns `null`.

A cursor on a reference behaves like go-to-definition, so hovering a call site
names the resolved function, but there is no type inference beyond the checked
boundary.

## Document symbols

Top-level declarations map to LSP symbol kinds (module header `2`, functions
`12`, enums and props `10` with `EnumMember` children, structs `23`, traits
`11`, impls `5`, aliases/effects `26`); `use` and `#[test]` attributes produce
no symbols. The selection range is the declaration's name token when the lexer
can find it, otherwise the whole item span. Symbols come from the open
document only; there is no workspace symbol index.

## Semantic tokens

`textDocument/semanticTokens/full` is a single-shot full token list built from
the lexer token stream plus a scanner over the trivia gaps for `//` and nested
`/* */` comments. The legend is fixed:

```text
keyword function type namespace enum enumMember string number comment operator variable
```

Names after `fn`/`enum`/`struct`/`type`/`trait`/`impl`, identification after
`let` and `let mut`, dotted module headers and `use` paths, statement keywords
(`match`, `if`, `return`, the loop family), primitive and well-known type
names (`i64`, `Unit`, `Bytes`, ...), strings, characters, numbers, lifetimes,
and comments are colored; ordinary identifiers, punctuation, and effect
markers are left to the client's fallback. Tokens use relative
`deltaLine`/`deltaStart` positions in UTF-16 units.


## Formatting

`textDocument/formatting` calls `project::format::format_source` and returns one
whole-document `TextEdit`. It is the same token-level layout pass as `kush fmt`:
it normalizes indentation and spacing, keeps single blank lines between
top-level item groups, preserves comments, literal contents, and the file's
line endings, and never reorders tokens. Before returning, the original and
candidate are lexed and the edit is refused unless the token kinds match. If the
document is not valid enough to lex, it returns `null` rather than inventing
edits.

## Client

`editors/vscode-kush` keeps its TextMate grammar and adds a standard
`vscode-languageclient` client. Settings:

- `kush.server.enabled` (default `true`);
- `kush.server.path` (default `kush`).

The extension starts `kush.server.path` with `lsp`, over
stdio. Use **Kush: Restart Language Server** after changing the binary. No
global editor installation or automatic PATH modification is performed by the
Kush repository.

## Tests

Unit tests cover framing, size limits, JSON errors, UTF-16/surrogate conversion,
URI escaping, shutdown, and unknown methods. Stdio integration tests spawn
`kush lsp` and cover project diagnostics, unsaved invalid text, cross-file and
local definitions, imported module definitions, stale versions, Unicode
columns, `didClose` clearing, JSON escaping, malformed input, unknown methods,
and the absence of disk mutations, `Kush.lock`, or a native `target/` directory.

## Review corrections

The initial advertised extra-arguments setting was removed because the server
accepts only `kush lsp`. Open-document locations use the client's URI, and old
published diagnostics under another URI alias are cleared. Canonicalization of
existing parent directories keeps new unsaved paths stable when saved through
a symlinked workspace. Unsaved entry module headers receive package-name
validation even when the entry has later syntax errors, named-import navigation
selects the declaration name, and hover/document symbols/semantic tokens were
extracted from that same cursor probe.
