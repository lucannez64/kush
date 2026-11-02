# Kush editor support for VS Code

This extension provides:

- TextMate syntax highlighting for `.kush` files
  (`syntaxes/kush.tmLanguage.json`);
- language registration and bracket/comment configuration;
- a standard LSP client that starts `kush lsp` over stdio for open documents.

The server reuses the compiler frontend for project-aware diagnostics and
go-to-definition. It does not execute programs, run Cargo, link native code, or
write `Kush.lock`. See [docs/language-server.md](../../docs/language-server.md)
for the exact supported protocol surface and limits.

## Setup

Build or install a `kush` executable, then install this extension:

```sh
cd editors/vscode-kush
npm install
```

Open the directory in VS Code and press **F5** to launch an Extension
Development Host, or use **Extensions: Install Extension from Location...**.
The TextMate grammar works even if the language server is not available.

## Configuration

| Setting | Default | Meaning |
| --- | --- | --- |
| `kush.server.enabled` | `true` | Start the LSP client for `.kush` files. |
| `kush.server.path` | `kush` | Path to the Kush executable. |

Use **Kush: Restart Language Server** after changing the binary path or
rebuilding Kush. Diagnostics appear for unsaved text as you type; save is not
required. The server discovers `Kush.toml` from the workspace root (or the
launch directory). Without a manifest, open files are checked with their
sibling imports where possible.

## Supported editor features

- live diagnostics for open Kush documents, including project imports and
  unsaved editor text;
- go-to-definition for local bindings, functions, types, imported items, and
  `use` module paths;
- formatting through `textDocument/formatting`, using the existing
  whitespace-only formatter (trailing spaces and final newline; comments and
  token order are preserved).

Not provided: completion, hover, rename, find-references, semantic tokens,
incremental sync, or a full pretty-printer. Go-to-definition is lexical: method
calls resolved only through receiver-type dispatch, dynamic trait dispatch, and
builtins have no source location and return no result instead of a synthetic
file. See the language-server document for details.
