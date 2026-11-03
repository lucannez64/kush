# Kush for Zed

Syntax highlighting, bracket matching, outline and indentation from
[`../tree-sitter-kush`](../tree-sitter-kush), plus the `kush lsp` language
server (diagnostics, go to definition, hover, formatting, document symbols).

## Install

```sh
scripts/install-zed-kush.sh                 # this machine
scripts/install-zed-kush.sh user@host       # another machine over SSH
```

Then in Zed: command palette → **zed: install dev extension** → choose
`~/.local/share/kush-zed/zed-kush`. Zed builds the extension (needs rustup;
the `wasm32-wasip2` target is added automatically if missing) and the grammar.

The language server is `kush` on `PATH` (the script installs it to
`~/.local/bin`). To use another binary, set in Zed settings:

```json
{ "lsp": { "kush-lsp": { "binary": { "path": "/path/to/kush" } } } }
```

After grammar or compiler changes, re-run the script, then **zed: rebuild dev
extension**. The grammar parses every `.kush` file in this repository.
