# nvim support for Kush

Kush highlighting in Neovim comes from the language server's semantic tokens,
so both highlighting and LSP features (hover, go-to-definition, formatting,
document symbols, diagnostics through the server) come from one process:
`kush lsp`.

## Setup

Add the integration to Neovim 0.11+ configuration:

```lua
-- filetypes: *.kush
vim.filetype.add({ extension = { kush = 'kush' } })

vim.lsp.config('kush', {
  -- Override with the absolute path of your kush binary.
  cmd = { 'kush', 'lsp' },
  filetypes = { 'kush' },
  root_markers = { 'Kush.toml', '.git' },
})
vim.lsp.enable('kush')
```

Copy `ftplugin/kush.lua` and `syntax/kush.vim` into your runtimepath (e.g.
`~/.config/nvim/ftplugin/` and `~/.config/nvim/syntax/`) or add this repository
directory to `vim.opt.runtimepath:append()`.

## Files

- `lsp/kush.lua`: default `vim.lsp.config` values; Neovim loads it when the
  file is on the runtimepath.
- `ftplugin/kush.lua`: comment string and indent settings for `kush` buffers.
- `syntax/kush.vim`: regex fallback highlighting for when the language server
  is not attached (scratch buffers, cold starts before initialization).

## Notes

- Neovim links each semantic token type to Treesitter highlight captures such
  as `@keyword` and `@function`, so colorscheme theming applies automatically.
- The server supports UTF-16 positions, whole-document sync, definition,
  hover, formatting, and document symbols. Incremental sync, completion,
  rename, and references are documented as unimplemented in
  `docs/language-server.md`.
- Single files work without a project; a `Kush.toml` root gives whole-project
  diagnostics and cross-module definition.
