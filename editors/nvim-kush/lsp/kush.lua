-- Kush default language-server configuration, loaded by Neovim when this
-- directory is on the runtimepath. Clients may override `cmd` through
-- `vim.lsp.config('kush', { cmd = { ... } })`.
local kush = vim.env.KUSH_BIN or 'kush'

return {
  cmd = { kush, 'lsp' },
  filetypes = { 'kush' },
  root_markers = { 'Kush.toml', '.git' },
}
