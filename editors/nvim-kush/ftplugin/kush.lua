-- Kush buffer settings: line comments and conventional 4-space indent.
vim.bo.commentstring = '// %s'
vim.bo.tabstop = 4
vim.bo.shiftwidth = 4
vim.bo.expandtab = true

-- Regex fallback highlighting (syntax/kush.vim) runs only while the kush
-- language server is not attached; the moment it attaches the buffer shows
-- only its semantic tokens, never both schemes at once.
local bufnr = vim.api.nvim_get_current_buf()
local group = vim.api.nvim_create_augroup('kush-syntax-fallback', { clear = true })

vim.api.nvim_create_autocmd('LspAttach', {
  group = group,
  buffer = bufnr,
  callback = function(event)
    local client = vim.lsp.get_client_by_id(event.data.client_id)
    if client ~= nil and client.name == 'kush' then
      vim.bo[bufnr].syntax = 'OFF'
    end
  end,
})

local timer = vim.uv.new_timer()
timer:start(1500, 0, vim.schedule_wrap(function()
  if vim.api.nvim_buf_is_valid(bufnr) and vim.bo[bufnr].filetype == 'kush' then
    local attached = #vim.lsp.get_clients({ bufnr = bufnr, name = 'kush' }) > 0
    if not attached and vim.bo[bufnr].syntax == '' then
      vim.bo[bufnr].syntax = 'kush'
    end
  end
  pcall(function()
    timer:stop()
    timer:close()
  end)
end))
