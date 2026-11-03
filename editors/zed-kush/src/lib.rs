//! Zed extension for Kush: starts `kush lsp` for `.kush` files.
//!
//! The server binary is found from the `lsp.kush-lsp.binary.path` setting,
//! then from `kush` on the worktree's PATH.
use zed_extension_api::{self as zed, settings::LspSettings, LanguageServerId, Result};

struct KushExtension;

impl zed::Extension for KushExtension {
    fn new() -> Self {
        KushExtension
    }

    fn language_server_command(
        &mut self,
        language_server_id: &LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        let binary = LspSettings::for_worktree(language_server_id.as_ref(), worktree)
            .ok()
            .and_then(|settings| settings.binary);
        let configured = binary.as_ref().and_then(|binary| binary.path.clone());
        let path = match configured.or_else(|| worktree.which("kush")) {
            Some(path) => path,
            None => {
                return Err(
                    "`kush` was not found on PATH; install it or set lsp.kush-lsp.binary.path"
                        .into(),
                )
            }
        };
        let args = binary
            .and_then(|binary| binary.arguments)
            .unwrap_or_else(|| vec!["lsp".into()]);
        Ok(zed::Command {
            command: path,
            args,
            env: worktree.shell_env(),
        })
    }
}

zed::register_extension!(KushExtension);
