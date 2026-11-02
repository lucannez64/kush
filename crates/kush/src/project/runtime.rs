//! Process-level program invocation and argument forwarding.
//!
//! `kush run ... -- <args>` forwards every argument after `--` as the compiled
//! program's process arguments. The native runtime currently has no source-level
//! `argv` API; that belongs to the host worker. This interface is the stable
//! place the parent can wire that API into: the arguments are already delivered
//! unchanged as process arguments, and `command()` is kept public for future
//! host and test integration.
use super::Failure;
use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Debug, Clone)]
pub struct ProgramInvocation {
    executable: PathBuf,
    arguments: Vec<OsString>,
}

impl ProgramInvocation {
    pub fn new(
        executable: impl Into<PathBuf>,
        arguments: impl IntoIterator<Item = OsString>,
    ) -> Self {
        Self {
            executable: executable.into(),
            arguments: arguments.into_iter().collect(),
        }
    }

    pub fn executable(&self) -> &Path {
        &self.executable
    }

    pub fn arguments(&self) -> &[OsString] {
        &self.arguments
    }

    /// Build a command without a shell. Every argument stays a separate
    /// `OsString`, so spaces, quotes, and leading dashes are preserved.
    pub fn command(&self) -> Command {
        let mut command = Command::new(&self.executable);
        command.args(&self.arguments);
        command
    }

    /// Run with inherited standard streams and the caller's current directory.
    pub fn run(&self) -> Result<u8, Failure> {
        let status = self.command().status().map_err(|e| {
            Failure::new(format!(
                "cannot execute '{}': {e}",
                self.executable.display()
            ))
        })?;
        match status.code() {
            Some(code) if (0..=255).contains(&code) => Ok(code as u8),
            Some(code) => Err(Failure::new(format!(
                "program exited with status {code}, which does not fit a process result"
            ))),
            None => Err(Failure::new(
                "native program aborted or was terminated by a signal".to_owned(),
            )),
        }
    }
}

pub fn run_artifact(executable: &Path, arguments: &[OsString]) -> Result<u8, Failure> {
    ProgramInvocation::new(executable, arguments.iter().cloned()).run()
}
