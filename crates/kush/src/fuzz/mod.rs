//! PROOF-FUZZ: attack the run-time checks the prover could not discharge.
//! See docs/proof-fuzz.md. This module holds the pieces shared by the
//! `kush fuzz` driver and its tests: the instrumented build and the run
//! record an instrumented program writes to `$KUSH_FUZZ_OUT`.
use crate::executable::Executable;
use crate::native::{self, CodegenOptions, LinkSpec, Optimization};
use crate::Diagnostic;

pub mod engine;
pub mod harness;
use std::path::Path;

/// The environment variable naming the file an instrumented program writes
/// its run record to.
pub const OUT_VARIABLE: &str = "KUSH_FUZZ_OUT";

/// Code-generation settings of a fuzz build: Cranelift without
/// optimization, every obligation site instrumented, overflow never
/// deferred.
pub fn codegen() -> CodegenOptions {
    CodegenOptions {
        fuzz: true,
        ..CodegenOptions::cranelift(Optimization::None, false)
    }
}

/// Build `program` as an instrumented native executable at `output`.
pub fn build(program: &Executable, output: &Path, links: &LinkSpec) -> Result<(), Diagnostic> {
    native::build_with_codegen(program, output, false, links, codegen())
}

/// How one run of an instrumented program ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// It returned from `main`.
    Exited,
    /// The check of this obligation site failed.
    Failed(usize),
    /// It panicked outside every obligation site (an allocation, I/O or an
    /// explicit failure).
    Unattributed,
    /// It ran out of stack.
    StackExhausted,
}

/// One site's counters for a run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SiteRecord {
    /// How many times its checked operation ran.
    pub hits: u64,
    /// The smallest distance from failing it seen (negative: it failed);
    /// `i64::MAX` when it never ran.
    pub margin: i64,
}

/// The run record of an instrumented program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunRecord {
    pub outcome: Outcome,
    /// Indexed by site id, as in [`Executable::obligation_sites`].
    pub sites: Vec<SiteRecord>,
}

impl RunRecord {
    /// Parse the bytes an instrumented program wrote. `None` when they are
    /// not a complete record (the program was killed before writing one).
    pub fn parse(bytes: &[u8]) -> Option<Self> {
        let word = |at: usize| -> Option<i64> {
            Some(i64::from_ne_bytes(bytes.get(at..at + 8)?.try_into().ok()?))
        };
        if bytes.get(..8)? != b"KUSHFUZ1" {
            return None;
        }
        let failed = word(8)?;
        let count = usize::try_from(word(16)?).ok()?;
        if bytes.len() != 24 + count * 16 {
            return None;
        }
        let outcome = match failed {
            -1 => Outcome::Exited,
            -2 => Outcome::Unattributed,
            -3 => Outcome::StackExhausted,
            site if site >= 0 && (site as usize) < count => Outcome::Failed(site as usize),
            _ => return None,
        };
        let sites = (0..count)
            .map(|site| {
                let at = 24 + site * 16;
                Some(SiteRecord {
                    hits: word(at)? as u64,
                    margin: word(at + 8)?,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Self { outcome, sites })
    }
}

/// `kush fuzz` on a project: check it, build the harness program under
/// `target/kush/fuzz`, attack every selected function (or only list them),
/// and print the report. Returns the number of counterexamples found.
pub fn fuzz_project(
    project: &crate::project::Project,
    options: &engine::Options,
    list: bool,
    out: &mut dyn std::io::Write,
) -> Result<usize, crate::project::Failure> {
    use crate::project::Failure;
    let entry = project.package.entry_path();
    let program = project.load_program(&entry)?;
    let links = project.native_links()?;
    let directory = project.root.join("target").join("kush").join("fuzz");
    let mut session = engine::Session::new(&program, &project.modules, &links, &directory, Some(&project.root))
        .map_err(Failure::new)?;
    let write = |out: &mut dyn std::io::Write, text: &str| {
        out.write_all(text.as_bytes())
            .map_err(|e| Failure::new(format!("cannot write the report: {e}")))
    };
    if list {
        write(out, &session.render_list(options))?;
        return Ok(0);
    }
    let selected = (0..session.targets.len())
        .filter(|&t| session.selected(t, options))
        .count();
    let checks = session.shown(options).len();
    write(
        out,
        &format!(
            "attacking {checks} unproved checks in {selected} functions of {} (seed {})\n",
            project.package.name, options.seed
        ),
    )?;
    session.fuzz(options);
    write(out, &session.render(options))?;
    Ok(session.found())
}
