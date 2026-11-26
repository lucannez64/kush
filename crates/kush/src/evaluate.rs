//! The evaluator (`kush eval`, the reference the native backend is tested
//! against): the word-level MIR machine (`mir::machine`,
//! docs/mir-design.md section 9) behind `Executable`'s entry points.

use crate::executable::Executable;
use crate::host::Host;
use crate::mir::machine::{self, Limits, Stop};
use crate::{Diagnostic, Span};
use std::io::{self, Read, Write};

type Result<T> = std::result::Result<T, Diagnostic>;

/// Default step budget of the evaluator: statements, terminators and
/// scheduler steps each cost one.
pub const DEFAULT_EVAL_FUEL: usize = 10_000_000;

/// Allocation diagnostics of a run (`--stats`), as a native build counts
/// them.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MemoryStats {
    pub allocations: usize,
    pub deallocations: usize,
    pub peak_live: usize,
    /// Successful capacity growths of byte buffers and vectors. Reallocation
    /// replaces storage, so it is not counted as an allocation/free pair.
    pub buffer_growths: usize,
    /// Successful checked `Box.reuse` operations that kept their allocation.
    pub reuses: usize,
    /// Checked nested in-place map fusions selected by the compiler.
    pub fusions: usize,
}

impl MemoryStats {
    /// Stable user-facing diagnostics line. It is written to stderr by the
    /// CLI and is a tooling observation, not a source-language effect.
    pub fn report(&self) -> String {
        format!(
            "allocation-stats: allocations={} deallocations={} peak-live={} buffer-growths={} reuses={} fusions={}",
            self.allocations,
            self.deallocations,
            self.peak_live,
            self.buffer_growths,
            self.reuses,
            self.fusions
        )
    }
}

/// A machine stop as the evaluator's error.
fn diagnostic(stop: Stop) -> Diagnostic {
    match stop {
        Stop::Panic(diagnostic) => diagnostic,
        Stop::Unsupported(what) => Diagnostic::new(
            Span::default(),
            format!("internal error: the evaluator does not support {what}"),
        ),
        Stop::Fault(fault) => Diagnostic::new(
            Span::default(),
            format!("internal error: the evaluator faulted: {fault}"),
        ),
    }
}

impl Executable {
    /// Run a checked, parameterless compile-time generator (`#[staged]`)
    /// without host access; returns the graph of the `Code` it builds.
    pub(crate) fn evaluate_staged_code(&self, entry: usize) -> Result<Vec<u8>> {
        machine::generate(self, entry).map_err(diagnostic)
    }
    /// Set the evaluator's step budget; `kush eval --fuel N`. Native
    /// execution has no such budget.
    pub fn set_eval_fuel(&mut self, fuel: usize) {
        self.eval_fuel = fuel;
    }
    pub fn eval_fuel(&self) -> usize {
        self.eval_fuel
    }
    /// Run the program with a step budget; native execution does not have
    /// one.
    pub fn evaluate(&self, output: &mut dyn Write) -> Result<i64> {
        self.evaluate_with_stats(output).map(|(value, _)| value)
    }
    pub fn evaluate_with_stats(&self, output: &mut dyn Write) -> Result<(i64, MemoryStats)> {
        self.evaluate_with_io_and_stats(&mut io::empty(), output)
    }
    /// Run the program with explicit standard streams.
    pub fn evaluate_with_io(&self, input: &mut dyn Read, output: &mut dyn Write) -> Result<i64> {
        self.evaluate_with_io_and_stats(input, output)
            .map(|(value, _)| value)
    }
    pub fn evaluate_with_io_and_stats(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
    ) -> Result<(i64, MemoryStats)> {
        self.run(input, output, &Host::empty(), None)
    }
    /// Run the program with explicit standard streams and host inputs.
    /// Native programs always observe the real process; this entry point
    /// makes arguments and environment observable and testable without
    /// global state.
    pub fn evaluate_with_host(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        host: &Host,
    ) -> Result<i64> {
        self.evaluate_with_host_and_stats(input, output, host)
            .map(|(value, _)| value)
    }
    pub fn evaluate_with_host_and_stats(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        host: &Host,
    ) -> Result<(i64, MemoryStats)> {
        self.run(input, output, host, None)
    }
    /// Run the program with a deterministic budget for **fallible**
    /// allocation attempts. Normal allocation is unaffected. A budget of zero
    /// makes `Box.try_new`, a growth-capable `Box.try_reuse`,
    /// `Bytes.try_with_capacity`, a growing `Vec.try_reserve`, an
    /// `Arena.try_alloc` that needs a chunk and `Code.compile` fail with
    /// their checked error value. This is a test/tooling probe for failure
    /// paths, not a language effect or a native allocator limit.
    pub fn evaluate_with_alloc_budget(
        &self,
        output: &mut dyn Write,
        budget: usize,
    ) -> Result<(i64, MemoryStats)> {
        self.run(&mut io::empty(), output, &Host::empty(), Some(budget))
    }
    fn run(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        host: &Host,
        try_budget: Option<usize>,
    ) -> Result<(i64, MemoryStats)> {
        let limits = Limits {
            fuel: self.eval_fuel,
            try_budget,
            generation: false,
        };
        machine::evaluate(self, input, output, host, limits).map_err(diagnostic)
    }
}
