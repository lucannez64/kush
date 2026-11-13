//! PROOF-FUZZ driver: build the harness program once, instrumented, then run
//! it on generated tapes, one process per input, keeping the inputs that
//! reach a new obligation site or come closer to failing one. Everything is
//! deterministic for a given seed. See docs/proof-fuzz.md, sections 1 and 2.
use super::harness::{self, Assembled, Collection, Layout, Scalar, Slot, Target};
use super::{Outcome, RunRecord};
use crate::executable::{Executable, ObligationKind};
use crate::native::LinkSpec;
use crate::program::{ModuleSource, Program};
use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// Settings of one `kush fuzz` session.
#[derive(Debug, Clone)]
pub struct Options {
    /// Only functions whose qualified name contains this.
    pub filter: Option<String>,
    /// Runs per targeted function.
    pub runs: usize,
    /// Wall-clock cap for the whole session.
    pub time: Option<Duration>,
    pub seed: u64,
    /// Wall-clock limit of one run; a run that exceeds it is not a find.
    pub timeout: Duration,
    /// Seed inputs of `#[fuzz]` entries: `<corpus>/<entry name>/*`, each
    /// file the raw bytes of one input.
    pub corpus: Option<PathBuf>,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            filter: None,
            runs: 2000,
            time: None,
            seed: 0,
            timeout: Duration::from_secs(2),
            corpus: None,
        }
    }
}

/// Where an obligation site is, in source terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    pub file: String,
    pub line: usize,
    pub column: usize,
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}:{}", self.file, self.line, self.column)
    }
}

/// A counterexample: the input that made a site's check fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Finding {
    /// The target whose harness ran (an index into [`Session::targets`]).
    pub target: usize,
    pub tape: Vec<u8>,
    /// The decoded arguments, as `name = value` pairs.
    pub inputs: Vec<(String, String)>,
    /// The run of that harness that found it (1-based); 0 for a saved
    /// regression input.
    pub run: usize,
    /// Runs spent minimizing it.
    pub shrink_runs: usize,
    /// Whether it was found through a public function. A private function's
    /// input may be one no caller ever passes: a *local* counterexample.
    pub public: bool,
    /// What would let the prover discharge the check.
    pub suggestion: String,
    /// A `#[test]` reproducing it, when the function can be called from the
    /// test target.
    pub reproduction: Option<String>,
}

/// What the session learned about one obligation site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SiteReport {
    pub kind: ObligationKind,
    pub goal: String,
    pub location: Location,
    /// The source text of the checked expression.
    pub text: String,
    /// The target function the site is in, if it is in one.
    pub target: Option<usize>,
    pub hits: u64,
    /// Smallest distance from failing seen; `i64::MAX` when never reached.
    pub margin: i64,
    pub finding: Option<Finding>,
}

/// The state a site ends a session in (docs/proof-fuzz.md, section 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    Found,
    Survived,
    Unreached,
    NoGenerator,
}

impl SiteReport {
    pub fn state(&self, targets: &[Target]) -> State {
        if self.finding.is_some() {
            State::Found
        } else if self.hits > 0 {
            State::Survived
        } else if self
            .target
            .is_some_and(|target| targets[target].harness.is_err())
        {
            State::NoGenerator
        } else {
            State::Unreached
        }
    }
}

/// How the runs of one harness ended.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RunStats {
    pub runs: usize,
    /// No record: the run timed out or was killed.
    pub lost: usize,
    pub exited: usize,
    pub failed: usize,
    /// Panics outside every obligation site, and stack exhaustion.
    pub other: usize,
}

/// The harness program of a project, built and ready to run.
pub struct Session {
    /// Per target, how its harness's runs ended.
    pub stats: Vec<RunStats>,
    pub targets: Vec<Target>,
    assembled: Assembled,
    /// Fuzz-program site id to its report index; `None` for generated code.
    sites: Vec<Option<usize>>,
    pub reports: Vec<SiteReport>,
    binary: PathBuf,
    record: PathBuf,
    /// Element accesses the prover proved in bounds in the original program.
    pub bounds_proved: usize,
}

impl Session {
    /// Plan, generate, check and build the harness program for `original`
    /// (an entry program loaded with `modules`) in `directory`.
    /// Locations are shown relative to `root` when they are under it.
    pub fn new(
        original: &Program,
        modules: &dyn ModuleSource,
        links: &LinkSpec,
        directory: &Path,
        root: Option<&Path>,
        entries: Vec<Target>,
    ) -> Result<Self, String> {
        let checked = crate::executable::check_program(original)
            .map_err(|error| original.sources.render(&error))?;
        let mut targets = harness::plan(original, &checked);
        targets.extend(entries);
        let assembled = harness::assemble(original, &mut targets, modules)?;
        std::fs::create_dir_all(directory)
            .map_err(|e| format!("cannot create {}: {e}", directory.display()))?;
        // The generated sources, for reading when a harness behaves oddly.
        let mut generated_text = assembled.sources.root.clone();
        for (_, text) in assembled.sources.relays.values() {
            generated_text.push_str(&format!("\n// ---- relay ----\n{text}"));
        }
        for (module, extra) in &assembled.sources.appended {
            generated_text.push_str(&format!("\n// ---- appended to {module} ----\n{extra}"));
        }
        let _ = std::fs::write(directory.join("harnesses.kush"), generated_text);
        let binary = directory.join("harnesses");
        super::build(&assembled.executable, &binary, links)
            .map_err(|error| assembled.program.sources.render(&error))?;
        let ranges: Vec<(String, usize, usize)> = targets
            .iter()
            .map(|target| (target.file.clone(), target.range.0, target.range.1))
            .collect();
        let generated: BTreeMap<&str, usize> = assembled
            .sources
            .appended
            .iter()
            .filter_map(|(module, extra)| {
                let file = assembled.program.sources.files.iter().find(|file| {
                    file.text.ends_with(extra.as_str()) && module_matches(&file.text, module)
                })?;
                Some((file.name.as_str(), file.text.len() - extra.len()))
            })
            .collect();
        let mut sites = Vec::new();
        let mut reports = Vec::new();
        for site in assembled.executable.obligation_sites() {
            let Some(file) = assembled.program.sources.file(site.span) else {
                sites.push(None);
                continue;
            };
            let offset = site.span.start - file.base;
            let is_generated = file.name == assembled.sources.root_name
                || assembled.sources.relays.values().any(|(name, _)| *name == file.name)
                || generated
                    .get(file.name.as_str())
                    .is_some_and(|&start| offset >= start);
            if is_generated {
                sites.push(None);
                continue;
            }
            let before = &file.text[..offset];
            let shown = root
                .and_then(|root| Path::new(&file.name).strip_prefix(root).ok())
                .map_or_else(|| file.name.clone(), |path| path.display().to_string());
            let location = Location {
                file: shown,
                line: before.matches('\n').count() + 1,
                column: before.len() - before.rfind('\n').map_or(0, |at| at + 1) + 1,
            };
            let target = ranges
                .iter()
                .position(|(name, start, end)| *name == file.name && *start <= offset && offset < *end);
            sites.push(Some(reports.len()));
            reports.push(SiteReport {
                kind: site.kind,
                goal: site.goal.clone(),
                text: file
                    .text
                    .get(offset..site.span.end - file.base)
                    .unwrap_or("")
                    .to_owned(),
                location,
                target,
                hits: 0,
                margin: i64::MAX,
                finding: None,
            });
        }
        Ok(Self {
            stats: vec![RunStats::default(); targets.len()],
            targets,
            sites,
            reports,
            record: directory.join("record"),
            binary,
            assembled,
            bounds_proved: checked.bounds_report().0,
        })
    }

    pub fn executable(&self) -> &Executable {
        &self.assembled.executable
    }

    /// Whether a target is selected by the filter.
    pub fn selected(&self, target: usize, options: &Options) -> bool {
        options
            .filter
            .as_ref()
            .is_none_or(|filter| self.targets[target].name.contains(filter.as_str()))
    }

    /// Run every selected harness for its budget.
    pub fn fuzz(&mut self, options: &Options) {
        let start = Instant::now();
        let mut random = Random::new(options.seed);
        for number in 0..self.assembled.sources.harnesses.len() {
            let target = self.assembled.sources.harnesses[number];
            if !self.selected(target, options) {
                continue;
            }
            let layout = self.targets[target]
                .harness
                .clone()
                .expect("a harness has a layout");
            let dictionary = dictionary(&self.targets[target].constants);
            let mut corpus: Vec<Vec<u8>> = Vec::new();
            let mut queue = seeds(&layout, &dictionary);
            if self.targets[target].fuzz_entry
                && let Some(corpus) = &options.corpus
            {
                // Corpus files run first (the queue is popped from the end).
                queue.extend(entry_seeds(&corpus.join(&self.targets[target].name)));
            }
            let mut run = 0;
            while run < options.runs {
                if options.time.is_some_and(|limit| start.elapsed() >= limit) {
                    return;
                }
                // Seeds always join the corpus; mutants only when they
                // reach a new site or come closer to failing one.
                let (tape, seed) = match queue.pop() {
                    Some(tape) => (tape, true),
                    None if corpus.is_empty() => (vec![0; layout.fixed], true),
                    None => (
                        {
                        let parent = &corpus[random.below(corpus.len())];
                        let other = &corpus[random.below(corpus.len())];
                        mutate(parent, other, &layout, &dictionary, &mut random)
                        },
                        false,
                    ),
                };
                run += 1;
                self.stats[target].runs += 1;
                let Some(record) = self.execute(number, &tape, options.timeout) else {
                    self.stats[target].lost += 1;
                    continue;
                };
                match record.outcome {
                    Outcome::Exited => self.stats[target].exited += 1,
                    Outcome::Failed(_) => self.stats[target].failed += 1,
                    Outcome::Unattributed | Outcome::StackExhausted => self.stats[target].other += 1,
                }
                if self.absorb(target, &layout, &tape, run, &record) || seed {
                    corpus.push(tape);
                }
            }
            self.finish_findings(number, options);
        }
    }

    /// Minimize the new findings of harness `number`, then attach their
    /// suggestion and reproduction.
    fn finish_findings(&mut self, number: usize, options: &Options) {
        let target = self.assembled.sources.harnesses[number];
        let Ok(layout) = self.targets[target].harness.clone() else {
            return;
        };
        for report in 0..self.reports.len() {
            let Some(finding) = &self.reports[report].finding else {
                continue;
            };
            if finding.target != target || !finding.suggestion.is_empty() {
                continue;
            }
            let (tape, shrink_runs) = super::shrink::shrink(&layout, &finding.tape, SHRINK_BUDGET, |tape| {
                matches!(
                    self.execute(number, tape, options.timeout).map(|r| r.outcome),
                    Some(Outcome::Failed(site)) if self.sites.get(site).copied().flatten() == Some(report)
                )
            });
            let site = &self.reports[report];
            let owner = &self.targets[site.target.unwrap_or(target)];
            let suggestion = super::shrink::suggestion(site.kind, &site.text, &site.goal, owner);
            let what = format!("{} check at {}", site.kind.label(), site.location);
            let values = super::shrink::values(&layout, &tape);
            let reproduction = super::shrink::reproduction(
                &self.targets[target],
                &layout,
                &values,
                &what,
                site.location.line,
            );
            let finding = self.reports[report].finding.as_mut().expect("checked above");
            finding.inputs = decode(&layout, &tape);
            finding.tape = tape;
            finding.shrink_runs = shrink_runs;
            finding.suggestion = suggestion;
            finding.reproduction = reproduction;
        }
    }

    /// Replay the saved regression inputs of the selected functions, before
    /// any new input: a fixed bug shows as a survived check again.
    pub fn replay(&mut self, directory: &Path, options: &Options) {
        for number in 0..self.assembled.sources.harnesses.len() {
            let target = self.assembled.sources.harnesses[number];
            if !self.selected(target, options) {
                continue;
            }
            let Ok(layout) = self.targets[target].harness.clone() else {
                continue;
            };
            let Ok(entries) = std::fs::read_dir(directory.join(&self.targets[target].name)) else {
                continue;
            };
            let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
            paths.sort();
            for path in paths {
                let Ok(tape) = std::fs::read(&path) else {
                    continue;
                };
                self.stats[target].runs += 1;
                if let Some(record) = self.execute(number, &tape, options.timeout) {
                    self.absorb(target, &layout, &tape, 0, &record);
                }
            }
            self.finish_findings(number, options);
        }
    }

    /// `--save`: write each finding's reproduction into the test target
    /// (public functions) or its input under `regressions` (the others).
    /// Returns one line per file written.
    pub fn save(&self, test_target: Option<&Path>, regressions: &Path) -> Result<Vec<String>, String> {
        let mut written = Vec::new();
        let mut tests = Vec::new();
        for report in &self.reports {
            let Some(finding) = &report.finding else {
                continue;
            };
            if finding.run == 0 {
                continue;
            }
            let target = &self.targets[finding.target];
            match (&finding.reproduction, test_target) {
                (Some(test), Some(_)) => tests.push((target, test.clone())),
                _ => {
                    let directory = regressions.join(&target.name);
                    std::fs::create_dir_all(&directory)
                        .map_err(|e| format!("cannot create {}: {e}", directory.display()))?;
                    let path = directory.join(format!("{:016x}.tape", fnv(&finding.tape)));
                    std::fs::write(&path, &finding.tape)
                        .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
                    written.push(format!("saved input {}", path.display()));
                }
            }
        }
        if let (Some(path), false) = (test_target, tests.is_empty()) {
            let mut text = std::fs::read_to_string(path)
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            let mut added = 0;
            for (target, test) in tests {
                let name = test.lines().nth(1).unwrap_or("").to_owned();
                if text.contains(&name) {
                    continue;
                }
                let module = target.module.join(".");
                if !target.fuzz_entry
                    && !text.lines().any(|line| line.trim() == format!("use {module};"))
                {
                    text = insert_use(&text, &module);
                }
                if !text.contains(SAVED_MARKER) {
                    text.push_str(&format!("\n{SAVED_MARKER}\n"));
                }
                text.push('\n');
                text.push_str(&test);
                added += 1;
            }
            if added > 0 {
                std::fs::write(path, &text)
                    .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
                written.push(format!("added {added} tests to {}", path.display()));
            }
        }
        Ok(written)
    }

    /// Run harness `number` on one tape. `None` when the run left no record
    /// (it timed out or was killed).
    pub fn execute(&self, number: usize, tape: &[u8], timeout: Duration) -> Option<RunRecord> {
        // The harness reads at most its layout's longest tape.
        let target = self.assembled.sources.harnesses[number];
        let longest = self.targets[target].harness.as_ref().map_or(tape.len(), Layout::max_tape);
        let tape = &tape[..tape.len().min(longest)];
        let _ = std::fs::remove_file(&self.record);
        let mut child = Command::new(&self.binary)
            .arg(number.to_string())
            .env(super::OUT_VARIABLE, &self.record)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .ok()?;
        if let Some(mut input) = child.stdin.take() {
            // A harness that exits before reading closes the pipe; that is
            // not an error of the input.
            let _ = input.write_all(tape);
        }
        let deadline = Instant::now() + timeout;
        loop {
            match child.try_wait() {
                Ok(Some(_)) => break,
                Ok(None) if Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_micros(200));
                }
                _ => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return None;
                }
            }
        }
        RunRecord::parse(&std::fs::read(&self.record).ok()?)
    }

    /// Fold one run into the reports; whether the input is worth keeping
    /// (it reached a site for the first time or came closer to failing one).
    fn absorb(
        &mut self,
        target: usize,
        layout: &Layout,
        tape: &[u8],
        run: usize,
        record: &RunRecord,
    ) -> bool {
        let mut interesting = false;
        for (site, counters) in record.sites.iter().enumerate() {
            let Some(Some(report)) = self.sites.get(site).copied() else {
                continue;
            };
            let report = &mut self.reports[report];
            if counters.hits > 0 && report.hits == 0 {
                interesting = true;
            }
            report.hits += counters.hits;
            if counters.margin < report.margin {
                interesting = true;
                report.margin = counters.margin;
            }
        }
        if let Outcome::Failed(site) = record.outcome
            && let Some(Some(report)) = self.sites.get(site).copied()
            && self.reports[report].finding.is_none()
        {
            self.reports[report].finding = Some(Finding {
                target,
                tape: tape.to_vec(),
                inputs: decode(layout, tape),
                run,
                shrink_runs: 0,
                public: self.targets[target].public,
                suggestion: String::new(),
                reproduction: None,
            });
        }
        interesting
    }
}

impl Session {
    /// Reports of the sites in selected targets, plus every finding.
    pub fn shown(&self, options: &Options) -> Vec<&SiteReport> {
        // An entry attacks the whole program: every site it reaches counts.
        let entry = (0..self.targets.len())
            .any(|t| self.targets[t].fuzz_entry && self.targets[t].harness.is_ok() && self.selected(t, options));
        self.reports
            .iter()
            .filter(|report| {
                report.finding.is_some()
                    || report.target.is_some_and(|target| self.selected(target, options))
                    || (entry && report.hits > 0)
            })
            .collect()
    }

    pub fn found(&self) -> usize {
        self.reports.iter().filter(|r| r.finding.is_some()).count()
    }

    /// `kush fuzz --list`: each selected function and its checks, unrun.
    pub fn render_list(&self, options: &Options) -> String {
        let mut out = String::new();
        for (index, target) in self.targets.iter().enumerate() {
            if !self.selected(index, options) {
                continue;
            }
            match &target.harness {
                Ok(_) => out.push_str(&format!("{}\n", target.name)),
                Err(reason) => out.push_str(&format!("{}  (no generator: {reason})\n", target.name)),
            }
            for report in self.reports.iter().filter(|r| r.target == Some(index)) {
                out.push_str(&format!(
                    "  {:<9}{}  {}\n",
                    report.kind.label(),
                    report.location,
                    report.goal
                ));
            }
        }
        out
    }

    /// The session report: every finding in detail, then the counts.
    pub fn render(&self, options: &Options) -> String {
        let mut out = String::new();
        let shown = self.shown(options);
        for report in &shown {
            let Some(finding) = &report.finding else {
                continue;
            };
            let function = report
                .target
                .map_or("?", |target| self.targets[target].name.as_str());
            out.push_str(&format!(
                "FOUND  {:<9}{function}  {}\n       check    {}\n",
                report.kind.label(),
                report.location,
                report.goal
            ));
            let inputs: Vec<String> = finding
                .inputs
                .iter()
                .map(|(name, value)| format!("{name} = {value}"))
                .collect();
            let via = &self.targets[finding.target].name;
            let origin = if finding.run == 0 {
                "saved input".to_owned()
            } else {
                format!("run {}, minimized in {} runs", finding.run, finding.shrink_runs)
            };
            out.push_str(&format!(
                "       input    {}    (calling {via}, {origin})\n",
                if inputs.is_empty() { "(none)".to_owned() } else { inputs.join(", ") },
            ));
            out.push_str(&format!(
                "       kind     {}\n       suggest  {}\n",
                if finding.public {
                    "bug: reached through a public function"
                } else {
                    "local: reached through a private function; no caller may pass this input"
                },
                finding.suggestion
            ));
            if let Some(test) = &finding.reproduction {
                out.push_str("       test\n");
                for line in test.lines() {
                    out.push_str(&format!("           {line}\n"));
                }
            }
        }
        let mut counts = [0usize; 4];
        for report in &shown {
            counts[match report.state(&self.targets) {
                State::Found => 0,
                State::Survived => 1,
                State::Unreached => 2,
                State::NoGenerator => 3,
            }] += 1;
        }
        for (index, target) in self.targets.iter().enumerate() {
            if !self.selected(index, options) {
                continue;
            }
            if let Err(reason) = &target.harness {
                out.push_str(&format!("no generator  {}: {reason}\n", target.name));
            }
            let stats = self.stats[index];
            if stats.lost + stats.other > 0 {
                out.push_str(&format!(
                    "runs  {}: {} runs, {} timed out or killed, {} other panics\n",
                    target.name, stats.runs, stats.lost, stats.other
                ));
            }
        }
        out.push_str(&format!(
            "result: {} found, {} survived, {} unreached, {} without a generator; {} element accesses proved\n",
            counts[0], counts[1], counts[2], counts[3], self.bounds_proved
        ));
        out
    }
}

/// Runs spent minimizing one counterexample.
const SHRINK_BUDGET: usize = 300;

/// The comment `--save` puts before the tests it adds.
pub const SAVED_MARKER: &str = "// --- kush fuzz: reproductions ---";

/// Insert `use module;` after the last `use` line (or the module line).
fn insert_use(text: &str, module: &str) -> String {
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let at = lines
        .iter()
        .rposition(|line| line.trim_start().starts_with("use "))
        .or_else(|| lines.iter().position(|line| line.trim_start().starts_with("module ")))
        .map_or(0, |at| at + 1);
    let mut out = String::new();
    for (index, line) in lines.iter().enumerate() {
        if index == at {
            out.push_str(&format!("use {module};\n"));
        }
        out.push_str(line);
    }
    if at >= lines.len() {
        if !out.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(&format!("use {module};\n"));
    }
    out
}

/// FNV-1a, for stable names of saved inputs.
fn fnv(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// Whether `text` declares `module <dotted>;`.
fn module_matches(text: &str, dotted: &str) -> bool {
    text.contains(&format!("module {dotted};"))
}

/// Mutation dictionary: boundary values and the target's own constants.
fn dictionary(constants: &[i128]) -> Vec<i128> {
    let mut values = vec![
        0,
        1,
        -1,
        2,
        i128::from(i8::MIN),
        i128::from(i8::MAX),
        i128::from(u8::MAX),
        i128::from(i16::MIN),
        i128::from(i16::MAX),
        i128::from(u16::MAX),
        i128::from(i32::MIN),
        i128::from(i32::MAX),
        i128::from(u32::MAX),
        i128::from(i64::MIN),
        i128::from(i64::MAX),
        i128::from(u64::MAX),
    ];
    for &constant in constants {
        values.extend([constant - 1, constant, constant + 1]);
    }
    values.sort_unstable();
    values.dedup();
    values
}

/// Write `value` into `width` little-endian bytes at `offset`, growing the
/// tape with zeros if needed.
pub(super) fn put(tape: &mut Vec<u8>, offset: usize, width: usize, value: i128) {
    if tape.len() < offset + width {
        tape.resize(offset + width, 0);
    }
    tape[offset..offset + width].copy_from_slice(&value.to_le_bytes()[..width]);
}

pub(super) fn get(tape: &[u8], offset: usize, width: usize) -> u128 {
    let mut bytes = [0u8; 16];
    for (k, byte) in bytes.iter_mut().take(width).enumerate() {
        *byte = tape.get(offset + k).copied().unwrap_or(0);
    }
    u128::from_le_bytes(bytes)
}

/// The initial inputs: all zeros, then each scalar set to each dictionary
/// value in turn (the rest zero). Popped from the end, so zeros run first.
fn seeds(layout: &Layout, dictionary: &[i128]) -> Vec<Vec<u8>> {
    let mut seeds = Vec::new();
    for slot in &layout.slots {
        if let Slot::Scalar { offset, scalar, .. } = slot {
            for &value in dictionary {
                let mut tape = vec![0; layout.fixed];
                put(&mut tape, *offset, scalar.width(), value);
                seeds.push(tape);
            }
        }
    }
    seeds.push(vec![0; layout.fixed]);
    seeds
}

/// The corpus files of an entry as tapes: a two-byte length, then the bytes.
fn entry_seeds(directory: &Path) -> Vec<Vec<u8>> {
    let Ok(entries) = std::fs::read_dir(directory) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    paths.reverse();
    paths
        .iter()
        .filter_map(|path| std::fs::read(path).ok())
        .map(|bytes| {
            let bytes = &bytes[..bytes.len().min(harness::ENTRY_LENGTH)];
            let mut tape = (bytes.len() as u16).to_le_bytes().to_vec();
            tape.extend_from_slice(bytes);
            tape
        })
        .collect()
}

/// Byte ranges of each collection's elements on this tape, by slot index.
pub(super) fn element_ranges(layout: &Layout, tape: &[u8]) -> Vec<(usize, usize, usize)> {
    let mut at = layout.fixed;
    let mut ranges = Vec::new();
    for (index, slot) in layout.slots.iter().enumerate() {
        if let Slot::Collection {
            offset,
            collection,
            minimum,
            maximum,
            ..
        } = slot
        {
            let length = minimum + (get(tape, *offset, 2) as usize) % (maximum + 1);
            let width = element_width(*collection);
            ranges.push((index, at, length));
            at += length * width;
        }
    }
    ranges
}

pub(super) fn element_width(collection: Collection) -> usize {
    match collection {
        Collection::Bytes => 1,
        Collection::Vec(element) => element.width(),
    }
}

/// One to three random edits of `parent`.
fn mutate(
    parent: &[u8],
    other: &[u8],
    layout: &Layout,
    dictionary: &[i128],
    random: &mut Random,
) -> Vec<u8> {
    let mut tape = parent.to_vec();
    if tape.len() < layout.fixed {
        tape.resize(layout.fixed, 0);
    }
    for _ in 0..=random.below(3) {
        match random.below(10) {
            // A run of elements is deleted, or repeated (the length follows).
            8 | 9 => {
                let ranges = element_ranges(layout, &tape);
                if let Some(&(slot, start, length)) = ranges.get(random.below(ranges.len().max(1)))
                    && length > 0
                    && let Slot::Collection {
                        offset,
                        collection,
                        minimum,
                        maximum,
                        ..
                    } = &layout.slots[slot]
                {
                    let width = element_width(*collection);
                    let from = random.below(length);
                    let count = 1 + random.below((length - from).min(16));
                    let (a, b) = (start + from * width, start + (from + count) * width);
                    if tape.len() < start + length * width {
                        tape.resize(start + length * width, 0);
                    }
                    let new_length = if random.below(2) == 0 && length - count >= *minimum {
                        tape.drain(a..b);
                        length - count
                    } else if length + count <= minimum + maximum {
                        let run: Vec<u8> = tape[a..b].to_vec();
                        tape.splice(b..b, run);
                        length + count
                    } else {
                        length
                    };
                    put(&mut tape, *offset, 2, (new_length - minimum) as i128);
                }
            }
            // A scalar gets a dictionary value.
            0 | 1 => {
                if let Some(Slot::Scalar { offset, scalar, .. }) = pick_slot(layout, random, true) {
                    let value = dictionary[random.below(dictionary.len())];
                    put(&mut tape, *offset, scalar.width(), value);
                }
            }
            // A scalar moves by a small step.
            2 => {
                if let Some(Slot::Scalar { offset, scalar, .. }) = pick_slot(layout, random, true) {
                    let width = scalar.width();
                    let value = signed(get(&tape, *offset, width), *scalar);
                    let step = random.below(16) as i128 + 1;
                    let step = if random.below(2) == 0 { step } else { -step };
                    put(&mut tape, *offset, width, value + step);
                }
            }
            // A collection gets a new length.
            3 => {
                if let Some(Slot::Collection { offset, maximum, .. }) = pick_slot(layout, random, false) {
                    let length = if random.below(2) == 0 {
                        random.below(9)
                    } else {
                        random.below(maximum + 1)
                    };
                    put(&mut tape, *offset, 2, length as i128);
                }
            }
            // An element gets a dictionary value.
            4 => {
                let ranges = element_ranges(layout, &tape);
                if let Some(&(slot, start, length)) = ranges.get(random.below(ranges.len().max(1)))
                    && length > 0
                {
                    let Slot::Collection { collection, .. } = &layout.slots[slot] else {
                        unreachable!()
                    };
                    let width = element_width(*collection);
                    let value = dictionary[random.below(dictionary.len())];
                    put(&mut tape, start + random.below(length) * width, width, value);
                }
            }
            // A random bit flips.
            5 => {
                let at = random.below(tape.len().max(1));
                if tape.len() <= at {
                    tape.resize(at + 1, 0);
                }
                tape[at] ^= 1 << random.below(8);
            }
            // A random byte anywhere, possibly past the end.
            6 => {
                let at = random.below(tape.len() + 8);
                if tape.len() <= at {
                    tape.resize(at + 1, 0);
                }
                tape[at] = random.word() as u8;
            }
            // The tail comes from another input.
            _ => {
                let cut = random.below(tape.len().max(1));
                tape.truncate(cut.max(layout.fixed));
                if other.len() > tape.len() {
                    tape.extend_from_slice(&other[tape.len()..]);
                }
            }
        }
    }
    tape
}

fn pick_slot<'a>(layout: &'a Layout, random: &mut Random, scalar: bool) -> Option<&'a Slot> {
    let matching: Vec<&Slot> = layout
        .slots
        .iter()
        .filter(|slot| matches!(slot, Slot::Scalar { .. }) == scalar)
        .collect();
    (!matching.is_empty()).then(|| matching[random.below(matching.len())])
}

/// A tape word read as the scalar's value.
pub(super) fn signed(raw: u128, scalar: Scalar) -> i128 {
    match scalar {
        Scalar::Int {
            bytes,
            signed: true,
            ..
        } => {
            let shift = 128 - 8 * bytes as u32;
            ((raw << shift) as i128) >> shift
        }
        Scalar::Int { .. } => raw as i128,
        Scalar::Bool => (raw & 1) as i128,
    }
}

fn show_scalar(raw: u128, scalar: Scalar) -> String {
    match scalar {
        Scalar::Bool => (raw % 2 == 1).to_string(),
        _ => signed(raw, scalar).to_string(),
    }
}

/// The arguments a tape decodes to, named after the target's parameters.
pub fn decode(layout: &Layout, tape: &[u8]) -> Vec<(String, String)> {
    let ranges = element_ranges(layout, tape);
    let mut values = Vec::new();
    for (index, slot) in layout.slots.iter().enumerate() {
        let name = match slot {
            Slot::Scalar { name, .. } | Slot::Collection { name, .. } => name.clone(),
        };
        let value = match slot {
            Slot::Scalar { offset, scalar, .. } => show_scalar(get(tape, *offset, scalar.width()), *scalar),
            Slot::Collection { collection, .. } => {
                let &(_, start, length) = ranges
                    .iter()
                    .find(|(slot, ..)| *slot == index)
                    .expect("every collection has a range");
                match collection {
                    Collection::Bytes => {
                        let bytes: Vec<u8> = (0..length)
                            .map(|k| tape.get(start + k).copied().unwrap_or(0))
                            .collect();
                        format!("b\"{}\"", bytes.escape_ascii())
                    }
                    Collection::Vec(element) => {
                        let width = element.width();
                        let items: Vec<String> = (0..length)
                            .map(|k| show_scalar(get(tape, start + k * width, width), *element))
                            .collect();
                        format!("[{}]", items.join(", "))
                    }
                }
            }
        };
        values.push((name, value));
    }
    values
}

/// SplitMix64: small, deterministic, good enough to pick mutations.
pub struct Random(u64);

impl Random {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }
    pub fn word(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Uniform-enough in `0..n` (`n > 0`).
    pub fn below(&mut self, n: usize) -> usize {
        (self.word() % n.max(1) as u64) as usize
    }
}
