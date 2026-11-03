//! Project workflow: `Kush.toml`, local path dependencies, deterministic
//! resolution, `Kush.lock`, project build/run/check/test, formatting, and
//! scaffolding.
//!
//! The project layer does not change single-file commands and does not rewrite
//! source imports. It supplies a deterministic [`program::ModuleSource`] to the
//! existing loader and reuses the existing checker/native backend.
use crate::{
    ast::ItemKind,
    program::{self},
};
use std::{
    collections::BTreeMap,
    fmt, fs,
    io::Write,
    path::{Path, PathBuf},
};

pub mod format;
pub mod lock;
pub mod manifest;
pub mod modules;
pub mod new;
pub mod runtime;
pub mod test;

pub const MANIFEST_NAME: &str = "Kush.toml";
const MAX_PACKAGES: usize = 256;
const MAX_DEPENDENCY_DEPTH: usize = 64;

#[derive(Debug, Clone)]
pub struct Failure {
    message: String,
}

impl Failure {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Failure {}

#[derive(Debug, Clone)]
pub struct Package {
    pub name: String,
    pub version: String,
    /// Canonical package directory.
    pub root: PathBuf,
    pub manifest_path: PathBuf,
    /// Manifest-relative entry file.
    pub entry: PathBuf,
    /// Direct dependency import names, sorted.
    pub dependencies: Vec<String>,
    /// Reserved native-bridge options, with existing paths canonicalized.
    pub native: manifest::NativeOptions,
}

impl Package {
    pub fn entry_path(&self) -> PathBuf {
        self.root.join(&self.entry)
    }
}

#[derive(Debug, Clone)]
pub struct Project {
    /// Canonical root package directory.
    pub root: PathBuf,
    pub manifest_path: PathBuf,
    pub package: Package,
    /// Transitive dependencies, sorted by package name.
    pub dependencies: Vec<Package>,
    pub modules: modules::ModuleIndex,
    pub test_target: Option<PathBuf>,
}

/// Find `Kush.toml` in `start` (if it is a directory) or its parent, then walk
/// upward. An explicit file path is returned unchanged.
pub fn find_manifest(start: &Path) -> Option<PathBuf> {
    if start.is_file() && start.file_name().is_some_and(|name| name == MANIFEST_NAME) {
        return Some(start.to_path_buf());
    }
    let mut directory = if start.is_dir() {
        start
    } else {
        start.parent()?
    };
    loop {
        let candidate = directory.join(MANIFEST_NAME);
        if candidate.is_file() {
            return Some(candidate);
        }
        directory = directory.parent()?;
    }
}

/// Load the project whose manifest is `start/Kush.toml`, or whose directory
/// contains it when `start` is a directory.
pub fn load(start: &Path) -> Result<Project, Failure> {
    let manifest_path = if start.is_dir() {
        start.join(MANIFEST_NAME)
    } else {
        start.to_path_buf()
    };
    let manifest_path = fs::canonicalize(&manifest_path).map_err(|e| {
        Failure::new(format!(
            "cannot read project manifest {}: {e}",
            manifest_path.display()
        ))
    })?;
    if !manifest_path.is_file() {
        return Err(Failure::new(format!(
            "{}: project manifest is not a file",
            manifest_path.display()
        )));
    }
    load_manifest(&manifest_path)
}

pub fn load_manifest(path: &Path) -> Result<Project, Failure> {
    let root = path.parent().ok_or_else(|| {
        Failure::new(format!(
            "{}: manifest has no parent directory",
            path.display()
        ))
    })?;
    let root = fs::canonicalize(root).map_err(|e| {
        Failure::new(format!(
            "cannot resolve project directory {}: {e}",
            root.display()
        ))
    })?;
    let manifest_path = fs::canonicalize(path).map_err(|e| {
        Failure::new(format!(
            "cannot resolve project manifest {}: {e}",
            path.display()
        ))
    })?;
    let text = fs::read_to_string(&manifest_path)
        .map_err(|e| Failure::new(format!("cannot read {}: {e}", manifest_path.display())))?;
    let parsed = manifest::parse(&text, &manifest_path)?;
    let package = package_from(parsed.clone(), &root, &manifest_path, true)?;
    let root_name = package.name.clone();
    let mut dependencies = BTreeMap::new();
    let mut stack = vec![(root_name.clone(), manifest_path.clone())];
    for (name, relative) in &parsed.dependencies {
        if *name == root_name {
            return Err(Failure::new(format!(
                "{}: dependency '{name}' has the same name as the root package",
                manifest_path.display()
            )));
        }
        load_dependency(name, relative, &root, &mut dependencies, &mut stack)?;
    }
    let dependencies = dependencies.into_values().collect::<Vec<_>>();
    // A transitive package may claim the root's name; direct dependencies are
    // rejected above, but the deeper graph reached them only here.
    if let Some(conflict) = dependencies
        .iter()
        .find(|package| package.name == root_name)
    {
        return Err(Failure::new(format!(
            "package name '{}' is provided by both '{}' and '{}'",
            root_name,
            manifest_path.display(),
            conflict.manifest_path.display()
        )));
    }
    let mut all = Vec::with_capacity(dependencies.len() + 1);
    all.push(package.clone());
    all.extend(dependencies.iter().cloned());
    let mut modules = modules::ModuleIndex::build(&all)?;

    let test_target = match parsed.test {
        Some(relative) => {
            let path = package.root.join(relative);
            if !path.is_file() {
                return Err(Failure::new(format!(
                    "{}: test target '{}' does not exist",
                    manifest_path.display(),
                    path.display()
                )));
            }
            Some(path)
        }
        None => {
            let default = package.root.join("tests/main.kush");
            default.is_file().then_some(default)
        }
    };

    if let Some(target) = &test_target {
        modules.register_test(&package, target)?;
    }
    Ok(Project {
        root: package.root.clone(),
        manifest_path: package.manifest_path.clone(),
        package,
        dependencies,
        modules,
        test_target,
    })
}

fn package_from(
    parsed: manifest::Manifest,
    root: &Path,
    manifest_path: &Path,
    is_root: bool,
) -> Result<Package, Failure> {
    let entry = root.join(&parsed.package.entry);
    if !entry.is_file() {
        return Err(Failure::new(format!(
            "{}: package '{}' entry '{}' does not exist",
            manifest_path.display(),
            parsed.package.name,
            entry.display()
        )));
    }
    if is_root && let Some(test) = &parsed.test {
        let path = root.join(test);
        if !path.is_file() {
            return Err(Failure::new(format!(
                "{}: test target '{}' does not exist",
                manifest_path.display(),
                path.display()
            )));
        }
    }
    let native = manifest::resolve_native(&parsed.native, root, manifest_path)?;
    Ok(Package {
        name: parsed.package.name,
        version: parsed.package.version,
        root: root.to_path_buf(),
        manifest_path: manifest_path.to_path_buf(),
        entry: parsed.package.entry,
        dependencies: parsed.dependencies.keys().cloned().collect(),
        native,
    })
}

fn load_dependency(
    expected_name: &str,
    relative: &Path,
    parent_root: &Path,
    packages: &mut BTreeMap<String, Package>,
    stack: &mut Vec<(String, PathBuf)>,
) -> Result<(), Failure> {
    if stack.len() > MAX_DEPENDENCY_DEPTH {
        return Err(Failure::new(format!(
            "dependency graph is deeper than {MAX_DEPENDENCY_DEPTH} packages"
        )));
    }
    let directory = parent_root.join(relative);
    let directory = fs::canonicalize(&directory).map_err(|e| {
        Failure::new(format!(
            "dependency '{expected_name}' path '{}' cannot be resolved: {e}",
            directory.display()
        ))
    })?;
    if !directory.is_dir() {
        return Err(Failure::new(format!(
            "dependency '{expected_name}' path '{}' is not a directory",
            directory.display()
        )));
    }
    let manifest_path = directory.join(MANIFEST_NAME);
    if !manifest_path.is_file() {
        return Err(Failure::new(format!(
            "dependency '{expected_name}' at '{}' has no {MANIFEST_NAME}",
            directory.display()
        )));
    }
    let manifest_path = fs::canonicalize(&manifest_path).map_err(|e| {
        Failure::new(format!(
            "dependency '{expected_name}' manifest {} cannot be resolved: {e}",
            manifest_path.display()
        ))
    })?;
    if let Some(position) = stack.iter().position(|(_, path)| path == &manifest_path) {
        let mut chain = stack[position..]
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        chain.push(expected_name.to_owned());
        return Err(Failure::new(format!(
            "dependency cycle: {}",
            chain.join(" -> ")
        )));
    }
    let text = fs::read_to_string(&manifest_path).map_err(|e| {
        Failure::new(format!(
            "cannot read dependency manifest {}: {e}",
            manifest_path.display()
        ))
    })?;
    let parsed = manifest::parse(&text, &manifest_path)?;
    if parsed.package.name != expected_name {
        return Err(Failure::new(format!(
            "{}: dependency '{expected_name}' declares package name '{}'; dependency keys must match package names (renames are not supported)",
            manifest_path.display(),
            parsed.package.name
        )));
    }
    if let Some(existing) = packages.get(expected_name) {
        if existing.manifest_path == manifest_path {
            return Ok(());
        }
        return Err(Failure::new(format!(
            "package name '{expected_name}' is provided by both '{}' and '{}'",
            existing.manifest_path.display(),
            manifest_path.display()
        )));
    }
    if packages.len() >= MAX_PACKAGES {
        return Err(Failure::new(format!(
            "project has more than {MAX_PACKAGES} dependency packages"
        )));
    }
    let package = package_from(parsed.clone(), &directory, &manifest_path, false)?;
    packages.insert(expected_name.to_owned(), package);
    stack.push((expected_name.to_owned(), manifest_path));
    for (name, relative) in &parsed.dependencies {
        load_dependency(name, relative, &directory, packages, stack)?;
    }
    stack.pop();
    Ok(())
}

impl Project {
    pub fn all_packages(&self) -> impl Iterator<Item = &Package> {
        std::iter::once(&self.package).chain(self.dependencies.iter())
    }

    pub fn load_program(&self, path: &Path) -> Result<program::Program, Failure> {
        let name = path.display().to_string();
        let text = fs::read_to_string(path)
            .map_err(|e| Failure::new(format!("cannot read {name}: {e}")))?;
        program::load(&name, &text, &self.modules).map_err(|(sources, diagnostic)| {
            Failure::new(sources.map_or_else(
                || diagnostic.render(&name, &text),
                |sources| sources.render(&diagnostic),
            ))
        })
    }

    pub fn load_program_source(&self, name: &str, text: &str) -> Result<program::Program, Failure> {
        program::load(name, text, &self.modules).map_err(|(sources, diagnostic)| {
            Failure::new(sources.map_or_else(
                || diagnostic.render(name, text),
                |sources| sources.render(&diagnostic),
            ))
        })
    }

    fn native_links(&self) -> Result<crate::native::LinkSpec, Failure> {
        let mut links = crate::native::LinkSpec::default();
        for package in self.all_packages() {
            let spec = crate::native::LinkSpec::from_project_native(
                &package.root,
                &package.native.libraries,
                &package.native.library_paths,
                &package.native.cargo_manifests,
            )
            .map_err(|error| Failure::new(error.message))?;
            for item in spec.objects {
                if !links.objects.contains(&item) {
                    links.objects.push(item);
                }
            }
            for item in spec.libraries {
                if !links.libraries.contains(&item) {
                    links.libraries.push(item);
                }
            }
            for item in spec.library_dirs {
                if !links.library_dirs.contains(&item) {
                    links.library_dirs.push(item);
                }
            }
            for item in spec.system_libraries {
                if !links.system_libraries.contains(&item) {
                    links.system_libraries.push(item);
                }
            }
        }
        Ok(links)
    }
}

#[derive(Debug, Clone, Default)]
pub struct BuildOptions {
    pub output: Option<PathBuf>,
    pub stats: bool,
    pub locked: bool,
}

#[derive(Debug, Clone)]
pub struct BuildOutcome {
    pub output: PathBuf,
    pub entry: PathBuf,
    pub functions: usize,
}

pub fn build(project: &Project, options: &BuildOptions) -> Result<BuildOutcome, Failure> {
    lock::verify_or_write(project, options.locked)?;
    let entry = project.package.entry_path();
    let program = project.load_program(&entry)?;
    let checked = crate::executable::check_program(&program)
        .map_err(|error| Failure::new(program.sources.render(&error)))?;
    let output = options.output.clone().unwrap_or_else(|| {
        project
            .root
            .join("target")
            .join("kush")
            .join(&project.package.name)
    });
    if fs::canonicalize(&entry).ok() == fs::canonicalize(&output).ok() {
        return Err(Failure::new(format!(
            "{}: output must not overwrite the source file",
            output.display()
        )));
    }
    if let Some(parent) = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|e| {
            Failure::new(format!(
                "cannot create output directory {}: {e}",
                parent.display()
            ))
        })?;
    }
    let links = project.native_links()?;
    crate::native::build_with_options(&checked, &output, options.stats, &links)
        .map_err(|error| Failure::new(program.sources.render(&error)))?;
    Ok(BuildOutcome {
        output,
        entry,
        functions: checked.function_count(),
    })
}

#[derive(Debug, Clone)]
pub enum CheckSummary {
    Executable { path: PathBuf, functions: usize },
    Logical { path: PathBuf, definitions: usize },
}

impl CheckSummary {
    pub fn path(&self) -> &Path {
        match self {
            Self::Executable { path, .. } | Self::Logical { path, .. } => path,
        }
    }

    pub fn render(&self) -> String {
        let path = match self {
            Self::Executable { path, .. } | Self::Logical { path, .. } => path.display(),
        };
        match self {
            Self::Executable { functions, .. } => format!(
                "Checked {path}: {functions} executable functions (value types, patterns, and declared effects)."
            ),
            Self::Logical { definitions, .. } => format!(
                "Checked {path}: {definitions} logical definitions (restricted kernel; ownership/effect/subtype checking is not implemented)."
            ),
        }
    }
}

pub fn check(project: &Project, locked: bool) -> Result<Vec<CheckSummary>, Failure> {
    // `check` is the fast wiring gate: the native extension points a build
    // would reject now fail here too, before any lock file is written.
    project.native_links()?;
    lock::verify_or_write(project, locked)?;
    let mut summaries = Vec::new();
    let entry = project.package.entry_path();
    let source = fs::read_to_string(&entry)
        .map_err(|e| Failure::new(format!("cannot read {}: {e}", entry.display())))?;
    let module = crate::parser::parse(&source)
        .map_err(|error| Failure::new(error.render(&entry.display().to_string(), &source)))?;
    let executable = module.items.iter().any(|declaration| {
        matches!(
            &declaration.item.kind,
            ItemKind::Enum { total: false, .. }
                | ItemKind::Struct { .. }
                | ItemKind::Use(_)
                | ItemKind::Trait { .. }
                | ItemKind::Impl { .. }
        ) || matches!(&declaration.item.kind, ItemKind::Function(function) if !function.total)
    });
    if executable {
        let program = project.load_program(&entry)?;
        let checked = crate::executable::check_program(&program)
            .map_err(|error| Failure::new(program.sources.render(&error)))?;
        summaries.push(CheckSummary::Executable {
            path: entry,
            functions: checked.function_count(),
        });
    } else {
        let checked = crate::check::check(&source)
            .map_err(|error| Failure::new(error.render(&entry.display().to_string(), &source)))?;
        summaries.push(CheckSummary::Logical {
            path: entry,
            definitions: checked.definitions.len(),
        });
    }
    if let Some(target) = &project.test_target {
        let (source, tests) = test::discover(project, target)?;
        let source = test::synthesized_source(&source, &tests);
        let name = target.display().to_string();
        let program = project.load_program_source(&name, &source)?;
        let checked = crate::executable::check_program(&program)
            .map_err(|error| Failure::new(program.sources.render(&error)))?;
        summaries.push(CheckSummary::Executable {
            path: target.clone(),
            functions: checked.function_count(),
        });
    }
    Ok(summaries)
}

#[derive(Debug, Clone, Default)]
pub struct RunOptions {
    pub output: Option<PathBuf>,
    pub stats: bool,
    pub locked: bool,
    pub arguments: Vec<std::ffi::OsString>,
}

pub fn run(project: &Project, options: &RunOptions) -> Result<u8, Failure> {
    let built = build(
        project,
        &BuildOptions {
            output: options.output.clone(),
            stats: options.stats,
            locked: options.locked,
        },
    )?;
    runtime::run_artifact(&built.output, &options.arguments)
}

#[derive(Debug, Clone, Default)]
pub struct TestOptions {
    pub filter: Option<String>,
    pub exact: bool,
    pub list: bool,
    pub nocapture: bool,
    pub locked: bool,
}

#[derive(Debug, Clone)]
pub struct TestSummary {
    pub target: PathBuf,
    pub passed: usize,
    pub failed: usize,
    pub filtered: usize,
    pub total: usize,
}

pub fn test_project(
    project: &Project,
    options: &TestOptions,
    out: &mut dyn Write,
) -> Result<TestSummary, Failure> {
    lock::verify_or_write(project, options.locked)?;
    let target = project.test_target.clone().ok_or_else(|| {
        Failure::new(format!(
            "{}: no test target configured; add `test = \"tests/main.kush\"` to [package] or create tests/main.kush",
            project.manifest_path.display()
        ))
    })?;
    let (source, tests) = test::discover(project, &target)?;
    let selected = tests
        .iter()
        .filter(|test| matches_filter(test.id(), options.filter.as_deref(), options.exact))
        .cloned()
        .collect::<Vec<_>>();
    let filtered = tests.len() - selected.len();
    if options.list {
        for test in &selected {
            writeln!(out, "{}: test", test.name).map_err(output_failure)?;
        }
        if selected.is_empty() {
            writeln!(out).map_err(output_failure)?;
        }
        writeln!(
            out,
            "{} {}, {filtered} filtered out",
            selected.len(),
            if selected.len() == 1 { "test" } else { "tests" }
        )
        .map_err(output_failure)?;
        return Ok(TestSummary {
            target,
            passed: 0,
            failed: 0,
            filtered,
            total: tests.len(),
        });
    }
    // A filter selects execution, not whether the target is valid.
    let generated = test::synthesized_source(&source, &tests);
    let program = project.load_program_source(&target.display().to_string(), &generated)?;
    let _ = crate::executable::check_program(&program)
        .map_err(|error| Failure::new(program.sources.render(&error)))?;
    writeln!(
        out,
        "running {} {} in {}",
        selected.len(),
        if selected.len() == 1 { "test" } else { "tests" },
        target.display()
    )
    .map_err(output_failure)?;
    writeln!(out).map_err(output_failure)?;
    let target_stem = target.file_stem().map_or_else(
        || "tests".to_owned(),
        |stem| stem.to_string_lossy().into_owned(),
    );
    let artifact_directory = project.root.join("target").join("kush").join(".tests");
    fs::create_dir_all(&artifact_directory).map_err(|e| {
        Failure::new(format!(
            "cannot create test artifact directory {}: {e}",
            artifact_directory.display()
        ))
    })?;
    let links = if selected.is_empty() {
        crate::native::LinkSpec::default()
    } else {
        project.native_links()?
    };
    let mut passed = 0;
    let mut failures = Vec::new();
    for (index, test) in selected.iter().enumerate() {
        let generated = test::synthesized_source(&source, std::slice::from_ref(test));
        let name = target.display().to_string();
        let program = project.load_program_source(&name, &generated)?;
        let checked = crate::executable::check_program(&program)
            .map_err(|error| Failure::new(program.sources.render(&error)))?;
        // Concurrent `kush test` runs must not build into the same final
        // filename: each artifact is built under a process-unique temporary
        // name and installed with an atomic rename.
        let artifact =
            artifact_directory.join(format!("{target_stem}__{:02}_{}", index + 1, test.name));
        let temporary = artifact_directory.join(format!(
            "{target_stem}__{:02}_{}.{}.tmp",
            index + 1,
            test.name,
            std::process::id()
        ));
        let _ = fs::remove_file(&temporary);
        crate::native::build_with_options(&checked, &temporary, false, &links)
            .map_err(|error| Failure::new(program.sources.render(&error)))?;
        fs::rename(&temporary, &artifact).map_err(|e| {
            Failure::new(format!(
                "cannot install test binary {}: {e}",
                artifact.display()
            ))
        })?;
        let invocation =
            runtime::ProgramInvocation::new(&artifact, std::iter::empty::<std::ffi::OsString>());
        let output = invocation
            .command()
            .current_dir(&project.root)
            .output()
            .map_err(|e| Failure::new(format!("cannot execute test '{}': {e}", test.name)))?;
        if output.status.success() {
            passed += 1;
            writeln!(out, "test {} ... ok", test.name).map_err(output_failure)?;
            if options.nocapture && (!output.stdout.is_empty() || !output.stderr.is_empty()) {
                write_captured(out, &output.stdout, &output.stderr)?;
            }
        } else {
            writeln!(out, "test {} ... FAILED", test.name).map_err(output_failure)?;
            failures.push((test.name.clone(), output));
        }
    }
    if !failures.is_empty() {
        writeln!(out, "\nfailures:\n").map_err(output_failure)?;
        for (name, output) in &failures {
            writeln!(out, "---- {name} ----").map_err(output_failure)?;
            writeln!(out, "status: {}", describe_status(&output.status)).map_err(output_failure)?;
            write_captured(out, &output.stdout, &output.stderr)?;
            writeln!(out).map_err(output_failure)?;
        }
    }
    let failed = failures.len();
    writeln!(
        out,
        "test result: {}. {passed} passed; {failed} failed; {filtered} filtered out",
        if failed == 0 { "ok" } else { "FAILED" }
    )
    .map_err(output_failure)?;
    Ok(TestSummary {
        target,
        passed,
        failed,
        filtered,
        total: tests.len(),
    })
}

fn matches_filter(name: &str, filter: Option<&str>, exact: bool) -> bool {
    match filter {
        None => true,
        Some(filter) if exact => name == filter,
        Some(filter) => name.contains(filter),
    }
}

fn write_captured(out: &mut dyn Write, stdout: &[u8], stderr: &[u8]) -> Result<(), Failure> {
    if !stdout.is_empty() {
        writeln!(out, "stdout:").map_err(output_failure)?;
        for line in String::from_utf8_lossy(stdout).lines() {
            writeln!(out, "    {line}").map_err(output_failure)?;
        }
    }
    if !stderr.is_empty() {
        writeln!(out, "stderr:").map_err(output_failure)?;
        for line in String::from_utf8_lossy(stderr).lines() {
            writeln!(out, "    {line}").map_err(output_failure)?;
        }
    }
    Ok(())
}

fn describe_status(status: &std::process::ExitStatus) -> String {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = status.signal() {
            return format!("terminated by signal {signal}");
        }
    }
    match status.code() {
        Some(code) => format!("exit code {code}"),
        None => status.to_string(),
    }
}

fn output_failure(error: std::io::Error) -> Failure {
    Failure::new(format!("cannot write output: {error}"))
}
