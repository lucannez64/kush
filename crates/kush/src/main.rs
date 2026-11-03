use kush::{
    Diagnostic, Span,
    ast::ItemKind,
    project::{self, Project},
};
use std::{
    env,
    ffi::OsString,
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::ExitCode,
};

const HELP: &str = "Kush 0.1.0\n\n\
Single files:\n\
  kush parse <file.kush> [--ast]\n\
  kush lex <file.kush>\n\
  kush resolve <file.kush>\n\
  kush check <file.kush>\n\
  kush build <file.kush> -o <executable> [--stats] [--link <archive>] [--link-lib <name>]\n\
  kush run <file.kush> [--stats] [-- <program args>...]\n\
  kush eval <file.kush> [--stats] [-- <program args>...]\n\n\
Projects (Kush.toml):\n\
  kush new <directory> [--name <name>]\n\
  kush check [--manifest-path <Kush.toml>] [--locked]\n\
  kush build [--manifest-path <Kush.toml>] [-o <executable>] [--stats] [--locked]\n\
  kush run [--manifest-path <Kush.toml>] [--stats] [--locked] [-- <program args>...]\n\
  kush test [--manifest-path <Kush.toml>] [FILTER] [--exact] [--list] [--nocapture] [--locked]\n\
  kush fmt [--check] [--manifest-path <Kush.toml>] [FILE...]\n\n\
Native adapters (Bridge.toml):\n\
  kush bindgen <Bridge.toml> [--check]\n\n\
Editors:\n\
  kush lsp\n\n\
Native optimization (build/run, files or projects):\n\
  --release           Cranelift speed optimization + scalar callback inlining\n\
  --opt-level <none|speed>  select backend optimization independently\n\
  --inline-scalars / --no-inline-scalars  control the restricted inliner\n\n\
  kush --help\n\
  kush --version\n\n\
Build/run use Cranelift on Linux x86-64 and require cc. Eval is the bounded reference interpreter.\n\
Check accepts mixed programs: total logical definitions are kernel-checked and erased before executable checking.\n\
--stats writes one 'allocation-stats:' line to stderr; program stdout and exit status are unchanged.\n\
Project commands search upward for Kush.toml. Arguments after '--' are forwarded unchanged to the program.\n\
Test targets declare tests with #[test]; see docs/projects.md. kush fmt only normalizes trailing whitespace and the final newline.\n\
kush bindgen reads a strict Bridge.toml, writes generated Rust shims and a matching Kush module,\n\
and with --check reports drift without writing. It never overwrites files without the generated marker.\n";

fn output_error(e: io::Error) -> (u8, String) {
    (1, format!("cannot write output: {e}"))
}

fn run(args: Vec<OsString>, out: &mut impl Write) -> Result<u8, (u8, String)> {
    let Some(command) = args.first() else {
        return Err((2, HELP.into()));
    };
    if command == "--help" || command == "-h" || command == "--version" {
        if args.len() != 1 {
            return Err((2, "unexpected arguments".into()));
        }
        if command == "--version" {
            writeln!(out, "kush {}", env!("CARGO_PKG_VERSION")).map_err(output_error)?;
        } else {
            out.write_all(HELP.as_bytes()).map_err(output_error)?;
        }
        return Ok(0);
    }
    let name = command.to_string_lossy();
    let rest = &args[1..];
    match name.as_ref() {
        "new" => new_command(rest, out),
        "bindgen" => bindgen_command(rest, out),
        "fmt" => format_command(rest, out),
        "test" => test_command(rest, out),
        "check" | "build" | "run" if is_project_invocation(rest) => {
            project_command(name.as_ref(), rest, out)
        }
        _ => single_file_command(&args, out),
    }
}

fn is_project_invocation(rest: &[OsString]) -> bool {
    rest.is_empty()
        || rest.first().is_some_and(|argument| {
            // A dash-prefixed argument that names a Kush source routes through
            // the single-file flow, so a missing file keeps its "cannot read"
            // error instead of usage help. Flags (`-o`, `--locked`,
            // `--manifest-path`) stay project arguments.
            argument.to_string_lossy().starts_with('-')
                && !argument.to_string_lossy().ends_with(".kush")
        })
}

fn project_command(
    command: &str,
    args: &[OsString],
    out: &mut impl Write,
) -> Result<u8, (u8, String)> {
    match command {
        "check" => {
            let mut manifest = None;
            let mut locked = false;
            let mut index = 0;
            while index < args.len() {
                match argument(args, index, command)? {
                    "--manifest-path" => {
                        manifest = Some(PathBuf::from(value(args, &mut index, command)?));
                    }
                    "--locked" => locked = true,
                    other => return Err(usage_error(command, other)),
                }
                index += 1;
            }
            let project = open_project(manifest)?;
            let summaries = project::check(&project, locked).map_err(project_error)?;
            for summary in summaries {
                writeln!(out, "{}", summary.render()).map_err(output_error)?;
            }
            Ok(0)
        }
        "build" => {
            let mut manifest = None;
            let mut output = None;
            let mut stats = false;
            let mut codegen = kush::native::CodegenOptions::default();
            let mut locked = false;
            let mut index = 0;
            while index < args.len() {
                match argument(args, index, command)? {
                    "--manifest-path" => {
                        manifest = Some(PathBuf::from(value(args, &mut index, command)?));
                    }
                    "-o" => {
                        output = Some(PathBuf::from(value(args, &mut index, command)?));
                    }
                    "--stats" => stats = true,
                    "--locked" => locked = true,
                    other => {
                        if !codegen_argument(args, &mut index, &mut codegen, command)? {
                            return Err(usage_error(command, other));
                        }
                    }
                }
                index += 1;
            }
            let project = open_project(manifest)?;
            let built = project::build(
                &project,
                &project::BuildOptions {
                    codegen,
                    output,
                    stats,
                    locked,
                },
            )
            .map_err(project_error)?;
            writeln!(out, "Built {} with Cranelift.", built.output.display())
                .map_err(output_error)?;
            Ok(0)
        }
        "run" => {
            let mut manifest = None;
            let mut stats = false;
            let mut codegen = kush::native::CodegenOptions::default();
            let mut locked = false;
            let mut program_arguments = Vec::new();
            let mut index = 0;
            while index < args.len() {
                let text = argument(args, index, command)?;
                if text == "--" {
                    program_arguments.extend(args[index + 1..].iter().cloned());
                    break;
                }
                match text {
                    "--manifest-path" => {
                        manifest = Some(PathBuf::from(value(args, &mut index, command)?));
                    }
                    "--stats" => stats = true,
                    "--locked" => locked = true,
                    other => {
                        if !codegen_argument(args, &mut index, &mut codegen, command)? {
                            return Err(usage_error(command, other));
                        }
                    }
                }
                index += 1;
            }
            let project = open_project(manifest)?;
            out.flush().map_err(output_error)?;
            project::run(
                &project,
                &project::RunOptions {
                    codegen,
                    output: None,
                    stats,
                    locked,
                    arguments: program_arguments,
                },
            )
            .map_err(project_error)
        }
        _ => Err((2, format!("invalid command\n\n{HELP}"))),
    }
}

fn bindgen_command(args: &[OsString], out: &mut impl Write) -> Result<u8, (u8, String)> {
    let mut config = None;
    let mut check = false;
    let mut index = 0;
    while index < args.len() {
        match argument(args, index, "bindgen")? {
            "--check" => check = true,
            other if other.starts_with('-') => return Err(usage_error("bindgen", other)),
            other => {
                if config.is_some() {
                    return Err((2, "bindgen accepts exactly one Bridge.toml path".into()));
                }
                config = Some(PathBuf::from(other));
            }
        }
        index += 1;
    }
    let config = config.ok_or_else(|| (2, "bindgen requires a Bridge.toml path".into()))?;
    let report =
        kush::bindgen::run(&config, check).map_err(|error| (1, format!("bindgen: {error}")))?;
    out.write_all(report.render().as_bytes())
        .map_err(output_error)?;
    Ok(u8::from(check && report.changed()))
}

fn new_command(args: &[OsString], out: &mut impl Write) -> Result<u8, (u8, String)> {
    let mut directory = None;
    let mut name = None;
    let mut index = 0;
    while index < args.len() {
        match argument(args, index, "new")? {
            "--name" => {
                name = Some(
                    value(args, &mut index, "new")?
                        .to_string_lossy()
                        .into_owned(),
                );
            }
            other if other.starts_with('-') => return Err(usage_error("new", other)),
            other => {
                if directory.is_some() {
                    return Err((2, "new accepts exactly one directory path".into()));
                }
                directory = Some(PathBuf::from(other));
            }
        }
        index += 1;
    }
    let directory = directory.ok_or_else(|| (2, "new requires a directory path".into()))?;
    let created = project::new::create(&directory, name.as_deref()).map_err(project_error)?;
    writeln!(
        out,
        "Created {} (package {})",
        created.directory.display(),
        created.name
    )
    .map_err(output_error)?;
    Ok(0)
}

fn test_command(args: &[OsString], out: &mut impl Write) -> Result<u8, (u8, String)> {
    let mut manifest = None;
    let mut filter = None;
    let mut exact = false;
    let mut list = false;
    let mut nocapture = false;
    let mut locked = false;
    let mut index = 0;
    while index < args.len() {
        match argument(args, index, "test")? {
            "--manifest-path" => {
                manifest = Some(PathBuf::from(value(args, &mut index, "test")?));
            }
            "--exact" => exact = true,
            "--list" => list = true,
            "--nocapture" => nocapture = true,
            "--locked" => locked = true,
            other if other.starts_with('-') => return Err(usage_error("test", other)),
            other => {
                if filter.is_some() {
                    return Err((2, "test accepts at most one filter argument".into()));
                }
                filter = Some(other.to_owned());
            }
        }
        index += 1;
    }
    let project = open_project(manifest)?;
    let summary = project::test_project(
        &project,
        &project::TestOptions {
            filter,
            exact,
            list,
            nocapture,
            locked,
        },
        out,
    )
    .map_err(project_error)?;
    Ok(u8::from(summary.failed != 0))
}

fn format_command(args: &[OsString], out: &mut impl Write) -> Result<u8, (u8, String)> {
    let mut check = false;
    let mut manifest = None;
    let mut files = Vec::new();
    let mut index = 0;
    while index < args.len() {
        match argument(args, index, "fmt")? {
            "--check" => check = true,
            "--manifest-path" => {
                manifest = Some(PathBuf::from(value(args, &mut index, "fmt")?));
            }
            other if other.starts_with('-') => return Err(usage_error("fmt", other)),
            other => files.push(PathBuf::from(other)),
        }
        index += 1;
    }
    if files.is_empty() {
        let project = open_project(manifest)?;
        let outcome = project::format::format_project(&project, check).map_err(project_error)?;
        for path in &outcome.changed {
            if check {
                writeln!(out, "{}: would be reformatted", path.display()).map_err(output_error)?;
            } else {
                writeln!(out, "Formatted {}", path.display()).map_err(output_error)?;
            }
        }
        if outcome.changed.is_empty() {
            writeln!(out, "{} files already formatted", outcome.unchanged).map_err(output_error)?;
        }
        return Ok(u8::from(check && !outcome.changed.is_empty()));
    }
    let mut changed = 0;
    for path in &files {
        let was_changed = project::format::format_file(path, check).map_err(project_error)?;
        if was_changed {
            changed += 1;
            if check {
                writeln!(out, "{}: would be reformatted", path.display()).map_err(output_error)?;
            } else {
                writeln!(out, "Formatted {}", path.display()).map_err(output_error)?;
            }
        }
    }
    if changed == 0 {
        writeln!(out, "{} files already formatted", files.len()).map_err(output_error)?;
    }
    Ok(u8::from(check && changed != 0))
}

fn open_project(manifest: Option<PathBuf>) -> Result<Project, (u8, String)> {
    let manifest = match manifest {
        Some(path) => {
            if path.is_dir() {
                // `--manifest-path <dir>` behaves like the default search.
                project::find_manifest(&path)
                    .ok_or_else(|| (2, format!("no Kush.toml found in {}", path.display())))?
            } else if !path.exists() {
                return Err((
                    2,
                    format!("project manifest {} does not exist", path.display()),
                ));
            } else {
                path
            }
        }
        None => {
            let current = env::current_dir()
                .map_err(|e| (1, format!("cannot determine current directory: {e}")))?;
            project::find_manifest(&current).ok_or_else(|| {
                (
                    2,
                    format!(
                        "no Kush.toml found in {} or any parent directory",
                        current.display()
                    ),
                )
            })?
        }
    };
    project::load(&manifest).map_err(project_error)
}

fn project_error(failure: project::Failure) -> (u8, String) {
    (1, failure.message().to_owned())
}

fn argument<'a>(
    args: &'a [OsString],
    index: usize,
    command: &str,
) -> Result<&'a str, (u8, String)> {
    args[index].to_str().ok_or_else(|| {
        (
            2,
            format!("{command}: arguments must be valid UTF-8 option names"),
        )
    })
}

fn value<'a>(
    args: &'a [OsString],
    index: &mut usize,
    command: &str,
) -> Result<&'a OsString, (u8, String)> {
    *index += 1;
    args.get(*index)
        .ok_or_else(|| (2, format!("{command}: option requires a value\n\n{HELP}")))
}

fn usage_error(command: &str, argument: &str) -> (u8, String) {
    (
        2,
        format!("{command}: unexpected argument '{argument}'\n\n{HELP}"),
    )
}

fn codegen_argument(
    args: &[OsString],
    index: &mut usize,
    options: &mut kush::native::CodegenOptions,
    command: &str,
) -> Result<bool, (u8, String)> {
    match args[*index].to_str() {
        Some("--release") => *options = kush::native::CodegenOptions::release(),
        Some("--inline-scalars") => options.inline_scalar_callbacks = true,
        Some("--no-inline-scalars") => options.inline_scalar_callbacks = false,
        Some("--opt-level") => {
            options.optimization = match value(args, index, command)?.to_str() {
                Some("none") => kush::native::Optimization::None,
                Some("speed") => kush::native::Optimization::Speed,
                _ => return Err((2, "--opt-level requires 'none' or 'speed'".into())),
            };
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn single_file_command(args: &[OsString], out: &mut impl Write) -> Result<u8, (u8, String)> {
    let Some(command) = args.first() else {
        return Err((2, HELP.into()));
    };
    let run_like = command == "run" || command == "eval";
    let ast = command == "parse" && args.len() == 3 && args[2] == "--ast";
    let mut codegen = kush::native::CodegenOptions::default();
    let mut links = kush::native::LinkSpec::default();
    let mut build = false;
    let mut build_stats = false;
    if command == "build" && args.len() >= 4 && args[2] == "-o" {
        build = true;
        let mut index = 4;
        while index < args.len() {
            match args[index].to_str() {
                Some("--stats") => build_stats = true,
                Some("--link") | Some("--link-lib") => {
                    let flag = args[index].to_str().unwrap_or_default();
                    index += 1;
                    let Some(value) = args.get(index).and_then(|value| value.to_str()) else {
                        build = false;
                        break;
                    };
                    if flag == "--link" {
                        links.libraries.push(value.into());
                    } else {
                        links.system_libraries.push(value.to_owned());
                    }
                }
                _ => {
                    if !codegen_argument(args, &mut index, &mut codegen, "build")? {
                        build = false;
                        break;
                    }
                }
            }
            index += 1;
        }
    }
    let mut stats = (run_like && args.len() == 3 && args[2] == "--stats")
        || (command == "build" && build_stats);
    let mut program_arguments = Vec::new();
    let mut run_file_valid = false;
    if run_like {
        let mut index = 2;
        run_file_valid = true;
        while index < args.len() {
            if args[index] == "--" {
                program_arguments.extend(args[index + 1..].iter().cloned());
                break;
            } else if args[index] == "--stats" {
                stats = true;
            } else if command != "run" || !codegen_argument(args, &mut index, &mut codegen, "run")?
            {
                run_file_valid = false;
                break;
            }
            index += 1;
        }
    }

    let valid = if command == "parse" {
        args.len() == 2 || ast
    } else if command == "build" {
        build
    } else if run_like {
        args.len() == 2 || run_file_valid
    } else {
        args.len() == 2
    };
    let known = ["parse", "lex", "resolve", "check", "build", "run", "eval"]
        .iter()
        .any(|name| command == name);
    if !known || !valid {
        return Err((2, format!("invalid arguments\n\n{HELP}")));
    }
    let path = Path::new(&args[1]);
    let name = path.to_string_lossy();
    let source = fs::read_to_string(path).map_err(|e| (1, format!("cannot read {name}: {e}")))?;
    let diagnostic = |e: Diagnostic| (1, e.render(&name, &source));
    // Commands that see a whole program load the root file plus its imports.
    let load = || -> Result<kush::program::Program, (u8, String)> {
        kush::program::load_path(path).map_err(|(sources, e)| {
            (
                1,
                sources.map_or_else(|| e.render(&name, &source), |s| s.render(&e)),
            )
        })
    };
    if command == "lex" {
        for token in kush::lexer::lex(&source).map_err(diagnostic)? {
            writeln!(
                out,
                "{}..{} {:?}",
                token.span.start, token.span.end, token.kind
            )
            .map_err(output_error)?;
        }
    } else if command == "resolve" {
        let program = load()?;
        let resolved = kush::resolve::resolve_program(&program)
            .map_err(|e| (1, program.sources.render(&e)))?;
        writeln!(
            out,
            "Resolved {name}: {} references across {} modules (names only).",
            resolved.references.len(),
            program.units.len()
        )
        .map_err(output_error)?;
    } else if command == "check" {
        let module = kush::parse(&source).map_err(diagnostic)?;
        if module.items.iter().any(|d| {
            matches!(
                &d.item.kind,
                ItemKind::Enum { total: false, .. }
                    | ItemKind::Struct { .. }
                    | ItemKind::Use(_)
                    | ItemKind::Trait { .. }
                    | ItemKind::Impl { .. }
            ) || matches!(&d.item.kind, ItemKind::Function(f) if !f.total)
        }) {
            let program = load()?;
            let checked = kush::executable::check_program(&program)
                .map_err(|e| (1, program.sources.render(&e)))?;
            writeln!(
                out,
                "Checked {name}: {} executable functions (value types, patterns, and declared effects).",
                checked.function_count()
            )
            .map_err(output_error)?;
        } else {
            let checked = kush::check(&source).map_err(diagnostic)?;
            writeln!(out, "Checked {name}: {} logical definitions (restricted kernel; ownership/effect/subtype checking is not implemented).", checked.definitions.len()).map_err(output_error)?;
        }
    } else if command == "build" || command == "run" || command == "eval" {
        let program = load()?;
        let checked = kush::executable::check_program(&program)
            .map_err(|e| (1, program.sources.render(&e)))?;
        if command == "eval" {
            let argv = std::iter::once(&args[1])
                .chain(program_arguments.iter())
                .map(|value| value.as_encoded_bytes().to_vec())
                .collect();
            let host = kush::Host::process().with_args(argv);
            if stats {
                let (result, stats) = checked
                    .evaluate_with_host_and_stats(&mut io::stdin().lock(), out, &host)
                    .map_err(diagnostic)?;
                eprintln!("{}", stats.report());
                return Ok((result as u64 & 255) as u8);
            }
            let result = checked
                .evaluate_with_host(&mut io::stdin().lock(), out, &host)
                .map_err(diagnostic)?;
            return Ok((result as u64 & 255) as u8);
        }
        if command == "build" {
            let output = Path::new(&args[3]);
            if fs::canonicalize(path).ok() == fs::canonicalize(output).ok() {
                return Err(diagnostic(Diagnostic::new(
                    Span::default(),
                    "output must not overwrite the source file",
                )));
            }
            kush::native::build_with_codegen(&checked, output, stats, &links, codegen)
                .map_err(diagnostic)?;
            writeln!(out, "Built {} with Cranelift.", output.display()).map_err(output_error)?;
        } else {
            let scratch = kush::native::Scratch::new(&env::temp_dir()).map_err(diagnostic)?;
            let binary = scratch.path().join("program");
            kush::native::build_with_codegen(&checked, &binary, stats, &links, codegen)
                .map_err(diagnostic)?;
            return kush::project::runtime::run_artifact(&binary, &program_arguments)
                .map_err(project_error);
        }
    } else {
        let module = kush::parse(&source).map_err(diagnostic)?;
        if ast {
            writeln!(out, "{module:#?}").map_err(output_error)?;
        } else {
            writeln!(
                out,
                "Parsed {name}: {} declarations (syntax only).",
                module.items.len()
            )
            .map_err(output_error)?;
        }
    }
    Ok(0)
}

fn main() -> ExitCode {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    // The language server owns stdout as a framed JSON-RPC stream. Dispatch it
    // before locking stdout for the ordinary command printer.
    if args.first().is_some_and(|argument| argument == "lsp") {
        if let Err(message) = kush::language_server::parse_stdio_args(&args[1..]) {
            let _ = writeln!(io::stderr().lock(), "{message}");
            return ExitCode::from(2);
        }
        return match kush::language_server::run_stdio() {
            Ok(code) => ExitCode::from(code),
            Err(error) => {
                let _ = writeln!(io::stderr().lock(), "kush lsp: {error}");
                ExitCode::from(1)
            }
        };
    }
    match run(args, &mut io::stdout().lock()) {
        Ok(code) => ExitCode::from(code),
        Err((code, message)) => {
            let _ = writeln!(io::stderr().lock(), "{message}");
            ExitCode::from(code)
        }
    }
}
