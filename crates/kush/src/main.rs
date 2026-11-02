use kush::{Diagnostic, Span, ast::ItemKind};
use std::{
    env,
    ffi::OsString,
    fs,
    io::{self, Write},
    path::Path,
    process::{Command, ExitCode},
};
const HELP: &str = "Kush 0.1.0\n\nUsage:\n  kush parse <file.kush> [--ast]\n  kush lex <file.kush>\n  kush resolve <file.kush>\n  kush check <file.kush>\n  kush build <file.kush> -o <executable> [--stats]\n  kush run <file.kush> [--stats]\n  kush eval <file.kush> [--stats]\n  kush --help\n  kush --version\n\nBuild/run use Cranelift on Linux x86-64 and require cc. Eval is the bounded reference interpreter.\nCheck accepts mixed programs: total logical definitions are kernel-checked and erased before executable checking.\n--stats writes one 'allocation-stats:' line to stderr; program stdout and exit status are unchanged.\n";
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
    let known = ["parse", "lex", "resolve", "check", "build", "run", "eval"]
        .iter()
        .any(|name| command == name);
    let ast = command == "parse" && args.len() == 3 && args[2] == "--ast";
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
                    build = false;
                    break;
                }
            }
            index += 1;
        }
    }
    let run_like = command == "run" || command == "eval";
    let stats = (run_like && args.len() == 3 && args[2] == "--stats")
        || (command == "build" && build_stats);
    let valid = if command == "parse" {
        args.len() == 2 || ast
    } else if command == "build" {
        build
    } else if run_like {
        args.len() == 2 || stats
    } else {
        args.len() == 2
    };
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
            if stats {
                let (result, stats) = checked
                    .evaluate_with_io_and_stats(&mut io::stdin().lock(), out)
                    .map_err(diagnostic)?;
                eprintln!("{}", stats.report());
                return Ok((result as u64 & 255) as u8);
            }
            let result = checked
                .evaluate_with_io(&mut io::stdin().lock(), out)
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
            kush::native::build_with_options(&checked, output, stats, &links)
                .map_err(diagnostic)?;
            writeln!(out, "Built {} with Cranelift.", output.display()).map_err(output_error)?;
        } else {
            let scratch = kush::native::Scratch::new(&env::temp_dir()).map_err(diagnostic)?;
            let binary = scratch.path().join("program");
            kush::native::build_with_stats(&checked, &binary, stats).map_err(diagnostic)?;
            let status = Command::new(&binary)
                .status()
                .map_err(|e| (1, format!("cannot execute program: {e}")))?;
            return match status.code() {
                Some(code) => Ok(code as u8),
                None => Err((
                    1,
                    "native program aborted or was terminated by a signal".into(),
                )),
            };
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
    match run(env::args_os().skip(1).collect(), &mut io::stdout().lock()) {
        Ok(code) => ExitCode::from(code),
        Err((code, message)) => {
            let _ = writeln!(io::stderr().lock(), "{message}");
            ExitCode::from(code)
        }
    }
}
