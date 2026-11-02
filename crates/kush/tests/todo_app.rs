//! Persistent multi-file todo CLI built on the checked filesystem, argument,
//! and environment APIs. The project-shaped source tree (`Kush.toml`,
//! `src/main.kush`, sibling modules) is loaded with an equivalent module index
//! so the same files can be used by the project workflow after merge.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::{
    Host,
    executable::{self, Executable},
    program::{self, ModuleSource},
};
use std::{
    fs, io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/todo-cli")
}

struct ProjectSource {
    src: PathBuf,
}

impl ModuleSource for ProjectSource {
    fn find(&self, path: &[String]) -> Option<(String, String)> {
        if path.first().map(String::as_str) != Some("todo_cli") {
            return None;
        }
        let mut file = self.src.clone();
        for part in &path[1..] {
            file.push(part);
        }
        file.set_extension("kush");
        let text = fs::read_to_string(&file).ok()?;
        Some((file.display().to_string(), text))
    }
}

fn checked_app() -> Executable {
    let directory = root();
    let main = fs::read_to_string(directory.join("src/main.kush")).unwrap();
    let source = ProjectSource {
        src: directory.join("src"),
    };
    let program = program::load(
        &directory.join("src/main.kush").display().to_string(),
        &main,
        &source,
    )
    .unwrap();
    executable::check_program(&program)
        .unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

fn directory(label: &str) -> PathBuf {
    let id = NEXT.fetch_add(1, Ordering::Relaxed);
    let path =
        std::env::temp_dir().join(format!("kush-todo-app-{label}-{}-{id}", std::process::id()));
    let _ = fs::remove_dir_all(&path);
    fs::create_dir(&path).unwrap();
    path
}

struct Observation {
    status: i64,
    output: Vec<u8>,
}

fn reference(
    program: &Executable,
    args: &[String],
    environment: &[(String, String)],
) -> Observation {
    let mut argv = vec![b"todo".to_vec()];
    argv.extend(args.iter().map(|argument| argument.as_bytes().to_vec()));
    let host = Host::new(
        argv,
        environment
            .iter()
            .map(|(name, value)| (name.as_bytes().to_vec(), value.as_bytes().to_vec()))
            .collect(),
    );
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &host)
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations);
    Observation { status, output }
}

struct Native {
    binary: PathBuf,
    _scratch: kush::native::Scratch,
}

impl Native {
    fn build(program: &Executable) -> Self {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("todo");
        kush::native::build(program, &binary).unwrap();
        Self {
            binary,
            _scratch: scratch,
        }
    }

    fn run(
        &self,
        args: &[String],
        environment: &[(String, String)],
        current: &Path,
    ) -> Observation {
        let output = Command::new(&self.binary)
            .args(args)
            .env_clear()
            .envs(environment.iter().map(|(name, value)| (name, value)))
            .current_dir(current)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        Observation {
            status: output.status.code().unwrap() as i64,
            output: output.stdout,
        }
    }
}

fn text(observation: &Observation) -> String {
    String::from_utf8(observation.output.clone()).unwrap()
}

fn substitute(template: &[&str], file: &str) -> Vec<String> {
    template
        .iter()
        .map(|part| {
            if *part == "$FILE" {
                file.to_owned()
            } else {
                (*part).to_owned()
            }
        })
        .collect()
}

#[test]
fn project_test_target_parses_even_before_std_test_is_available() {
    // The project test workflow supplies `std.test`; this checkout does not.
    // Parsing still validates the project-shaped test file and its attributes.
    let source = fs::read_to_string(root().join("tests/main.kush")).unwrap();
    kush::parse(&source).unwrap();
}

#[test]
fn persistent_cli_reloads_invalidates_and_reports_usage() {
    let program = checked_app();
    let reference_directory = directory("reference");
    let native_directory = directory("native");
    let native = Native::build(&program);

    let reference_file = reference_directory.join("tasks.txt");
    let native_file = native_directory.join("tasks.txt");
    let reference_path = reference_file.display().to_string();
    let native_path = native_file.display().to_string();

    let templates: Vec<Vec<&str>> = vec![
        vec!["--file"],
        vec!["--file", "$FILE", "list"],
        vec!["--file", "$FILE", "add", "Buy", "milk"],
        vec!["--file", "$FILE", "add", "Ship", "code"],
        vec!["--file", "$FILE", "list"],
        vec!["--file", "$FILE", "done", "1"],
        vec!["--file", "$FILE", "list"],
        vec!["--file", "$FILE", "remove", "2"],
        vec!["--file", "$FILE", "list"],
        vec!["--file", "$FILE", "add"],
        vec!["--file", "$FILE", "done", "99"],
        vec!["--file", "$FILE", "unknown"],
        vec!["--help"],
    ];
    for template in templates {
        let reference_args = substitute(&template, &reference_path);
        let native_args = substitute(&template, &native_path);
        let expected = reference(&program, &reference_args, &[]);
        let actual = native.run(&native_args, &[], &native_directory);
        assert_eq!(
            actual.status,
            expected.status,
            "status mismatch for {template:?}: {}",
            text(&actual)
        );
        assert_eq!(
            actual.output,
            expected.output,
            "output mismatch for {template:?}\nreference: {}\nnative: {}",
            text(&expected),
            text(&actual)
        );
    }
    // Both backends persisted the same content across separate processes.
    assert_eq!(fs::read_to_string(&reference_file).unwrap(), "1|Buy milk\n");
    assert_eq!(fs::read_to_string(&native_file).unwrap(), "1|Buy milk\n");
    assert!(!reference_directory.join("tasks.txt.tmp").exists());
    assert!(!native_directory.join("tasks.txt.tmp").exists());

    // Malformed files are rejected without a rewrite and with status 2.
    for bad in [b"bad\n".as_slice(), b"0|bad\r\n".as_slice()] {
        fs::write(&reference_file, bad).unwrap();
        fs::write(&native_file, bad).unwrap();
        let reference_args = substitute(&["--file", "$FILE", "list"], &reference_path);
        let native_args = substitute(&["--file", "$FILE", "list"], &native_path);
        let expected = reference(&program, &reference_args, &[]);
        let actual = native.run(&native_args, &[], &native_directory);
        assert_eq!(actual.status, 2);
        assert_eq!(actual.output, expected.output);
        assert_eq!(fs::read(&reference_file).unwrap(), bad);
        assert_eq!(fs::read(&native_file).unwrap(), bad);
    }

    // Appending to a valid final line without a newline inserts one separator.
    fs::write(&reference_file, b"0|Existing").unwrap();
    fs::write(&native_file, b"0|Existing").unwrap();
    let reference_args = substitute(&["--file", "$FILE", "add", "New"], &reference_path);
    let native_args = substitute(&["--file", "$FILE", "add", "New"], &native_path);
    let expected = reference(&program, &reference_args, &[]);
    let actual = native.run(&native_args, &[], &native_directory);
    assert_eq!(actual.status, expected.status);
    assert_eq!(actual.output, expected.output);
    assert_eq!(
        fs::read_to_string(&reference_file).unwrap(),
        "0|Existing\n0|New\n"
    );
    assert_eq!(
        fs::read_to_string(&native_file).unwrap(),
        "0|Existing\n0|New\n"
    );

    // `KUSH_TODO_FILE` supplies the default path when no --file is present.
    fs::write(&reference_file, b"0|From environment\n").unwrap();
    fs::write(&native_file, b"0|From environment\n").unwrap();
    let expected_environment = vec![(
        "KUSH_TODO_FILE".to_owned(),
        reference_file.display().to_string(),
    )];
    let actual_environment = vec![(
        "KUSH_TODO_FILE".to_owned(),
        native_file.display().to_string(),
    )];
    let expected = reference(&program, &["list".to_owned()], &expected_environment);
    let actual = native.run(&["list".to_owned()], &actual_environment, &native_directory);
    assert_eq!(actual.status, expected.status);
    assert_eq!(actual.output, expected.output);
    assert!(text(&expected).contains("From environment"));

    let _ = fs::remove_dir_all(&reference_directory);
    let _ = fs::remove_dir_all(&native_directory);
}
