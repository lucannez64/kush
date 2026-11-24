//! LANG-IMPORT-ALIAS: `use path as name` renames an imported module or item,
//! so two modules with the same last segment can both be imported.

fn project(main: &str) -> std::path::PathBuf {
    let root = std::env::temp_dir().join(format!(
        "kush-import-alias-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(root.join("demo")).unwrap();
    std::fs::write(
        root.join("demo").join("env.kush"),
        "module demo.env;
         pub enum Color { Red, Green(i64) }
         pub fn value() -> i64 ! {} { 40 }
         pub fn tint(c: Color) -> i64 ! {} { match c { Color.Red => 1, Color.Green(n) => n } }
        ",
    )
    .unwrap();
    std::fs::write(root.join("main.kush"), main).unwrap();
    root
}

fn check(main: &str) -> Result<kush::executable::Executable, String> {
    let root = project(main);
    let result = kush::program::load_path(&root.join("main.kush"))
        .map_err(|(_, error)| error.message)
        .and_then(|loaded| kush::executable::check_program(&loaded).map_err(|e| e.message));
    let _ = std::fs::remove_dir_all(&root);
    result
}

fn run(main: &str) -> i64 {
    let program = check(main).unwrap_or_else(|error| panic!("{error}\n{main}"));
    let mut output = Vec::new();
    let (value, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("import-alias");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(native.status.code(), Some((value as u64 & 255) as i32));
    }
    value
}

#[test]
fn modules_with_the_same_last_segment_import_under_new_names() {
    assert_eq!(
        run("use std.env as host_env;
             use demo.env;
             fn main() -> i64 ! {} { env.value() + 2 }"),
        42
    );
    assert_eq!(
        run("use demo.env as settings;
             fn main() -> i64 ! {} { settings.value() + 1 }"),
        41
    );
}

#[test]
fn items_and_enums_import_under_new_names() {
    assert_eq!(
        run("use demo.env.value as answer;
             fn main() -> i64 ! {} { answer() + 2 }"),
        42
    );
    // A renamed enum brings its constructors under the new name.
    assert_eq!(
        run("use demo.env.Color as Shade;
             use demo.env.tint;
             fn main() -> i64 ! {} { tint(Shade.Green(40)) + tint(Shade.Red) + 1 }"),
        42
    );
}

#[test]
fn the_new_name_must_be_free() {
    for (main, fragment) in [
        (
            "use std.env;
             use demo.env;
             fn main() -> i64 ! {} { 0 }",
            "import 'env' conflicts with another declaration or import",
        ),
        (
            "use demo.env as answer;
             fn answer() -> i64 ! {} { 0 }
             fn main() -> i64 ! {} { 0 }",
            "import 'answer' conflicts with another declaration or import",
        ),
        (
            "use demo.env.value as;
             fn main() -> i64 ! {} { 0 }",
            "expected",
        ),
    ] {
        let error = check(main)
            .err()
            .unwrap_or_else(|| panic!("accepted:\n{main}"));
        assert!(error.contains(fragment), "{error}\n{main}");
    }
}
