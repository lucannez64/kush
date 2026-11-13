//! The kernel written in Kush (`examples/kernel`, docs/kernel-in-kush.md):
//! its package tests pass, it reads and prints back every exchange file the
//! Rust side dumps from the example corpus byte for byte, and its normal
//! forms agree with the Rust kernel's.
use std::{path::PathBuf, process::Command};

const CORPUS: &[&str] = &[
    "proofs",
    "induction",
    "logical-data",
    "finite-proofs",
    "large-naturals",
    "universes",
    "logical-lambdas",
];

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn kush() -> Command {
    Command::new(env!("CARGO_BIN_EXE_kush"))
}

fn scratch(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush-kik-{label}-{}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

#[test]
fn the_package_tests_pass() {
    let output = kush()
        .arg("test")
        .arg("--manifest-path")
        .arg(root().join("examples/kernel/Kush.toml"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("0 failed"), "{stdout}");
}

fn build(dir: &std::path::Path) -> PathBuf {
    let binary = dir.join("kernel");
    let build = kush()
        .arg("build")
        .arg("--manifest-path")
        .arg(root().join("examples/kernel/Kush.toml"))
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        build.status.success(),
        "{}",
        String::from_utf8_lossy(&build.stderr)
    );
    binary
}

fn dump(name: &str) -> String {
    let source = std::fs::read_to_string(root().join(format!("examples/{name}.kush"))).unwrap();
    let checked = kush::check(&source)
        .or_else(|_| kush::executable::logical_module(&source))
        .unwrap();
    kush::exchange::dump(&checked)
}

/// Compare the Kush kernel's `normalize` answers with the Rust kernel's.
/// Lines agree exactly, except that a budget exhaustion on either side is
/// inconclusive (the two kernels charge different steps). Returns the number
/// of conclusive normal forms compared.
fn agree_on_normal_forms(binary: &std::path::Path, file: &std::path::Path, text: &str) -> usize {
    std::fs::write(file, text).unwrap();
    let rust = kush::exchange::answer(text).unwrap();
    let output = Command::new(binary)
        .arg("normalize")
        .arg(file)
        .output()
        .unwrap();
    assert!(output.status.success());
    let kush_answer = String::from_utf8(output.stdout).unwrap();
    let rust_lines: Vec<&str> = rust.lines().collect();
    let kush_lines: Vec<&str> = kush_answer.lines().collect();
    assert_eq!(rust_lines.len(), kush_lines.len(), "{kush_answer}");
    let mut compared = 0;
    for (rust_line, kush_line) in rust_lines.iter().zip(&kush_lines) {
        if *rust_line == "budget" || *kush_line == "budget" {
            continue;
        }
        assert_eq!(rust_line, kush_line, "in {}", file.display());
        compared += 1;
    }
    compared
}

#[test]
fn normal_forms_agree_with_the_rust_kernel() {
    let dir = scratch("normal");
    let binary = build(&dir);
    for name in CORPUS {
        let file = dir.join(format!("{name}.kcore"));
        let text = dump(name);
        let compared = agree_on_normal_forms(&binary, &file, &text);
        assert_eq!(
            compared,
            text.lines().count(),
            "{name}: no item may be inconclusive"
        );
    }
    // Targeted reductions, each a normalize query.
    let cases = "
        (def two 0 nat (succ (succ zero)))
        (def id 1 (pi (sort (u 0)) (pi (var 0) (var 1))) (lam (sort (u 0)) (lam (var 0) (var 0))))
        (data Even 0 type () (ctor E0 () () ()) (ctor ES () ((global Even)) ()))
        (normalize (succ (lit 999999999)))
        (normalize (succ (succ (global two))))
        (normalize (lam nat (succ (var 0))))
        (normalize (lam nat (app (lam nat (lam nat (var 1))) (var 0))))
        (normalize (app (app (global id 1) (sort 0)) nat))
        (normalize (natelim (lam nat nat) zero (lam nat (lam nat (var 1))) (lit 100000000000000000000)))
        (normalize (natelim (lam nat nat) (lit 3) (lam nat (lam nat (succ (var 0)))) (lit 40)))
        (normalize (natelim (lam nat nat) zero (lam nat (lam nat (succ (var 0)))) (lit 1000000)))
        (normalize (lam nat (natelim (lam nat nat) zero (lam nat (lam nat (var 0))) (var 0))))
        (normalize (transport nat zero zero (lam nat nat) (refl nat zero) (lit 5)))
        (normalize (lam (eq nat zero zero) (transport nat zero zero (lam nat nat) (var 0) (lit 5))))
        (normalize (eqelim nat zero zero (lam nat (lam (eq nat zero (var 0)) nat)) (lit 9) (refl nat zero)))
        (normalize (indelim Even (lam (global Even) nat) (zero (lam (global Even) (lam nat (succ (succ (var 0)))))) (app (global ES) (app (global ES) (global E0)))))
        (normalize (lam (global Even) (indelim Even (lam (global Even) nat) (zero (lam (global Even) (lam nat (var 0)))) (var 0))))
    ";
    let file = dir.join("cases.kcore");
    assert!(agree_on_normal_forms(&binary, &file, cases) >= 15);
    std::fs::remove_dir_all(&dir).ok();
}

/// Compare `kernel check` (Kush) with `kush kernel` (Rust) line by line.
/// A budget exhaustion on either side is inconclusive. Returns the number of
/// lines compared.
fn agree_on_answers(binary: &std::path::Path, file: &std::path::Path, text: &str) -> usize {
    std::fs::write(file, text).unwrap();
    let rust = kush::exchange::answer(text).unwrap();
    let output = Command::new(binary)
        .arg("check")
        .arg(file)
        .output()
        .unwrap();
    assert!(output.status.success());
    let kush_answer = String::from_utf8(output.stdout).unwrap();
    let rust_lines: Vec<&str> = rust.lines().collect();
    let kush_lines: Vec<&str> = kush_answer.lines().collect();
    assert_eq!(rust_lines.len(), kush_lines.len(), "{kush_answer}");
    let mut compared = 0;
    for (index, (rust_line, kush_line)) in rust_lines.iter().zip(&kush_lines).enumerate() {
        if rust_line.starts_with("budget") || kush_line.starts_with("budget") {
            continue;
        }
        assert_eq!(
            rust_line,
            kush_line,
            "item {} of {}",
            index + 1,
            file.display()
        );
        compared += 1;
    }
    compared
}

/// Typing cases without data families, mostly rejections: the corpus only
/// exercises acceptance.
const TYPING: &str = "
    (def two 0 nat (succ (succ zero)))
    (def bad 0 nat (sort 0))
    (def two 0 nat zero)
    (check (refl nat (global two)) (eq nat (global two) (lit 2)))
    (check (refl nat (global two)) (eq nat (global two) (lit 3)))
    (check (refl nat (lit 3)) (eq nat (succ (succ (succ zero))) (lit 3)))
    (check (sort 0) (sort 0))
    (check nat (sort 1))
    (check prop (sort 0))
    (check prop prop)
    (infer (pi nat prop))
    (infer (pi prop (var 0)))
    (infer (pi (sort 0) (var 0)))
    (infer (pi (sort 3) (sort 1)))
    (infer (lam (sort 0) (lam (var 0) (var 0))))
    (infer (var 0))
    (infer (app zero zero))
    (infer (lam zero zero))
    (infer (succ (sort 0)))
    (check (lam prop (lam (var 0) (lam (var 1) (refl (var 2) (var 1)))))
           (pi prop (pi (var 0) (pi (var 1) (eq (var 2) (var 1) (var 0))))))
    (check (lam nat (lam nat (refl nat (var 1))))
           (pi nat (pi nat (eq nat (var 1) (var 0)))))
    (check (lam (pi nat nat) (refl (pi nat nat) (var 0)))
           (pi (pi nat nat) (eq (pi nat nat) (lam nat (app (var 1) (var 0))) (var 0))))
    (check (lam (pi nat nat) (refl (pi nat nat) (var 0)))
           (pi (pi nat nat) (eq (pi nat nat) (lam nat (app (var 1) (succ (var 0)))) (var 0))))
    (infer (eqelim nat zero zero (lam nat (lam (eq nat zero (var 0)) nat)) (lit 9) (refl nat zero)))
    (infer (eqelim nat zero zero (lam nat nat) (lit 9) (refl nat zero)))
    (infer (eqelim nat zero (lit 1) (lam nat (lam (eq nat zero (var 0)) nat)) (lit 9) (refl nat zero)))
    (infer (eqelim nat zero zero (lam nat (lam (eq nat (var 0) (var 0)) nat)) (lit 9) (refl nat zero)))
    (infer (transport nat zero zero (lam nat nat) (refl nat zero) (lit 5)))
    (infer (transport nat zero (lit 1) (lam nat nat) (refl nat zero) (lit 5)))
    (infer (transport nat zero zero (lam nat zero) (refl nat zero) (lit 5)))
    (infer (natelim (lam nat nat) zero (lam nat (lam nat (succ (var 0)))) (lit 3)))
    (infer (natelim (lam nat nat) zero (lam nat (succ (var 0))) (lit 3)))
    (infer (natelim (lam nat nat) (sort 0) (lam nat (lam nat (succ (var 0)))) (lit 3)))
    (normalize (natelim (lam nat nat) zero (lam nat (lam nat (succ (var 0)))) (lit 30)))
    (normalize (natelim (lam nat nat) zero (lam nat (lam nat (succ (var 0)))) (lit 1000000)))
    (def id 1 (pi (sort (u 0)) (pi (var 0) (var 1))) (lam (sort (u 0)) (lam (var 0) (var 0))))
    (infer (global id 1))
    (infer (global id))
    (infer (global id (u 0)))
    (infer (app (app (global id 0) (sort 0)) nat))
    (def lifted 0 (sort 1) (sort (u 0)))
    (def poly 2 (sort (succ (max (u 0) (u 1)))) (pi (sort (u 0)) (sort (u 1))))
    (def poly_bad 2 (sort (succ (u 0))) (pi (sort (u 0)) (sort (u 1))))
    (infer (i64 5))
    (check (bool true) (scalar i64))
    (infer (eq (scalar Bool) (bool true) (bool false)))
    (check (refl (scalar Unit) unit) (eq (scalar Unit) unit unit))
    (infer (global missing))
";

/// Data family cases: admission (positivity, universes, Prop) and
/// elimination (motives, branches, large elimination, proof irrelevance).
const DATA: &str = "
    (data Even 0 type () (ctor E0 () () ()) (ctor ES () ((global Even)) ()))
    (data Negative 0 type () (ctor B () ((pi (global Negative) nat)) ()))
    (data Nested 0 type () (ctor N () ((app (lam (sort 0) (var 0)) (global Nested))) ()))
    (data Big 0 type () (ctor Wrap () ((sort 0)) ()))
    (infer (global Big))
    (infer (global Wrap))
    (data Two 0 prop () (ctor First () () ()) (ctor Second () () ()))
    (check (refl (global Two) (global First)) (eq (global Two) (global First) (global Second)))
    (check (refl (global Even) (global E0)) (eq (global Even) (global E0) (app (global ES) (global E0))))
    (infer (indelim Two (lam (global Two) nat) (zero (lit 1)) (global First)))
    (infer (indelim Two (lam (global Two) (global Two)) ((global First) (global First)) (global Second)))
    (data Boxed 0 prop () (ctor Box () ((sort 0)) ()))
    (data Fin 0 type (nat)
      (ctor FZ (nat) () ((succ (var 0))))
      (ctor FS (nat) ((app (global Fin) (var 0))) ((succ (var 1)))))
    (infer (app (app (app (global FS) (lit 2)) (lit 1)) (app (app (global FZ) (lit 1)) zero)))
    (infer (indelim Fin (lam nat (lam (app (global Fin) (var 0)) nat))
      ((lam nat (lam nat zero)) (lam nat (lam nat (lam (app (global Fin) (var 0)) (lam nat (succ (var 0)))))))
      (app (app (app (global FS) (lit 2)) (lit 1)) (app (app (global FZ) (lit 1)) zero))))
    (normalize (indelim Fin (lam nat (lam (app (global Fin) (var 0)) nat))
      ((lam nat (lam nat zero)) (lam nat (lam nat (lam (app (global Fin) (var 0)) (lam nat (succ (var 0)))))))
      (app (app (app (global FS) (lit 2)) (lit 1)) (app (app (global FZ) (lit 1)) zero))))
    (infer (indelim Fin (lam nat (lam (app (global Fin) (var 0)) nat))
      ((lam nat (lam nat zero)))
      (app (app (global FZ) (lit 1)) zero)))
    (infer (indelim Fin (lam nat (lam (app (global Fin) (var 0)) nat))
      ((lam nat (lam nat zero)) (lam nat (lam nat (lam (app (global Fin) (var 0)) (lam nat (var 1))))))
      (app (app (global FZ) (lit 1)) zero)))
    (infer (indelim Fin (lam (app (global Fin) zero) nat)
      ((lam nat (lam nat zero)) (lam nat (lam nat (lam (app (global Fin) (var 0)) (lam nat (succ (var 0)))))))
      (app (app (global FZ) (lit 1)) zero)))
    (infer (indelim Even (lam (global Even) nat) (zero (lam (global Even) (lam nat (succ (var 0))))) (lit 3)))
    (data Dup 0 type () (ctor D () () ()) (ctor D () () ()))
    (data Clash 0 type () (ctor E0 () () ()))
    (data Arity 0 type (nat) (ctor A () () ()))
    (data List 1 type ((sort (u 0)))
      (ctor nil () () ((var 0)))
      (ctor cons () ((var 0) (app (global List (u 0)) (var 1))) ((var 2))))
    (infer (app (global List 1) (sort 0)))
    (infer (app (app (app (global cons 1) (sort 0)) nat) (app (global nil 1) (sort 0))))
    (data Uneven 1 type ((sort (u 0)))
      (ctor nil2 () () ((var 0)))
      (ctor cons2 () ((var 0) (app (global Uneven 0) (var 1))) ((var 2))))
    (data Even 0 type () (ctor Other () () ()))
    (infer (global Negative))
";

#[test]
fn the_checker_agrees_with_the_rust_kernel() {
    let dir = scratch("check");
    let binary = build(&dir);
    // The whole corpus, every item compared.
    for name in CORPUS {
        let file = dir.join(format!("{name}.kcore"));
        let text = dump(name);
        assert_eq!(
            agree_on_answers(&binary, &file, &text),
            text.lines().count(),
            "{name}"
        );
    }
    let file = dir.join("typing.kcore");
    let compared = agree_on_answers(&binary, &file, TYPING);
    assert!(compared >= 45, "{compared}");
    let file = dir.join("data.kcore");
    let compared = agree_on_answers(&binary, &file, DATA);
    assert_eq!(compared, 29, "{compared}");
    assert!(
        kush::exchange::answer(DATA)
            .unwrap()
            .matches("reject")
            .count()
            >= 12
    );
    // The cases really include rejections.
    assert!(
        kush::exchange::answer(TYPING)
            .unwrap()
            .matches("reject")
            .count()
            >= 20
    );
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn the_kush_kernel_prints_the_corpus_back_unchanged() {
    let dir = scratch("print");
    let binary = build(&dir);
    for name in CORPUS {
        let dump = dump(name);
        let file = dir.join(format!("{name}.kcore"));
        std::fs::write(&file, &dump).unwrap();
        let output = Command::new(&binary)
            .arg("print")
            .arg(&file)
            .output()
            .unwrap();
        assert!(output.status.success(), "{name}");
        assert_eq!(String::from_utf8(output.stdout).unwrap(), dump, "{name}");
    }
    // Malformed input is reported with its byte offset and a nonzero status.
    let bad = dir.join("bad.kcore");
    std::fs::write(&bad, "(def x 0 nat zero)\n(launch)\n").unwrap();
    let output = Command::new(&binary)
        .arg("print")
        .arg(&bad)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("at byte 20"));
    std::fs::remove_dir_all(&dir).ok();
}
