//! KIK-SPEC: the specification of the kernel's syntax
//! (`examples/kernel/spec/scoped.kush`) is checked by the Rust kernel, and
//! the Kush kernel checks the same declarations from their exchange dump.
//! "Kush checks the proofs about its own syntax."
use std::{path::PathBuf, process::Command};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn spec() -> String {
    std::fs::read_to_string(root().join("examples/kernel/spec/scoped.kush")).unwrap()
}

fn kernel_binary(dir: &std::path::Path) -> PathBuf {
    let binary = dir.join("kernel");
    let build = Command::new(env!("CARGO_BIN_EXE_kush"))
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

fn scratch(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("kush-spec-{label}-{}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

/// The declarations of the spec's dump, without the normalize queries (the
/// normal forms of proofs are large and say nothing new).
fn declarations(dump: &str) -> String {
    dump.lines()
        .filter(|line| !line.starts_with("(normalize"))
        .map(|line| format!("{line}\n"))
        .collect()
}

const LEMMAS: &[&str] = &[
    "rename",
    "shift",
    "subst",
    "subst0",
    "map_id",
    "rename_id",
    "under_ext",
    "subst_ext",
    "under_compose",
    "subst_rename",
    "under_var",
    "subst_var",
    "subst0_shift",
    "substituted",
    "moved_out",
    "shifted",
];

#[test]
fn both_kernels_check_the_specification() {
    // The Rust kernel admits every definition: scope preservation of
    // renaming and substitution (their types) and the lemmas.
    let checked = kush::check(&spec()).unwrap_or_else(|error| panic!("{error:?}"));
    for name in LEMMAS {
        assert!(
            checked
                .definitions
                .iter()
                .any(|definition| definition == name),
            "{name}"
        );
    }
    let text = declarations(&kush::exchange::dump(&checked));
    let dir = scratch("check");
    let binary = kernel_binary(&dir);
    let file = dir.join("scoped.kcore");
    std::fs::write(&file, &text).unwrap();
    let output = Command::new(&binary)
        .arg("check")
        .arg(&file)
        .output()
        .unwrap();
    assert!(output.status.success());
    let answers = String::from_utf8(output.stdout).unwrap();
    // The Kush kernel admits the same declarations, in the same order.
    let expected: String = checked
        .definitions
        .iter()
        .map(|name| format!("ok {name}\n"))
        .collect();
    assert_eq!(answers, expected);
    // A false claim is rejected: change the result an example states.
    // The proof proves `Sort 4 = Sort 4` where `subst0 .. = Sort 3` is claimed.
    let wrong = text.replace(
        "(refl (app (global Tm) zero) (app (app (global Tm::Sort) zero) (lit 3)))",
        "(refl (app (global Tm) zero) (app (app (global Tm::Sort) zero) (lit 4)))",
    );
    assert_ne!(wrong, text, "the example's claim is in the dump");
    std::fs::write(&file, &wrong).unwrap();
    let output = Command::new(&binary)
        .arg("check")
        .arg(&file)
        .output()
        .unwrap();
    let answers = String::from_utf8(output.stdout).unwrap();
    assert!(answers.contains("reject substituted"), "{answers}");
    std::fs::remove_dir_all(&dir).ok();
}

/// Full comparison with every normalize query; slow in a debug build (the
/// Rust kernel normalizes the proofs). Run by scripts/kernel-diff.sh.
#[test]
#[ignore = "slow: run with --ignored or scripts/kernel-diff.sh"]
fn both_kernels_agree_on_every_item_of_the_specification() {
    let checked = kush::check(&spec()).unwrap();
    let text = kush::exchange::dump(&checked);
    let rust = kush::exchange::answer(&text).unwrap();
    let dir = scratch("agree");
    let binary = kernel_binary(&dir);
    let file = dir.join("scoped.kcore");
    std::fs::write(&file, &text).unwrap();
    let output = Command::new(&binary)
        .arg("check")
        .arg(&file)
        .output()
        .unwrap();
    let kush_answer = String::from_utf8(output.stdout).unwrap();
    let mut compared = 0;
    for (rust_line, kush_line) in rust.lines().zip(kush_answer.lines()) {
        if rust_line == "budget" || kush_line == "budget" {
            continue;
        }
        assert_eq!(rust_line, kush_line);
        compared += 1;
    }
    assert_eq!(rust.lines().count(), kush_answer.lines().count());
    assert!(compared >= checked.definitions.len());
    std::fs::remove_dir_all(&dir).ok();
}
