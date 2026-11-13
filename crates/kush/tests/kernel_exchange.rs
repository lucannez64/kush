//! KIK-EXCHANGE: the kernel exchange format round-trips the example corpus,
//! `answer` replays it with the Rust kernel, and malformed input fails
//! cleanly. See docs/kernel-exchange.md.
use kush::exchange::{self, Item};
use kush::kernel::Term;
use std::process::Command;

const CORPUS: &[(&str, &str)] = &[
    ("proofs", include_str!("../../../examples/proofs.kush")),
    (
        "induction",
        include_str!("../../../examples/induction.kush"),
    ),
    (
        "logical-data",
        include_str!("../../../examples/logical-data.kush"),
    ),
    (
        "finite-proofs",
        include_str!("../../../examples/finite-proofs.kush"),
    ),
    (
        "large-naturals",
        include_str!("../../../examples/large-naturals.kush"),
    ),
    (
        "universes",
        include_str!("../../../examples/universes.kush"),
    ),
    (
        "logical-lambdas",
        include_str!("../../../examples/logical-lambdas.kush"),
    ),
];

fn module(source: &str) -> kush::check::CheckedModule {
    kush::check(source)
        .or_else(|_| kush::executable::logical_module(source))
        .unwrap()
}

fn print(item: &Item) -> String {
    match item {
        Item::Def {
            name,
            levels,
            ty,
            value,
            steps,
        } => exchange::def_sexp(name, *levels, ty, value, *steps).to_string(),
        Item::Data { spec, steps } => exchange::data_sexp(spec, *steps).to_string(),
        Item::Check { term, ty } => format!(
            "(check {} {})",
            exchange::term_sexp(term),
            exchange::term_sexp(ty)
        ),
        Item::Infer(term) => format!("(infer {})", exchange::term_sexp(term)),
        Item::Normalize(term) => format!("(normalize {})", exchange::term_sexp(term)),
    }
}

#[test]
fn the_corpus_round_trips_and_replays() {
    for (name, source) in CORPUS {
        let checked = module(source);
        let dump = exchange::dump(&checked);
        let items = exchange::parse(&dump).unwrap_or_else(|e| panic!("{name}: {e}"));
        // Printing is the identity on a dump: one canonical line per item.
        let reprinted: String = items.iter().map(|item| print(item) + "\n").collect();
        assert_eq!(reprinted, dump, "{name}");
        // The Rust kernel admits every declaration from text and computes the
        // same normal forms as the kernel that checked the source.
        let answer = exchange::answer(&dump).unwrap();
        let lines: Vec<&str> = answer.lines().collect();
        assert_eq!(lines.len(), items.len(), "{name}");
        for (item, line) in items.iter().zip(&lines) {
            match item {
                Item::Def { name: def, .. } => assert_eq!(*line, format!("ok {def}")),
                Item::Data { spec, .. } => assert_eq!(*line, format!("ok {}", spec.name)),
                Item::Normalize(term) => {
                    let normal = checked.kernel.normalize_closed(term).unwrap();
                    assert_eq!(*line, format!("= {}", exchange::term_sexp(&normal)));
                }
                other => panic!("unexpected item in a dump: {other:?}"),
            }
        }
    }
}

#[test]
fn answers_report_rejections_budgets_and_queries() {
    let text = "
        ; comments and blank lines are ignored
        (def two 0 nat (succ (succ zero)))
        (def bad 0 nat (sort 0))
        (normalize (global two))
        (normalize (global bad))
        (check (refl nat (global two)) (eq nat (global two) (lit 2)))
        (check (refl nat (global two)) (eq nat (global two) (lit 3)))
        (infer (lam (sort 0) (lam (var 0) (var 0))))
        (normalize (natelim (lam nat nat) zero (lam nat (lam nat (succ (var 0)))) (lit 1000000)))
        (def id 1 (pi (sort (u 0)) (pi (var 0) (var 1))) (lam (sort (u 0)) (lam (var 0) (var 0))))
        (infer (global id (succ (u 0))))
        (infer (global id (max 1 2)))
        (data Two 0 prop () (ctor First () () ()) (ctor Second () () ()))
        (check (global Second) (global Two))
    ";
    let answer = exchange::answer(text).unwrap();
    assert_eq!(
        answer,
        "ok two\n\
         reject bad\n\
         = (lit 2)\n\
         reject\n\
         ok\n\
         reject\n\
         : (pi (sort 0) (pi (var 0) (var 1)))\n\
         budget\n\
         ok id\n\
         reject\n\
         : (pi (sort 2) (pi (var 0) (var 1)))\n\
         ok Two\n\
         ok\n"
    );
}

#[test]
fn levels_print_canonically() {
    for (text, printed) in [
        ("(sort (max (u 0) (succ (u 0))))", "(sort (succ (u 0)))"),
        ("(sort (max 1 (succ (u 0))))", "(sort (succ (u 0)))"),
        ("(sort (max (u 1) 1 (u 0)))", "(sort (max 1 (u 0) (u 1)))"),
        ("(sort (succ 4))", "(sort 5)"),
        ("(lit 0)", "zero"),
        ("(lit 000123)", "(lit 123)"),
    ] {
        let sexp = &exchange::read(text).unwrap()[0];
        let term: Term = exchange::parse_term(sexp).unwrap();
        assert_eq!(exchange::term_sexp(&term).to_string(), printed);
    }
}

#[test]
fn malformed_input_is_an_error_not_a_verdict() {
    for (text, expected) in [
        ("(def x 0 nat zero", "unclosed"),
        ("(def x 0 nat zero))", "unexpected ')'"),
        ("(def x 0 nat)", "takes 4 arguments"),
        ("(normalize (frob))", "unknown term form"),
        ("(normalize nope)", "unknown term atom"),
        ("(normalize (var -1))", "de Bruijn index"),
        ("(normalize (lit 12a))", "decimal"),
        ("(normalize (sort (u)))", "takes 1 arguments"),
        ("(data D 0 maybe ())", "type or prop"),
        ("(data D 0 type () (oops))", "ctor"),
        ("frob", "expected a declaration or query"),
        ("(launch)", "unknown item"),
    ] {
        let error = exchange::answer(text).unwrap_err().to_string();
        assert!(error.contains(expected), "{text}: {error}");
    }
    let deep = "(normalize ".repeat(2000) + &")".repeat(2000);
    assert!(exchange::answer(&deep).unwrap_err().0.contains("deeply"));
}

#[test]
fn the_cli_dumps_and_answers() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let dump = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("core")
        .arg(root.join("examples/logical-data.kush"))
        .output()
        .unwrap();
    assert!(
        dump.status.success(),
        "{}",
        String::from_utf8_lossy(&dump.stderr)
    );
    let scratch = std::env::temp_dir().join(format!("kush-exchange-{}.kcore", std::process::id()));
    std::fs::write(&scratch, &dump.stdout).unwrap();
    let answer = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("kernel")
        .arg(&scratch)
        .output()
        .unwrap();
    std::fs::remove_file(&scratch).ok();
    assert!(answer.status.success());
    let text = String::from_utf8(answer.stdout).unwrap();
    assert!(
        text.lines()
            .all(|line| line.starts_with("ok ") || line.starts_with("= "))
    );
    assert!(text.contains("ok Even"));
    // Usage errors and unreadable files fail with a nonzero status.
    for args in [vec!["core"], vec!["kernel", "/nonexistent.kcore"]] {
        let output = Command::new(env!("CARGO_BIN_EXE_kush"))
            .args(&args)
            .output()
            .unwrap();
        assert!(!output.status.success(), "{args:?}");
    }
}
