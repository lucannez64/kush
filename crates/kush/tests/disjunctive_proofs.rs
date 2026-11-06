//! PROVE-DISJ: `||`, `!=` and `!( .. )` in erased propositions and in branch
//! facts. Disjunctive facts are clauses; an obligation is proved by bounded
//! case splitting, and every split is re-checked by the certificate verifier,
//! which negates the goal formula itself.
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("disjunctive-proofs");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{source}"
        );
    }
}

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

#[test]
fn disjunctions_are_hypotheses_and_goals() {
    agrees(
        "fn outside(x: i64, erased p: { x <= 0 || x >= 10 }) -> i64 ! {} { 1 }
         fn from_branch(x: i64) -> i64 ! {} { if x < 0 || x > 20 { outside(x, _) } else { 0 } }
         fn not_five(x: i64, erased p: { x != 5 }) -> i64 ! {} { 2 }
         fn from_ne(x: i64) -> i64 ! {} { if x != 5 { not_five(x, _) } else { 0 } }
         fn from_else(x: i64) -> i64 ! {} { if x == 5 { 0 } else { not_five(x, _) } }
         fn large(x: i64, erased p: { x >= 10 }) -> i64 ! {} { 3 }
         fn use_clause(x: i64, erased p: { x <= 0 || x >= 10 }) -> i64 ! {} {
             if x >= 1 { large(x, _) } else { 0 }
         }
         fn not_both(a: Bool, b: Bool, erased p: { !(a && b) }) -> i64 ! {} { 4 }
         fn from_not(a: Bool, b: Bool) -> i64 ! {} { if !a { not_both(a, b, _) } else { 0 } }
         fn absurd(erased q: { 0 >= 1 }) -> i64 ! {} { 0 }
         fn all_cases(a: Bool, b: Bool, erased p: { a || b }, erased q: { !a }, erased r: { !b }) -> i64 ! {} {
             absurd(_)
         }
         fn main() -> i64 ! {panic} {
             from_branch(30) + from_ne(4) + from_else(6) + use_clause(12, _) + from_not(false, true)
         }",
        12,
    );
}

#[test]
fn unproved_disjunctions_are_rejected() {
    rejects(
        "fn outside(x: i64, erased p: { x <= 0 || x >= 10 }) -> i64 ! {} { 1 }
         fn f(x: i64) -> i64 ! {} { if x < 0 || x > 5 { outside(x, _) } else { 0 } }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'x <= 0 || x >= 10'",
    );
    rejects(
        "fn not_five(x: i64, erased p: { x != 5 }) -> i64 ! {} { 2 }
         fn f(x: i64) -> i64 ! {} { if x >= 5 { not_five(x, _) } else { 0 } }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'x != 5'",
    );
    rejects(
        "fn not_both(a: Bool, b: Bool, erased p: { !(a && b) }) -> i64 ! {} { 4 }
         fn f(a: Bool, b: Bool) -> i64 ! {} { if a || b { not_both(a, b, _) } else { 0 } }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove '!(a && b)'",
    );
    // A formula with too many cases is reported, never truncated.
    rejects(
        "fn wide(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64,
                 erased p: { (a == 0 || a == 1) && (b == 0 || b == 1) && (c == 0 || c == 1)
                             && (d == 0 || d == 1) && (e == 0 || e == 1) && (f == 0 || f == 1) }) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "more than 32 cases",
    );
}
