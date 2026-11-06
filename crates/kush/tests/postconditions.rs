//! ENSURES: `ensures` postconditions (user-approved syntax, 2026-11-06).
//!
//! `ensures { P }`, `ensures result => { P }`, `ensures !result => { P }` and
//! `ensures Variant(x, ..) => { P }` are proved at every value the function
//! returns (block, `if` and `match` tails and `return`) from the facts there,
//! with independently checked certificates. Callers receive each clause as a
//! fact about the call's result: in `if` branches, `match` arms and `let`
//! bindings. Propositions use parameters, `result`, guard binders, field
//! paths (`p.x`), `value is Variant`, and the PROVE-DISJ connectives.
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("postconditions");
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

const DECIDE: &str = "
enum Decision { Accept(i64), Reject }
fn decide(x: i64, limit: i64) -> Decision ! {}
    ensures Accept(v) => { v == x && x <= limit }
    ensures Reject => { x > limit }
{
    if x <= limit { Decision.Accept(x) } else { Decision.Reject }
}
fn is_accepted(d: Decision) -> Bool ! {}
    ensures result => { d is Accept }
    ensures !result => { d is Reject }
{
    match d { Decision.Accept(_) => true, Decision.Reject => false }
}
fn at_most_ten(v: i64, erased p: { v <= 10 }) -> i64 ! {} { v }
";

#[test]
fn postconditions_are_proved_and_used_by_callers() {
    agrees(
        &format!(
            "{DECIDE}
             fn next(c: i64) -> i64 ! {{panic}} ensures {{ result == c + 1 }} {{ c + 1 }}
             fn positive(x: i64) -> Bool ! {{}}
                 ensures result => {{ x >= 1 }}
                 ensures !result => {{ x <= 0 }}
             {{ x > 0 }}
             fn caller(x: i64) -> i64 ! {{panic}} {{
                 let n = next(x);
                 let d = decide(n, 10);
                 match d {{
                     Decision.Accept(v) => at_most_ten(v, _),
                     Decision.Reject => 0,
                 }}
             }}
             // A negative theorem about a composition, as in hax.
             fn never_over(x: i64) -> Bool ! {{}} ensures {{ !result }} {{
                 if x > 100 {{ is_accepted(decide(x, 50)) }} else {{ false }}
             }}
             fn from_condition(x: i64) -> i64 ! {{}} {{
                 if positive(x) {{ at_most_ten(1 - x + 9, _) }} else {{ 0 }}
             }}
             fn main() -> i64 ! {{panic}} {{
                 caller(4) + (if positive(3) {{ 1 }} else {{ 0 }}) + (if never_over(500) {{ 100 }} else {{ 0 }})
                     + from_condition(1)
             }}"
        ),
        5 + 1 + 9,
    );
}

#[test]
fn record_fields_returns_and_nested_tails() {
    agrees(
        "struct Facts { flag: Bool, low: i64, high: i64 }
         enum Verdict { Inside(i64), Outside }
         fn classify(f: Facts) -> Verdict ! {}
             ensures Inside(v) => { f.flag && f.low <= v && v <= f.high }
             ensures Outside => { !f.flag || f.low > f.high }
         {
             if !f.flag { return Verdict.Outside; }
             if f.low <= f.high {
                 let v = f.low;
                 Verdict.Inside(v)
             } else {
                 Verdict.Outside
             }
         }
         fn width(f: Facts) -> i64 ! {}
             ensures { result >= 0 }
         {
             match classify(f) {
                 Verdict.Inside(v) => { if f.high >= v { 0 } else { 1 } },
                 Verdict.Outside => 0,
             }
         }
         fn main() -> i64 ! {panic} {
             let f = Facts { flag: true, low: 3, high: 7 };
             match classify(f) {
                 Verdict.Inside(v) => v + width(Facts { flag: false, low: 1, high: 0 }),
                 Verdict.Outside => 99,
             }
         }",
        3,
    );
}

#[test]
fn wrong_or_unjustified_postconditions_are_rejected() {
    rejects(
        "fn next(c: i64) -> i64 ! {panic} ensures { result == c + 2 } { c + 1 }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures { result == c + 2 }'",
    );
    rejects(
        &format!(
            "{DECIDE}
             fn strong(x: i64) -> Decision ! {{}} ensures Accept(v) => {{ v <= 5 }} {{
                 if x <= 10 {{ Decision.Accept(x) }} else {{ Decision.Reject }}
             }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "cannot prove 'ensures Accept(v) => { v <= 5 }'",
    );
    rejects(
        "fn b(x: i64) -> Bool ! {} ensures result => { x >= 2 } { x > 0 }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures result => { x >= 2 }'",
    );
    // A caller only gets what the postcondition says...
    rejects(
        &format!(
            "{DECIDE}
             fn c(x: i64) -> i64 ! {{}} {{
                 match decide(x, 20) {{ Decision.Accept(v) => at_most_ten(v, _), Decision.Reject => 0 }}
             }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "cannot prove 'v <= 10'",
    );
    // ...in the arm it guards.
    rejects(
        &format!(
            "{DECIDE}
             fn c(x: i64) -> i64 ! {{}} {{
                 match decide(x, 10) {{ Decision.Reject => at_most_ten(x, _), Decision.Accept(v) => 0 }}
             }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "cannot prove 'v <= 10'",
    );
    rejects(
        &format!(
            "{DECIDE}
             fn c(x: i64) -> Bool ! {{}} ensures {{ !result }} {{ is_accepted(decide(x, 50)) }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "cannot prove 'ensures { !(result) }'",
    );
    // The message keeps the clause's grouping.
    rejects(
        "fn r(a: Bool, b: Bool, c: i64) -> Bool ! {} ensures result => { a && (b || c - (1 - 2) > 0) } { a }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures result => { a && (b || c - (1 - 2) > 0) }'",
    );
    // Every return is checked.
    rejects(
        "fn r(x: i64) -> i64 ! {} ensures { result >= 0 } { if x < 0 { return x; } x }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures { result >= 0 }'",
    );
}

#[test]
fn postconditions_need_a_body_and_explicit_returns() {
    rejects(
        "foreign \"f\" fn f(x: i64) -> i64 ! {io} ensures { result >= 0 };
         fn main() -> i64 ! {} { 0 }",
        "postconditions need an executable body",
    );
    rejects(
        "enum Result<T, E> { Ok(T), Err(E) }
         fn g(r: Result<i64, i64>) -> Result<i64, i64> ! {} ensures { 0 == 0 } {
             let v = r?;
             Result.Ok(v)
         }
         fn main() -> i64 ! {} { 0 }",
        "'?' cannot leave a function with postconditions",
    );
    // A lambda's returns are not the enclosing function's.
    agrees(
        "fn outer(x: i64) -> i64 ! {alloc, panic} ensures { result >= 0 } {
             let f = fn(y: i64) -> i64 ! {} { 0 - 5 };
             let z = f(x);
             if z >= 0 { z } else { 0 }
         }
         fn main() -> i64 ! {alloc, panic} { outer(3) }",
        0,
    );
}

/// Review findings: each program used to be accepted although a false fact
/// reached code that ran (or an overflow check was dropped).
#[test]
fn review_regressions_for_postconditions() {
    // A unit result returned implicitly still proves the postcondition.
    rejects(
        "fn assert_pos(x: i64) -> Unit ! {} ensures { x > 0 } { let y = x; }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures { x > 0 }'",
    );
    rejects(
        "fn assert_pos(x: i64) -> Unit ! {} ensures { x > 0 } { if x > 100 { } }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures { x > 0 }'",
    );
    // A Bool goal is never weakened by dropping an unknown part.
    rejects(
        "fn opaque(y: i64) -> Bool ! {} { y == 3 }
         fn always(x: i64) -> Bool ! {} ensures { result } { true && opaque(x) }
         fn main() -> i64 ! {} { 0 }",
        "cannot be stated",
    );
    rejects(
        "fn opaque(y: i64) -> Bool ! {} { y == 3 }
         fn pos(x: i64) -> Bool ! {} ensures result => { x > 0 } { x > 0 || opaque(x) }
         fn main() -> i64 ! {} { 0 }",
        "cannot be stated",
    );
    // A value replaced in one branch loses the facts of its old value.
    rejects(
        &format!(
            "{DECIDE}
             fn f(c: Bool) -> i64 ! {{}} {{
                 let mut d = decide(3, 10);
                 if c {{ d = Decision.Accept(1000); }}
                 match d {{ Decision.Accept(v) => at_most_ten(v, _), Decision.Reject => 0 }}
             }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "cannot prove 'v <= 10'",
    );
    // Writes through `&mut` (a method receiver, a field place, a reference
    // parameter) and reassignment in a loop invalidate the facts.
    for body in [
        "let mut p = mk(); p.bump(1000); let v = p.x; at_most_ten(v, _)",
        "let mut p = mk(); set(&mut p); let v = p.x; at_most_ten(v, _)",
        "let mut w = W { p: mk() }; set(&mut w.p); let v = w.p.x; at_most_ten(v, _)",
        "let mut p = mk(); let mut i = 0; let mut last = 0;
         while i < 2 { let v = p.x; last = at_most_ten(v, _); p = P { x: 1000, y: 0 }; i = i + 1; }
         last",
    ] {
        rejects(
            &format!(
                "struct P {{ x: i64, y: i64 }}
                 struct W {{ p: P }}
                 impl P {{ fn bump(&mut self, by: i64) -> Unit ! {{panic}} {{ self.x = self.x + by; }} }}
                 fn set(r: &mut P) -> Unit ! {{}} {{ r.x = 1000; }}
                 fn mk() -> P ! {{}} ensures {{ result.x <= 10 }} {{ P {{ x: 1, y: 2 }} }}
                 fn at_most_ten(v: i64, erased p: {{ v <= 10 }}) -> i64 ! {{}} {{ v }}
                 fn f() -> i64 ! {{panic}} {{ {body} }}
                 fn main() -> i64 ! {{}} {{ 0 }}"
            ),
            "cannot prove 'v <= 10'",
        );
    }
    rejects(
        "struct P { x: i64, y: i64 }
         fn at_most_ten(v: i64, erased p: { v <= 10 }) -> i64 ! {} { v }
         fn f(r: &mut P) -> i64 ! {} {
             if r.x > 10 { return 0; }
             r.x = 1000;
             let v = r.x;
             at_most_ten(v, _)
         }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'v <= 10'",
    );
}

/// A call in the right operand of `&&` / `||` (VELA port): its
/// postconditions are kept for the caller, but only under the condition
/// that the operand ran.
#[test]
fn postconditions_of_calls_in_short_circuit_operands() {
    agrees(
        "struct F { a: Bool, b: Bool, c: Bool }
         fn g(f: F) -> Bool ! {}
             ensures result => { f.b }
             ensures !result => { !f.b }
         { f.b }
         fn mid(f: F) -> Bool ! {} ensures result => { f.a && f.b && f.c } { f.a && g(f) && f.c }
         fn alt(f: F) -> Bool ! {} ensures !result => { !f.a && !f.b } { f.a || g(f) }
         fn main() -> i64 ! {panic} {
             let f = F { a: true, b: true, c: false };
             (if mid(f) { 1 } else { 0 }) + (if alt(f) { 2 } else { 0 })
         }",
        2,
    );
    // `never` returns only when x <= 0. After `x >= 5 && never(x)` the caller
    // knows `x < 5 || x <= 0`, not `x <= 0`: the call may not have run.
    rejects(
        "fn never(x: i64) -> Bool ! {} ensures { x <= 0 } {
             if x <= 0 { true } else { never(x) }
         }
         fn at_most_zero(v: i64, erased p: { v <= 0 }) -> i64 ! {} { v }
         fn f(x: i64) -> i64 ! {} { let b = x >= 5 && never(x); at_most_zero(x, _) }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'v <= 0'",
    );
    agrees(
        "fn never(x: i64) -> Bool ! {} ensures { x <= 0 } {
             if x <= 0 { true } else { never(x) }
         }
         fn below_five(v: i64, erased p: { v <= 4 }) -> i64 ! {} { v }
         fn f(x: i64) -> i64 ! {} { let b = x >= 5 && never(x); below_five(x, _) }
         fn main() -> i64 ! {} { f(3) }",
        3,
    );
}

/// `let b = condition` records that `b` is true exactly when the condition
/// holds (VELA port), so later branches on `b` know the condition.
#[test]
fn bool_bindings_remember_their_condition() {
    agrees(
        "fn at_most_ten(v: i64, erased p: { v <= 10 }) -> i64 ! {} { v }
         fn pick(x: i64, f: Bool) -> i64 ! {} {
             let small = x <= 10 && !f;
             if small { at_most_ten(x, _) } else { 0 }
         }
         fn other(x: i64) -> i64 ! {} {
             let big = x > 10;
             if !big { at_most_ten(x, _) } else { 0 }
         }
         fn main() -> i64 ! {panic} { pick(4, false) + other(3) }",
        7,
    );
    // Only the condition's truth value: reassignment or the other branch
    // tells nothing.
    rejects(
        "fn at_most_ten(v: i64, erased p: { v <= 10 }) -> i64 ! {} { v }
         fn f(x: i64) -> i64 ! {} { let small = x <= 10; if small { 0 } else { at_most_ten(x, _) } }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'v <= 10'",
    );
    rejects(
        "fn at_most_ten(v: i64, erased p: { v <= 10 }) -> i64 ! {} { v }
         fn f(x: i64, y: Bool) -> i64 ! {} {
             let mut small = x <= 10;
             small = y;
             if small { at_most_ten(x, _) } else { 0 }
         }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'v <= 10'",
    );
}

/// kush-kv: a decoder with one clause per variant. The case search sets
/// aside clauses the facts already satisfy and closes contradicted cases
/// first; it used to exhaust its node budget here.
#[test]
fn many_guarded_clauses_compose() {
    agrees(
        "enum Scan { Record(i64, i64), End, Torn, Corrupt }
         fn body(at: i64, len: i64, size: i64, erased p: { 0 <= at && at + 20 <= len && 0 <= size }) -> Scan ! {}
             ensures Record(end, s) => { at + 20 <= end && end <= len && end == at + 20 + size && s == size }
             ensures End => { at == len && at < len }
             ensures Torn => { at < len }
             ensures Corrupt => { at + 20 <= len }
         {
             if size > len - at - 20 { return Scan.Torn; }
             if size == 7 { return Scan.Corrupt; }
             Scan.Record(at + 20 + size, size)
         }
         fn scan(at: i64, len: i64, size: i64, erased p: { 0 <= at && at <= len && 0 <= size }) -> Scan ! {}
             ensures Record(end, s) => { at + 20 <= end && end <= len }
             ensures End => { at == len }
             ensures Torn => { at < len }
             ensures Corrupt => { at + 20 <= len }
         {
             if at == len { return Scan.End; }
             if len - at < 20 { return Scan.Torn; }
             if size > 100 { body(at, len, size - 1, _) } else { body(at, len, size, _) }
         }
         fn main() -> i64 ! {} {
             match scan(0, 100, 30, _) { Scan.Record(end, s) => end, Scan.End => 1, Scan.Torn => 2, Scan.Corrupt => 3 }
         }",
        50,
    );
    rejects(
        "enum Scan { Record(i64), End, Torn }
         fn body(at: i64, len: i64) -> Scan ! {}
             ensures Record(end) => { end <= len }
             ensures End => { at == len }
             ensures Torn => { at < len }
         { if at < len { Scan.Record(len) } else { Scan.Torn } }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures Torn => { at < len }'",
    );
}

/// A range proof may use a bound on another term: `x <= limit` with
/// `limit` an `i64` keeps `size + length` in range.
#[test]
fn range_proofs_use_bounds_of_other_terms() {
    agrees(
        "fn end(size: i64, length: i64, limit: i64, erased b: { 0 <= limit }) -> i64 ! {} {
             if size < 0 || length <= 0 { 0 } else { if length > limit - size { 0 } else { size + length } }
         }
         fn main() -> i64 ! {} { end(3, 4, 10, _) }",
        7,
    );
}
