//! Proof usability (PROOF-USABILITY): well-founded recursion for functions
//! with postconditions (`decreases`), struct update syntax, guards on a path
//! (`ensures result.effect is Insert(permit) => { .. }`), length terms in
//! postconditions, and proof failures that name source places.
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("proof_usability");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{source}"
        );
    }
}

fn accepts(source: &str) {
    check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
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

// ── Termination ──────────────────────────────────────────────────────────────

/// The motivating hole: a function that never returns "proved" a false
/// postcondition from its own recursive call.
#[test]
fn recursion_without_progress_cannot_use_its_own_postcondition() {
    rejects(
        "fn f(x: i64) -> i64 ! {} ensures { result > x && result < x } { f(x) }
         fn main() -> i64 ! {} { 0 }",
        "cannot show that this recursion ends",
    );
    // The same call without a postcondition proves nothing, so it is not
    // this check's business.
    accepts(
        "fn spin(x: i64) -> i64 ! {} { spin(x) }
         fn main() -> i64 ! {} { 0 }",
    );
}

#[test]
fn structural_recursion_on_a_matched_parameter_is_accepted() {
    agrees(
        "enum List { Nil, Cons(i64, Box<List>) }
         fn count(items: List) -> i64 ! {} ensures { result >= 0 && result <= 3 } {
             match items {
                 List.Nil => 0,
                 List.Cons(_, rest) => {
                     let n = count(Box.take(rest));
                     if n < 3 { n + 1 } else { n }
                 },
             }
         }
         fn main() -> i64 ! {alloc, panic} {
             count(List.Cons(1, Box.new(List.Cons(2, Box.new(List.Nil))))) + 40
         }",
        42,
    );
    // The smaller list must be passed for the parameter it came from.
    rejects(
        "enum List { Nil, Cons(i64, Box<List>) }
         fn f(a: List, b: List) -> i64 ! {} ensures { result >= 0 } {
             match a { List.Nil => 0, List.Cons(_, rest) => f(b, Box.take(rest)) }
         }
         fn main() -> i64 ! {} { 0 }",
        "cannot show that this recursion ends",
    );
}

#[test]
fn an_integer_argument_must_fall_and_stay_non_negative() {
    agrees(
        "fn sum(n: i64) -> i64 ! {} ensures { result >= 0 && result <= 50 } {
             if n <= 0 { 0 } else { let r = sum(n - 1); if r < 50 { r + 1 } else { r } }
         }
         fn main() -> i64 ! {} { sum(5) + 37 }",
        42,
    );
    // Counting up has no falling argument: it needs a measure.
    rejects(
        "fn count(i: i64, n: i64) -> i64 ! {} ensures { result >= 0 } {
             if i >= n { 0 } else { count(i + 1, n) }
         }
         fn main() -> i64 ! {} { 0 }",
        "Add 'decreases { measure }'",
    );
}

#[test]
fn decreases_gives_a_measure() {
    agrees(
        "fn count(i: i64, n: i64) -> i64 ! {} ensures { result >= 0 && result <= 100 }
             decreases { n - i }
         {
             if i >= n { 0 } else { let r = count(i + 1, n); if r < 100 { r + 1 } else { r } }
         }
         fn main() -> i64 ! {} { count(0, 5) + 37 }",
        42,
    );
    // The measure does not fall.
    rejects(
        "fn count(i: i64, n: i64) -> i64 ! {} ensures { result >= 0 } decreases { n - i } {
             if i >= n { 0 } else { count(i, n) }
         }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'decreases: the measure is at least 0 and smaller than on entry'",
    );
    // The measure falls but is not bounded below.
    rejects(
        "fn down(i: i64) -> i64 ! {} ensures { result >= 0 } decreases { i } {
             if i == 0 { 0 } else if i > -100 { down(i - 1) } else { 0 }
         }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'decreases",
    );
    rejects(
        "fn f(x: i64) -> i64 ! {} decreases { x } { x }
         fn main() -> i64 ! {} { 0 }",
        "this function has no 'ensures'",
    );
}

#[test]
fn mutual_recursion_needs_a_measure_on_every_function() {
    rejects(
        "fn even(n: i64) -> Bool ! {} ensures { result || !result } {
             if n <= 0 { true } else { odd(n - 1) }
         }
         fn odd(n: i64) -> Bool ! {} ensures { result || !result } {
             if n <= 0 { false } else { even(n - 1) }
         }
         fn main() -> i64 ! {} { 0 }",
        "use each other's postconditions",
    );
    agrees(
        "fn even(n: i64) -> Bool ! {} ensures { result || !result } decreases { n } {
             if n <= 0 { true } else { odd(n - 1) }
         }
         fn odd(n: i64) -> Bool ! {} ensures { result || !result } decreases { n } {
             if n <= 0 { false } else { even(n - 1) }
         }
         fn main() -> i64 ! {} { if even(10) { 42 } else { 0 } }",
        42,
    );
}

// ── Struct update ────────────────────────────────────────────────────────────

#[test]
fn struct_update_copies_the_unwritten_fields() {
    agrees(
        "enum Stage { Open, Done }
         struct Driver { stage: Stage, n: i64, ok: Bool }
         struct World { driver: Driver, k: i64 }
         fn finish(d: Driver) -> Driver ! {}
             ensures { result.stage is Done && result.n == d.n && (!result.ok || d.ok) }
         { Driver { stage: Stage.Done, ..d } }
         fn reset(w: World) -> Driver ! {} ensures { result.n == 5 && result.ok } {
             Driver { ok: true, n: 5, ..w.driver }
         }
         fn main() -> i64 ! {} {
             let d = finish(Driver { stage: Stage.Open, n: 40, ok: true });
             let e = reset(World { driver: d, k: 1 });
             d.n + e.n - 3
         }",
        42,
    );
}

#[test]
fn struct_update_rejections() {
    rejects(
        "struct D { a: i64, b: i64 }
         fn f(d: D) -> D ! {} { D { a: 1, b: 2, ..d } }
         fn main() -> i64 ! {} { 0 }",
        "writes every field",
    );
    rejects(
        "struct D { a: i64, b: i64 }
         fn g() -> D ! {} { D { a: 1, b: 2 } }
         fn f() -> D ! {} { D { a: 1, ..g() } }
         fn main() -> i64 ! {} { 0 }",
        "must be a local or a field path",
    );
    rejects(
        "struct D { a: i64, b: i64 }
         fn f(d: D) -> D ! {} { D { a: 1, ..d, b: 2 } }
         fn main() -> i64 ! {} { 0 }",
        "must be the last entry",
    );
    rejects(
        "struct D { a: i64, b: i64 }
         fn f(d: D) -> D ! {} { D { c: 1, ..d } }
         fn main() -> i64 ! {} { 0 }",
        "record has no field 'c'",
    );
    // A copied field cannot own heap data; a written one can.
    rejects(
        "struct D { a: Box<i64>, b: i64 }
         fn f(d: D) -> D ! {} { D { b: 1, ..d } }
         fn main() -> i64 ! {} { 0 }",
        "cannot move owned field 'a'",
    );
}

// ── Guards on a path ─────────────────────────────────────────────────────────

const STEP: &str = "
struct Permit { epoch: i64, possession: Bool }
enum Effect { Insert(Permit), Fail(i64), Idle }
struct Transition { stage: i64, effect: Effect }
fn step(epoch: i64, ok: Bool) -> Transition ! {}
    ensures result.effect is Insert(permit) => { permit.epoch == epoch && ok && result.stage == 2 }
    ensures result.effect is Fail(code) => { code == 7 && !ok }
    ensures result.effect is Idle => { false }
{
    if ok {
        Transition { stage: 2, effect: Effect.Insert(Permit { epoch: epoch, possession: true }) }
    } else {
        Transition { stage: 9, effect: Effect.Fail(7) }
    }
}
";

#[test]
fn a_guard_can_name_the_payload_of_an_enum_inside_the_result() {
    agrees(
        &format!(
            "{STEP}
             fn permitted_epoch(epoch: i64) -> i64 ! {{}} ensures {{ result == epoch }} {{
                 let t = step(epoch, true);
                 match t.effect {{
                     Effect.Insert(p) => p.epoch,
                     Effect.Fail(_) => epoch,
                     Effect.Idle => epoch,
                 }}
             }}
             fn main() -> i64 ! {{}} {{ permitted_epoch(42) }}"
        ),
        42,
    );
    // The guard may also test a parameter.
    accepts(
        "enum Effect { Fail(i64), Idle }
         fn code(e: Effect) -> i64 ! {}
             ensures e is Fail(c) => { result == c }
             ensures e is Idle => { result == 0 }
         { match e { Effect.Fail(c) => c, Effect.Idle => 0 } }
         fn main() -> i64 ! {} { 0 }",
    );
}

#[test]
fn a_path_guard_is_proved_not_assumed() {
    rejects(
        &STEP.replace("code == 7", "code == 8"),
        "cannot prove 'ensures result.effect is Fail(code) => { code == 8 && !(ok) }'",
    );
    rejects(
        "enum E { A, B }
         struct T { e: E }
         fn f() -> T ! {} ensures result.e => { true } { T { e: E.A } }
         fn main() -> i64 ! {} { 0 }",
        "expected 'is Variant =>'",
    );
}

// ── Lengths ──────────────────────────────────────────────────────────────────

#[test]
fn postconditions_state_and_use_vec_lengths() {
    agrees(
        "fn push1(v: Vec<i64>) -> Vec<i64> ! {alloc, panic}
             ensures { Vec.len(result) == Vec.len(v) + 1 }
         { Vec.push(v, 1) }
         fn push2(v: Vec<i64>) -> Vec<i64> ! {alloc, panic}
             ensures { Vec.len(result) == Vec.len(v) + 2 }
         { let w = push1(v); let mut x = w; x = Vec.push(x, 3); x }
         fn same(v: Vec<i64>) -> Vec<i64> ! {} ensures { Vec.len(result) == Vec.len(v) } { v }
         fn count(v: &Vec<i64>) -> i64 ! {} ensures { result == Vec.len(v) && result >= 0 } {
             Vec.len(v)
         }
         fn fresh() -> Vec<i64> ! {alloc, panic} ensures { Vec.len(result) == 0 } { Vec.new() }
         fn two() -> i64 ! {alloc, panic} ensures { result == 2 } {
             let v = same(push2(fresh()));
             count(&v)
         }
         fn main() -> i64 ! {alloc, panic} { two() + 40 }",
        42,
    );
    rejects(
        "fn push1(v: Vec<i64>) -> Vec<i64> ! {alloc, panic}
             ensures { Vec.len(result) == Vec.len(v) + 2 }
         { Vec.push(v, 1) }
         fn main() -> i64 ! {} { 0 }",
        "cannot prove 'ensures { Vec.len(result) == Vec.len(v) + 2 }'",
    );
    // A reassigned vector has a new length.
    rejects(
        "fn grow(v: Vec<i64>) -> Vec<i64> ! {alloc, panic}
             ensures { Vec.len(result) == Vec.len(v) }
         { let mut w = v; w = Vec.push(w, 1); w }
         fn main() -> i64 ! {} { 0 }",
        "len(w) == len(v) + 1",
    );
}

#[test]
fn postconditions_state_lengths_of_bytes_text_and_slices() {
    agrees(
        "struct Queue { items: Vec<i64>, n: i64 }
         fn queue(v: Vec<i64>) -> Queue ! {}
             ensures { Vec.len(result.items) == Vec.len(v) && result.n == Vec.len(v) }
         { let n = Vec.len(&v); Queue { items: v, n: n } }
         fn append(b: Bytes) -> Bytes ! {alloc, panic}
             ensures { Bytes.len(result) == Bytes.len(b) + 1 }
         { Bytes.push(b, 7) }
         fn text(s: &String) -> i64 ! {} ensures { result == String.len(s) } { String.len(s) }
         fn view(s: &str) -> i64 ! {} ensures { result == Str.len(s) } { Str.len(s) }
         fn slice(s: &[i64]) -> i64 ! {} ensures { result == Slice.len(s) } { Slice.len(s) }
         fn main() -> i64 ! {alloc, panic} {
             let b = append(append(Bytes.with_capacity(4)));
             let v: Vec<i64> = Vec.new();
             let q = queue(Vec.push(v, 9));
             Bytes.len(&b) + q.n + 39
         }",
        42,
    );
}

// ── Messages ─────────────────────────────────────────────────────────────────

#[test]
fn proof_failures_name_fields_variants_and_calls() {
    let source = "
enum Stage { Open, Closing, Done }
enum Effect { Complete, Idle }
struct Driver { stage: Stage, restored: Bool }
struct Transition { driver: Driver, effect: Effect }
fn finish(d: Driver) -> Transition ! {}
    ensures { result.driver.stage is Done && result.driver.restored }
{ Transition { driver: Driver { stage: Stage.Done, restored: true }, effect: Effect.Complete } }
fn step(d: Driver) -> Transition ! {} ensures { !(result.effect is Complete) } {
    match d.stage {
        Stage.Done => finish(d),
        Stage.Open => Transition { driver: d, effect: Effect.Idle },
        Stage.Closing => Transition { driver: d, effect: Effect.Idle },
    }
}
fn main() -> i64 ! {} { 0 }";
    let error = check(source).expect_err("the Done arm returns Complete");
    for fragment in [
        "d.stage is Done",
        "finish(..).driver.stage is Done",
        "finish(..).driver.restored",
    ] {
        assert!(
            error.message.contains(fragment),
            "expected {fragment:?} in {:?}",
            error.message
        );
    }
    assert!(!error.message.contains("field@"), "{:?}", error.message);
    assert!(!error.message.contains("call#"), "{:?}", error.message);
}
