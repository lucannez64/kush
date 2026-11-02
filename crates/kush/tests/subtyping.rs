use kush::executable::check;

fn value(source: &str) -> i64 {
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    result
}

fn output(source: &str) -> String {
    let program = check(source).unwrap();
    let mut out = Vec::new();
    let (_, stats) = program
        .evaluate_with_io_and_stats(&mut std::io::empty(), &mut out)
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    String::from_utf8(out).unwrap()
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

#[test]
fn normalization_obeys_algebraic_lattice_laws() {
    // Idempotence and bottom/top of the union lattice.
    value(
        "fn f(x: i64 | i64) -> i64 ! {} { x } fn g(x: (i64 & Bool) | i64) -> i64 ! {} { x }
         fn main() -> i64 ! {panic} { f(20) + g(22) }",
    );
    // Distributivity: (i64|Bool) & (i64|Bytes) = i64.
    value(
        "fn f(x: (i64 | Bool) & (i64 | Bytes)) -> i64 ! {} { x }
         fn main() -> i64 ! {} { f(42) }",
    );
    // Absorption inside one enum keeps the zero-cost variant mask.
    value(
        "enum E { A, B, C }
         fn f(x: (E.A | E.B) | E) -> i64 ! {} { match x { E.A => 1, E.B => 2, E.C => 3 } }
         fn main() -> i64 ! {} { f(E.C) }",
    );
    // Intersection with a variant mask narrows it.
    value(
        "enum E { A, B }
         fn f(x: E.A & E) -> i64 ! {} { match x { E.A => 42 } }
         fn main() -> i64 ! {} { f(E.A) }",
    );
    // Flattening of nested unions in both parenthesizations.
    value(
        "fn f(x: i64 | (Bool | Bytes)) -> i64 | Bool | Bytes ! {panic} { x }
         fn g(x: (i64 | Bool) | Bytes) -> i64 | Bool | Bytes ! {panic} { x }
         fn main() -> i64 ! {panic} {
            match f(g(42)) { i64 @ n => n, Bool @ _ => 0, Bytes @ _ => 0 }
         }",
    );
}

#[test]
fn normalization_budgets_are_explicit() {
    rejects(
        "enum E1 { A } enum E2 { A } enum E3 { A } enum E4 { A } enum E5 { A }
         enum E6 { A } enum E7 { A } enum E8 { A } enum E9 { A }
         fn f(x: i64 | Bool | Unit | Bytes | Box<i64> | Box<Bool> | Vec<i64> | Vec<Bool>
                   | E1 | E2 | E3 | E4 | E5 | E6 | E7 | E8 | E9) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "16-alternative",
    );
    let fields = (0..31).map(|_| "i64").collect::<Vec<_>>().join(",");
    rejects(
        &format!(
            "enum Wide {{ Value({fields}) }} fn f(x: Wide | i64) -> i64 ! {{}} {{ 0 }}
             fn main() -> i64 ! {{}} {{ 0 }}"
        ),
        "32-word layout",
    );
}

#[test]
fn false_intersections_have_no_runtime_inhabitant() {
    rejects(
        "fn main() -> i64 ! {} { let x: i64 & Bool = 1; 0 }",
        "type mismatch",
    );
    rejects(
        "fn f(x: i64 & Bool) -> i64 ! {} { x } fn main() -> i64 ! {} { f(1) }",
        "type mismatch",
    );
    // A never-typed body is fine: no value can reach it.
    value("fn f(x: i64 & Bool) -> i64 ! {} { x } fn main() -> i64 ! {} { 42 }");
}

#[test]
fn heterogeneous_scalar_unions_join_and_narrow() {
    assert_eq!(
        value(
            "fn classify(x: i64 | Bool) -> i64 ! {panic} {
            match x {
                i64 @ n if n > 40 => n,
                i64 @ n => n - 1,
                Bool @ b => if b { 1 } else { 0 },
            }
         }
         fn main() -> i64 ! {panic} {
            let c = true;
            let x = if c { 41 } else { true };
            classify(x) + classify(true)
         }",
        ),
        42
    );
}

#[test]
fn owning_unions_repack_and_drop_only_the_active_alternative() {
    let source = "fn choose(c: Bool) -> Box<i64> | Bytes ! {alloc, panic} {
            if c { Box.new(41) } else { Bytes.from(\"abcdef\") }
        }
        fn main() -> i64 ! {alloc, panic} {
            let a = choose(true);
            let b = choose(false);
            let unused: Box<i64> | Bytes = if true { Box.new(0) } else { Bytes.from(\"x\") };
            match a { Box<i64> @ x => Box.take(x) + 1, Bytes @ y => Bytes.len(&y) } +
            match b { Box<i64> @ _ => 0, Bytes @ y => Bytes.len(&y) }
        }";
    assert_eq!(value(source), 42 + 6);
}

#[test]
fn record_and_enum_unions_narrow_nested_payloads() {
    let source = "struct Pair { left: i64, right: i64 }
        enum Shape { Dot, Line(i64) }
        fn point(p: Pair) -> i64 ! {panic} { p.left + p.right }
        fn area(x: Pair | Shape | i64) -> i64 ! {panic} {
            match x {
                Pair @ p => point(p),
                Shape @ s => match s { Shape.Dot => 0, Shape.Line(n) => n },
                i64 @ n => n,
            }
        }
        fn main() -> i64 ! {panic} {
            area(Pair { left: 19, right: 20 }) + area(Shape.Line(1)) + area(2)
        }";
    assert_eq!(value(source), 42);
}

#[test]
fn generic_record_unions_infer_from_one_matching_alternative() {
    assert_eq!(
        value(
            "struct Pair<T> { a: T, b: T }
             fn main() -> i64 ! {panic} {
                let x: Pair<i64> | i64 = Pair { a: 20, b: 22 };
                match x {
                    Pair<i64> @ p => match p { Pair { a, b } => a + b },
                    i64 @ n => n,
                }
             }",
        ),
        42
    );
    rejects(
        "struct Pair<T> { a: T, b: T }
         fn f(x: Pair<i64> | Pair<Bool>) -> i64 ! {} { 0 }
         fn main() -> i64 ! {} { let x: Pair<i64> | Pair<Bool> = Pair { a: 1, b: 2 }; 0 }",
        "several union alternatives",
    );
}

#[test]
fn union_widening_repacks_subset_union_at_call_and_return_boundaries() {
    let source = "fn small(c: Bool) -> i64 | Bool ! {} { if c { 40 } else { true } }
        fn wider(c: Bool) -> i64 | Bool | Bytes ! {alloc, panic} {
            let x: i64 | Bool | Bytes = small(c);
            x
        }
        fn consume(x: i64 | Bool | Bytes) -> i64 ! {panic} {
            match x { i64 @ n => n, Bool @ b => if b { 2 } else { 0 }, Bytes @ b => Bytes.len(&b) }
        }
        fn main() -> i64 ! {alloc, panic} { consume(wider(true)) + consume(wider(false)) }";
    assert_eq!(value(source), 42);
}

#[test]
fn union_matches_are_exhaustive_and_detect_unreachable_arms() {
    rejects(
        "fn f(x: i64 | Bool) -> i64 ! {} { match x { i64 @ n => n } } fn main() -> i64 ! {} { 0 }",
        "non-exhaustive",
    );
    rejects(
        "fn f(x: i64 | Bool) -> i64 ! {} { match x { i64 @ _ => 0, Bool @ _ => 1, i64 @ n => n } }
         fn main() -> i64 ! {} { 0 }",
        "unreachable",
    );
    rejects(
        "fn f(x: i64 | Bool) -> i64 ! {} { match x { i64 @ n if n > 0 => n, Bool @ _ => 0 } }
         fn main() -> i64 ! {} { 0 }",
        "non-exhaustive",
    );
    // A guarded arm does not contribute coverage; an unguarded remainder does.
    value(
        "fn f(x: i64 | Bool) -> i64 ! {panic} {
            match x { i64 @ n if n > 0 => n, i64 @ _ => 0, Bool @ _ => 1 }
         }
         fn main() -> i64 ! {panic} { f(42) }",
    );
}

#[test]
fn generic_functions_infer_and_specialize_union_arguments() {
    value(
        "fn id<T>(x: T) -> T ! {} { x }
         fn main() -> i64 ! {panic} {
            let c = true;
            let u = if c { 41 } else { true };
            let v = id(u);
            match v { i64 @ n => n, Bool @ _ => 0 }
         }",
    );
    value(
        "fn id<T>(x: T) -> T ! {} { x }
         enum Option<T> { None, Some(T) }
         fn main() -> i64 ! {panic} {
            let x = id::<Option<i64> | i64>(Some(41));
            match x { Option<i64> @ o => match o { Some(n) => n, None => 0 }, i64 @ n => n }
         }",
    );
    // Distinct generic instantiations can be union alternatives and are
    // narrowed with explicit member types.
    value(
        "enum Option<T> { None, Some(T) }
         fn f(x: Option<i64> | Option<Bool>) -> i64 ! {panic} {
            match x {
                Option<i64> @ o => match o { Option.Some(n) => n, Option.None => 0 },
                Option<Bool> @ o => match o { Option.Some(b) => if b { 1 } else { 0 }, Option.None => 2 },
            }
         }
         fn main() -> i64 ! {panic} { f(Option.Some::<Bool>(true)) }",
    );
    rejects(
        "enum Option<T> { None, Some(T) }
         fn f(x: Option<i64> | Option<Bool>) -> i64 ! {} { match x { Option.Some(n) => 0, _ => 0 } }
         fn main() -> i64 ! {} { 0 }",
        "matches several union alternatives",
    );
    // Owning containers remain invariant: no implicit Vec covariance.
    rejects(
        "fn f(v: Vec<i64 | Bool>) -> i64 ! {} { 0 }
         fn main() -> i64 ! {alloc, panic} { let v: Vec<i64> = Vec.new(); f(v) }",
        "type mismatch",
    );
}

#[test]
fn return_and_try_preserve_union_cleanup_and_reject_invalid_repacking() {
    value(
        "enum Result<T, E> { Ok(T), Err(E) }
         fn step(c: Bool) -> Result<i64, i64 | Bool> ! {} { if c { Err(7) } else { Err(true) } }
         fn run(c: Bool) -> Result<i64, i64 | Bool> ! {alloc, panic} {
            let guard = Box.new(5);
            let n = step(c)?;
            Ok(Box.take(guard) + n)
         }
         fn main() -> i64 ! {alloc, panic} {
            match run(false) { Ok(n) => n, Err(e) => match e { i64 @ n => n, Bool @ _ => 1 } }
         }",
    );
    rejects(
        "enum Result<T, E> { Ok(T), Err(E) }
         fn step() -> Result<i64, i64> ! {} { Err(7) }
         fn run() -> Result<i64, i64 | Bool> ! {} { Ok(step()?) }
         fn main() -> i64 ! {} { 0 }",
        "cannot repack",
    );
}

#[test]
fn owned_unions_keep_grade_obligations_and_linear_alternatives() {
    value(
        "fn take(x: (Box<i64> | i64) @[1]) -> (Box<i64> | i64) @[1] ! {} {
            match x { Box<i64> @ b => b, i64 @ n => n }
         }
         fn main() -> i64 ! {alloc, panic} {
            match take(Box.new(42)) { Box<i64> @ b => Box.take(b), i64 @ n => n }
         }",
    );
    // Returning the same owned-union obligation through an ungraded result
    // would make it affine at the caller, so it is rejected explicitly.
    rejects(
        "fn take(x: (Box<i64> | i64) @[1]) -> Box<i64> | i64 ! {} {
            match x { Box<i64> @ b => b, i64 @ n => n }
         }
         fn main() -> i64 ! {alloc, panic} { 0 }",
        "ungraded result",
    );
    rejects(
        "fn bad(x: (Box<i64> | Bytes) @[2]) -> i64 ! {panic} { 0 }
         fn main() -> i64 ! {} { 0 }",
        "would duplicate",
    );
    rejects(
        "#[linear] enum Token { One(i64), End }
         fn f(x: i64 | Token) -> i64 ! {} { match x { i64 @ n => n, Token @ _ => 0 } }
         fn main() -> i64 ! {} { 0 }",
        "ignores a linear value",
    );
    // A shared copyable union may be used twice under exact grade 2.
    value(
        "fn twice(x: (i64 | Bool) @[2]) -> i64 ! {panic} {
            match x { i64 @ n => n, Bool @ b => if b { 1 } else { 0 } } +
            match x { i64 @ n => n, Bool @ _ => 0 }
         }
         fn main() -> i64 ! {panic} { twice(20) }",
    );
}

#[test]
fn borrowed_views_cannot_escape_through_unions() {
    rejects(
        "fn f(x: &[i64] | i64) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "borrowed references or slice views",
    );
    rejects(
        "fn f(x: &Box<i64> | i64) -> i64 ! {} { 0 } fn main() -> i64 ! {} { 0 }",
        "borrowed references or slice views",
    );
    // Slices still work outside unions and keep their lexical loans.
    value(
        "fn sum(view: &[i64]) -> i64 ! {panic} {
            let mut i = 0; let mut sum = 0;
            while i < Slice.len(view) { sum = sum + Slice.get(view, i); i = i + 1; }
            sum
         }
         fn main() -> i64 ! {panic} {
            let values: [i64; 3] = [10, 20, 12];
            let view: &[i64] = &values[..];
            sum(view)
         }",
    );
}

#[test]
fn unit_alternatives_use_real_injection_in_returns_and_loops() {
    assert_eq!(
        value(
            "fn f(c: Bool) -> Unit | i64 ! {panic} {
                if c { return; }
                return 41;
             }
             fn main() -> i64 ! {panic} {
                let x: Unit | i64 = loop { break; };
                let y: Unit | i64 = if true { () };
                match f(true) { Unit @ _ => 1, i64 @ n => n } +
                match f(false) { Unit @ _ => 0, i64 @ n => n } +
                match x { Unit @ _ => 0, i64 @ n => n } +
                match y { Unit @ _ => 0, i64 @ n => n }
             }",
        ),
        42
    );
}

#[test]
fn arrays_and_vectors_can_be_injected_contextually_into_unions() {
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let a: [i64; 2] | i64 = [20, 22];
                let v: Vec<i64> | i64 = [40, 2];
                match a { [i64; 2] @ xs => xs[0] + xs[1], i64 @ n => n } +
                match v { Vec<i64> @ vs => Vec.len(&vs) + 40, i64 @ n => n }
             }",
        ),
        84
    );
}

#[test]
fn union_repacking_handles_different_payload_widths() {
    let source = "struct Pair { left: Box<i64>, right: Box<i64> }
        fn small(c: Bool) -> i64 | Bool ! {} { if c { 40 } else { true } }
        fn wide(c: Bool) -> i64 | Bool | Pair ! {alloc, panic} {
            let s: i64 | Bool | Pair = small(c);
            s
        }
        fn main() -> i64 ! {alloc, panic} {
            let a = wide(true);
            let b = wide(false);
            let p: i64 | Bool | Pair = Pair { left: Box.new(1), right: Box.new(1) };
            match a { i64 @ n => n, Bool @ _ => 0, Pair @ _ => 0 } +
            match b { i64 @ _ => 0, Bool @ _ => 2, Pair @ _ => 0 } +
            match p { i64 @ _ => 0, Bool @ _ => 0, Pair @ Pair { left, right } => Box.take(left) + Box.take(right) }
        }";
    assert_eq!(value(source), 44);
}

#[test]
fn owning_union_drop_uses_only_the_active_alternative_layout() {
    let source = "struct Pair { left: Box<i64>, right: Box<i64> }
        fn choose(c: Bool) -> Box<i64> | Pair ! {alloc, panic} {
            if c { Box.new(40) } else { Pair { left: Box.new(1), right: Box.new(1) } }
        }
        fn main() -> i64 ! {alloc, panic} {
            let a = choose(true);
            let b = choose(false);
            let ignored: Box<i64> | Pair = Box.new(0);
            match a { Box<i64> @ x => Box.take(x), Pair @ _ => 0 } +
            match b { Box<i64> @ _ => 0, Pair @ Pair { left, right } => Box.take(left) + Box.take(right) }
        }";
    assert_eq!(value(source), 42);
}

#[test]
fn subtyping_example_prints_the_documented_output() {
    let source = include_str!("../../../examples/subtyping.kush");
    assert_eq!(output(source), "21\n20\n4\n39\n3\n21\n4\n42\n");
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_and_reference_agree_on_subtyping_example() {
    use std::process::Command;
    let source = include_str!("../../../examples/subtyping.kush");
    let program = check(source).unwrap();
    let mut expected = Vec::new();
    let status = program.evaluate(&mut expected).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("subtyping");
    kush::native::build(&program, &binary).unwrap();
    let result = Command::new(binary).output().unwrap();
    assert_eq!(result.status.code(), Some(status as i32));
    assert_eq!(result.stdout, expected);
    assert!(result.stderr.is_empty());
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_and_reference_agree_on_width_changing_union_repack() {
    use std::process::Command;
    let source = "struct Pair { left: Box<i64>, right: Box<i64> }
        fn small(c: Bool) -> i64 | Bool ! {} { if c { 40 } else { true } }
        fn wide(c: Bool) -> i64 | Bool | Pair ! {alloc, panic} {
            let s: i64 | Bool | Pair = small(c); s
        }
        fn main() -> i64 ! {alloc, panic} {
            match wide(true) { i64 @ n => n, Bool @ _ => 0, Pair @ _ => 0 } +
            match wide(false) { i64 @ _ => 0, Bool @ _ => 2, Pair @ _ => 0 }
        }";
    let program = check(source).unwrap();
    let mut expected = Vec::new();
    let status = program.evaluate(&mut expected).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("repack-width");
    kush::native::build(&program, &binary).unwrap();
    let result = Command::new(binary).output().unwrap();
    assert_eq!(result.status.code(), Some(status as i32));
    assert_eq!(result.stdout, expected);
    assert!(result.stderr.is_empty());
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn native_and_reference_agree_on_owning_union_repacking() {
    use std::process::Command;
    let source = "fn small(c: Bool) -> i64 | Bool ! {} { if c { 40 } else { true } }
        fn wider(c: Bool) -> i64 | Bool | Bytes ! {alloc, panic} {
            let x: i64 | Bool | Bytes = small(c); x
        }
        fn main() -> i64 ! {alloc, panic} {
            match wider(true) { i64 @ n => n, Bool @ _ => 0, Bytes @ _ => 0 } +
            match wider(false) { i64 @ _ => 0, Bool @ _ => 2, Bytes @ _ => 0 }
        }";
    let program = check(source).unwrap();
    let mut expected = Vec::new();
    let status = program.evaluate(&mut expected).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("repack");
    kush::native::build(&program, &binary).unwrap();
    let result = Command::new(binary).output().unwrap();
    assert_eq!(result.status.code(), Some(status as i32));
    assert_eq!(result.stdout, expected);
    assert!(result.stderr.is_empty());
}

#[test]
fn callable_union_alternatives_inject_repack_and_narrow_coherently() {
    assert_eq!(
        value(
            "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
             fn answer() -> i64 ! {panic} { 42 }
             fn main() -> i64 ! {panic} {
                let f: fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = inc;
                let w: i64 | fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = f;
                let a = match w {
                    i64 @ n => n,
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                };
                let g: i64 | fn(i64) -> i64 ! {panic} | fn() -> i64 ! {panic} = answer;
                let b = match g {
                    i64 @ n => n,
                    fn(i64) -> i64 ! {panic} @ h => h(41),
                    fn() -> i64 ! {panic} @ h => h(),
                };
                a + b - 42
             }"
        ),
        42
    );
    // A once closure alternative is owned; the active payload is dropped with
    // its environment when it is not called.
    assert_eq!(
        value(
            "fn main() -> i64 ! {alloc, panic} {
                let n = Box.new(1);
                let c: i64 | once fn(i64) -> i64 ! {panic} =
                    fn(x: i64) -> i64 ! {panic} { Box.take(n) + x };
                42
             }"
        ),
        42
    );
    // A narrowed callable alternative keeps its per-signature indirect-call
    // ABI; using a different arrow shape requires an explicit adapter.
    rejects(
        "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn main() -> i64 ! {panic} {
            let f: fn(i64) -> i64 ! {panic} | fn(Bool) -> i64 ! {panic} = inc;
            match f { fn(i64) -> Bool ! {panic} @ h => h(1), _ => 42 }
         }",
        "not an alternative",
    );
}
