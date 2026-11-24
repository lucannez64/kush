//! FND-ROWS-INFER (docs/foundations-review.md section 3, E1): a private
//! function may omit its effect row. Its row is the least fixed point over
//! the call graph of what its body requires; public functions, methods,
//! foreign, exported, staged and `#[gpu]` functions still declare theirs.
use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    match check(source) {
        Ok(_) => panic!("accepted:\n{source}"),
        Err(error) => assert!(
            error.message.contains(fragment),
            "expected {fragment:?}, got {error:?}\n{source}"
        ),
    }
}

fn agrees(source: &str, expected: i64, stdout: &str) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(result, expected, "{source}");
    assert_eq!(String::from_utf8_lossy(&output), stdout, "{source}");
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("effect-row-inference");
        kush::native::build(&program, &binary).unwrap();
        let native = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            native.status.code(),
            Some((expected as u64 & 255) as i32),
            "{source}"
        );
        assert_eq!(String::from_utf8_lossy(&native.stdout), stdout, "{source}");
    }
}

#[test]
fn private_functions_infer_their_rows_through_calls() {
    agrees(
        "fn show(x: i64) -> Unit { print_i64(x); }
         fn twice(x: i64) -> Unit { show(x); show(x + 1); }
         fn boxed() -> i64 { Box.take(Box.new(4)) }
         fn pure(x: i64) -> i64 { x * 2 }
         fn main() -> i64 ! {io, alloc} { twice(boxed()); pure(21) }",
        42,
        "4\n5\n",
    );
    // `main` may infer its row too.
    agrees(
        "fn show(x: i64) -> Unit { print_i64(x); }
         fn main() -> i64 { show(3); 0 }",
        0,
        "3\n",
    );
}

#[test]
fn a_declared_row_is_checked_against_the_inferred_rows_it_calls() {
    rejects(
        "fn show(x: i64) -> Unit { print_i64(x); }
         fn twice(x: i64) -> Unit { show(x); show(x) }
         fn main() -> i64 ! {} { twice(1); 0 }",
        "operation requires effects {io}",
    );
    // A function value carries the inferred row in its type.
    rejects(
        "fn show(x: i64) -> Unit { print_i64(x); }
         fn main() -> i64 ! {} { let f: fn(i64) -> Unit ! {} = show; 0 }",
        "type mismatch",
    );
    agrees(
        "fn show(x: i64) -> Unit { print_i64(x); }
         fn main() -> i64 ! {io} { let f: fn(i64) -> Unit ! {io} = show; f(9); 0 }",
        0,
        "9\n",
    );
}

#[test]
fn recursive_functions_reach_the_least_fixed_point() {
    agrees(
        "fn even(n: i64) -> Bool { if n == 0 { true } else { odd(n - 1) } }
         fn odd(n: i64) -> Bool { if n == 0 { false } else { print_i64(n); even(n - 1) } }
         fn count(n: i64) -> i64 { if n == 0 { 0 } else { 1 + count(n - 1) } }
         fn main() -> i64 ! {io} { if even(3) { 1 } else { count(5) } }",
        5,
        "2\n",
    );
    // A recursive function with no effect stays pure.
    agrees(
        "fn count(n: i64) -> i64 { if n == 0 { 0 } else { 1 + count(n - 1) } }
         fn main() -> i64 ! {} { count(7) }",
        7,
        "",
    );
    // Mutual recursion carries `io` to both functions.
    rejects(
        "fn even(n: i64) -> Bool { if n == 0 { true } else { odd(n - 1) } }
         fn odd(n: i64) -> Bool { if n == 0 { false } else { print_i64(n); even(n - 1) } }
         fn main() -> i64 ! {} { if even(4) { 1 } else { 0 } }",
        "operation requires effects {io}",
    );
}

#[test]
fn declared_operations_are_inferred_and_discharged_by_handlers() {
    agrees(
        "effect Ask: i64 -> i64;
         fn ask() -> i64 { perform Ask(1) }
         fn both() -> i64 { ask() + ask() }
         fn main() -> i64 ! {} {
             handle Ask: i64 -> i64 with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x + 20) } { both() }
         }",
        42,
        "",
    );
    // A handle inside an inferred function removes the operation from its
    // row.
    agrees(
        "effect Ask: i64 -> i64;
         fn ask() -> i64 { perform Ask(1) }
         fn served() -> i64 {
             handle Ask: i64 -> i64 with fn(
                 x: i64,
                 resume: linear once fn(i64) -> i64 ! {},
             ) -> i64 ! {} { resume(x + 41) } { ask() }
         }
         fn main() -> i64 ! {} { served() }",
        42,
        "",
    );
    rejects(
        "effect Ask: i64 -> i64;
         fn ask() -> i64 { perform Ask(1) }
         fn main() -> i64 ! {} { ask() }",
        "operation requires effects {Ask}",
    );
}

#[test]
fn generic_and_higher_order_bodies_infer_too() {
    agrees(
        "fn id<T>(x: T) -> T { x }
         fn apply(f: fn(i64) -> i64 ! {io}, x: i64) -> i64 { f(x) }
         fn loud(x: i64) -> i64 ! {io} { print_i64(x); x }
         fn main() -> i64 ! {io} { id(apply(loud, 6)) }",
        6,
        "6\n",
    );
    // A lambda's row is its own: building it is pure.
    agrees(
        "fn make() -> i64 { let f = fn(x: i64) -> i64 ! {io} { print_i64(x); x }; 3 }
         fn main() -> i64 ! {} { make() }",
        3,
        "",
    );
}

#[test]
fn a_suspension_point_gives_an_inferred_row_alloc() {
    // Whether the continuation allocates is decided after the row is
    // settled, so an inferred row takes `alloc` for a non-tail perform.
    let source = |row: &str| {
        format!(
            "effect Ask: i64 -> i64;
             fn ask() -> i64 {{ let a = perform Ask(1); a + 1 }}
             fn run() -> i64 {{
                 handle Ask: i64 -> i64 with fn(
                     x: i64,
                     resume: linear once fn(i64) -> i64 ! {{}},
                 ) -> i64 ! {{}} {{ let r = resume(x); r * 2 }} {{ let v = perform Ask(20); v + 1 }}
             }}
             fn main() -> i64 ! {{{row}}} {{ run() }}"
        )
    };
    rejects(&source(""), "operation requires effects {alloc}");
    agrees(&source("alloc"), 42, "");
}

#[test]
fn only_private_free_functions_omit_their_row() {
    for (source, fragment) in [
        (
            "pub fn show(x: i64) -> Unit { print_i64(x); }
             fn main() -> i64 ! {io} { show(1); 0 }",
            "a public function declares its effect row",
        ),
        (
            "foreign \"abs\" fn abs(x: i32) -> i32;
             fn main() -> i64 ! {} { 0 }",
            "a foreign function declares its effect row",
        ),
        (
            "export \"kush_seven\" fn seven() -> i64 { 7 }
             fn main() -> i64 ! {} { 0 }",
            "an exported function declares its effect row",
        ),
        (
            "fn apply<e: Effects>(f: fn() -> i64 ! {e}) -> i64 { f() }
             fn main() -> i64 ! {} { 0 }",
            "a function with effect parameters declares its effect row",
        ),
        (
            "struct P { x: i64 }
             impl P { fn value(self: P) -> i64 { self.x } }
             fn main() -> i64 ! {} { 0 }",
            "a method declares its effect row",
        ),
        (
            "trait T { fn value(self: Self) -> i64; }
             fn main() -> i64 ! {} { 0 }",
            "a method declares its effect row",
        ),
    ] {
        rejects(source, fragment);
    }
}

#[test]
fn a_total_function_may_omit_its_row() {
    agrees(
        "total fn double(n: Nat) -> Nat { Nat.succ(Nat.succ(n)) }
         fn main() -> i64 ! {} { 1 }",
        1,
        "",
    );
}
