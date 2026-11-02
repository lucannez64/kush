//! Grade-zero runtime erasure and observable-initializer guarantees.
//!
//! `@[0]` still evaluates its initializer because Kush is strict. The binding
//! is not materialized: no store, runtime local, read, or cleanup is emitted,
//! and every runtime observation remains a compile-time error. Initializer
//! effects (I/O, panic, allocation) stay observable and agree across backends.
use kush::executable::{MemoryStats, check};

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn run(source: &str) -> (i64, String, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(
        stats.allocations, stats.deallocations,
        "allocation balance: {source}"
    );
    (status, String::from_utf8(output).unwrap(), stats)
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) -> MemoryStats {
    let (status, output, stats) = run(source);
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(output, expected_output, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("grade-zero-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
    stats
}

#[test]
fn the_initializer_is_still_evaluated_for_its_effects() {
    agrees(
        r#"fn main() -> i64 ! {io, panic} {
            let value: i64 @[0] = { print_i64(7); 1 };
            42
        }"#,
        42,
        "7\n",
    );
}

#[test]
fn allocation_effects_are_preserved_and_balanced() {
    let stats = agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let value: i64 @[0] = Box.take(Box.new(9));
            42
        }"#,
        42,
        "",
    );
    assert_eq!(stats.allocations, 1, "{stats:?}");
    assert_eq!(stats.deallocations, 1, "{stats:?}");
}

#[test]
fn a_custom_algebra_zero_is_erased_the_same_way() {
    agrees(
        r#"algebra Usage {
            elements { None, Once }
            zero = None; one = Once;
            add {
                None + None = None, None + Once = Once,
                Once + None = Once, Once + Once = Once,
            }
            mul {
                None * None = None, None * Once = None,
                Once * None = None, Once * Once = Once,
            }
        }
        fn main() -> i64 ! {io, panic} {
            let value: i64 @[Usage.None] = { print_i64(3); 1 };
            5
        }"#,
        5,
        "3\n",
    );
}

#[test]
fn runtime_observation_of_an_erased_binding_is_rejected() {
    rejects(
        "fn main() -> i64 ! {} { let value: i64 @[0] = 1; value }",
        "grade @[0]",
    );
    rejects(
        "fn main() -> i64 ! {} { let value: i64 @[0] = 1; let other = value; 0 }",
        "grade @[0]",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let value: i64 @[0] = 1; value + 1 }",
        "grade @[0]",
    );
    // Zero runtime observations is exactly the contract, so an unused erased
    // binding is accepted and its initializer still runs.
    if let Err(error) = check("fn main() -> i64 ! {} { let value: i64 @[0] = 1; 0 }") {
        panic!("expected an unused grade-zero binding to be accepted: {error:?}");
    }
}

#[test]
fn owning_values_cannot_be_graded_zero() {
    // An affine owner is initialized and dropped eagerly; a linear obligation
    // cannot be discarded.
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} { let value: Box<i64> @[0] = Box.new(1); 0 }",
        0,
        "",
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    rejects(
        "#[linear] enum L { A(i64) }
         fn main() -> i64 ! {} { let value: L @[0] = L.A(1); 0 }",
        "silently discard the linear obligation",
    );
}

#[test]
fn erased_results_have_no_payload_and_cannot_be_laundered() {
    // The callee computes and erases its result; the call is a Unit value.
    agrees(
        r#"fn compute() -> i64 @[0] ! {io, panic} { print_i64(7); 42 }
        fn main() -> i64 ! {io, panic} {
            let ignored = compute();
            9
        }"#,
        9,
        "7\n",
    );
    // Every attempted use is a type mismatch: there is no value to observe.
    rejects(
        "fn compute() -> i64 @[0] ! {panic} { 42 }
         fn main() -> i64 ! {panic} { compute() + 1 }",
        "type mismatch",
    );
    rejects(
        "fn compute() -> i64 @[0] ! {panic} { 42 }
         fn main() -> i64 ! {panic} { let value: i64 = compute(); value }",
        "type mismatch",
    );
    rejects(
        "fn compute() -> i64 @[0] ! {panic} { 42 }
         fn main() -> i64 ! {panic} { if true { compute() } else { compute() } }",
        "type mismatch",
    );
    rejects(
        "fn compute() -> i64 @[0] ! {panic} { 42 }
         fn main() -> i64 ! {panic} { return compute() }",
        "type mismatch",
    );
    rejects(
        "fn compute() -> i64 @[0] ! {panic} { 42 }
         fn main() -> i64 ! {alloc, panic} { [compute(), compute()][0] }",
        "bind this owned value",
    );
}

#[test]
fn erased_results_work_through_function_values_and_returns() {
    agrees(
        r#"fn compute() -> i64 @[0] ! {panic} { 42 }
        fn main() -> i64 ! {panic} {
            let f: fn() -> i64 @[0] ! {panic} = compute;
            f();
            5
        }"#,
        5,
        "",
    );
    // Returning an erased call from another erased-result function is
    // well-typed: both functions erase the same payload type.
    agrees(
        r#"fn inner() -> i64 @[0] ! {panic} { 7 }
        fn outer() -> i64 @[0] ! {panic} { inner() }
        fn main() -> i64 ! {panic} { outer(); 3 }"#,
        3,
        "",
    );
}

#[test]
fn main_cannot_erase_its_process_result() {
    rejects(
        "fn main() -> i64 @[0] ! {} { 42 }",
        "main cannot carry a result usage contract",
    );
}

#[test]
fn owning_and_linear_results_cannot_be_erased() {
    rejects(
        "fn make() -> Box<i64> @[0] ! {alloc, panic} { Box.new(1) }
         fn main() -> i64 ! {alloc, panic} { make(); 0 }",
        "silently discard the owning/linear value",
    );
    rejects(
        "#[linear] enum L { A(i64) }
         fn make() -> L @[0] ! {} { L.A(1) }
         fn main() -> i64 ! {} { 0 }",
        "silently discard the owning/linear value",
    );
}

#[test]
fn grade_zero_parameters_are_physically_absent_from_the_abi() {
    // The argument is still evaluated in source order for its effects, but no
    // value crosses the call boundary for the erased positions.
    agrees(
        r#"fn ignore3(a: i64 @[0], b: i64, c: i64 @[0]) -> i64 ! {panic} { b }
        fn main() -> i64 ! {io, panic} {
            ignore3({ print_i64(1); 10 }, { print_i64(2); 20 }, { print_i64(3); 30 })
        }"#,
        20,
        "1\n2\n3\n",
    );
}

#[test]
fn a_zero_parameter_argument_cannot_be_read_by_the_callee() {
    rejects(
        "fn f(x: i64 @[0]) -> i64 ! {} { x } fn main() -> i64 ! {} { f(1) }",
        "grade @[0]",
    );
}

#[test]
fn function_value_adapters_bridge_erased_parameter_arities() {
    // The source ignores its parameter, so it widens to an ordinary one-value
    // arrow. The synthesized adapter accepts the physical argument and calls
    // the zero-parameter ABI of the source.
    agrees(
        r#"fn ignore(x: i64 @[0]) -> i64 ! {panic} { 42 }
        fn apply(f: fn(i64) -> i64 ! {panic}) -> i64 ! {panic} { f(3) }
        fn main() -> i64 ! {panic} { apply(ignore) }"#,
        42,
        "",
    );
    // The opposite direction would have to invent an argument for a function
    // that does observe it, and stays rejected.
    rejects(
        "fn uses(x: i64) -> i64 ! {panic} { x }
         fn apply(f: fn(i64 @[0]) -> i64 ! {panic}) -> i64 ! {panic} { f(1) }
         fn main() -> i64 ! {panic} { apply(uses) }",
        "type mismatch",
    );
}

#[test]
fn indirect_erased_parameter_calls_keep_argument_effects() {
    agrees(
        r#"fn main() -> i64 ! {io, panic} {
            let f: fn(i64 @[0]) -> i64 ! {panic} =
                fn(x: i64 @[0]) -> i64 ! {panic} { 42 };
            f({ print_i64(9); 1 })
        }"#,
        42,
        "9\n",
    );
}

#[test]
fn pure_to_once_adapters_bridge_erased_parameter_arities() {
    agrees(
        r#"fn ignore(x: i64 @[0]) -> i64 ! {alloc, panic} { 42 }
        fn apply(f: once fn(i64) -> i64 ! {alloc, panic}) -> i64 ! {alloc, panic} {
            f(3)
        }
        fn main() -> i64 ! {alloc, panic} { apply(ignore) }"#,
        42,
        "",
    );
}

#[test]
fn vector_map_callbacks_cannot_erase_observed_elements() {
    rejects(
        r#"fn ghost(value: i64 @[0]) -> i64 ! {} { 7 }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            Vec.map_in_place(values, ghost);
            0
        }"#,
        "cannot use a callback whose element parameter is graded @[0]",
    );
}

#[test]
fn capturing_closure_adapters_bridge_erased_parameter_arities() {
    agrees(
        r#"fn call(f: once fn(i64) -> i64 ! {alloc, panic}) -> i64 ! {alloc, panic} {
            f(1)
        }
        fn main() -> i64 ! {alloc, panic} {
            let base = 40;
            let f: once fn(i64 @[0]) -> i64 ! {alloc, panic} =
                fn(x: i64 @[0]) -> i64 ! {alloc, panic} { base + 2 };
            call(f)
        }"#,
        42,
        "",
    );
}

#[test]
fn dynamic_dispatch_can_erase_a_copyable_result() {
    agrees(
        r#"trait Compute { fn compute(self: Self) -> i64 @[0] ! {io, panic}; }
        struct A { n: i64 }
        struct B { n: i64 }
        impl Compute for A {
            fn compute(self: Self) -> i64 @[0] ! {io, panic} { print_i64(self.n); self.n }
        }
        impl Compute for B {
            fn compute(self: Self) -> i64 @[0] ! {io, panic} { print_i64(self.n); self.n }
        }
        fn main() -> i64 ! {io, panic, alloc} {
            let object: dyn Compute = A { n: 4 };
            object.compute();
            0
        }"#,
        0,
        "4\n",
    );
}

#[test]
fn dynamic_trait_dispatch_erases_parameter_slots() {
    agrees(
        r#"trait Ignore { fn pick(self: Self, x: i64 @[0]) -> i64 ! {panic}; }
        struct A { n: i64 }
        impl Ignore for A {
            fn pick(self: Self, x: i64 @[0]) -> i64 ! {panic} { self.n }
        }
        fn main() -> i64 ! {io, panic, alloc} {
            let object: dyn Ignore = A { n: 42 };
            object.pick({ print_i64(7); 1 })
        }"#,
        42,
        "7\n",
    );
}

#[test]
fn trait_implementations_must_match_erased_parameter_contracts() {
    rejects(
        r#"trait Pick { fn pick(self: Self, x: i64 @[0]) -> i64 ! {panic}; }
        struct A { n: i64 }
        struct B { n: i64 }
        impl Pick for A { fn pick(self: Self, x: i64 @[0]) -> i64 ! {panic} { self.n } }
        impl Pick for B { fn pick(self: Self, x: i64) -> i64 ! {panic} { self.n + x } }
        fn main() -> i64 ! {panic} { 0 }"#,
        "does not match the trait signature",
    );
}
