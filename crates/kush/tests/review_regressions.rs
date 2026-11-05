//! Regression tests for defects confirmed during an independent integration
//! review. These are active regressions for representation and linearity.
use kush::executable::check;

fn checked_ok(source: &str) -> String {
    match check(source) {
        Ok(_) => "accepted".to_owned(),
        Err(error) => format!("rejected: {}", error.message),
    }
}

#[test]
fn inferred_array_argument_coerces_later_elements() {
    // `U` is inferred from the first element (`i64 | Bool`). The second
    // element must still be injected into that union; without the coercion the
    // raw `true` word is stored where a union tag/payload is expected.
    let source = "fn second<U>(xs: [U; 2]) -> U ! {panic} { let [a, b] = xs; b }
        fn main() -> i64 ! {panic} {
            let u: i64 | Bool = 41;
            match second([u, true]) { i64 @ n => n, Bool @ b => if b { 1 } else { 0 } }
        }";
    let program = check(source).unwrap();
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 1);
    assert_eq!(stats.allocations, stats.deallocations);
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn inferred_array_argument_adapts_callable_elements() {
    use std::process::Command;
    let source = "fn second<U>(xs: [U; 2]) -> U ! {panic} { let [a, b] = xs; b }
        fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn make_once() -> once fn(i64) -> i64 ! {panic} ! {alloc, panic} {
            let n = Box.new(100);
            fn(x: i64) -> i64 ! {panic} { Box.take(n) + x }
        }
        fn main() -> i64 ! {alloc, panic} {
            let g = second([make_once(), inc]);
            g(41)
        }";
    let program = check(source).unwrap();
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 42);
    assert_eq!(stats.allocations, stats.deallocations);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("review-array-callable");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(binary).output().unwrap();
    assert_eq!(output.status.code(), Some(42));
}

#[test]
fn loop_break_does_not_launder_graded_owner() {
    for source in [
        // Statement discard.
        "fn main() -> i64 ! {alloc, panic} {
            let b: Box<i64> @[1] = Box.new(1);
            loop { break b; };
            42
        }",
        // Bound to an ungraded local.
        "fn main() -> i64 ! {alloc, panic} {
            let b: Box<i64> @[1] = Box.new(1);
            let g = loop { break b; };
            42
        }",
        // Explicit drop.
        "fn main() -> i64 ! {alloc, panic} {
            let b: Box<i64> @[1] = Box.new(1);
            drop(loop { break b; });
            42
        }",
        // Ungraded function parameter.
        "fn eat(b: Box<i64>) -> i64 ! {alloc, panic} { 42 }
        fn main() -> i64 ! {alloc, panic} {
            let b: Box<i64> @[1] = Box.new(1);
            eat(loop { break b; })
        }",
    ] {
        assert_ne!(checked_ok(source), "accepted", "{source}");
    }
}

#[test]
fn graded_payload_binding_keeps_the_obligation() {
    for source in [
        "enum E { A(Box<i64>) }
        fn f(e: E @[1]) -> i64 ! {alloc, panic} { match e { E.A(x) => 42 } }
        fn main() -> i64 ! {alloc, panic} { f(E.A(Box.new(1))) }",
        "struct P { x: Box<i64> }
        fn f(p: P @[1]) -> i64 ! {alloc, panic} { let P { x } = p; 42 }
        fn main() -> i64 ! {alloc, panic} { f(P { x: Box.new(1) }) }",
        "fn main() -> i64 ! {alloc, panic} {
            let b: Box<i64> @[1] = Box.new(1);
            let u: Box<i64> | i64 = b;
            match u { Box<i64> @ x => 42, i64 @ n => n }
        }",
    ] {
        assert_ne!(checked_ok(source), "accepted", "{source}");
    }
}

#[test]
fn linear_short_circuit_and_loop_break_paths_agree() {
    for source in [
        // Short-circuit right operand consumes the closure only when evaluated.
        "fn f(c: Bool) -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let g: linear once fn() -> i64 ! {panic} = fn() -> i64 ! {panic} { Box.take(n) };
            if c && { g() == 1 } { 42 } else { 0 }
        }
        fn main() -> i64 ! {alloc, panic} { f(false) }",
        // One break consumes the closure, another does not.
        "fn f(c: Bool) -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let g: linear once fn() -> i64 ! {panic} = fn() -> i64 ! {panic} { Box.take(n) };
            loop {
                if c { g(); break 42; }
                break 0;
            }
        }
        fn main() -> i64 ! {alloc, panic} { f(false) }",
        // The loop may execute zero times, so its break-path consumption is conditional.
        "fn f(c: Bool) -> i64 ! {alloc, panic} {
            let n: Box<i64> @[1] = Box.new(1);
            let g: linear once fn() -> i64 ! {panic} = fn() -> i64 ! {panic} { Box.take(n) };
            while c { g(); break; }
            42
        }
        fn main() -> i64 ! {alloc, panic} { f(false) }",
    ] {
        assert_ne!(checked_ok(source), "accepted", "{source}");
    }
}

fn agrees(source: &str, expected: i64) {
    let program = check(source).unwrap();
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, expected);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("review-regression");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn inferred_function_and_record_arrays_coerce_owning_and_scalar_unions_natively() {
    agrees("fn second<U>(xs:[U;2])->U ! {} {let [a,b]=xs;b}
        fn main()->i64 ! {} {let u:i64|Bool=41;match second([u,true]) {i64@n=>n,Bool@b=>if b {1}else{0}}}",1);
    agrees(
        "fn ignore<U>(xs:[U;2])->i64 ! {} {42}
        fn main()->i64 ! {alloc,panic} {let u:Box<i64>|i64=0;ignore([u,Box.new(1)])}",
        42,
    );
    agrees("struct Holder<U>{values:[U;2]}
        fn main()->i64 ! {} {let u:i64|Bool=41;let Holder{values:xs}=Holder{values:[u,true]};let [a,b]=xs;match b {i64@n=>n,Bool@b=>if b {1}else{0}}}",1);
}

#[test]
fn try_and_loop_values_preserve_linear_payloads_and_allow_explicit_consumption() {
    let prefix = "enum Result<T,E>{Ok(T),Err(E)} fn f()->Result<i64,i64> ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let r:Result<Box<i64>,i64>=Ok(b);";
    for ending in ["let g=r?;Ok(0)}", "drop(r?);Ok(0)}"] {
        let source = format!("{}{}", prefix.replace("i64>=", "i64> ="), ending);
        assert!(check(&source).is_err(), "{source}");
    }
    agrees("enum Result<T,E>{Ok(T),Err(E)}
        fn f()->Result<i64,i64> ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let r:Result<Box<i64>,i64> = Ok(b);let g=r?;Ok(Box.take(g))}
        fn main()->i64 ! {alloc,panic} {match f() {Ok(n)=>n,Err(e)=>e}}",42);
    agrees(
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let g:Box<i64> @[1]=loop {break b;};Box.take(g)}",
        42,
    );
}

#[test]
fn type_linear_enums_require_agreement_but_returning_branches_do_not_join() {
    let prefix =
        "#[linear] enum Ticket{Live} fn consume(t:Ticket)->Bool ! {} {match t {Ticket.Live=>true}}";
    for body in [
        "c && consume(t);0",
        "c || consume(t);0",
        "while c {consume(t);break;} 0",
        "loop {if c {consume(t);break;}break;} 0",
    ] {
        let source = format!("{prefix} fn f(c:Bool,t:Ticket)->i64 ! {{}} {{{body}}}");
        assert!(check(&source).is_err(), "{source}");
    }
    agrees(
        &format!(
            "{prefix} fn f(c:Bool,t:Ticket)->i64 ! {{}} {{c && {{consume(t);return 21;}};consume(t);21}} fn main()->i64 ! {{panic}} {{f(true,Ticket.Live)+f(false,Ticket.Live)}}"
        ),
        42,
    );
}

#[test]
fn extracting_a_linear_owned_payload_from_a_box_preserves_its_obligation() {
    let source = "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let wrapped=Box.new(b);let inner=Box.take(wrapped);drop(inner);0}";
    assert!(
        check(source).is_err(),
        "unboxing must not turn a linear payload affine"
    );
    agrees(
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let wrapped=Box.new(b);let inner=Box.take(wrapped);Box.take(inner)}",
        42,
    );
}

#[test]
fn propagated_linear_captures_keep_closure_and_body_obligations() {
    for source in [
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(1);let c=b;fn()->i64 ! {panic} {Box.take(c)};0}",
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(1);let c=b;let f:linear once fn()->i64 ! {alloc,panic}=fn()->i64 ! {alloc,panic} {let d=c;0};f()}",
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(1);let c=loop {break b;};let f=fn()->i64 ! {} {Box.take(c)};drop(f);0}",
        "struct P{x:Box<i64>} fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(1);let p=P{x:b};let P{x}=p;let f=fn()->i64 ! {} {Box.take(x)};0}",
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(1);let mut c=Box.new(2);c=b;let f=fn()->i64 ! {} {Box.take(c)};drop(f);0}",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
    agrees(
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let c=b;let f=fn()->i64 ! {} {Box.take(c)};f()}",
        42,
    );
    agrees(
        "struct P{x:Box<i64>} fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let p=P{x:b};let P{x}=p;let f=fn()->i64 ! {} {Box.take(x)};f()}",
        42,
    );
}

#[test]
fn reordered_record_temporaries_preserve_capture_linearity() {
    agrees(
        "struct P{x:Box<i64>,y:i64} fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let p=P{y:0,x:b};let f=fn()->i64 ! {} {let P{x,y}=p;Box.take(x)};f()}",
        42,
    );
    assert!(check("struct P{x:Box<i64>,y:i64} fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(42);let p=P{y:0,x:b};let f=fn()->i64 ! {} {let P{x,y}=p;Box.take(x)};0}").is_err());
}

#[test]
fn capture_linearity_follows_the_type_graph_without_depth_truncation() {
    let mut source = "#[linear] enum Token{Only}\nenum W0{Item(Box<Token>)}\n".to_owned();
    for i in 1..81 {
        source.push_str(&format!("enum W{i}{{Item(Box<W{}>)}}\n", i - 1));
    }
    source.push_str("fn f(x:W80)->Unit ! {alloc,panic} {fn()->W80 ! {} {x};}");
    assert!(
        check(&source).is_err(),
        "a deep wrapper cannot hide a linear capture"
    );
}

#[test]
fn repeating_paths_cannot_introduce_new_outer_linear_obligations() {
    for action in [
        "let alias=c;drop(alias);",
        "let alias=c;",
        "eat(c);",
        "generic(c);",
        "let f=fn()->i64 ! {} {let x=c;0};f();",
    ] {
        for back_edge in ["", "continue;"] {
            let source = format!(
                "fn eat(b:Box<i64>)->Unit ! {{}} {{}} fn generic<T>(x:T)->Unit ! {{}} {{}} fn main()->i64 ! {{alloc,panic}} {{let mut c=Box.new(0);let mut i=0;while i<2 {{let d:Box<i64> @[1]=Box.new(1);{action}c=d;i=i+1;{back_edge}}}Box.take(c)}}"
            );
            assert!(check(&source).is_err(), "{source}");
        }
    }
    // Even an unavailable binding can receive a new obligation before a back-edge.
    assert!(check("fn main()->i64 ! {alloc,panic} {let mut c=Box.new(0);drop(c);let mut i=0;while i<2 {let d:Box<i64> @[1]=Box.new(1);c=d;i=i+1;}0}").is_err());
    agrees(
        "fn main()->i64 ! {alloc,panic} {let mut c:Box<i64> @[1]=Box.new(0);let mut i=0;while i<2 {let d:Box<i64> @[1]=Box.new(42);let alias=c;Box.take(alias);c=d;i=i+1;}Box.take(c)}",
        42,
    );
    // A guaranteed break is not a repeating path; its replacement stays linear.
    agrees(
        "fn main()->i64 ! {alloc,panic} {let mut c=Box.new(0);loop {let d:Box<i64> @[1]=Box.new(42);Box.take(c);c=d;break;}Box.take(c)}",
        42,
    );
}

#[test]
fn a_record_field_may_hold_functions_of_the_record_itself() {
    // Naming the field type while the record is still being declared used to
    // index its (still empty) field list and panic in the compiler.
    let source = r#"
        struct S { f: [fn(S) -> S ! {}; 1], n: i64 }
        fn bump(s: S) -> S ! {} { S { f: s.f, n: s.n ^ 1 } }
        fn main() -> i64 ! {panic} {
            let s = S { f: [bump], n: 41 };
            let [g] = s.f;
            let t = g(s);
            t.n
        }"#;
    let program = check(source).unwrap();
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 40);
    assert_eq!(stats.allocations, stats.deallocations);
}
