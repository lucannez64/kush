//! IEEE-754 f32/f64 values: contextual literals, arithmetic, comparisons,
//! explicit conversions, printing, and aggregate/callable storage. Every case
//! runs in the reference evaluator and, on Linux x86-64, in a native binary.
use kush::executable::check;

const PRELUDE: &str = "use std.option.Option;\n";

fn rejects(source: &str, fragment: &str) {
    let source = format!("{PRELUDE}{source}");
    let error = check(&source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn native(source: &str) -> Option<std::process::Output> {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("floats-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let source = format!("{PRELUDE}{source}");
    let program = check(&source).unwrap();
    let mut output = Vec::new();
    let status = program.evaluate(&mut output).unwrap();
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    if let Some(output) = native(&source) {
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

/// Both backends must produce the same stdout and exit status. Used for the
/// printing corpus where the shortest decimal is the implementation contract.
fn differential(source: &str) {
    let source = format!("{PRELUDE}{source}");
    let program = check(&source).unwrap();
    let mut expected_output = Vec::new();
    let expected_status = program.evaluate(&mut expected_output).unwrap();
    if let Some(output) = native(&source) {
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            String::from_utf8(expected_output).unwrap()
        );
    }
}

#[test]
fn float_lexing_keeps_projection_and_ranges_intact() {
    use kush::lexer::{Kind, lex};
    let tokens = lex("pair.0 nested.0.1 1..2 1.5 1e3 1.5e-2").unwrap();
    let kinds = tokens
        .into_iter()
        .map(|token| token.kind)
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        vec![
            Kind::Ident("pair".into()),
            Kind::Dot,
            Kind::Integer("0".into()),
            Kind::Ident("nested".into()),
            Kind::Dot,
            Kind::Integer("0".into()),
            Kind::Dot,
            Kind::Integer("1".into()),
            Kind::Integer("1".into()),
            Kind::DotDot,
            Kind::Integer("2".into()),
            Kind::Float("1.5".into()),
            Kind::Float("1e3".into()),
            Kind::Float("1.5e-2".into()),
            Kind::Eof,
        ]
    );
    assert!(lex("1e").is_err());
    assert!(lex("1e+").is_err());
    assert!(lex("12u32").is_err());
}

#[test]
fn float_literals_are_contextual_and_print_their_shortest_form() {
    agrees(
        "fn main() -> i64 ! {io, panic} {
            print_float(1.5);
            print_float(0.1);
            print_float(-0.0);
            print_float(1e20);
            print_float(1.0 / 0.0);
            print_float(-1.0 / 0.0);
            print_float(0.0 / 0.0);
            print_float(3.0);
            let small: f32 = 0.1;
            print_float(small);
            let exact: f32 = 16777216.0;
            print_float(exact);
            0
        }",
        0,
        "1.5\n0.1\n-0\n100000000000000000000\ninf\n-inf\nNaN\n3\n0.1\n16777216\n",
    );
    rejects(
        "fn main() -> i64 ! {} { let x: i64 = 1.5; 0 }",
        "type mismatch",
    );
    rejects(
        "fn main() -> i64 ! {} { let x: f64 = 1; 0 }",
        "type mismatch",
    );
    rejects(
        "fn main() -> i64 ! {io, panic} { print_float(1); 0 }",
        "expects a floating-point value",
    );
    rejects(
        "fn main() -> i64 ! {} { let x: f32 = 3.5e38; 0 }",
        "too large for f32",
    );
    rejects(
        "fn main() -> i64 ! {} { let x = 1e400; 0 }",
        "too large for f64",
    );
    // Underflow is ordinary IEEE rounding, not an error.
    agrees(
        "fn main() -> i64 ! {io, panic} { let x: f64 = 1e-400; print_float(x); 0 }",
        0,
        "0\n",
    );
}

#[test]
fn ieee_arithmetic_comparisons_and_special_values_are_consistent() {
    agrees(
        "fn main() -> i64 ! {io, panic} {
            let x = 1.5;
            let y = 2.0;
            print_float(x + y);
            print_float(x - y);
            print_float(x * y);
            print_float(y / x);
            print_float(x % y);
            print_float(5.0 % 2.0);
            print_float(1.0 % 0.0);
            print_float(-x);
            print_int(if x < y { 1 } else { 0 });
            print_int(if x <= 1.5 { 1 } else { 0 });
            print_int(if x > y { 1 } else { 0 });
            print_int(if -0.0 == 0.0 { 1 } else { 0 });
            let nan = 0.0 / 0.0;
            print_int(if nan == nan { 1 } else { 0 });
            print_int(if nan != nan { 1 } else { 0 });
            print_int(if nan < 1.0 { 1 } else { 0 });
            print_int(if nan >= 1.0 { 1 } else { 0 });
            let f: f32 = 16777216.0;
            print_float(f + 1.0);
            let d = 9007199254740992.0;
            print_float(d + 1.0);
            0
        }",
        0,
        "3.5\n-0.5\n3\n1.3333333333333333\n1.5\n1\nNaN\n-1.5\n1\n1\n0\n1\n0\n1\n0\n0\n16777216\n9007199254740992\n",
    );
    rejects(
        "fn main() -> i64 ! {} { let a: f32 = 1.0; let b: f64 = 2.0; let c = a + b; 0 }",
        "expected f32",
    );
    rejects(
        "fn main() -> i64 ! {} { let a: f64 = 1.0; let c = a & 1.0; 0 }",
        "not bitwise",
    );
    rejects(
        "fn main() -> i64 ! {} { match 1.5 { 1.5 => 1, _ => 0 } }",
        "floating-point literal patterns are not supported",
    );
}

#[test]
fn integer_to_float_conversions_are_explicit_and_exactness_is_checked() {
    agrees(
        "fn show(v: Option<f64>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_float(x), Option.None => print_float(-1.0) }
        }
        fn main() -> i64 ! {io, panic} {
            let n: i32 = 42;
            let m: u16 = 300;
            let a: f64 = Float.from_int(n);
            let b: f32 = Float.from_int(m);
            print_float(a);
            print_float(b);
            print_float(Float.from_int_rounded::<f64>(9007199254740993));
            show(Float.try_from_int::<f64>(9007199254740993));
            show(Float.try_from_int::<f64>(1152921504606846976));
            match Float.try_from_int::<f32>(16777217) {
                Option.Some(x) => print_float(x),
                Option.None => print_float(-1.0),
            };
            match Float.try_from_int::<f32>(16777216) {
                Option.Some(x) => print_float(x),
                Option.None => print_float(-1.0),
            };
            let umax: u64 = u64.MAX;
            show(Float.try_from_int::<f64>(umax));
            0
        }",
        0,
        "42\n300\n9007199254740992\n-1\n1152921504606847000\n-1\n16777216\n-1\n",
    );
    rejects(
        "fn main() -> i64 ! {} { let x: f64 = Float.from_int(9007199254740993); 0 }",
        "cannot represent every i64 value exactly",
    );
    rejects(
        "fn main() -> i64 ! {} { let x: f64 = Float.from_int(1.5); 0 }",
        "expects an integer",
    );
}

#[test]
fn float_to_integer_conversions_truncate_and_reject_out_of_range_values() {
    agrees(
        "fn show_i64(v: Option<i64>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn show_u64(v: Option<u64>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn show_i8(v: Option<i8>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn show_u8(v: Option<u8>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn show_i16(v: Option<i16>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn show_u16(v: Option<u16>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn show_i32(v: Option<i32>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn show_u32(v: Option<u32>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_int(x), Option.None => print_int(-1) }
        }
        fn main() -> i64 ! {io, panic} {
            show_i64(Float.try_to_int::<i64>(3.9));
            show_i64(Float.try_to_int::<i64>(-3.9));
            show_i64(3.9.try_to_int::<i64>());
            show_i64(Float.try_to_int::<i64>(-9223372036854775808.0));
            show_i64(Float.try_to_int::<i64>(9223372036854775808.0));
            show_i64(Float.try_to_int::<i64>(9223372036854774784.0));
            show_i64(Float.try_to_int::<i64>(-9223372036854777856.0));
            show_u64(Float.try_to_int::<u64>(9223372036854775808.0));
            show_u64(Float.try_to_int::<u64>(18446744073709549568.0));
            show_u64(Float.try_to_int::<u64>(18446744073709551616.0));
            show_u64(Float.try_to_int::<u64>(-0.5));
            show_u64(Float.try_to_int::<u64>(0.0 / 0.0));
            show_i64(Float.try_to_int::<i64>(1.0 / 0.0));
            let small: f32 = 255.9;
            show_i64(Float.try_to_int::<i64>(small));
            show_i8(Float.try_to_int::<i8>(-128.9));
            show_i8(Float.try_to_int::<i8>(128.0));
            show_u8(Float.try_to_int::<u8>(255.9));
            show_u8(Float.try_to_int::<u8>(256.0));
            show_i16(Float.try_to_int::<i16>(-32768.5));
            show_i16(Float.try_to_int::<i16>(32768.0));
            show_u16(Float.try_to_int::<u16>(65535.9));
            show_u16(Float.try_to_int::<u16>(65536.0));
            show_i32(Float.try_to_int::<i32>(-2147483648.0));
            show_i32(Float.try_to_int::<i32>(2147483648.0));
            show_u32(Float.try_to_int::<u32>(4294967295.0));
            show_u32(Float.try_to_int::<u32>(4294967296.0));
            0
        }",
        0,
        "3\n-3\n3\n-9223372036854775808\n-1\n9223372036854774784\n-1\n9223372036854775808\n18446744073709549568\n-1\n0\n-1\n-1\n255\n-128\n-1\n255\n-1\n-32768\n-1\n65535\n-1\n-2147483648\n-1\n4294967295\n-1\n",
    );
    rejects(
        "fn main() -> i64 ! {} { let x = Float.try_to_int(1.5); 0 }",
        "needs a target integer type",
    );
    rejects(
        "fn main() -> i64 ! {} { let x = Float.try_to_int::<f64>(1.5); 0 }",
        "needs an integer type argument",
    );
}

#[test]
fn float_width_conversions_and_float_methods_are_explicit() {
    agrees(
        "fn show(v: Option<f32>) -> Unit ! {io, panic} {
            match v { Option.Some(x) => print_float(x), Option.None => print_float(-1.0) }
        }
        fn main() -> i64 ! {io, panic} {
            let small: f32 = 3.25;
            print_float(Float.to_f64(small));
            print_float(Float.to_f64(2.5));
            show(Float.try_to_f32(3.5));
            show(Float.try_to_f32(1e39));
            show(Float.try_to_f32(1.0 / 0.0));
            show(Float.try_to_f32(0.0 / 0.0));
            show(Float.try_to_f32(3.4028235e38));
            show(Float.try_to_f32(3.4028236e38));
            show(Float.try_to_f32(-0.0));
            print_float(Float.abs(-3.5));
            print_float(Float.sqrt(9.0));
            print_float(Float.sqrt(-1.0));
            print_int(if (0.0 / 0.0).is_nan() { 1 } else { 0 });
            print_int(if (1.0 / 0.0).is_infinite() { 1 } else { 0 });
            print_int(if 1.5.is_finite() { 1 } else { 0 });
            let q: f32 = 2.25;
            print_float(q.sqrt());
            0
        }",
        0,
        "3.25\n2.5\n3.5\n-1\ninf\nNaN\n340282350000000000000000000000000000000\n-1\n-0\n3.5\n3\nNaN\n1\n1\n1\n1.5\n",
    );
    rejects(
        "fn main() -> i64 ! {} { let x = Float.try_to_f32::<f64>(1.0); 0 }",
        "takes no type arguments",
    );
}

#[test]
fn floats_flow_through_tuples_records_enums_vectors_generics_and_callables() {
    agrees(
        "struct Holder { value: f64 }
        fn identity<T: Type>(x: T) -> T ! {} { x }
        fn apply(f: fn(f64) -> f64 ! {}, x: f64) -> f64 ! {} { f(x) }
        fn main() -> i64 ! {io, panic, alloc} {
            let pair = (1.5, 2.5);
            print_float(pair.0);
            print_float(pair.1);
            let (a, b) = pair;
            print_float(a + b);
            let holder: Holder = Holder { value: 4.5 };
            print_float(holder.value);
            let mut values: Vec<f64> = Vec.new();
            values = values.push(3.5);
            print_float(values.get(0));
            let arr: [f64; 2] = [1.25, 2.5];
            print_float(arr[0] + arr[1]);
            let number: f64 | i64 = 2.5;
            match number {
                f64 @ x => print_float(x),
                i64 @ n => print_int(n),
            };
            print_float(identity(6.5));
            let doubled = fn(x: f64) -> f64 ! {} { x * 2.0 };
            print_float(apply(doubled, 9.0));
            let opt: Option<f64> = Option.Some(7.5);
            match opt {
                Option.Some(x) => print_float(x),
                Option.None => print_float(0.0),
            };
            0
        }",
        0,
        "1.5\n2.5\n4\n4.5\n3.5\n3.75\n2.5\n6.5\n18\n7.5\n",
    );
}

#[test]
fn native_printing_matches_reference_for_tricky_values() {
    differential(
        "fn main() -> i64 ! {io, panic} {
            print_float(5e-324);
            print_float(1.7976931348623157e308);
            print_float(2.2250738585072014e-308);
            print_float(1.0 / 3.0);
            print_float(0.1 + 0.2);
            print_float(123456789.123456789);
            print_float(1e-7);
            print_float(1e300);
            print_float(-5e-324);
            let a: f32 = 1.0e-45;
            print_float(a);
            let b: f32 = 3.4028235e38;
            print_float(b);
            let c: f32 = 0.1 + 0.2;
            print_float(c);
            let d: f32 = 1.1754944e-38;
            print_float(d);
            0
        }",
    );
}

#[test]
fn floats_are_rejected_as_erased_machine_indices() {
    rejects(
        "fn keep(x: f64, erased same: Eq<f64, x, x>) -> i64 ! {} { 1 }
        fn main() -> i64 ! {panic} { keep(1.5, refl::<f64>(1.5)) }",
        "f64",
    );
}
