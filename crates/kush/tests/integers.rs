//! Fixed-width integers, Char, bitwise operators, and explicit conversions.
//! Every case runs in the reference evaluator and natively.
use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let source = format!("use std.option.Option;\n{source}");
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
        let binary = scratch.path().join("integers-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let source = format!("use std.option.Option;\n{source}");
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

/// Both backends must stop with a panic.
fn panics(body: &str) {
    let source = format!("use std.option.Option;\nfn main() -> i64 ! {{io, panic}} {{ {body} }}");
    let program = check(&source).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("panic"), "{source}: {error:?}");
    if let Some(output) = native(&source) {
        assert!(!output.status.success(), "{source} should abort natively");
    }
}

#[test]
fn literals_take_the_contextual_integer_type() {
    agrees(
        "fn add(a: u8, b: u8) -> u8 ! {panic} { a + b }
        fn main() -> i64 ! {io, panic} {
            let small: u8 = 200;
            let wide: u64 = 18446744073709551615;
            let negative: i8 = -128;
            print_int(add(small, 55));
            print_int(wide);
            print_int(negative);
            print_int(u16.MAX);
            print_int(i32.MIN);
            if 0 < small && small > 199 { 1 } else { 0 }
        }",
        1,
        "255\n18446744073709551615\n-128\n65535\n-2147483648\n",
    );
    rejects(
        "fn main() -> i64 ! {} { let x: u8 = 256; 0 }",
        "outside the u8 range",
    );
    rejects(
        "fn main() -> i64 ! {} { let x: u8 = -1; 0 }",
        "outside the u8 range",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let a: u8 = 1; let b: i32 = 2; Int.convert(a + b) }",
        "expected u8, found i32",
    );
    rejects(
        "fn main() -> i64 ! {panic} { let a: u8 = 1; let b = -a; 0 }",
        "cannot negate an unsigned",
    );
}

#[test]
fn arithmetic_is_checked_for_each_width() {
    panics("let x: u8 = 255; let y = x + 1; 0");
    panics("let x: u8 = 0; let y = x - 1; 0");
    panics("let x: i8 = -128; let y = -x; 0");
    panics("let x: i8 = -128; let y = x / -1; 0");
    panics("let x: u32 = 65536; let y = x * x; 0");
    panics("let x: u64 = 18446744073709551615; let y = x + 1; 0");
    panics("let x: u16 = 7; let y: u16 = 0; let z = x % y; 0");
    panics("let x: u8 = 1; let y = x << 8; 0");
    agrees(
        "fn main() -> i64 ! {io, panic} {
            let big: u64 = 18446744073709551614;
            let half: u64 = 9223372036854775808;
            print_int(big / 3);
            print_int(big % 1000);
            print_int(if big > half { 1 } else { 0 });
            let a: i16 = -300;
            print_int(a / 7);
            print_int(a % 7);
            0
        }",
        0,
        "6148914691236517204\n614\n1\n-42\n-6\n",
    );
}

#[test]
fn bitwise_operators_and_shifts() {
    agrees(
        "fn main() -> i64 ! {io, panic} {
            let flags: u8 = 0b1010;
            print_int(flags & 6);
            print_int(flags | 1);
            print_int(flags ^ 255);
            print_int(!flags);
            let one: u8 = 1;
            print_int(one << 7);
            print_int(200 >> 3);
            let negative: i32 = -16;
            print_int(negative >> 2);
            print_int(1 + 2 << 3);
            print_int(!0);
            print_int(0xff + 0o17 + 0b1_0000);
            0
        }",
        0,
        "2\n11\n245\n245\n128\n25\n-4\n24\n-1\n286\n",
    );
}

#[test]
fn explicit_conversions_and_arithmetic_forms() {
    agrees(
        "fn show(o: Option<u8>) -> Unit ! {io, panic} {
            match o { Option.Some(v) => print_int(v), Option.None => print_int(-1) }
        }
        fn main() -> i64 ! {io, panic} {
            let small: u8 = 250;
            let wide: u32 = Int.convert(small);
            print_int(wide);
            show(Int.try_convert(300));
            show(Int.try_convert(42));
            let negative: i64 = -1;
            show(Int.try_convert(negative));
            let truncated: u8 = Int.truncate(300);
            print_int(truncated);
            let signed: i8 = Int.truncate(200);
            print_int(signed);
            print_int(Int.wrapping_add(small, 10));
            print_int(Int.saturating_add(small, 10));
            let low: u8 = 3;
            print_int(Int.saturating_sub(low, 10));
            let neg: i8 = -100;
            print_int(Int.saturating_mul(neg, 2));
            show(Int.checked_mul(small, 2));
            show(Int.checked_sub(small, 50));
            let max: u64 = u64.MAX;
            print_int(Int.wrapping_mul(max, 3));
            0
        }",
        0,
        "250\n-1\n42\n-1\n44\n-56\n4\n255\n0\n-128\n-1\n200\n18446744073709551613\n",
    );
    rejects(
        "fn main() -> i64 ! {} { let a: i64 = 5; let b: u8 = Int.convert(a); 0 }",
        "could lose information",
    );
    rejects(
        "fn main() -> i64 ! {} { let a: u8 = 5; let b = Int.convert(a); 0 }",
        "needs a target integer type",
    );
}

#[test]
fn chars_compare_match_and_convert() {
    agrees(
        "fn classify(c: Char) -> i64 ! {} {
            match c { 'a' => 1, 'é' => 2, _ => if c >= '0' && c <= '9' { 3 } else { 0 } }
        }
        fn main() -> i64 ! {io, panic} {
            print_int(classify('a'));
            print_int(classify('é'));
            print_int(classify('7'));
            print_int(Char.code('€'));
            let surrogate: u32 = 55296;
            match Char.from_code(surrogate) { Option.Some(c) => print_int(1), Option.None => print_int(0) }
            match Char.from_code(65) { Option.Some(c) => print_int(Char.code(c)), Option.None => print_int(0) }
            if 'b' == 'b' && 'a' != 'b' { 0 } else { 1 }
        }",
        0,
        "1\n2\n3\n8364\n0\n65\n",
    );
}

#[test]
fn integer_widths_work_in_generics_patterns_and_collections() {
    agrees(
        "fn first<T>(values: &[T], fallback: T) -> T ! {panic} {
            if Slice.len(values) > 0 { Slice.get(values, 0) } else { fallback }
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let bytes: [u8; 3] = [7, 8, 9];
            print_int(first(&bytes[..], 0));
            let mut v: Vec<u16> = Vec.new();
            v = Vec.push(v, 1000);
            print_int(Vec.get(&v, 0));
            let code: u8 = 10;
            match code { 10 => print_int(1), _ => print_int(0) }
            0
        }",
        0,
        "7\n1000\n1\n",
    );
}
