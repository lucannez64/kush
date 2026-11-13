//! STD-BIGNAT: `std.natural` agrees with the kernel's Rust `Natural` on
//! parsing, printing, successor, predecessor, comparison and `i64`
//! conversion, on both backends, and frees every allocation.
use kush::executable::check;
use kush::natural::Natural;
use std::cmp::Ordering;

fn reference(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations, "cleanup");
    String::from_utf8(output).unwrap()
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("naturals");
    kush::native::build(&program, &binary).unwrap();
    let native = std::process::Command::new(&binary).output().unwrap();
    assert_eq!(native.status.code(), Some(0));
    String::from_utf8(native.stdout).unwrap()
}

fn agrees(source: &str) -> String {
    let output = reference(source);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    assert_eq!(native(source), output);
    output
}

const PRELUDE: &str = r#"
use std.io;
use std.natural;
use std.natural.Natural;
use std.option.Option;
use std.result.Result;

fn line(text: &Bytes) -> Unit ! {io, alloc, panic} {
    let mut out = Bytes.with_capacity(Bytes.len(text) + 1);
    let mut i = 0;
    while i < Bytes.len(text) {
        out = Bytes.push(out, Bytes.get(text, i));
        i = i + 1;
    }
    out = Bytes.push(out, 10);
    match io.write(io.stdout(), &out) {
        Result.Ok(_) => {},
        Result.Err(_) => panic(),
    }
}

fn show(n: &Natural) -> Unit ! {io, alloc, panic} {
    line(&natural.format(n));
}

fn report(text: &Bytes, next: &Bytes) -> Unit ! {io, alloc, panic} {
    match natural.parse(text) {
        Result.Err(code) => { print_i64(code); },
        Result.Ok(n) => {
            show(&n);
            print_i64(natural.digits(&n));
            show(&natural.successor(&n));
            match natural.predecessor(&n) {
                Option.Some(m) => { show(&m); },
                Option.None => { line(&Bytes.from("none")); },
            }
            match natural.to_i64(&n) {
                Option.Some(v) => { print_i64(v); },
                Option.None => { line(&Bytes.from("big")); },
            }
            match natural.parse(next) {
                Result.Ok(other) => { print_i64(natural.compare(&n, &other)); },
                Result.Err(code) => { print_i64(code); },
            }
        },
    }
}
"#;

/// What the Kush program prints for one input, computed with the Rust type.
fn expected(text: &str, next: &str) -> String {
    let mut out = String::new();
    let n = match text.parse::<Natural>() {
        Ok(n) => n,
        Err(kush::natural::Error::InvalidDecimal) => return "22\n".into(),
    };
    out += &format!("{n}\n{}\n", n.decimal_digits());
    out += &format!("{}\n", n.successor());
    match n.predecessor() {
        Some(m) => out += &format!("{m}\n"),
        None => out += "none\n",
    }
    match n.to_string().parse::<i64>() {
        Ok(v) => out += &format!("{v}\n"),
        Err(_) => out += "big\n",
    }
    match next.parse::<Natural>() {
        Ok(other) => {
            let (a, b) = (n.to_string(), other.to_string());
            let order = a.len().cmp(&b.len()).then(a.cmp(&b));
            out += match order {
                Ordering::Less => "-1\n",
                Ordering::Equal => "0\n",
                Ordering::Greater => "1\n",
            };
        }
        Err(_) => out += "22\n",
    }
    out
}

#[test]
fn std_natural_agrees_with_the_kernel_naturals() {
    // Values well past the old 4096-digit budget, which no longer exists.
    let nines = "9".repeat(5000);
    let inputs: Vec<String> = [
        "0",
        "000",
        "1",
        "7",
        "999999999",
        "1000000000",
        "1000000001",
        "999999999999999999",
        "1000000000000000000",
        "9223372036854775806",
        "9223372036854775807",
        "9223372036854775808",
        "18446744073709551616",
        "00000000000000000000000000012",
        "340282366920938463463374607431768211456",
        "100000000000000000000000000000000000000000000000000",
        "",
        "12a",
        "-1",
        "+1",
    ]
    .iter()
    .map(|s| s.to_string())
    .chain([nines.clone(), format!("1{}", "0".repeat(5000))])
    .collect();
    let mut body = String::new();
    let mut want = String::new();
    for (index, text) in inputs.iter().enumerate() {
        let next = &inputs[(index + 1) % inputs.len()];
        // Keep the comparison partner well-formed so every line is checked.
        let next = if next.parse::<Natural>().is_ok() {
            next.as_str()
        } else {
            "1000000000"
        };
        body += &format!("    report(&Bytes.from(\"{text}\"), &Bytes.from(\"{next}\"));\n");
        want += &expected(text, next);
    }
    // Copy, equality and from_i64 round out the API.
    body += r#"
    let big = match natural.parse(&Bytes.from("123456789012345678901")) {
        Result.Ok(n) => n,
        Result.Err(_) => return 1,
    };
    let twin = natural.copy(&big);
    print_i64(if natural.equal(&big, &twin) { 1 } else { 0 });
    let small = match natural.from_i64(4000000000) {
        Result.Ok(n) => n,
        Result.Err(_) => return 1,
    };
    show(&small);
    print_i64(natural.work(&small));
    match natural.from_i64(-1) {
        Result.Ok(n) => { show(&n); },
        Result.Err(code) => { print_i64(code); },
    }
    let z = natural.zero();
    print_i64(if natural.is_zero(&z) { 1 } else { 0 });
    print_i64(natural.work(&z));
"#;
    want += "1\n4000000000\n2\n34\n1\n1\n";
    let source =
        format!("{PRELUDE}\nfn main() -> i64 ! {{io, alloc, panic}} {{\n{body}    0\n}}\n");
    assert_eq!(agrees(&source), want);
}
