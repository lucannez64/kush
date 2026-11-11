//! Deferred overflow checks (`native::deferred`) are unobservable: for every
//! program the reference evaluator, the ordinary native build, and the
//! deferred builds on each available backend print the same output and end
//! the same way, including when an overflow panics.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{
    executable,
    native::{self, Backend, CodegenOptions, LinkSpec, Optimization, Scratch},
};
use std::process::Command;

fn clang_available() -> bool {
    Command::new(std::env::var_os("KUSH_CLANG").unwrap_or_else(|| "clang".into()))
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

fn modes() -> Vec<CodegenOptions> {
    let mut modes = vec![CodegenOptions::default(), CodegenOptions::release()];
    for optimization in [Optimization::None, Optimization::Speed] {
        modes.push(CodegenOptions {
            deferred_overflow: Some(true),
            ..CodegenOptions::cranelift(optimization, true)
        });
    }
    if clang_available() {
        modes.push(CodegenOptions::release_llvm());
        modes.push(CodegenOptions {
            deferred_overflow: Some(false),
            ..CodegenOptions::release_llvm()
        });
        modes.push(CodegenOptions {
            optimization: Optimization::None,
            backend: Backend::Llvm,
            deferred_overflow: Some(true),
            ..CodegenOptions::default()
        });
        modes.push(CodegenOptions {
            native_cpu: true,
            ..CodegenOptions::release_llvm()
        });
    }
    // Planning for the build machine certifies multiply-heavy loops too.
    modes.push(CodegenOptions {
        deferred_overflow: Some(true),
        native_cpu: true,
        ..CodegenOptions::release()
    });
    modes
}

/// A Kush panic: the message, then SIGABRT. A segfault, an arithmetic trap or
/// an illegal instruction is not a panic.
fn assert_panicked(output: &std::process::Output, context: &str) {
    use std::os::unix::process::ExitStatusExt;
    assert_eq!(output.status.signal(), Some(6), "{context}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("panic"),
        "{context}"
    );
}

/// Every native mode agrees with the ordinary build: same output, and a
/// panic where it panics. For programs the evaluator cannot afford to run.
fn native_modes_agree(source: &str) {
    let program = executable::check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let mut reference = None;
    for (at, options) in modes().into_iter().enumerate() {
        let binary = scratch.path().join(format!("agree-{at}"));
        native::build_with_codegen(&program, &binary, false, &LinkSpec::default(), options)
            .unwrap_or_else(|error| panic!("{options:?}: {error:?}\n{source}"));
        let mut child = Command::new(&binary)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        // A deferred loop must report promptly however long it would run.
        let started = std::time::Instant::now();
        while child.try_wait().unwrap().is_none() {
            if started.elapsed() > std::time::Duration::from_secs(30) {
                child.kill().unwrap();
                panic!("{options:?} did not finish\n{source}");
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        let output = child.wait_with_output().unwrap();
        if !output.status.success() {
            assert_panicked(&output, &format!("{options:?}\n{source}"));
        }
        let result = (output.stdout, output.status.success());
        match &reference {
            None => reference = Some(result),
            Some(expected) => assert_eq!(&result, expected, "{options:?}\n{source}"),
        }
    }
}

/// Run on every mode and compare with the evaluator. `None` is a panic.
fn agrees(source: &str, expected: Option<&[i128]>) {
    let program = executable::check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut reference = Vec::new();
    let evaluated = program.evaluate(&mut reference);
    assert_eq!(
        evaluated.is_ok(),
        expected.is_some(),
        "{evaluated:?}\n{source}"
    );
    if let Some(expected) = expected {
        let text: String = expected.iter().map(|value| format!("{value}\n")).collect();
        assert_eq!(String::from_utf8_lossy(&reference), text, "{source}");
    }
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    for (at, options) in modes().into_iter().enumerate() {
        let binary = scratch.path().join(format!("deferred-{at}"));
        native::build_with_codegen(&program, &binary, false, &LinkSpec::default(), options)
            .unwrap_or_else(|error| panic!("{options:?}: {error:?}\n{source}"));
        let output = Command::new(&binary).output().unwrap();
        assert_eq!(
            output.stdout,
            reference,
            "{options:?}\n{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            output.status.success(),
            expected.is_some(),
            "{options:?}\n{source}"
        );
        if expected.is_none() {
            assert_panicked(&output, &format!("{options:?}\n{source}"));
        }
    }
}

const SUM: &str = "
fn sum(view: &[i64]) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = 0;
    while i < Slice.len(view) {
        acc = acc + Slice.get(view, i);
        i = i + 1;
    }
    acc
}";

#[test]
fn reductions_agree_without_overflow() {
    agrees(
        &format!(
            "{SUM}
            fn main() -> Unit ! {{io, panic}} {{
                let values: [i64; 9] = [1, -2, 3, -4, 5, -6, 7, -8, 1000000];
                print_i64(sum(&values[..]));
                print_i64(sum(&values[2..2]));
                print_i64(sum(&values[8..]));
            }}"
        ),
        Some(&[999_996, 0, 1_000_000]),
    );
}

#[test]
fn large_cancelling_operands_take_the_exact_replay() {
    // The magnitude bound cannot prove these sums, and no prefix overflows.
    agrees(
        &format!(
            "{SUM}
            fn main() -> Unit ! {{io, panic}} {{
                let values: [i64; 6] = [
                    9223372036854775807, -9223372036854775807,
                    -9223372036854775807, 9223372036854775807,
                    4611686018427387904, -4611686018427387904,
                ];
                print_i64(sum(&values[..]));
                print_i64(sum(&values[..1]));
                print_i64(sum(&values[4..5]));
            }}"
        ),
        Some(&[0, 9_223_372_036_854_775_807, 4_611_686_018_427_387_904]),
    );
}

#[test]
fn a_prefix_overflow_panics_even_when_the_acc_fits() {
    agrees(
        &format!(
            "{SUM}
            fn main() -> Unit ! {{io, panic}} {{
                let values: [i64; 3] = [9223372036854775807, 1, -5];
                print_i64(7);
                print_i64(sum(&values[..]));
                print_i64(8);
            }}"
        ),
        None,
    );
    agrees(
        &format!(
            "{SUM}
            fn main() -> Unit ! {{io, panic}} {{
                let values: [i64; 3] = [-9223372036854775807, -1, -1];
                print_i64(sum(&values[..]));
            }}"
        ),
        None,
    );
}

#[test]
fn subtraction_right_hand_and_conditional_reductions() {
    let program = |values: &str| {
        format!(
            "fn fold(view: &[i64]) -> i64 ! {{panic}} {{
                let mut down = 0;
                let mut up = 10;
                let mut odd = 0;
                let mut i = 0;
                while i < Slice.len(view) {{
                    down = down - Slice.get(view, i);
                    up = Slice.get(view, i) + up;
                    if i % 2 == 1 {{ odd = odd + Slice.get(view, i); }}
                    i = i + 1;
                }}
                down + up + odd
            }}
            fn main() -> Unit ! {{io, panic}} {{
                let values: [i64; 4] = {values};
                print_i64(fold(&values[..]));
            }}"
        )
    };
    agrees(&program("[5, 7, -9, 11]"), Some(&[-14 + 24 + 18]));
    // `down` reaches i64::MIN exactly, then one more step overflows.
    agrees(&program("[9223372036854775807, 1, 0, 0]"), None);
    agrees(
        &program("[4611686018427387904, 4611686018427387904, 0, 0]"),
        None,
    );
}

#[test]
fn a_zero_trip_loop_keeps_an_extreme_initial_value() {
    agrees(
        "fn keep(view: &[i64], start: i64) -> i64 ! {panic} {
            let mut acc = start;
            let mut i = 0;
            while i < Slice.len(view) {
                acc = acc + Slice.get(view, i);
                i = i + 1;
            }
            acc
        }
        fn main() -> Unit ! {io, panic} {
            let values: [i64; 2] = [1, 2];
            let least = 0 - 9223372036854775807 - 1;
            print_i64(keep(&values[1..1], least));
            print_i64(keep(&values[..], least));
        }",
        Some(&[i128::from(i64::MIN), i128::from(i64::MIN) + 3]),
    );
}

#[test]
fn element_wise_arithmetic_defers_exactly() {
    let program = |values: &str| {
        format!(
            "fn scale(view: &mut [i64]) -> Unit ! {{panic}} {{
                let mut i = 0;
                while i < Slice.len(view) {{
                    Slice.set(view, i, Slice.get(view, i) * 3 - 1);
                    i = i + 1;
                }}
            }}
            fn dot(a: &[i64], b: &[i64]) -> i64 ! {{panic}} {{
                let mut acc = 0;
                let mut i = 0;
                while i < Slice.len(a) {{
                    acc = acc + Slice.get(a, i) * Slice.get(b, i);
                    i = i + 1;
                }}
                acc
            }}
            fn main() -> Unit ! {{io, panic}} {{
                let mut values: [i64; 5] = {values};
                scale(&mut values[..]);
                print_i64(values[0]);
                print_i64(values[4]);
                print_i64(dot(&values[..], &values[..]));
            }}"
        )
    };
    agrees(
        &program("[1, -2, 3, -4, 5]"),
        Some(&[2, 14, 4 + 49 + 64 + 169 + 196]),
    );
    // The third element overflows `* 3`; nothing after the loop may run.
    agrees(&program("[1, 2, 4611686018427387904, 4, 5]"), None);
    // The scaling fits but a product in the reduction does not.
    agrees(&program("[1, 2, 1431655765000000000, 4, 5]"), None);
}

#[test]
fn narrow_and_unsigned_kinds_defer_their_range_checks() {
    let program = |a: &str, b: &str| {
        format!(
            "fn main() -> Unit ! {{io, panic}} {{
                let bytes: [u8; 4] = {a};
                let words: [u64; 3] = {b};
                let view: &[u8] = &bytes[..];
                let wide: &[u64] = &words[..];
                let mut acc: u8 = 0;
                let mut least: i32 = 0;
                let mut i = 0;
                while i < Slice.len(view) {{
                    acc = acc + Slice.get(view, i);
                    least = least - 1000000000;
                    i = i + 1;
                }}
                let mut carry: u64 = 1;
                let mut j = 0;
                while j < Slice.len(wide) {{
                    carry = carry * 2 + Slice.get(wide, j);
                    j = j + 1;
                }}
                print_int(acc);
                print_int(carry);
            }}"
        )
    };
    agrees(&program("[1, 2, 3, 4]", "[1, 0, 1]"), None);
    agrees(
        "fn main() -> Unit ! {io, panic} {
            let bytes: [u8; 4] = [100, 50, 60, 45];
            let words: [u64; 3] = [9223372036854775807, 0, 0];
            let view: &[u8] = &bytes[..];
            let wide: &[u64] = &words[..];
            let mut acc: u8 = 0;
            let mut i = 0;
            while i < Slice.len(view) {
                acc = acc + Slice.get(view, i);
                i = i + 1;
            }
            let mut carry: u64 = 0;
            let mut j = 0;
            while j < Slice.len(wide) {
                carry = carry + Slice.get(wide, j) + Slice.get(wide, j);
                j = j + 1;
            }
            print_int(acc);
            print_int(carry);
        }",
        Some(&[255, 18_446_744_073_709_551_614]),
    );
}

#[test]
fn values_that_steer_the_loop_keep_immediate_checks() {
    // `step` feeds the index, so its overflow must panic before the read.
    agrees(
        "fn walk(view: &[i64]) -> i64 ! {panic} {
            let mut acc = 0;
            let mut step = 4611686018427387904;
            let mut i = 0;
            while i < Slice.len(view) {
                step = step * 2 - step - step;
                acc = acc + Slice.get(view, i + step);
                i = i + 1;
            }
            acc
        }
        fn main() -> Unit ! {io, panic} {
            let values: [i64; 3] = [1, 2, 3];
            print_i64(walk(&values[..]));
        }",
        None,
    );
    // Output inside the loop is an effect: every line before the panic shows.
    let program = executable::check(
        "fn main() -> Unit ! {io, panic} {
            let mut x = 1;
            let mut i = 0;
            while i < 70 {
                x = x * 2;
                print_i64(i);
                i = i + 1;
            }
            print_i64(x);
        }",
    )
    .unwrap();
    let mut reference = Vec::new();
    assert!(program.evaluate(&mut reference).is_err());
    assert_eq!(reference.iter().filter(|byte| **byte == b'\n').count(), 62);
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    for (at, options) in modes().into_iter().enumerate() {
        let binary = scratch.path().join(format!("effects-{at}"));
        native::build_with_codegen(&program, &binary, false, &LinkSpec::default(), options)
            .unwrap();
        let output = Command::new(&binary).output().unwrap();
        assert_eq!(output.stdout, reference, "{options:?}");
        assert!(!output.status.success(), "{options:?}");
    }
}

#[test]
fn deferred_loops_terminate_and_panic_without_a_counter_dependency() {
    // A counted loop whose only overflow is in a value nothing else reads.
    agrees(
        "fn main() -> Unit ! {io, panic} {
            let mut x = 1;
            let mut i = 0;
            while i < 70 {
                x = x * 2;
                i = i + 1;
            }
            print_i64(x);
        }",
        None,
    );
    agrees(
        "fn main() -> Unit ! {io, panic} {
            let mut x = 1;
            let mut y = 0;
            let mut i = 0;
            while i < 62 {
                x = x * 2;
                y = 0 - x;
                if i == 40 { break; }
                i = i + 1;
            }
            print_i64(x);
            print_i64(y);
        }",
        Some(&[1 << 41, -(1 << 41)]),
    );
    // Not counted: the loop relies on the overflow panic to stop.
    agrees(
        "fn main() -> Unit ! {io, panic} {
            let mut x = 1;
            let mut running = true;
            while running {
                x = x * 2;
                if x == 0 { running = false; }
            }
            print_i64(x);
        }",
        None,
    );
}

const SCALE: &str = "
fn scale<'a, 'b>(source: &'a [i64], target: &'b mut [i64], factor: i64) -> Unit ! {panic} {
    let mut i = 0;
    while i < Slice.len(source) {
        Slice.set(target, i, 0 - (Slice.get(source, i) * factor - 7));
        i = i + 1;
    }
}";

#[test]
fn certified_stores_replay_or_panic_like_checked_ones() {
    let program = |values: &str, factor: &str| {
        format!(
            "{SCALE}
            fn main() -> Unit ! {{io, panic}} {{
                let source: [i64; 4] = {values};
                let mut target: [i64; 4] = [1, 1, 1, 1];
                scale(&source[..], &mut target[..], {factor});
                print_i64(target[0]);
                print_i64(target[1]);
                print_i64(target[2]);
                print_i64(target[3]);
            }}"
        )
    };
    agrees(&program("[1, -2, 3, -4]", "5"), Some(&[2, 17, -8, 27]));
    // Too large to certify, yet nothing overflows: the replay must produce
    // every element exactly.
    agrees(
        &program(
            "[4611686018427387904, -4611686018427387904, 3074457345618258602, 1]",
            "1",
        ),
        Some(&[
            -4_611_686_018_427_387_897,
            4_611_686_018_427_387_911,
            -3_074_457_345_618_258_595,
            6,
        ]),
    );
    agrees(
        &program("[1, 2, 3074457345618258602, 4]", "3"),
        Some(&[4, 1, -9_223_372_036_854_775_799, -5]),
    );
    // The same element one step further overflows the multiplication.
    agrees(&program("[1, 2, 3074457345618258603, 4]", "3"), None);
    // Only the final negation overflows: 0 - (i64::MIN).
    agrees(&program("[1, 2, -9223372036854775801, 4]", "1"), None);
}

#[test]
fn in_place_updates_use_exact_tests() {
    let program = |values: &str| {
        format!(
            "fn grow(view: &mut [i64]) -> Unit ! {{panic}} {{
                let mut i = 0;
                while i < Slice.len(view) {{
                    Slice.set(view, i, Slice.get(view, i) * Slice.get(view, i) + i);
                    i = i + 1;
                }}
            }}
            fn main() -> Unit ! {{io, panic}} {{
                let mut values: [i64; 3] = {values};
                grow(&mut values[..]);
                grow(&mut values[..]);
                print_i64(values[0]);
                print_i64(values[1]);
                print_i64(values[2]);
            }}"
        )
    };
    agrees(
        &program("[2, -3, 1000]"),
        Some(&[16, 101, 1_000_004_000_006]),
    );
    agrees(&program("[2, -3, 100000]"), None);
}

#[test]
fn products_locals_and_mixed_kinds_in_one_loop() {
    let program = |values: &str, weights: &str, small: &str| {
        format!(
            "fn blend(a: &[i64], b: &[i64], bytes: &[u8], bias: i64) -> i64 ! {{panic}} {{
                let mut acc = 0;
                let mut low = 0;
                let mut tally: u8 = 0;
                let mut i = 0;
                while i < Slice.len(a) {{
                    let x = Slice.get(a, i);
                    let square = x * x;
                    acc = acc + square * bias - Slice.get(b, i) * x;
                    low = low - (x + bias) * 2;
                    tally = tally + Slice.get(bytes, i);
                    if x == 99 {{ break; }}
                    i = i + 1;
                }}
                acc + low + Int.convert(tally)
            }}
            fn main() -> Unit ! {{io, panic}} {{
                let a: [i64; 4] = {values};
                let b: [i64; 4] = {weights};
                let bytes: [u8; 4] = {small};
                print_i64(blend(&a[..], &b[..], &bytes[..], 3));
            }}"
        )
    };
    // acc = sum(3x^2 - b*x), low = -sum(2(x + 3)), tally = sum(bytes).
    agrees(
        &program("[1, -2, 3, -4]", "[5, 6, 7, 8]", "[10, 20, 30, 40]"),
        Some(&[(3 + 12 + 27 + 48) - (5 - 12 + 21 - 32) - 2 * (4 + 1 + 6 - 1) + 100]),
    );
    // The loop stops at the 99 before the element that would overflow.
    agrees(
        &program("[1, 99, 3037000500, 4]", "[5, 6, 7, 8]", "[10, 20, 30, 40]"),
        Some(&[(3 + 29403) - (5 + 594) - 2 * (4 + 102) + 30]),
    );
    // x * x overflows.
    agrees(
        &program("[1, 2, 3037000500, 4]", "[5, 6, 7, 8]", "[10, 20, 30, 40]"),
        None,
    );
    // Only the narrow tally overflows; the 64-bit certificate holds.
    agrees(
        &program("[1, -2, 3, -4]", "[5, 6, 7, 8]", "[100, 100, 30, 40]"),
        None,
    );
    // The certificate fails (large operands) but nothing overflows.
    agrees(
        &program(
            "[1000000000, -1000000000, 1, 0]",
            "[2000000000, 2000000000, 0, 0]",
            "[1, 2, 3, 4]",
        ),
        Some(&[3_000_000_000_000_000_000 + 3_000_000_000_000_000_000 + 3 - 2 * 13 + 10]),
    );
}

/// The planner really selects the modes the tests above rely on.
#[test]
fn planned_loops_carry_a_certificate_and_rejected_ones_do_not() {
    if !clang_available() {
        return;
    }
    let certified = |source: &str| {
        let program = executable::check(source).unwrap();
        let ir = native::emit_llvm_ir(&program, CodegenOptions::release_llvm()).unwrap();
        let checked = native::emit_llvm_ir(
            &program,
            CodegenOptions {
                deferred_overflow: Some(false),
                ..CodegenOptions::release_llvm()
            },
        )
        .unwrap();
        assert!(!checked.contains("@llvm.ctlz"), "{source}");
        ir.contains("@llvm.ctlz")
    };
    assert!(certified(&format!(
        "{SUM}
        fn main() -> Unit ! {{io, panic}} {{
            let values: [i64; 2] = [1, 2];
            print_i64(sum(&values[..]));
        }}"
    )));
    assert!(certified(&format!(
        "{SCALE}
        fn main() -> Unit ! {{io, panic}} {{
            let source: [i64; 2] = [1, 2];
            let mut target: [i64; 2] = [0, 0];
            scale(&source[..], &mut target[..], 3);
            print_i64(target[1]);
        }}"
    )));
    // Output inside the loop, and a loop that is not counted.
    assert!(!certified(
        "fn main() -> Unit ! {io, panic} {
            let mut x = 1;
            let mut i = 0;
            while i < 10 { x = x * 2; print_i64(x); i = i + 1; }
            let mut running = true;
            while running { x = x + x; if x > 100000 { running = false; } }
            print_i64(x);
        }"
    ));
}

// Programs found by an independent review. Each one panics in an ordinary
// build and used to crash, trap or hang with deferral on.

/// Review finding: a proof that rests on a deferred operation must not license an unchecked read.
#[test]
fn review_oob() {
    native_modes_agree(
        r#"
fn f(view: &[i64], n: i64) -> i64 ! {panic} {
    let mut acc = 0;
    let mut j: i32 = 0;
    let mut i = 0;
    while i <= n {
        let d: i32 = j + 2147483644;
        if 4 <= Slice.len(view) {
            acc = acc + Slice.at(view, Int.convert(j), _);
        }
        j = j + 1;
        i = i + 1;
    }
    acc
}
fn main() -> Unit ! {io, panic} {
    let xs: [i64; 4] = [1, 2, 3, 4];
    print_i64(1);
    print_i64(f(&xs[..], 100000000));
}
"#,
    );
}

/// Review finding: a wrapped narrow value stored and reloaded stays in range.
#[test]
fn review_memidx() {
    native_modes_agree(
        r#"
fn f<'a,'b>(table: &'a Vec<i64>, src: &'b [u16], out: &'b mut [u16]) -> i64 ! {panic} {
    let mut acc = 0;
    let mut i = 0;
    while i < Slice.len(src) {
        Slice.set(out, 0, Slice.get(src, i) * Slice.get(src, i) * Slice.get(src, i));
        let v: u16 = Slice.get(out, 0);
        if 65536 <= Vec.len(table) {
            acc = acc + Vec.at(table, Int.convert(v), _);
        }
        i = i + 1;
    }
    acc
}
fn main() -> Unit ! {io, panic, alloc} {
    let mut table: Vec<i64> = Vec.new();
    let mut k = 0;
    while k < 65536 { table = Vec.push(table, k); k = k + 1; }
    let s: [u16; 3] = [3, 60000, 7];
    let mut o: [u16; 1] = [3];
    print_i64(1);
    print_i64(f(&table, &s[..], &mut o[..]));
}
"#,
    );
}

/// Review finding: a wrapped narrow operand reaches a division in canonical form.
#[test]
fn review_fpe() {
    native_modes_agree(
        r#"
fn f(view: &[i32], d: i32) -> i32 ! {panic} {
    let mut last: i32 = 0;
    let mut i = 0;
    while i < Slice.len(view) {
        let a = Slice.get(view, i);
        last = (a * a * 2) / d;
        i = i + 1;
    }
    last
}
fn main() -> Unit ! {io, panic} {
    let values: [i32; 2] = [1, -2147483648];
    print_i64(1);
    print_int(f(&values[..], -1));
}
"#,
    );
}

/// Review finding: the same for a remainder.
#[test]
fn review_rem() {
    native_modes_agree(
        r#"
fn f(view: &[i32], d: i32) -> i32 ! {panic} {
    let mut last: i32 = 0;
    let mut i = 0;
    while i < Slice.len(view) {
        let a = Slice.get(view, i);
        last = (a * a * 2) % d;
        i = i + 1;
    }
    last
}
fn main() -> Unit ! {io, panic} {
    let values: [i32; 2] = [1, -2147483648];
    print_i64(1);
    print_int(f(&values[..], -1));
}
"#,
    );
}

/// Review finding: an overflow is reported promptly in a loop of 9e18 iterations.
#[test]
fn review_hang3() {
    native_modes_agree(
        r#"
fn spin(view: &[i64], out: &mut [i64], n: i64, start: i64) -> i64 ! {panic} {
    let mut acc = start;
    let mut i = 0;
    while i <= n {
        acc = acc + Slice.get(view, i % 4);
        Slice.set(out, i % 4, acc);
        i = i + 1;
    }
    acc
}
fn main() -> Unit ! {io, panic} {
    let values: [i64; 4] = [1, 2, 3, 4];
    let mut out: [i64; 4] = [1, 2, 3, 4];
    print_i64(1);
    print_i64(spin(&values[..], &mut out[..], 9000000000000000000, 9223372036854775807));
}
"#,
    );
}

/// Review finding: a float counter does not make a loop counted.
#[test]
fn review_float() {
    native_modes_agree(
        r#"
fn f(view: &[i64], start: i64) -> i64 ! {panic} {
    let mut acc = start;
    let mut x = 1.0;
    while x < 2.0 {
        acc = acc + Slice.get(view, 0);
        x = x + 0.00000000000000000000000001;
    }
    acc
}
fn main() -> Unit ! {io, panic} {
    let values: [i64; 2] = [1, 2];
    print_i64(1);
    print_i64(f(&values[..], 9223372036854775800));
}
"#,
    );
}

/// Review finding: a bound reloaded from memory the loop writes.
#[test]
fn review_membound() {
    native_modes_agree(
        r#"
fn f<'a,'b>(a: &'a [i64], out: &'b mut [i64]) -> i64 ! {panic} {
    let mut i = 0;
    while i < Slice.get(out, 0) {
        Slice.set(out, 0, Slice.get(a, i % 2) * 4611686018427387904);
        i = i + 1;
    }
    i
}
fn main() -> Unit ! {io, panic} {
    let a: [i64; 2] = [5, 5];
    let mut o: [i64; 1] = [3];
    print_i64(1);
    print_i64(f(&a[..], &mut o[..]));
}
"#,
    );
}
