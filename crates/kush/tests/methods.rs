//! Receiver-style calls to the existing builtin operations. Method syntax is a
//! type-directed spelling of the namespace form; it adds no user-defined
//! methods or traits, and it preserves effects, evaluation order, proofs,
//! loans, and Option/Result shapes.
use kush::executable::check;

const PREFIX: &str = "use std.option.Option;\n";

fn rejects(source: &str, fragment: &str) {
    let source = format!("{PREFIX}{source}");
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
        let binary = scratch.path().join("methods-test");
        kush::native::build(&program, &binary).unwrap();
        return Some(std::process::Command::new(&binary).output().unwrap());
    }
    #[allow(unreachable_code)]
    None
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let source = format!("{PREFIX}{source}");
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

#[test]
fn bytes_vec_and_slice_methods_match_namespace_calls() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let b = Bytes.from(\"AB\");
            print_i64(b.len());
            print_i64(b.capacity());
            print_i64(b.get(1));
            let copy = b.copy();
            print_i64(copy.len());
            let cleared = b.clear();
            print_i64(cleared.len());
            let mut v: Vec<i64> = Vec.new();
            v = v.push(10);
            v = v.push(20);
            print_i64(v.len());
            print_i64(v.get(1));
            v = v.set(0, 7);
            print_i64(v.get(0));
            let view: &[i64] = &v[..];
            print_i64(view.len());
            print_i64(view.get(0));
            match view.try_get(9) {
                Option.Some(_) => print_i64(1),
                Option.None => print_i64(-1),
            }
            0
        }",
        0,
        "2\n2\n66\n2\n0\n2\n20\n7\n2\n7\n-1\n",
    );
}

#[test]
fn string_and_integer_methods_infer_from_the_receiver() {
    agrees(
        "fn main() -> i64 ! {io, alloc, panic} {
            let text = \"hé\";
            print_i64(text.len());
            print_i64(text.scalar_len());
            print_i64(text.byte_at(1));
            match text.scalar_at(1) {
                Option.Some(c) => print_int(c.code()),
                Option.None => print_i64(-1),
            }
            let raw = text.as_bytes();
            print_i64(Bytes.len(&raw));
            let small: u8 = 250;
            print_int(small.wrapping_add(10));
            print_int(small.saturating_add(10));
            match small.checked_add(10) {
                Option.Some(v) => print_int(v),
                Option.None => print_int(-1),
            }
            let wide: u32 = small.convert();
            print_int(wide);
            let narrowed: u8 = wide.truncate();
            print_int(narrowed);
            0
        }",
        0,
        "3\n2\n195\n233\n3\n4\n255\n-1\n250\n250\n",
    );
}

#[test]
fn from_utf8_and_box_methods_preserve_ownership() {
    agrees(
        "use std.result.Result;
        fn main() -> i64 ! {io, alloc, panic} {
            let bytes = Bytes.from(\"ok\");
            match bytes.from_utf8() {
                Result.Ok(text) => print_i64(text.len()),
                Result.Err(b) => print_i64(Bytes.len(&b)),
            }
            let boxed = Box.new(41);
            print_i64(boxed.read());
            let value = boxed.take();
            print_i64(value);
            0
        }",
        0,
        "2\n41\n41\n",
    );
}

#[test]
fn borrowing_methods_require_a_local_owner() {
    rejects(
        "fn make() -> Bytes ! {alloc, panic} { Bytes.from(\"x\") }
        fn main() -> Unit ! {alloc, panic} { make().len(); }",
        "temporary borrows are not supported",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let b = Bytes.from(\"x\"); let c = b.copy(); b = Bytes.from(\"y\"); }",
        "immutable binding",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let b = Bytes.from(\"x\"); let c = b; b.len(); }",
        "cannot borrow a moved owner",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let b = Bytes.from(\"x\"); b.get({ drop(b); 0 }); }",
        "cannot move or drop an owner or view",
    );
}

#[test]
fn non_builtin_record_callable_fields_keep_method_spelling() {
    // Only reserved builtin method names are intercepted. A differently named
    // callable field still uses the ordinary field-projection call path.
    agrees(
        "struct Holder { apply: fn(i64) -> i64 ! {panic} }
        fn main() -> i64 ! {io, panic} {
            let holder = Holder { apply: fn(x: i64) -> i64 ! {panic} { x + 1 } };
            print_i64(holder.apply(41));
            print_i64(holder.apply(0));
            0
        }",
        0,
        "42\n1\n",
    );
}

#[test]
fn method_calls_do_not_bypass_builtin_checks() {
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let v: Vec<i64> = Vec.new(); v.at(0, _); }",
        "cannot prove",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let s = \"abc\"; s.set(0, 1); }",
        "no supported builtin method 'set'",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let v: Vec<i64> = Vec.new(); v.push(); }",
        "after its receiver",
    );
    rejects(
        "fn main() -> Unit ! {alloc, panic} { let b = Bytes.from(\"x\"); b.len::<i64>(); }",
        "takes no type arguments",
    );
}
