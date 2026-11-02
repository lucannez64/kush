#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{
    executable,
    native::{self, Scratch},
};
use std::{fs, process::Command};

fn compare(source: &str) {
    let program = executable::check(source).unwrap();
    let mut expected_output = Vec::new();
    let expected_exit = program.evaluate(&mut expected_output).unwrap();
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("program");
    native::build(&program, &binary).unwrap();
    let output = Command::new(&binary)
        .current_dir(scratch.path())
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some((expected_exit as u64 & 255) as i32),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, expected_output);
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(&fs::read(binary).unwrap()[..4], b"\x7fELF");
}
#[test]
fn cranelift_builds_and_runs_first_program() {
    compare(include_str!("../../../examples/first.kush"));
}
#[test]
fn scalar_operator_corpus_matches_reference_execution() {
    compare(
        "fn main() -> Unit ! {io, panic} {
        print_i64(2 + 3 * 4); print_i64(8 - 3 - 1); print_i64(-7 / 3); print_i64(-7 % 3);
        print_i64(-9223372036854775808); print_i64(9223372036854775807);
        print_i64(if !false && 1 < 2 || false { 1 } else { 0 });
        print_i64(if 3 >= 3 && 2 <= 3 && 4 != 5 && () == () { 1 } else { 0 });
        print_i64(match true { false => -1, true => 9 });
        print_i64(match -9223372036854775808 { -9223372036854775808 => 10, _ => 0 });
    }",
    );
}
#[test]
fn forward_calls_return_edges_and_mutable_ssa_values_match_reference() {
    compare(
        "fn main() -> Unit ! {io, panic} {
        print_i64(branch(true)); print_i64(branch(false));
        print_i64(early(0)); print_i64(early(2));
        print_i64(both(true)); print_i64(both(false));
        let mut x = 0;
        print_i64(pair({ x = 1; x }, { x = 2; x }));
        print_i64(x);
    }
    fn branch(flag: Bool) -> i64 ! {} { let mut x = 1; if flag { x = 3; } else { x = 4; } x }
    fn early(n: i64) -> i64 ! {} { if n == 0 { return 5; } n }
    fn both(b: Bool) -> i64 ! {} { if b { return 7; } else { return 8; } }
    fn pair(a: i64, b: i64) -> i64 ! {panic} { a * 10 + b }",
    );
}
#[test]
fn short_circuit_and_guard_side_effects_follow_source_order() {
    compare(
        "fn main() -> Unit ! {io, panic} {
        false && panic(); true || panic();
        let mut x = 0;
        let result = match 3 {
            0 | 1 => 0,
            n if { x = 10; n < 0 } => -1,
            n if { x = x + 1; n > 0 } => n,
            _ => -2,
        };
        print_i64(x); print_i64(result);
        print_i64(match 2 { n if { return; } => n, _ => 0 });
    }",
    );
}
#[test]
fn checked_integer_failures_abort_instead_of_wrapping_or_trapping_silently() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    for expr in [
        "9223372036854775807 + 1",
        "-9223372036854775808 - 1",
        "9223372036854775807 * 2",
        "1 / 0",
        "1 % 0",
        "-9223372036854775808 / -1",
        "-9223372036854775808 % -1",
        "-(-9223372036854775808)",
        "panic()",
    ] {
        let program =
            executable::check(&format!("fn main() -> i64 ! {{panic}} {{ {expr} }}")).unwrap();
        let binary = scratch.path().join("failure");
        native::build(&program, &binary).unwrap();
        let output = Command::new(binary)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert!(!output.status.success(), "{expr}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("panic: checked arithmetic"));
    }
}
#[test]
fn source_and_link_failures_do_not_replace_existing_output() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let source = scratch.path().join("input.kush");
    let output = scratch.path().join("program");
    fs::write(&source, "fn main() -> i64 ! {} { true }").unwrap();
    fs::write(&output, "previous").unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("build")
        .arg(&source)
        .arg("-o")
        .arg(&output)
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert_eq!(fs::read_to_string(&output).unwrap(), "previous");
    let program = executable::check("fn library() -> i64 ! {} { 1 }").unwrap();
    assert!(native::build(&program, &output).is_err());
    assert_eq!(fs::read_to_string(&output).unwrap(), "previous");
    fs::write(&source, "fn main() -> Unit ! {} {}").unwrap();
    // Exercise an actual linker failure without changing the test process's
    // environment or needing unsafe std::env mutation.
    let tools = scratch.path().join("tools");
    fs::create_dir(&tools).unwrap();
    let cc = tools.join("cc");
    fs::write(&cc, "#!/bin/sh\necho forced-link-failure >&2\nexit 23\n").unwrap();
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(&cc, fs::Permissions::from_mode(0o700)).unwrap();
    let linked = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("build")
        .arg(&source)
        .arg("-o")
        .arg(&output)
        .env("PATH", &tools)
        .output()
        .unwrap();
    assert!(!linked.status.success());
    assert!(String::from_utf8_lossy(&linked.stderr).contains("native link failed"));
    assert_eq!(fs::read_to_string(&output).unwrap(), "previous");
    let result = Command::new(env!("CARGO_BIN_EXE_kush"))
        .arg("build")
        .arg(&source)
        .arg("-o")
        .arg(&source)
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(fs::read_to_string(&source).unwrap().contains("fn main"));
}
#[test]
fn run_eval_check_and_build_cli_commands_work() {
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/first.kush");
    for action in ["run", "eval", "check"] {
        let output = Command::new(env!("CARGO_BIN_EXE_kush"))
            .arg(action)
            .arg(&source)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if action == "check" {
            assert!(String::from_utf8_lossy(&output.stdout).contains("executable functions"));
        } else {
            assert_eq!(output.stdout, b"42\n720\n42\n");
        }
    }
    compare("fn main() -> i64 ! {} { -1 }");
}

#[test]
fn enums_results_and_nested_pattern_parser_run_natively() {
    compare(include_str!("../../../examples/results.kush"));
}

#[test]
fn enum_returns_nested_payloads_mutable_joins_and_recursive_calls_match_reference() {
    compare(
        "enum E { Number(i64), Pair(Bool, i64), Nested(Option<i64>, Result<Bool, i64>) }
        enum Option<T> { None, Some(T) } enum Result<T,E> { Ok(T), Err(E) }
        fn choose(flag: Bool) -> E ! {} { if flag { E.Pair(true, 17) } else { E.Number(-7) } }
        fn identity(x: E) -> E ! {} { x }
        fn recur(n: i64) -> E ! {panic} { if n == 0 { return E.Number(88); } recur(n - 1) }
        fn show(x: E) -> i64 ! {} { match x {
            E.Number(n) | E.Pair(_, n) => n,
            E.Nested(Some(n), Ok(true)) => n,
            E.Nested(_, _) => -1,
        } }
        fn main() -> Unit ! {io, panic} {
            let mut x = identity(choose(true)); print_i64(show(x));
            if true { x = choose(false); } else { x = recur(3); }
            print_i64(show(identity(x))); print_i64(show(recur(3)));
            print_i64(show(E.Nested(Some(31), Ok(true))));
            print_i64(show(E.Nested(None, Err(3))));
        }",
    );
}

#[test]
fn nested_alternative_bindings_select_correct_payload_and_preserve_guards() {
    compare(
        "enum E { Left(i64, Bool), Right(Bool, i64), Unit(()) }
        fn f(x: E) -> i64 ! {} { match x {
            E.Left(n, _) | E.Right(_, n) if n > 0 => n,
            E.Left(n, _) | E.Right(_, n) => n,
            E.Unit(()) => 99,
        } }
        fn main() -> Unit ! {io, panic} {
            print_i64(f(E.Left(7, false))); print_i64(f(E.Right(true, 19)));
            print_i64(f(E.Right(true, -5))); print_i64(f(E.Unit(())));
        }",
    );
}

#[test]
fn try_propagates_once_between_different_success_widths_and_reordered_tags() {
    compare(
        "enum Result<T,E> { Err(E), Ok(T) } enum Error { Code(i64, Bool), Empty }
        enum Option<T> { None, Some(T) }
        fn leaf(ok: Bool) -> Result<Bool, Error> ! {io, panic} {
            print_i64(1); if ok { Ok(true) } else { Err(Error.Code(71, true)) }
        }
        fn mapped(ok: Bool) -> Result<Option<i64>, Error> ! {io, panic} {
            let b = leaf(ok)?; print_i64(2);
            Ok(if b { Some(9) } else { None })
        }
        fn show(x: Result<Option<i64>, Error>) -> Unit ! {io, panic} { match x {
            Ok(Some(n)) => print_i64(n), Ok(None) => print_i64(0),
            Err(Error.Code(n, _)) => print_i64(n), Err(Error.Empty) => print_i64(-1),
        } }
        fn main() -> Unit ! {io, panic} { show(mapped(true)); show(mapped(false)); }",
    );
}

#[test]
fn constructors_evaluate_payloads_left_to_right_and_unit_forms_remain_distinct() {
    compare("enum E { Pair(i64, i64), Empty(), Unit }
        fn f(x: E) -> i64 ! {panic} { match x { E.Pair(a,b) => a*10+b, E.Empty() => 8, E.Unit => 9 } }
        fn main() -> Unit ! {io, panic} {
            let mut n = 0; print_i64(f(E.Pair({n=1;n}, {n=2;n}))); print_i64(n);
            print_i64(f(E.Empty())); print_i64(f(E.Unit));
        }");
}

#[test]
fn wide_aggregate_arguments_cross_register_boundaries_and_fill_return_buffers() {
    compare("enum Wide { Tuple(i64,i64,i64,i64,i64,i64,i64,i64), Small(i64) }
        fn pass(a: i64, x: Wide, b: i64) -> Wide ! {io,panic} { print_i64(a); print_i64(b); x }
        fn sum(x: Wide) -> i64 ! {panic} { match x { Wide.Tuple(a,b,c,d,e,f,g,h) => a+b+c+d+e+f+g+h, Wide.Small(n) => n } }
        fn main() -> Unit ! {io,panic} {
            print_i64(sum(pass(91, Wide.Tuple(1,2,3,4,5,6,7,8), 92)));
            print_i64(sum(pass(93, Wide.Small(-9223372036854775808), 94)));
        }");
}

#[test]
fn finite_nested_instantiations_of_the_same_generic_enum_are_not_recursive_layouts() {
    compare(
        "enum Wrap<T> { Item(T) }
        fn make() -> Wrap<Wrap<i64>> ! {} { Item(Item(17)) }
        fn get(x: Wrap<Wrap<i64>>) -> i64 ! {} { match x { Item(Item(n)) => n } }
        fn main() -> Unit ! {io,panic} { print_i64(get(make())); }",
    );
}

#[test]
fn affine_owning_list_and_borrow_example_runs_without_live_allocations() {
    compare(include_str!("../../../examples/ownership.kush"));
}

#[test]
fn partial_constructors_call_arguments_and_error_payloads_are_cleaned_on_early_exit() {
    compare(
        "enum Result<T,E>{Ok(T),Err(E)} enum Pair{Both(Box<i64>,i64)}
        fn fail()->Result<i64,Box<i64>> ! {alloc,panic} {Err(Box.new(7))}
        fn pair(a:Box<i64>,b:i64)->i64 ! {} {Box.take(a)}
        fn first()->Result<i64,Box<i64>> ! {alloc,panic} {
            let local=Box.new(8); let e=Pair.Both(Box.new(1),fail()?); Ok(0)
        }
        fn second()->Result<i64,Box<i64>> ! {alloc,panic} {
            let n=pair(Box.new(1),fail()?); Ok(n)
        }
        fn third()->i64 ! {alloc,panic} {let e=Pair.Both(Box.new(1),return 9);}
        fn main()->Unit ! {io,alloc,panic} {drop(first());drop(second());print_i64(third());}",
    );
}

#[test]
fn owned_match_bindings_are_borrowed_in_guards_and_ignored_fields_drop_once() {
    compare(
        "enum E{A(Box<i64>,Box<i64>),B(Box<i64>)}
        fn f(e:E)->i64 ! {} {match e {
            E.A(b,_) | E.B(b) if Box.read(&b)<0 => Box.take(b),
            E.A(_,b) | E.B(b) => Box.read(&b),
        }} fn main()->Unit ! {io,alloc,panic} {
            print_i64(f(E.A(Box.new(1),Box.new(2))));
            print_i64(f(E.B(Box.new(-5))));
            let unused=E.A(Box.new(3),Box.new(4));
            match unused { _=>() };
        }",
    );
}

#[test]
fn conditional_moves_overwrites_and_reinitialization_have_dynamic_cleanup_flags() {
    compare(
        "fn f(b:Box<i64>,flag:Bool)->i64 ! {} {if flag{return Box.take(b);} Box.read(&b)}
        fn branch(flag:Bool)->i64 ! {alloc,panic} {
            let mut b=Box.new(1); if flag {drop(b);} b=Box.new(2); b=b;
            let c=Box.new(b); let inner=Box.take(c); Box.take(inner)
        }
        fn main()->Unit ! {io,alloc,panic} {
            print_i64(branch(true));print_i64(branch(false));
            print_i64(f(Box.new(7),true));print_i64(f(Box.new(8),false));
            let b=Box.new(1); false && {drop(b); true};
        }",
    );
}

#[test]
fn regular_recursive_generic_and_mutually_boxed_layouts_destruct_correctly() {
    compare("enum List<T>{Nil,Cons(T,Box<List<T>>)}
        enum A{End,Next(Box<Wrap<A>>)} enum Wrap<T>{Item(T)}
        fn make()->List<i64> ! {alloc,panic} {List.Cons(1,Box.new(List.Cons(2,Box.new(List.Nil))))}
        #[noalloc] fn sum(xs:List<i64>)->i64 ! {panic} {match xs {Nil=>0,Cons(n,tail)=>n+sum(Box.take(tail))}}
        fn main()->Unit ! {io,alloc,panic} {
            print_i64(sum(make()));let unused=make();let a=A.Next(Box.new(Wrap.Item(A.End)));
        }");
}

#[test]
fn call_scoped_borrows_keep_owners_live_and_end_before_later_moves() {
    compare(
        "#[noalloc] fn inspect(r:&Box<i64>)->i64 ! {} {Box.read(r)}
        fn combine(a:i64,b:i64)->i64 ! {panic} {a+b}
        fn main()->Unit ! {io,alloc,panic} {
            let b=Box.new(21);
            print_i64(combine(inspect({&b}),Box.take(b)));
            let b=Box.new(7);let c=Box.new(9);print_i64(inspect(if false{&b}else{&c}));
        }",
    );
}

#[test]
fn owning_buffers_preserve_raw_bytes_across_copy_growth_and_nested_cleanup() {
    compare(include_str!("../../../examples/bytes.kush"));
    let mut source = String::from(
        r#"
        enum Holder{Bytes(Bytes),Nested(Box<Bytes>)}
        #[noalloc] fn size(b:&Bytes)->i64 ! {} {Bytes.len(b)}
        fn main()->Unit ! {alloc,panic,io} {
            let empty=Bytes.from("");print_i64(Bytes.len(&empty));
            let source=Bytes.from("é\0");let copy=Bytes.copy(&source);drop(source);
            print_i64(size(&copy));print_i64(Bytes.get(&copy,0));print_i64(Bytes.get(&copy,1));print_i64(Bytes.get(&copy,2));
            let mut b=Bytes.with_capacity(0);
    "#,
    );
    for _ in 0..9 {
        source.push_str("b=Bytes.push(b,255);");
    }
    source.push_str(
        r#"
            print_i64(Bytes.len(&b));print_i64(Bytes.capacity(&b));print_i64(Bytes.get(&b,8));
            let mut b=Bytes.with_capacity(1);b=Bytes.push_reserved(b,0); print_i64(Bytes.get(&b,0));
            let owned=Holder.Bytes(b);let nested=Holder.Nested(Box.new(copy));
        }
    "#,
    );
    compare(&source);
}

#[test]
fn native_expression_parser_matches_reference_for_success_and_partial_tree_errors() {
    let example = include_str!("../../../examples/expression-parser.kush");
    let source = example.replace(
        r#"run(Bytes.from("12 + 3 * 10"));"#,
        r#"
        run(Bytes.from("12 + 3 * 10"));run(Bytes.from("2*3+4"));run(Bytes.from(" 42 \t\r\n"));
        run(Bytes.from(""));run(Bytes.from("1 +"));run(Bytes.from("1 ?"));run(Bytes.from("1+2*3+"));
        run(Bytes.from("9223372036854775807"));run(Bytes.from("9223372036854775808"));
    "#,
    );
    compare(&source);
}

#[test]
fn pending_buffer_arguments_and_error_payloads_are_cleaned_on_early_exit() {
    compare(
        r#"
        enum Result<T,E>{Ok(T),Err(E)} enum Pair{Both(Bytes,Box<Bytes>)}
        fn fail()->Result<i64,Bytes> ! {alloc,panic} {Err(Bytes.from("error"))}
        fn pair()->Result<Pair,Bytes> ! {alloc,panic} {
            let unused=Bytes.from("local");
            Ok(Pair.Both(Bytes.from("pending"),Box.new({fail()?;Bytes.from("unreachable")})))
        }
        fn return_early()->Unit ! {alloc,panic} { Pair.Both(Bytes.from("pending"),{return;}); }
        fn main()->Unit ! {alloc,panic,io} {
            match pair() {Ok(_)=>print_i64(-1),Err(error)=>print_i64(Bytes.len(&error))}
            return_early();
            let b=Box.new(Bytes.from("boxed")); let value=Box.take(b);
            let mut buffer=Bytes.from("old"); buffer=Bytes.from("replacement");
        }
    "#,
    );
}

#[test]
fn native_byte_bounds_and_capacity_failures_abort() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    for body in [
        "Bytes.with_capacity(-1);",
        r#"let b=Bytes.from("");Bytes.get(&b,0);"#,
        r#"let b=Bytes.from("x");Bytes.get(&b,-1);"#,
        r#"let b=Bytes.from("x");Bytes.get(&b,1);"#,
        "Bytes.push(Bytes.with_capacity(0),-1);",
        "Bytes.push(Bytes.with_capacity(0),256);",
        "Bytes.push_reserved(Bytes.with_capacity(0),0);",
        r#"Bytes.push_reserved(Bytes.from("x"),0);"#,
    ] {
        let program =
            executable::check(&format!("fn main()->Unit ! {{alloc,panic}} {{{body}}}")).unwrap();
        let binary = scratch.path().join("failure");
        native::build(&program, &binary).unwrap();
        let result = Command::new(binary)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert!(!result.status.success(), "{body}");
        assert!(
            String::from_utf8_lossy(&result.stderr).contains("panic:"),
            "{body}"
        );
    }
}
