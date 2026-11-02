use kush::executable::check;
fn value(source: &str, expected: i64) {
    let p = check(source).unwrap();
    let (result, stats) = p.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, expected);
    assert_eq!(stats.allocations, stats.deallocations);
}
#[test]
fn generic_functions_specialize_and_records_destructure() {
    value(
        "struct Pair<T>{a:T,b:T} fn id<T>(x:T)->T ! {} {x} fn main()->i64 ! {} {let Pair{a:a,b:b}=Pair{a:id(21),b:id(42)};id(b)}",
        42,
    );
}
#[test]
fn vectors_and_loop_control_preserve_ownership() {
    value(
        "fn main()->i64 ! {alloc,panic} {let mut v:Vec<i64> =Vec.new();let mut i=0;while i<4 {v=Vec.push(v,i);i=i+1;} Vec.get(&v,3)}",
        3,
    );
}
#[test]
fn proved_reads_erase_bounds_obligations() {
    value(
        "fn main()->i64 ! {alloc,panic} {let b=Bytes.from(\"a\");if Bytes.len(&b)>0 {Bytes.at(&b,0,_)} else {0}}",
        97,
    );
    assert!(check("fn f(b:&Bytes,i:i64)->i64 ! {} {Bytes.at(b,i,_)}").is_err());
}
#[test]
fn sibling_branch_versions_are_independent_but_joined_values_lose_old_bounds() {
    value(
        "fn main()->i64 ! {alloc,panic} {let b=Bytes.from(\"a\");let mut i=0;if false {i=2;} else {if i>=0 && i<Bytes.len(&b) {return Bytes.at(&b,i,_);}} 0}",
        97,
    );
    assert!(check("fn main()->i64 ! {alloc,panic} {let b=Bytes.from(\"a\");let mut i=0;if true {i=2;} Bytes.at(&b,i,_)}").is_err());
}
#[test]
fn linear_bindings_must_be_consumed_exactly_once() {
    assert!(check("fn f(x:i64 @[1])->Unit ! {} {}").is_err());
    value(
        "fn f(x:i64 @[1])->i64 ! {} {x} fn main()->i64 ! {} {f(42)}",
        42,
    );
}
#[test]
fn variant_unions_and_intersections_refine_exhaustive_matches() {
    value(
        "enum E{A,B,C} fn f(x:(E.A | E.B) & E)->i64 ! {} {match x {E.A=>1,E.B=>42}} fn main()->i64 ! {} {f(E.B)}",
        42,
    );
    assert!(check("enum E{A,B} fn f(x:E.A)->Unit ! {} {} fn main()->Unit ! {} {f(E.B);}").is_err());
}
#[test]
fn multi_file_calculator_agrees_with_native() {
    use std::{
        io::Write,
        path::Path,
        process::{Command, Stdio},
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/calc.kush");
    let loaded = kush::program::load_path(&root).unwrap();
    let p = kush::executable::check_program(&loaded).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("calc");
    kush::native::build(&p, &binary).unwrap();
    for (input, expected, status) in [
        ("1+2*3", "7\n", 0),
        ("(1+2)*-3", "-9\n", 0),
        ("10/(5-5)", "-300\n", 1),
        ("7 $ 1", "-102\n", 1),
        ("8/2/2-1", "1\n", 0),
    ] {
        let mut out = Vec::new();
        let (actual, stats) = p
            .evaluate_with_io_and_stats(&mut input.as_bytes(), &mut out)
            .unwrap();
        assert_eq!(actual, status);
        assert_eq!(out, expected.as_bytes());
        assert_eq!(stats.allocations, stats.deallocations);
        let mut child = Command::new(&binary)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(input.as_bytes())
            .unwrap();
        let result = child.wait_with_output().unwrap();
        assert_eq!(
            result.status.code(),
            Some(status as i32),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(result.stdout, out);
        assert!(result.stderr.is_empty());
    }
}

#[test]
fn mutations_in_conditions_and_surviving_branches_cannot_forge_bounds() {
    for source in [
        "fn f(b:&Bytes)->i64 ! {} {let mut i=0;if i>=0 && {i=-1;i<Bytes.len(b)} {Bytes.at(b,i,_)} else {0}}",
        "fn f(b:&Bytes)->i64 ! {} {let mut i=0;if i<0 {return 0;} else {i=-1;} if i<Bytes.len(b) {Bytes.at(b,i,_)} else {0}}",
    ] {
        assert!(check(source).is_err());
    }
}

#[test]
fn modules_enforce_visibility_and_supply_standard_result() {
    for public in [true, false] {
        let sources = kush::program::Memory(vec![(
            "helper".into(),
            format!(
                "module helper; {} fn answer()->i64 ! {{}} {{42}}",
                if public { "pub" } else { "" }
            ),
        )]);
        let p = kush::program::load(
            "app.kush",
            "module app;use helper;fn main()->i64 ! {} {helper.answer()}",
            &sources,
        )
        .unwrap();
        let checked = kush::executable::check_program(&p);
        if public {
            assert_eq!(checked.unwrap().evaluate(&mut Vec::new()).unwrap(), 42);
        } else {
            assert!(checked.is_err());
        }
    }
    value("use std.result.Result;fn main()->i64 ! {} {let r:Result<i64,i64>=Ok(42);match r {Ok(n)=>n,Err(e)=>e}}".replace("i64>=","i64> =").as_str(),42);
}

#[test]
fn fixed_arrays_are_inline_typed_and_checked() {
    value(
        "#[noalloc] fn pair()->[i64;2] ! {} {[20,22]} fn main()->i64 ! {panic} {let a=pair();a[0]+a[1]}",
        42,
    );
    value("fn main()->i64 ! {} {let a:[i64;0]=[];42}", 42);
    value(
        "fn main()->i64 ! {} {let a:[[i64;2];2]=[[1,2],[3,42]];let b=a[1];b[1]}",
        42,
    );
    for source in [
        "fn main()->i64 ! {} {let a:[i64;2]=[1];a[0]}",
        "fn main()->i64 ! {} {let a:[i64;1]=[1];a[1]}",
        "fn main()->i64 ! {} {let a:[i64;32]=[];0}",
        "fn main()->i64 ! {alloc,panic} {let a:[Bytes;1]=[Bytes.from(\"x\")];let b=a[0];0}",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
    let p = check("fn main()->i64 ! {alloc,panic} {let a:[Box<i64>;2]=[Box.new(1),Box.new(2)];0}")
        .unwrap();
    let (_, stats) = p.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
}

#[test]
fn array_destructuring_moves_owning_elements() {
    value(
        "fn main()->i64 ! {alloc,panic} {let a:[Box<i64>;2]=[Box.new(20),Box.new(22)];let [x,y]=a;Box.take(x)+Box.take(y)}",
        42,
    );
    assert!(check("fn main()->Unit ! {} {let a:[i64;2]=[1,2];let [x]=a;}").is_err());
}

#[test]
fn inline_arrays_execute_natively_with_owning_cleanup() {
    use std::process::Command;
    let source = "#[noalloc] fn pair()->[i64;2] ! {} {[20,22]} fn main()->i64 ! {alloc,panic} {let p=pair();let a:[Box<i64>;2]=[Box.new(p[0]),Box.new(p[1])];let [x,y]=a;let unused:[Box<i64>;1]=[Box.new(0)];Box.take(x)+Box.take(y)}";
    let p = check(source).unwrap();
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("arrays");
    kush::native::build(&p, &binary).unwrap();
    let result = Command::new(binary).output().unwrap();
    assert_eq!(result.status.code(), Some(42));
    assert!(result.stderr.is_empty());
}
