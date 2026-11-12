#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{
    executable,
    native::{self, CodegenOptions, LinkSpec, Optimization, Scratch},
};
use std::{fs, process::Command};

const OPTIONS: [CodegenOptions; 4] = [
    CodegenOptions::cranelift(Optimization::None, false),
    CodegenOptions::cranelift(Optimization::Speed, false),
    CodegenOptions::cranelift(Optimization::None, true),
    CodegenOptions::release(),
];
fn agrees(source: &str) {
    let program = executable::check(source).unwrap();
    let mut expected = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut expected).unwrap();
    assert_eq!(stats.allocations, stats.deallocations);
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    for (at, options) in OPTIONS.into_iter().enumerate() {
        let binary = scratch.path().join(format!("release-{at}"));
        native::build_with_codegen(&program, &binary, true, &LinkSpec::default(), options).unwrap();
        let output = Command::new(binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((status as u64 & 255) as i32),
            "{options:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, expected, "{options:?}");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert_eq!(
            stderr
                .lines()
                .find(|line| line.starts_with("allocation-stats:")),
            Some(stats.report().as_str()),
            "{options:?}: {stderr}"
        );
    }
}

#[test]
fn graded_bitwise_maps_and_negative_values_agree_in_all_modes() {
    agrees(
        r#"
        fn mask(x:i64 @[2])->i64 ! {} { (x & 65535) ^ (x & 255) }
        fn tag(x:i64)->i64 ! {} { x ^ 23130 }
        fn main()->Unit ! {io,alloc,panic} {
            let values:Vec<i64> =[-9223372036854775808,-1,0,255,256,9223372036854775807];
            let out=Vec.map_in_place(Vec.map_in_place(values,mask),tag);
            let mut i=0; while i<Vec.len(&out) { print_i64(Vec.get(&out,i)); i=i+1; }
            let empty:Vec<i64> =[]; let empty=Vec.map_in_place(empty,tag); print_i64(Vec.len(&empty));
        }"#,
    );
}
#[test]
fn unsupported_callbacks_preserve_effects_owning_cleanup_and_abi() {
    agrees(
        r#"
        fn noisy(x:i64)->i64 ! {io,panic} { print_i64(x); x+1 }
        fn owning(x:Box<i64>)->i64 ! {} { Box.take(x) }
        fn main()->Unit ! {io,alloc,panic} {
            let values:Vec<i64> =[1,2];
            let mapped=Vec.map_in_place(values,{print_i64(99);noisy});
            print_i64(Vec.get(&mapped,1));
            let owners:Vec<Box<i64>> =[Box.new(4),Box.new(5)];
            let out=Vec.map_in_place(owners,owning); print_i64(Vec.get(&out,1));
        }"#,
    );
}
#[test]
fn erased_proof_linear_and_borrowed_programs_keep_their_contracts() {
    agrees(
        r#"
        prop Approved<key:i64> { Yes:Approved<7> }
        fn issue(key:i64,erased proof:Approved<key>,audit:i64 @[0])->Box<i64> @[1] ! {alloc,panic} {Box.new(key)}
        fn finish(owner:Box<i64> @[1],view:&[i64])->i64 ! {panic} {Box.take(owner)+Slice.get(view,0)}
        fn main()->Unit ! {io,alloc,panic} {
            let owner=issue(7,Approved.Yes::<7>,123);
            let mut values:[i64;2]=[20,30];
            let view=&mut values[..]; Slice.set(view,0,35);
            print_i64(finish(owner,&values[..]));
        }"#,
    );
}
#[test]
fn non_bitwise_callbacks_and_dynamic_handlers_keep_the_fallback_path() {
    agrees(
        r#"
        effect Read:i64->i64;
        fn call(value:i64)->i64 ! {Read,panic} {perform Read(value)}
        fn branch(x:i64)->i64 ! {panic} {if x>0 {x+1}else{0}}
        fn main()->Unit ! {io,alloc,panic} {
            let values:Vec<i64> =[0,1,2]; let out=Vec.map_in_place(values,branch);
            print_i64(Vec.get(&out,2));
            print_i64(handle Read:i64->i64 with fn(value:i64,resume:linear once fn(i64)->i64 ! {})->i64 ! {} {resume(value ^ 1)} {call(42)});
        }"#,
    );
    // Grade contracts also remain unchanged under backend optimization.
    agrees(include_str!("../../../examples/grades.kush"));
}
#[test]
fn aggregate_intermediates_boolean_callbacks_and_delegating_bodies_fall_back() {
    agrees(
        r#"
        struct Pair { a:i64, b:i64 }
        fn split(x:i64)->Pair ! {} {Pair{a:x,b:x ^ 7}}
        fn join(p:Pair)->i64 ! {} {p.a ^ p.b}
        fn tag(x:i64)->i64 ! {} {x ^ 1}
        fn forward(x:i64)->i64 ! {} {tag(x)}
        fn flip(x:Bool)->Bool ! {} {!x}
        fn main()->Unit ! {io,alloc,panic} {
            let values:Vec<i64> = [1,2];
            let out=Vec.map_chain_in_place(values,split,join);
            let out=Vec.map_in_place(Vec.map_in_place(out,forward),tag);
            print_i64(Vec.get(&out,1));
            let flags:Vec<Bool> = [true,false];
            let flags=Vec.map_in_place(flags,flip);
            print_i64(if Vec.get(&flags,1){1}else{0});
        }"#,
    );
}

#[test]
fn release_does_not_remove_arithmetic_or_slice_panics() {
    for source in [
        "fn bad(x:i64)->i64 ! {panic} {x+1} fn main()->i64 ! {alloc,panic} {let v:Vec<i64> =[9223372036854775807];let out=Vec.map_in_place(v,bad);Vec.get(&out,0)}",
        "fn main()->i64 ! {alloc,panic} {let v:Vec<i64> =[1];let view=&v[..];Slice.get(view,2)}",
        "fn bad(v:&[i64])->i64 ! {panic} {let mut i=0-1;while i<Slice.len(v){return Slice.get(v,i);}0} fn main()->i64 ! {panic} {let a:[i64;1]=[1];bad(&a[..])}",
        "fn bad(v:&[i64])->i64 ! {panic} {let mut i=0;while i<Slice.len(v){i=Slice.len(v);return Slice.get(v,i);}0} fn main()->i64 ! {panic} {let a:[i64;1]=[1];bad(&a[..])}",
    ] {
        let program = executable::check(source).unwrap();
        assert!(program.evaluate(&mut Vec::new()).is_err());
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        for (at, options) in OPTIONS.into_iter().enumerate() {
            let binary = scratch.path().join(format!("panic-{at}"));
            native::build_with_codegen(&program, &binary, false, &LinkSpec::default(), options)
                .unwrap();
            let output = Command::new(binary).output().unwrap();
            assert!(!output.status.success(), "{options:?}");
            assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
        }
    }
}
#[test]
fn cli_release_flags_work_for_files_projects_and_argument_forwarding() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    fs::write(
        scratch.path().join("Kush.toml"),
        "[package]\nname=\"release_cli\"\nversion=\"0.1.0\"\nentry=\"main.kush\"\n",
    )
    .unwrap();
    let source = scratch.path().join("main.kush");
    fs::write(&source,"module release_cli; use std.result.Result; fn main()->Unit ! {io,panic} {print_i64(match ENV.arg_count(){Ok(n)=>n,Err(_)=>0});}").unwrap();
    let cli = env!("CARGO_BIN_EXE_kush");
    for args in [
        vec!["run", "--release", "--", "--release"],
        vec!["run", "main.kush", "--release", "--", "--release"],
    ] {
        let out = Command::new(cli)
            .args(args)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(out.stdout, b"2\n");
    }
    for flags in [
        vec!["--release"],
        vec!["--opt-level", "speed", "--no-inline-scalars"],
        vec!["--inline-scalars"],
    ] {
        let out = Command::new(cli)
            .args(["build", "main.kush", "-o", "output"])
            .args(flags)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    for args in [
        vec!["eval", "main.kush", "--release"],
        vec!["build", "--opt-level", "wrong"],
        vec!["build", "main.kush", "-o", "output", "--opt-level"],
    ] {
        let out = Command::new(cli)
            .args(args)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2));
    }
}

#[test]
fn push_fast_paths_cover_growth_borrowed_owners_and_narrowed_vectors() {
    agrees(
        r#"
        struct Pair { left:Box<i64>, right:Box<i64> }
        fn narrow(x:[i64;2])->i64 ! {} {x[0]}
        fn main()->Unit ! {alloc,panic,io} {
            let mut values:Vec<i64> =Vec.with_capacity(1);
            let mut i=0; while i<20 { values=Vec.push(values,i); i=i+1; }
            Vec.push(&mut values,42); print_i64(Vec.get(&values,20));
            let mut pairs:Vec<Pair> =Vec.with_capacity(1);
            pairs=Vec.push(pairs,Pair{left:Box.new(1),right:Box.new(2)});
            Vec.push(&mut pairs,Pair{left:Box.new(3),right:Box.new(4)});
            Vec.clear(&mut pairs);
            Vec.push(&mut pairs,Pair{left:Box.new(5),right:Box.new(6)});
            let wide:Vec<[i64;2]> =[[7,8],[9,10]];
            let mut small=Vec.map_in_place(wide,narrow);
            small=Vec.push(small,11); print_i64(Vec.get(&small,2));
        }
    "#,
    );
}

#[test]
fn slice_loop_versions_preserve_byte_views_mutation_and_control_flow() {
    agrees(
        r#"
        fn sum(view:&[i64])->i64 ! {panic} {
            let mut result=0; let mut i=0;
            while i<Slice.len(view) { result=result+Slice.get(view,i); i=i+1; }
            result
        }
        fn edit(view:&mut [i64])->i64 ! {panic} {
            let mut i=0;
            while i<Slice.len(view) {
                Slice.set(view,i,Slice.get(view,i)+1);
                i=i+1; if i==2 {continue;} if i==3 {break;}
            }
            i
        }
        fn main()->Unit ! {alloc,panic,io} {
            let mut bytes=Bytes.from("ABC"); print_i64(sum(&bytes[..]));
            print_i64(edit(&mut bytes[..])); print_i64(sum(&bytes[..]));
            let mut array:[i64;4]=[10,20,30,40];
            print_i64(sum(&array[..])); print_i64(edit(&mut array[..]));
            print_i64(sum(&array[..]));
            let empty:Vec<i64> =[]; print_i64(sum(&empty[..]));
        }
    "#,
    );
}

/// kush-kv: with speed optimization `Vec.len` is an inline header load
/// (checked `Vec.get`/`Vec.set` stay runtime calls, see
/// docs/native-optimizations.md). Values, multi-word and owning elements
/// agree in every mode, and an index outside `0 .. len` (negative or too
/// large) still panics.
#[test]
fn inline_vector_access_keeps_values_and_bounds_checks() {
    agrees(
        r#"
        struct Loc { offset: i64, length: i64, seq: u64, deleted: Bool }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut v: Vec<i64> = [5, 6, 7];
            v = Vec.set(v, 1, 60);
            let mut locs: Vec<Loc> = Vec.with_capacity(2);
            locs = Vec.push(locs, Loc { offset: 1, length: 2, seq: 3, deleted: false });
            locs = Vec.push(locs, Loc { offset: 4, length: 5, seq: 6, deleted: true });
            locs = Vec.set(locs, 0, Loc { offset: 10, length: 20, seq: 30, deleted: true });
            let a = Vec.get(&locs, 0);
            let b = Vec.get(&locs, 1);
            let mut owned: Vec<Bytes> = Vec.with_capacity(2);
            owned = Vec.push(owned, Bytes.from("a"));
            owned = Vec.set(owned, 0, Bytes.from("bc"));
            print_i64(Vec.len(&v) + Vec.get(&v, 1) + Vec.get(&v, 2));
            print_i64(a.offset + a.length + Int.truncate(a.seq) + (if a.deleted { 1 } else { 0 }));
            print_i64(b.offset + (if b.deleted { 100 } else { 0 }));
            print_i64(Vec.len(&owned));
            drop(owned);
        }
        "#,
    );
    for access in [
        "Vec.get(&v, 3)",
        "Vec.get(&v, -1)",
        "Vec.get(&Vec.set(v, 3, 1), 0)",
        "Vec.get(&Vec.set(v, -1, 1), 0)",
    ] {
        let source = format!(
            "fn main() -> i64 ! {{alloc, panic}} {{ let v: Vec<i64> = [1, 2, 3]; {access} }}"
        );
        let program = executable::check(&source).unwrap();
        assert!(program.evaluate(&mut Vec::new()).is_err());
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        for (at, options) in OPTIONS.into_iter().enumerate() {
            let binary = scratch.path().join(format!("vec-panic-{at}"));
            native::build_with_codegen(&program, &binary, false, &LinkSpec::default(), options)
                .unwrap();
            let output = Command::new(binary).output().unwrap();
            assert!(!output.status.success(), "{access} {options:?}");
            assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
        }
    }
}
