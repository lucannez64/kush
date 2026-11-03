//! Root/loan invariants that variance, recursive summaries and rows must retain.
use kush::executable::check;
fn rejects(source: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains("cannot replace an owner"),
        "{error:?}"
    );
}
#[test]
fn ending_one_shared_borrow_does_not_release_another_views_owner() {
    rejects(
        r#"fn main()->i64 ! {panic} {
        let mut data:[i64;2]=[40,2];let first=&data[..];let second=&data[..];
        drop(first);data=[9,9];Slice.get(second,0)
    }"#,
    );
}
#[test]
fn reordered_structural_leaf_keeps_its_source_owner() {
    rejects(
        r#"struct Window<'a>{start:i64,view:&'a [i64]}
    fn main()->i64 ! {panic} {
        let mut data:[i64;2]=[40,2];let w=Window{start:0,view:&data[..]};
        let narrowed:struct{view:&[i64]}=w;
        match narrowed {struct{view}=>{data=[9,9];Slice.get(view,0)}}
    }"#,
    );
}
#[test]
fn inferred_intersection_result_keeps_every_possible_owner() {
    for owner in ["left", "right"] {
        rejects(&format!(
            r#"
        fn choose<'a,'b>(a:&'a [i64],b:&'b [i64],pick:Bool)->&[i64] ! {{}} {{if pick {{a}} else {{b}}}}
        fn main()->i64 ! {{panic}} {{
            let mut left:[i64;2]=[40,2];let mut right:[i64;2]=[3,4];
            let result=choose(&left[..],&right[..],true);
            {owner}=[9,9];Slice.get(result,0)
        }}"#
        ));
    }
}
#[test]
fn shared_copy_loan_ends_after_the_last_surviving_view_use() {
    let program = check(
        r#"fn main()->i64 ! {panic} {
        let mut data:[i64;2]=[40,2];let first=&data[..];let second=first;
        let answer=Slice.get(second,0);drop(first);data=[2,3];answer+data[0]
    }"#,
    )
    .unwrap();
    let (value, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, 42);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    for options in [
        kush::native::CodegenOptions::default(),
        kush::native::CodegenOptions::release(),
    ] {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("lifetime-baseline");
        kush::native::build_with_codegen(&program, &binary, true, &Default::default(), options)
            .unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(42),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn shared_derived_view_keeps_its_parent_binding_live() {
    let error = check(
        r#"fn main()->i64 ! {panic} {
        let data:[i64;2]=[40,2];let parent=&data[..];let child=parent;
        drop(parent);Slice.get(child,0)
    }"#,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("cannot move or drop an owner or view"),
        "{error:?}"
    );
}
