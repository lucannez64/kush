//! Handler-free callees may omit depth guards but must preserve caller frames.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{executable::check, native};
fn compare(source: &str, expected: Option<i64>) {
    let program = check(source).unwrap();
    let reference = program.evaluate_with_stats(&mut Vec::new());
    match expected {
        Some(value) => {
            let (actual, stats) = reference.unwrap();
            assert_eq!(actual, value);
            assert_eq!(stats.allocations, stats.deallocations);
        }
        None => assert!(
            reference
                .unwrap_err()
                .message
                .contains("no dynamically active handler")
        ),
    }
    for options in [
        native::CodegenOptions::default(),
        native::CodegenOptions::release(),
    ] {
        let scratch = native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("handler-depth");
        native::build_with_codegen(&program, &binary, true, &Default::default(), options).unwrap();
        let output = std::process::Command::new(binary)
            .current_dir(scratch.path())
            .output()
            .unwrap();
        if let Some(value) = expected {
            assert_eq!(
                output.status.code(),
                Some((value & 255) as i32),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        } else {
            assert!(!output.status.success());
            assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
        }
    }
}
#[test]
fn handler_free_worker_preserves_ancestor_handler_across_loop_exits() {
    compare(
        r#"
    effect Op: i64 -> i64;
    fn worker(n:i64)->i64 ! {Op,panic} {
        let mut i=0;let mut sum=0;
        while i<n {i=i+1;if i==2 {continue;}sum=sum+perform Op(i);if i==4 {break;}}
        loop {break sum;}
    }
    fn next()->i64 ! {Op,panic} {perform Op(5)}
    fn main()->i64 ! {panic} {
        handle Op:i64->i64 with fn(x:i64,resume:linear once fn(i64)->i64 ! {})->i64 ! {} {resume(x)} {
            worker(9)+next()
        }
    }"#,
        Some(13),
    );
}
#[test]
fn installer_early_return_cannot_leak_a_handler_into_unguarded_caller() {
    compare(
        r#"
    effect Op:i64->i64;
    fn install()->i64 ! {panic} {
        handle Op:i64->i64 with fn(x:i64,resume:linear once fn(i64)->i64 ! {})->i64 ! {} {resume(x)} {return 1;}
    }
    fn main()->i64 ! {Op,panic} {let x=install();x+perform Op(2)}
    "#,
        None,
    );
}
