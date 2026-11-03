//! Headerless capacity encoding and release byte-append fast paths.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{executable::check, native};
fn compare(source: &str, expected: Option<i64>) {
    let checked = check(source).unwrap();
    let stats_report = match expected {
        Some(value) => {
            let (actual, stats) = checked.evaluate_with_stats(&mut Vec::new()).unwrap();
            assert_eq!(actual, value);
            assert_eq!(stats.allocations, stats.deallocations);
            Some(stats.report())
        }
        None => {
            assert!(checked.evaluate(&mut Vec::new()).is_err());
            None
        }
    };
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    for options in [
        native::CodegenOptions::default(),
        native::CodegenOptions::release(),
    ] {
        let scratch = native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("headerless-buffer");
        native::build_with_codegen(&checked, &binary, true, &Default::default(), options).unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        if let Some(value) = expected {
            assert_eq!(
                output.status.code(),
                Some((value & 255) as i32),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&output.stderr).trim(),
                stats_report.as_deref().unwrap().trim()
            );
        } else {
            assert!(!output.status.success());
            assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
        }
    }
}
#[test]
fn appending_crosses_headerless_and_large_storage_with_correct_contents() {
    compare(
        r#"fn main()->i64 ! {alloc,panic} {
        let mut b=Bytes.with_capacity(0);let mut i=0;
        while i<2048 {b=Bytes.push(b,i%256);i=i+1;}
        let answer=Bytes.get(&b,2047)+Bytes.capacity(&b)-2048;
        drop(b);answer
    }"#,
        Some(255),
    );
}
#[test]
fn fast_append_keeps_the_full_capacity_of_large_buffers() {
    compare(
        r#"fn main()->i64 ! {alloc,panic} {
        let b=Bytes.with_capacity(65537);let b=Bytes.push_reserved(b,42);
        let answer=Bytes.get(&b,0)+Bytes.capacity(&b)-65537;drop(b);answer
    }"#,
        Some(42),
    );
}
#[test]
fn byte_range_checks_run_before_the_fast_store_and_the_growth_path() {
    for capacity in [0, 1, 1009] {
        for value in [-1, 256] {
            compare(
                &format!(
                    "fn main()->Unit ! {{alloc,panic}} {{let b=Bytes.with_capacity({capacity});drop(Bytes.push(b,{value}));}}"
                ),
                None,
            );
        }
    }
}
#[test]
fn reserved_push_checks_logical_capacity_despite_physical_slack() {
    compare(
        r#"#[noalloc] fn append(b:Bytes)->Bytes ! {panic} {Bytes.push_reserved(b,42)}
    fn main()->i64 ! {alloc,panic} {let b=append(Bytes.with_capacity(1));Bytes.get(&b,0)}"#,
        Some(42),
    );
    compare(
        r#"fn main()->Unit ! {alloc,panic} {let b=Bytes.with_capacity(1);let b=Bytes.push_reserved(b,1);drop(Bytes.push_reserved(b,2));}"#,
        None,
    );
}

#[test]
fn inline_byte_access_preserves_bounds_and_clear_capacity() {
    for capacity in [0, 1, 1008, 1009, 65537] {
        compare(
            &format!(
                "fn main()->i64 ! {{alloc,panic}} {{let b=Bytes.with_capacity({capacity});let b=Bytes.push(b,255);let n=Bytes.len(&b);let x=Bytes.get(&b,0);let c=Bytes.capacity(&b);let b=Bytes.clear(b);let answer=n+x+Bytes.len(&b)+Bytes.capacity(&b)-c;drop(b);answer}}"
            ),
            Some(256),
        );
        for index in [-1, 1, i64::MAX] {
            compare(
                &format!(
                    "fn main()->i64 ! {{alloc,panic}} {{let b=Bytes.push(Bytes.with_capacity({capacity}),42);Bytes.get(&b,{index})}}"
                ),
                None,
            );
        }
    }
}
