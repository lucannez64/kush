use kush::executable::check;

#[test]
fn dependent_graded_higher_order_core_agrees_with_native() {
    let source = include_str!("../../../examples/integrated-core.kush");
    let program = check(source).unwrap();
    let (result, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(result, 42);
    assert_eq!(
        stats.allocations, 2,
        "only the Box and closure environment allocate"
    );
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("integrated-core");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert_eq!(output.status.code(), Some(42));
        assert!(output.stdout.is_empty());
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
