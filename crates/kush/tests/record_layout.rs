//! Nominal records have no discriminator; genuine sums and aggregate ABIs do.
use kush::executable::check;

fn agrees(source: &str, expected: i64) {
    let checked = check(source).unwrap();
    let (value, stats) = checked.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(value, expected);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("record-layout");
        kush::native::build(&checked, &binary).unwrap();
        let output = std::process::Command::new(binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn nested_first_fields_and_reference_writes_are_not_tags() {
    agrees(
        r#"
struct Inner { x: i64, y: i64 }
struct Outer { inner: Inner, z: i64 }
fn update(p: &mut Outer) -> i64 ! {panic} {
    p.inner.x = 41;
    p.inner.y = 7;
    p.inner.x + p.inner.y + p.z
}
fn main() -> i64 ! {panic} {
    let mut value = Outer { inner: Inner { x: 3, y: 4 }, z: 9 };
    update(&mut value)
}
"#,
        57,
    );
}

#[test]
fn owning_first_fields_survive_patterns_sums_and_structural_conversion() {
    agrees(
        r#"
struct Pair { first: Box<i64>, second: i64 }
enum Choice { Empty, Full(Pair) }
fn main() -> i64 ! {alloc, panic} {
    let value: Choice = Choice.Full(Pair { first: Box.new(40), second: 2 });
    match value {
        Choice.Empty => 0,
        Choice.Full(pair) => {
            let row: struct { first: Box<i64> } = pair;
            match row { struct { first } => Box.take(first) }
        }
    }
}
"#,
        40,
    );
}

#[test]
fn record_vectors_narrow_and_widen_with_balanced_ownership() {
    agrees(
        r#"
struct Pair { first: i64, second: i64 }
fn unpack(p: Pair) -> i64 ! {panic} { p.first + p.second }
fn main() -> i64 ! {alloc, panic} {
    let values: Vec<Pair> = [Pair { first: 10, second: 11 }];
    let values = Vec.map_in_place(values, unpack);
    let values = Vec.push(values, 7);
    Vec.get(&values, 0) + Vec.get(&values, 1)
}
"#,
        28,
    );
}
