//! Checked user-defined allocators with allocator-owning `AllocBox` and
//! `AllocVec` containers.
//!
//! Every positive case runs in the reference evaluator and, on Linux x86-64,
//! in the native backend. The shared `agrees` helper also asserts balanced
//! allocation counters on both sides.

use kush::executable::{MemoryStats, check};

fn evaluate(source: &str) -> (i64, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(
        stats.allocations, stats.deallocations,
        "cleanup must be balanced: {source}"
    );
    (result, stats)
}

fn value(source: &str) -> i64 {
    evaluate(source).0
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn agrees(source: &str, expected: i64) {
    use std::process::Command;
    let program = check(source).unwrap();
    let (reference, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(reference, expected);
    assert_eq!(stats.allocations, stats.deallocations);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("allocator-containers-test");
    kush::native::build_with_stats(&program, &binary, true).unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some((expected as u64 & 255) as i32),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stats_line = String::from_utf8(output.stderr)
        .unwrap()
        .lines()
        .find(|line| line.starts_with("allocation-stats: "))
        .unwrap()
        .to_owned();
    let field = |name: &str| -> usize {
        stats_line
            .split_whitespace()
            .find_map(|field| field.strip_prefix(name)?.strip_prefix('='))
            .unwrap()
            .parse()
            .unwrap()
    };
    assert_eq!(
        field("allocations"),
        field("deallocations"),
        "{stats_line}\n{source}"
    );
    assert_eq!(
        field("allocations"),
        stats.allocations,
        "{stats_line}\n{source}"
    );
}

const ALLOCATOR: &str = r#"
fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} {
    Bytes.with_capacity(bytes)
}
fn block_free(block: Bytes) -> Unit ! {} {
    drop(block)
}
"#;

#[test]
fn alloc_box_owns_its_allocator_and_reads_and_takes() {
    let source = format!(
        r#"{ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.new(block_alloc, block_free);
            let box = AllocBox.new(allocator, 40);
            AllocBox.read(&box) + AllocBox.take(box)
        }}"#
    );
    let (result, stats) = evaluate(&source);
    assert_eq!(result, 80);
    // One block allocation and one metadata allocation, both released.
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 80);
}

#[test]
fn allocator_binding_may_be_dropped_while_boxes_are_live() {
    let source = format!(
        r#"{ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let box = {{
                let allocator = Allocator.new(block_alloc, block_free);
                AllocBox.new(allocator, 7)
            }};
            AllocBox.read(&box)
        }}"#
    );
    assert_eq!(value(&source), 7);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 7);
}

#[test]
fn alloc_box_try_new_preserves_the_payload_on_refusal() {
    let source = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        fn refuse_alloc(bytes: i64) -> Bytes ! {alloc, panic} {
            if bytes > 0 { Bytes.with_capacity(0) } else { Bytes.with_capacity(bytes) }
        }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn main() -> i64 ! {alloc, panic} {
            let allocator = Allocator.new(refuse_alloc, block_free);
            match AllocBox.try_new(allocator, 7) {
                Ok(box) => AllocBox.take(box),
                Err(payload) => payload + 100
            }
        }"#;
    let (result, stats) = evaluate(source);
    // The 8-byte payload is refused; the empty refusal block is released by
    // the same allocator, so no storage leaks.
    assert_eq!(result, 107);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 107);
}

#[test]
fn alloc_vec_grows_and_releases_through_the_recorded_allocator() {
    let source = format!(
        r#"{ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.new(block_alloc, block_free);
            let vector: AllocVec<i64> = AllocVec.new(allocator);
            let vector = AllocVec.push(vector, 1);
            let vector = AllocVec.push(vector, 2);
            let vector = AllocVec.push(vector, 3);
            let vector = AllocVec.push(vector, 4);
            let vector = AllocVec.set(vector, 1, 20);
            AllocVec.len(&vector) + AllocVec.get(&vector, 1) + AllocVec.get(&vector, 3)
        }}"#
    );
    let (result, stats) = evaluate(&source);
    assert_eq!(result, 28);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 28);
}

#[test]
fn alloc_vec_drops_owning_elements_and_its_block() {
    let source = format!(
        r#"{ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.new(block_alloc, block_free);
            let vector: AllocVec<Box<i64>> = AllocVec.with_capacity(allocator, 2);
            let vector = AllocVec.push(vector, Box.new(1));
            let vector = AllocVec.push(vector, Box.new(2));
            AllocVec.len(&vector)
        }}"#
    );
    let (result, stats) = evaluate(&source);
    assert_eq!(result, 2);
    // Two payload boxes, one vector metadata allocation, one block.
    assert_eq!(stats.allocations, 4);
    assert_eq!(stats.deallocations, 4);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 2);
}

#[test]
fn allocator_values_are_copyable_and_can_be_shared() {
    let source = format!(
        r#"{ALLOCATOR}
        fn make(allocator: Allocator) -> AllocBox<i64> ! {{alloc, panic}} {{
            AllocBox.new(allocator, 5)
        }}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.new(block_alloc, block_free);
            let first = make(allocator);
            let second = make(allocator);
            AllocBox.take(first) + AllocBox.take(second)
        }}"#
    );
    assert_eq!(value(&source), 10);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 10);
}

#[test]
fn hostile_allocator_shapes_are_rejected() {
    rejects(
        r#"
        fn bad_alloc(bytes: i64) -> i64 ! {alloc, panic} { bytes }
        fn main() -> Unit ! {} {
            let allocator = Allocator.new(bad_alloc, bad_alloc);
        }"#,
        "allocation function",
    );
    rejects(
        r#"
        fn block_free(block: Bytes) -> Unit ! {alloc, panic} { drop(block) }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.new(block_free, block_free);
        }"#,
        "allocation function",
    );
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn impure_free(block: Bytes) -> Unit ! {alloc, panic} { drop(block) }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.new(block_alloc, impure_free);
        }"#,
        "release callbacks must have the empty effect row",
    );
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.new(block_alloc, block_free);
            let box = AllocBox.new(allocator, 1);
            let copy = box;
            let again = box;
        }"#,
        "move",
    );
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.new(block_alloc, block_free);
            let box = AllocBox.new(allocator, 1);
            AllocBox.take(AllocBox.take(box));
        }"#,
        "",
    );
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.new(block_alloc, block_free);
            let vector: AllocVec<Box<i64>> = AllocVec.new(allocator);
            let vector = AllocVec.push(vector, Box.new(1));
            AllocVec.get(&vector, 0);
        }"#,
        "owning, linear, and view elements",
    );
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.new(block_alloc, block_free);
            let vector: AllocVec<i64> = AllocVec.new(allocator);
            let first = AllocVec.push(vector, 1);
            let second = AllocVec.push(vector, 2);
        }"#,
        "move",
    );
}

#[test]
fn allocator_bytes_are_not_dyn_array_or_slice_elements() {
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.new(block_alloc, block_free);
            let box = AllocBox.new(allocator, [1, 2, 3]);
            let view: &[i64] = &box[..];
        }"#,
        "cannot slice",
    );
}

#[test]
fn alloc_box_try_new_preserves_an_owning_payload_on_refusal() {
    let source = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        fn refuse_alloc(bytes: i64) -> Bytes ! {alloc, panic} {
            if bytes > 0 { Bytes.with_capacity(0) } else { Bytes.with_capacity(bytes) }
        }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn main() -> i64 ! {alloc, panic} {
            match AllocBox.try_new(Allocator.new(refuse_alloc, block_free), Box.new(41)) {
                Ok(box) => Box.take(AllocBox.take(box)),
                Err(payload) => Box.take(payload)
            }
        }"#;
    let (result, stats) = evaluate(source);
    assert_eq!(result, 41);
    // The supplied payload box plus the empty refusal block; the refusal block
    // is released through the same allocator, so no owner or block leaks.
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 41);
}

#[test]
fn alloc_vec_growth_releases_the_previous_owning_block() {
    let source = format!(
        r#"{ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.new(block_alloc, block_free);
            let vector: AllocVec<Box<i64>> = AllocVec.new(allocator);
            let mut i = 0;
            let mut vector = vector;
            while i < 5 {{
                vector = AllocVec.push(vector, Box.new(i));
                i = i + 1;
            }}
            AllocVec.len(&vector)
        }}"#
    );
    let (result, stats) = evaluate(&source);
    assert_eq!(result, 5);
    // Five payload boxes, one metadata allocation, and the two blocks the
    // growth sequence allocated; the first block is released on growth.
    assert_eq!(stats.allocations, 8);
    assert_eq!(stats.deallocations, 8);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 5);
}
