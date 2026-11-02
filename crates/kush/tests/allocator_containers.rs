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

/// Task programs add scheduler bookkeeping allocations, so this helper checks
/// the result, balanced cleanup, and native exit status without requiring the
/// reference and native allocation counts to match byte-for-byte.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn agrees_task(source: &str, expected: i64) {
    use std::process::Command;
    let program = check(source).unwrap();
    let (reference, stats) = program.evaluate_with_stats(&mut Vec::new()).unwrap();
    assert_eq!(reference, expected);
    assert_eq!(stats.allocations, stats.deallocations);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("allocator-context-task-test");
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
    assert_eq!(field("allocations"), field("deallocations"), "{stats_line}");
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

#[test]
fn alloc_containers_reject_borrowed_and_linear_elements() {
    rejects(
        &format!(
            r#"{ALLOCATOR}
            fn main() -> i64 ! {{alloc, panic}} {{
                let allocator = Allocator.new(block_alloc, block_free);
                let mut v: AllocVec<&str> = AllocVec.new(allocator);
                {{
                    let s = "abcd";
                    v = AllocVec.push(v, s.as_str());
                }}
                let t: &str = AllocVec.get(&v, 0);
                Str.len(t)
            }}"#
        ),
        "cannot hold a borrowed reference",
    );
    rejects(
        &format!(
            r#"{ALLOCATOR}
            struct Point {{ x: i64 }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let allocator = Allocator.new(block_alloc, block_free);
                let p = Point {{ x: 40 }};
                let mut v: AllocVec<&Point> = AllocVec.new(allocator);
                v = AllocVec.push(v, &p);
                0
            }}"#
        ),
        "cannot hold a borrowed reference",
    );
    rejects(
        &format!(
            r#"{ALLOCATOR}
            #[linear]
            enum Ticket {{ Live }}
            fn main() -> i64 ! {{alloc, panic}} {{
                let allocator = Allocator.new(block_alloc, block_free);
                let v: AllocVec<Ticket> = AllocVec.new(allocator);
                0
            }}"#
        ),
        "linear",
    );
}

const GROWING_ALLOCATOR: &str = r#"
fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} {
    Bytes.with_capacity(bytes)
}
fn block_free(block: Bytes) -> Unit ! {} {
    drop(block)
}
fn block_grow(block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
    let mut out = Bytes.with_capacity(bytes);
    let mut i = 0;
    while i < old_bytes {
        out = Bytes.push(out, Bytes.get(&block, i));
        i = i + 1;
    }
    drop(block);
    out
}
"#;

#[test]
fn alloc_vec_growth_uses_a_realloc_hook_and_preserves_elements() {
    let source = format!(
        r#"{GROWING_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.with_realloc(block_alloc, block_free, block_grow);
            let vector: AllocVec<i64> = AllocVec.new(allocator);
            let vector = AllocVec.push(vector, 1);
            let vector = AllocVec.push(vector, 2);
            let vector = AllocVec.push(vector, 3);
            let vector = AllocVec.push(vector, 4);
            let vector = AllocVec.push(vector, 5);
            AllocVec.len(&vector) + AllocVec.get(&vector, 0) + AllocVec.get(&vector, 4)
        }}"#
    );
    let (result, stats) = evaluate(&source);
    assert_eq!(result, 11);
    // The growth hook allocates through the same allocator, so every block is
    // still released through the recorded release callback exactly once.
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 11);
}

#[test]
fn alloc_vec_try_push_reports_refusal_and_preserves_state() {
    let source = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn refuse_alloc(bytes: i64) -> Bytes ! {alloc, panic} {
            if bytes > 32 { Bytes.with_capacity(0) } else { Bytes.with_capacity(bytes) }
        }
        fn push_ok(v: AllocVec<i64>, x: i64) -> AllocVec<i64> ! {alloc, panic} {
            match AllocVec.try_push(v, x) {
                Ok(vector) => vector,
                Err(pair) => match pair { (vector, _) => vector }
            }
        }
        fn main() -> i64 ! {alloc, panic} {
            let allocator = Allocator.new(refuse_alloc, block_free);
            let v: AllocVec<i64> = AllocVec.new(allocator);
            let v = push_ok(v, 1);
            let v = push_ok(v, 2);
            let v = push_ok(v, 3);
            let v = push_ok(v, 4);
            match AllocVec.try_push(v, 5) {
                Ok(vector) => 100 + AllocVec.len(&vector),
                Err(pair) => match pair {
                    (vector, refused) =>
                        AllocVec.len(&vector) * 10 + AllocVec.get(&vector, 0) + refused
                }
            }
        }"#;
    let (result, stats) = evaluate(source);
    // Four elements survive, the fifth is returned untouched, and the refused
    // empty block is released through the same allocator.
    assert_eq!(result, 40 + 1 + 5);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 46);
}

#[test]
fn alloc_vec_try_push_returns_the_owning_element_on_refusal() {
    let source = r#"
        enum Result<T, E> { Ok(T), Err(E) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn refuse_alloc(bytes: i64) -> Bytes ! {alloc, panic} {
            if bytes > 8 { Bytes.with_capacity(0) } else { Bytes.with_capacity(bytes) }
        }
        fn main() -> i64 ! {alloc, panic} {
            let allocator = Allocator.new(refuse_alloc, block_free);
            let v: AllocVec<Box<i64>> = AllocVec.new(allocator);
            let v = match AllocVec.try_push(v, Box.new(1)) {
                Ok(vector) => vector,
                Err(_) => {
                    let empty: AllocVec<Box<i64>> = AllocVec.with_capacity(allocator, 1);
                    empty
                }
            };
            let v = AllocVec.push(v, Box.new(2));
            match AllocVec.try_push(v, Box.new(41)) {
                Ok(vector) => AllocVec.len(&vector),
                Err(pair) => match pair { (vector, box) => Box.take(box) + AllocVec.len(&vector) }
            }
        }"#;
    let (result, stats) = evaluate(source);
    // Two payload boxes are live through the vector and one through the
    // refused element; every payload and block is released exactly once.
    assert_eq!(result, 41 + 1);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 42);
}

#[test]
fn alloc_vec_pop_returns_the_last_copyable_element() {
    let source = format!(
        r#"{ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.new(block_alloc, block_free);
            let vector: AllocVec<i64> = AllocVec.with_capacity(allocator, 2);
            let vector = AllocVec.push(vector, 10);
            let vector = AllocVec.push(vector, 20);
            let (vector, last) = AllocVec.pop(vector);
            let (vector, first) = AllocVec.pop(vector);
            AllocVec.len(&vector) + first + last
        }}"#
    );
    let (result, stats) = evaluate(&source);
    assert_eq!(result, 30);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 30);
    let empty = format!(
        r#"{ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.new(block_alloc, block_free);
            let vector: AllocVec<i64> = AllocVec.new(allocator);
            let (vector, _) = AllocVec.pop(vector);
            AllocVec.len(&vector)
        }}"#
    );
    let program = check(&empty).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("AllocVec is empty"), "{error:?}");
}

#[test]
fn allocator_growth_hook_contracts_are_checked() {
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn bad_grow(block: Bytes) -> Bytes ! {alloc, panic} { block }
        fn main() -> Unit ! {alloc, panic} {
            let allocator = Allocator.with_realloc(block_alloc, block_free, bad_grow);
        }"#,
        "growth function",
    );
    rejects(
        r#"
        fn block_alloc(bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
        fn block_free(block: Bytes) -> Unit ! {} { drop(block) }
        fn impure_grow(block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic, io} {
            let _ = block;
            let _ = old_bytes;
            Bytes.with_capacity(bytes)
        }
        fn main() -> Unit ! {alloc, panic, io} {
            let allocator = Allocator.with_realloc(block_alloc, block_free, impure_grow);
        }"#,
        "growth callbacks may only declare",
    );
    // A growth hook that returns a block smaller than the request is a panic,
    // never a partially moved vector.
    let short = format!(
        r#"{ALLOCATOR}
        fn short_grow(block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {{alloc, panic}} {{
            let _ = old_bytes;
            drop(block);
            Bytes.with_capacity(0)
        }}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.with_realloc(block_alloc, block_free, short_grow);
            let vector: AllocVec<i64> = AllocVec.new(allocator);
            let vector = AllocVec.push(vector, 1);
            let vector = AllocVec.push(vector, 2);
            let vector = AllocVec.push(vector, 3);
            let vector = AllocVec.push(vector, 4);
            let vector = AllocVec.push(vector, 5);
            AllocVec.len(&vector)
        }}"#
    );
    let program = check(&short).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(error.message.contains("smaller than"), "{error:?}");
    // The fallible append ignores the growth hook by design, so a refusal can
    // preserve the vector even when a hook exists.
    let fallible = format!(
        r#"enum Result<T, E> {{ Ok(T), Err(E) }}
        {GROWING_ALLOCATOR}
        fn refuse_alloc(bytes: i64) -> Bytes ! {{alloc, panic}} {{
            if bytes > 8 {{ Bytes.with_capacity(0) }} else {{ Bytes.with_capacity(bytes) }}
        }}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator =
                Allocator.with_realloc(refuse_alloc, block_free, block_grow);
            let vector: AllocVec<i64> = AllocVec.with_capacity(allocator, 1);
            let vector = AllocVec.push(vector, 1);
            match AllocVec.try_push(vector, 2) {{
                Ok(vector) => AllocVec.len(&vector),
                Err(pair) => match pair {{ (vector, x) => x + AllocVec.len(&vector) }}
            }}
        }}"#
    );
    let (result, stats) = evaluate(&fallible);
    assert_eq!(result, 3);
    assert_eq!(stats.allocations, stats.deallocations);
    // The allocation callback may panic, so a fallible append still requires
    // the caller to declare `panic` as well as `alloc`.
    rejects(
        r#"
        enum Result<T, E> { Ok(T), Err(E) }
        fn push(v: AllocVec<i64>) -> i64 ! {alloc} {
            match AllocVec.try_push(v, 1) {
                Ok(vector) => AllocVec.len(&vector),
                Err(pair) => match pair { (vector, _) => AllocVec.len(&vector) }
            }
        }
        fn main() -> Unit ! {} {}"#,
        "requires effects {panic}",
    );
    // Pop copies its element, so owning elements must be consumed explicitly.
    rejects(
        &format!(
            r#"{ALLOCATOR}
            fn main() -> i64 ! {{alloc, panic}} {{
                let allocator = Allocator.new(block_alloc, block_free);
                let vector: AllocVec<Box<i64>> = AllocVec.new(allocator);
                let (vector, _) = AllocVec.pop(vector);
                AllocVec.len(&vector)
            }}"#
        ),
        "copies its element",
    );
}

#[test]
fn realloc_callback_expressions_keep_literals_and_initializer_cleanup() {
    let source = format!(
        r#"{GROWING_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let allocator = Allocator.with_realloc(block_alloc, block_free, {{
                drop(Bytes.from("growth hook initializer"));
                block_grow
            }});
            let mut vector: AllocVec<i64> = AllocVec.new(allocator);
            let mut i = 0;
            while i < 5 {{ vector = AllocVec.push(vector, i); i = i + 1; }}
            AllocVec.get(&vector, 4)
        }}"#
    );
    assert_eq!(value(&source), 4);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 4);
}

#[test]
fn realloc_hook_declared_first_is_not_confused_with_no_hook() {
    let source = r#"
        fn grow(block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
            let mut fresh = Bytes.with_capacity(bytes);
            let mut i = 0;
            while i < old_bytes { fresh = Bytes.push(fresh, Bytes.get(&block, i)); i = i + 1; }
            drop(block); fresh
        }
        fn allocate(bytes: i64) -> Bytes ! {alloc, panic} {
            Bytes.with_capacity(if bytes > 32 {0} else {bytes})
        }
        fn release(block: Bytes) -> Unit ! {} {drop(block)}
        fn main() -> i64 ! {alloc, panic} {
            let allocator = Allocator.with_realloc(allocate, release, grow);
            let mut values: AllocVec<i64> = AllocVec.new(allocator);
            let mut i = 0;
            while i < 5 {values = AllocVec.push(values, i); i = i + 1;}
            AllocVec.get(&values, 4)
        }"#;
    assert_eq!(value(source), 4);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 4);
}

#[test]
fn realloc_callbacks_cannot_overwrite_typed_elements_or_owning_handles() {
    let source = r#"
        fn allocate(bytes: i64) -> Bytes ! {alloc, panic} {
            let mut block = Bytes.with_capacity(bytes);
            let mut i = 0;
            while i < bytes {block = Bytes.push_reserved(block, 255); i = i + 1;}
            block
        }
        fn release(block: Bytes) -> Unit ! {} {drop(block)}
        fn replace(block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
            if old_bytes > 0 && Bytes.get(&block, 0) != 0 {
                drop(block); return Bytes.with_capacity(0);
            }
            drop(block);
            let mut fresh = Bytes.with_capacity(bytes);
            let mut i = 0;
            while i < bytes {fresh = Bytes.push_reserved(fresh, 0); i = i + 1;}
            fresh
        }
        fn main() -> i64 ! {alloc, panic} {
            let allocator = Allocator.with_realloc(allocate, release, replace);
            let mut values: AllocVec<i64> = AllocVec.new(allocator);
            let mut i = 0;
            while i < 5 {values = AllocVec.push(values, i + 41); i = i + 1;}
            let answer = AllocVec.get(&values, 0) + AllocVec.get(&values, 4);
            let mut owners: AllocVec<Box<i64>> = AllocVec.new(allocator);
            let mut j = 0;
            while j < 5 {owners = AllocVec.push(owners, Box.new(j)); j = j + 1;}
            let owners = AllocVec.clear(owners);
            drop(owners);
            answer
        }"#;
    assert_eq!(value(source), 86);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 86);
}

const STATEFUL_ALLOCATOR: &str = r#"
struct Counting {
    calls: i64,
    live: i64,
    limit: i64,
}
impl AllocatorProtocol for Counting {
    fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc, panic} {
        self.calls = self.calls + 1;
        self.live = self.live + 1;
        if self.limit > 0 && self.live > self.limit {
            Bytes.with_capacity(0)
        } else {
            Bytes.with_capacity(bytes)
        }
    }
    fn free(self: &mut Self, block: Bytes) -> Unit ! {} {
        self.live = 0;
        drop(block)
    }
    fn grow(self: &mut Self, block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
        self.calls = self.calls + 1;
        let mut out = Bytes.with_capacity(bytes);
        let mut i = 0;
        while i < old_bytes {
            out = Bytes.push(out, Bytes.get(&block, i));
            i = i + 1;
        }
        drop(block);
        out
    }
}
"#;

#[test]
fn stateful_allocator_context_uses_its_own_instance_callbacks() {
    let source = format!(
        r#"{STATEFUL_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let box = {{
                let context = AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 0 }});
                AllocBox.new(context, 41)
            }};
            AllocBox.take(box)
        }}"#
    );
    assert_eq!(value(&source), 41);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 41);
}

#[test]
fn stateful_alloc_vec_grows_through_the_instance_growth_hook() {
    let source = format!(
        r#"{STATEFUL_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let mut vector: AllocVec<i64> =
                AllocVec.with_capacity(AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 0 }}), 1);
            let mut i = 0;
            while i < 5 {{
                vector = AllocVec.push(vector, i + 41);
                i = i + 1;
            }}
            AllocVec.len(&vector) + AllocVec.get(&vector, 4)
        }}"#
    );
    assert_eq!(value(&source), 50);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 50);
}

#[test]
fn shared_instance_context_outlives_its_binding_and_serves_several_containers() {
    let source = format!(
        r#"{STATEFUL_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let context = AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 0 }});
            let first = AllocBox.new(AllocatorContext.share(&context), 1);
            let second = AllocBox.new(AllocatorContext.share(&context), 2);
            drop(context);
            AllocBox.take(first) * 10 + AllocBox.take(second)
        }}"#
    );
    assert_eq!(value(&source), 12);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 12);
}

#[test]
fn stateful_allocator_refusal_returns_the_untouched_vector_and_element() {
    let source = format!(
        r#"enum Result<T, E> {{ Ok(T), Err(E) }}
        {STATEFUL_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let context = AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 1 }});
            let mut vector: AllocVec<i64> = AllocVec.with_capacity(context, 1);
            vector = AllocVec.push(vector, 1);
            match AllocVec.try_push(vector, 2) {{
                Ok(vector) => AllocVec.len(&vector) + 100,
                Err(pair) => match pair {{
                    (vector, refused) => AllocVec.len(&vector) * 10 + AllocVec.get(&vector, 0) + refused
                }}
            }}
        }}"#
    );
    assert_eq!(value(&source), 13);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 13);
}

const OWNING_STATE_ALLOCATOR: &str = r#"
struct OwnedCounting {
    calls: i64,
    live: i64,
    limit: i64,
    token: Box<i64>,
}
impl AllocatorProtocol for OwnedCounting {
    fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc, panic} {
        self.calls = self.calls + 1;
        self.live = self.live + 1;
        if self.limit > 0 && self.live > self.limit {
            Bytes.with_capacity(0)
        } else {
            Bytes.with_capacity(bytes)
        }
    }
    fn free(self: &mut Self, block: Bytes) -> Unit ! {} {
        self.live = 0;
        drop(block)
    }
    fn grow(self: &mut Self, block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
        let mut out = Bytes.with_capacity(bytes);
        let mut i = 0;
        while i < old_bytes {
            out = Bytes.push(out, Bytes.get(&block, i));
            i = i + 1;
        }
        drop(block);
        out
    }
}
"#;

#[test]
fn stateful_allocator_refusal_preserves_the_owning_payload_and_destroys_state_once() {
    let source = format!(
        r#"enum Result<T, E> {{ Ok(T), Err(E) }}
        {OWNING_STATE_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic}} {{
            let context = AllocatorContext.new(OwnedCounting {{
                calls: 0, live: 0, limit: 1, token: Box.new(7),
            }});
            let first = AllocBox.new(AllocatorContext.share(&context), Box.new(41));
            let second = match AllocBox.try_new(AllocatorContext.share(&context), Box.new(9)) {{
                Ok(box) => 100 + Box.take(AllocBox.take(box)),
                Err(payload) => Box.take(payload),
            }};
            let first = Box.take(AllocBox.take(first));
            drop(context);
            first + second
        }}"#
    );
    let (result, stats) = evaluate(&source);
    assert_eq!(result, 50);
    assert_eq!(stats.allocations, stats.deallocations);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 50);
}

#[test]
fn allocator_context_crosses_a_structured_task_boundary() {
    let source = format!(
        r#"use std.task.TaskExit;
        {STATEFUL_ALLOCATOR}
        fn main() -> i64 ! {{alloc, panic, suspend}} {{
            let context = AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 0 }});
            Task.scope(fn() -> i64 ! {{alloc, panic, suspend}} {{
                let task: Task<i64> = Task.spawn(fn() -> i64 ! {{alloc, panic, suspend}} {{
                    let box = AllocBox.new(context, 41);
                    AllocBox.take(box)
                }});
                match Task.join(task) {{
                    TaskExit.Completed(value) => value,
                    TaskExit.Cancelled => -1,
                }}
            }})
        }}"#
    );
    assert_eq!(value(&source), 41);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees_task(&source, 41);
}

#[test]
fn hostile_allocator_context_shapes_are_rejected() {
    // A context needs an owned record with no borrowed leaves.
    rejects(
        r#"
        fn main() -> Unit ! {alloc, panic} {
            let context = AllocatorContext.new(5);
        }"#,
        "owned record instance",
    );
    rejects(
        r#"
        struct Borrowed<'a> { view: &'a [i64] }
        impl AllocatorProtocol for Borrowed<'_> {
            fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
            fn free(self: &mut Self, block: Bytes) -> Unit ! {} { drop(block) }
            fn grow(self: &mut Self, block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
                let _ = old_bytes; drop(block); Bytes.with_capacity(bytes)
            }
        }
        fn main() -> Unit ! {alloc, panic} {
            let view: [i64; 1] = [1];
            let context = AllocatorContext.new(Borrowed { view: &view[..] });
        }"#,
        "borrowed",
    );
    // A closure capture is not silently converted into reusable callbacks.
    rejects(
        r#"
        fn main() -> Unit ! {alloc, panic} {
            let context = AllocatorContext.new(fn(bytes: i64) -> Bytes ! {alloc, panic} {
                Bytes.with_capacity(bytes)
            });
        }"#,
        "owned record instance",
    );
    // Missing or mismatched protocol methods are rejected by the ordinary
    // exact trait-signature check.
    rejects(
        r#"
        struct Bad { count: i64 }
        impl AllocatorProtocol for Bad {
            fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
            fn free(self: &mut Self, block: Bytes) -> Unit ! {alloc, panic} { drop(block) }
            fn grow(self: &mut Self, block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
                let _ = old_bytes; drop(block); Bytes.with_capacity(bytes)
            }
        }
        fn main() -> Unit ! {alloc, panic} {
            let context = AllocatorContext.new(Bad { count: 0 });
        }"#,
        "does not match the trait signature exactly",
    );
    rejects(
        r#"
        struct Bad { count: i64 }
        impl AllocatorProtocol for Bad {
            fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc, panic} { Bytes.with_capacity(bytes) }
            fn free(self: &mut Self, block: Bytes) -> Unit ! {} { drop(block) }
        }
        fn main() -> Unit ! {alloc, panic} {
            let context = AllocatorContext.new(Bad { count: 0 });
        }"#,
        "missing implementation of trait method",
    );
    // Contexts are affine: copying one would duplicate a retained state
    // obligation without an explicit share.
    rejects(
        &format!(
            r#"{STATEFUL_ALLOCATOR}
            fn main() -> i64 ! {{alloc, panic}} {{
                let context = AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 0 }});
                let copy = context;
                let again = context;
                AllocBox.take(AllocBox.new(copy, 1)) + AllocBox.take(AllocBox.new(again, 2))
            }}"#
        ),
        "move",
    );
}

#[test]
fn stateful_growth_hook_cannot_overwrite_typed_vector_elements_or_owners() {
    let source = r#"
        struct Zeroing {
            calls: i64,
        }
        impl AllocatorProtocol for Zeroing {
            fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc, panic} {
                self.calls = self.calls + 1;
                let mut block = Bytes.with_capacity(bytes);
                let mut i = 0;
                while i < bytes {
                    block = Bytes.push_reserved(block, 255);
                    i = i + 1;
                }
                block
            }
            fn free(self: &mut Self, block: Bytes) -> Unit ! {} { drop(block) }
            fn grow(self: &mut Self, block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc, panic} {
                self.calls = self.calls + 1;
                if old_bytes > 0 && Bytes.get(&block, 0) != 0 {
                    drop(block);
                    return Bytes.with_capacity(0);
                }
                drop(block);
                let mut fresh = Bytes.with_capacity(bytes);
                let mut i = 0;
                while i < bytes {
                    fresh = Bytes.push_reserved(fresh, 0);
                    i = i + 1;
                }
                fresh
            }
        }
        fn main() -> i64 ! {alloc, panic} {
            let allocator = AllocatorContext.new(Zeroing { calls: 0 });
            let mut values: AllocVec<i64> = AllocVec.new(AllocatorContext.share(&allocator));
            let mut i = 0;
            while i < 5 {
                values = AllocVec.push(values, i + 41);
                i = i + 1;
            }
            let answer = AllocVec.get(&values, 0) + AllocVec.get(&values, 4);
            let mut owners: AllocVec<Box<i64>> = AllocVec.new(AllocatorContext.share(&allocator));
            let mut j = 0;
            while j < 5 {
                owners = AllocVec.push(owners, Box.new(j));
                j = j + 1;
            }
            let owners = AllocVec.clear(owners);
            drop(owners);
            drop(allocator);
            answer
        }"#;
    assert_eq!(value(source), 86);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 86);
}

#[test]
fn allocator_context_and_container_cross_a_function_boundary() {
    let source = format!(
        r#"{STATEFUL_ALLOCATOR}
        fn build() -> AllocBox<i64> ! {{alloc, panic}} {{
            let context = AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 0 }});
            AllocBox.new(context, 7)
        }}
        fn main() -> i64 ! {{alloc, panic}} {{
            AllocBox.take(build())
        }}"#
    );
    assert_eq!(value(&source), 7);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 7);
}

#[test]
fn allocator_context_is_an_ordinary_function_parameter_and_result() {
    let source = format!(
        r#"{STATEFUL_ALLOCATOR}
        fn make(context: AllocatorContext) -> AllocBox<i64> ! {{alloc, panic}} {{
            AllocBox.new(context, 5)
        }}
        fn share_context(context: &AllocatorContext) -> AllocatorContext ! {{}} {{
            AllocatorContext.share(context)
        }}
        fn main() -> i64 ! {{alloc, panic}} {{
            let context = AllocatorContext.new(Counting {{ calls: 0, live: 0, limit: 0 }});
            let first = make(share_context(&context));
            let second = make(context);
            AllocBox.take(first) + AllocBox.take(second)
        }}"#
    );
    assert_eq!(value(&source), 10);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(&source, 10);
}
