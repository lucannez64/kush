//! Checked unique-box reuse, allocation-preserving vector transforms, and
//! observable allocation diagnostics. Native and reference execution must
//! agree on values, output, exit status, and diagnostic counts.
use kush::executable::{MemoryStats, check};

fn reference(source: &str) -> (i64, MemoryStats, Vec<u8>) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (result, stats, output)
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

/// Run the native backend with diagnostic counters and compare it with the
/// reference evaluator. Native diagnostics are the same stable one-line format.
fn agrees(source: &str, expected: i64) -> MemoryStats {
    let (reference_value, stats, stdout) = reference(source);
    assert_eq!(reference_value, expected, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("reuse-test");
        kush::native::build_with_stats(&program, &binary, true).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, stdout);
        let stderr = String::from_utf8(output.stderr).unwrap();
        let line = stderr
            .lines()
            .find(|line| line.starts_with("allocation-stats: "))
            .unwrap_or_else(|| panic!("missing native allocation diagnostics: {stderr:?}"));
        assert_eq!(line, stats.report(), "{source}");
        assert_eq!(
            stderr
                .lines()
                .filter(|line| line.starts_with("allocation-stats: "))
                .count(),
            1,
            "exactly one diagnostics line"
        );
    }
    stats
}

#[test]
fn checked_box_reuse_preserves_the_allocation_and_returns_a_new_payload() {
    let source = "fn main() -> i64 ! {alloc, panic} {
        let mut owner = Box.new(0);
        let mut i = 0;
        while i < 100 {
            let n = Box.read(&owner);
            owner = Box.reuse(owner, n + 1);
            i = i + 1;
        }
        Box.take(owner)
    }";
    let stats = agrees(source, 100);
    assert_eq!(stats.allocations, 1, "reuse never falls back to allocation");
    assert_eq!(stats.reuses, 100);
    assert_eq!(stats.deallocations, 1);
    assert_eq!(stats.peak_live, 1);

    // Measured before/after: replacing each reuse with Box.new allocates the
    // initial box plus 100 replacements in the same workload.
    let replaced = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut owner = Box.new(0);
            let mut i = 0;
            while i < 100 {
                let n = Box.read(&owner);
                owner = Box.new(n + 1);
                i = i + 1;
            }
            Box.take(owner)
        }",
        100,
    );
    assert_eq!(replaced.allocations, 101);
    assert_eq!(replaced.reuses, 0);
}

#[test]
fn box_reuse_drops_the_old_affine_payload_exactly_once_and_allows_narrowing() {
    // The old payload is an owned Box<i64>; it must be released, not leaked or
    // double-freed, while the outer allocation is kept.
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let inner = Box.new(1);
            let owner = Box.new(inner);
            let owner = Box.reuse(owner, 42);
            Box.take(owner)
        }",
        42,
    );
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    assert_eq!(stats.reuses, 1);

    // A wider old layout can safely store a narrower new payload.
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let owner: Box<[i64; 2]> = Box.new([20, 22]);
            let owner: Box<i64> = Box.reuse(owner, 42);
            Box.take(owner)
        }",
        42,
    );
    assert_eq!(stats.reuses, 1);
}

#[test]
fn box_reuse_rejects_linear_payloads_and_wider_layouts() {
    rejects(
        "#[linear] enum Ticket { Live }
         fn main() -> i64 ! {alloc, panic} {
            let owner = Box.new(Ticket.Live);
            let owner = Box.reuse(owner, Ticket.Live);
            match Box.take(owner) { Ticket.Live => 42 }
         }",
        "cannot implicitly drop the linear payload",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> = Box.new(1);
            let owner: Box<[i64; 2]> = Box.reuse(owner, [1, 2]);
            42
         }",
        "no allocating fallback",
    );
    // A linear new payload keeps its obligation on the returned owner.
    rejects(
        "#[linear] enum Ticket { Live }
         fn main() -> i64 ! {alloc, panic} {
            let owner = Box.reuse(Box.new(0), Ticket.Live);
            42
         }",
        "linear value is not consumed",
    );
}

#[test]
fn box_reuse_propagates_binding_obligations_and_rejects_borrow_conflicts() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let value: Box<i64> @[1] = Box.new(1);
            let owner = Box.reuse(value, 2);
            42
         }",
        "linear value is not consumed",
    );
    agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let value: Box<i64> @[1] = Box.new(1);
            let owner = Box.reuse(value, 2);
            Box.take(owner)
         }",
        2,
    );
    rejects(
        "fn both(r: &Box<i64>, o: Box<i64>) -> i64 ! {panic} {
            Box.read(r) + Box.take(o)
         }
         fn main() -> i64 ! {alloc, panic} {
            let owner = Box.new(1);
            both(&owner, Box.reuse(owner, 2))
         }",
        "while it is borrowed",
    );
    // A slice view keeps the vector owner unavailable for an in-place map.
    rejects(
        "fn id(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let view: &[i64] = &values[..];
            let mapped = Vec.map_in_place(values, id);
            Slice.len(view) + Vec.len(&mapped)
         }",
        "borrowed by this call or a slice view",
    );
}

#[test]
fn pending_reuse_owner_is_cleaned_once_on_later_question_mark_or_return() {
    let stats = agrees(
        "enum Result<T, E> { Ok(T), Err(E) }
         fn bad() -> Result<i64, i64> ! {} { Err(7) }
         fn work(r: Result<i64, i64>) -> Result<i64, i64> ! {alloc, panic} {
            let owner = Box.new(1);
            let owner = Box.reuse(owner, r?);
            Ok(Box.take(owner))
         }
         fn main() -> i64 ! {alloc, panic} {
            match work(bad()) { Ok(v) => v, Err(e) => e + 35 }
         }",
        42,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    assert_eq!(stats.reuses, 0);
    agrees(
        "fn work(flag: Bool) -> i64 ! {alloc, panic} {
            let owner = Box.new(1);
            if flag { return 41; }
            Box.take(Box.reuse(owner, 42))
         }
         fn main() -> i64 ! {alloc, panic} { work(false) }",
        42,
    );
}

#[test]
fn map_in_place_preserves_storage_and_applies_first_class_functions() {
    let source = "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            values = Vec.map_in_place(values, inc);
            Vec.get(&values, 0) * 10 + Vec.get(&values, 1)
        }";
    let stats = agrees(source, 23);
    assert_eq!(stats.allocations, 1, "map must not allocate");
    assert_eq!(stats.deallocations, 1);
    assert_eq!(stats.buffer_growths, 1);
    assert_eq!(stats.reuses, 0);
}

#[test]
fn map_in_place_narrows_layouts_and_rejects_widening() {
    let stats = agrees(
        "fn first(x: [i64; 2]) -> i64 ! {panic} { let [a, b] = x; a + b }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<[i64; 2]> = Vec.new();
            values = Vec.push(values, [1, 2]);
            values = Vec.push(values, [3, 4]);
            let mapped: Vec<i64> = Vec.map_in_place(values, first);
            Vec.get(&mapped, 0) * 10 + Vec.get(&mapped, 1)
         }",
        37,
    );
    assert_eq!(stats.allocations, 1);
    rejects(
        "fn pair(x: i64) -> [i64; 2] ! {} { [x, x] }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let mapped: Vec<[i64; 2]> = Vec.map_in_place(values, pair);
            Vec.len(&mapped)
         }",
        "cannot widen elements",
    );
}

#[test]
fn reuse_and_map_respect_union_and_aggregate_widths() {
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64 | Bool> = Box.new(41);
            let owner: Box<i64> = Box.reuse(owner, 42);
            Box.take(owner)
         }",
        42,
    );
    assert_eq!(stats.reuses, 1);
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> = Box.new(1);
            let owner: Box<i64 | Bool> = Box.reuse(owner, true);
            42
         }",
        "no allocating fallback",
    );
    agrees(
        "fn narrow(value: i64 | Bool) -> i64 ! {} {
            match value { i64 @ n => n, Bool @ b => if b { 1 } else { 0 } }
         }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64 | Bool> = Vec.new();
            values = Vec.push(values, 41);
            values = Vec.push(values, true);
            let values: Vec<i64> = Vec.map_in_place(values, narrow);
            Vec.get(&values, 0) + Vec.get(&values, 1)
         }",
        42,
    );
}

#[test]
fn map_in_place_rejects_once_callbacks_and_linear_elements() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let f: once fn(i64) -> i64 ! {panic} = fn(x: i64) -> i64 ! {panic} { x + 1 };
            Vec.map_in_place(values, f)
         }",
        "once or linear-once callback cannot be duplicated",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let f: linear once fn(i64) -> i64 ! {panic} = fn(x: i64) -> i64 ! {panic} { x + 1 };
            Vec.map_in_place(values, f)
         }",
        "once or linear-once callback cannot be duplicated",
    );
    rejects(
        "#[linear] enum Ticket { Live }
         fn bad() -> i64 ! {alloc, panic} {
            let values: Vec<Ticket> = Vec.new();
            42
         }
         fn main() -> i64 ! {alloc, panic} { bad() }",
        "linear",
    );
    // Grade contracts of copyable callback parameters are preserved.
    agrees(
        "fn twice(x: i64 @[2]) -> i64 ! {panic} { x + x }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 21);
            values = Vec.map_in_place(values, twice);
            Vec.get(&values, 0)
         }",
        42,
    );
}

#[test]
fn map_in_place_moves_owning_elements_into_callbacks() {
    let stats = agrees(
        "fn unwrap(owner: Box<i64>) -> i64 ! {} { Box.take(owner) }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<Box<i64>> = Vec.new();
            values = Vec.push(values, Box.new(1));
            values = Vec.push(values, Box.new(2));
            let mapped: Vec<i64> = Vec.map_in_place(values, unwrap);
            Vec.get(&mapped, 0) * 10 + Vec.get(&mapped, 1)
         }",
        12,
    );
    assert_eq!(stats.allocations, 3);
    assert_eq!(stats.deallocations, 3);
}

#[test]
fn map_in_place_replaces_owned_elements_without_copying_owners() {
    let stats = agrees(
        "fn bump(owner: Box<i64>) -> Box<i64> ! {panic} {
            let n = Box.read(&owner);
            Box.reuse(owner, n + 1)
         }
         fn unwrap(owner: Box<i64>) -> i64 ! {} { Box.take(owner) }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<Box<i64>> = Vec.new();
            values = Vec.push(values, Box.new(1));
            values = Vec.push(values, Box.new(2));
            values = Vec.map_in_place(values, bump);
            let mapped: Vec<i64> = Vec.map_in_place(values, unwrap);
            Vec.get(&mapped, 0) * 10 + Vec.get(&mapped, 1)
         }",
        23,
    );
    assert_eq!(stats.allocations, 3, "two boxes and one vector");
    assert_eq!(stats.deallocations, 3);
    assert_eq!(stats.reuses, 2);
}

#[test]
fn map_in_place_zero_length_and_early_exit_clean_pending_owners() {
    let stats = agrees(
        "fn id(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = Vec.new();
            let values = Vec.map_in_place(values, id);
            Vec.len(&values) + 42
         }",
        42,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    let stats = agrees(
        "enum Result<T, E> { Ok(T), Err(E) }
         fn bad() -> Result<fn(i64) -> i64 ! {}, i64> ! {} { Err(7) }
         fn work(r: Result<fn(i64) -> i64 ! {}, i64>) -> Result<i64, i64> ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let mapped = Vec.map_in_place(values, r?);
            Ok(Vec.get(&mapped, 0))
         }
         fn main() -> i64 ! {alloc, panic} {
            match work(bad()) { Ok(v) => v, Err(e) => e + 35 }
         }",
        42,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
}

#[test]
fn nested_pure_maps_fuse_and_effectful_maps_do_not() {
    let fused = "fn seven(x: i64) -> i64 ! {} { 7 }
        fn nine(x: i64) -> i64 ! {} { 9 }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            let values = Vec.map_in_place(Vec.map_in_place(values, seven), nine);
            Vec.get(&values, 0) * 10 + Vec.get(&values, 1)
        }";
    let program = check(fused).unwrap();
    assert_eq!(program.fusion_count(), 1);
    assert_eq!(agrees(fused, 99).fusions, 1);

    let effectful = "fn noisy(x: i64) -> i64 ! {io, panic} { print_i64(x); x + 1 }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            let values = Vec.map_in_place(Vec.map_in_place(values, noisy), noisy);
            print_i64(Vec.get(&values, 0));
            print_i64(Vec.get(&values, 1));
        }";
    assert_eq!(check(effectful).unwrap().fusion_count(), 0);
    let (result, stats, output) = reference(effectful);
    assert_eq!(result, 0);
    assert_eq!(stats.fusions, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "1\n2\n2\n3\n3\n4\n");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(effectful, 0);
}

#[test]
fn noalloc_contracts_are_independent_of_reuse_and_fusion() {
    let source = "fn id(x: i64) -> i64 ! {} { x }
        #[noalloc]
        fn bump(owner: Box<i64>) -> Box<i64> ! {panic} {
            let n = Box.read(&owner);
            Box.reuse(owner, n + 1)
        }
        #[noalloc]
        fn same(values: Vec<i64>) -> Vec<i64> ! {} { Vec.map_in_place(values, id) }
        fn main() -> i64 ! {alloc, panic} {
            let owner = bump(Box.new(41));
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = same(values);
            Box.take(owner) + Vec.get(&values, 0)
        }";
    let stats = agrees(source, 43);
    assert_eq!(stats.reuses, 1);
    rejects(
        "fn make(x: i64) -> Box<i64> ! {alloc, panic} { Box.new(x) }
         #[noalloc]
         fn same(values: Vec<i64>) -> Vec<Box<i64>> ! {panic} {
            Vec.map_in_place(values, make)
         }
         fn main() -> i64 ! {alloc, panic} { 42 }",
        "requires effects {alloc}",
    );
    rejects(
        "#[noalloc]
         fn bump(owner: Box<i64>) -> Box<i64> ! {alloc, panic} { Box.reuse(owner, 1) }
         fn main() -> i64 ! {alloc, panic} { 42 }",
        "noalloc contract forbids the alloc effect",
    );
}

#[test]
fn allocation_report_is_stable_and_contains_all_observations() {
    let stats = MemoryStats {
        allocations: 3,
        deallocations: 2,
        peak_live: 2,
        buffer_growths: 1,
        reuses: 4,
        fusions: 5,
    };
    assert_eq!(
        stats.report(),
        "allocation-stats: allocations=3 deallocations=2 peak-live=2 buffer-growths=1 reuses=4 fusions=5"
    );
}

#[test]
fn reuse_cannot_discard_a_propagated_linear_owned_payload() {
    rejects(
        "fn main()->i64 ! {alloc,panic} {let b:Box<i64> @[1]=Box.new(1);let wrapped=Box.new(b);let result=Box.reuse(wrapped,42);Box.take(result)}",
        "linear",
    );
}

#[test]
fn in_place_callback_allocation_keeps_the_vector_in_peak_live_counts() {
    let stats = agrees(
        "fn replace(x:Box<i64>)->Box<i64> ! {alloc,panic} {let next=Box.new(1);drop(x);next} fn main()->i64 ! {alloc,panic} {let v:Vec<Box<i64>> = [Box.new(0)];let mapped=Vec.map_in_place(v,replace);42}",
        42,
    );
    assert_eq!(stats.peak_live, 3);
    assert_eq!(stats.allocations, 3);
}

#[test]
fn in_place_maps_cannot_create_vectors_of_linear_elements() {
    rejects(
        "#[linear] enum Token{Only} fn make(x:i64)->Token ! {} {Token.Only} fn main()->Unit ! {alloc,panic} {let v:Vec<i64> = [1];let mapped=Vec.map_in_place(v,make);}",
        "linear result",
    );
}
