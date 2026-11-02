//! Explicit vector storage reuse: `Vec.clear`, `Vec.reserve`, and the
//! interleaved `Vec.map_chain_in_place`. Reference and native execution must
//! agree on values, output, failure, and the stable allocation diagnostics.
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

/// Run the native backend with diagnostics and compare it with the reference
/// evaluator. Native diagnostics use the same stable one-line format.
fn agrees(source: &str, expected: i64) -> MemoryStats {
    let (reference_value, stats, stdout) = reference(source);
    assert_eq!(reference_value, expected, "{source}");
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let program = check(source).unwrap();
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("vector-reuse-test");
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
    }
    stats
}

/// Both backends must fail; the reference may report a checked budget rather
/// than a `panic:` string, while the native runtime aborts through `kush_panic`.
fn fails(source: &str, fragment: &str) {
    let program = check(source).unwrap();
    let error = program.evaluate(&mut Vec::new()).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("vector-reuse-failure");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert!(!output.status.success(), "{source}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("panic:"),
            "{source}"
        );
    }
}

#[test]
fn clear_drops_owned_elements_exactly_once_and_keeps_the_allocation() {
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<Box<i64>> = Vec.new();
            values = Vec.push(values, Box.new(1));
            values = Vec.push(values, Box.new(2));
            values = Vec.push(values, Box.new(3));
            let values = Vec.clear(values);
            Vec.len(&values)
        }",
        0,
    );
    assert_eq!(stats.allocations, 4, "three boxes plus the vector");
    assert_eq!(stats.deallocations, 4, "boxes cleared, vector dropped last");
    assert_eq!(stats.peak_live, 4);
    assert_eq!(stats.buffer_growths, 1, "clear performs no growth");
    assert_eq!(stats.reuses, 0);
    assert_eq!(stats.fusions, 0);
}

#[test]
fn clear_retains_capacity_for_later_pushes() {
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 9);
            values = Vec.clear(values);
            let mut i = 0;
            while i < 4 {
                values = Vec.push(values, i);
                i = i + 1;
            }
            Vec.len(&values) + Vec.get(&values, 3)
        }",
        7,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    assert_eq!(
        stats.buffer_growths, 1,
        "the first push grew capacity once; clear retains it"
    );

    let empty = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = Vec.new();
            let values = Vec.clear(values);
            Vec.len(&values)
        }",
        0,
    );
    assert_eq!(empty.allocations, 1);
    assert_eq!(empty.buffer_growths, 0);
}

#[test]
fn clear_is_available_under_noalloc() {
    let stats = agrees(
        "#[noalloc]
         fn reset(values: Vec<i64>) -> Vec<i64> ! {} { Vec.clear(values) }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 7);
            let values = reset(values);
            Vec.len(&values)
         }",
        0,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
}

#[test]
fn clear_and_reserve_also_work_as_receiver_methods() {
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = values.push(3);
            values = values.push(4);
            values = values.reserve(4);
            let cleared = values.clear();
            Vec.len(&cleared)
        }",
        0,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    assert_eq!(
        stats.buffer_growths, 2,
        "first push grows once, reserve grows once"
    );
}

#[test]
fn reserve_grows_at_most_once_and_makes_room_for_the_request() {
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.with_capacity(1);
            values = Vec.push(values, 7);
            values = Vec.reserve(values, 10);
            let mut i = 0;
            while i < 10 {
                values = Vec.push(values, i);
                i = i + 1;
            }
            Vec.len(&values) + Vec.get(&values, 10)
        }",
        20,
    );
    assert_eq!(stats.allocations, 1, "reserve reallocates, never allocates");
    assert_eq!(stats.deallocations, 1);
    assert_eq!(stats.buffer_growths, 1, "exactly one growth event");
    assert_eq!(stats.reuses, 0);

    // A request that already fits performs no growth; the boundary case
    // `len + additional == capacity` also stays put.
    let no_growth = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.with_capacity(5);
            values = Vec.push(values, 1);
            values = Vec.reserve(values, 4);
            let values = Vec.reserve(values, 0);
            Vec.len(&values) + Vec.get(&values, 0) + 40
        }",
        42,
    );
    assert_eq!(no_growth.allocations, 1);
    assert_eq!(no_growth.buffer_growths, 0, "reserve did not need to grow");
}

#[test]
fn reserve_rejects_negative_and_overflowing_requests() {
    fails(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.reserve(values, -1);
            Vec.len(&values)
        }",
        "panic: negative vector reserve",
    );
    fails(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.reserve(values, 9223372036854775807);
            Vec.len(&values)
        }",
        "budget exhausted",
    );
}

#[test]
fn reserve_and_clear_require_an_owned_vector_that_is_not_borrowed() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let view: &[i64] = &values[..];
            let values = Vec.reserve(values, 4);
            Slice.len(view) + Vec.len(&values)
        }",
        "cannot move an owner while it is borrowed",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let view: &[i64] = &values[..];
            let values = Vec.clear(values);
            Slice.len(view) + Vec.len(&values)
        }",
        "cannot move an owner while it is borrowed",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = Vec.new();
            Vec.clear(&values)
        }",
        "an owned Vec<T> (it is consumed and returned)",
    );
    rejects(
        "#[noalloc]
         fn reserve(values: Vec<i64>) -> Vec<i64> ! {panic} { Vec.reserve(values, 1) }
         fn main() -> i64 ! {alloc, panic} { 42 }",
        "requires effects {alloc}",
    );
}

#[test]
fn map_chain_interleaves_callbacks_and_reports_no_compiler_fusion() {
    let source = "fn first(x: i64) -> i64 ! {io, panic} { print_i64(x); x + 10 }
        fn second(x: i64) -> i64 ! {io, panic} { print_i64(x); x * 2 }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            let values = Vec.map_chain_in_place(values, first, second);
            print_i64(Vec.get(&values, 0));
            print_i64(Vec.get(&values, 1));
        }";
    let program = check(source).unwrap();
    assert_eq!(
        program.fusion_count(),
        0,
        "the chain is explicit, not fused"
    );
    let (result, stats, output) = reference(source);
    assert_eq!(result, 0);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.buffer_growths, 1);
    assert_eq!(stats.fusions, 0);
    assert_eq!(
        String::from_utf8(output).unwrap(),
        // f(1), g(11), f(2), g(12) — not f(1), f(2), g(11), g(12).
        "1\n11\n2\n12\n22\n24\n"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    agrees(source, 0);
}

#[test]
fn map_chain_allows_wider_intermediate_ssa_layouts_with_a_narrow_final_result() {
    let stats = agrees(
        "fn pair(x: i64) -> [i64; 2] ! {panic} { [x, x + 1] }
         fn sum_pair(pair: [i64; 2]) -> i64 ! {panic} {
            let [a, b] = pair;
            a + b
         }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            values = Vec.push(values, 2);
            let values = Vec.map_chain_in_place(values, pair, sum_pair);
            Vec.get(&values, 0) * 10 + Vec.get(&values, 1)
         }",
        35,
    );
    assert_eq!(stats.allocations, 1, "the vector allocation is preserved");
    assert_eq!(stats.deallocations, 1);
    assert_eq!(stats.buffer_growths, 1);
}

#[test]
fn map_chain_rejects_widening_and_representation_changes() {
    rejects(
        "fn pair(x: i64) -> [i64; 2] ! {} { [x, x] }
         fn keep(pair: [i64; 2]) -> [i64; 2] ! {} { pair }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values: Vec<[i64; 2]> = Vec.map_chain_in_place(values, pair, keep);
            Vec.len(&values)
         }",
        "cannot widen elements",
    );
    rejects(
        "fn id(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values: Vec<[i64; 2]> = Vec.map_chain_in_place(values, id, id);
            Vec.len(&values)
         }",
        "final result element layout is [i64; 2]",
    );
}

#[test]
fn map_chain_checks_both_callback_signatures_and_reusable_values() {
    rejects(
        "fn take_pair(pair: [i64; 2]) -> i64 ! {panic} { let [a, b] = pair; a + b }
         fn id(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            Vec.map_chain_in_place(values, take_pair, id)
         }",
        "first callback parameter [i64; 2] must accept i64",
    );
    rejects(
        "fn id(x: i64) -> i64 ! {} { x }
         fn take_pair(pair: [i64; 2]) -> i64 ! {panic} { let [a, b] = pair; a + b }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            Vec.map_chain_in_place(values, id, take_pair)
         }",
        "second callback parameter [i64; 2] must accept i64",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let f: once fn(i64) -> i64 ! {panic} = fn(x: i64) -> i64 ! {panic} { x + 1 };
            let g: once fn(i64) -> i64 ! {panic} = fn(x: i64) -> i64 ! {panic} { x + 2 };
            Vec.map_chain_in_place(values, f, g)
         }",
        "once or linear-once callback cannot be reused",
    );
    rejects(
        "#[linear] enum Ticket { Live }
         fn make(x: i64) -> Ticket ! {} { Ticket.Live }
         fn keep(ticket: Ticket) -> Ticket ! {} { ticket }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_chain_in_place(values, make, keep);
            Vec.len(&values)
         }",
        "cannot store linear first elements",
    );
    rejects(
        "fn spawn_one(x: i64) -> Task<i64> ! {suspend} {
            Task.spawn(fn() -> i64 ! {suspend} { 1 })
         }
         fn id(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {alloc, panic, suspend} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_chain_in_place(values, id, spawn_one);
            Vec.len(&values)
         }",
        "a function cannot return a task handle",
    );
    rejects(
        "fn noisy(x: i64) -> i64 ! {io, panic} { print_i64(x); x + 1 }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            Vec.map_chain_in_place(values, noisy, noisy)
         }",
        "requires effects {io}",
    );
}

#[test]
fn map_chain_callback_effects_are_required_independently_of_optimization() {
    rejects(
        "fn make(x: i64) -> Box<i64> ! {alloc, panic} { Box.new(x) }
         fn unwrap(owner: Box<i64>) -> i64 ! {} { Box.take(owner) }
         #[noalloc]
         fn chain(values: Vec<i64>) -> Vec<i64> ! {panic} {
            Vec.map_chain_in_place(values, make, unwrap)
         }
         fn main() -> i64 ! {alloc, panic} { 42 }",
        "requires effects {alloc}",
    );
    let stats = agrees(
        "#[noalloc]
         fn id(x: i64) -> i64 ! {} { x }
         #[noalloc]
         fn same(values: Vec<i64>) -> Vec<i64> ! {} {
            Vec.map_chain_in_place(values, id, id)
         }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 21);
            let values = same(values);
            Vec.get(&values, 0)
         }",
        21,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.buffer_growths, 1);
}

#[test]
fn map_chain_moves_owning_elements_through_the_intermediate_slot_once() {
    let stats = agrees(
        "fn keep(owner: Box<i64>) -> Box<i64> ! {panic} {
            let n = Box.read(&owner);
            Box.reuse(owner, n + 1)
         }
         fn unwrap(owner: Box<i64>) -> i64 ! {} { Box.take(owner) }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<Box<i64>> = Vec.new();
            values = Vec.push(values, Box.new(1));
            values = Vec.push(values, Box.new(2));
            let values: Vec<i64> = Vec.map_chain_in_place(values, keep, unwrap);
            Vec.get(&values, 0) * 10 + Vec.get(&values, 1)
         }",
        23,
    );
    assert_eq!(stats.allocations, 3, "two boxes and one vector");
    assert_eq!(stats.deallocations, 3);
    assert_eq!(stats.reuses, 2);
}

#[test]
fn empty_map_chain_still_evaluates_callback_expressions_once_left_to_right() {
    // The vector expression is evaluated before the callback expressions. A
    // `?` in the second callback returns early and the pending empty vector
    // owner is cleaned exactly once.
    let stats = agrees(
        "use std.result.Result;
         fn bad() -> Result<fn(i64) -> i64 ! {panic}, i64> ! {} { Err(7) }
         fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn work(r: Result<fn(i64) -> i64 ! {panic}, i64>) -> Result<i64, i64> ! {alloc, panic} {
            let values: Vec<i64> = Vec.new();
            let mapped = Vec.map_chain_in_place(values, inc, r?);
            Ok(Vec.len(&mapped))
         }
         fn main() -> i64 ! {alloc, panic} {
            match work(bad()) {
                Ok(value) => value,
                Err(error) => error + 35,
            }
         }",
        42,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1, "pending empty vector cleaned once");

    // A nonempty chain whose first callback expression diverges still cleans
    // the pending vector owner.
    let early = agrees(
        "use std.result.Result;
         fn bad() -> Result<fn(i64) -> i64 ! {panic}, i64> ! {} { Err(3) }
         fn inc(x: i64) -> i64 ! {panic} { x + 1 }
         fn work(r: Result<fn(i64) -> i64 ! {panic}, i64>) -> Result<i64, i64> ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let mapped = Vec.map_chain_in_place(values, r?, inc);
            Ok(Vec.len(&mapped))
         }
         fn main() -> i64 ! {alloc, panic} {
            match work(bad()) {
                Ok(value) => value,
                Err(error) => error + 39,
            }
         }",
        42,
    );
    assert_eq!(early.allocations, 1);
    assert_eq!(early.deallocations, 1);
    assert_eq!(early.buffer_growths, 1);
}

#[test]
fn automatic_pure_fusion_handles_owned_intermediates_without_a_new_guard() {
    // Empty-effect owning callbacks are still safe to fuse: the intermediate
    // owner is a transient SSA value and is released exactly once either way.
    let source = "fn unwrap(owner: Box<i64>) -> i64 ! {} { Box.take(owner) }
        fn id(x: i64) -> i64 ! {} { x }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<Box<i64>> = Vec.new();
            values = Vec.push(values, Box.new(2));
            values = Vec.push(values, Box.new(3));
            let values = Vec.map_in_place(Vec.map_in_place(values, unwrap), id);
            Vec.get(&values, 0) * 10 + Vec.get(&values, 1)
        }";
    let program = check(source).unwrap();
    assert_eq!(program.fusion_count(), 1);
    let stats = agrees(source, 23);
    assert_eq!(stats.fusions, 1);
    assert_eq!(stats.allocations, 3);
    assert_eq!(stats.deallocations, 3);
    assert_eq!(stats.peak_live, 3);

    // An allocating intermediate callback is not pure, so the two maps stay
    // separate passes and the explicit map order is preserved.
    let allocating = "fn make(x: i64) -> Box<i64> ! {alloc, panic} { Box.new(x) }
        fn unwrap(owner: Box<i64>) -> i64 ! {} { Box.take(owner) }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 2);
            values = Vec.push(values, 3);
            let values = Vec.map_in_place(Vec.map_in_place(values, make), unwrap);
            Vec.get(&values, 0) * 10 + Vec.get(&values, 1)
        }";
    let program = check(allocating).unwrap();
    assert_eq!(program.fusion_count(), 0);
    let stats = agrees(allocating, 23);
    assert_eq!(stats.fusions, 0);
    assert_eq!(stats.allocations, 3);
    assert_eq!(stats.deallocations, 3);
}

#[test]
fn map_chain_does_not_flatten_a_nested_chain_automatically() {
    let source = "fn inc(x: i64) -> i64 ! {panic} { x + 1 }
        fn double(x: i64) -> i64 ! {panic} { x * 2 }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_chain_in_place(
                Vec.map_chain_in_place(values, inc, double),
                inc,
                double,
            );
            Vec.get(&values, 0)
        }";
    let program = check(source).unwrap();
    assert_eq!(
        program.fusion_count(),
        0,
        "explicit chains stay separate passes"
    );
    let stats = agrees(source, 10);
    assert_eq!(stats.fusions, 0);
    assert_eq!(stats.allocations, 1);
}

#[test]
fn map_chain_must_consume_an_unborrowed_vector() {
    rejects(
        "fn id(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let view: &[i64] = &values[..];
            let values = Vec.map_chain_in_place(values, id, id);
            Slice.len(view) + Vec.len(&values)
         }",
        "cannot move an owner while it is borrowed",
    );
    rejects(
        "fn id(x: i64) -> i64 ! {} { x }
         fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            Vec.map_chain_in_place(&values, id, id)
         }",
        "consumes an owned Vec<T>",
    );
}
