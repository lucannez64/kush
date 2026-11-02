//! Completion tests for the memory/optimization area: automatic fusion,
//! widening and fallible reuse, and allocator-region ownership.
//!
//! Reference and native runs must agree on values, output, exit status, and the
//! stable allocation diagnostics line. Failure probes use the reference
//! fallible-allocation budget and the native `KUSH_ALLOC_FAIL_AFTER` test hook.
use kush::executable::{MemoryStats, check};
use kush::native;
use std::process::Command;

fn reference(source: &str) -> (i64, MemoryStats, Vec<u8>) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (result, stats, output)
}

fn reference_with_budget(source: &str, budget: usize) -> (i64, MemoryStats) {
    let program = check(source).unwrap();
    let mut output = Vec::new();
    let (result, stats) = program
        .evaluate_with_alloc_budget(&mut output, budget)
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (result, stats)
}

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

struct NativeRun {
    exit: Option<i32>,
    stdout: Vec<u8>,
    stderr: String,
}

fn native_run(source: &str, env: &[(&str, &str)]) -> NativeRun {
    let program = check(source).unwrap();
    let scratch = native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("memory-completion-test");
    native::build_with_stats(&program, &binary, true).unwrap();
    let mut command = Command::new(&binary);
    command.current_dir(scratch.path());
    for (name, value) in env {
        command.env(name, value);
    }
    let output = command.output().unwrap();
    NativeRun {
        exit: output.status.code(),
        stdout: output.stdout,
        stderr: String::from_utf8(output.stderr).unwrap(),
    }
}

fn native_stats(run: &NativeRun) -> MemoryStats {
    let line = run
        .stderr
        .lines()
        .find(|line| line.starts_with("allocation-stats: "))
        .unwrap_or_else(|| panic!("missing native allocation diagnostics: {:?}", run.stderr));
    let field = |name: &str| -> usize {
        line.split_whitespace()
            .find_map(|field| field.strip_prefix(name)?.strip_prefix('='))
            .unwrap_or_else(|| panic!("missing {name} in {line:?}"))
            .parse()
            .unwrap()
    };
    MemoryStats {
        allocations: field("allocations"),
        deallocations: field("deallocations"),
        peak_live: field("peak-live"),
        buffer_growths: field("buffer-growths"),
        reuses: field("reuses"),
        fusions: field("fusions"),
    }
}

fn agrees(source: &str, expected: i64) -> MemoryStats {
    let (reference_value, stats, stdout) = reference(source);
    assert_eq!(reference_value, expected, "{source}");
    let run = native_run(source, &[]);
    assert_eq!(
        run.exit,
        Some((expected as u64 & 255) as i32),
        "{}",
        run.stderr
    );
    assert_eq!(run.stdout, stdout);
    assert_eq!(native_stats(&run), stats, "{source}");
    stats
}

// ---------------------------------------------------------------------------
// Automatic fusion equivalence
// ---------------------------------------------------------------------------

#[test]
fn alloc_only_total_callbacks_fuse_and_keep_reference_native_parity() {
    let source = "enum Result<T, E> { Ok(T), Err(E) }
        fn touch(pair: [i64; 2]) -> [i64; 2] ! {alloc} {
            let [a, b] = pair;
            match Box.try_new(a) {
                Ok(x) => [Box.take(x), b],
                Err(v) => [v, b]
            }
        }
        fn id(pair: [i64; 2]) -> [i64; 2] ! {} { pair }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<[i64; 2]> = Vec.new();
            values = Vec.push(values, [1, 2]);
            values = Vec.push(values, [3, 4]);
            let values = Vec.map_in_place(Vec.map_in_place(values, touch), id);
            let [a, b] = Vec.get(&values, 0);
            let [c, d] = Vec.get(&values, 1);
            a + b + c + d
        }";
    let program = check(source).unwrap();
    assert_eq!(program.fusion_count(), 1);
    let stats = agrees(source, 10);
    assert_eq!(stats.fusions, 1);
    assert_eq!(stats.allocations, 3, "two fallible boxes plus the vector");
    assert_eq!(stats.buffer_growths, 1);
}

#[test]
fn fusion_rejects_io_panic_loops_and_indirect_callbacks() {
    // A callback with I/O keeps two explicit passes and observes the original
    // per-element trace order.
    let io = "fn show(x: i64) -> i64 ! {io, panic} { print_i64(x); x }
        fn id(x: i64) -> i64 ! {} { x }
        fn main() -> Unit ! {io, alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_in_place(Vec.map_in_place(values, show), id);
            print_i64(Vec.get(&values, 0));
        }";
    let program = check(io).unwrap();
    assert_eq!(program.fusion_count(), 0);
    let (_, stats, output) = reference(io);
    assert_eq!(stats.fusions, 0);
    assert_eq!(String::from_utf8(output).unwrap(), "1\n1\n");

    // A panic-capable callback cannot be fused: the panic site would move.
    let panics = "fn check_positive(x: i64) -> i64 ! {panic} {
            if x < 0 { panic() } else { x }
        }
        fn id(x: i64) -> i64 ! {} { x }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_in_place(Vec.map_in_place(values, check_positive), id);
            Vec.get(&values, 0)
        }";
    assert_eq!(check(panics).unwrap().fusion_count(), 0);

    // An empty-effect loop has no checked termination argument, so it is not a
    // fusion candidate even though its effect row is empty.
    let loops = "fn spin(x: i64) -> i64 ! {} { while false { } x }
        fn id(x: i64) -> i64 ! {} { x }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_in_place(Vec.map_in_place(values, spin), id);
            Vec.get(&values, 0)
        }";
    assert_eq!(check(loops).unwrap().fusion_count(), 0);

    // Indirect calls could select an effectful or divergent body.
    let indirect = "fn id(x: i64) -> i64 ! {} { x }
        fn apply(x: i64) -> i64 ! {} { let f: fn(i64) -> i64 ! {} = id; f(x) }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_in_place(Vec.map_in_place(values, apply), id);
            Vec.get(&values, 0)
        }";
    assert_eq!(check(indirect).unwrap().fusion_count(), 0);

    // Recursion has no checked termination argument.
    let recursion = "fn again(x: i64) -> i64 ! {} { again(x) }
        fn id(x: i64) -> i64 ! {} { x }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_in_place(Vec.map_in_place(values, again), id);
            Vec.get(&values, 0)
        }";
    assert_eq!(check(recursion).unwrap().fusion_count(), 0);
}

#[test]
fn explicit_map_chain_never_counts_as_automatic_fusion() {
    let source = "fn first(x: i64) -> i64 ! {panic} { x + 1 }
        fn second(x: i64) -> i64 ! {panic} { x * 2 }
        fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.map_chain_in_place(Vec.map_chain_in_place(values, first, second), first, second);
            Vec.get(&values, 0)
        }";
    assert_eq!(check(source).unwrap().fusion_count(), 0);
}

// ---------------------------------------------------------------------------
// Widening reuse
// ---------------------------------------------------------------------------

#[test]
fn widening_reuse_grows_or_keeps_the_allocation_with_an_explicit_fallback() {
    let source = "fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> = Box.new(1);
            let owner: Box<[i64; 2]> = Box.reuse_grow(owner, [20, 22]);
            let [a, b] = Box.take(owner);
            a + b
        }";
    let stats = agrees(source, 42);
    assert_eq!(stats.allocations, 1, "the wider store kept one allocation");
    assert_eq!(stats.reuses, 1);
    assert_eq!(stats.deallocations, 1);

    // The growth-capable operation can also narrow, exactly like Box.reuse.
    let narrow = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let owner: Box<[i64; 2]> = Box.new([1, 2]);
            let owner: Box<i64> = Box.reuse_grow(owner, 7);
            Box.take(owner)
        }",
        7,
    );
    assert_eq!(narrow.allocations, 1);
    assert_eq!(narrow.reuses, 1);
}

#[test]
fn widening_reuse_drops_the_old_payload_once_and_keeps_obligations() {
    // The old payload owns a box. Both the old payload and the box allocation
    // are released exactly once while the outer allocation is reused.
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let inner = Box.new(9);
            let owner: Box<Box<i64>> = Box.new(inner);
            let owner: Box<[i64; 2]> = Box.reuse_grow(owner, [40, 2]);
            let [a, b] = Box.take(owner);
            a + b
        }",
        42,
    );
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    assert_eq!(stats.reuses, 1);

    // A binding obligation follows the returned owner, never the old binding.
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let value: Box<i64> @[1] = Box.new(1);
            let owner: Box<[i64; 2]> = Box.reuse_grow(value, [1, 2]);
            42
        }",
        "linear value is not consumed",
    );
    agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let value: Box<i64> @[1] = Box.new(1);
            let owner: Box<[i64; 2]> = Box.reuse_grow(value, [40, 2]);
            let [a, b] = Box.take(owner);
            a + b
        }",
        42,
    );
}

#[test]
fn widening_reuse_requires_alloc_panic_and_rejects_linear_or_borrowed_owners() {
    rejects(
        "#[noalloc] fn grow(owner: Box<i64>) -> i64 ! {panic} {
            let owner: Box<[i64; 2]> = Box.reuse_grow(owner, [1, 2]);
            42
        }
        fn main() -> i64 ! {alloc, panic} { 0 }",
        "requires effects {alloc}",
    );
    rejects(
        "#[linear] enum Ticket { Live }
         fn main() -> i64 ! {alloc, panic} {
            let owner = Box.new(Ticket.Live);
            let owner = Box.reuse_grow(owner, Ticket.Live);
            42
         }",
        "cannot implicitly drop the linear payload",
    );
    rejects(
        "fn both(r: &Box<i64>, o: Box<[i64; 2]>) -> i64 ! {panic} {
            let [a, b] = Box.take(o);
            Box.read(r) + a + b
        }
        fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> = Box.new(1);
            both(&owner, Box.reuse_grow(owner, [1, 2]))
        }",
        "while it is borrowed",
    );
}

// ---------------------------------------------------------------------------
// Fallible allocation and reuse
// ---------------------------------------------------------------------------

#[test]
fn fallible_box_new_returns_the_untouched_payload_on_failure() {
    let source = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            match Box.try_new(41) { Ok(b) => Box.take(b), Err(v) => v }
        }";
    let stats = agrees(source, 41);
    assert_eq!(stats.allocations, 1);

    let (value, stats) = reference_with_budget(source, 0);
    assert_eq!(value, 41, "the payload owner is returned in Err");
    assert_eq!(stats.allocations, 0);
    assert_eq!(stats.deallocations, 0);

    let run = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(run.exit, Some(41));
    assert_eq!(native_stats(&run).allocations, 0);
    assert_eq!(native_stats(&run).deallocations, 0);

    // An owning payload is also returned unchanged on refusal.
    let owning = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            match Box.try_new(Box.new(41)) {
                Ok(b) => Box.take(Box.take(b)),
                Err(inner) => Box.take(inner)
            }
        }";
    let (value, stats) = reference_with_budget(owning, 0);
    assert_eq!(value, 41);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    let run = native_run(owning, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(run.exit, Some(41));
    assert_eq!(native_stats(&run).allocations, 1);
    assert_eq!(native_stats(&run).deallocations, 1);
}

#[test]
fn non_widening_fallible_reuse_cannot_fail_and_preserves_owning_old_payloads() {
    let same = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> = Box.new(1);
            match Box.try_reuse(owner, 41) { Ok(b) => Box.take(b), Err(b) => Box.take(b) }
        }";
    let (value, stats) = reference_with_budget(same, 0);
    assert_eq!(
        value, 41,
        "a non-widening reuse performs no allocator action"
    );
    assert_eq!(stats.reuses, 1);
    let run = native_run(same, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(run.exit, Some(41));
    assert_eq!(native_stats(&run).reuses, 1);

    // On refusal the old owner and its nested payload are untouched.
    let owning = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let inner = Box.new(41);
            let owner: Box<Box<i64>> = Box.new(inner);
            let result: Result<Box<[i64; 2]>, Box<Box<i64>>> =
                Box.try_reuse(owner, [20, 22]);
            match result {
                Ok(b) => { let [a, c] = Box.take(b); a + c },
                Err(b) => Box.take(Box.take(b))
            }
        }";
    let (value, stats) = reference_with_budget(owning, 0);
    assert_eq!(value, 41);
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    let run = native_run(owning, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(run.exit, Some(41));
    assert_eq!(native_stats(&run).allocations, 2);
    assert_eq!(native_stats(&run).deallocations, 2);
}

#[test]
fn fallible_growth_reuse_preserves_the_old_owner_and_new_payload_on_refusal() {
    let source = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> = Box.new(7);
            let result: Result<Box<[i64; 2]>, Box<i64>> = Box.try_reuse(owner, [20, 22]);
            match result {
                Ok(b) => { let [a, c] = Box.take(b); a + c },
                Err(b) => Box.take(b)
            }
        }";
    let stats = agrees(source, 42);
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.reuses, 1);

    let (value, refused) = reference_with_budget(source, 0);
    assert_eq!(value, 7, "the old owner is returned intact on refusal");
    assert_eq!(refused.allocations, 1);
    assert_eq!(refused.reuses, 0);
    assert_eq!(refused.deallocations, 1);

    let run = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(run.exit, Some(7));
    let native = native_stats(&run);
    assert_eq!(native.allocations, 1);
    assert_eq!(native.reuses, 0);
    assert_eq!(native.deallocations, 1);
}

#[test]
fn fallible_reuse_rejects_owning_payloads_and_missing_result_shape() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let owner: Box<i64> = Box.new(1);
            let result = Box.try_reuse(owner, Box.new(2));
            42
        }",
        "requires a non-owning new payload",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            match Box.try_new(1) { _ => 42 }
        }",
        "requires enum Result<T,E>",
    );
}

#[test]
fn fallible_bytes_reports_overflow_and_native_allocator_refusal() {
    let huge = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            match Bytes.try_with_capacity(9223372036854775807) {
                Ok(b) => Bytes.len(&b),
                Err(requested) => if requested > 0 { 1 } else { 0 }
            }
        }";
    let (value, stats, _) = reference(huge);
    assert_eq!(value, 1);
    assert_eq!(stats.allocations, 0);
    assert_eq!(agrees(huge, 1).allocations, 0);

    let negative = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            match Bytes.try_with_capacity(-1) { Ok(b) => Bytes.len(&b), Err(n) => n + 2 }
        }";
    assert_eq!(reference(negative).0, 1);

    let small = "enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            match Bytes.try_with_capacity(4) { Ok(b) => Bytes.len(&b), Err(n) => n }
        }";
    let (value, stats) = reference_with_budget(small, 0);
    assert_eq!(value, 4);
    assert_eq!(stats.allocations, 0);
    let run = native_run(small, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(run.exit, Some(4));
    assert_eq!(native_stats(&run).allocations, 0);
    assert_eq!(agrees(small, 0).allocations, 1);
}

#[test]
fn fallible_allocation_does_not_mask_ordinary_abort_contracts() {
    // Ordinary Box.new still requires {alloc, panic}; the fallible spelling
    // requires only alloc and never turns refusal into an abort.
    rejects(
        "#[noalloc] fn f() -> i64 ! {panic} { match Box.try_new(1) { _ => 1 } }
         enum Result<T, E> { Ok(T), Err(E) }
         fn main() -> i64 ! {alloc, panic} { 0 }",
        "requires effects {alloc}",
    );
}

// ---------------------------------------------------------------------------
// Arena allocator ownership
// ---------------------------------------------------------------------------

#[test]
fn arena_boxes_outlive_the_arena_binding_and_clean_up_exactly_once() {
    let source = "fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let first = Arena.alloc(&arena, 20);
            let second = Arena.alloc(&arena, 22);
            drop(arena);
            ArenaBox.take(first) + ArenaBox.take(second)
        }";
    let stats = agrees(source, 42);
    assert_eq!(
        stats.allocations, 1,
        "the region descriptor is the region's logical allocation"
    );
    assert_eq!(stats.deallocations, 1);
    assert_eq!(stats.peak_live, 1);

    // Reading a copyable payload through the box borrow is also valid.
    let reads = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let value = Arena.alloc(&arena, 42);
            drop(arena);
            ArenaBox.read(&value)
        }",
        42,
    );
    assert_eq!(reads.allocations, 1);
}

#[test]
fn arena_boxes_destroy_owned_payloads_before_releasing_the_region() {
    let stats = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let boxed = Arena.alloc(&arena, Box.new(41));
            let inner = ArenaBox.take(boxed);
            drop(arena);
            Box.take(inner)
        }",
        41,
    );
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
}

#[test]
fn arena_provenance_rejects_use_after_move_and_owned_reads() {
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            drop(arena);
            let boxed = Arena.alloc(&arena, 1);
            ArenaBox.take(boxed)
        }",
        "cannot borrow a moved owner",
    );
    rejects(
        "fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let boxed = Arena.alloc(&arena, Box.new(1));
            let copied = ArenaBox.read(&boxed);
            drop(copied);
            42
        }",
        "cannot copy an owned payload",
    );
    rejects(
        "#[linear] enum Ticket { Live }
         fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let boxed = Arena.alloc(&arena, Ticket.Live);
            42
         }",
        "cannot place the linear value",
    );
}

#[test]
fn arena_boxes_can_cross_a_function_boundary_and_return() {
    agrees(
        "fn fill(arena: &Arena) -> ArenaBox<i64> ! {alloc, panic} {
            Arena.alloc(arena, 42)
        }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let boxed = fill(&arena);
            drop(arena);
            ArenaBox.take(boxed)
        }",
        42,
    );
}

#[test]
fn arena_box_captures_in_structured_tasks_are_destroyed_once() {
    let source = "use std.task.TaskExit;
        fn main() -> i64 ! {alloc, panic, suspend} {
            let arena = Arena.new();
            let boxed = Arena.alloc(&arena, 41);
            Task.scope(fn() -> Unit ! {alloc, panic, suspend} {
                let child = Task.spawn(fn() -> i64 ! {alloc, panic, suspend} {
                    Task.yield();
                    ArenaBox.take(boxed)
                });
                match Task.join(child) {
                    TaskExit.Completed(value) => {
                        if value == 41 { } else { panic() }
                    },
                    TaskExit.Cancelled => panic()
                }
            });
            drop(arena);
            42
        }";
    // Task control/result blocks are counted differently by the reference
    // scheduler and the native runtime, so parity here is on values and
    // balanced cleanup, not on a byte-identical task allocation count.
    let (value, stats, stdout) = reference(source);
    assert_eq!(value, 42);
    assert_eq!(stats.allocations, stats.deallocations);
    assert!(stdout.is_empty());
    let run = native_run(source, &[]);
    assert_eq!(run.exit, Some(42), "{}", run.stderr);
    assert!(run.stdout.is_empty());
    let native = native_stats(&run);
    assert_eq!(native.allocations, native.deallocations);
}
