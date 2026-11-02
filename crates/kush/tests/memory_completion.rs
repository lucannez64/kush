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

#[test]
fn two_fallible_allocation_stages_keep_pass_order_under_refusal() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        fn probe(x: i64) -> i64 ! {alloc} {
            match Box.try_new(x) {
                Ok(b) => { drop(b); 1 },
                Err(v) => 0,
            }
        }
        fn touch(x: i64) -> i64 ! {alloc} {
            match Box.try_new(x) {
                Ok(b) => Box.take(b),
                Err(v) => v,
            }
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [10, 20];
            let out = Vec.map_in_place(Vec.map_in_place(values, probe), touch);
            Vec.get(&out, 0) + Vec.get(&out, 1)
        }"#;
    // Unfused: probe gets both successful allocations before touch runs. An
    // interleaved traversal would spend the second success in touch(element0)
    // and incorrectly turn probe(element1)'s result from one into zero.
    let (value, _) = reference_with_budget(source, 2);
    assert_eq!(value, 2, "allocation refusal is a program-visible result");
    assert_eq!(check(source).unwrap().fusion_count(), 0);
    let native = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "2")]);
    assert_eq!(native.exit, Some(2), "{}", native.stderr);
}

#[test]
fn owning_memory_wrappers_cannot_hide_borrowed_record_captures() {
    let prefix = r#"struct Window<'a> { view: &'a [i64] }
        fn main() -> i64 ! {alloc, panic} {
            let mut data: [i64; 1] = [42];
            let read = make(Window { view: &data[..] });
            data = [9];
            read()
        }"#;
    for (allocate, extract) in [
        ("Box.new(window)", "Box.take(boxed)"),
        ("Box.reuse_grow(Box.new(0), window)", "Box.take(boxed)"),
        ("Arena.alloc(&arena, window)", "ArenaBox.take(boxed)"),
    ] {
        let source = format!(
            "{prefix}\nfn make<'a>(window: Window<'a>) -> once fn() -> i64 ! {{panic}} ! {{alloc, panic}} {{
                let arena = Arena.new();
                let boxed = {allocate};
                fn() -> i64 ! {{panic}} {{
                    let w = {extract};
                    Slice.get(w.view, 0)
                }}
            }}"
        );
        rejects(&source, "borrowed");
    }
}

#[test]
fn fallible_reuse_that_fits_retained_capacity_cannot_refuse() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        struct Cell { x: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let owner = Box.new(1);
            match Box.try_reuse(owner, Cell { x: 42 }) {
                Ok(b) => { let cell = Box.take(b); cell.x },
                Err(b) => Box.take(b),
            }
        }"#;
    // The native allocator rounds an eight-byte box to a sixteen-byte class;
    // this two-word record fits without making a fallible allocation attempt.
    let native = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(native.exit, Some(42), "{}", native.stderr);
    let (reference, _) = reference_with_budget(source, 0);
    assert_eq!(
        reference, 42,
        "reference must retain the same usable box capacity"
    );
}

#[test]
fn narrowing_reuse_keeps_capacity_for_later_fallible_growth() {
    for setup in [
        "let wide = Box.new([1, 2]); let owner = Box.reuse(wide, 1);",
        "let small = Box.new(1); let wide = Box.reuse_grow(small, [1, 2]); let owner = Box.reuse(wide, 1);",
    ] {
        let source = format!(
            "enum Result<T, E> {{ Ok(T), Err(E) }} struct Cell {{ x: i64 }}
             fn main() -> i64 ! {{alloc, panic}} {{
                {setup}
                match Box.try_reuse(owner, Cell {{ x: 42 }}) {{
                    Ok(b) => {{ let cell = Box.take(b); cell.x }},
                    Err(b) => Box.take(b),
                }}
             }}"
        );
        assert_eq!(reference_with_budget(&source, 0).0, 42);
        let native = native_run(&source, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
        assert_eq!(native.exit, Some(42), "{}", native.stderr);
    }
}

#[test]
fn fallible_growth_capacity_is_exact_and_not_rounded_by_a_later_noop() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        struct Wide { x: i64, y: i64 }
        struct Wider { x: i64, y: i64, z: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let owner = Box.new(0);
            match Box.try_reuse(owner, Wide { x: 1, y: 2 }) {
                Ok(b) => {
                    let b = Box.reuse_grow(b, Wide { x: 2, y: 3 });
                    let b = Box.reuse(b, 1);
                    match Box.try_reuse(b, Wider { x: 1, y: 2, z: 3 }) {
                        Ok(wider) => { drop(wider); 99 },
                        Err(old) => Box.take(old),
                    }
                },
                Err(old) => { drop(old); 77 },
            }
        }"#;
    assert_eq!(reference_with_budget(source, 1).0, 1);
    let native = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "1")]);
    assert_eq!(native.exit, Some(1), "{}", native.stderr);
}

#[test]
fn stored_arena_reference_stays_borrowed_through_payload_evaluation() {
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let reference = &arena;
            let boxed = Arena.alloc(reference, { drop(arena); 42 });
            ArenaBox.take(boxed)
        }"#,
        "cannot move or drop an owner or view",
    );
}

#[test]
fn stored_arena_reference_can_end_after_successful_allocation() {
    agrees(
        r#"fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let reference = &arena;
            let boxed = Arena.alloc(reference, 42);
            drop(arena);
            ArenaBox.take(boxed)
        }"#,
        42,
    );
}

#[test]
fn cancellation_state_reads_are_not_automatically_fused() {
    let source = r#"fn observed(x: i64) -> i64 ! {} {
            if Task.check_cancel() { x } else { x }
        }
        fn identity(x: i64) -> i64 ! {} { x }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [42];
            let out = Vec.map_in_place(Vec.map_in_place(values, observed), identity);
            Vec.get(&out, 0)
        }"#;
    assert_eq!(check(source).unwrap().fusion_count(), 0);
    assert_eq!(reference(source).0, 42);
    assert_eq!(native_run(source, &[]).exit, Some(42));
}

#[test]
fn cancellation_state_reads_in_match_guards_are_not_automatically_fused() {
    let source = r#"fn observed(x: i64) -> i64 ! {} {
            match x { y if Task.check_cancel() => y, z => z }
        }
        fn identity(x: i64) -> i64 ! {} { x }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [42];
            let out = Vec.map_in_place(Vec.map_in_place(values, observed), identity);
            Vec.get(&out, 0)
        }"#;
    assert_eq!(check(source).unwrap().fusion_count(), 0);
    assert_eq!(reference(source).0, 42);
    assert_eq!(native_run(source, &[]).exit, Some(42));
}

fn reserve_budget_agrees(source: &str, budget: usize, expected: i64) -> MemoryStats {
    let (result, stats) = reference_with_budget(source, budget);
    assert_eq!(result, expected);
    let run = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", &budget.to_string())]);
    assert_eq!(run.exit, Some((expected & 255) as i32), "{}", run.stderr);
    assert_eq!(native_stats(&run), stats);
    stats
}

#[test]
fn fallible_vector_reserve_fits_size_class_without_spending_the_budget() {
    let stats = reserve_budget_agrees(
        r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = Vec.with_capacity(0);
            let values = match values.try_reserve(1) {
                Ok(v) => v, Err(v) => { drop(v); return 1; }
            };
            let values = Vec.push(values, 42);
            let values = match Vec.try_reserve(values, 1) {
                Ok(v) => { drop(v); return 2; }, Err(v) => v
            };
            Vec.get(&values, 0)
        }"#,
        0,
        42,
    );
    assert_eq!(stats.buffer_growths, 1);
    assert_eq!(stats.allocations, 1);
}

#[test]
fn fallible_vector_reserve_grows_once_then_preserves_contents_on_refusal() {
    let stats = reserve_budget_agrees(
        r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = Vec.with_capacity(0);
            let values = match Vec.try_reserve(values, 5) {
                Ok(v) => v, Err(v) => { drop(v); return 1; }
            };
            let values = Vec.push(values, 42);
            let values = match Vec.try_reserve(values, 5) {
                Ok(v) => { drop(v); return 2; }, Err(v) => v
            };
            Vec.get(&values, 0)
        }"#,
        1,
        42,
    );
    assert_eq!(stats.buffer_growths, 1);
}

#[test]
fn fallible_vector_reserve_rejects_invalid_requests_before_allocation_attempts() {
    let stats = reserve_budget_agrees(
        r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [42];
            let values = match Vec.try_reserve(values, -1) {
                Ok(v) => { drop(v); return 1; }, Err(v) => v
            };
            let values = match Vec.try_reserve(values, 9223372036854775807) {
                Ok(v) => { drop(v); return 2; }, Err(v) => v
            };
            let values = match Vec.try_reserve(values, 10) {
                Ok(v) => v, Err(v) => { drop(v); return 3; }
            };
            Vec.get(&values, 0)
        }"#,
        1,
        42,
    );
    assert_eq!(stats.buffer_growths, 1);
}

#[test]
fn fallible_vector_reserve_preserves_owning_elements_and_drops_them_once() {
    let stats = reserve_budget_agrees(
        r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<Box<i64>> = [Box.new(42)];
            let values = match Vec.try_reserve(values, 10) {
                Ok(v) => { drop(v); return 1; }, Err(v) => v
            };
            let length = Vec.len(&values);
            let values = Vec.clear(values);
            drop(values);
            length
        }"#,
        0,
        1,
    );
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.buffer_growths, 0);
}

#[test]
fn fallible_vector_reserve_retains_physical_capacity_after_map_narrowing() {
    reserve_budget_agrees(
        r#"enum Result<T, E> { Ok(T), Err(E) }
        fn first(pair: [i64; 4]) -> i64 ! {} { let [a, b, c, d] = pair; a }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<[i64; 4]> = [[42, 1, 2, 3]];
            let values = Vec.map_in_place(values, first);
            let values = match Vec.try_reserve(values, 3) {
                Ok(v) => v, Err(v) => { drop(v); return 1; }
            };
            let values = Vec.push(values, 9);
            Vec.get(&values, 0)
        }"#,
        0,
        42,
    );
}

#[test]
fn vector_capacity_operations_preserve_linear_owner_obligations() {
    for operation in [
        "Vec.try_reserve(values, 0)",
        "Vec.reserve(values, 0)",
        "Vec.clear(values)",
    ] {
        let source = format!(
            "enum Result<T, E> {{ Ok(T), Err(E) }}
             fn make() -> Vec<i64> @[1] ! {{alloc, panic}} {{ [42] }}
             fn main() -> i64 ! {{alloc, panic}} {{
                let values = make(); drop({operation}); 0
             }}"
        );
        rejects(&source, "linear");
    }
}

#[test]
fn fallible_vector_reserve_requires_allocation_effect_and_an_owned_receiver() {
    rejects(
        "enum Result<T, E> { Ok(T), Err(E) }
         #[noalloc] fn reserve(v: Vec<i64>) -> Result<Vec<i64>, Vec<i64>> ! {} { Vec.try_reserve(v, 0) }
         fn main() -> i64 ! {} { 0 }",
        "alloc",
    );
    rejects(
        "enum Result<T, E> { Ok(T), Err(E) }
         fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [42]; drop(Vec.try_reserve(&values, 1)); 0
         }",
        "owned Vec",
    );
}

#[test]
fn fallible_vector_reserve_keeps_argument_order_and_early_return_cleanup() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        fn make() -> Vec<i64> ! {alloc, panic, io} { print_i64(1); [42] }
        fn main() -> i64 ! {alloc, panic, io} {
            match Vec.try_reserve(make(), { print_i64(2); 0 }) {
                Ok(v) => { print_i64(3); Vec.get(&v, 0) },
                Err(v) => { drop(v); 0 }
            }
        }"#;
    agrees(source, 42);
    assert_eq!(reference(source).2, b"1\n2\n3\n");
    let stats = agrees(
        r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<Box<i64>> = [Box.new(42)];
            drop(Vec.try_reserve(values, { return 42; })); 0
        }"#,
        42,
    );
    assert_eq!(stats.allocations, 2);
}

// ---------------------------------------------------------------------------
// Fallible arena allocation and user chunk strategy
// ---------------------------------------------------------------------------

#[test]
fn fallible_arena_returns_the_payload_and_preserves_the_region_on_refusal() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            match Arena.try_alloc(&arena, 42) {
                Ok(b) => { drop(arena); ArenaBox.take(b) },
                Err(v) => { drop(arena); v }
            }
        }"#;
    assert_eq!(reference_with_budget(source, 0).0, 42);
    assert_eq!(reference(source).0, 42);
    let refused = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(refused.exit, Some(42), "{}", refused.stderr);
    let allowed = native_run(source, &[]);
    assert_eq!(allowed.exit, Some(42), "{}", allowed.stderr);
}

#[test]
fn refused_arena_chunk_request_leaves_the_region_usable() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            match Arena.try_alloc(&arena, 7) {
                Ok(b) => { drop(b); 0 },
                Err(first) => {
                    let later = Arena.alloc(&arena, 9);
                    first + ArenaBox.take(later)
                }
            }
        }"#;
    // The fallible probe refuses the first chunk. The ordinary allocation
    // ignores the probe and must still see an untouched, usable region.
    assert_eq!(reference_with_budget(source, 0).0, 16);
    let refused = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(refused.exit, Some(16), "{}", refused.stderr);
}

#[test]
fn fallible_arena_spends_the_budget_only_on_a_real_chunk_request() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            let first = match Arena.try_alloc(&arena, 1) {
                Ok(b) => ArenaBox.take(b),
                Err(v) => v,
            };
            let second = match Arena.try_alloc(&arena, 2) {
                Ok(b) => ArenaBox.take(b),
                Err(v) => v,
            };
            let third = match Arena.try_alloc(&arena, 3) {
                Ok(b) => ArenaBox.take(b),
                Err(v) => v,
            };
            drop(arena);
            first + second + third
        }"#;
    // The first request creates a 4 KiB chunk; the next two fit without any
    // fallible allocator attempt, so a one-success budget still returns 6.
    assert_eq!(reference_with_budget(source, 1).0, 6);
    let run = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "1")]);
    assert_eq!(run.exit, Some(6), "{}", run.stderr);
}

#[test]
fn user_chunk_strategy_changes_fallible_arena_growth_behavior() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        fn exact(need: i64, current: i64) -> i64 ! {} {
            if need < 1 { 1 } else { need }
        }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.with_strategy(exact);
            let first = match Arena.try_alloc(&arena, 10) {
                Ok(b) => ArenaBox.take(b),
                Err(v) => v,
            };
            let second = match Arena.try_alloc(&arena, 20) {
                Ok(b) => { drop(b); 1 },
                Err(v) => v,
            };
            drop(arena);
            first + second
        }"#;
    // With an exact-chunk strategy, the second request needs a fresh chunk and
    // therefore fails under a one-attempt budget: 10 + 20 = 30.
    assert_eq!(reference_with_budget(source, 1).0, 30);
    let exact = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "1")]);
    assert_eq!(exact.exit, Some(30), "{}", exact.stderr);

    // The default 4 KiB chunk accepted both requests with the same budget.
    let summed = source.replace("Arena.with_strategy(exact)", "Arena.new()");
    assert_eq!(reference_with_budget(&summed, 1).0, 11);
    let default = native_run(&summed, &[("KUSH_ALLOC_FAIL_AFTER", "1")]);
    assert_eq!(default.exit, Some(11), "{}", default.stderr);
}

#[test]
fn arena_strategy_owns_no_environment_and_survives_the_arena_owner() {
    agrees(
        r#"fn exact(need: i64, current: i64) -> i64 ! {} { need }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.with_strategy(exact);
            let first = Arena.alloc(&arena, 20);
            let second = Arena.alloc(&arena, 22);
            drop(arena);
            ArenaBox.take(first) + ArenaBox.take(second)
        }"#,
        42,
    );
}

#[test]
fn arena_strategy_rejects_capturing_effectful_and_mismatched_functions() {
    rejects(
        r#"fn capture(strategy: once fn(i64, i64) -> i64 ! {}) -> Arena ! {alloc, panic} {
            Arena.with_strategy(strategy)
        }
        fn main() -> i64 ! {alloc, panic} { 0 }"#,
        "noncapturing fn(i64, i64) -> i64",
    );
    rejects(
        r#"fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.with_strategy(fn() -> i64 ! {} { 1 });
            0
        }"#,
        "exact fn(i64, i64) -> i64",
    );
    rejects(
        r#"fn allocates(need: i64, current: i64) -> i64 ! {alloc} {
            let b = Box.new(need);
            Box.take(b) + current
        }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.with_strategy(allocates);
            0
        }"#,
        "pure strategy",
    );
    rejects(
        r#"fn wrong(need: i64) -> i64 ! {} { need }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.with_strategy(wrong);
            0
        }"#,
        "exact fn(i64, i64) -> i64",
    );
}

// ---------------------------------------------------------------------------
// Vector element widening reuse
// ---------------------------------------------------------------------------

#[test]
fn vector_map_grow_widens_elements_and_reports_one_growth() {
    let stats = agrees(
        r#"fn widen(x: i64) -> [i64; 4] ! {panic} { [x, x + 1, x + 2, x + 3] }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [1, 2];
            let values = Vec.map_in_place_grow(values, widen);
            let [a, b, c, d] = Vec.get(&values, 1);
            a + b + c + d
        }"#,
        14,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.buffer_growths, 1);
}

#[test]
fn vector_map_grow_reuses_retained_physical_capacity_without_growth() {
    let stats = agrees(
        r#"fn first(pair: [i64; 4]) -> i64 ! {} { let [a, b, c, d] = pair; a }
        fn pair(x: i64) -> [i64; 2] ! {panic} { [x, x + 1] }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<[i64; 4]> = [[1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3], [4, 4, 4, 4]];
            let values = Vec.map_in_place(values, first);
            let values = Vec.map_in_place_grow(values, pair);
            let [a, b] = Vec.get(&values, 3);
            a * 10 + b
        }"#,
        45,
    );
    // The narrowed map retained the wide allocation; widening back to two
    // words fits, so no allocator growth is charged.
    assert_eq!(stats.buffer_growths, 0);
}

#[test]
fn vector_map_grow_applies_callbacks_forward_and_moves_elements_safely() {
    let source = r#"fn widen(x: i64) -> [i64; 2] ! {io, panic} { print_i64(x); [x, x + 1] }
        fn main() -> i64 ! {alloc, panic, io} {
            let values: Vec<i64> = [1, 2, 3];
            let values = Vec.map_in_place_grow(values, widen);
            let [a, b] = Vec.get(&values, 2);
            a * 10 + b
        }"#;
    agrees(source, 34);
    assert_eq!(reference(source).2, b"1\n2\n3\n");
}

#[test]
fn vector_map_grow_consumes_owning_elements_exactly_once() {
    let stats = agrees(
        r#"fn unwrap(boxed: Box<i64>) -> [i64; 2] ! {panic} {
            [Box.take(boxed), 1]
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<Box<i64>> = [Box.new(5), Box.new(6)];
            let values = Vec.map_in_place_grow(values, unwrap);
            let [a, b] = Vec.get(&values, 0);
            let [c, d] = Vec.get(&values, 1);
            a + b + c + d
        }"#,
        13,
    );
    assert_eq!(stats.allocations, 3);
}

#[test]
fn vector_map_grow_keeps_the_new_stride_for_later_operations() {
    agrees(
        r#"fn widen(x: i64) -> [i64; 3] ! {} { [x, x, x] }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [1, 2];
            let values = Vec.map_in_place_grow(values, widen);
            let values = Vec.push(values, [7, 8, 9]);
            let [a, b, c] = Vec.get(&values, 2);
            let [x, y, z] = Vec.get(&values, 1);
            a + b + c + x + y + z
        }"#,
        30,
    );
}

#[test]
fn vector_map_chain_grow_widens_the_final_layout() {
    agrees(
        r#"fn wide(x: i64) -> [i64; 4] ! {panic} { [x, x + 1, x + 2, x + 3] }
        fn narrow(pair: [i64; 4]) -> [i64; 2] ! {panic} {
            let [a, b, c, d] = pair;
            [a + c, b + d]
        }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [1, 2];
            let values = Vec.map_chain_in_place_grow(values, wide, narrow);
            let [a, b] = Vec.get(&values, 1);
            a * 10 + b
        }"#,
        68,
    );
}

#[test]
fn vector_map_grow_does_not_create_automatic_fusions() {
    let source = r#"fn widen(x: i64) -> [i64; 2] ! {} { [x, x] }
        fn first(pair: [i64; 2]) -> i64 ! {} { let [a, b] = pair; a }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [1, 2];
            let values = Vec.map_in_place(Vec.map_in_place_grow(values, widen), first);
            Vec.get(&values, 0) + Vec.get(&values, 1)
        }"#;
    assert_eq!(reference(source).0, 3);
    assert_eq!(check(source).unwrap().fusion_count(), 0);
}

#[test]
fn vector_map_grow_requires_alloc_panic_and_an_owned_receiver() {
    rejects(
        r#"fn widen(x: i64) -> [i64; 2] ! {} { [x, x] }
        #[noalloc] fn transform(values: Vec<i64>) -> Vec<[i64; 2]> ! {panic} {
            Vec.map_in_place_grow(values, widen)
        }
        fn main() -> i64 ! {} { 0 }"#,
        "alloc",
    );
    rejects(
        r#"fn widen(x: i64) -> [i64; 2] ! {} { [x, x] }
        fn main() -> i64 ! {alloc, panic} {
            let values: Vec<i64> = [1];
            drop(Vec.map_in_place_grow(&values, widen));
            0
        }"#,
        "owned Vec",
    );
}

#[test]
fn refused_arena_allocation_returns_a_structured_payload_unchanged() {
    let source = r#"enum Result<T, E> { Ok(T), Err(E) }
        struct Pair { left: i64, right: i64 }
        fn main() -> i64 ! {alloc, panic} {
            let arena = Arena.new();
            match Arena.try_alloc(&arena, Pair { left: 20, right: 22 }) {
                Ok(b) => { drop(arena); let pair = ArenaBox.take(b); pair.left + pair.right },
                Err(pair) => { drop(arena); pair.left + pair.right }
            }
        }"#;
    assert_eq!(reference_with_budget(source, 0).0, 42);
    let refused = native_run(source, &[("KUSH_ALLOC_FAIL_AFTER", "0")]);
    assert_eq!(refused.exit, Some(42), "{}", refused.stderr);
}
