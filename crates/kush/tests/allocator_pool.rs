//! Bounded native allocator pool. Small native allocations are served from
//! 16-byte size classes with retained storage capped at 1 MiB. Pooling is a
//! physical optimization only: the stable `allocation-stats:` line must stay
//! byte-identical to the reference evaluator. The opt-in
//! `KUSH_ALLOCATOR_POOL_STATS=1` variable adds one native-only
//! `allocator-pool:` line that makes hits, misses, retention, the size-class
//! boundary, and the retained-byte bound observable.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::{
    executable::{self, Executable, MemoryStats},
    native::{self, Scratch},
};
use std::process::Command;

const RETAIN_CAP: u64 = 1024 * 1024;

fn check(source: &str) -> Executable {
    executable::check(source).unwrap()
}

fn reference(source: &str) -> (i64, MemoryStats, Vec<u8>) {
    let program = check(source);
    let mut output = Vec::new();
    let (result, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    (result, stats, output)
}

struct Run {
    exit: Option<i32>,
    stdout: Vec<u8>,
    stderr: String,
}

fn parse_stats(line: &str) -> MemoryStats {
    let field = |name: &str| -> usize {
        line.split_whitespace()
            .find_map(|part| part.strip_prefix(name))
            .and_then(|value| value.strip_prefix('='))
            .and_then(|value| value.parse().ok())
            .unwrap_or_else(|| panic!("missing {name} in {line:?}"))
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

fn run_with(source: &str, pool_stats: bool) -> Run {
    let program = check(source);
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("allocator-pool-test");
    native::build_with_stats(&program, &binary, true).unwrap();
    let mut command = Command::new(&binary);
    command.current_dir(scratch.path());
    if pool_stats {
        command.env("KUSH_ALLOCATOR_POOL_STATS", "1");
    }
    let output = command.output().unwrap();
    Run {
        exit: output.status.code(),
        stdout: output.stdout,
        stderr: String::from_utf8(output.stderr).unwrap(),
    }
}

fn stats_line(run: &Run) -> &str {
    let lines = run
        .stderr
        .lines()
        .filter(|line| line.starts_with("allocation-stats: "))
        .collect::<Vec<_>>();
    assert_eq!(lines.len(), 1, "{}", run.stderr);
    lines[0]
}

#[derive(Debug, Default, Clone, Copy)]
struct Pool {
    hits: u64,
    misses: u64,
    retains: u64,
    releases: u64,
    drained: u64,
    retained: u64,
    peak_retained: u64,
}

fn pool_line(run: &Run) -> Option<Pool> {
    let line = run
        .stderr
        .lines()
        .find(|line| line.starts_with("allocator-pool: "))?;
    let mut pool = Pool::default();
    for part in line.split_whitespace().skip(1) {
        let (name, value) = part
            .split_once('=')
            .unwrap_or_else(|| panic!("malformed field {part:?} in {line:?}"));
        let value: u64 = value.parse().unwrap();
        match name {
            "hits" => pool.hits = value,
            "misses" => pool.misses = value,
            "retains" => pool.retains = value,
            "releases" => pool.releases = value,
            "drained" => pool.drained = value,
            "retained-bytes" => pool.retained = value,
            "peak-retained-bytes" => pool.peak_retained = value,
            other => panic!("unexpected pool field {other:?} in {line:?}"),
        }
    }
    assert_eq!(
        pool.retained, 0,
        "retained storage must be drained on a normal exit: {line:?}"
    );
    assert!(pool.peak_retained <= RETAIN_CAP, "{line:?}");
    Some(pool)
}

/// Both backends must agree on values, stdout, exit status, and the stable
/// one-line allocation diagnostics while the pool line reports physical state.
fn agrees(source: &str, expected: i64) -> (MemoryStats, Pool) {
    let program = check(source);
    let mut expected_output = Vec::new();
    let (reference_result, reference_stats) =
        program.evaluate_with_stats(&mut expected_output).unwrap();
    assert_eq!(reference_result, expected, "{source}");
    let run = run_with(source, true);
    assert_eq!(
        run.exit,
        Some((expected as u64 & 255) as i32),
        "{}",
        run.stderr
    );
    assert_eq!(run.stdout, expected_output, "{}", run.stderr);
    assert_eq!(
        stats_line(&run),
        reference_stats.report(),
        "physical pooling must not change logical diagnostics: {source}"
    );
    let pool = pool_line(&run).expect("missing allocator-pool line");
    (reference_stats, pool)
}

#[test]
fn pool_diagnostics_are_opt_in_and_never_change_the_stable_line() {
    let source = "fn main() -> i64 ! {alloc, panic} {
        let a = Box.new(7);
        let b = Box.new(8);
        Box.take(a) + Box.take(b)
    }";
    let without = run_with(source, false);
    let with = run_with(source, true);
    assert_eq!(without.exit, Some(15));
    assert_eq!(with.exit, Some(15));
    assert_eq!(without.stdout, with.stdout);
    assert!(
        pool_line(&without).is_none(),
        "the allocator-pool line is opt-in: {}",
        without.stderr
    );
    let (_, stats, _) = reference(source);
    assert_eq!(stats_line(&without), stats.report());
    assert_eq!(
        stats_line(&with),
        stats.report(),
        "the opt-in line never alters allocation-stats"
    );
    assert_eq!(without.stderr.lines().count(), 1);
    assert_eq!(with.stderr.lines().count(), 2);
}

#[test]
fn repeated_boxes_reuse_one_retained_size_class() {
    let (stats, pool) = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut sum = 0;
            let mut i = 0;
            while i < 64 {
                let owner = Box.new(i);
                sum = sum + Box.take(owner);
                i = i + 1;
            }
            sum
        }",
        2016,
    );
    assert_eq!(stats.allocations, 64, "one box allocation per iteration");
    assert_eq!(stats.deallocations, 64);
    assert_eq!(stats.peak_live, 1, "each box dies before the next is made");
    assert_eq!(stats.buffer_growths, 0);
    assert_eq!(
        pool.misses, 1,
        "one system block for the 8-byte payload class"
    );
    assert_eq!(pool.hits, 63, "every later box is served from the pool");
    assert_eq!(pool.retains, 64);
    assert_eq!(pool.drained, 1, "only one distinct block was ever retained");
    assert_eq!(pool.releases, 0);
    assert_eq!(
        pool.peak_retained, 48,
        "32-byte header plus a 16-byte class"
    );
}

#[test]
fn repeated_bytes_and_vectors_keep_counts_and_values() {
    let (stats, pool) = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut bytes = Bytes.with_capacity(4);
            let mut values: Vec<i64> = Vec.with_capacity(4);
            let mut i = 0;
            while i < 8 {
                bytes = Bytes.push(bytes, i);
                values = Vec.push(values, i * 3);
                i = i + 1;
            }
            let bytes = Box.take(Box.new(bytes));
            let values = Box.take(Box.new(values));
            let mut sum = Bytes.len(&bytes) + Vec.len(&values);
            let mut j = 0;
            while j < Vec.len(&values) {
                sum = sum + Vec.get(&values, j) + Bytes.get(&bytes, j);
                j = j + 1;
            }
            sum
        }",
        8 + 8 + 84 + 28,
    );
    assert_eq!(stats.allocations, 4, "two buffers, two boxes");
    assert_eq!(stats.deallocations, 4);
    assert_eq!(stats.buffer_growths, 2, "one growth per full fixed buffer");
    assert!(pool.hits >= 1, "the two boxes reuse a shared 16-byte class");
    assert_eq!(pool.retained, 0);
}

#[test]
fn zero_capacity_and_the_size_class_boundary_are_exact() {
    // A zero-capacity buffer still allocates its 16-byte struct header and is
    // pooled in the smallest class.
    let (stats, pool) = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let empty = Bytes.with_capacity(0);
            Bytes.len(&empty) + Bytes.capacity(&empty)
        }",
        0,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(pool.misses, 1);
    assert_eq!(
        pool.peak_retained, 48,
        "32-byte header plus a 16-byte class"
    );

    // A 1024-byte payload is the largest pooled block (struct header 16 +
    // capacity 1008).
    let (stats, pool) = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let buffer = Bytes.with_capacity(1008);
            let capacity = Bytes.capacity(&buffer);
            drop(buffer);
            capacity
        }",
        1008,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    assert_eq!(pool.misses, 1);
    assert_eq!(pool.retains, 1);
    assert_eq!(pool.releases, 0);
    assert_eq!(
        pool.peak_retained, 1056,
        "32-byte header plus a 1024-byte class"
    );

    // One byte more (1025-byte payload) is unpooled: no miss, no retention,
    // and the block returns to the system immediately.
    let (stats, pool) = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let buffer = Bytes.with_capacity(1009);
            let capacity = Bytes.capacity(&buffer);
            drop(buffer);
            capacity
        }",
        1009,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    assert_eq!(pool.misses, 0, "requests above 1024 bytes bypass the pool");
    assert_eq!(pool.retains, 0);
    assert_eq!(pool.releases, 1);
    assert_eq!(pool.drained, 0);
    assert_eq!(pool.peak_retained, 0);
}

#[test]
fn buffer_growth_from_pooled_storage_preserves_contents() {
    // A vector starts in the pooled range, grows through several classes, and
    // crosses the 1024-byte boundary into unpooled system blocks.
    let (stats, pool) = agrees(
        "fn main() -> Unit ! {io, alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            let mut i = 0;
            while i < 400 {
                values = Vec.push(values, i);
                i = i + 1;
            }
            let mut sum = 0;
            let mut j = 0;
            while j < Vec.len(&values) {
                sum = sum + Vec.get(&values, j);
                j = j + 1;
            }
            print_i64(sum);
            print_i64(Vec.len(&values));
        }",
        0,
    );
    assert_eq!(stats.allocations, 1, "growth reallocates, never allocates");
    assert_eq!(stats.buffer_growths, 8);
    assert_eq!(pool.hits, 0);
    assert_eq!(pool.misses, 6, "initial block plus five pooled growths");
    assert_eq!(pool.retains, 6);
    assert_eq!(
        pool.releases, 3,
        "three grown buffers exceed the class limit"
    );
    assert_eq!(
        pool.peak_retained, 1376,
        "header plus padded payload per retained block"
    );
    assert_eq!(pool.drained, 6);

    // Byte buffers also exercise the case where a logical growth fits inside
    // the retained size class, so no new physical block is requested, and the
    // growth counter still matches the reference exactly.
    let (stats, pool) = agrees(
        "fn main() -> Unit ! {io, alloc, panic} {
            let mut bytes = Bytes.with_capacity(0);
            let mut i = 0;
            while i < 3000 {
                bytes = Bytes.push(bytes, i % 256);
                i = i + 1;
            }
            let mut sum = 0;
            let mut j = 0;
            while j < Bytes.len(&bytes) {
                sum = sum + Bytes.get(&bytes, j);
                j = j + 1;
            }
            print_i64(Bytes.len(&bytes));
            print_i64(Bytes.capacity(&bytes));
            print_i64(sum);
        }",
        0,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.buffer_growths, 10);
    assert_eq!(pool.hits, 0);
    assert_eq!(pool.misses, 7);
    assert_eq!(pool.retains, 7);
    assert_eq!(pool.releases, 3);
    assert_eq!(
        pool.peak_retained, 1344,
        "header plus padded payload per retained block"
    );
}

#[test]
fn clear_reserve_and_push_reserved_integrate_with_the_pool() {
    // `clear` retains the allocation; `reserve` grows exactly once through the
    // header-aware path and the existing elements survive the move.
    let (stats, pool) = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 3);
            values = Vec.push(values, 4);
            values = values.reserve(64);
            let first = Vec.get(&values, 0);
            let second = Vec.get(&values, 1);
            let cleared = values.clear();
            Vec.len(&cleared) + first * 10 + second
        }",
        34,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    assert_eq!(stats.buffer_growths, 2, "first push plus reserve");
    assert!(
        pool.peak_retained >= 576,
        "header plus the grown 544-byte class"
    );

    // `push_reserved` is still a non-allocating operation under `#[noalloc]`
    // and never grows; the pooled allocation happens in the caller.
    let (stats, pool) = agrees(
        "#[noalloc]
         fn append(buffer: Bytes, byte: i64) -> Bytes ! {panic} {
             Bytes.push_reserved(buffer, byte)
         }
         fn main() -> i64 ! {alloc, panic} {
             let buffer = append(Bytes.with_capacity(1), 7);
             Bytes.len(&buffer) + Bytes.get(&buffer, 0)
         }",
        8,
    );
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.buffer_growths, 0);
    assert_eq!(pool.misses, 1);
    assert_eq!(
        pool.peak_retained, 64,
        "32-byte header plus the 32-byte class"
    );
}

#[test]
fn retention_never_exceeds_the_one_mebibyte_cap() {
    // 70000 distinct 16-byte class blocks are retained until the cap; the rest
    // must return to the system instead of growing the cache without bound.
    // The reference evaluator's step budget cannot model this many allocations,
    // so the native totals are pinned directly; every other test compares the
    // stable line with the reference.
    let source = "fn main() -> i64 ! {alloc, panic} {
        let mut values: Vec<Box<i64>> = Vec.new();
        let mut i = 0;
        while i < 70000 {
            values = Vec.push(values, Box.new(i));
            i = i + 1;
        }
        Vec.len(&values)
    }";
    let run = run_with(source, true);
    assert_eq!(run.exit, Some((70000i64 & 255) as i32), "{}", run.stderr);
    let stats = parse_stats(stats_line(&run));
    assert_eq!(stats.allocations, 70001, "70000 boxes plus the vector");
    assert_eq!(stats.deallocations, 70001);
    assert_eq!(stats.peak_live, 70001);
    assert_eq!(stats.buffer_growths, 16);
    let pool = pool_line(&run).expect("missing allocator-pool line");
    assert!(
        pool.peak_retained <= RETAIN_CAP,
        "the cap is never exceeded"
    );
    assert!(
        pool.peak_retained >= RETAIN_CAP - 1024,
        "the cache fills to the cap before overflow blocks are released"
    );
    assert!(
        pool.releases > 0,
        "blocks over the cap are returned to the system"
    );
    assert_eq!(pool.retained, 0, "the drain releases the whole cache");
    assert!(pool.drained > 0);
}

#[test]
fn task_blocks_use_the_same_header_aware_path_and_stats_are_unchanged() {
    let source = "use std.task.TaskExit;
        fn worker(n: i64) -> i64 ! {panic} { n * 2 }
        fn main() -> Unit ! {io, alloc, panic, suspend} {
            Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
                let a: Task<i64> = Task.spawn(fn() -> i64 ! {panic, suspend} { worker(1) });
                match Task.join(a) {
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }
                let b: Task<i64> = Task.spawn(fn() -> i64 ! {panic, suspend} { worker(2) });
                match Task.join(b) {
                    TaskExit.Completed(v) => print_i64(v),
                    TaskExit.Cancelled => print_i64(-1),
                }
            })
        }";
    let (reference_result, _, expected_output) = reference(source);
    assert_eq!(reference_result, 0);
    let run = run_with(source, true);
    assert_eq!(run.exit, Some(0), "{}", run.stderr);
    assert_eq!(run.stdout, expected_output);
    let stats = parse_stats(stats_line(&run));
    // The reference evaluator models tasks without native stacks, so the task
    // test pins the native totals instead of comparing them with the reference.
    assert_eq!(stats.allocations, 8, "root, scheduler stack, two spawns");
    assert_eq!(stats.deallocations, 8);
    assert_eq!(stats.peak_live, 5);
    assert_eq!(stats.buffer_growths, 0);
    let pool = pool_line(&run).expect("missing allocator-pool line");
    assert!(
        pool.hits >= 1,
        "the second task result buffer reuses the first class"
    );
    assert_eq!(pool.drained, 1);
    assert_eq!(pool.peak_retained, 48, "one task result class block");
}

#[test]
fn nested_owner_cleanup_and_invalid_free_contracts_are_unchanged() {
    // Nested owning boxes are freed exactly once each through the header path.
    let (stats, pool) = agrees(
        "fn main() -> i64 ! {alloc, panic} {
            let inner = Box.new(41);
            let outer = Box.new(inner);
            let owner = Box.take(outer);
            let value = Box.read(&owner);
            Box.take(owner) + value
        }",
        82,
    );
    assert_eq!(stats.allocations, 2);
    assert_eq!(stats.deallocations, 2);
    assert_eq!(stats.peak_live, 2);
    assert_eq!(pool.misses, 2, "both boxes are live before the first free");
    assert_eq!(pool.hits, 0);
    assert_eq!(
        pool.drained, 2,
        "both 8-byte blocks are retained and drained"
    );
    assert_eq!(pool.peak_retained, 96, "two class-16 blocks with headers");

    // The `alloc` effect and `#[noalloc]` rejection are source contracts and
    // must not be weakened by the physical pool.
    let noalloc_box = executable::check(
        "#[noalloc]
         fn make(x: i64) -> Box<i64> ! {panic} { Box.new(x) }
         fn main() -> i64 ! {alloc, panic} { 42 }",
    )
    .unwrap_err();
    assert!(
        noalloc_box
            .message
            .contains("operation requires effects {alloc}"),
        "{noalloc_box:?}"
    );
    let noalloc_vec = executable::check(
        "#[noalloc]
         fn push(values: Vec<i64>, value: i64) -> Vec<i64> ! {panic} {
             Vec.push(values, value)
         }
         fn main() -> i64 ! {alloc, panic} { 42 }",
    )
    .unwrap_err();
    assert!(noalloc_vec.message.contains("alloc"), "{noalloc_vec:?}");

    // Overflowing reserve is still rejected by the checked grow path instead
    // of reaching the allocator with a wrapped size.
    let program = executable::check(
        "fn main() -> i64 ! {alloc, panic} {
            let mut values: Vec<i64> = Vec.new();
            values = Vec.push(values, 1);
            let values = Vec.reserve(values, 9223372036854775807);
            Vec.len(&values)
        }",
    )
    .unwrap();
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("allocator-pool-overflow");
    native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).output().unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("panic:"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
