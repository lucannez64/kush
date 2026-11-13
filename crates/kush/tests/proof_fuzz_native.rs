//! PROOF-FUZZ step 2: a fuzz build instruments every obligation site. A run
//! writes a record to `$KUSH_FUZZ_OUT` naming the site whose check failed
//! (or how the program ended otherwise), with each site's hit count and the
//! smallest distance from failing it saw. See docs/proof-fuzz.md.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::executable::{Executable, check};
use kush::fuzz::{self, Outcome, RunRecord};
use kush::native::{self, LinkSpec, Scratch};

struct Run {
    program: Executable,
    source: String,
    record: RunRecord,
}

impl Run {
    /// The source text of a site.
    fn text(&self, site: usize) -> &str {
        let span = self.program.obligation_sites()[site].span;
        &self.source[span.start..span.end]
    }
    /// The site whose source text is `text`.
    fn site(&self, text: &str) -> usize {
        let sites = self.program.obligation_sites();
        let found: Vec<usize> = (0..sites.len()).filter(|&s| self.text(s) == text).collect();
        assert_eq!(found.len(), 1, "sites with text {text:?}: {found:?}");
        found[0]
    }
    fn failed_text(&self) -> &str {
        match self.record.outcome {
            Outcome::Failed(site) => self.text(site),
            other => panic!("expected a failed site, got {other:?}"),
        }
    }
}

fn run(source: &str) -> Run {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("fuzzed");
    fuzz::build(&program, &binary, &LinkSpec::default()).unwrap();
    let out = scratch.path().join("record");
    let status = std::process::Command::new(&binary)
        .env(fuzz::OUT_VARIABLE, &out)
        .stderr(std::process::Stdio::null())
        .status()
        .unwrap();
    let bytes = std::fs::read(&out).unwrap_or_else(|e| panic!("no record ({status}): {e}"));
    let record = RunRecord::parse(&bytes).expect("a complete run record");
    assert_eq!(record.sites.len(), program.obligation_sites().len());
    Run {
        program,
        source: source.to_owned(),
        record,
    }
}

#[test]
fn an_overflow_names_its_site() {
    let run = run("fn add(a: i64, b: i64) -> i64 ! {panic} { a + b }
fn main() -> i64 ! {panic} { add(1, 2) + add(9223372036854775807, 1) }");
    assert_eq!(run.failed_text(), "a + b");
    let site = run.site("a + b");
    assert_eq!(run.record.sites[site].hits, 2);
    assert_eq!(run.record.sites[site].margin, -1);
}

#[test]
fn margins_measure_the_distance_from_failing() {
    let run = run("fn bump(x: u8, y: u8) -> u8 ! {panic} { x + y }
fn neg(x: i8) -> i8 ! {panic} { -x }
fn at(v: &Vec<i64>, i: i64) -> i64 ! {panic} { v[i] }
fn div(a: i64, b: i64) -> i64 ! {panic} { a / b }
fn shift(a: u8, b: u8) -> u8 ! {panic} { a >> b }
fn main() -> i64 ! {alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(1);
    v = v.push(2);
    v = v.push(3);
    let a: i64 = Int.convert(bump(250, 3));
    let b: i64 = Int.convert(neg(5));
    let c = at(&v, 1) + at(&v, 2);
    let d = div(10, 4);
    let e: i64 = Int.convert(shift(255, 6));
    a + b + c + d + e
}");
    assert_eq!(run.record.outcome, Outcome::Exited);
    let margin = |text: &str| run.record.sites[run.site(text)].margin;
    // 253 is 2 below u8's maximum.
    assert_eq!(margin("x + y"), 2);
    // -5 is 123 above i8's minimum and 132 below its maximum.
    assert_eq!(margin("-x"), 123);
    // Index 1 and 2 of three elements: 2 is the last one.
    assert_eq!(margin("v[i]"), 0);
    assert_eq!(run.record.sites[run.site("v[i]")].hits, 2);
    // A divisor of 4 is 3 away from zero.
    assert_eq!(margin("a / b"), 3);
    // A shift by 6 is 1 below u8's width.
    assert_eq!(margin("a >> b"), 1);
}

#[test]
fn bounds_division_and_shift_failures_name_their_sites() {
    let bounds = run("fn at(v: &Vec<i64>, i: i64) -> i64 ! {panic} { v[i] }
fn main() -> i64 ! {alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(1);
    at(&v, 0) + at(&v, 3)
}");
    assert_eq!(bounds.failed_text(), "v[i]");
    let division = run("fn div(a: i64, b: i64) -> i64 ! {panic} { a / b }
fn main() -> i64 ! {panic} { div(1, 0) }");
    assert_eq!(division.failed_text(), "a / b");
    let shift = run("fn shift(a: u8, b: u8) -> u8 ! {panic} { a << b }
fn main() -> i64 ! {panic} { Int.convert(shift(1, 8)) }");
    assert_eq!(shift.failed_text(), "a << b");
}

#[test]
fn a_panic_after_a_site_is_not_attributed_to_it() {
    let run = run("fn add(a: i64, b: i64) -> i64 ! {panic} { a + b }
fn main() -> i64 ! {alloc, panic} {
    let n = add(1, 2) - 4;
    let v: Vec<i64> = Vec.with_capacity(n);
    Vec.len(&v)
}");
    assert_eq!(run.record.outcome, Outcome::Unattributed);
    assert_eq!(run.record.sites[run.site("a + b")].hits, 1);
}

#[test]
fn an_unreached_site_keeps_its_initial_record() {
    let run = run("fn add(a: i64, b: i64) -> i64 ! {panic} { a + b }
fn main() -> i64 ! {panic} { if false { add(1, 2) } else { 0 } }");
    let site = run.record.sites[run.site("a + b")];
    assert_eq!((site.hits, site.margin), (0, i64::MAX));
}

#[test]
fn an_ordinary_build_writes_no_record() {
    let program = check(
        "fn add(a: i64, b: i64) -> i64 ! {panic} { a + b }
fn main() -> i64 ! {panic} { add(1, 2) }",
    )
    .unwrap();
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("plain");
    native::build(&program, &binary).unwrap();
    let out = scratch.path().join("record");
    let status = std::process::Command::new(&binary)
        .env(fuzz::OUT_VARIABLE, &out)
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(3));
    assert!(!out.exists());
}

#[test]
fn deferred_overflow_is_off_in_fuzz_builds() {
    // A counted reduction loop is deferred on LLVM and with
    // --deferred-overflow; a fuzz build still fails at the addition itself.
    let run = run("fn sum(v: &Vec<i64>) -> i64 ! {panic} {
    let mut total = 0;
    let mut i = 0;
    while i < v.len() { total = total + v[i]; i = i + 1; }
    total
}
fn main() -> i64 ! {alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(9223372036854775807);
    v = v.push(1);
    sum(&v)
}");
    assert_eq!(run.failed_text(), "total + v[i]");
}

#[test]
fn a_malformed_record_is_rejected() {
    assert_eq!(RunRecord::parse(b""), None);
    assert_eq!(RunRecord::parse(b"KUSHFUZ1"), None);
    let mut bytes = b"KUSHFUZ1".to_vec();
    bytes.extend(5i64.to_ne_bytes());
    bytes.extend(1i64.to_ne_bytes());
    bytes.extend([0; 16]);
    // Site 5 of 1.
    assert_eq!(RunRecord::parse(&bytes), None);
}
