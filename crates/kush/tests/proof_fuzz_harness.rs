//! PROOF-FUZZ step 3: harnesses. Every function that contains an obligation
//! site gets a generated harness in its own module; a synthetic root decodes
//! the harness's arguments from a tape on standard input. Preconditions are
//! guards, so an input they rule out never reaches the function. See
//! docs/proof-fuzz.md, section 2.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::executable::{Executable, check_program};
use kush::fuzz::harness::{self, Collection, Layout, Slot, Target};
use kush::fuzz::{self, Outcome, RunRecord};
use kush::native::{LinkSpec, Scratch};
use kush::program::{self, Memory, Program};
use std::io::Write;
use std::process::{Command, Stdio};

const LIB: &str = "module app.lib;

pub struct Pair { pub a: i64, pub b: i64 }

pub fn at(v: &Vec<i64>, i: i64) -> i64 ! {panic} { v[i] }
fn add8(a: u8, b: u8) -> u8 ! {panic} { a + b }
pub fn pick(v: &Vec<i64>, i: i64, erased ok: { 0 <= i && i < 4 }) -> i64 ! {panic} { v[i] }
pub fn refined(v: &mut Vec<u8> where len >= 8, i: i64) -> u8 ! {panic} { v[i] }
pub fn flag(b: Bool, x: i8) -> i8 ! {panic} { if b { x - 1 } else { x } }
pub fn first(s: &[i64], i: i64) -> i64 ! {panic} { s[i] }
pub fn bytes(b: &Bytes, i: i64) -> i64 ! {panic} { Bytes.len(b) * 0x10 + i * 3 }
pub fn sum(p: Pair) -> i64 ! {panic} { p.a + p.b }
pub struct Secret { n: i64 }
pub fn reveal(s: Secret) -> i64 ! {panic} { s.n + 1 }
pub fn twice<T>(x: i64, t: T) -> i64 ! {panic} { x + x }
pub fn calls(x: i64) -> i64 ! {panic} { add8(1, 2); x * 7 }
#[linear]
pub struct Token { pub n: i64 }
pub fn mint(x: i64) -> Token ! {panic} { Token { n: x + 1 } }
pub fn spend(t: Token) -> i64 ! {} { let Token { n } = t; n }
";

const MAIN: &str = "module app;
use app.lib;
fn main() -> i64 ! {alloc, panic} {
    let mut v: Vec<i64> = Vec.new();
    v = v.push(1);
    lib.at(&v, 0) + lib.sum(lib.Pair { a: 1, b: 2 }) + lib.twice(1, true) + lib.calls(1)
        + lib.spend(lib.mint(1))
}";

struct Fixture {
    modules: Memory,
    original: Program,
    targets: Vec<Target>,
    sources: harness::Sources,
    fuzz_program: Program,
    executable: Executable,
    binary: std::path::PathBuf,
    _scratch: Scratch,
}

fn fixture() -> Fixture {
    let modules = Memory(vec![("app.lib".into(), LIB.into())]);
    let original = program::load("main.kush", MAIN, &modules).unwrap_or_else(|(_, e)| panic!("{e:?}"));
    let checked = check_program(&original).unwrap();
    let mut targets = harness::plan(&original, &checked);
    let assembled = harness::assemble(&original, &mut targets, &modules).unwrap_or_else(|e| panic!("{e}"));
    let harness::Assembled {
        sources,
        program: fuzz_program,
        executable,
    } = assembled;
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("harnesses");
    fuzz::build(&executable, &binary, &LinkSpec::default()).unwrap();
    Fixture {
        modules,
        original,
        targets,
        sources,
        fuzz_program,
        executable,
        binary,
        _scratch: scratch,
    }
}

impl Fixture {
    fn target(&self, name: &str) -> (usize, &Target) {
        let index = self
            .targets
            .iter()
            .position(|t| t.name == name)
            .unwrap_or_else(|| panic!("no target {name}: {:?}", self.names()));
        (index, &self.targets[index])
    }
    fn names(&self) -> Vec<&str> {
        self.targets.iter().map(|t| t.name.as_str()).collect()
    }
    fn layout(&self, name: &str) -> &Layout {
        self.target(name).1.harness.as_ref().unwrap()
    }
    /// Run the harness of `name` on a tape, returning the record and the
    /// source text of the failing site, if any.
    fn run(&self, name: &str, tape: &[u8]) -> (RunRecord, Option<String>) {
        let (index, _) = self.target(name);
        let number = self.sources.harnesses.iter().position(|&i| i == index).unwrap();
        let out = self.binary.with_extension("record");
        let mut child = Command::new(&self.binary)
            .arg(number.to_string())
            .env(fuzz::OUT_VARIABLE, &out)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(tape).unwrap();
        child.wait().unwrap();
        let record = RunRecord::parse(&std::fs::read(&out).unwrap()).unwrap();
        let failed = match record.outcome {
            Outcome::Failed(site) => {
                let span = self.executable.obligation_sites()[site].span;
                let file = self.fuzz_program.sources.file(span).unwrap();
                Some(file.text[span.start - file.base..span.end - file.base].to_owned())
            }
            _ => None,
        };
        (record, failed)
    }
}

/// A tape for `layout` with these scalar values and collection contents.
fn tape(layout: &Layout, scalars: &[i64], collections: &[&[i64]]) -> Vec<u8> {
    let mut fixed = vec![0u8; layout.fixed];
    let mut rest = Vec::new();
    let (mut scalar, mut collection) = (0, 0);
    for slot in &layout.slots {
        match slot {
            Slot::Scalar { offset, scalar: kind, .. } => {
                let bytes = scalars[scalar].to_le_bytes();
                fixed[*offset..offset + kind.width()].copy_from_slice(&bytes[..kind.width()]);
                scalar += 1;
            }
            Slot::Collection {
                offset,
                collection: kind,
                minimum,
                ..
            } => {
                let items = collections[collection];
                let extra = (items.len() - minimum) as u16;
                fixed[*offset..offset + 2].copy_from_slice(&extra.to_le_bytes());
                let width = match kind {
                    Collection::Bytes => 1,
                    Collection::Vec(element) => element.width(),
                };
                for item in items {
                    rest.extend_from_slice(&item.to_le_bytes()[..width]);
                }
                collection += 1;
            }
        }
    }
    fixed.extend(rest);
    fixed
}

#[test]
fn targets_are_the_functions_with_unproved_checks() {
    let f = fixture();
    let names = f.names();
    for name in ["app.lib.at", "app.lib.add8", "app.lib.pick", "app.lib.refined", "app.lib.sum", "app.lib.calls"] {
        assert!(names.contains(&name), "{name} missing from {names:?}");
    }
    // `main` has overflow checks too, and is a target with no parameters.
    assert!(names.contains(&"app.main"), "{names:?}");
    // A record of public fields is built field by field; a type parameter
    // without a bound is fixed to i64.
    let sum = f.layout("app.lib.sum");
    assert_eq!(sum.slots.len(), 2);
    assert!(sum.generated_state);
    assert!(f.target("app.lib.twice").1.harness.is_ok());
    // Private fields and no function returning the record: no generator.
    let reveal = f.target("app.lib.reveal").1.harness.as_ref().unwrap_err();
    assert!(reveal.contains("private fields and no constructor"), "{reveal}");
    assert!(f.target("app.lib.calls").1.constants.contains(&7));
    // A result the harness cannot discard: its harness is left out, with
    // the checker's reason.
    let mint = f.target("app.lib.mint").1.harness.as_ref().unwrap_err();
    assert!(mint.starts_with("its harness does not check"), "{mint}");
    let _ = (&f.modules, &f.original);
}

#[test]
fn a_harness_reaches_and_breaks_its_check() {
    let f = fixture();
    let layout = f.layout("app.lib.at");
    let (record, failed) = f.run("app.lib.at", &tape(layout, &[2], &[&[5, 6, 7]]));
    assert_eq!(record.outcome, Outcome::Exited);
    let (_, failed_again) = f.run("app.lib.at", &tape(layout, &[3], &[&[5, 6, 7]]));
    assert_eq!(failed, None);
    assert_eq!(failed_again.as_deref(), Some("v[i]"));
}

#[test]
fn narrow_scalars_and_bools_decode() {
    let f = fixture();
    let (_, failed) = f.run("app.lib.add8", &tape(f.layout("app.lib.add8"), &[200, 55], &[]));
    assert_eq!(failed, None);
    let (_, failed) = f.run("app.lib.add8", &tape(f.layout("app.lib.add8"), &[200, 56], &[]));
    assert_eq!(failed.as_deref(), Some("a + b"));
    let flag = f.layout("app.lib.flag");
    assert_eq!(f.run("app.lib.flag", &tape(flag, &[1, -128], &[])).1.as_deref(), Some("x - 1"));
    assert_eq!(f.run("app.lib.flag", &tape(flag, &[0, -128], &[])).1, None);
}

#[test]
fn preconditions_guard_the_call() {
    let f = fixture();
    let layout = f.layout("app.lib.pick");
    // i = 9 is ruled out by the precondition: the call never happens.
    let (record, failed) = f.run("app.lib.pick", &tape(layout, &[9], &[&[1]]));
    assert_eq!((record.outcome, failed), (Outcome::Exited, None));
    // i = 2 satisfies it, but the vector is too short.
    assert_eq!(f.run("app.lib.pick", &tape(layout, &[2], &[&[1]])).1.as_deref(), Some("v[i]"));
}

#[test]
fn refined_lengths_slices_and_bytes_are_generated() {
    let f = fixture();
    let refined = f.layout("app.lib.refined");
    let Slot::Collection { minimum, .. } = &refined.slots[0] else {
        panic!("{refined:?}")
    };
    assert_eq!(*minimum, 8);
    let eight = [0i64; 8];
    assert_eq!(f.run("app.lib.refined", &tape(refined, &[7], &[&eight])).1, None);
    assert_eq!(
        f.run("app.lib.refined", &tape(refined, &[8], &[&eight])).1.as_deref(),
        Some("v[i]")
    );
    let first = f.layout("app.lib.first");
    assert_eq!(f.run("app.lib.first", &tape(first, &[1], &[&[4]])).1.as_deref(), Some("s[i]"));
    let bytes = f.layout("app.lib.bytes");
    assert_eq!(
        f.run("app.lib.bytes", &tape(bytes, &[i64::MAX / 3 + 1], &[&[1, 2]])).1.as_deref(),
        Some("i * 3")
    );
}

#[test]
fn a_short_tape_reads_as_zeros() {
    let f = fixture();
    // An empty tape: the vector is empty and i = 0.
    assert_eq!(f.run("app.lib.at", &[]).1.as_deref(), Some("v[i]"));
}

#[test]
fn integer_literals_parse() {
    use kush::fuzz::harness::integer_literal;
    assert_eq!(integer_literal("0x1F"), Some(31));
    assert_eq!(integer_literal("1_000"), Some(1000));
    assert_eq!(integer_literal("-0b101"), Some(-5));
    assert_eq!(integer_literal("x"), None);
}
