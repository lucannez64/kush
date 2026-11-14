//! PROOF-FUZZ generators for records, enums and generic functions
//! (PF-RECORDS). A record of public fields is built field by field (its
//! length-refined fields long enough), one with private fields by a
//! constructor of its module, an enum from a tag byte and its payload, and a
//! generic function at a type implementing its bound. Findings through a
//! generated record are local; functions with I/O get no harness. See
//! docs/proof-fuzz.md, section 2.4.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]
use kush::fuzz::engine::{Options, Session, State};
use kush::native::{LinkSpec, Scratch};
use kush::program::{self, Memory};

const SHAPES: &str = "module app.shapes;

pub const SIDE: i64 = 4;

pub enum Mode { Off, On, Scaled(u8) }

/// Open data: any field values make a grid.
pub struct Grid { pub cells: Vec<u8> where len >= SIDE * SIDE, pub mode: Mode, pub scale: i64 }

/// Encapsulated: only `new` makes one.
pub struct Counter { count: i64, limit: i64 }

pub fn new() -> Counter ! {} { Counter { count: 1, limit: 10 } }

pub fn tick(c: &mut Counter, by: i64) -> i64 ! {panic} {
    c.count = c.count + by;
    c.count
}

pub trait Measure {
    fn size(self: &Self) -> i64 ! {panic};
}

impl Measure for Grid {
    pub fn size(self: &Self) -> i64 ! {panic} { self.scale }
}
";

const LIB: &str = "module app.lib;

use app.shapes.Grid;
use app.shapes.Mode;
use app.shapes.Measure;

// `cells` has at least 16 elements, so index 15 is proved; `scale` is not
// bounded, so the sum is attacked.
pub fn corner(g: &Grid) -> i64 ! {panic} {
    let c: i64 = Int.convert(g.cells[15]);
    g.scale + c + 1
}

pub fn factor(m: Mode) -> i64 ! {panic} {
    match m {
        Mode.Off => 0,
        Mode.On => 1,
        Mode.Scaled(k) => { let s: i64 = Int.convert(k); 100 / (s - 7) },
    }
}

pub fn twice<T: Measure>(t: &T) -> i64 ! {panic} { t.size() * 2 }

pub fn say(x: i64) -> i64 ! {io, panic} { x + 1 }
";

// A generic function has checks only where it is instantiated: `main`
// calls `twice` once.
const MAIN: &str = "module app;
use app.lib;
use app.shapes;
fn main() -> i64 ! {alloc, panic} {
    let mut cells: Vec<u8> = Vec.new();
    let mut i = 0;
    while i < 16 { cells = cells.push(0); i = i + 1; }
    let g = shapes.Grid { cells: cells, mode: shapes.Mode.Off, scale: 1 };
    lib.twice(&g)
}";

fn session(scratch: &Scratch) -> Session {
    let modules = Memory(vec![
        ("app.lib".into(), LIB.into()),
        ("app.shapes".into(), SHAPES.into()),
    ]);
    let original =
        program::load("main.kush", MAIN, &modules).unwrap_or_else(|(_, e)| panic!("{e:?}"));
    let mut session = Session::new(
        &original,
        &modules,
        &LinkSpec::default(),
        &scratch.path().join("fuzz"),
        None,
        Vec::new(),
    )
    .unwrap_or_else(|e| panic!("{e}"));
    session.fuzz(&Options {
        runs: 400,
        ..Options::default()
    });
    session
}

fn report_of(session: &Session, function: &str) -> Vec<(State, String)> {
    session
        .reports
        .iter()
        .filter(|r| r.function == function)
        .map(|r| {
            let inputs = r.finding.as_ref().map_or(String::new(), |f| {
                f.inputs
                    .iter()
                    .map(|(n, v)| format!("{n} = {v}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            });
            (r.state(&session.targets), inputs)
        })
        .collect()
}

#[test]
fn records_enums_and_generics_are_generated() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let session = session(&scratch);
    let render = session.render(&Options::default());
    // A record of public fields from another module: its refined field is
    // long enough (the index is proved and the session runs), and the
    // product of an unbounded field is found.
    let corner = report_of(&session, "app.lib.corner");
    assert!(
        corner.iter().any(|(state, inputs)| *state == State::Found
            && inputs.contains("g.scale = ")
            && inputs.contains("g.mode = ")),
        "{corner:?}\n{render}"
    );
    // A finding through a generated record is local.
    let finding = session
        .reports
        .iter()
        .find(|r| r.function == "app.lib.corner" && r.finding.is_some())
        .and_then(|r| r.finding.as_ref())
        .unwrap();
    assert!(!finding.public);
    assert!(finding.reproduction.is_none());
    // An enum: its tag is shown with the variant; a finding reached with
    // only an enum stays a bug of the public function.
    let factor = session
        .reports
        .iter()
        .find(|r| r.function == "app.lib.factor" && r.finding.is_some())
        .and_then(|r| r.finding.as_ref())
        .unwrap_or_else(|| panic!("{render}"));
    let inputs: Vec<String> = factor.inputs.iter().map(|(n, v)| format!("{n} = {v}")).collect();
    // The tag picks a variant modulo their number.
    assert!(inputs[0].starts_with("m = ") && inputs[0].ends_with(" (Mode.Scaled)"), "{render}");
    assert_eq!(inputs[1], "m.Scaled.0 = 7", "{render}");
    assert!(factor.public);
    // A record with private fields comes from its constructor.
    let tick = report_of(&session, "app.shapes.tick");
    assert!(tick.iter().any(|(state, _)| *state == State::Found), "{tick:?}");
    // A generic function at the type implementing its bound.
    let twice = report_of(&session, "app.lib.twice");
    assert!(twice.iter().any(|(state, _)| *state == State::Found), "{twice:?}\n{render}");
}

#[test]
fn functions_with_io_get_no_harness() {
    let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
    let session = session(&scratch);
    let say = report_of(&session, "app.lib.say");
    assert!(say.iter().all(|(state, _)| *state == State::NoGenerator), "{say:?}");
    let list = session.render_list(&Options::default());
    assert!(
        list.contains("app.lib.say  (no generator: performs I/O (attack it through a #[fuzz] entry))"),
        "{list}"
    );
}
