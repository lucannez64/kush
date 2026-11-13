//! PROOF-FUZZ harnesses: for each function that contains an obligation
//! site, a generated `pub fn __kush_fuzz_N(..)` appended to the function's own
//! module (so private functions are reachable) that guards the function's
//! preconditions and calls it, plus one synthetic root module whose `main`
//! decodes the arguments of harness `argv[1]` from standard input (the tape)
//! and calls it. See docs/proof-fuzz.md, section 2.
//!
//! The tape layout is fixed per harness: every scalar has its own bytes at a
//! fixed offset (little-endian), every collection a two-byte length there;
//! the collections' elements follow, in parameter order. Bytes past the end
//! of the tape read as zero, so every byte string is a valid input.
use crate::ast::{self, ItemKind, TypeKind};
use crate::executable::Executable;
use crate::program::{ModuleSource, Program};
use crate::Span;
use std::collections::BTreeMap;

/// Longest generated collection beyond its required minimum length.
pub const MAX_EXTRA_LENGTH: usize = 64;
/// Longest input of a `#[fuzz]` entry.
pub const ENTRY_LENGTH: usize = 4096;

/// A scalar the tape can encode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scalar {
    /// An integer type by name (`i64`, `u8`, ...), its width in bytes and
    /// signedness.
    Int {
        name: &'static str,
        bytes: usize,
        signed: bool,
    },
    Bool,
}

impl Scalar {
    fn from_name(name: &str) -> Option<Self> {
        let (name, bytes, signed) = match name {
            "i8" => ("i8", 1, true),
            "i16" => ("i16", 2, true),
            "i32" => ("i32", 4, true),
            "i64" => ("i64", 8, true),
            "u8" => ("u8", 1, false),
            "u16" => ("u16", 2, false),
            "u32" => ("u32", 4, false),
            "u64" => ("u64", 8, false),
            "Bool" => return Some(Self::Bool),
            _ => return None,
        };
        Some(Self::Int {
            name,
            bytes,
            signed,
        })
    }
    /// Bytes this scalar takes on the tape.
    pub fn width(self) -> usize {
        match self {
            Self::Int { bytes, .. } => bytes,
            Self::Bool => 1,
        }
    }
    fn type_name(self) -> &'static str {
        match self {
            Self::Int { name, .. } => name,
            Self::Bool => "Bool",
        }
    }
    /// Kush expression decoding this scalar at tape offset `at`.
    fn decode(self, at: &str) -> String {
        match self {
            Self::Int { name: "i64", .. } => format!("__fz_word(&tape, {at}, 8)"),
            Self::Int { bytes, .. } => format!("Int.truncate(__fz_word(&tape, {at}, {bytes}))"),
            Self::Bool => format!("__fz_word(&tape, {at}, 1) % 2 == 1"),
        }
    }
}

/// A collection the tape can encode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Collection {
    Bytes,
    Vec(Scalar),
}

/// How a harness passes a generated value to the target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Passing {
    Value,
    Shared,
    Exclusive,
    /// `&[T]` from a generated `Vec<T>`.
    Slice,
}

/// One runtime parameter's place on the tape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Slot {
    Scalar {
        name: String,
        offset: usize,
        scalar: Scalar,
        passing: Passing,
    },
    /// The length is `minimum + (u16 at offset) % (maximum + 1)`.
    Collection {
        name: String,
        offset: usize,
        collection: Collection,
        minimum: usize,
        /// Most elements beyond `minimum`: [`MAX_EXTRA_LENGTH`] for a
        /// function's argument, [`ENTRY_LENGTH`] for a `#[fuzz]` entry's input.
        maximum: usize,
        passing: Passing,
    },
}

/// The tape layout of one harness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Layout {
    pub slots: Vec<Slot>,
    /// Bytes of the fixed part; collection elements follow it.
    pub fixed: usize,
}

impl Layout {
    /// The longest tape this layout reads; bytes beyond it are ignored.
    pub fn max_tape(&self) -> usize {
        self.fixed
            + self
                .slots
                .iter()
                .map(|slot| match slot {
                    Slot::Collection {
                        collection,
                        minimum,
                        maximum,
                        ..
                    } => {
                        let width = match collection {
                            Collection::Bytes => 1,
                            Collection::Vec(element) => element.width(),
                        };
                        (minimum + maximum) * width
                    }
                    Slot::Scalar { .. } => 0,
                })
                .sum::<usize>()
    }
}

/// A function that contains obligation sites.
#[derive(Debug, Clone)]
pub struct Target {
    /// `module.function`.
    pub name: String,
    pub module: Vec<String>,
    /// The function item's span in the program it was planned from.
    pub span: Span,
    /// The tape layout, or why the function cannot be called directly.
    pub harness: Result<Layout, String>,
    /// Integer constants in the function body, for the mutation dictionary.
    pub constants: Vec<i128>,
    /// The function's own name, whether it is `pub`, and whether this unit
    /// is the program's entry file.
    pub function: String,
    pub public: bool,
    pub entry: bool,
    /// Every parameter's name and whether it is erased, in order.
    pub parameters: Vec<(String, bool)>,
    /// The proposition of each erased parameter, in order, without braces.
    pub preconditions: Vec<String>,
    /// A `#[fuzz]` entry of the test target rather than a function.
    pub fuzz_entry: bool,
    /// The file the function is in and its byte range there.
    pub file: String,
    pub range: (usize, usize),
    /// The declared effect row's text, as in `io, alloc, panic`.
    pub effects: String,
}

/// Every top-level function of `program` containing at least one obligation
/// site of `executable`, in source order.
pub fn plan(program: &Program, executable: &Executable) -> Vec<Target> {
    let sites = executable.obligation_sites();
    let mut targets = Vec::new();
    for (unit_index, unit) in program.units.iter().enumerate() {
        let module = unit_module(program, unit);
        // The standard library is not the program under attack, and its
        // modules cannot take generated harnesses.
        if module.first().is_some_and(|first| first == "std") {
            continue;
        }
        for item in &program.module.items[unit.items.clone()] {
            let ItemKind::Function(function) = &item.item.kind else {
                continue;
            };
            if function.body.is_none()
                || !sites
                    .iter()
                    .any(|site| item.item.span.start <= site.span.start && site.span.end <= item.item.span.end)
            {
                continue;
            }
            let text = program
                .sources
                .file(item.item.span)
                .map(|file| (file.text.as_str(), file.base))
                .unwrap_or(("", 0));
            let mut constants = Vec::new();
            if let Some(body) = &function.body {
                collect_constants_block(body, &mut constants);
            }
            constants.sort_unstable();
            constants.dedup();
            targets.push(Target {
                name: qualified(&module, &function.name),
                module: module.clone(),
                span: item.item.span,
                harness: layout(function, text),
                constants,
                function: function.name.clone(),
                public: item.public,
                entry: unit_index == 0,
                parameters: function
                    .parameters
                    .iter()
                    .map(|p| (p.name.clone(), p.erased))
                    .collect(),
                preconditions: function
                    .parameters
                    .iter()
                    .filter(|p| p.erased)
                    .map(|p| {
                        let text = slice(text, p.ty.span).trim();
                        text.strip_prefix('{')
                            .and_then(|t| t.strip_suffix('}'))
                            .unwrap_or(text)
                            .to_owned()
                    })
                    .collect(),
                fuzz_entry: false,
                file: program
                    .sources
                    .file(item.item.span)
                    .map_or_else(String::new, |file| file.name.clone()),
                range: (item.item.span.start - text.1, item.item.span.end - text.1),
                effects: function
                    .effects
                    .iter()
                    .map(|effect| slice(text, effect.span).trim().to_owned())
                    .collect::<Vec<_>>()
                    .join(", "),
            });
        }
    }
    targets
}

fn qualified(module: &[String], name: &str) -> String {
    if module.is_empty() {
        name.to_owned()
    } else {
        format!("{}.{name}", module.join("."))
    }
}

/// The declared module path of a unit (`module a.b;`), else its load path.
pub(super) fn unit_module(program: &Program, unit: &crate::program::Unit) -> Vec<String> {
    program.module.items[unit.items.clone()]
        .iter()
        .find_map(|item| match &item.item.kind {
            ItemKind::Module(path) => Some(path.clone()),
            _ => None,
        })
        .unwrap_or_else(|| unit.path.clone())
}

fn slice(text: (&str, usize), span: Span) -> &str {
    let (text, base) = text;
    text.get(span.start - base..span.end - base).unwrap_or("")
}

const ALLOWED_EFFECTS: [&str; 3] = ["io", "alloc", "panic"];

fn layout(function: &ast::Function, text: (&str, usize)) -> Result<Layout, String> {
    if !function.generics.is_empty() {
        return Err("generic function".into());
    }
    for effect in &function.effects {
        let name = match &effect.kind {
            TypeKind::Named { path, arguments } if arguments.is_empty() && path.len() == 1 => {
                path[0].as_str()
            }
            _ => return Err(format!("effect `{}`", slice(text, effect.span))),
        };
        if !ALLOWED_EFFECTS.contains(&name) {
            return Err(format!("effect `{name}`"));
        }
    }
    let mut slots = Vec::new();
    let mut offset = 0;
    for parameter in &function.parameters {
        if parameter.erased {
            let ty = slice(text, parameter.ty.span).trim();
            if !(ty.starts_with('{') && ty.ends_with('}')) {
                return Err(format!(
                    "erased parameter `{}` is not a proposition",
                    parameter.name
                ));
            }
            continue;
        }
        let (inner, passing) = match &parameter.ty.kind {
            TypeKind::Borrow { mutable, inner, .. } => (
                inner.as_ref(),
                if *mutable {
                    Passing::Exclusive
                } else {
                    Passing::Shared
                },
            ),
            _ => (&parameter.ty, Passing::Value),
        };
        let unsupported = || {
            format!(
                "no generator for `{}: {}`",
                parameter.name,
                slice(text, parameter.ty.span)
            )
        };
        let minimum = match &parameter.min_length {
            None => 0,
            Some(length) => match &length.kind {
                ast::ExprKind::Integer(n) => integer_literal(n)
                    .and_then(|n| usize::try_from(n).ok())
                    .ok_or_else(unsupported)?,
                _ => return Err(unsupported()),
            },
        };
        match &inner.kind {
            TypeKind::Named { path, arguments } if path.len() == 1 => {
                let name = path[0].as_str();
                if let (Some(scalar), true) = (Scalar::from_name(name), arguments.is_empty()) {
                    if passing != Passing::Value {
                        return Err(unsupported());
                    }
                    slots.push(Slot::Scalar {
                        name: parameter.name.clone(),
                        offset,
                        scalar,
                        passing,
                    });
                    offset += scalar.width();
                    continue;
                }
                let collection = match (name, arguments.as_slice()) {
                    ("Bytes", []) => Collection::Bytes,
                    ("Vec", [element]) => match &element.kind {
                        TypeKind::Named { path, arguments }
                            if path.len() == 1 && arguments.is_empty() =>
                        {
                            Collection::Vec(Scalar::from_name(&path[0]).ok_or_else(unsupported)?)
                        }
                        _ => return Err(unsupported()),
                    },
                    _ => return Err(unsupported()),
                };
                slots.push(Slot::Collection {
                    name: parameter.name.clone(),
                    offset,
                    collection,
                    minimum,
                    maximum: MAX_EXTRA_LENGTH,
                    passing,
                });
                offset += 2;
            }
            TypeKind::Slice(element) if passing == Passing::Shared => {
                let TypeKind::Named { path, arguments } = &element.kind else {
                    return Err(unsupported());
                };
                let scalar = (path.len() == 1 && arguments.is_empty())
                    .then(|| Scalar::from_name(&path[0]))
                    .flatten()
                    .ok_or_else(unsupported)?;
                slots.push(Slot::Collection {
                    name: parameter.name.clone(),
                    offset,
                    collection: Collection::Vec(scalar),
                    minimum,
                    maximum: MAX_EXTRA_LENGTH,
                    passing: Passing::Slice,
                });
                offset += 2;
            }
            _ => return Err(unsupported()),
        }
    }
    Ok(Layout {
        slots,
        fixed: offset,
    })
}

/// Integer literals of a body, for the mutation dictionary. A structural
/// walk would repeat the whole expression tree; the debug form names every
/// literal as `Integer(n)`, and a stray match only adds a dictionary value.
fn collect_constants_block(block: &ast::Block, out: &mut Vec<i128>) {
    let text = format!("{block:?}");
    let mut rest = text.as_str();
    while let Some(at) = rest.find("Integer(") {
        rest = &rest[at + "Integer(".len()..];
        let end = rest.find(')').unwrap_or(rest.len());
        if let Some(value) = integer_literal(rest[..end].trim().trim_matches('"')) {
            out.push(value);
        }
    }
}

/// The value of a Kush integer literal (`42`, `0x1F`, `0b101`, `1_000`,
/// with an optional `-`).
pub fn integer_literal(text: &str) -> Option<i128> {
    let (negative, text) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let digits: String = text.chars().filter(|c| *c != '_').collect();
    let value = if let Some(hex) = digits.strip_prefix("0x") {
        i128::from_str_radix(hex, 16).ok()?
    } else if let Some(binary) = digits.strip_prefix("0b") {
        i128::from_str_radix(binary, 2).ok()?
    } else {
        digits.parse().ok()?
    };
    Some(if negative { -value } else { value })
}

/// Generated sources for a set of targets.
pub struct Sources {
    /// The synthetic root module.
    pub root_name: String,
    pub root: String,
    /// Harness text appended to each target module, by dotted module path.
    pub appended: BTreeMap<String, String>,
    /// For each harness number, the index of its target.
    pub harnesses: Vec<usize>,
    /// The original root file as an ordinary module (dotted path, file name,
    /// text): the synthetic root replaces it, and may import it.
    pub entry: Option<(String, String, String)>,
    /// Generated relay modules by dotted path (file name, text). Kush has no
    /// import aliases, so the root reaches each target module through a
    /// relay with a unique name: two target modules may share their last
    /// name, and a module called `main` would clash with the root's `main`.
    pub relays: BTreeMap<String, (String, String)>,
}

/// The module path of the synthetic root.
pub const ROOT_MODULE: &str = "kush_fuzz_entry";

/// Harness sources for every target with a layout. `original` is the program
/// the targets were planned from (for the source text of propositions).
pub fn sources(program: &Program, targets: &[Target]) -> Sources {
    let mut appended: BTreeMap<String, String> = BTreeMap::new();
    let mut relays: BTreeMap<String, (String, String)> = BTreeMap::new();
    let mut relay_of: BTreeMap<String, String> = BTreeMap::new();
    let mut harnesses = Vec::new();
    let mut dispatch = String::new();
    let root_module = targets
        .first()
        .and_then(|t| t.module.first().cloned())
        .map_or_else(|| ROOT_MODULE.to_owned(), |package| format!("{package}.{ROOT_MODULE}"));
    let package_prefix = root_module
        .strip_suffix(ROOT_MODULE)
        .unwrap_or("")
        .to_owned();
    for (index, target) in targets.iter().enumerate() {
        let Ok(layout) = &target.harness else {
            continue;
        };
        let number = harnesses.len();
        harnesses.push(index);
        let module = target.module.join(".");
        let short = target.module.last().cloned().unwrap_or_default();
        let next_relay = relay_of.len();
        let relay = relay_of
            .entry(module.clone())
            .or_insert_with(|| format!("{package_prefix}kush_fuzz_relay_{next_relay}"))
            .clone();
        let relay_short = relay.rsplit('.').next().unwrap_or(&relay).to_owned();
        // The harness in the target's module.
        let mut parameters = Vec::new();
        let mut body = String::new();
        let mut arguments = Vec::new();
        let mut slots = layout.slots.iter();
        let mut preconditions = target.preconditions.iter();
        for (_, erased) in &target.parameters {
            if *erased {
                let inner = preconditions.next().map_or("true", String::as_str);
                body.push_str(&format!("    if !({inner}) {{ return; }}\n"));
                arguments.push("_".to_owned());
                continue;
            }
            let slot = slots.next().expect("one slot per runtime parameter");
            let (name, ty, passing) = match slot {
                Slot::Scalar {
                    name,
                    scalar,
                    passing,
                    ..
                } => (name, scalar.type_name().to_owned(), *passing),
                Slot::Collection {
                    name,
                    collection,
                    passing,
                    minimum,
                    ..
                } => {
                    let ty = match collection {
                        Collection::Bytes => "Bytes".to_owned(),
                        Collection::Vec(element) => format!("Vec<{}>", element.type_name()),
                    };
                    if *minimum > 0 {
                        let length = match collection {
                            Collection::Bytes => format!("Bytes.len(&{name})"),
                            Collection::Vec(_) => format!("{name}.len()"),
                        };
                        body.push_str(&format!("    if {length} < {minimum} {{ return; }}\n"));
                    }
                    (name, ty, *passing)
                }
            };
            parameters.push(format!("{name}: {ty}"));
            arguments.push(match passing {
                Passing::Value => name.clone(),
                Passing::Shared => format!("&{name}"),
                Passing::Exclusive => {
                    body.push_str(&format!("    let mut {name} = {name};\n"));
                    format!("&mut {name}")
                }
                Passing::Slice => format!("&{name}[..]"),
            });
        }
        let effects = harness_effects(&target.effects);
        let harness = format!(
            "\npub fn __kush_fuzz_{number}({}) -> Unit ! {{{effects}}} {{\n{body}    let _ = {}({});\n}}\n",
            parameters.join(", "),
            target.function,
            arguments.join(", "),
        );
        appended.entry(module.clone()).or_default().push_str(&harness);
        let names: Vec<&str> = layout
            .slots
            .iter()
            .map(|slot| match slot {
                Slot::Scalar { name, .. } | Slot::Collection { name, .. } => name.as_str(),
            })
            .collect();
        relays
            .entry(relay.clone())
            .or_insert_with(|| (format!("<{relay}>"), format!("module {relay};\n\nuse {module};\n")))
            .1
            .push_str(&format!(
                "\npub fn call_{number}({}) -> Unit ! {{{effects}}} {{\n    {short}.__kush_fuzz_{number}({});\n}}\n",
                parameters.join(", "),
                names.join(", "),
            ));
        // Its branch of the root's dispatch.
        dispatch.push_str(&format!("    if which == {number} {{\n"));
        let mut call = Vec::new();
        for (position, slot) in layout.slots.iter().enumerate() {
            let name = &format!("fz_p{position}");
            match slot {
                Slot::Scalar {
                    offset,
                    scalar,
                    ..
                } => {
                    dispatch.push_str(&format!(
                        "        let {name}: {} = {};\n",
                        scalar.type_name(),
                        scalar.decode(&offset.to_string())
                    ));
                    call.push(name.clone());
                }
                Slot::Collection {
                    offset,
                    collection,
                    minimum,
                    maximum,
                    ..
                } => {
                    let extra = maximum + 1;
                    dispatch.push_str(&format!(
                        "        let {name}_n = {minimum} + __fz_word(&tape, {offset}, 2) % {extra};\n"
                    ));
                    match collection {
                        Collection::Bytes => dispatch.push_str(&format!(
                            "        let mut {name}: Bytes = Bytes.with_capacity({name}_n);\n        let mut fz_k = 0;\n        while fz_k < {name}_n {{ {name} = Bytes.push({name}, __fz_word(&tape, at, 1)); at = at + 1; fz_k = fz_k + 1; }}\n"
                        )),
                        Collection::Vec(element) => dispatch.push_str(&format!(
                            "        let mut {name}: Vec<{ty}> = Vec.with_capacity({name}_n);\n        let mut fz_k = 0;\n        while fz_k < {name}_n {{ let fz_e: {ty} = {decode}; {name} = {name}.push(fz_e); at = at + {width}; fz_k = fz_k + 1; }}\n",
                            ty = element.type_name(),
                            decode = element.decode("at"),
                            width = element.width(),
                        )),
                    }
                    call.push(name.clone());
                }
            }
        }
        dispatch.push_str(&format!(
            "        {relay_short}.call_{number}({});\n        return 0;\n    }}\n",
            call.join(", ")
        ));
    }
    let mut root = format!("module {root_module};\n\nuse std.env;\nuse std.io;\nuse std.result.Result;\n");
    for relay in relays.keys() {
        root.push_str(&format!("use {relay};\n"));
    }
    root.push_str(ROOT_HELPERS);
    // `read_all` fails on input longer than its buffer: size it for the
    // longest tape of any harness (the driver never sends more).
    let capacity = harnesses
        .iter()
        .filter_map(|&index| targets[index].harness.as_ref().ok())
        .map(Layout::max_tape)
        .max()
        .unwrap_or(0)
        + 1;
    root.push_str(&format!("\nfn main() -> i64 ! {{io, alloc, panic}} {{\n    let which = __fz_which();\n    let tape = match io.read_all(io.stdin(), Bytes.with_capacity({capacity})) {{\n        Result.Ok(bytes) => bytes,\n        Result.Err(_) => return 2,\n    }};\n"));
    // `at` walks the collection elements after the fixed part; each branch
    // starts it at its own layout's end.
    let mut branches = String::new();
    for (number, &index) in harnesses.iter().enumerate() {
        let fixed = targets[index].harness.as_ref().map_or(0, |l| l.fixed);
        branches.push_str(&format!("    if which == {number} {{ at = {fixed}; }}\n"));
    }
    root.push_str("    let mut at = 0;\n");
    root.push_str(&branches);
    root.push_str(&dispatch);
    root.push_str("    1\n}\n");
    // `#[stack_size(N)]` belongs to the program's `main`: it moves from the
    // entry's `main` (blanked to spaces, so offsets stay put) to the root's.
    let mut stack_size = String::new();
    let entry = program.units.first().and_then(|unit| {
        let path = unit_module(program, unit).join(".");
        let file = program.sources.files.get(unit.file)?;
        let mut text = file.text.clone();
        for item in &program.module.items[unit.items.clone()] {
            for attribute in item.attributes.iter().filter(|a| a.kind == "stack_size") {
                let (start, end) = (attribute.span.start - file.base, attribute.span.end - file.base);
                if let Some(original) = file.text.get(start..end) {
                    stack_size = format!("{original}\n");
                    text.replace_range(start..end, &" ".repeat(end - start));
                }
            }
        }
        (!path.is_empty()).then(|| (path, file.name.clone(), text))
    });
    let root = root.replace("\nfn main() -> i64", &format!("\n{stack_size}fn main() -> i64"));
    Sources {
        root_name: format!("<{root_module}>"),
        root,
        appended,
        harnesses,
        entry,
        relays,
    }
}

const ROOT_HELPERS: &str = "
/// Generated by `kush fuzz`: little-endian `width` bytes of the tape at
/// `at`; bytes past its end read as zero.
fn __fz_word(tape: &Bytes, at: i64, width: i64) -> i64 ! {panic} {
    let mut value = 0;
    let mut k = width - 1;
    while k >= 0 {
        let index = at + k;
        let byte = if index >= 0 && index < Bytes.len(tape) { Bytes.get(tape, index) } else { 0 };
        value = (value << 8) | byte;
        k = k - 1;
    }
    value
}
/// The harness number in the first program argument.
fn __fz_which() -> i64 ! {io, alloc, panic} {
    let digits = match env.arg(1, Bytes.with_capacity(16)) {
        Result.Ok(bytes) => bytes,
        Result.Err(_) => return 0 - 1,
    };
    let mut value = 0;
    let mut k = 0;
    while k < Bytes.len(&digits) {
        value = value * 10 + Bytes.get(&digits, k) - 48;
        k = k + 1;
    }
    value
}
";

/// The harness's effect row: the target's effects plus `panic` (the guards).
fn harness_effects(row: &str) -> String {
    let mut effects: Vec<String> = row
        .split(',')
        .map(|effect| effect.trim().to_owned())
        .filter(|effect| !effect.is_empty())
        .collect();
    if !effects.iter().any(|e| e == "panic") {
        effects.push("panic".into());
    }
    effects.join(", ")
}


/// A module source that appends generated harness text to some modules.
pub struct Overlay<'a> {
    pub base: &'a dyn ModuleSource,
    pub sources: &'a Sources,
}

impl ModuleSource for Overlay<'_> {
    fn find(&self, path: &[String]) -> Option<(String, String)> {
        let dotted = path.join(".");
        if let Some((name, text)) = self.sources.relays.get(&dotted) {
            return Some((name.clone(), text.clone()));
        }
        let (name, mut text) = match &self.sources.entry {
            Some((entry, name, text)) if *entry == dotted => (name.clone(), text.clone()),
            _ => self.base.find(path)?,
        };
        if let Some(extra) = self.sources.appended.get(&dotted) {
            if !text.ends_with('\n') {
                text.push('\n');
            }
            text.push_str(extra);
        }
        Some((name, text))
    }
}

/// A checked harness program.
pub struct Assembled {
    pub sources: Sources,
    pub program: Program,
    pub executable: Executable,
}

/// Generate, load and check the harness program for `targets`. A harness
/// that does not check (a result it cannot discard, a precondition that is
/// not an executable expression, ...) has its target marked with the reason
/// and is left out; any other error is returned rendered.
pub fn assemble(
    original: &Program,
    targets: &mut [Target],
    base: &dyn ModuleSource,
) -> Result<Assembled, String> {
    loop {
        let sources = sources(original, targets);
        let overlay = Overlay {
            base,
            sources: &sources,
        };
        let loaded = crate::program::load(&sources.root_name, &sources.root, &overlay)
            .and_then(|program| match crate::executable::check_program(&program) {
                Ok(executable) => Ok((program, executable)),
                Err(error) => Err((Some(program.sources.clone()), error)),
            });
        let (map, error) = match loaded {
            Ok((program, executable)) => {
                return Ok(Assembled {
                    sources,
                    program,
                    executable,
                });
            }
            Err(failure) => failure,
        };
        let rendered = map
            .as_ref()
            .map_or_else(|| error.message.clone(), |map| map.render(&error));
        let Some(number) = map
            .as_ref()
            .and_then(|map| harness_of(map, &sources, error.span))
        else {
            return Err(rendered);
        };
        targets[sources.harnesses[number]].harness =
            Err(format!("its harness does not check: {}", error.message));
    }
}

/// The harness whose generated text contains `span`, if any.
fn harness_of(map: &crate::program::SourceMap, sources: &Sources, span: Span) -> Option<usize> {
    let file = map.file(span)?;
    let offset = span.start - file.base;
    let before = &file.text[..offset.min(file.text.len())];
    let marker = if file.name == sources.root_name {
        // A dispatch branch of the root (the helpers above them are fixed).
        "if which == "
    } else if sources.relays.values().any(|(name, _)| *name == file.name) {
        "pub fn call_"
    } else {
        let generated = sources.appended.values().any(|extra| {
            file.text.ends_with(extra.as_str()) && offset >= file.text.len() - extra.len()
        });
        if !generated {
            return None;
        }
        "pub fn __kush_fuzz_"
    };
    let at = before.rfind(marker)? + marker.len();
    let digits: String = file.text[at..].chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// The `#[fuzz]` entries of a test target: `fn name(input: &Bytes) -> Unit`
/// functions the driver calls with arbitrary bytes. `module` is the test
/// target's module path and `file` the name it is loaded under.
pub fn plan_entries(text: &str, file: &str) -> Result<Vec<Target>, String> {
    let module = crate::parser::parse(text).map_err(|diagnostic| diagnostic.render(file, text))?;
    let path = module
        .items
        .iter()
        .find_map(|item| match &item.item.kind {
            ItemKind::Module(path) => Some(path.clone()),
            _ => None,
        })
        .unwrap_or_default();
    let mut targets = Vec::new();
    for item in &module.items {
        let ItemKind::Function(function) = &item.item.kind else {
            continue;
        };
        if !item.attributes.iter().any(|a| a.kind == "fuzz") {
            continue;
        }
        let span = item.item.span;
        let source = (text, 0);
        let shape = match function.parameters.as_slice() {
            [parameter]
                if !parameter.erased
                    && function.generics.is_empty()
                    && slice(source, parameter.ty.span).replace(' ', "") == "&Bytes"
                    && slice(source, function.result.span).trim() == "Unit" =>
            {
                Ok(Layout {
                    slots: vec![Slot::Collection {
                        name: parameter.name.clone(),
                        offset: 0,
                        collection: Collection::Bytes,
                        minimum: 0,
                        maximum: ENTRY_LENGTH,
                        passing: Passing::Shared,
                    }],
                    fixed: 2,
                })
            }
            _ => Err("a #[fuzz] entry takes one `&Bytes` and returns Unit".to_owned()),
        };
        let effects: Vec<String> = function
            .effects
            .iter()
            .map(|effect| slice(source, effect.span).trim().to_owned())
            .collect();
        let shape = match effects.iter().find(|e| !ALLOWED_EFFECTS.contains(&e.as_str())) {
            Some(effect) => Err(format!("effect `{effect}`")),
            None => shape,
        };
        let mut constants = Vec::new();
        if let Some(body) = &function.body {
            collect_constants_block(body, &mut constants);
        }
        constants.sort_unstable();
        constants.dedup();
        targets.push(Target {
            name: qualified(&path, &function.name),
            module: path.clone(),
            span,
            harness: shape,
            constants,
            function: function.name.clone(),
            public: true,
            entry: false,
            parameters: function
                .parameters
                .iter()
                .map(|p| (p.name.clone(), p.erased))
                .collect(),
            preconditions: Vec::new(),
            fuzz_entry: true,
            file: file.to_owned(),
            range: (span.start, span.end),
            effects: effects.join(", "),
        });
    }
    Ok(targets)
}
