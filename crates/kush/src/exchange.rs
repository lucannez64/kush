//! The kernel exchange format: a small canonical S-expression syntax for core
//! terms, declarations and queries, shared by the Rust kernel and the kernel
//! written in Kush (`examples/kernel`). See `docs/kernel-exchange.md`.
//!
//! `dump` prints a checked module's admitted environment followed by queries;
//! `answer` replays a file with the Rust kernel and prints one result line per
//! item, in the format the Kush kernel prints too, so the two can be diffed.
//! This module only reads and prints; admission still goes through the
//! checking `Kernel` API.
use crate::{
    check::CheckedModule,
    kernel::{IndexedConstructorSpec, IndexedDataSpec, Kernel, Level, Scalar, ScalarValue, Term},
    natural::Natural,
};
use std::fmt::{self, Write as _};

/// Nesting limit of the reader, so a hostile file cannot exhaust the stack.
const MAX_DEPTH: usize = 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;
fn fail<T>(message: impl Into<String>) -> Result<T> {
    Err(Error(message.into()))
}

/// An S-expression: an atom (a maximal run of bytes other than whitespace,
/// parentheses and `;`) or a parenthesized list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}
impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(atom) => f.write_str(atom),
            Sexp::List(items) => {
                f.write_char('(')?;
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        f.write_char(' ')?;
                    }
                    write!(f, "{item}")?;
                }
                f.write_char(')')
            }
        }
    }
}
fn atom(text: impl Into<String>) -> Sexp {
    Sexp::Atom(text.into())
}
fn list(items: impl IntoIterator<Item = Sexp>) -> Sexp {
    Sexp::List(items.into_iter().collect())
}
fn tagged(tag: &str, items: impl IntoIterator<Item = Sexp>) -> Sexp {
    list(std::iter::once(atom(tag)).chain(items))
}

/// Read every top-level S-expression. `;` starts a comment to end of line.
pub fn read(text: &str) -> Result<Vec<Sexp>> {
    let bytes = text.as_bytes();
    let mut at = 0;
    let mut items = Vec::new();
    loop {
        skip_space(bytes, &mut at);
        if at == bytes.len() {
            return Ok(items);
        }
        items.push(read_one(bytes, &mut at, 0)?);
    }
}
fn skip_space(bytes: &[u8], at: &mut usize) {
    while *at < bytes.len() {
        match bytes[*at] {
            b' ' | b'\t' | b'\n' | b'\r' => *at += 1,
            b';' => {
                while *at < bytes.len() && bytes[*at] != b'\n' {
                    *at += 1;
                }
            }
            _ => break,
        }
    }
}
fn read_one(bytes: &[u8], at: &mut usize, depth: usize) -> Result<Sexp> {
    if depth > MAX_DEPTH {
        return fail("exchange input nests too deeply");
    }
    skip_space(bytes, at);
    match bytes.get(*at) {
        None => fail("unexpected end of exchange input"),
        Some(b')') => fail(format!("unexpected ')' at byte {at}")),
        Some(b'(') => {
            *at += 1;
            let mut items = Vec::new();
            loop {
                skip_space(bytes, at);
                match bytes.get(*at) {
                    None => return fail("unclosed '(' in exchange input"),
                    Some(b')') => {
                        *at += 1;
                        return Ok(Sexp::List(items));
                    }
                    Some(_) => items.push(read_one(bytes, at, depth + 1)?),
                }
            }
        }
        Some(_) => {
            let start = *at;
            while *at < bytes.len()
                && !matches!(
                    bytes[*at],
                    b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')' | b';'
                )
            {
                *at += 1;
            }
            std::str::from_utf8(&bytes[start..*at])
                .map(atom)
                .map_err(|_| Error("exchange atoms must be UTF-8".into()))
        }
    }
}

// ---------------------------------------------------------------- printing

pub fn level_sexp(level: &Level) -> Sexp {
    let mut parts = Vec::new();
    let constant = level.constant_part();
    if constant > 0 || level.parameter_offsets().is_empty() {
        parts.push(atom(constant.to_string()));
    }
    for (index, offset) in level.parameter_offsets() {
        let mut part = tagged("u", [atom(index.to_string())]);
        for _ in 0..*offset {
            part = tagged("succ", [part]);
        }
        parts.push(part);
    }
    if parts.len() == 1 {
        parts.pop().unwrap()
    } else {
        tagged("max", parts)
    }
}

pub fn term_sexp(term: &Term) -> Sexp {
    let s = |term: &Term| term_sexp(term);
    match term {
        Term::Var(index) => tagged("var", [atom(index.to_string())]),
        Term::Global(name, levels) => tagged(
            "global",
            std::iter::once(atom(name.clone())).chain(levels.iter().map(level_sexp)),
        ),
        Term::Universe(level) => tagged("sort", [level_sexp(level)]),
        Term::Prop => atom("prop"),
        Term::Pi { domain, codomain } => tagged("pi", [s(domain), s(codomain)]),
        Term::Lam { domain, body } => tagged("lam", [s(domain), s(body)]),
        Term::App(function, argument) => tagged("app", [s(function), s(argument)]),
        Term::Nat => atom("nat"),
        Term::Zero => atom("zero"),
        Term::Succ(value) => tagged("succ", [s(value)]),
        Term::Literal(value) => tagged("lit", [atom(value.to_string())]),
        Term::NatElim {
            motive,
            zero,
            step,
            value,
        } => tagged("natelim", [s(motive), s(zero), s(step), s(value)]),
        Term::Eq { ty, left, right } => tagged("eq", [s(ty), s(left), s(right)]),
        Term::Refl { ty, value } => tagged("refl", [s(ty), s(value)]),
        Term::Transport {
            ty,
            from,
            to,
            motive,
            proof,
            value,
        } => tagged(
            "transport",
            [s(ty), s(from), s(to), s(motive), s(proof), s(value)],
        ),
        Term::EqElim {
            ty,
            left,
            right,
            motive,
            refl,
            proof,
        } => tagged(
            "eqelim",
            [s(ty), s(left), s(right), s(motive), s(refl), s(proof)],
        ),
        Term::IndElim {
            data,
            motive,
            branches,
            scrutinee,
        } => tagged(
            "indelim",
            [
                atom(data.clone()),
                s(motive),
                list(branches.iter().map(term_sexp)),
                s(scrutinee),
            ],
        ),
        Term::Scalar(scalar) => tagged("scalar", [atom(scalar.name())]),
        Term::ScalarLiteral(ScalarValue::I64(value)) => tagged("i64", [atom(value.to_string())]),
        Term::ScalarLiteral(ScalarValue::Bool(value)) => tagged("bool", [atom(value.to_string())]),
        Term::ScalarLiteral(ScalarValue::Unit) => atom("unit"),
    }
}

fn terms(items: &[Term]) -> Sexp {
    list(items.iter().map(term_sexp))
}

pub fn data_sexp(spec: &IndexedDataSpec) -> Sexp {
    let mut items = vec![
        atom(spec.name.clone()),
        atom(spec.levels.to_string()),
        atom(if spec.prop { "prop" } else { "type" }),
        terms(&spec.params),
    ];
    for constructor in &spec.constructors {
        items.push(tagged(
            "ctor",
            [
                atom(constructor.name.clone()),
                terms(&constructor.locals),
                terms(&constructor.fields),
                terms(&constructor.result),
            ],
        ));
    }
    tagged("data", items)
}

pub fn def_sexp(name: &str, levels: u32, ty: &Term, value: &Term) -> Sexp {
    tagged(
        "def",
        [
            atom(name),
            atom(levels.to_string()),
            term_sexp(ty),
            term_sexp(value),
        ],
    )
}

/// The admitted data family `name`, as the specification that admits it.
fn data_spec(kernel: &Kernel, name: &str) -> Option<IndexedDataSpec> {
    let info = kernel.data(name)?;
    Some(IndexedDataSpec {
        name: info.name.clone(),
        params: info.params.clone(),
        constructors: info
            .constructors
            .iter()
            .map(|constructor| IndexedConstructorSpec {
                name: constructor.name.clone(),
                locals: constructor.locals.clone(),
                fields: constructor.fields.clone(),
                result: constructor.result.clone(),
            })
            .collect(),
        prop: info.prop,
        levels: info.levels,
    })
}

/// Print a checked module's environment in admission order, one declaration
/// per line, followed by a `normalize` query for every definition (each
/// universe parameter instantiated at level 0).
pub fn dump(module: &CheckedModule) -> String {
    let kernel = &module.kernel;
    let mut out = String::new();
    let mut queries = Vec::new();
    for name in &module.definitions {
        if let Some(spec) = data_spec(kernel, name) {
            let _ = writeln!(out, "{}", data_sexp(&spec));
            continue;
        }
        let (Some(ty), Some(value)) = (kernel.definition_type(name), kernel.definition_value(name))
        else {
            continue;
        };
        let levels = kernel.global_levels(name).unwrap_or(0);
        let _ = writeln!(out, "{}", def_sexp(name, levels, ty, value));
        let global = Term::Global(name.clone(), vec![Level::zero(); levels as usize]);
        queries.push(tagged("normalize", [term_sexp(&global)]));
    }
    for query in queries {
        let _ = writeln!(out, "{query}");
    }
    out
}

// ----------------------------------------------------------------- parsing

fn expect_atom<'a>(sexp: &'a Sexp, what: &str) -> Result<&'a str> {
    match sexp {
        Sexp::Atom(text) => Ok(text),
        Sexp::List(_) => fail(format!("expected {what}, found a list")),
    }
}
fn expect_list<'a>(sexp: &'a Sexp, what: &str) -> Result<&'a [Sexp]> {
    match sexp {
        Sexp::List(items) => Ok(items),
        Sexp::Atom(text) => fail(format!("expected {what}, found '{text}'")),
    }
}
fn number<T: std::str::FromStr>(sexp: &Sexp, what: &str) -> Result<T> {
    let text = expect_atom(sexp, what)?;
    text.parse()
        .map_err(|_| Error(format!("expected {what}, found '{text}'")))
}
/// Split `(tag args...)` into the tag and its arguments, checking arity.
fn form(items: &[Sexp], arity: usize) -> Result<&[Sexp]> {
    let tag = expect_atom(&items[0], "a form tag")?;
    if items.len() != arity + 1 {
        return fail(format!(
            "'{tag}' takes {arity} arguments, found {}",
            items.len() - 1
        ));
    }
    Ok(&items[1..])
}

pub fn parse_level(sexp: &Sexp) -> Result<Level> {
    match sexp {
        Sexp::Atom(_) => Ok(Level::constant(number(sexp, "a universe level")?)),
        Sexp::List(items) if !items.is_empty() => match expect_atom(&items[0], "a level form")? {
            "u" => Ok(Level::param(number(
                &form(items, 1)?[0],
                "a level parameter",
            )?)),
            "succ" => parse_level(&form(items, 1)?[0])?
                .succ()
                .map_err(|e| Error(e.to_string())),
            "max" if items.len() >= 2 => {
                let mut level = parse_level(&items[1])?;
                for item in &items[2..] {
                    level = level.max(&parse_level(item)?);
                }
                Ok(level)
            }
            other => fail(format!("unknown level form '{other}'")),
        },
        Sexp::List(_) => fail("empty level form"),
    }
}

pub fn parse_term(sexp: &Sexp) -> Result<Term> {
    let b = |sexp: &Sexp| parse_term(sexp).map(Box::new);
    let items = match sexp {
        Sexp::Atom(text) => {
            return match text.as_str() {
                "prop" => Ok(Term::Prop),
                "nat" => Ok(Term::Nat),
                "zero" => Ok(Term::Zero),
                "unit" => Ok(Term::unit()),
                other => fail(format!("unknown term atom '{other}'")),
            };
        }
        Sexp::List(items) if items.is_empty() => return fail("empty term form"),
        Sexp::List(items) => items,
    };
    let tag = expect_atom(&items[0], "a term form")?;
    Ok(match tag {
        "var" => Term::Var(number(&form(items, 1)?[0], "a de Bruijn index")?),
        "global" => {
            if items.len() < 2 {
                return fail("'global' needs a name");
            }
            Term::Global(
                expect_atom(&items[1], "a global name")?.to_owned(),
                items[2..].iter().map(parse_level).collect::<Result<_>>()?,
            )
        }
        "sort" => Term::Universe(parse_level(&form(items, 1)?[0])?),
        "pi" => {
            let a = form(items, 2)?;
            Term::Pi {
                domain: b(&a[0])?,
                codomain: b(&a[1])?,
            }
        }
        "lam" => {
            let a = form(items, 2)?;
            Term::Lam {
                domain: b(&a[0])?,
                body: b(&a[1])?,
            }
        }
        "app" => {
            let a = form(items, 2)?;
            Term::App(b(&a[0])?, b(&a[1])?)
        }
        "succ" => Term::Succ(b(&form(items, 1)?[0])?),
        "lit" => {
            let text = expect_atom(&form(items, 1)?[0], "a natural")?;
            let value: Natural = text.parse().map_err(|e| Error(format!("{e}")))?;
            Term::natural(value)
        }
        "natelim" => {
            let a = form(items, 4)?;
            Term::NatElim {
                motive: b(&a[0])?,
                zero: b(&a[1])?,
                step: b(&a[2])?,
                value: b(&a[3])?,
            }
        }
        "eq" => {
            let a = form(items, 3)?;
            Term::Eq {
                ty: b(&a[0])?,
                left: b(&a[1])?,
                right: b(&a[2])?,
            }
        }
        "refl" => {
            let a = form(items, 2)?;
            Term::Refl {
                ty: b(&a[0])?,
                value: b(&a[1])?,
            }
        }
        "transport" => {
            let a = form(items, 6)?;
            Term::Transport {
                ty: b(&a[0])?,
                from: b(&a[1])?,
                to: b(&a[2])?,
                motive: b(&a[3])?,
                proof: b(&a[4])?,
                value: b(&a[5])?,
            }
        }
        "eqelim" => {
            let a = form(items, 6)?;
            Term::EqElim {
                ty: b(&a[0])?,
                left: b(&a[1])?,
                right: b(&a[2])?,
                motive: b(&a[3])?,
                refl: b(&a[4])?,
                proof: b(&a[5])?,
            }
        }
        "indelim" => {
            let a = form(items, 4)?;
            Term::IndElim {
                data: expect_atom(&a[0], "a data family name")?.to_owned(),
                motive: b(&a[1])?,
                branches: parse_terms(&a[2], "a branch list")?,
                scrutinee: b(&a[3])?,
            }
        }
        "scalar" => Term::Scalar(match expect_atom(&form(items, 1)?[0], "a scalar")? {
            "i64" => Scalar::I64,
            "Bool" => Scalar::Bool,
            "Unit" => Scalar::Unit,
            other => return fail(format!("unknown scalar '{other}'")),
        }),
        "i64" => Term::i64(number(&form(items, 1)?[0], "an i64")?),
        "bool" => Term::boolean(number(&form(items, 1)?[0], "a boolean")?),
        other => return fail(format!("unknown term form '{other}'")),
    })
}

fn parse_terms(sexp: &Sexp, what: &str) -> Result<Vec<Term>> {
    expect_list(sexp, what)?.iter().map(parse_term).collect()
}

/// One item of an exchange file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    Def {
        name: String,
        levels: u32,
        ty: Term,
        value: Term,
    },
    Data(IndexedDataSpec),
    /// Check a closed term against a closed type.
    Check {
        term: Term,
        ty: Term,
    },
    /// Infer and print the normal form of a closed term's type.
    Infer(Term),
    /// Check, then print the normal form of a closed term.
    Normalize(Term),
}

pub fn parse_item(sexp: &Sexp) -> Result<Item> {
    let items = expect_list(sexp, "a declaration or query")?;
    if items.is_empty() {
        return fail("empty item");
    }
    Ok(match expect_atom(&items[0], "an item tag")? {
        "def" => {
            let a = form(items, 4)?;
            Item::Def {
                name: expect_atom(&a[0], "a definition name")?.to_owned(),
                levels: number(&a[1], "a level parameter count")?,
                ty: parse_term(&a[2])?,
                value: parse_term(&a[3])?,
            }
        }
        "data" => {
            if items.len() < 5 {
                return fail("'data' needs a name, level count, sort and parameter list");
            }
            let prop = match expect_atom(&items[3], "type or prop")? {
                "type" => false,
                "prop" => true,
                other => return fail(format!("expected type or prop, found '{other}'")),
            };
            let constructors = items[5..]
                .iter()
                .map(|sexp| {
                    let parts = expect_list(sexp, "a constructor")?;
                    if parts.is_empty() || expect_atom(&parts[0], "ctor")? != "ctor" {
                        return fail("expected (ctor name (locals) (fields) (result))");
                    }
                    let a = form(parts, 4)?;
                    Ok(IndexedConstructorSpec {
                        name: expect_atom(&a[0], "a constructor name")?.to_owned(),
                        locals: parse_terms(&a[1], "a local list")?,
                        fields: parse_terms(&a[2], "a field list")?,
                        result: parse_terms(&a[3], "a result list")?,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            Item::Data(IndexedDataSpec {
                name: expect_atom(&items[1], "a data family name")?.to_owned(),
                levels: number(&items[2], "a level parameter count")?,
                prop,
                params: parse_terms(&items[4], "a parameter list")?,
                constructors,
            })
        }
        "check" => {
            let a = form(items, 2)?;
            Item::Check {
                term: parse_term(&a[0])?,
                ty: parse_term(&a[1])?,
            }
        }
        "infer" => Item::Infer(parse_term(&form(items, 1)?[0])?),
        "normalize" => Item::Normalize(parse_term(&form(items, 1)?[0])?),
        other => return fail(format!("unknown item '{other}'")),
    })
}

pub fn parse(text: &str) -> Result<Vec<Item>> {
    read(text)?.iter().map(parse_item).collect()
}

// ---------------------------------------------------------------- answering

/// The outcome category of a failed kernel operation.
fn verdict(error: &crate::kernel::Error) -> &'static str {
    if error.0.contains("budget exhausted") {
        "budget"
    } else {
        "reject"
    }
}

/// Replay an exchange file with the Rust kernel. One line per item:
/// `ok NAME` / `reject NAME` / `budget NAME` for declarations, `ok` /
/// `reject` / `budget` for checks, and `= TERM` or `: TYPE` for normalize and
/// infer queries. A rejected declaration is not admitted, exactly as in the
/// kernel, so later items that use it are rejected too.
pub fn answer(text: &str) -> Result<String> {
    let mut kernel = Kernel::default();
    let mut out = String::new();
    for item in parse(text)? {
        let line = match item {
            Item::Def {
                name,
                levels,
                ty,
                value,
            } => match kernel.define_polymorphic(name.clone(), levels, ty, value) {
                Ok(()) => format!("ok {name}"),
                Err(error) => format!("{} {name}", verdict(&error)),
            },
            Item::Data(spec) => {
                let name = spec.name.clone();
                match kernel.define_indexed_data(spec) {
                    Ok(()) => format!("ok {name}"),
                    Err(error) => format!("{} {name}", verdict(&error)),
                }
            }
            Item::Check { term, ty } => match kernel.check_closed(&term, &ty) {
                Ok(()) => "ok".into(),
                Err(error) => verdict(&error).into(),
            },
            Item::Infer(term) => match kernel.infer_closed(&term) {
                Ok(ty) => format!(": {}", term_sexp(&ty)),
                Err(error) => verdict(&error).into(),
            },
            Item::Normalize(term) => match kernel.normalize_closed(&term) {
                Ok(normal) => format!("= {}", term_sexp(&normal)),
                Err(error) => verdict(&error).into(),
            },
        };
        out.push_str(&line);
        out.push('\n');
    }
    Ok(out)
}
