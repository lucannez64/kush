//! PROOF-FUZZ generators for records, enums and generic functions (PF-RECORDS).
//!
//! A parameter whose type is a record or an enum is built from several tape
//! slots by *makers*: generated functions appended to the module that
//! defines the type, where its field types are written in that module's own
//! terms. The harness, in the target's module, calls them through module
//! aliases (adding a `use` when the alias is free), so the tape itself stays a
//! flat list of scalars and collections.
//!
//! - A record whose fields are all `pub` is open data: any field values make
//!   one, and it is built field by field.
//! - A record with private fields is built by a constructor function of its
//!   module (one returning it, preferably `new`), never field by field: its
//!   invariants belong to that module.
//! - An enum (not generic) is a tag byte choosing a variant, plus each
//!   variant's payload.
//! - A generic function's type parameters are fixed once: an unbounded one is
//!   `i64`, a bounded one the first type implementing its trait that can be
//!   built.
//!
//! A value built from a generated record may be a state the program never
//! creates, so its findings are local, never bugs. See docs/proof-fuzz.md,
//! section 2.4.
use super::harness::{Collection, Passing, Scalar, Slot, MAX_EXTRA_LENGTH};
use crate::ast::{self, ExprKind, ItemKind, Payload, TypeKind};
use crate::lexer::Kind;
use crate::program::Program;
use std::collections::{BTreeMap, BTreeSet};

/// Deepest nesting of records and enums built for one parameter.
const MAX_DEPTH: usize = 8;

/// A generated function appended to a module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Maker {
    /// The module it is appended to, dotted.
    pub module: String,
    pub name: String,
    pub text: String,
}

/// How a runtime parameter's value is made from tape slots.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Build {
    /// The slot with this index.
    Leaf(usize),
    /// A call of a maker (`alias.__kush_fuzz_make_T`, as the harness's
    /// module names it) on the values of `arguments`.
    Make { call: String, arguments: Vec<Build> },
}

/// A runtime parameter that is built rather than one slot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Built {
    /// Its position among the function's runtime parameters.
    pub parameter: usize,
    pub build: Build,
    pub passing: Passing,
}

/// A type resolved in the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Scalar(Scalar),
    Bytes,
    Vec(Scalar),
    /// A struct or enum declared in `unit`, applied to `arguments`.
    Nominal {
        unit: usize,
        name: String,
        arguments: Vec<Ty>,
    },
}

/// What one unit declares and imports.
struct UnitTypes {
    module: Vec<String>,
    file: usize,
    /// Struct, enum, trait and constant declarations: name -> item index.
    structs: BTreeMap<String, usize>,
    enums: BTreeMap<String, usize>,
    traits: BTreeMap<String, usize>,
    constants: BTreeMap<String, usize>,
    functions: Vec<usize>,
    impls: Vec<usize>,
    /// `use a.b;`: `b` -> the unit of `a.b`.
    aliases: BTreeMap<String, usize>,
    /// `use a.b.Item;`: `Item` -> (the unit of `a.b`, `Item`).
    imported: BTreeMap<String, (usize, String)>,
    /// Every name declared or imported at the top level.
    names: BTreeSet<String>,
}

/// The program's types, for building generators.
pub struct Types<'p> {
    program: &'p Program,
    units: Vec<UnitTypes>,
    /// Module aliases harnesses add, program-wide: `(unit, alias)` -> the
    /// unit it names. Two harnesses in one module may not use one alias for
    /// two modules.
    aliases: std::cell::RefCell<BTreeMap<(usize, String), usize>>,
}

impl<'p> Types<'p> {
    pub fn new(program: &'p Program) -> Self {
        let mut units = Vec::new();
        for unit in &program.units {
            let mut types = UnitTypes {
                module: super::harness::unit_module(program, unit),
                file: unit.file,
                structs: BTreeMap::new(),
                enums: BTreeMap::new(),
                traits: BTreeMap::new(),
                constants: BTreeMap::new(),
                functions: Vec::new(),
                impls: Vec::new(),
                aliases: BTreeMap::new(),
                imported: BTreeMap::new(),
                names: BTreeSet::new(),
            };
            for index in unit.items.clone() {
                let item = &program.module.items[index].item;
                match &item.kind {
                    ItemKind::Struct { name, .. } => {
                        types.structs.insert(name.clone(), index);
                        types.names.insert(name.clone());
                    }
                    ItemKind::Enum { name, .. } => {
                        types.enums.insert(name.clone(), index);
                        types.names.insert(name.clone());
                    }
                    ItemKind::Trait { name, .. } => {
                        types.traits.insert(name.clone(), index);
                        types.names.insert(name.clone());
                    }
                    ItemKind::Function(function) => {
                        if function.constant {
                            types.constants.insert(function.name.clone(), index);
                        }
                        types.functions.push(index);
                        types.names.insert(function.name.clone());
                    }
                    ItemKind::Impl { .. } => types.impls.push(index),
                    ItemKind::Use(path) => {
                        let Some(last) = path.last() else {
                            continue;
                        };
                        types.names.insert(last.clone());
                        match unit.imports.get(&item.span.start) {
                            Some((target, None)) => {
                                types.aliases.insert(last.clone(), *target);
                            }
                            Some((target, Some(name))) => {
                                types.imported.insert(last.clone(), (*target, name.clone()));
                            }
                            None => {}
                        }
                    }
                    ItemKind::Prop { name, .. }
                    | ItemKind::Alias { name, .. }
                    | ItemKind::Effect { name, .. }
                    | ItemKind::EffectRow { name, .. } => {
                        types.names.insert(name.clone());
                    }
                    _ => {}
                }
            }
            units.push(types);
        }
        Self {
            program,
            units,
            aliases: std::cell::RefCell::new(BTreeMap::new()),
        }
    }

    fn text(&self, unit: usize, span: crate::Span) -> &'p str {
        let file = &self.program.sources.files[self.units[unit].file];
        file.text
            .get(span.start - file.base..span.end - file.base)
            .unwrap_or("")
    }

    fn item(&self, index: usize) -> &'p ast::Declaration {
        &self.program.module.items[index]
    }

    /// The unit declaring a named type or trait written `path` in `unit`.
    fn lookup(&self, unit: usize, path: &[String], kind: Lookup) -> Option<(usize, String)> {
        let declares = |unit: usize, name: &str| {
            let types = &self.units[unit];
            match kind {
                Lookup::Type => types.structs.contains_key(name) || types.enums.contains_key(name),
                Lookup::Trait => types.traits.contains_key(name),
                Lookup::Constant => types.constants.contains_key(name),
            }
        };
        match path {
            [name] => {
                if declares(unit, name) {
                    return Some((unit, name.clone()));
                }
                let (target, item) = self.units[unit].imported.get(name)?;
                declares(*target, item).then(|| (*target, item.clone()))
            }
            [alias, name] => {
                let target = *self.units[unit].aliases.get(alias)?;
                declares(target, name).then(|| (target, name.clone()))
            }
            _ => None,
        }
    }

    /// Resolve a written type in `unit`, with generic names bound by `env`.
    fn resolve(&self, ty: &ast::Type, unit: usize, env: &BTreeMap<String, Ty>) -> Result<Ty, String> {
        let unsupported = || format!("no generator for `{}`", self.text(unit, ty.span).trim());
        let TypeKind::Named { path, arguments } = &ty.kind else {
            return Err(unsupported());
        };
        if let [name] = path.as_slice() {
            if arguments.is_empty() {
                if let Some(scalar) = Scalar::from_name(name) {
                    return Ok(Ty::Scalar(scalar));
                }
                if name == "Bytes" {
                    return Ok(Ty::Bytes);
                }
                if let Some(bound) = env.get(name) {
                    return Ok(bound.clone());
                }
            }
            if name == "Vec" {
                return match arguments.as_slice() {
                    [element] => match self.resolve(element, unit, env)? {
                        Ty::Scalar(scalar) => Ok(Ty::Vec(scalar)),
                        _ => Err(unsupported()),
                    },
                    _ => Err(unsupported()),
                };
            }
        }
        let (declared, name) = self.lookup(unit, path, Lookup::Type).ok_or_else(unsupported)?;
        let arguments = arguments
            .iter()
            .map(|argument| self.resolve(argument, unit, env))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Ty::Nominal {
            unit: declared,
            name,
            arguments,
        })
    }

    /// A compile-time integer: literals, constants and `+ - * <<` of them.
    fn evaluate(&self, expr: &ast::Expr, unit: usize, depth: usize) -> Option<i128> {
        if depth > 16 {
            return None;
        }
        match &expr.kind {
            ExprKind::Integer(text) => super::harness::integer_literal(text),
            ExprKind::Name(name) => {
                let (declared, name) = self.lookup(unit, std::slice::from_ref(name), Lookup::Constant)?;
                let index = self.units[declared].constants[&name];
                let ItemKind::Function(function) = &self.item(index).item.kind else {
                    return None;
                };
                let tail = function.body.as_ref()?.tail.as_ref()?;
                self.evaluate(tail, declared, depth + 1)
            }
            ExprKind::Binary { op, left, right } => {
                let left = self.evaluate(left, unit, depth + 1)?;
                let right = self.evaluate(right, unit, depth + 1)?;
                match op {
                    Kind::Plus => left.checked_add(right),
                    Kind::Minus => left.checked_sub(right),
                    Kind::Star => left.checked_mul(right),
                    Kind::Shl => u32::try_from(right).ok().and_then(|r| left.checked_shl(r)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The types a bounded generic parameter may be fixed to: every
    /// non-generic struct or enum with an `impl` of the bound's trait.
    fn implementors(&self, bound: &ast::Type, unit: usize) -> Vec<Ty> {
        let TypeKind::Named { path, .. } = &bound.kind else {
            return Vec::new();
        };
        let Some(wanted) = self.lookup(unit, path, Lookup::Trait) else {
            return Vec::new();
        };
        let mut found = Vec::new();
        for (index, types) in self.units.iter().enumerate() {
            for &item in &types.impls {
                let ItemKind::Impl {
                    generics,
                    trait_path: Some(trait_path),
                    self_ty,
                    ..
                } = &self.item(item).item.kind
                else {
                    continue;
                };
                let TypeKind::Named { path, .. } = &trait_path.kind else {
                    continue;
                };
                if !generics.is_empty() || self.lookup(index, path, Lookup::Trait).as_ref() != Some(&wanted) {
                    continue;
                }
                if let Ok(ty @ Ty::Nominal { .. }) = self.resolve(self_ty, index, &BTreeMap::new()) {
                    found.push(ty);
                }
            }
        }
        found
    }
}

#[derive(Clone, Copy)]
enum Lookup {
    Type,
    Trait,
    Constant,
}

/// The slots, makers and imports one target's harness needs.
pub struct Generator<'t, 'p> {
    types: &'t Types<'p>,
    /// The unit the harness is appended to.
    home: usize,
    pub slots: Vec<Slot>,
    pub offset: usize,
    pub labels: BTreeMap<usize, Vec<String>>,
    pub makers: Vec<Maker>,
    /// Imports added to the harness's module: `(module, imported module)`.
    pub uses: Vec<(String, String)>,
    /// Module aliases added so far, so one is added once.
    added: BTreeMap<String, usize>,
    /// Extra effects the makers perform (a constructor's).
    pub effects: BTreeSet<String>,
    /// Records built so far (field by field or by a constructor).
    pub records: usize,
}

/// A generator's state, to roll a failed attempt back.
struct Snapshot {
    slots: usize,
    offset: usize,
    labels: BTreeMap<usize, Vec<String>>,
    makers: usize,
    uses: usize,
    added: BTreeMap<String, usize>,
    effects: BTreeSet<String>,
    records: usize,
}

impl<'t, 'p> Generator<'t, 'p> {
    pub fn new(types: &'t Types<'p>, home: usize) -> Self {
        Self {
            types,
            home,
            slots: Vec::new(),
            offset: 0,
            labels: BTreeMap::new(),
            makers: Vec::new(),
            uses: Vec::new(),
            added: BTreeMap::new(),
            effects: BTreeSet::new(),
            records: 0,
        }
    }

    /// The bindings of a generic function's type parameters.
    pub fn instantiate(&mut self, generics: &[ast::Generic]) -> Result<BTreeMap<String, Ty>, String> {
        let mut env = BTreeMap::new();
        for generic in generics {
            if generic.excludes.is_some() || generic.includes.is_some() {
                return Err("generic over effects".into());
            }
            let ty = match &generic.bound {
                None => Ty::Scalar(Scalar::from_name("i64").expect("i64 is a scalar")),
                Some(bound) => {
                    if let TypeKind::Named { path, .. } = &bound.kind
                        && let [kind] = path.as_slice()
                        && matches!(kind.as_str(), "Nat" | "Effects" | "Grade" | "Prop" | "Type")
                    {
                        return Err(format!("generic over `{kind}`"));
                    }
                    let candidates = self.types.implementors(bound, self.home);
                    // The first that can be built (a probe, rolled back).
                    let chosen = candidates.into_iter().find(|candidate| {
                        let saved = self.save();
                        let built = self.value(candidate, 0, "probe", 0).is_ok();
                        self.restore(saved);
                        built
                    });
                    chosen.ok_or_else(|| {
                        format!(
                            "no buildable type implements `{}`",
                            self.types.text(self.home, bound.span).trim()
                        )
                    })?
                }
            };
            env.insert(generic.name.clone(), ty);
        }
        Ok(env)
    }

    /// Build a parameter of type `ty` written in the harness's unit.
    pub fn parameter(
        &mut self,
        ty: &ast::Type,
        env: &BTreeMap<String, Ty>,
        minimum: usize,
        name: &str,
    ) -> Result<Build, String> {
        let resolved = self.types.resolve(ty, self.home, env)?;
        self.value(&resolved, minimum, name, 0)
    }

    fn save(&self) -> Snapshot {
        Snapshot {
            slots: self.slots.len(),
            offset: self.offset,
            labels: self.labels.clone(),
            makers: self.makers.len(),
            uses: self.uses.len(),
            added: self.added.clone(),
            effects: self.effects.clone(),
            records: self.records,
        }
    }

    fn restore(&mut self, saved: Snapshot) {
        self.slots.truncate(saved.slots);
        self.offset = saved.offset;
        self.labels = saved.labels;
        self.makers.truncate(saved.makers);
        self.uses.truncate(saved.uses);
        self.added = saved.added;
        self.effects = saved.effects;
        self.records = saved.records;
    }

    fn value(&mut self, ty: &Ty, minimum: usize, name: &str, depth: usize) -> Result<Build, String> {
        if depth > MAX_DEPTH {
            return Err(format!("`{name}` nests records too deeply"));
        }
        match ty {
            Ty::Scalar(scalar) => {
                self.slots.push(Slot::Scalar {
                    name: name.to_owned(),
                    offset: self.offset,
                    scalar: *scalar,
                    passing: Passing::Value,
                });
                self.offset += scalar.width();
                Ok(Build::Leaf(self.slots.len() - 1))
            }
            Ty::Bytes | Ty::Vec(_) => {
                self.slots.push(Slot::Collection {
                    name: name.to_owned(),
                    offset: self.offset,
                    collection: match ty {
                        Ty::Vec(element) => Collection::Vec(*element),
                        _ => Collection::Bytes,
                    },
                    minimum,
                    maximum: MAX_EXTRA_LENGTH,
                    passing: Passing::Value,
                });
                self.offset += 2;
                Ok(Build::Leaf(self.slots.len() - 1))
            }
            Ty::Nominal {
                unit,
                name: type_name,
                arguments,
            } => {
                let types = &self.types.units[*unit];
                if types.module.first().is_some_and(|first| first == "std") {
                    return Err(format!("no generator for `{type_name}` (a standard-library type)"));
                }
                if let Some(&index) = types.enums.get(type_name) {
                    self.enumeration(*unit, index, type_name, arguments, name, depth)
                } else {
                    let index = types.structs[type_name];
                    self.record(*unit, index, type_name, arguments, name, depth)
                }
            }
        }
    }

    /// How the harness's module calls `maker` of `unit`.
    fn call(&mut self, unit: usize, maker: &str) -> Result<String, String> {
        if unit == self.home {
            return Ok(maker.to_owned());
        }
        let home = &self.types.units[self.home];
        if let Some((alias, _)) = home.aliases.iter().find(|(_, target)| **target == unit) {
            return Ok(format!("{alias}.{maker}"));
        }
        if let Some((alias, _)) = self.added.iter().find(|(_, target)| **target == unit) {
            return Ok(format!("{alias}.{maker}"));
        }
        let module = &self.types.units[unit].module;
        let last = module.last().cloned().unwrap_or_default();
        let taken = self
            .types
            .aliases
            .borrow()
            .get(&(self.home, last.clone()))
            .is_some_and(|&other| other != unit);
        if last.is_empty() || home.names.contains(&last) || self.added.contains_key(&last) || taken {
            return Err(format!(
                "cannot name module `{}` from `{}`",
                module.join("."),
                home.module.join(".")
            ));
        }
        self.added.insert(last.clone(), unit);
        self.types.aliases.borrow_mut().insert((self.home, last.clone()), unit);
        self.uses.push((home.module.join("."), module.join(".")));
        Ok(format!("{last}.{maker}"))
    }

    fn add_maker(&mut self, unit: usize, name: &str, text: String) {
        let module = self.types.units[unit].module.join(".");
        if !self.makers.iter().any(|m| m.module == module && m.name == name) {
            self.makers.push(Maker {
                module,
                name: name.to_owned(),
                text,
            });
        }
    }

    fn enumeration(
        &mut self,
        unit: usize,
        index: usize,
        type_name: &str,
        arguments: &[Ty],
        name: &str,
        depth: usize,
    ) -> Result<Build, String> {
        let ItemKind::Enum { generics, variants, .. } = &self.types.item(index).item.kind else {
            unreachable!("an enum item");
        };
        if !generics.is_empty() || !arguments.is_empty() || variants.is_empty() || variants.len() > 256 {
            return Err(format!("no generator for `{type_name}` (a generic enum)"));
        }
        let tag = self.slots.len();
        self.slots.push(Slot::Scalar {
            name: name.to_owned(),
            offset: self.offset,
            scalar: Scalar::from_name("u8").expect("u8 is a scalar"),
            passing: Passing::Value,
        });
        self.offset += 1;
        self.labels
            .insert(tag, variants.iter().map(|v| format!("{type_name}.{}", v.name)).collect());
        let mut parameters = vec!["tag: u8".to_owned()];
        let mut built = vec![Build::Leaf(tag)];
        let mut body = format!("    let which = tag % {};\n", variants.len());
        for (position, variant) in variants.iter().enumerate() {
            let components: Vec<&ast::Type> = match &variant.payload {
                Payload::Unit => Vec::new(),
                Payload::Tuple(types) => types.iter().collect(),
                _ => return Err(format!("no generator for `{type_name}.{}`", variant.name)),
            };
            if variant.result.is_some() || !variant.locals.is_empty() {
                return Err(format!("no generator for `{type_name}` (an indexed enum)"));
            }
            let mut names = Vec::new();
            for (k, component) in components.iter().enumerate() {
                let resolved = self.types.resolve(component, unit, &BTreeMap::new())?;
                let parameter = format!("p{}", parameters.len());
                built.push(self.value(&resolved, 0, &format!("{name}.{}.{k}", variant.name), depth + 1)?);
                parameters.push(format!("{parameter}: {}", self.types.text(unit, component.span).trim()));
                names.push(parameter);
            }
            let value = if names.is_empty() {
                format!("{type_name}.{}", variant.name)
            } else {
                format!("{type_name}.{}({})", variant.name, names.join(", "))
            };
            if position + 1 == variants.len() {
                body.push_str(&format!("    {value}\n"));
            } else {
                body.push_str(&format!("    if which == {position} {{ return {value}; }}\n"));
            }
        }
        let maker = format!("__kush_fuzz_make_{type_name}");
        let text = format!(
            "\npub fn {maker}({}) -> {type_name} ! {{panic}} {{\n{body}}}\n",
            parameters.join(", ")
        );
        self.add_maker(unit, &maker, text);
        Ok(Build::Make {
            call: self.call(unit, &maker)?,
            arguments: built,
        })
    }

    fn record(
        &mut self,
        unit: usize,
        index: usize,
        type_name: &str,
        arguments: &[Ty],
        name: &str,
        depth: usize,
    ) -> Result<Build, String> {
        let declaration = self.types.item(index);
        let ItemKind::Struct {
            lifetimes,
            generics,
            fields,
            ..
        } = &declaration.item.kind
        else {
            unreachable!("a struct item");
        };
        if !lifetimes.is_empty() || !declaration.attributes.is_empty() {
            return Err(format!("no generator for `{type_name}` (a borrowed or foreign record)"));
        }
        if generics.len() != arguments.len() {
            return Err(format!("no generator for `{type_name}`"));
        }
        let env: BTreeMap<String, Ty> = generics
            .iter()
            .map(|g| g.name.clone())
            .zip(arguments.iter().cloned())
            .collect();
        if fields.iter().all(|field| field.public) {
            self.fields(unit, type_name, generics, fields, &env, name, depth)
        } else {
            self.constructor(unit, type_name, generics, name, depth)
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn fields(
        &mut self,
        unit: usize,
        type_name: &str,
        generics: &[ast::Generic],
        fields: &[ast::Field],
        env: &BTreeMap<String, Ty>,
        name: &str,
        depth: usize,
    ) -> Result<Build, String> {
        let mut parameters = Vec::new();
        let mut built = Vec::new();
        let mut assignments = Vec::new();
        for field in fields {
            let resolved = self.types.resolve(&field.ty, unit, env)?;
            // A length-refined field is checked by the record literal; the
            // tape always makes it at least that long.
            let minimum = match &field.min_length {
                None => 0,
                Some(length) => self
                    .types
                    .evaluate(length, unit, 0)
                    .and_then(|n| usize::try_from(n).ok())
                    .ok_or_else(|| format!("no generator for `{type_name}.{}` (its length)", field.name))?,
            };
            built.push(self.value(&resolved, minimum, &format!("{name}.{}", field.name), depth + 1)?);
            parameters.push(format!("{}: {}", field.name, self.types.text(unit, field.ty.span).trim()));
            assignments.push(format!("{0}: {0}", field.name));
        }
        let (declared, applied) = self.generic_text(unit, generics);
        let maker = format!("__kush_fuzz_make_{type_name}");
        let text = format!(
            "\npub fn {maker}{declared}({}) -> {type_name}{applied} ! {{panic}} {{\n    {type_name} {{ {} }}\n}}\n",
            parameters.join(", "),
            assignments.join(", ")
        );
        self.add_maker(unit, &maker, text);
        self.records += 1;
        Ok(Build::Make {
            call: self.call(unit, &maker)?,
            arguments: built,
        })
    }

    /// `<A: Bound, B>` and `<A, B>` for a declaration's type parameters.
    fn generic_text(&self, unit: usize, generics: &[ast::Generic]) -> (String, String) {
        if generics.is_empty() {
            return (String::new(), String::new());
        }
        let declared: Vec<String> = generics
            .iter()
            .map(|g| match &g.bound {
                Some(bound) => format!("{}: {}", g.name, self.types.text(unit, bound.span).trim()),
                None => g.name.clone(),
            })
            .collect();
        let applied: Vec<&str> = generics.iter().map(|g| g.name.as_str()).collect();
        (format!("<{}>", declared.join(", ")), format!("<{}>", applied.join(", ")))
    }

    /// A record with private fields, from a function of its module that
    /// returns it: `new` if there is one, else the one with fewest
    /// parameters that can be generated.
    fn constructor(
        &mut self,
        unit: usize,
        type_name: &str,
        generics: &[ast::Generic],
        name: &str,
        depth: usize,
    ) -> Result<Build, String> {
        let reason = format!("no generator for `{type_name}` (private fields and no constructor)");
        if !generics.is_empty() {
            return Err(reason);
        }
        let mut candidates: Vec<&ast::Function> = Vec::new();
        for &index in &self.types.units[unit].functions {
            let ItemKind::Function(function) = &self.types.item(index).item.kind else {
                continue;
            };
            if function.constant
                || function.body.is_none()
                || !function.generics.is_empty()
                || function.parameters.iter().any(|p| p.erased)
            {
                continue;
            }
            let returns = matches!(
                self.types.resolve(&function.result, unit, &BTreeMap::new()),
                Ok(Ty::Nominal { unit: u, name: n, .. }) if u == unit && n == type_name
            );
            if returns {
                candidates.push(function);
            }
        }
        candidates.sort_by_key(|f| (f.name != "new", f.parameters.len()));
        for function in candidates {
            let mut effects = BTreeSet::new();
            let allowed = function.effects.iter().all(|effect| {
                let text = self.types.text(unit, effect.span).trim().to_owned();
                let ok = ["alloc", "panic"].contains(&text.as_str());
                effects.insert(text);
                ok
            });
            if !allowed {
                continue;
            }
            let saved = self.save();
            let mut parameters = Vec::new();
            let mut names = Vec::new();
            let mut built = Vec::new();
            let mut failed = false;
            for parameter in &function.parameters {
                let resolved = match self.types.resolve(&parameter.ty, unit, &BTreeMap::new()) {
                    Ok(resolved) => resolved,
                    Err(_) => {
                        failed = true;
                        break;
                    }
                };
                let minimum = match &parameter.min_length {
                    None => 0,
                    Some(length) => match self.types.evaluate(length, unit, 0).and_then(|n| usize::try_from(n).ok()) {
                        Some(n) => n,
                        None => {
                            failed = true;
                            break;
                        }
                    },
                };
                match self.value(&resolved, minimum, &format!("{name}.{}", parameter.name), depth + 1) {
                    Ok(build) => built.push(build),
                    Err(_) => {
                        failed = true;
                        break;
                    }
                }
                let refinement = parameter.min_length.as_ref().map_or(String::new(), |length| {
                    format!(" where len >= {}", self.types.text(unit, length.span).trim())
                });
                parameters.push(format!(
                    "{}: {}{refinement}",
                    parameter.name,
                    self.types.text(unit, parameter.ty.span).trim()
                ));
                names.push(parameter.name.clone());
            }
            if failed {
                self.restore(saved);
                continue;
            }
            let row: Vec<String> = effects.iter().cloned().collect();
            self.effects.extend(effects);
            let maker = format!("__kush_fuzz_make_{type_name}");
            let text = format!(
                "\npub fn {maker}({}) -> {type_name} ! {{{}}} {{\n    {}({})\n}}\n",
                parameters.join(", "),
                row.join(", "),
                function.name,
                names.join(", ")
            );
            self.add_maker(unit, &maker, text);
            self.records += 1;
            return Ok(Build::Make {
                call: self.call(unit, &maker)?,
                arguments: built,
            });
        }
        Err(reason)
    }
}
