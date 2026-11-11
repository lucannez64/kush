//! Lexical name resolution across the modules of a program. Each module has
//! its own top-level scope; `use` imports public items or whole modules. This
//! pass does not type-check members, patterns, effects, subtyping, or ownership.
use crate::{Diagnostic, Span, ast::*, program::Program};
use std::collections::{BTreeMap, BTreeSet};

pub type BindingId = usize;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingKind {
    Builtin,
    Function,
    Data,
    Alias,
    Constructor,
    Generic,
    Parameter,
    Local,
    /// A declared static-dispatch trait. Trait names are not runtime types.
    Trait,
    /// A declared finite grade algebra. Its name is not a runtime type and is
    /// only meaningful as the qualifier of a grade annotation.
    GradeAlgebra,
    /// A declared effect operation signature. The name is not a runtime value;
    /// it names the dynamic handler stack entry used by `perform`.
    Effect,
    /// A declared named effect row (`effect row Name = { ... };`). The name is
    /// only meaningful inside an effect-row position; it expands to a finite
    /// union and cannot be used as a runtime type.
    EffectRow,
}

/// One declared finite grade algebra. The carrier and operation tables stay as
/// source names; the grade pass validates and lowers them to a static runtime
/// description used by annotations.
#[derive(Debug, Clone)]
pub struct GradeAlgebraDecl {
    pub name: String,
    pub elements: Vec<String>,
    pub zero: String,
    pub one: String,
    pub add: Vec<GradeEquation>,
    pub mul: Vec<GradeEquation>,
    pub span: Span,
}
/// Where a generic binder appears. Effect-exclusion constraints are meaningful
/// only for executable function and method effect rows; every other declaration
/// form rejects them instead of silently dropping a checked promise.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GenericContext {
    Executable,
    Unsupported(&'static str),
}
#[derive(Debug, Clone)]
pub struct Binding {
    pub name: String,
    pub kind: BindingKind,
    pub span: Span,
    pub owner: Option<BindingId>,
}
#[derive(Debug, Clone)]
pub struct Reference {
    pub span: Span,
    pub binding: BindingId,
}
#[derive(Debug, Default)]
pub struct Resolution {
    pub bindings: Vec<Binding>,
    pub references: Vec<Reference>,
    pub declarations: BTreeMap<usize, BindingId>,
    pub dependencies: BTreeMap<BindingId, BTreeSet<BindingId>>,
    /// Defining module index of each top-level item and constructor.
    pub unit_of: BTreeMap<BindingId, usize>,
    /// Defining module index of every top-level item by source span start,
    /// including items such as impls that have no binding of their own.
    pub item_units: BTreeMap<usize, usize>,
    pub public: BTreeSet<BindingId>,
    /// Module paths, root first.
    pub units: Vec<Vec<String>>,
    /// Generic binders declared `<e: Effects>`. Effect rows are a compile-time
    /// category separate from types, grades, and natural const parameters.
    pub effect_binders: BTreeSet<BindingId>,
    /// The lexically visible Option declaration for each Slice.try_get call.
    pub slice_options: BTreeMap<(usize, usize), BindingId>,
    /// Declared named effect rows, keyed by their binding. The stored effect
    /// list is resolved but not expanded; [`crate::runtime_types::effect_row_term`]
    /// expands aliases (and rejects cycles) when a row is evaluated.
    pub effect_rows: BTreeMap<BindingId, Vec<Type>>,
    /// Impl method function binding, keyed by the method declaration's start
    /// offset. Methods are not name-resolvable at module scope; they are reached
    /// only by receiver-type dispatch or the explicit `receiver.Trait.method`
    /// spelling.
    pub method_bindings: BTreeMap<usize, BindingId>,
    /// Declared finite grade algebras, keyed by their source name. Grade
    /// annotations use `Algebra.Element`; see [the grade documentation].
    pub algebras: BTreeMap<String, GradeAlgebraDecl>,
    /// Lowered, law-checked algebra tables used while evaluating annotations.
    pub(crate) lowered_algebras: BTreeMap<String, std::sync::Arc<crate::grades::Algebra>>,
    /// Concrete rows bits for declared effect operations. A declared
    /// `effect Op: P -> R;` also names an effect row entry, so `! {Op}` is
    /// checked like the built-in `io`/`alloc`/`suspend`/`panic` vocabulary.
    /// Built-ins occupy bits 0..4; declared effects take the following bits in
    /// declaration order.
    pub effect_bits: BTreeMap<String, u16>,
    /// Traits named in a multi-trait object type `dyn A + B` anywhere in the
    /// program. They always use the dynamic object representation.
    pub multi_object_traits: BTreeSet<BindingId>,
    references_by_span: BTreeMap<(usize, usize), BindingId>,
    binders_by_span: BTreeMap<(usize, usize), BindingId>,
}
impl Resolution {
    pub fn reference(&self, span: Span) -> Option<BindingId> {
        self.references_by_span
            .get(&(span.start, span.end))
            .copied()
    }
    pub fn binder(&self, span: Span) -> Option<BindingId> {
        self.binders_by_span.get(&(span.start, span.end)).copied()
    }
    /// The function binding of an impl method declaration, by its start offset.
    pub fn method(&self, span: Span) -> Option<BindingId> {
        self.method_bindings.get(&span.start).copied()
    }
    /// Allocate a compiler-synthesized function binding for one inherited
    /// default trait method materialized for a concrete impl. These bindings
    /// are not name-resolvable and are not keyed by a source span: one trait
    /// default may be materialized for several impl targets, each with its own
    /// `Self` and trait-argument specialization.
    pub fn synthesize_method(
        &mut self,
        name: &str,
        span: Span,
        unit: usize,
        public: bool,
    ) -> BindingId {
        let id = self.bindings.len();
        self.bindings.push(Binding {
            name: name.to_owned(),
            kind: BindingKind::Function,
            span,
            owner: None,
        });
        self.unit_of.insert(id, unit);
        if public {
            self.public.insert(id);
        }
        id
    }
}
type Result<T> = std::result::Result<T, Diagnostic>;

/// Resolve one standalone file. `use` requires [`resolve_program`].
pub fn resolve(module: &Module) -> Result<Resolution> {
    let imports = BTreeMap::new();
    Resolver::new().run(
        &module.items,
        &[UnitInfo {
            items: 0..module.items.len(),
            imports: &imports,
        }],
    )
}
/// Resolve every module of a loaded program into one binding table.
pub fn resolve_program(program: &Program) -> Result<Resolution> {
    let units = program
        .units
        .iter()
        .map(|u| UnitInfo {
            items: u.items.clone(),
            imports: &u.imports,
        })
        .collect::<Vec<_>>();
    Resolver::new().run(&program.module.items, &units)
}
struct UnitInfo<'a> {
    items: std::ops::Range<usize>,
    imports: &'a BTreeMap<usize, (usize, Option<String>)>,
}
#[derive(Default)]
struct Scope {
    path: Vec<String>,
    globals: BTreeMap<String, BindingId>,
    constructors: BTreeMap<String, Vec<BindingId>>,
    aliases: BTreeMap<String, usize>,
}
pub(crate) const BUILTIN_NAMES: &[&str] = &[
    "Type",
    "Prop",
    "Nat",
    "Int",
    "Bool",
    "Unit",
    "Never",
    "Char",
    "str",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "isize",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "usize",
    "f32",
    "f64",
    "io",
    "alloc",
    "suspend",
    "panic",
    "state",
    "Effects",
    "many",
    "Grade",
    "Eq",
    "refl",
    "Nat.zero",
    "Nat.succ",
    "print_i64",
    "print_int",
    "print_float",
    "Float",
    "Float.abs",
    "Float.sqrt",
    "Float.is_nan",
    "Float.is_infinite",
    "Float.is_finite",
    "Float.from_int",
    "Float.from_int_rounded",
    "Float.try_from_int",
    "Float.to_f64",
    "Float.try_to_f32",
    "Float.try_to_int",
    "Int",
    "Int.convert",
    "Int.try_convert",
    "Int.truncate",
    "Int.wrapping_add",
    "Int.wrapping_sub",
    "Int.wrapping_mul",
    "Int.saturating_add",
    "Int.saturating_sub",
    "Int.saturating_mul",
    "Int.checked_add",
    "Int.checked_sub",
    "Int.checked_mul",
    "Char.code",
    "Char.from_code",
    "i8.MIN",
    "i8.MAX",
    "i16.MIN",
    "i16.MAX",
    "i32.MIN",
    "i32.MAX",
    "i64.MIN",
    "i64.MAX",
    "u8.MIN",
    "u8.MAX",
    "u16.MIN",
    "u16.MAX",
    "u32.MIN",
    "u32.MAX",
    "u64.MIN",
    "u64.MAX",
    "Stdin",
    "Stdout",
    "IO",
    "IO.stdin",
    "IO.stdout",
    "IO.read_all",
    "IO.read_line",
    "IO.read_chunk",
    "IO.write",
    "FS",
    "FS.read",
    "FS.write",
    "FS.write_exclusive",
    "FS.append",
    "FS.remove",
    "FS.rename",
    "FS.mkdir",
    "FS.remove_dir",
    "FS.list",
    "FS.is_file",
    "FS.is_dir",
    "FS.size",
    "FS.exists",
    "FS.open",
    "FS.read_at",
    "FS.write_at",
    "FS.sync",
    "FS.truncate",
    "FS.file_size",
    "FS.close",
    "FS.sync_dir",
    "ENV",
    "ENV.arg_count",
    "ENV.arg",
    "ENV.var_count",
    "ENV.var",
    "TIME",
    "TIME.unix_seconds",
    "TIME.monotonic_ns",
    "TIME.sleep_ms",
    "PROC",
    "PROC.run",
    "NET",
    "NET.tcp_exchange",
    "OS",
    "OS.strerror",
    "Bytes",
    "Bytes.from",
    "Bytes.with_capacity",
    "Bytes.try_with_capacity",
    "Bytes.len",
    "Bytes.capacity",
    "Bytes.get",
    "Bytes.push",
    "Bytes.push_reserved",
    "Bytes.copy",
    "Bytes.clear",
    "Bytes.at",
    "String",
    "String.from",
    "String.from_utf8",
    "String.len",
    "String.scalar_len",
    "String.byte_at",
    "String.scalar_at",
    "String.as_bytes",
    "String.as_str",
    "String.as_mut_str",
    "String.substr",
    "String.bytes",
    "Str.len",
    "Str.scalar_len",
    "Str.byte_at",
    "Str.scalar_at",
    "Str.to_string",
    "Str.substr",
    "Str.make_ascii_uppercase",
    "Str.make_ascii_lowercase",
    "Str.set_scalar",
    "Vec",
    "Vec.new",
    "Vec.with_capacity",
    "Vec.len",
    "Vec.get",
    "Vec.push",
    "Vec.set",
    "Vec.pop",
    "Vec.at",
    "Vec.map_in_place",
    "Vec.map_chain_in_place",
    "Vec.map_in_place_grow",
    "Vec.map_chain_in_place_grow",
    "Vec.clear",
    "Vec.reserve",
    "Vec.try_reserve",
    "Slice.len",
    "Slice.get",
    "Slice.try_get",
    "Slice.at",
    "Slice.set",
    "Slice.split_at_mut",
    "DynArray",
    "DynArray.new",
    "DynArray.push",
    "DynArray.len",
    "DynArray.get",
    "DynArray.set",
    "DynArray.pop",
    "Array.fill",
    "Box",
    "Box.new",
    "Box.take",
    "Box.read",
    "Box.set",
    "Box.reuse",
    "Box.reuse_grow",
    "Box.try_new",
    "Box.try_reuse",
    "Arena",
    "Arena.new",
    "Arena.with_strategy",
    "Arena.alloc",
    "Arena.try_alloc",
    "ArenaBox",
    "ArenaBox.read",
    "ArenaBox.take",
    "Allocator",
    "Allocator.new",
    "Allocator.with_realloc",
    "AllocatorContext",
    "AllocatorContext.new",
    "AllocatorContext.share",
    "AllocBox",
    "AllocBox.new",
    "AllocBox.try_new",
    "AllocBox.read",
    "AllocBox.take",
    "AllocVec",
    "AllocVec.new",
    "AllocVec.with_capacity",
    "AllocVec.len",
    "AllocVec.get",
    "AllocVec.push",
    "AllocVec.try_push",
    "AllocVec.pop",
    "AllocVec.set",
    "AllocVec.clear",
    "Task",
    "Task.scope",
    "Task.spawn",
    "Task.yield",
    "Task.join",
    "Task.cancel",
    "Task.check_cancel",
    "drop",
    "Nat.induct",
    "Eq.transport",
    "Eq.elim",
    "Data.elim",
];

struct Resolver {
    result: Resolution,
    builtins: BTreeMap<String, BindingId>,
    units: Vec<Scope>,
    unit: usize,
    scopes: Vec<BTreeMap<String, BindingId>>,
    owner: Option<BindingId>,
    depth: usize,
    /// Names of declared associated constants. `Type.NAME` is treated as a
    /// projection only when `NAME` is one of these, so qualified constructors
    /// such as `Option.Some` keep their ordinary value meaning.
    associated_const_names: BTreeSet<String>,
    /// Names of declared associated types. `T.Item` is treated as a projection
    /// only when `Item` is one of these, so a qualified logical name such as
    /// `Nat.succ<N>` keeps its ordinary type meaning.
    associated_type_names: BTreeSet<String>,
}
impl Resolver {
    fn new() -> Self {
        let mut resolver = Self {
            result: Resolution::default(),
            builtins: BTreeMap::new(),
            units: Vec::new(),
            unit: 0,
            scopes: Vec::new(),
            owner: None,
            depth: 0,
            associated_const_names: BTreeSet::new(),
            associated_type_names: BTreeSet::new(),
        };
        // Primitive names only. Standard-library containers are not fabricated.
        for &name in BUILTIN_NAMES {
            let id = resolver.add(name.to_owned(), BindingKind::Builtin, Span::default(), None);
            resolver.builtins.insert(name.to_owned(), id);
        }
        resolver
    }
    fn add(
        &mut self,
        name: String,
        kind: BindingKind,
        span: Span,
        owner: Option<BindingId>,
    ) -> BindingId {
        let id = self.result.bindings.len();
        self.result.bindings.push(Binding {
            name,
            kind,
            span,
            owner,
        });
        id
    }
    fn global(&mut self, name: &str, kind: BindingKind, span: Span) -> Result<BindingId> {
        if self.units[self.unit].globals.contains_key(name) || self.builtins.contains_key(name) {
            return Err(Diagnostic::new(
                span,
                format!("duplicate or reserved declaration '{name}'"),
            ));
        }
        let id = self.add(name.to_owned(), kind, span, None);
        self.units[self.unit].globals.insert(name.to_owned(), id);
        self.result.unit_of.insert(id, self.unit);
        Ok(id)
    }
    fn local(
        &mut self,
        name: &str,
        kind: BindingKind,
        span: Span,
        shadow: bool,
    ) -> Result<BindingId> {
        if name == "_" {
            return Err(Diagnostic::new(
                span,
                "'_' cannot name a declaration; use a wildcard pattern",
            ));
        }
        if !shadow && self.scopes.last().is_some_and(|s| s.contains_key(name)) {
            return Err(Diagnostic::new(span, format!("duplicate binder '{name}'")));
        }
        let id = self.add(name.to_owned(), kind, span, self.owner);
        self.scopes
            .last_mut()
            .expect("internal scope")
            .insert(name.to_owned(), id);
        self.result
            .binders_by_span
            .insert((span.start, span.end), id);
        Ok(id)
    }
    /// A local or parameter named `name` in an enclosing scope: the
    /// candidate capability of `perform name(x)`. The checker decides whether
    /// it really is a capability.
    fn local_capability(&self, name: &str) -> Option<BindingId> {
        let id = self.scopes.iter().rev().find_map(|scope| scope.get(name))?;
        matches!(
            self.result.bindings[*id].kind,
            BindingKind::Local | BindingKind::Parameter
        )
        .then_some(*id)
    }
    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.scopes.push(BTreeMap::new());
        let result = f(self);
        self.scopes.pop();
        result
    }
    fn nested<T>(&mut self, span: Span, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth >= 128 {
            return Err(Diagnostic::new(
                span,
                "name-resolution nesting budget exceeded (128)",
            ));
        }
        self.depth += 1;
        let result = f(self);
        self.depth -= 1;
        result
    }
    fn lookup(&self, path: &[String], span: Span) -> Result<BindingId> {
        let scope = &self.units[self.unit];
        let path = if !scope.path.is_empty()
            && path.starts_with(&scope.path)
            && path.len() > scope.path.len()
        {
            &path[scope.path.len()..]
        } else {
            path
        };
        let name = path.join(".");
        if path.len() == 1 {
            for scope in self.scopes.iter().rev() {
                if let Some(id) = scope.get(&name) {
                    return Ok(*id);
                }
            }
        }
        if let Some(id) = scope.globals.get(&name) {
            return Ok(*id);
        }
        if path.len() >= 2
            && let Some(target) = scope.aliases.get(&path[0])
        {
            let rest = path[1..].join(".");
            let Some(id) = self.units[*target].globals.get(&rest) else {
                return Err(Diagnostic::new(
                    span,
                    format!("module '{}' has no item '{rest}'", path[0]),
                ));
            };
            if !self.result.public.contains(id) {
                return Err(Diagnostic::new(
                    span,
                    format!("'{rest}' is private to module '{}'; mark it 'pub'", path[0]),
                ));
            }
            return Ok(*id);
        }
        if let Some(id) = self.builtins.get(&name) {
            return Ok(*id);
        }
        if let (1, Some(ids)) = (path.len(), scope.constructors.get(&name)) {
            if ids.len() == 1 {
                return Ok(ids[0]);
            }
            return Err(Diagnostic::new(
                span,
                format!("ambiguous constructor '{name}'; qualify it with its enum name"),
            ));
        }
        Err(Diagnostic::new(span, format!("unknown name '{name}'")))
    }
    fn reference(&mut self, path: &[String], span: Span) -> Result<BindingId> {
        let id = self.lookup(path, span)?;
        self.record(id, span);
        Ok(id)
    }
    fn record(&mut self, id: BindingId, span: Span) {
        self.result.references.push(Reference { span, binding: id });
        self.result
            .references_by_span
            .insert((span.start, span.end), id);
        if let Some(owner) = self.owner {
            let target = &self.result.bindings[id];
            let dependency = match target.kind {
                BindingKind::Function | BindingKind::Data | BindingKind::Alias => Some(id),
                BindingKind::Trait => Some(id),
                BindingKind::Constructor => target.owner,
                _ => None,
            };
            if let Some(dependency) = dependency {
                self.result
                    .dependencies
                    .entry(owner)
                    .or_default()
                    .insert(dependency);
            }
        }
    }
    fn run(mut self, items: &[Declaration], units: &[UnitInfo]) -> Result<Resolution> {
        // Declared effect operations extend the finite effect-row vocabulary.
        // Four built-in bits are reserved, so the 16-bit row universe admits
        // twelve declared operations. Assignment follows source declaration
        // order across modules, which is also the order used for operation ids.
        for info in units {
            for declaration in &items[info.items.clone()] {
                if let ItemKind::Effect { name, .. } = &declaration.item.kind
                    && !self.result.effect_bits.contains_key(name)
                {
                    let bit = 1u16
                        .checked_shl(4u32 + self.result.effect_bits.len() as u32)
                        .unwrap_or(0);
                    if bit == 0 {
                        return Err(Diagnostic::new(
                            declaration.item.span,
                            "at most twelve declared effect operations are supported, because an effect row is a finite 16-bit set",
                        ));
                    }
                    self.result.effect_bits.insert(name.clone(), bit);
                }
            }
        }
        for info in units {
            for declaration in &items[info.items.clone()] {
                match &declaration.item.kind {
                    ItemKind::Trait { associated, .. } | ItemKind::Impl { associated, .. } => {
                        for item in associated {
                            match item {
                                Associated::Const { name, .. } => {
                                    self.associated_const_names.insert(name.clone());
                                }
                                Associated::Type { name, .. } => {
                                    self.associated_type_names.insert(name.clone());
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        // 1. Top-level declarations of every module.
        for (unit, info) in units.iter().enumerate() {
            self.unit = unit;
            self.units.push(Scope::default());
            for (index, declaration) in items[info.items.clone()].iter().enumerate() {
                let item = &declaration.item;
                self.result.item_units.insert(item.span.start, unit);
                let (name, kind) = match &item.kind {
                    ItemKind::Module(path) => {
                        if index != 0 || declaration.public || !declaration.attributes.is_empty() {
                            return Err(Diagnostic::new(
                                item.span,
                                "module header must occur first, without visibility or attributes",
                            ));
                        }
                        self.units[unit].path = path.clone();
                        continue;
                    }
                    ItemKind::Use(_) => continue,
                    ItemKind::Function(f) => (&f.name, BindingKind::Function),
                    ItemKind::Struct { name, .. } | ItemKind::Enum { name, .. } => {
                        (name, BindingKind::Data)
                    }
                    ItemKind::Prop { name, .. } => (name, BindingKind::Data),
                    ItemKind::Alias { name, .. } => (name, BindingKind::Alias),
                    ItemKind::Effect { name, .. } => (name, BindingKind::Effect),
                    ItemKind::EffectRow { name, .. } => (name, BindingKind::EffectRow),
                    ItemKind::Trait { name, .. } => (name, BindingKind::Trait),
                    ItemKind::GradeAlgebra(algebra) => (&algebra.name, BindingKind::GradeAlgebra),
                    ItemKind::Impl { methods, .. } => {
                        // Methods live in their owning impl, not in module scope.
                        // They still need stable function bindings for checking,
                        // specialization, and evaluation.
                        for method in methods {
                            let id = self.add(
                                format!("<impl method {}>", method.function.name),
                                BindingKind::Function,
                                method.span,
                                None,
                            );
                            self.result.unit_of.insert(id, unit);
                            if method.public {
                                self.result.public.insert(id);
                            }
                            self.result.method_bindings.insert(method.span.start, id);
                        }
                        continue;
                    }
                };
                let id = self.global(name, kind, item.span)?;
                // The allocator protocol is injected ahead of user items but
                // must be nameable from every module without an import.
                if matches!(&item.kind, ItemKind::Trait { name, .. } if name == "AllocatorProtocol")
                {
                    self.builtins.insert(name.clone(), id);
                }
                if declaration.public {
                    self.result.public.insert(id);
                }
                if let ItemKind::GradeAlgebra(algebra) = &item.kind {
                    let mut elements = Vec::new();
                    for element in &algebra.elements {
                        if elements.contains(&element.name) {
                            return Err(Diagnostic::new(
                                element.span,
                                format!(
                                    "duplicate element '{}' in grade algebra '{}'",
                                    element.name, algebra.name
                                ),
                            ));
                        }
                        elements.push(element.name.clone());
                    }
                    let name = algebra.name.clone();
                    let declaration = GradeAlgebraDecl {
                        name: name.clone(),
                        elements,
                        zero: algebra.zero.clone(),
                        one: algebra.one.clone(),
                        add: algebra.add.clone(),
                        mul: algebra.mul.clone(),
                        span: item.span,
                    };
                    if self
                        .result
                        .algebras
                        .insert(name.clone(), declaration)
                        .is_some()
                    {
                        return Err(Diagnostic::new(
                            item.span,
                            format!(
                                "duplicate grade algebra '{name}'; algebra names are program-global in this subset"
                            ),
                        ));
                    }
                }
                self.result.declarations.insert(item.span.start, id);
                // A trait method with a block is a default body. It needs a
                // stable function binding so that the resolver records the
                // body's dependencies under that owner. The executable checker
                // materializes one specialized copy per impl that inherits it.
                if let ItemKind::Trait { methods, .. } = &item.kind {
                    for method in methods
                        .iter()
                        .filter(|method| method.function.body.is_some())
                    {
                        let method_id = self.add(
                            format!("<trait default {}>", method.function.name),
                            BindingKind::Function,
                            method.span,
                            None,
                        );
                        self.result.unit_of.insert(method_id, unit);
                        self.result
                            .method_bindings
                            .insert(method.span.start, method_id);
                    }
                }
            }
        }
        self.result.units = self.units.iter().map(|u| u.path.clone()).collect();
        // 2. Constructors are public exactly when their enum is.
        for (unit, info) in units.iter().enumerate() {
            self.unit = unit;
            for declaration in &items[info.items.clone()] {
                if let ItemKind::Enum { name, variants, .. }
                | ItemKind::Prop { name, variants, .. } = &declaration.item.kind
                {
                    let owner = self.result.declarations[&declaration.item.span.start];
                    for variant in variants {
                        let qualified = format!("{name}.{}", variant.name);
                        let id = self.global(&qualified, BindingKind::Constructor, variant.span)?;
                        self.result.bindings[id].owner = Some(owner);
                        if declaration.public {
                            self.result.public.insert(id);
                        }
                        self.units[unit]
                            .constructors
                            .entry(variant.name.clone())
                            .or_default()
                            .push(id);
                    }
                }
            }
        }
        // 3. Imports, after every module's public surface is known.
        for (unit, info) in units.iter().enumerate() {
            for declaration in &items[info.items.clone()] {
                let ItemKind::Use(path) = &declaration.item.kind else {
                    continue;
                };
                let span = declaration.item.span;
                let Some((target, item)) = info.imports.get(&span.start) else {
                    return Err(Diagnostic::new(
                        span,
                        "imports need a loaded program; use 'kush check/run' on a file path",
                    ));
                };
                let local = item.clone().unwrap_or_else(|| path.last().unwrap().clone());
                if self.units[unit].globals.contains_key(&local)
                    || self.units[unit].aliases.contains_key(&local)
                {
                    return Err(Diagnostic::new(
                        span,
                        format!("import '{local}' conflicts with another declaration or import"),
                    ));
                }
                let Some(item) = item else {
                    self.units[unit].aliases.insert(local, *target);
                    continue;
                };
                let Some(&id) = self.units[*target].globals.get(item) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "module '{}' has no item '{item}'",
                            self.units[*target].path.join(".")
                        ),
                    ));
                };
                if !self.result.public.contains(&id) {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "'{item}' is private to module '{}'; mark it 'pub'",
                            self.units[*target].path.join(".")
                        ),
                    ));
                }
                self.units[unit].globals.insert(local.clone(), id);
                // Importing an enum imports its constructors, qualified and bare.
                let prefix = format!("{item}.");
                let constructors = self.units[*target]
                    .globals
                    .iter()
                    .filter(|(name, ctor)| {
                        name.starts_with(&prefix) && self.result.bindings[**ctor].owner == Some(id)
                    })
                    .map(|(name, ctor)| (name[prefix.len()..].to_owned(), *ctor))
                    .collect::<Vec<_>>();
                for (variant, ctor) in constructors {
                    self.units[unit]
                        .globals
                        .insert(format!("{local}.{variant}"), ctor);
                    self.units[unit]
                        .constructors
                        .entry(variant)
                        .or_default()
                        .push(ctor);
                }
            }
        }
        // 4. Bodies.
        for (unit, info) in units.iter().enumerate() {
            self.unit = unit;
            for declaration in &items[info.items.clone()] {
                let item = &declaration.item;
                self.owner = self.result.declarations.get(&item.span.start).copied();
                self.scoped(|r| match &item.kind {
                    ItemKind::Module(_) | ItemKind::Use(_) => Ok(()),
                    ItemKind::GradeAlgebra(_) => Ok(()),
                    ItemKind::Function(f) => r.function(f),
                    ItemKind::Trait {
                        generics,
                        associated,
                        methods,
                        ..
                    } => {
                        // Trait parameters are in scope while resolving every
                        // method signature and default body. A default body is
                        // owned by its trait method binding so its dependencies
                        // are audited; a signature has no body to resolve.
                        // Effect-exclusion constraints are a function-signature
                        // bound, so the trait's own parameters cannot carry one.
                        r.generics(
                            generics,
                            GenericContext::Unsupported("a trait declaration's parameters"),
                        )?;
                        for item in associated {
                            r.associated(item)?;
                        }
                        for method in methods {
                            let saved = r.owner;
                            if method.function.body.is_some() {
                                r.owner = r.result.method_bindings.get(&method.span.start).copied();
                            }
                            r.scoped(|r| r.function(&method.function))?;
                            r.owner = saved;
                        }
                        Ok(())
                    }
                    ItemKind::Impl {
                        generics,
                        trait_path,
                        self_ty,
                        associated,
                        methods,
                    } => {
                        r.generics(generics, GenericContext::Executable)?;
                        if let Some(trait_path) = trait_path {
                            r.ty(trait_path)?;
                        }
                        r.ty(self_ty)?;
                        for item in associated {
                            r.associated(item)?;
                        }
                        for method in methods {
                            let saved = r.owner;
                            r.owner = r.result.method_bindings.get(&method.span.start).copied();
                            r.scoped(|r| r.function(&method.function))?;
                            r.owner = saved;
                        }
                        Ok(())
                    }
                    ItemKind::Struct {
                        generics, fields, ..
                    } => {
                        r.generics(
                            generics,
                            GenericContext::Unsupported("a record declaration"),
                        )?;
                        r.fields(fields)
                    }
                    ItemKind::Enum {
                        generics, variants, ..
                    }
                    | ItemKind::Prop {
                        generics, variants, ..
                    } => {
                        r.generics(
                            generics,
                            GenericContext::Unsupported("a data or proposition declaration"),
                        )?;
                        for v in variants {
                            r.variant(v)?;
                        }
                        Ok(())
                    }
                    ItemKind::Alias { generics, ty, .. } => {
                        r.generics(generics, GenericContext::Unsupported("a type alias"))?;
                        r.ty(ty)
                    }
                    ItemKind::Effect {
                        parameter, result, ..
                    } => {
                        r.ty(parameter)?;
                        r.ty(result)
                    }
                    ItemKind::EffectRow { effects, .. } => {
                        for effect in effects {
                            r.ty(effect)?;
                        }
                        if let Some(owner) = r.owner {
                            r.result.effect_rows.insert(owner, effects.clone());
                        }
                        Ok(())
                    }
                })?;
            }
        }
        Ok(self.result)
    }
    /// Resolve one function-like declaration: generics, signature, and an
    /// optional body. Used by top-level functions, trait method signatures, and
    /// impl method bodies.
    fn function(&mut self, f: &Function) -> Result<()> {
        // Only executable functions and methods may constrain their effect-row
        // specialization. A total logical definition is erased from runtime IR,
        // so silently ignoring a constraint there would erase a checked promise.
        self.generics(
            &f.generics,
            if f.total {
                GenericContext::Unsupported("a total logical function")
            } else {
                GenericContext::Executable
            },
        )?;
        for p in &f.parameters {
            self.ty(&p.ty)?;
            self.local(&p.name, BindingKind::Parameter, p.span, false)?;
        }
        self.ty(&f.result)?;
        for effect in &f.effects {
            self.ty(effect)?;
        }
        // Postconditions see the parameters, `result`, and their binders.
        for clause in &f.ensures {
            self.scoped(|r| {
                r.local("result", BindingKind::Local, clause.result_span, true)?;
                if let EnsuresGuard::Variant {
                    subject, binders, ..
                } = &clause.guard
                {
                    if let Some(subject) = subject {
                        r.expr(subject)?;
                    }
                    for (name, span) in binders {
                        r.local(name, BindingKind::Local, *span, false)?;
                    }
                }
                r.expr(&clause.body)
            })?;
        }
        // The termination measure sees the parameters.
        if let Some(measure) = &f.decreases {
            self.scoped(|r| r.expr(measure))?;
        }
        if let Some(body) = &f.body {
            self.block(body)?;
        }
        Ok(())
    }
    fn generics(&mut self, generics: &[Generic], context: GenericContext) -> Result<()> {
        for generic in generics {
            let mut effect = false;
            if let Some(bound) = &generic.bound {
                self.ty(bound)?;
                effect = self.result.reference(bound.span).is_some_and(|id| {
                    self.result.bindings[id].kind == BindingKind::Builtin
                        && self.result.bindings[id].name == "Effects"
                });
            }
            if let Some(includes) = &generic.includes {
                if let GenericContext::Unsupported(what) = context {
                    return Err(Diagnostic::new(
                        generic.span,
                        format!(
                            "effect-row inclusion bounds are only supported on executable function and method effect binders; {what} cannot constrain an effect row"
                        ),
                    ));
                }
                if !effect {
                    return Err(Diagnostic::new(
                        generic.span,
                        format!(
                            "effect-row inclusion bounds require an effect-row binder such as '<{}: Effects + io>'; the bound here is not 'Effects'",
                            generic.name
                        ),
                    ));
                }
                self.ty(includes)?;
                self.effect_exclusions(includes)?;
            }
            if let Some(excludes) = &generic.excludes {
                if let GenericContext::Unsupported(what) = context {
                    return Err(Diagnostic::new(
                        generic.span,
                        format!(
                            "effect-exclusion constraints are only supported on executable function and method effect binders; {what} cannot constrain an effect row"
                        ),
                    ));
                }
                if !effect {
                    return Err(Diagnostic::new(
                        generic.span,
                        format!(
                            "effect exclusions require an effect-row binder such as '<{}: Effects - alloc>'; the bound here is not 'Effects'",
                            generic.name
                        ),
                    ));
                }
                self.ty(excludes)?;
                self.effect_exclusions(excludes)?;
            }
            if generic.includes.is_some() && generic.excludes.is_some() {
                let included =
                    crate::runtime_types::effect_includes(&self.result, generic)?.unwrap_or(0);
                let excluded =
                    crate::runtime_types::effect_excludes(&self.result, generic)?.unwrap_or(0);
                let overlap = included & excluded;
                if overlap != 0 {
                    return Err(Diagnostic::new(
                        generic.span,
                        format!(
                            "effect-row bound on '{}' both includes and excludes the same effects; an effect cannot be required and forbidden in one binder",
                            generic.name
                        ),
                    ));
                }
            }
            let id = self.local(&generic.name, BindingKind::Generic, generic.span, false)?;
            if effect {
                self.result.effect_binders.insert(id);
            }
        }
        Ok(())
    }
    /// Validate the right-hand side of an effect-exclusion binder. The type was
    /// already resolved, so this only checks its shape and that every leaf names
    /// a concrete supported effect. Effect variables and ordinary types are
    /// deliberately rejected: exclusions cannot themselves be polymorphic.
    fn effect_exclusions(&self, ty: &Type) -> Result<()> {
        match &ty.kind {
            TypeKind::Binary {
                op: crate::lexer::Kind::Pipe,
                left,
                right,
            } => {
                self.effect_exclusions(left)?;
                self.effect_exclusions(right)
            }
            TypeKind::Named { arguments, .. } => {
                if !arguments.is_empty() {
                    return Err(Diagnostic::new(
                        ty.span,
                        "an effect exclusion names a concrete effect and takes no arguments",
                    ));
                }
                let Some(id) = self.result.reference(ty.span) else {
                    return Err(Diagnostic::new(
                        ty.span,
                        "an effect exclusion must name one of the concrete effects 'io', 'alloc', 'suspend', or 'panic'",
                    ));
                };
                let binding = &self.result.bindings[id];
                let concrete = (binding.kind == BindingKind::Builtin
                    && matches!(binding.name.as_str(), "io" | "alloc" | "suspend" | "panic"))
                    || binding.kind == BindingKind::Effect;
                if !concrete {
                    return Err(Diagnostic::new(
                        ty.span,
                        format!(
                            "'{}' is not a concrete effect; excluding an effect variable or an ordinary type is not supported",
                            binding.name
                        ),
                    ));
                }
                Ok(())
            }
            _ => Err(Diagnostic::new(
                ty.span,
                "effect exclusions must be concrete effect names or a '|' union of them, as in '<e: Effects - (alloc | suspend)>'",
            )),
        }
    }
    fn fields(&mut self, fields: &[Field]) -> Result<()> {
        let mut seen = BTreeSet::new();
        for field in fields {
            if !seen.insert(&field.name) {
                return Err(Diagnostic::new(
                    field.span,
                    format!("duplicate field '{}'", field.name),
                ));
            }
            self.ty(&field.ty)?;
        }
        Ok(())
    }
    /// Resolve one enum/variant constructor. Constructor-local binders and named
    /// logical fields live in their own scope, so they cannot leak into another
    /// constructor or the surrounding declaration.
    fn variant(&mut self, variant: &Variant) -> Result<()> {
        self.scoped(|r| {
            r.generics(
                &variant.locals,
                GenericContext::Unsupported("a data constructor binder"),
            )?;
            match &variant.payload {
                Payload::Unit => {}
                Payload::Tuple(types) => {
                    for ty in types {
                        r.ty(ty)?;
                    }
                }
                Payload::Fields(fields) => r.named_fields(fields)?,
                Payload::Record(fields) => r.fields(fields)?,
            }
            if let Some(result) = &variant.result {
                r.ty(result)?;
            }
            Ok(())
        })
    }
    /// Named constructor fields bind sequentially: a later field type and the
    /// result indices may mention an earlier field.
    fn named_fields(&mut self, fields: &[Field]) -> Result<()> {
        let mut seen = BTreeSet::new();
        for field in fields {
            if !seen.insert(&field.name) {
                return Err(Diagnostic::new(
                    field.span,
                    format!("duplicate constructor field '{}'", field.name),
                ));
            }
            self.ty(&field.ty)?;
            self.local(&field.name, BindingKind::Parameter, field.span, false)?;
        }
        Ok(())
    }
    /// Resolve one associated item of a trait or impl. Type values and constant
    /// types are ordinary type syntax. A default constant expression is checked
    /// in the declaration's module and may name `Self`-projected constants,
    /// which the executable checker substitutes for the concrete impl.
    fn associated(&mut self, item: &Associated) -> Result<()> {
        match item {
            Associated::Type {
                value: Some(value), ..
            } => self.ty(value),
            Associated::Type { .. } => Ok(()),
            Associated::Const { ty, value, .. } => {
                self.ty(ty)?;
                if let Some(value) = value {
                    self.expr(value)?;
                }
                Ok(())
            }
        }
    }
    fn ty(&mut self, ty: &Type) -> Result<()> {
        self.nested(ty.span, |r| {
            match &ty.kind {
                TypeKind::Named { path, arguments } => {
                    // Associated type projections are not module paths:
                    // `Self::Item` is resolved against the impl that supplies
                    // the value, and `T::Item` against the trait bound of the
                    // generic parameter `T`. Record the base binding so the
                    // executable checker can normalize the projection.
                    if path.len() == 2
                        && (path[0] == "Self" || r.associated_type_names.contains(&path[1]))
                    {
                        if path[0] != "Self"
                            && let Ok(base) = r.lookup(std::slice::from_ref(&path[0]), ty.span)
                            && matches!(
                                r.result.bindings[base].kind,
                                BindingKind::Generic | BindingKind::Parameter
                            )
                        {
                            r.record(base, ty.span);
                        }
                        for argument in arguments {
                            r.ty(argument)?;
                        }
                        return Ok(());
                    }
                    r.reference(path, ty.span)?;
                    for argument in arguments {
                        r.ty(argument)?;
                    }
                }
                TypeKind::Integer(_) => {}
                TypeKind::Bool(_) => {}
                // Erased lifetime arguments are not value bindings. The
                // executable checker validates them against the declaration.
                TypeKind::Lifetime(_) => {}
                // `Self` is not a binding. It is substituted by the concrete
                // impl target before runtime type lowering.
                TypeKind::SelfType | TypeKind::Infer => {}
                TypeKind::Capability { effects, .. } => {
                    for effect in effects {
                        r.ty(effect)?;
                    }
                }
                TypeKind::Dyn(bounds) => {
                    for inner in crate::ast::dyn_types(bounds) {
                        r.ty(inner)?;
                    }
                    if bounds.len() > 1 {
                        for bound in bounds {
                            if let Some(id) = r.result.reference(bound.trait_ref.span) {
                                r.result.multi_object_traits.insert(id);
                            }
                        }
                    }
                }
                TypeKind::Tuple(types) => {
                    for ty in types {
                        r.ty(ty)?;
                    }
                }
                TypeKind::Slice(inner) | TypeKind::Borrow { inner, .. } => r.ty(inner)?,
                TypeKind::Array(inner, length) => {
                    r.ty(inner)?;
                    r.length(length)?;
                }
                TypeKind::Function {
                    parameters,
                    result,
                    effects,
                    ..
                } => {
                    r.scoped(|r| {
                        for parameter in parameters {
                            r.ty(&parameter.ty)?;
                            if let Some(name) = &parameter.name {
                                r.local(name, BindingKind::Parameter, parameter.span, false)?;
                            }
                        }
                        r.ty(result)?;
                        for ty in effects {
                            r.ty(ty)?;
                        }
                        Ok(())
                    })?;
                }
                TypeKind::Binary { left, right, .. } => {
                    r.ty(left)?;
                    r.ty(right)?;
                }
                TypeKind::Graded { inner, grade } => {
                    r.ty(inner)?;
                    // Grade expressions may name `Algebra.Element` and use
                    // arithmetic. Resolve ordinary grade variables where
                    // possible but leave algebra paths to the grade pass.
                    r.length(grade)?;
                }
                TypeKind::Structural { fields, row, .. } => {
                    for field in fields {
                        r.ty(&field.ty)?;
                    }
                    if let Some(row) = row {
                        r.ty(row)?;
                    }
                }
                TypeKind::Predicate(proposition) => r.expr(proposition)?,
            }
            Ok(())
        })
    }
    /// Resolve names inside a compile-time array-length expression. Unknown
    /// names are left for the evaluator so that diagnostics keep one clear
    /// "not a compile-time expression" message instead of a premature
    /// unknown-name error. Resolvable names still record references and
    /// dependencies, which is what const-parameter substitution and the
    /// logical dependency audit need.
    fn length(&mut self, ty: &Type) -> Result<()> {
        self.nested(ty.span, |r| {
            match &ty.kind {
                TypeKind::Named { path, arguments } => {
                    let _ = r.reference(path, ty.span);
                    for argument in arguments {
                        r.length(argument)?;
                    }
                }
                TypeKind::Binary { left, right, .. } => {
                    r.length(left)?;
                    r.length(right)?;
                }
                TypeKind::Integer(_) => {}
                TypeKind::Bool(_) => {}
                _ => {}
            }
            Ok(())
        })
    }
    fn block(&mut self, block: &Block) -> Result<()> {
        self.nested(block.span, |r| {
            r.scoped(|r| {
                for statement in &block.statements {
                    match statement {
                        Statement::Let {
                            pattern, ty, value, ..
                        } => {
                            if let Some(ty) = ty {
                                r.ty(ty)?;
                            }
                            r.expr(value)?; // initializer cannot see its new binding
                            r.bind_pattern(pattern, true)?;
                        }
                        Statement::Expr(expr) => r.expr(expr)?,
                    }
                }
                if let Some(tail) = &block.tail {
                    r.expr(tail)?;
                }
                Ok(())
            })
        })
    }
    fn expression_path(expr: &Expr) -> Option<Vec<String>> {
        let mut parts = Vec::new();
        let mut current = expr;
        loop {
            if parts.len() >= 128 {
                return None;
            }
            match &current.kind {
                ExprKind::Name(name) => {
                    parts.push(name.clone());
                    parts.reverse();
                    return Some(parts);
                }
                ExprKind::Field { value, name } => {
                    parts.push(name.clone());
                    current = value;
                }
                _ => return None,
            }
        }
    }
    fn expr(&mut self, expr: &Expr) -> Result<()> {
        self.nested(expr.span, |r| {
            match &expr.kind {
                // '_' as an expression is a proof hole for an erased argument.
                ExprKind::Name(name) if name == "_" => {}
                ExprKind::Name(name) => {
                    r.reference(std::slice::from_ref(name), expr.span)?;
                }
                ExprKind::Record { ty, fields, base } => {
                    r.expr(ty)?;
                    let mut seen = BTreeSet::new();
                    for (name, value) in fields {
                        if !seen.insert(name) {
                            return Err(Diagnostic::new(
                                value.span,
                                format!("duplicate record field '{name}'"),
                            ));
                        }
                        r.expr(value)?;
                    }
                    if let Some(base) = base {
                        r.expr(base)?;
                    }
                }
                ExprKind::StructuralLiteral(fields) => {
                    let mut seen = BTreeSet::new();
                    for (name, value) in fields {
                        if !seen.insert(name) {
                            return Err(Diagnostic::new(
                                value.span,
                                format!("duplicate structural record field '{name}'"),
                            ));
                        }
                        r.expr(value)?;
                    }
                }
                ExprKind::Is { value, .. } => r.expr(value)?,
                ExprKind::Cast { value, ty } => {
                    r.ty(ty)?;
                    r.expr(value)?;
                }
                ExprKind::While { condition, body } => {
                    r.expr(condition)?;
                    r.block(body)?;
                }
                ExprKind::Loop(body) => r.block(body)?,
                ExprKind::Break(value) => {
                    if let Some(value) = value {
                        r.expr(value)?;
                    }
                }
                ExprKind::Continue => {}
                ExprKind::Integer(_)
                | ExprKind::Float(_)
                | ExprKind::String(_)
                | ExprKind::Char(_)
                | ExprKind::Bool(_) => {}
                ExprKind::Tuple(values) | ExprKind::Array(values) => {
                    for value in values {
                        r.expr(value)?;
                    }
                }
                ExprKind::Lambda(lambda) => {
                    r.scoped(|r| {
                        for parameter in &lambda.parameters {
                            r.ty(&parameter.ty)?;
                            r.local(
                                &parameter.name,
                                BindingKind::Parameter,
                                parameter.span,
                                false,
                            )?;
                        }
                        r.ty(&lambda.result)?;
                        for effect in &lambda.effects {
                            r.ty(effect)?;
                        }
                        r.block(&lambda.body)
                    })?;
                }
                ExprKind::Block(block) => r.block(block)?,
                ExprKind::Handle {
                    parameter,
                    result,
                    handler,
                    body,
                    capability,
                    operation: _,
                } => {
                    r.ty(parameter)?;
                    r.ty(result)?;
                    r.expr(handler)?;
                    match capability {
                        Some((name, span)) => r.scoped(|r| {
                            r.local(name, BindingKind::Local, *span, false)?;
                            r.block(body)
                        })?,
                        None => r.block(body)?,
                    }
                }
                ExprKind::Perform { value, operation } => {
                    // `perform op(x)` through a capability binding in scope:
                    // the perform expression's span refers to that binding.
                    if let Some(id) = r.local_capability(operation) {
                        r.result.references.push(Reference {
                            span: expr.span,
                            binding: id,
                        });
                        r.result
                            .references_by_span
                            .insert((expr.span.start, expr.span.end), id);
                    }
                    r.expr(value)?
                }
                ExprKind::Unary { operand, .. } | ExprKind::Try(operand) => r.expr(operand)?,
                ExprKind::Binary { left, right, .. } => {
                    r.expr(left)?;
                    r.expr(right)?;
                }
                ExprKind::Call { callee, arguments } => {
                    r.expr(callee)?;
                    let target = match &callee.kind {
                        ExprKind::Specialize { callee, .. } => callee.as_ref(),
                        _ => callee.as_ref(),
                    };
                    let named_option = r.result.reference(target.span).is_some_and(|id| {
                        let binding = &r.result.bindings[id];
                        binding.kind == BindingKind::Builtin
                            && matches!(
                                binding.name.as_str(),
                                "Slice.try_get"
                                    | "String.scalar_at"
                                    | "Str.scalar_at"
                                    | "Int.try_convert"
                                    | "Int.checked_add"
                                    | "Int.checked_sub"
                                    | "Int.checked_mul"
                                    | "Char.from_code"
                                    | "Float.try_from_int"
                                    | "Float.try_to_f32"
                                    | "Float.try_to_int"
                            )
                    });
                    // Method-call syntax resolves the receiver by type only in
                    // the executable checker. Record an in-scope Option here for
                    // the method names that may need one; a non-matching
                    // receiver is diagnosed later with a precise message.
                    let method_option = matches!(
                        &target.kind,
                        ExprKind::Field { name, .. }
                            if matches!(
                                name.as_str(),
                                "try_get"
                                    | "scalar_at"
                                    | "try_convert"
                                    | "checked_add"
                                    | "checked_sub"
                                    | "checked_mul"
                                    | "try_from_int"
                                    | "try_to_f32"
                                    | "try_to_int"
                            )
                    );
                    if named_option || method_option {
                        let option = r.lookup(&["Option".to_string()], expr.span);
                        if named_option {
                            let option = option.map_err(|_| {
                                Diagnostic::new(expr.span,
                                    "this operation returns Option<T> and requires enum Option<T> { None, Some(T) } in scope; import std.option.Option or declare it here")
                            })?;
                            r.result.slice_options.insert((expr.span.start, expr.span.end), option);
                            if let Some(owner) = r.owner {
                                r.result.dependencies.entry(owner).or_default().insert(option);
                            }
                        } else if let Ok(option) = option {
                            r.result.slice_options.insert((expr.span.start, expr.span.end), option);
                            if let Some(owner) = r.owner {
                                r.result.dependencies.entry(owner).or_default().insert(option);
                            }
                        }
                    }
                    for arg in arguments {
                        r.expr(arg)?;
                    }
                }
                ExprKind::Specialize { callee, arguments } => {
                    // `receiver.Trait::<Arguments>.method(...)` explicitly
                    // qualifies a generic trait specialization. Record the
                    // trait binding on the `receiver.Trait` selector so the
                    // checker can lower the call without re-resolving modules.
                    if let ExprKind::Field {
                        value: receiver,
                        name: trait_name,
                    } = &callee.kind
                        && let Ok(trait_id) =
                            r.lookup(std::slice::from_ref(trait_name), callee.span)
                        && r.result.bindings[trait_id].kind == BindingKind::Trait
                    {
                        r.record(trait_id, callee.span);
                        r.expr(receiver)?;
                        for arg in arguments {
                            r.ty(arg)?;
                        }
                        return Ok(());
                    }
                    r.expr(callee)?;
                    for arg in arguments {
                        r.ty(arg)?;
                    }
                }
                ExprKind::Field { value, name: _ } => {
                    // `Self.NAME` names an associated constant of the
                    // enclosing trait or impl. It is substituted for the
                    // concrete impl before execution and is never a runtime
                    // field access.
                    if matches!(&value.kind, ExprKind::Name(root) if root == "Self") {
                        return Ok(());
                    }
                    // `Type.NAME` names an associated constant when `Type` is
                    // a nominal declaration (or an inherent constant target)
                    // and no value of that qualified path exists. Record the
                    // type binding so the checker can project the constant.
                    if let Some(path) = Self::expression_path(expr)
                        && path.len() == 2
                        && r.associated_const_names.contains(&path[1])
                        && let Ok(base) = r.lookup(std::slice::from_ref(&path[0]), expr.span)
                        && matches!(
                            r.result.bindings[base].kind,
                            BindingKind::Data | BindingKind::Generic | BindingKind::Parameter
                        )
                    {
                        r.record(base, expr.span);
                        return Ok(());
                    }
                    // `receiver.Trait.method(...)` is the explicit spelling for
                    // a statically dispatched trait method. Record the trait
                    // reference on the `receiver.Trait` node so the checker can
                    // use it without re-parsing module scope.
                    if let ExprKind::Field {
                        value: receiver,
                        name: trait_name,
                    } = &value.kind
                        && let Ok(trait_id) =
                            r.lookup(std::slice::from_ref(trait_name), value.span)
                        && r.result.bindings[trait_id].kind == BindingKind::Trait
                    {
                        r.record(trait_id, value.span);
                        r.expr(receiver)?;
                        return Ok(());
                    }
                    if let Some(path) = Self::expression_path(expr) {
                        let local_root = r.scopes.iter().rev().any(|s| s.contains_key(&path[0]));
                        let module_root =
                            !local_root && r.units[r.unit].aliases.contains_key(&path[0]);
                        if module_root || (!local_root && r.lookup(&path, expr.span).is_ok()) {
                            r.reference(&path, expr.span)?;
                        } else {
                            // `Token.Live.method` on a nullary constructor:
                            // the prefix before the method name is itself a
                            // resolvable value path. Keep rejecting shorter
                            // unknown qualified type names such as `Point.miss`.
                            let value_path = &path[..path.len() - 1];
                            let method_prefix = path.len() >= 3
                                && r.lookup(value_path, expr.span).is_ok();
                            if !method_prefix
                                && let (false, Ok(root)) =
                                    (local_root, r.lookup(&path[..1], expr.span))
                            {
                                let binding = &r.result.bindings[root];
                                if binding.kind == BindingKind::Data
                                    || (binding.kind == BindingKind::Builtin
                                        && binding.name == "Nat")
                                {
                                    return Err(Diagnostic::new(
                                        expr.span,
                                        format!("unknown qualified name '{}'", path.join(".")),
                                    ));
                                }
                            }
                            r.expr(value)?;
                        }
                    } else {
                        r.expr(value)?;
                    }
                }
                ExprKind::Index { value, index } => {
                    r.expr(value)?;
                    r.expr(index)?;
                }
                ExprKind::Slice { value, start, end } => {
                    r.expr(value)?;
                    if let Some(start) = start {
                        r.expr(start)?;
                    }
                    if let Some(end) = end {
                        r.expr(end)?;
                    }
                }
                ExprKind::Return(value) => {
                    if let Some(value) = value {
                        r.expr(value)?;
                    }
                }
                ExprKind::If {
                    condition,
                    then,
                    otherwise,
                } => {
                    r.expr(condition)?;
                    r.block(then)?;
                    if let Some(otherwise) = otherwise {
                        r.expr(otherwise)?;
                    }
                }
                ExprKind::Match { value, arms } => {
                    r.expr(value)?;
                    for arm in arms {
                        r.scoped(|r| {
                            r.bind_pattern(&arm.pattern, false)?;
                            if let Some(guard) = &arm.guard {
                                r.expr(guard)?;
                            }
                            r.expr(&arm.body)
                        })?;
                    }
                }
            }
            Ok(())
        })
    }
    fn bind_pattern(&mut self, pattern: &Pattern, shadow: bool) -> Result<()> {
        let mut names = BTreeMap::new();
        self.pattern(pattern, &mut names)?;
        for (name, span) in names {
            self.local(&name, BindingKind::Local, span, shadow)?;
        }
        Ok(())
    }
    fn pattern(&mut self, pattern: &Pattern, names: &mut BTreeMap<String, Span>) -> Result<()> {
        self.nested(pattern.span, |r| {
            match &pattern.kind {
                PatternKind::Rest(name) => {
                    if let Some(name) = name
                        && names.insert(name.clone(), pattern.span).is_some()
                    {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!("duplicate pattern binding '{name}'"),
                        ));
                    }
                }
                PatternKind::Name(path) if path.len() == 1 => {
                    // Constructor aliases win in patterns. Otherwise a single name binds.
                    if r.units[r.unit].constructors.contains_key(&path[0]) {
                        let id = r.reference(path, pattern.span)?;
                        if r.result.bindings[id].kind != BindingKind::Constructor {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "constructor pattern is shadowed; use its qualified name",
                            ));
                        }
                    } else if names.insert(path[0].clone(), pattern.span).is_some() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!("duplicate pattern binding '{}'", path[0]),
                        ));
                    }
                }
                PatternKind::Name(path)
                | PatternKind::Constructor { path, .. }
                | PatternKind::Record { path, .. } => {
                    let id = r.reference(path, pattern.span)?;
                    if !matches!(
                        r.result.bindings[id].kind,
                        BindingKind::Constructor | BindingKind::Data
                    ) {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "expected a data constructor or record in pattern",
                        ));
                    }
                    match &pattern.kind {
                        PatternKind::Constructor { fields, .. } => {
                            for p in fields {
                                r.pattern(p, names)?;
                            }
                        }
                        PatternKind::Record { fields, .. } => {
                            let mut seen = BTreeSet::new();
                            for (field, p) in fields {
                                if !seen.insert(field) {
                                    return Err(Diagnostic::new(
                                        p.span,
                                        format!("duplicate pattern field '{field}'"),
                                    ));
                                }
                                r.pattern(p, names)?;
                            }
                        }
                        _ => {}
                    }
                }
                PatternKind::Structural { fields, .. } => {
                    let mut seen = BTreeSet::new();
                    for (field, p) in fields {
                        if !seen.insert(field) {
                            return Err(Diagnostic::new(
                                p.span,
                                format!("duplicate structural pattern field '{field}'"),
                            ));
                        }
                        r.pattern(p, names)?;
                    }
                }
                PatternKind::Tuple(patterns) | PatternKind::Slice(patterns) => {
                    for p in patterns {
                        r.pattern(p, names)?;
                    }
                }
                PatternKind::Type { ty, inner } => {
                    r.ty(ty)?;
                    r.pattern(inner, names)?;
                }
                PatternKind::Or(alternatives) => {
                    let mut first: Option<BTreeMap<String, Span>> = None;
                    for alternative in alternatives {
                        let mut branch = BTreeMap::new();
                        r.pattern(alternative, &mut branch)?;
                        if first
                            .as_ref()
                            .is_some_and(|first| !first.keys().eq(branch.keys()))
                        {
                            return Err(Diagnostic::new(
                                alternative.span,
                                "pattern alternatives must bind the same names",
                            ));
                        }
                        if first.is_none() {
                            first = Some(branch);
                        }
                    }
                    for (name, span) in first.unwrap_or_default() {
                        if names.insert(name.clone(), span).is_some() {
                            return Err(Diagnostic::new(
                                span,
                                format!("duplicate pattern binding '{name}'"),
                            ));
                        }
                    }
                }
                _ => {}
            }
            Ok(())
        })
    }
}
