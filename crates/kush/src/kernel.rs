//! Small explicitly typed logical kernel. No surface syntax or name-resolution
//! information is trusted here. Global definitions are admitted only after checking.
use crate::natural::Natural;
use std::{collections::BTreeMap, fmt};

/// An admitted machine carrier available to the logical kernel.
///
/// These carrier *types* and their canonical literals are checked symbolic
/// values. The kernel deliberately provides no arithmetic, casts, elimination,
/// or runtime coercion for them: a runtime function call is never reduced and
/// cannot be smuggled in as a total operation. Their only logical structure is
/// equality and occurrence in dependent indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scalar {
    I64,
    Bool,
    Unit,
}
impl Scalar {
    pub fn name(self) -> &'static str {
        match self {
            Self::I64 => "i64",
            Self::Bool => "Bool",
            Self::Unit => "Unit",
        }
    }
}

/// A canonical machine literal. `I64` stores the checked signed value, so an
/// out-of-range source literal cannot be represented at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarValue {
    I64(i64),
    Bool(bool),
    Unit,
}
impl ScalarValue {
    pub fn scalar(self) -> Scalar {
        match self {
            Self::I64(_) => Scalar::I64,
            Self::Bool(_) => Scalar::Bool,
            Self::Unit => Scalar::Unit,
        }
    }
}

/// A universe level in canonical form: `max(constant, u_i + offset_i, ...)`.
///
/// Levels are built from constants, level parameters (`Param(i)`, bound by
/// the enclosing universe-polymorphic declaration), successor and binary
/// maximum. This fragment has a unique normal form: each parameter keeps its
/// largest offset, and the constant is dropped (stored as 0) when some
/// parameter offset already dominates it, since parameters are never negative.
/// Structural equality is therefore level equality, and `a <= b` holds for
/// every assignment exactly when `max(a, b) == b`. There is no `imax`: `Prop`
/// is a separate sort, never `Universe(l)`.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct Level {
    constant: u32,
    /// `(parameter, offset)`, sorted by parameter, each parameter once.
    params: Vec<(u32, u32)>,
}
impl Level {
    pub fn zero() -> Self {
        Self::default()
    }
    pub fn constant(value: u32) -> Self {
        Self {
            constant: value,
            params: Vec::new(),
        }
    }
    pub fn param(index: u32) -> Self {
        Self {
            constant: 0,
            params: vec![(index, 0)],
        }
    }
    /// The closed value of a level without parameters.
    pub fn as_constant(&self) -> Option<u32> {
        self.params.is_empty().then_some(self.constant)
    }
    /// The canonical constant part (0 when a parameter offset dominates it).
    pub fn constant_part(&self) -> u32 {
        self.constant
    }
    /// `(parameter, offset)` pairs of the canonical form, by parameter.
    pub fn parameter_offsets(&self) -> &[(u32, u32)] {
        &self.params
    }
    /// The parameters a level mentions, in increasing order.
    pub fn parameters(&self) -> impl Iterator<Item = u32> + '_ {
        self.params.iter().map(|(index, _)| *index)
    }
    fn normalized(mut self) -> Self {
        let dominated = self.params.iter().map(|(_, offset)| *offset).max();
        if dominated.is_some_and(|offset| self.constant <= offset) {
            self.constant = 0;
        }
        self
    }
    pub fn succ(&self) -> Result<Self> {
        let bump = |value: u32| {
            value
                .checked_add(1)
                .ok_or_else(|| Error("universe level overflow".into()))
        };
        let constant = if self.params.is_empty() || self.constant > 0 {
            bump(self.constant)?
        } else {
            0
        };
        let params = self
            .params
            .iter()
            .map(|(index, offset)| Ok((*index, bump(*offset)?)))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self { constant, params }.normalized())
    }
    pub fn max(&self, other: &Self) -> Self {
        let mut params = self.params.clone();
        for (index, offset) in &other.params {
            match params.binary_search_by_key(index, |(index, _)| *index) {
                Ok(at) => params[at].1 = params[at].1.max(*offset),
                Err(at) => params.insert(at, (*index, *offset)),
            }
        }
        Self {
            constant: self.constant.max(other.constant),
            params,
        }
        .normalized()
    }
    /// Whether `self <= other` under every assignment of the parameters.
    pub fn leq(&self, other: &Self) -> bool {
        self.max(other) == *other
    }
    /// Replace each parameter `i` with `levels[i]`.
    fn instantiate(&self, levels: &[Level]) -> Result<Self> {
        let mut result = Self::constant(self.constant);
        for (index, offset) in &self.params {
            let mut level = levels
                .get(*index as usize)
                .cloned()
                .ok_or_else(|| Error(format!("unbound universe parameter {index}")))?;
            for _ in 0..*offset {
                level = level.succ()?;
            }
            result = result.max(&level);
        }
        Ok(result)
    }
}
impl fmt::Debug for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
impl From<u32> for Level {
    fn from(value: u32) -> Self {
        Self::constant(value)
    }
}
impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = Vec::new();
        if self.constant > 0 || self.params.is_empty() {
            parts.push(self.constant.to_string());
        }
        for (index, offset) in &self.params {
            parts.push(match offset {
                0 => format!("u{index}"),
                _ => format!("u{index}+{offset}"),
            });
        }
        if parts.len() == 1 {
            f.write_str(&parts[0])
        } else {
            write!(f, "max({})", parts.join(", "))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Zero-based de Bruijn index: 0 is the nearest enclosing binder.
    Var(usize),
    /// A global constant instantiated at universe levels, one per level
    /// parameter of its declaration (none for a monomorphic one).
    Global(String, Vec<Level>),
    Universe(Level),
    /// The sort of propositions. `Prop : Universe(0)`, never `Prop : Prop`.
    Prop,
    Pi {
        domain: Box<Term>,
        codomain: Box<Term>,
    },
    Lam {
        domain: Box<Term>,
        body: Box<Term>,
    },
    App(Box<Term>, Box<Term>),
    Nat,
    /// An admitted machine carrier type (`i64`, `Bool`, or `Unit`).
    Scalar(Scalar),
    /// A canonical machine literal. Its type is `Scalar(value.scalar())`.
    ScalarLiteral(ScalarValue),
    /// Compact numeral; normalization identifies literal zero with Zero.
    Literal(Natural),
    Zero,
    Succ(Box<Term>),
    /// motive : Nat -> Type(u), step : (n : Nat) -> motive n -> motive (succ n).
    NatElim {
        motive: Box<Term>,
        zero: Box<Term>,
        step: Box<Term>,
        value: Box<Term>,
    },
    Eq {
        ty: Box<Term>,
        left: Box<Term>,
        right: Box<Term>,
    },
    Refl {
        ty: Box<Term>,
        value: Box<Term>,
    },
    Transport {
        ty: Box<Term>,
        from: Box<Term>,
        to: Box<Term>,
        motive: Box<Term>,
        proof: Box<Term>,
        value: Box<Term>,
    },
    /// Dependent elimination of one admitted logical data type.
    ///
    /// `data` names the family. `motive` abstracts over the family's whole
    /// index telescope **and** the eliminated value:
    ///
    /// ```text
    /// motive : (i1 : I1) -> ... -> (ik : Ik) -> D i1 ... ik -> Universe(v)
    /// ```
    ///
    /// `branches` are in constructor declaration order. The branch for a
    /// constructor `c` binds the family indices, then its fields interleaved
    /// with one induction hypothesis after each direct recursive field, and
    /// returns `motive indices (c indices fields)`.
    IndElim {
        data: String,
        motive: Box<Term>,
        branches: Vec<Term>,
        scrutinee: Box<Term>,
    },
    /// Full dependent identity elimination (`J`).
    ///
    /// ```text
    /// motive : (y : A) -> Eq(A, x, y) -> Universe(v)
    /// refl    : motive x (Refl(A, x))
    /// proof   : Eq(A, x, y)
    /// result  : motive y proof
    /// ```
    EqElim {
        ty: Box<Term>,
        left: Box<Term>,
        right: Box<Term>,
        motive: Box<Term>,
        refl: Box<Term>,
        proof: Box<Term>,
    },
}
impl Term {
    /// A monomorphic global reference.
    pub fn global(name: impl Into<String>) -> Self {
        Self::Global(name.into(), Vec::new())
    }
    /// `Universe(level)` for a closed level.
    pub fn universe(level: u32) -> Self {
        Self::Universe(Level::constant(level))
    }
    pub fn natural(value: Natural) -> Self {
        if value.is_zero() {
            Self::Zero
        } else {
            Self::Literal(value)
        }
    }
    pub fn pi(domain: Term, codomain: Term) -> Self {
        Self::Pi {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }
    pub fn lam(domain: Term, body: Term) -> Self {
        Self::Lam {
            domain: Box::new(domain),
            body: Box::new(body),
        }
    }
    pub fn app(function: Term, argument: Term) -> Self {
        Self::App(Box::new(function), Box::new(argument))
    }
    pub fn succ(value: Term) -> Self {
        Self::Succ(Box::new(value))
    }
    pub fn i64(value: i64) -> Self {
        Self::ScalarLiteral(ScalarValue::I64(value))
    }
    pub fn boolean(value: bool) -> Self {
        Self::ScalarLiteral(ScalarValue::Bool(value))
    }
    pub fn unit() -> Self {
        Self::ScalarLiteral(ScalarValue::Unit)
    }
    pub fn i64_type() -> Self {
        Self::Scalar(Scalar::I64)
    }
    pub fn bool_type() -> Self {
        Self::Scalar(Scalar::Bool)
    }
    pub fn unit_type() -> Self {
        Self::Scalar(Scalar::Unit)
    }
    pub fn eq(ty: Term, left: Term, right: Term) -> Self {
        Self::Eq {
            ty: Box::new(ty),
            left: Box::new(left),
            right: Box::new(right),
        }
    }
    pub fn refl(ty: Term, value: Term) -> Self {
        Self::Refl {
            ty: Box::new(ty),
            value: Box::new(value),
        }
    }
    pub fn elim(
        data: impl Into<String>,
        motive: Term,
        branches: Vec<Term>,
        scrutinee: Term,
    ) -> Self {
        Self::IndElim {
            data: data.into(),
            motive: Box::new(motive),
            branches,
            scrutinee: Box::new(scrutinee),
        }
    }
    pub fn eq_elim(
        ty: Term,
        left: Term,
        right: Term,
        motive: Term,
        refl: Term,
        proof: Term,
    ) -> Self {
        Self::EqElim {
            ty: Box::new(ty),
            left: Box::new(left),
            right: Box::new(right),
            motive: Box::new(motive),
            refl: Box::new(refl),
            proof: Box::new(proof),
        }
    }
    /// Rebuild one layer; the flag marks children under a binder.
    fn map(&self, mut f: impl FnMut(&Term, bool) -> Result<Term>) -> Result<Term> {
        Ok(match self {
            Self::Pi { domain, codomain } => Self::pi(f(domain, false)?, f(codomain, true)?),
            Self::Lam { domain, body } => Self::lam(f(domain, false)?, f(body, true)?),
            Self::App(a, b) => Self::app(f(a, false)?, f(b, false)?),
            Self::Succ(n) => Self::succ(f(n, false)?),
            Self::NatElim {
                motive,
                zero,
                step,
                value,
            } => Self::NatElim {
                motive: Box::new(f(motive, false)?),
                zero: Box::new(f(zero, false)?),
                step: Box::new(f(step, false)?),
                value: Box::new(f(value, false)?),
            },
            Self::Eq { ty, left, right } => {
                Self::eq(f(ty, false)?, f(left, false)?, f(right, false)?)
            }
            Self::Refl { ty, value } => Self::refl(f(ty, false)?, f(value, false)?),
            Self::Transport {
                ty,
                from,
                to,
                motive,
                proof,
                value,
            } => Self::Transport {
                ty: Box::new(f(ty, false)?),
                from: Box::new(f(from, false)?),
                to: Box::new(f(to, false)?),
                motive: Box::new(f(motive, false)?),
                proof: Box::new(f(proof, false)?),
                value: Box::new(f(value, false)?),
            },
            Self::IndElim {
                data,
                motive,
                branches,
                scrutinee,
            } => Self::IndElim {
                data: data.clone(),
                motive: Box::new(f(motive, false)?),
                branches: branches
                    .iter()
                    .map(|branch| f(branch, false))
                    .collect::<Result<Vec<_>>>()?,
                scrutinee: Box::new(f(scrutinee, false)?),
            },
            Self::EqElim {
                ty,
                left,
                right,
                motive,
                refl,
                proof,
            } => Self::EqElim {
                ty: Box::new(f(ty, false)?),
                left: Box::new(f(left, false)?),
                right: Box::new(f(right, false)?),
                motive: Box::new(f(motive, false)?),
                refl: Box::new(f(refl, false)?),
                proof: Box::new(f(proof, false)?),
            },
            _ => self.clone(),
        })
    }
}

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

/// The checked sort of a type or proposition.
///
/// `Sort::Prop` is the sort of propositions (`P : Prop`). It is not itself a
/// proposition: `Prop : Universe(0)`. `Sort::Type(u)` is the ordinary
/// predicative universe hierarchy. `Prop` is impredicative: a dependent
/// function whose codomain is a proposition is a proposition again.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sort {
    Type(Level),
    Prop,
}
impl Sort {
    pub fn is_prop(&self) -> bool {
        matches!(self, Self::Prop)
    }
    /// The ordinary universe level a field of this sort contributes. `Prop`
    /// sits below `Type(0)`, so it contributes level 0.
    pub fn level(&self) -> Level {
        match self {
            Self::Type(level) => level.clone(),
            Self::Prop => Level::zero(),
        }
    }
}

/// Strip an application spine without reducing. Returns the head and the
/// arguments in source order.
fn spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut arguments = Vec::new();
    let mut current = term;
    while let Term::App(function, argument) = current {
        arguments.push(argument.as_ref());
        current = function.as_ref();
    }
    arguments.reverse();
    (current, arguments)
}

/// De Bruijn variable for the binder at `position` (outermost is 0) in a
/// telescope of `context_len` binders.
fn variable(context_len: usize, position: usize) -> Result<Term> {
    context_len
        .checked_sub(1 + position)
        .map(Term::Var)
        .ok_or_else(|| Error("internal error: telescope position out of range".into()))
}

#[derive(Debug, Clone, Copy)]
pub struct Limits {
    pub steps: usize,
    pub depth: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            steps: 100_000,
            depth: 128,
        }
    }
}
#[derive(Debug, Clone)]
struct Definition {
    /// Number of universe level parameters (`Level::param(0..levels)`).
    levels: u32,
    ty: Term,
    value: Term,
}

/// A positive, first-order indexed data family to admit.
///
/// `params` is a telescope: entry `i` is a type relative to entries `< i`.
/// Every declaration generic parameter becomes one entry, so the family is
/// `D : (p1 : P1) -> ... -> (pk : Pk) -> Universe(sort)`. Constructor `fields`
/// is a telescope relative to `params` followed by earlier fields, and
/// `result` has exactly `params.len()` index terms relative to `params` and
/// all fields. Recursive occurrences are restricted to whole fields whose head
/// is the family itself and whose index arguments do not mention the family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataSpec {
    pub name: String,
    pub params: Vec<Term>,
    pub constructors: Vec<ConstructorSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorSpec {
    pub name: String,
    pub fields: Vec<Term>,
    pub result: Vec<Term>,
}

/// A constructor with additional constructor-local binders.
///
/// The full telescope is
///
/// ```text
/// (params) -> (locals) -> (fields) -> D result
/// ```
///
/// `locals` are universally quantified for this constructor only. They are not
/// family indices, but field types and result indices may depend on them. This
/// is what makes `Fin` expressible: `fzero : (n : Nat) -> Fin (succ n)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexedConstructorSpec {
    pub name: String,
    /// Constructor-local telescope, relative to `params` and earlier locals.
    pub locals: Vec<Term>,
    /// Field telescope, relative to `params`, `locals`, and earlier fields.
    pub fields: Vec<Term>,
    /// One result index per family parameter, relative to `params`, `locals`,
    /// and all fields.
    pub result: Vec<Term>,
}

/// A data family declaration that supports constructor-local binders and
/// propositions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IndexedDataSpec {
    pub name: String,
    pub params: Vec<Term>,
    pub constructors: Vec<IndexedConstructorSpec>,
    /// When true the family lives in `Prop` and may only be eliminated into a
    /// proposition.
    pub prop: bool,
    /// Number of universe level parameters. Parameters, locals, fields and
    /// results may mention `Level::param(0..levels)`; a recursive field must
    /// instantiate the family at exactly those parameters, in order.
    pub levels: u32,
}
impl From<DataSpec> for IndexedDataSpec {
    fn from(spec: DataSpec) -> Self {
        Self {
            name: spec.name,
            params: spec.params,
            constructors: spec
                .constructors
                .into_iter()
                .map(|constructor| IndexedConstructorSpec {
                    name: constructor.name,
                    locals: Vec::new(),
                    fields: constructor.fields,
                    result: constructor.result,
                })
                .collect(),
            prop: false,
            levels: 0,
        }
    }
}

/// The admitted, independently validated form of a data family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataInfo {
    pub name: String,
    pub params: Vec<Term>,
    /// The family's universe, over its own level parameters.
    pub sort: Level,
    /// Whether the family lives in `Prop`.
    pub prop: bool,
    /// Number of universe level parameters.
    pub levels: u32,
    pub constructors: Vec<ConstructorInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorInfo {
    pub name: String,
    /// Constructor-local binders, outermost first.
    pub locals: Vec<Term>,
    pub fields: Vec<Term>,
    pub result: Vec<Term>,
    /// Whether field `i` is a direct recursive occurrence of the family.
    pub recursive: Vec<bool>,
}

#[derive(Debug, Clone)]
enum Global {
    Definition(Definition),
    Data {
        info: DataInfo,
        ty: Term,
    },
    Constructor {
        data: String,
        index: usize,
        ty: Term,
    },
}

#[derive(Debug, Default)]
pub struct Kernel {
    definitions: BTreeMap<String, Global>,
    limits: Limits,
    /// Universe parameters in scope for the open-term APIs (`check_open`,
    /// `sort_open`, ...). A frontend elaborating the body of a
    /// universe-polymorphic declaration sets this to the declaration's
    /// parameter count. Admission (`define_*`) uses its own explicit count.
    level_scope: u32,
}
impl Kernel {
    pub fn new(limits: Limits) -> Self {
        Self {
            definitions: BTreeMap::new(),
            limits,
            level_scope: 0,
        }
    }
    fn engine(&self) -> Engine<'_> {
        let mut engine = Engine::new(&self.definitions, self.limits);
        engine.levels = self.level_scope;
        engine
    }
    /// Set the universe parameters in scope for open queries; see
    /// `level_scope`. Returns the previous value.
    pub fn set_level_scope(&mut self, levels: u32) -> u32 {
        std::mem::replace(&mut self.level_scope, levels)
    }
    /// The number of universe parameters of an admitted global.
    pub fn global_levels(&self, name: &str) -> Option<u32> {
        Some(match self.definitions.get(name)? {
            Global::Definition(definition) => definition.levels,
            Global::Data { info, .. } => info.levels,
            Global::Constructor { data, .. } => match self.definitions.get(data)? {
                Global::Data { info, .. } => info.levels,
                _ => return None,
            },
        })
    }
    pub fn contains(&self, name: &str) -> bool {
        self.definitions.contains_key(name)
    }
    /// The value of an admitted definition (not of a data family or
    /// constructor, which are opaque).
    pub fn definition_value(&self, name: &str) -> Option<&Term> {
        match self.definitions.get(name)? {
            Global::Definition(definition) => Some(&definition.value),
            _ => None,
        }
    }
    pub fn definition_type(&self, name: &str) -> Option<&Term> {
        self.definitions.get(name).map(|global| match global {
            Global::Definition(definition) => &definition.ty,
            Global::Data { ty, .. } | Global::Constructor { ty, .. } => ty,
        })
    }
    /// Inspect an admitted data family. Absent for plain definitions.
    pub fn data(&self, name: &str) -> Option<&DataInfo> {
        match self.definitions.get(name) {
            Some(Global::Data { info, .. }) => Some(info),
            _ => None,
        }
    }
    /// Atomically validate and admit a closed definition. There is no axiom,
    /// unchecked global, or recursive-definition insertion API.
    pub fn define(&mut self, name: String, ty: Term, value: Term) -> Result<()> {
        self.define_polymorphic(name, 0, ty, value)
    }
    /// Admit a definition polymorphic over `levels` universe parameters. Its
    /// type and value may mention `Level::param(0..levels)`; every use names
    /// one level per parameter (`Term::Global(name, levels)`) and sees the
    /// type and value instantiated at those levels.
    pub fn define_polymorphic(
        &mut self,
        name: String,
        levels: u32,
        ty: Term,
        value: Term,
    ) -> Result<()> {
        if self.contains(&name) {
            return fail(format!("duplicate kernel definition '{name}'"));
        }
        if levels > 64 {
            return fail("definitions support at most 64 universe parameters");
        }
        {
            let mut e = self.engine();
            e.levels = levels;
            e.sort(&ty, &mut Vec::new())?;
            e.check(&value, &ty, &mut Vec::new())?;
        }
        self.definitions
            .insert(name, Global::Definition(Definition { levels, ty, value }));
        Ok(())
    }
    /// Atomically validate and admit a positive indexed data family and all of
    /// its constructors. Nothing is inserted unless every premise checks.
    pub fn define_data(&mut self, spec: DataSpec) -> Result<()> {
        self.define_indexed_data(spec.into())
    }
    /// Atomically admit a family whose constructors may have local binders and
    /// which may live in `Prop`. `define_data` is the no-locals,
    /// Type-valued special case.
    pub fn define_indexed_data(&mut self, spec: IndexedDataSpec) -> Result<()> {
        if spec.params.len() > 64 {
            return fail("data declarations support at most 64 index parameters");
        }
        if spec.constructors.len() > 64 {
            return fail("data declarations support at most 64 constructors");
        }
        if spec.levels > 64 {
            return fail("data declarations support at most 64 universe parameters");
        }
        // Recursive occurrences instantiate the family at its own parameters.
        let own_levels: Vec<Level> = (0..spec.levels).map(Level::param).collect();
        if self.contains(&spec.name) {
            return fail(format!("duplicate kernel global '{}'", spec.name));
        }
        let mut names = std::collections::BTreeSet::new();
        for constructor in &spec.constructors {
            if !names.insert(constructor.name.clone()) {
                return fail(format!("duplicate constructor '{}'", constructor.name));
            }
            if self.contains(&constructor.name) {
                return fail(format!(
                    "constructor name '{}' collides with an existing kernel global",
                    constructor.name
                ));
            }
            if constructor.result.len() != spec.params.len() {
                return fail(format!(
                    "constructor '{}' must produce exactly {} index arguments, found {}",
                    constructor.name,
                    spec.params.len(),
                    constructor.result.len()
                ));
            }
            if constructor.locals.len() > 64 {
                return fail(format!(
                    "constructor '{}' has more than 64 constructor-local binders",
                    constructor.name
                ));
            }
        }
        let k = spec.params.len();
        let mut sort = Level::zero();
        let mut constructors = Vec::with_capacity(spec.constructors.len());
        {
            let mut e = Engine::new(&self.definitions, self.limits);
            e.levels = spec.levels;
            let mut params = Vec::new();
            for param in &spec.params {
                if e.mentions(param, &spec.name)? {
                    return fail(format!(
                        "data '{}' occurs in its own parameter/index kinds; nested or negative self-reference is unsupported",
                        spec.name
                    ));
                }
                e.sort(param, &mut params)?;
                params.push(param.clone());
            }
            for constructor in &spec.constructors {
                let mut context = params.clone();
                for local in &constructor.locals {
                    if e.mentions(local, &spec.name)? {
                        return fail(format!(
                            "constructor '{}' has a non-strictly-positive or nested occurrence of '{}' in a constructor-local binder",
                            constructor.name, spec.name
                        ));
                    }
                    let universe = e.sort(local, &mut context)?;
                    // Constructor-local binders are existentially quantified
                    // for this constructor and can be exposed by the
                    // eliminator, so a Type-valued family's universe must
                    // account for them. Parameters are fixed inputs and do not
                    // raise the family's sort.
                    if !spec.prop {
                        sort = sort.max(&universe.level());
                    }
                    context.push(local.clone());
                }
                let mut recursive = Vec::with_capacity(constructor.fields.len());
                for field in &constructor.fields {
                    let (head, args) = spine(field);
                    if let Term::Global(name, levels) = head
                        && name == &spec.name
                        && levels != &own_levels
                    {
                        return fail(format!(
                            "constructor '{}' uses '{}' at other universe levels; a recursive occurrence must use the family's own universe parameters, in order",
                            constructor.name, spec.name
                        ));
                    }
                    let direct = matches!(head, Term::Global(name, _) if name == &spec.name)
                        && args.len() == k;
                    if direct {
                        for argument in &args {
                            if e.mentions(argument, &spec.name)? {
                                return fail(format!(
                                    "constructor '{}' has a non-strictly-positive recursive occurrence: an index argument of a recursive field mentions '{}'",
                                    constructor.name, spec.name
                                ));
                            }
                        }
                        recursive.push(true);
                    } else {
                        if e.mentions(field, &spec.name)? {
                            return fail(format!(
                                "constructor '{}' has a non-strictly-positive or nested recursive occurrence of '{}'; only a whole field of type '{} indices' is supported",
                                constructor.name, spec.name, spec.name
                            ));
                        }
                        let universe = e.sort(field, &mut context)?;
                        if !spec.prop {
                            sort = sort.max(&universe.level());
                        }
                        recursive.push(false);
                    }
                    context.push(field.clone());
                }
                constructors.push(ConstructorInfo {
                    name: constructor.name.clone(),
                    locals: constructor.locals.clone(),
                    fields: constructor.fields.clone(),
                    result: constructor.result.clone(),
                    recursive,
                });
            }
        }
        let mut family = if spec.prop {
            Term::Prop
        } else {
            Term::Universe(sort.clone())
        };
        for param in spec.params.iter().rev() {
            family = Term::pi(param.clone(), family);
        }
        let info = DataInfo {
            name: spec.name.clone(),
            params: spec.params.clone(),
            sort: sort.clone(),
            prop: spec.prop,
            levels: spec.levels,
            constructors,
        };
        // Validate every field, result index, and constructor type with the
        // candidate family visible, so recursive occurrences are checkable.
        let mut provisional = self.definitions.clone();
        provisional.insert(
            spec.name.clone(),
            Global::Data {
                info: info.clone(),
                ty: family.clone(),
            },
        );
        let mut constructor_types = Vec::with_capacity(spec.constructors.len());
        {
            let mut e = Engine::new(&provisional, self.limits);
            e.levels = spec.levels;
            for constructor in &info.constructors {
                let mut context = Vec::new();
                for param in &info.params {
                    e.sort(param, &mut context)?;
                    context.push(param.clone());
                }
                for local in &constructor.locals {
                    e.sort(local, &mut context)?;
                    context.push(local.clone());
                }
                for field in &constructor.fields {
                    let universe = e.sort(field, &mut context)?;
                    if !info.prop && !universe.level().leq(&sort) {
                        return fail(format!(
                            "constructor '{}' field escapes the data universe: field sort {} exceeds data sort {sort}",
                            constructor.name,
                            universe.level()
                        ));
                    }
                    context.push(field.clone());
                }
                let application = e.application(
                    Term::Global(info.name.clone(), own_levels.clone()),
                    constructor.result.iter().cloned(),
                )?;
                let universe = e.sort(&application, &mut context)?;
                if info.prop {
                    if !universe.is_prop() {
                        return fail(format!(
                            "constructor '{}' result index escapes Prop",
                            constructor.name
                        ));
                    }
                } else if universe.level() != sort || universe.is_prop() {
                    return fail(format!(
                        "constructor '{}' result index escapes the data universe",
                        constructor.name
                    ));
                }
                let mut ty = application;
                for field in constructor.fields.iter().rev() {
                    ty = Term::pi(field.clone(), ty);
                }
                for local in constructor.locals.iter().rev() {
                    ty = Term::pi(local.clone(), ty);
                }
                for param in info.params.iter().rev() {
                    ty = Term::pi(param.clone(), ty);
                }
                constructor_types.push(ty);
            }
        }
        self.definitions.insert(
            spec.name.clone(),
            Global::Data {
                info: info.clone(),
                ty: family,
            },
        );
        for (index, constructor) in info.constructors.iter().enumerate() {
            self.definitions.insert(
                constructor.name.clone(),
                Global::Constructor {
                    data: info.name.clone(),
                    index,
                    ty: constructor_types[index].clone(),
                },
            );
        }
        Ok(())
    }
    pub fn infer_closed(&self, term: &Term) -> Result<Term> {
        let mut e = self.engine();
        let ty = e.infer(term, &mut Vec::new())?;
        e.normal(&ty)
    }
    /// Classify a closed type or proposition by its sort.
    pub fn sort_closed(&self, term: &Term) -> Result<Sort> {
        let mut e = self.engine();
        e.sort(term, &mut Vec::new())
    }
    /// Classify an open type or proposition by its sort. The context is
    /// validated exactly as for `check_open`.
    pub fn sort_open(&self, term: &Term, context: &[Term]) -> Result<Sort> {
        let mut e = self.engine();
        let mut context = e.context(context)?;
        e.sort(term, &mut context)
    }
    pub fn check_closed(&self, term: &Term, ty: &Term) -> Result<()> {
        let mut e = self.engine();
        e.sort(ty, &mut Vec::new())?;
        e.check(term, ty, &mut Vec::new())
    }
    pub fn normalize_closed(&self, term: &Term) -> Result<Term> {
        let mut e = self.engine();
        e.infer(term, &mut Vec::new())?;
        e.normal(term)
    }
    /// Normalize an open term after validating each hypothesis type. This is a
    /// checked reduction: callers cannot use it to bypass typing.
    pub fn normalize_open(&self, term: &Term, context: &[Term]) -> Result<Term> {
        let mut e = self.engine();
        let mut context = e.context(context)?;
        e.infer(term, &mut context)?;
        e.normal(term)
    }
    /// Whether an open term normalizes to an admitted machine carrier. The
    /// context is validated. Used to decide whether a runtime value may serve as
    /// a symbolic index.
    pub fn scalar_open(&self, term: &Term, context: &[Term]) -> Result<Option<Scalar>> {
        let term = self.normalize_open(term, context)?;
        Ok(match term {
            Term::Scalar(scalar) => Some(scalar),
            _ => None,
        })
    }
    /// Whether a closed term is a proof, i.e. its type is classified by
    /// `Prop`. This is the boundary of proof irrelevance: `Nat` and other
    /// Type-valued inhabitants are never proofs.
    pub fn proof_closed(&self, term: &Term) -> Result<bool> {
        let mut e = self.engine();
        let ty = e.infer(term, &mut Vec::new())?;
        Ok(e.sort(&ty, &mut Vec::new())?.is_prop())
    }
    /// Whether an open term is a proof in a validated context.
    pub fn proof_open(&self, term: &Term, context: &[Term]) -> Result<bool> {
        let mut e = self.engine();
        let mut context = e.context(context)?;
        let ty = e.infer(term, &mut context)?;
        Ok(e.sort(&ty, &mut context)?.is_prop())
    }
    /// Check a term in a context of hypothesis types. Each context entry is
    /// itself validated as a type relative to the preceding entries, so callers
    /// cannot use this to insert values or unchecked globals.
    pub fn check_open(&self, term: &Term, ty: &Term, context: &[Term]) -> Result<()> {
        let mut e = self.engine();
        let mut context = e.context(context)?;
        e.sort(ty, &mut context)?;
        e.check(term, ty, &mut context)
    }
    /// Infer the type of an open term. The context is validated first.
    pub fn infer_open(&self, term: &Term, context: &[Term]) -> Result<Term> {
        let mut e = self.engine();
        let mut context = e.context(context)?;
        let ty = e.infer(term, &mut context)?;
        e.normal(&ty)
    }
    /// Substitute caller-supplied terms for the outermost binders of an open
    /// term, outermost first. This is the checked call-site substitution used
    /// by dependent erased parameters; it does not admit unchecked globals.
    /// Shift every free de Bruijn variable in an already checked open term by
    /// `amount`, as required when the surrounding telescope grows after the
    /// term was elaborated. Used by stable erased proof-valued local aliases.
    pub(crate) fn shift_open(&self, term: &Term, amount: usize) -> Result<Term> {
        let mut e = self.engine();
        e.shift(term, amount, 0)
    }

    pub(crate) fn substitute_outer(&self, term: &Term, arguments: &[Term]) -> Result<Term> {
        let mut e = self.engine();
        let mut term = term.clone();
        for argument in arguments.iter().rev() {
            term = e.substitute(&term, argument, 0)?;
        }
        Ok(term)
    }
}

struct Engine<'a> {
    definitions: &'a BTreeMap<String, Global>,
    fuel: usize,
    depth: usize,
    max_depth: usize,
    /// Universe parameters in scope: levels may mention `param(0..levels)`.
    levels: u32,
}
impl Engine<'_> {
    fn new(definitions: &BTreeMap<String, Global>, limits: Limits) -> Engine<'_> {
        Engine {
            definitions,
            fuel: limits.steps,
            depth: 0,
            max_depth: limits.depth,
            levels: 0,
        }
    }
    /// Reject a level that mentions a parameter not in scope.
    fn level_in_scope(&self, level: &Level) -> Result<()> {
        match level.parameters().find(|index| *index >= self.levels) {
            Some(index) => fail(format!("unbound universe parameter u{index}")),
            None => Ok(()),
        }
    }
    /// The number of universe parameters a global declares.
    fn global_arity(&self, name: &str) -> Result<u32> {
        Ok(match self.definitions.get(name) {
            Some(Global::Definition(definition)) => definition.levels,
            Some(Global::Data { info, .. }) => info.levels,
            Some(Global::Constructor { data, .. }) => self.data_info(data)?.levels,
            None => return fail(format!("unknown kernel global '{name}'")),
        })
    }
    /// Check the level arguments of a global reference: one per declared
    /// parameter, each in scope.
    fn global_levels(&self, name: &str, levels: &[Level]) -> Result<()> {
        let arity = self.global_arity(name)?;
        if levels.len() != arity as usize {
            return fail(format!(
                "'{name}' takes {arity} universe arguments, found {}",
                levels.len()
            ));
        }
        levels
            .iter()
            .try_for_each(|level| self.level_in_scope(level))
    }
    /// Replace universe parameters throughout a term. Charged like any other
    /// traversal.
    fn instantiate(&mut self, term: &Term, levels: &[Level]) -> Result<Term> {
        if levels.is_empty() {
            return Ok(term.clone());
        }
        self.step(|e| match term {
            Term::Universe(level) => Ok(Term::Universe(level.instantiate(levels)?)),
            Term::Global(name, arguments) => Ok(Term::Global(
                name.clone(),
                arguments
                    .iter()
                    .map(|level| level.instantiate(levels))
                    .collect::<Result<_>>()?,
            )),
            _ => term.map(|child, _| e.instantiate(child, levels)),
        })
    }
    /// A data family's description at the given universe levels.
    fn data_at(&mut self, name: &str, levels: &[Level]) -> Result<DataInfo> {
        let mut info = self.data_info(name)?;
        if levels.is_empty() {
            return Ok(info);
        }
        let all = |e: &mut Self, terms: &[Term]| {
            terms
                .iter()
                .map(|term| e.instantiate(term, levels))
                .collect::<Result<Vec<_>>>()
        };
        info.params = all(self, &info.params)?;
        info.sort = info.sort.instantiate(levels)?;
        for constructor in &mut info.constructors {
            constructor.locals = all(self, &constructor.locals)?;
            constructor.fields = all(self, &constructor.fields)?;
            constructor.result = all(self, &constructor.result)?;
        }
        Ok(info)
    }
    fn step<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth >= self.max_depth {
            return fail("kernel nesting budget exhausted");
        }
        self.charge(1)?;
        self.depth += 1;
        let result = f(self);
        self.depth -= 1;
        result
    }
    fn charge(&mut self, units: usize) -> Result<()> {
        self.fuel = self
            .fuel
            .checked_sub(units)
            .ok_or_else(|| Error("kernel computation budget exhausted".into()))?;
        Ok(())
    }
    /// Validate every hypothesis type relative to the entries before it.
    fn context(&mut self, context: &[Term]) -> Result<Vec<Term>> {
        let mut checked = Vec::with_capacity(context.len());
        for entry in context {
            self.sort(entry, &mut checked)?;
            checked.push(entry.clone());
        }
        Ok(checked)
    }
    fn application(
        &mut self,
        head: Term,
        arguments: impl IntoIterator<Item = Term>,
    ) -> Result<Term> {
        let mut term = head;
        for argument in arguments {
            self.charge(1)?;
            term = Term::app(term, argument);
        }
        Ok(term)
    }
    /// Whether `name` occurs anywhere in `term`. Used only for the conservative
    /// positivity restriction. The traversal is depth-limited and charged to
    /// the same budget as the rest of kernel checking.
    fn mentions(&mut self, term: &Term, name: &str) -> Result<bool> {
        self.step(|e| {
            if let Term::Global(global, _) = term {
                return Ok(global == name);
            }
            let mut found = false;
            term.map(|child, _| {
                if !found {
                    found = e.mentions(child, name)?;
                }
                Ok(child.clone())
            })?;
            Ok(found)
        })
    }
    /// Replace the outermost `arguments.len()` binders of `term` with terms
    /// that live in the target context. This is a parallel remapping: every
    /// removed binder is replaced in one pass, so indices are never
    /// decremented or accidentally captured.
    fn rewrite_outer(&mut self, term: &Term, arguments: &[Term]) -> Result<Term> {
        self.rewrite_at(term, arguments, 0)
    }
    fn rewrite_at(&mut self, term: &Term, arguments: &[Term], depth: usize) -> Result<Term> {
        self.step(|e| match term {
            Term::Literal(value) => e.numeral(value),
            Term::Var(index) if *index < depth => Ok(Term::Var(*index)),
            Term::Var(index) => {
                let offset = index - depth;
                let position = arguments.len().checked_sub(1 + offset).ok_or_else(|| {
                    Error("internal error: data telescope variable out of range".into())
                })?;
                e.shift(&arguments[position], depth, 0)
            }
            _ => term
                .map(|child, binder| e.rewrite_at(child, arguments, depth + usize::from(binder))),
        })
    }
    fn data_info(&self, name: &str) -> Result<DataInfo> {
        match self.definitions.get(name) {
            Some(Global::Data { info, .. }) => Ok(info.clone()),
            _ => fail(format!("'{name}' is not an admitted logical data type")),
        }
    }
    fn numeral(&mut self, value: &Natural) -> Result<Term> {
        self.charge(value.work())?;
        Ok(Term::natural(value.clone()))
    }
    /// Shift free indices upwards without capturing under Pi/Lam binders.
    fn shift(&mut self, term: &Term, amount: usize, cutoff: usize) -> Result<Term> {
        self.step(|e| match term {
            Term::Literal(value) => e.numeral(value),
            Term::Var(i) if *i >= cutoff => Ok(Term::Var(
                i.checked_add(amount)
                    .ok_or_else(|| Error("variable index overflow".into()))?,
            )),
            _ => term.map(|child, binder| e.shift(child, amount, cutoff + usize::from(binder))),
        })
    }
    /// Substitute for a removed binder, lowering indices above that binder.
    fn substitute(&mut self, term: &Term, value: &Term, depth: usize) -> Result<Term> {
        self.step(|e| match term {
            Term::Literal(value) => e.numeral(value),
            Term::Var(i) if *i == depth => e.shift(value, depth, 0),
            Term::Var(i) if *i > depth => Ok(Term::Var(i - 1)),
            _ => term.map(|child, binder| e.substitute(child, value, depth + usize::from(binder))),
        })
    }
    fn normal(&mut self, term: &Term) -> Result<Term> {
        self.step(|e| match term {
            Term::Literal(value) => e.numeral(value),
            Term::Succ(value) => match e.normal(value)? {
                Term::Zero => Ok(Term::natural(Natural::from(1))),
                Term::Literal(value) => {
                    e.charge(value.work())?;
                    let next = value
                        .successor()
                        .map_err(|error| Error(error.to_string()))?;
                    Ok(Term::natural(next))
                }
                neutral => Ok(Term::succ(neutral)),
            },
            Term::Global(name, levels) => match e.definitions.get(name) {
                Some(Global::Definition(definition)) => {
                    let value = definition.value.clone();
                    let value = e.instantiate(&value, levels)?;
                    e.normal(&value)
                }
                Some(_) => Ok(term.clone()),
                None => Err(Error(format!("unknown kernel global '{name}'"))),
            },
            Term::App(function, argument) => match e.normal(function)? {
                Term::Lam { body, .. } => {
                    let replaced = e.substitute(&body, argument, 0)?;
                    e.normal(&replaced)
                }
                function => Ok(Term::app(function, e.normal(argument)?)),
            },
            Term::NatElim {
                motive,
                zero,
                step,
                value,
            } => match e.normal(value)? {
                Term::Zero => e.normal(zero),
                Term::Succ(pred) => e.induction_step(motive, zero, step, *pred),
                Term::Literal(value) => {
                    e.charge(value.work())?;
                    match value.predecessor() {
                        Some(pred) => e.induction_step(motive, zero, step, Term::natural(pred)),
                        None => e.normal(zero),
                    }
                }
                value => Ok(Term::NatElim {
                    motive: Box::new(e.normal(motive)?),
                    zero: Box::new(e.normal(zero)?),
                    step: Box::new(e.normal(step)?),
                    value: Box::new(value),
                }),
            },
            Term::Transport { proof, value, .. }
                if matches!(e.normal(proof)?, Term::Refl { .. }) =>
            {
                e.normal(value)
            }
            Term::EqElim {
                ty,
                left,
                right,
                motive,
                refl,
                proof,
            } => {
                let proof = e.normal(proof)?;
                if matches!(proof, Term::Refl { .. }) {
                    return e.normal(refl);
                }
                Ok(Term::EqElim {
                    ty: Box::new(e.normal(ty)?),
                    left: Box::new(e.normal(left)?),
                    right: Box::new(e.normal(right)?),
                    motive: Box::new(e.normal(motive)?),
                    refl: Box::new(e.normal(refl)?),
                    proof: Box::new(proof),
                })
            }
            Term::IndElim {
                data,
                motive,
                branches,
                scrutinee,
            } => {
                let scrutinee = e.normal(scrutinee)?;
                if let Some(reduced) = e.data_elim_step(data, motive, branches, &scrutinee)? {
                    return e.normal(&reduced);
                }
                Ok(Term::IndElim {
                    data: data.clone(),
                    motive: Box::new(e.normal(motive)?),
                    branches: branches
                        .iter()
                        .map(|branch| e.normal(branch))
                        .collect::<Result<Vec<_>>>()?,
                    scrutinee: Box::new(scrutinee),
                })
            }
            Term::Scalar(_) => Ok(term.clone()),
            Term::ScalarLiteral(value) => {
                e.charge(1)?;
                Ok(Term::ScalarLiteral(*value))
            }
            _ => term.map(|child, _| e.normal(child)),
        })
    }
    /// One constructor-reduction step of a data eliminator. `None` keeps the
    /// elimination neutral (an open scrutinee or a different constructor).
    fn data_elim_step(
        &mut self,
        data: &str,
        motive: &Term,
        branches: &[Term],
        scrutinee: &Term,
    ) -> Result<Option<Term>> {
        let (head, arguments) = spine(scrutinee);
        let Term::Global(name, _) = head else {
            return Ok(None);
        };
        let (owner, index) = match self.definitions.get(name) {
            Some(Global::Constructor { data, index, .. }) => (data.clone(), *index),
            _ => return Ok(None),
        };
        if owner != data {
            return Ok(None);
        }
        let info = self.data_info(data)?;
        let params = info.params.len();
        let constructor = &info.constructors[index];
        let arity = params + constructor.locals.len();
        if arguments.len() != arity + constructor.fields.len() {
            return Ok(None);
        }
        let Some(branch) = branches.get(index) else {
            return fail("data eliminator is missing a constructor branch");
        };
        self.charge(1)?;
        let mut term = branch.clone();
        for argument in &arguments[..arity] {
            term = Term::app(term, (*argument).clone());
        }
        for (field, recursive) in constructor.recursive.iter().enumerate() {
            let value = arguments[arity + field].clone();
            term = Term::app(term, value.clone());
            if *recursive {
                term = Term::app(
                    term,
                    Term::IndElim {
                        data: data.to_owned(),
                        motive: Box::new(motive.clone()),
                        branches: branches.to_vec(),
                        scrutinee: Box::new(value),
                    },
                );
            }
        }
        Ok(Some(term))
    }
    fn induction_step(
        &mut self,
        motive: &Term,
        zero: &Term,
        step: &Term,
        pred: Term,
    ) -> Result<Term> {
        // Preserve the original lazy induction equation: a step which ignores
        // its induction hypothesis need not evaluate all preceding cases.
        let recursive = Term::NatElim {
            motive: Box::new(motive.clone()),
            zero: Box::new(zero.clone()),
            step: Box::new(step.clone()),
            value: Box::new(pred.clone()),
        };
        let applied = Term::app(Term::app(step.clone(), pred), recursive);
        self.normal(&applied)
    }
    /// Conversion is type-directed so that proof irrelevance can apply exactly
    /// to inhabitants of propositions. Two proofs of convertible propositions
    /// are convertible; ordinary values such as `Nat` numerals are still
    /// compared structurally.
    fn equal(&mut self, left: &Term, right: &Term, context: &mut Vec<Term>) -> Result<bool> {
        let left = self.normal(left)?;
        let right = self.normal(right)?;
        self.convert(&left, &right, context)
    }
    /// Whether `term` is a proof, i.e. its type is classified by `Prop`.
    fn proof(&mut self, term: &Term, context: &mut Vec<Term>) -> Result<bool> {
        let ty = self.infer(term, context)?;
        Ok(self.sort(&ty, context)?.is_prop())
    }
    fn convert(&mut self, left: &Term, right: &Term, context: &mut Vec<Term>) -> Result<bool> {
        self.step(|e| {
            if left == right {
                return Ok(true);
            }
            // Proof irrelevance: only inhabitants of checked propositions.
            if e.proof(left, context)? && e.proof(right, context)? {
                let left_type = e.infer(left, context)?;
                let right_type = e.infer(right, context)?;
                return e.equal(&left_type, &right_type, context);
            }
            // Eta for functions: `Lam(A, b) ≡ f` when `b ≡ f' 0` under `A`,
            // where `f'` is `f` weakened past the new binder. Only fires when
            // exactly one side is a lambda; two lambdas compare structurally.
            match (left, right) {
                (Term::Lam { domain, body }, other) | (other, Term::Lam { domain, body })
                    if !matches!(other, Term::Lam { .. }) =>
                {
                    let expanded = Term::app(e.shift(other, 1, 0)?, Term::Var(0));
                    let domain = domain.as_ref().clone();
                    return e.under(context, &domain, |e, c| e.equal(body, &expanded, c));
                }
                _ => {}
            }
            let equal = match (left, right) {
                (
                    Term::Pi {
                        domain: left_domain,
                        codomain: left_codomain,
                    },
                    Term::Pi {
                        domain: right_domain,
                        codomain: right_codomain,
                    },
                )
                | (
                    Term::Lam {
                        domain: left_domain,
                        body: left_codomain,
                    },
                    Term::Lam {
                        domain: right_domain,
                        body: right_codomain,
                    },
                ) => {
                    if !e.equal(left_domain, right_domain, context)? {
                        false
                    } else {
                        let domain = left_domain.as_ref().clone();
                        context.push(domain);
                        let result = e.equal(left_codomain, right_codomain, context)?;
                        context.pop();
                        result
                    }
                }
                (
                    Term::App(left_function, left_argument),
                    Term::App(right_function, right_argument),
                ) => {
                    e.equal(left_function, right_function, context)?
                        && e.equal(left_argument, right_argument, context)?
                }
                (Term::Succ(left), Term::Succ(right)) => e.equal(left, right, context)?,
                (Term::Literal(left), Term::Literal(right)) => left == right,
                (Term::Scalar(left), Term::Scalar(right)) => left == right,
                (Term::ScalarLiteral(left), Term::ScalarLiteral(right)) => left == right,
                (Term::Var(left), Term::Var(right)) => left == right,
                (Term::Global(left, left_levels), Term::Global(right, right_levels)) => {
                    left == right && left_levels == right_levels
                }
                (Term::Universe(left), Term::Universe(right)) => left == right,
                (Term::Nat, Term::Nat) | (Term::Zero, Term::Zero) | (Term::Prop, Term::Prop) => {
                    true
                }
                (
                    Term::NatElim {
                        motive: left_motive,
                        zero: left_zero,
                        step: left_step,
                        value: left_value,
                    },
                    Term::NatElim {
                        motive: right_motive,
                        zero: right_zero,
                        step: right_step,
                        value: right_value,
                    },
                ) => {
                    e.equal(left_motive, right_motive, context)?
                        && e.equal(left_zero, right_zero, context)?
                        && e.equal(left_step, right_step, context)?
                        && e.equal(left_value, right_value, context)?
                }
                (
                    Term::Eq {
                        ty: left_ty,
                        left: left_left,
                        right: left_right,
                    },
                    Term::Eq {
                        ty: right_ty,
                        left: right_left,
                        right: right_right,
                    },
                ) => {
                    e.equal(left_ty, right_ty, context)?
                        && e.equal(left_left, right_left, context)?
                        && e.equal(left_right, right_right, context)?
                }
                (
                    Term::Refl {
                        ty: left_ty,
                        value: left_value,
                    },
                    Term::Refl {
                        ty: right_ty,
                        value: right_value,
                    },
                ) => {
                    e.equal(left_ty, right_ty, context)?
                        && e.equal(left_value, right_value, context)?
                }
                (
                    Term::Transport {
                        ty: left_ty,
                        from: left_from,
                        to: left_to,
                        motive: left_motive,
                        proof: left_proof,
                        value: left_value,
                    },
                    Term::Transport {
                        ty: right_ty,
                        from: right_from,
                        to: right_to,
                        motive: right_motive,
                        proof: right_proof,
                        value: right_value,
                    },
                ) => {
                    e.equal(left_ty, right_ty, context)?
                        && e.equal(left_from, right_from, context)?
                        && e.equal(left_to, right_to, context)?
                        && e.equal(left_motive, right_motive, context)?
                        && e.equal(left_proof, right_proof, context)?
                        && e.equal(left_value, right_value, context)?
                }
                (
                    Term::IndElim {
                        data: left_data,
                        motive: left_motive,
                        branches: left_branches,
                        scrutinee: left_scrutinee,
                    },
                    Term::IndElim {
                        data: right_data,
                        motive: right_motive,
                        branches: right_branches,
                        scrutinee: right_scrutinee,
                    },
                ) => {
                    let mut same = left_data == right_data
                        && left_branches.len() == right_branches.len()
                        && e.equal(left_motive, right_motive, context)?
                        && e.equal(left_scrutinee, right_scrutinee, context)?;
                    if same {
                        for (left, right) in left_branches.iter().zip(right_branches) {
                            if !e.equal(left, right, context)? {
                                same = false;
                                break;
                            }
                        }
                    }
                    same
                }
                (
                    Term::EqElim {
                        ty: left_ty,
                        left: left_left,
                        right: left_right,
                        motive: left_motive,
                        refl: left_refl,
                        proof: left_proof,
                    },
                    Term::EqElim {
                        ty: right_ty,
                        left: right_left,
                        right: right_right,
                        motive: right_motive,
                        refl: right_refl,
                        proof: right_proof,
                    },
                ) => {
                    e.equal(left_ty, right_ty, context)?
                        && e.equal(left_left, right_left, context)?
                        && e.equal(left_right, right_right, context)?
                        && e.equal(left_motive, right_motive, context)?
                        && e.equal(left_refl, right_refl, context)?
                        && e.equal(left_proof, right_proof, context)?
                }
                _ => false,
            };
            Ok(equal)
        })
    }
    fn sort(&mut self, term: &Term, context: &mut Vec<Term>) -> Result<Sort> {
        let inferred = self.infer(term, context)?;
        match self.normal(&inferred)? {
            Term::Universe(level) => Ok(Sort::Type(level)),
            Term::Prop => Ok(Sort::Prop),
            _ => fail("expected a type (a term inhabiting a universe or Prop)"),
        }
    }
    fn check(&mut self, term: &Term, ty: &Term, context: &mut Vec<Term>) -> Result<()> {
        let actual = self.infer(term, context)?;
        if self.equal(&actual, ty, context)? {
            Ok(())
        } else {
            fail(format!(
                "type mismatch: expected {ty:?}, inferred {actual:?}"
            ))
        }
    }
    fn under<T>(
        &mut self,
        context: &mut Vec<Term>,
        domain: &Term,
        f: impl FnOnce(&mut Self, &mut Vec<Term>) -> Result<T>,
    ) -> Result<T> {
        context.push(domain.clone());
        let result = f(self, context);
        context.pop();
        result
    }
    /// The sort denoted by a family's codomain.
    ///
    /// A valid motive or type family has a codomain that is literally a sort
    /// term after normalization: `Universe(u)` denotes `Type(u)` and `Prop`
    /// denotes `Prop`. A codomain such as a variable `P : Prop` means the
    /// function returns *proofs* of `P`, not propositions, and is rejected.
    fn codomain_sort(&mut self, codomain: &Term, _context: &mut Vec<Term>) -> Result<Sort> {
        match self.normal(codomain)? {
            Term::Universe(level) => Ok(Sort::Type(level)),
            Term::Prop => Ok(Sort::Prop),
            _ => fail("expected a type family returning a type or proposition"),
        }
    }
    fn family(&mut self, term: &Term, domain: &Term, context: &mut Vec<Term>) -> Result<Sort> {
        let ty = self.infer(term, context)?;
        let Term::Pi {
            domain: actual,
            codomain,
        } = self.normal(&ty)?
        else {
            return fail("expected a type family with the specified domain");
        };
        if !self.equal(&actual, domain, context)? {
            return fail("expected a type family with the specified domain");
        }
        context.push(domain.clone());
        let result = self.codomain_sort(&codomain, context);
        context.pop();
        result
    }
    /// The motive of a data eliminator abstracts over every declared index of
    /// the family and then over the eliminated value itself.
    fn check_motive(
        &mut self,
        motive: &Term,
        info: &DataInfo,
        levels: &[Level],
        context: &mut Vec<Term>,
    ) -> Result<Sort> {
        let base = context.len();
        let ty = self.infer(motive, context)?;
        let mut ty = self.normal(&ty)?;
        for param in &info.params {
            let Term::Pi { domain, codomain } = ty else {
                context.truncate(base);
                return fail(
                    "the motive must abstract over every data index and then the eliminated value",
                );
            };
            if !self.equal(&domain, param, context)? {
                context.truncate(base);
                return fail("the motive's index domain does not match the data declaration");
            }
            context.push(param.clone());
            ty = *codomain;
        }
        let Term::Pi { domain, codomain } = ty else {
            context.truncate(base);
            return fail("the motive must take the eliminated value as its final argument");
        };
        let application = self.application(
            Term::Global(info.name.clone(), levels.to_vec()),
            (0..info.params.len()).rev().map(Term::Var),
        )?;
        if !self.equal(&domain, &application, context)? {
            context.truncate(base);
            return fail(
                "the motive's value domain must be the data family applied to its indices",
            );
        }
        context.push(application);
        let result = self.codomain_sort(&codomain, context);
        context.truncate(base);
        result
    }
    /// The dependent branch type of one constructor:
    ///
    /// ```text
    /// (pi1..pik) -> (locals)
    ///   -> (fields with an induction hypothesis after each direct recursive
    ///       field) -> motive (result indices) (c pi.. locals fields)
    /// ```
    fn branch_type(
        &mut self,
        info: &DataInfo,
        levels: &[Level],
        constructor: &ConstructorInfo,
        motive: &Term,
    ) -> Result<Term> {
        let k = info.params.len();
        let mut steps: Vec<Term> = Vec::new();
        let mut locals: Vec<usize> = Vec::new();
        let mut context_len = k;
        for local in &constructor.locals {
            steps.push(local.clone());
            locals.push(context_len);
            context_len += 1;
        }
        let mut fields: Vec<usize> = Vec::new();
        for (index, field) in constructor.fields.iter().enumerate() {
            let previous = fields.clone();
            let arguments = (0..k)
                .chain(locals.iter().copied())
                .chain(previous.iter().copied())
                .map(|position| variable(context_len, position))
                .collect::<Result<Vec<_>>>()?;
            steps.push(self.rewrite_outer(field, &arguments)?);
            fields.push(context_len);
            context_len += 1;
            if constructor.recursive[index] {
                let (_, indices) = spine(field);
                let arguments = (0..k)
                    .chain(locals.iter().copied())
                    .chain(previous.iter().copied())
                    .map(|position| variable(context_len, position))
                    .collect::<Result<Vec<_>>>()?;
                let mut hypothesis = self.shift(motive, context_len, 0)?;
                for index in indices {
                    hypothesis = Term::app(hypothesis, self.rewrite_outer(index, &arguments)?);
                }
                hypothesis = Term::app(hypothesis, Term::Var(0));
                steps.push(hypothesis);
                context_len += 1;
            }
        }
        let arguments = (0..k)
            .chain(locals.iter().copied())
            .chain(fields.iter().copied())
            .map(|position| variable(context_len, position))
            .collect::<Result<Vec<_>>>()?;
        let mut body = self.shift(motive, context_len, 0)?;
        for result in &constructor.result {
            body = Term::app(body, self.rewrite_outer(result, &arguments)?);
        }
        let constructed = self.application(
            Term::Global(constructor.name.clone(), levels.to_vec()),
            arguments.iter().cloned(),
        )?;
        body = Term::app(body, constructed);
        let mut branch = body;
        for step in steps.iter().rev() {
            branch = Term::pi(step.clone(), branch);
        }
        for param in info.params.iter().rev() {
            branch = Term::pi(param.clone(), branch);
        }
        Ok(branch)
    }
    fn infer(&mut self, term: &Term, context: &mut Vec<Term>) -> Result<Term> {
        self.step(|e| match term {
            Term::Var(index) => {
                let position = context
                    .len()
                    .checked_sub(1)
                    .and_then(|last| last.checked_sub(*index));
                let ty = position
                    .and_then(|i| context.get(i))
                    .ok_or_else(|| Error(format!("unbound variable index {index}")))?;
                e.shift(
                    ty,
                    index
                        .checked_add(1)
                        .ok_or_else(|| Error("variable index overflow".into()))?,
                    0,
                )
            }
            Term::Global(name, levels) => {
                e.global_levels(name, levels)?;
                let ty = match e.definitions.get(name) {
                    Some(Global::Definition(definition)) => definition.ty.clone(),
                    Some(Global::Data { ty, .. } | Global::Constructor { ty, .. }) => ty.clone(),
                    None => return Err(Error(format!("unknown kernel global '{name}'"))),
                };
                e.instantiate(&ty, levels)
            }
            Term::Universe(level) => {
                e.level_in_scope(level)?;
                Ok(Term::Universe(level.succ()?))
            }
            Term::Prop => Ok(Term::universe(0)),
            Term::Pi { domain, codomain } => {
                let left = e.sort(domain, context)?;
                let right = e.under(context, domain, |e, c| e.sort(codomain, c))?;
                Ok(match right {
                    // Impredicative Prop: a function into a proposition is a
                    // proposition, regardless of the domain's universe.
                    Sort::Prop => Term::Prop,
                    Sort::Type(level) => Term::Universe(left.level().max(&level)),
                })
            }
            Term::Lam { domain, body } => {
                e.sort(domain, context)?;
                let result = e.under(context, domain, |e, c| e.infer(body, c))?;
                Ok(Term::pi(*domain.clone(), result))
            }
            Term::App(function, argument) => {
                let ty = e.infer(function, context)?;
                let Term::Pi { domain, codomain } = e.normal(&ty)? else {
                    return fail("cannot apply a non-function");
                };
                e.check(argument, &domain, context)?;
                e.substitute(&codomain, argument, 0)
            }
            Term::Nat => Ok(Term::universe(0)),
            Term::Scalar(_) => Ok(Term::universe(0)),
            Term::ScalarLiteral(value) => {
                // Literals are canonical and carry no computation. Charging one
                // unit keeps inference/normalization inside the shared budget.
                e.charge(1)?;
                Ok(Term::Scalar(value.scalar()))
            }
            Term::Literal(value) => {
                e.charge(value.work())?;
                Ok(Term::Nat)
            }
            Term::Zero => Ok(Term::Nat),
            Term::Succ(value) => {
                e.check(value, &Term::Nat, context)?;
                Ok(Term::Nat)
            }
            Term::Eq { ty, left, right } => {
                let universe = e.sort(ty, context)?;
                e.check(left, ty, context)?;
                e.check(right, ty, context)?;
                // Equality stays Type-valued in this bootstrap. It lives in
                // the carrier's universe (`Prop` carriers contribute level 0),
                // so equality proofs are ordinary logical data rather than
                // automatically proof-irrelevant Prop inhabitants. Prop data
                // declarations provide explicitly irrelevant propositions.
                Ok(Term::Universe(universe.level()))
            }
            Term::Refl { ty, value } => {
                e.sort(ty, context)?;
                e.check(value, ty, context)?;
                Ok(Term::eq(*ty.clone(), *value.clone(), *value.clone()))
            }
            Term::NatElim {
                motive,
                zero,
                step,
                value,
            } => {
                e.family(motive, &Term::Nat, context)?;
                e.check(value, &Term::Nat, context)?;
                e.check(zero, &Term::app(*motive.clone(), Term::Zero), context)?;
                let motive1 = e.shift(motive, 1, 0)?;
                let motive2 = e.shift(motive, 2, 0)?;
                let step_ty = Term::pi(
                    Term::Nat,
                    Term::pi(
                        Term::app(motive1, Term::Var(0)),
                        Term::app(motive2, Term::succ(Term::Var(1))),
                    ),
                );
                e.check(step, &step_ty, context)?;
                Ok(Term::app(*motive.clone(), *value.clone()))
            }
            Term::Transport {
                ty,
                from,
                to,
                motive,
                proof,
                value,
            } => {
                e.sort(ty, context)?;
                e.check(from, ty, context)?;
                e.check(to, ty, context)?;
                e.family(motive, ty, context)?;
                e.check(
                    proof,
                    &Term::eq(*ty.clone(), *from.clone(), *to.clone()),
                    context,
                )?;
                e.check(value, &Term::app(*motive.clone(), *from.clone()), context)?;
                Ok(Term::app(*motive.clone(), *to.clone()))
            }
            Term::EqElim {
                ty,
                left,
                right,
                motive,
                refl,
                proof,
            } => {
                e.sort(ty, context)?;
                e.check(left, ty, context)?;
                e.check(right, ty, context)?;
                let motive_type = e.infer(motive, context)?;
                let motive_type = e.normal(&motive_type)?;
                let Term::Pi {
                    domain: value_domain,
                    codomain,
                } = motive_type
                else {
                    return fail("Eq.elim's motive must take a value and an equality proof");
                };
                if !e.equal(&value_domain, ty, context)? {
                    return fail("Eq.elim's motive value domain must be the carrier type");
                }
                let Term::Pi {
                    domain: equality_domain,
                    codomain,
                } = *codomain
                else {
                    return fail("Eq.elim's motive must take an equality proof after the value");
                };
                let expected = Term::eq(
                    e.shift(ty, 1, 0)?,
                    e.shift(left, 1, 0)?,
                    Term::Var(0),
                );
                if !e.equal(&equality_domain, &expected, context)? {
                    return fail(
                        "Eq.elim's motive equality domain must connect the left value to its argument",
                    );
                }
                context.push((*value_domain).clone());
                context.push((*equality_domain).clone());
                let result = e.codomain_sort(&codomain, context);
                context.pop();
                context.pop();
                result?;
                let refl_type = Term::app(
                    Term::app(*motive.clone(), *left.clone()),
                    Term::refl(*ty.clone(), *left.clone()),
                );
                e.check(refl, &refl_type, context)?;
                e.check(
                    proof,
                    &Term::eq(*ty.clone(), *left.clone(), *right.clone()),
                    context,
                )?;
                Ok(Term::app(
                    Term::app(*motive.clone(), *right.clone()),
                    *proof.clone(),
                ))
            }
            Term::IndElim {
                data,
                motive,
                branches,
                scrutinee,
            } => {
                let scrutinee_type = e.infer(scrutinee, context)?;
                let normalized = e.normal(&scrutinee_type)?;
                let (head, arguments) = spine(&normalized);
                // The scrutinee's type fixes the family's universe levels;
                // the inferred type's levels were checked when it was formed.
                let levels = match head {
                    Term::Global(name, levels) if name == data => levels.clone(),
                    _ => {
                        return fail(format!(
                            "eliminator for '{data}' requires a scrutinee of that data type"
                        ));
                    }
                };
                let info = e.data_at(data, &levels)?;
                if arguments.len() != info.params.len() {
                    return fail(format!(
                        "eliminator for '{data}' found {} index arguments, expected {}",
                        arguments.len(),
                        info.params.len()
                    ));
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| (*argument).clone())
                    .collect::<Vec<_>>();
                let motive_sort = e.check_motive(motive, &info, &levels, context)?;
                if info.prop && !motive_sort.is_prop() {
                    return fail(format!(
                        "large elimination from proposition '{data}' is not allowed: the motive must return a proposition"
                    ));
                }
                if branches.len() != info.constructors.len() {
                    return fail(format!(
                        "eliminator for '{data}' requires {} constructor branches, found {}",
                        info.constructors.len(),
                        branches.len()
                    ));
                }
                for (branch, constructor) in branches.iter().zip(&info.constructors) {
                    let expected = e.branch_type(&info, &levels, constructor, motive)?;
                    e.check(branch, &expected, context)?;
                }
                let mut result = (**motive).clone();
                for argument in arguments {
                    result = Term::app(result, argument);
                }
                Ok(Term::app(result, (**scrutinee).clone()))
            }
        })
    }
}
