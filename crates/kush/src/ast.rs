use crate::{Span, lexer::Kind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<T> {
    pub kind: T,
    pub span: Span,
}
impl<T> Node<T> {
    pub fn new(kind: T, span: Span) -> Self {
        Self { kind, span }
    }
}
pub type Type = Node<TypeKind>;

/// One trait bound of a `dyn` object type: the trait path (a `Named` type whose
/// span resolves to the trait) and explicit associated-type bindings, as in
/// `Convert<i64, Out = Text>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynBound {
    pub trait_ref: Type,
    pub bindings: Vec<(String, Type)>,
}

impl DynBound {
    /// Every syntactic type inside the bound: the trait path, then each bound
    /// associated-type value.
    pub fn types(&self) -> impl Iterator<Item = &Type> {
        std::iter::once(&self.trait_ref).chain(self.bindings.iter().map(|(_, ty)| ty))
    }
}

/// Every syntactic type inside a `dyn` bound list.
pub fn dyn_types(bounds: &[DynBound]) -> impl Iterator<Item = &Type> {
    bounds.iter().flat_map(DynBound::types)
}
pub type Expr = Node<ExprKind>;
pub type Pattern = Node<PatternKind>;
pub type Item = Node<ItemKind>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub items: Vec<Declaration>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    pub public: bool,
    pub attributes: Vec<Attribute>,
    pub item: Item,
}
/// One `#[name]` or `#[name("argument")]` declaration attribute.
///
/// The argument is a validated single string literal. Only `foreign` currently
/// consumes it: `#[foreign("release_symbol")] struct Handle {}` declares an
/// opaque foreign resource whose exactly-once release calls that C symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    pub kind: String,
    pub argument: Option<String>,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemKind {
    Module(Vec<String>),
    Use(Vec<String>),
    Function(Function),
    Struct {
        name: String,
        /// Erased lifetime parameters, written before ordinary generics.
        lifetimes: Vec<Lifetime>,
        generics: Vec<Generic>,
        fields: Vec<Field>,
    },
    Enum {
        total: bool,
        name: String,
        generics: Vec<Generic>,
        variants: Vec<Variant>,
    },
    /// `prop Name<P: Prop, ...> { ... }`: positive inductive data whose family
    /// lives in `Prop`. Constructors are checked, erased, and eliminated only
    /// into propositions.
    Prop {
        name: String,
        generics: Vec<Generic>,
        variants: Vec<Variant>,
    },
    Alias {
        name: String,
        /// Erased lifetime parameters of a transparent type alias.
        lifetimes: Vec<Lifetime>,
        generics: Vec<Generic>,
        ty: Type,
    },
    /// `effect Name: P -> R;` declares the payload/result signature of an
    /// effect operation. A lexical `handle Name` may serve direct performs;
    /// the declaration additionally lets a called function perform the
    /// operation through the dynamic one-shot handler stack.
    Effect {
        name: String,
        parameter: Type,
        result: Type,
    },
    /// `effect row Name = { io, alloc };` declares a named finite effect row.
    ///
    /// The alias is transparent and expands to the union of its effects wherever
    /// an effect row is written. It is not a runtime type, cannot take
    /// arguments, and may name other row aliases; cycles are rejected.
    EffectRow {
        name: String,
        effects: Vec<Type>,
    },
    /// `trait Name<T> { type Item; const LIMIT: i64; fn method(self: Self, ...) -> T ! { ... }; }`.
    ///
    /// Traits are static dispatch contracts. A method signature ends in
    /// `;` and requires an explicit impl; a method written with a block is a
    /// default body that an impl inherits when it omits the method. Trait type
    /// parameters are ordinary type/Nat/Grade/Effects parameters that form
    /// part of the trait's static identity. Associated types and constants add
    /// checked projection and per-impl substitution. Trait objects are a
    /// closed-world dynamic representation; see the checker.
    Trait {
        name: String,
        generics: Vec<Generic>,
        /// Associated type and constant declarations. An impl must provide a
        /// value for every associated type and for every constant without a
        /// default.
        associated: Vec<Associated>,
        methods: Vec<Method>,
    },
    /// `algebra Name { elements { A = 0, B = 1 } zero = A; one = B; }`.
    ///
    /// A restricted user-defined grade algebra: a finite set of named grade
    /// values embedded in the builtin extended-natural usage semiring. Elements
    /// map to concrete natural/`many` values, so `+` and `*` are the checked
    /// builtin operations; the checker validates closure, identities,
    /// associativity, commutativity, distributivity, and annihilation by
    /// exhaustive enumeration of the declared finite carrier.
    GradeAlgebra(GradeAlgebra),
    /// `impl Type { ... }` or `impl Trait<Arguments> for Type { ... }`.
    ///
    /// The `trait_path` is a named type node whose arguments are the concrete
    /// trait specialization; the resolver records its binding, and it must
    /// resolve to a declared trait.
    Impl {
        /// Type parameters of a generic or blanket impl, as in
        /// `impl<T> Show for Wrapper<T>` or `impl<T: Show> Show for T`.
        /// Lifetime parameters remain unsupported on impl headers.
        generics: Vec<Generic>,
        trait_path: Option<Type>,
        self_ty: Type,
        /// Associated type and constant definitions. In a trait impl every
        /// declared associated item must be defined, and no extra item may
        /// appear. Inherent impls may define associated constants for the
        /// nominal target type.
        associated: Vec<Associated>,
        methods: Vec<Method>,
    },
}
/// One associated item inside a trait declaration or an impl block.
///
/// An associated type projects through `Self::Name` or through a bounded
/// generic parameter `T::Name`. An associated constant is a compile-time
/// scalar; its value is substituted wherever it is named, so it has no runtime
/// storage or accessor function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Associated {
    /// `type Name;` in a trait or `type Name = Type;` in an impl.
    Type {
        name: String,
        value: Option<Type>,
        span: Span,
    },
    /// `const NAME: Type;` in a trait or `const NAME: Type = value;` in an
    /// impl. A trait declaration may also provide a default value.
    Const {
        name: String,
        ty: Type,
        value: Option<Expr>,
        span: Span,
    },
}
impl Associated {
    pub fn name(&self) -> &str {
        match self {
            Associated::Type { name, .. } | Associated::Const { name, .. } => name,
        }
    }
    pub fn span(&self) -> Span {
        match self {
            Associated::Type { span, .. } | Associated::Const { span, .. } => *span,
        }
    }
}
/// One method declaration inside a trait or impl. `public` is meaningful only
/// on an inherent/trait impl method; trait method declarations reject an
/// explicit visibility because they inherit the trait's visibility.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Method {
    pub public: bool,
    pub function: Function,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Generic {
    pub name: String,
    pub bound: Option<Type>,
    /// Concrete effects this binder must never be specialized with, written
    /// `<e: Effects - alloc>` or `<e: Effects - (alloc | suspend)>`.
    ///
    /// This is a bound on valid specialization, not row subtraction and not an
    /// effect handler: a specialization that includes any excluded effect is
    /// rejected, and the body may still perform every effect its row declares.
    /// Only executable function and method effect binders accept it.
    pub excludes: Option<Type>,
    /// Concrete effects this binder must always be specialized with, written
    /// `<e: Effects + io>` or `<e: Effects + (io | alloc)>`.
    ///
    /// This is a lower bound on valid specialization: a solution whose row
    /// omits an included effect is rejected. It is not row subtraction and it
    /// does not make the body perform the effect; the declared function row
    /// still determines observability.
    pub includes: Option<Type>,
    pub span: Span,
}
/// A `grade algebra` declaration. The finite carrier and both operations are
/// explicit; the grade pass validates the semiring laws by enumeration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GradeAlgebra {
    pub name: String,
    pub elements: Vec<GradeElement>,
    pub zero: String,
    pub one: String,
    pub add: Vec<GradeEquation>,
    pub mul: Vec<GradeEquation>,
}
/// One named element of a `grade algebra` declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GradeElement {
    pub name: String,
    pub span: Span,
}
/// One `left op right = result` row of a grade algebra operation table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GradeEquation {
    pub left: String,
    pub right: String,
    pub result: String,
    pub span: Span,
}
/// A declared lifetime parameter. Lifetimes are erased at runtime and are
/// tracked only by the borrow checker; they are distinct from type, natural,
/// grade, and effect generics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lifetime {
    pub name: String,
    pub span: Span,
    /// Explicit outlives bounds written after `:`, as in `'long: 'short`.
    /// The declaration outlives every bound target. Function signatures are the
    /// only declaration form that currently accepts bounds; records and aliases
    /// reject them with a diagnostic.
    pub bounds: Vec<LifetimeBound>,
}

/// One target of an outlives bound: in `'long: 'short`, `'short` is the bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LifetimeBound {
    pub name: String,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    pub name: String,
    /// For a structural conversion `value as struct { b: i64 from a }`: the
    /// source field name. `None` means the target name is also the source name.
    /// It is metadata for one explicit conversion, never part of the row's
    /// runtime identity.
    pub source: Option<String>,
    pub ty: Type,
    pub span: Span,
    /// `pub` on a struct field: visible outside the struct's module
    /// (FIELD-PRIVACY). Ignored for enum payloads and structural rows.
    pub public: bool,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variant {
    pub name: String,
    /// Constructor-local binders. These are universally quantified for this
    /// constructor only; they are distinct from the family's uniform/index
    /// parameters and may vary the constructor's result indices.
    pub locals: Vec<Generic>,
    pub payload: Payload,
    pub result: Option<Type>,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Payload {
    Unit,
    Tuple(Vec<Type>),
    /// Named logical constructor fields, written `(name: T, ...)`. Names bind
    /// in later field types and in the constructor result indices.
    Fields(Vec<Field>),
    Record(Vec<Field>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub total: bool,
    pub name: String,
    /// Lifetime parameters declared `< 'a, 'b >`, before ordinary generics.
    pub lifetimes: Vec<Lifetime>,
    pub generics: Vec<Generic>,
    pub parameters: Vec<Parameter>,
    pub result: Type,
    pub effects: Vec<Type>,
    pub body: Option<Block>,
    /// `foreign "symbol" fn ...;`: the exact C ABI symbol imported from the
    /// linked static libraries/objects. Foreign declarations have no body and
    /// may only be called directly, never used as first-class values.
    pub foreign: Option<String>,
    /// `export "symbol" fn ... { .. }` (KUSH-RUST-EXPORT): also callable from
    /// C and Rust under this exact symbol when built with `--lib`.
    pub export: Option<String>,
    /// `ensures` postconditions (ENSURES), checked at every return and
    /// available to callers as facts.
    pub ensures: Vec<Ensures>,
}
/// One `ensures` clause: `ensures [guard =>] { proposition }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ensures {
    pub guard: EnsuresGuard,
    /// The `{ .. }` proposition. It may mention parameters, `result`, and the
    /// guard's binders, with field paths (`p.x`) and `value is Variant`.
    pub body: Expr,
    /// Binder span of the implicit `result` name.
    pub result_span: Span,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnsuresGuard {
    /// `ensures { P }`
    Always,
    /// `ensures result => { P }` (a `Bool` result) or `!result => { P }`.
    Result(bool),
    /// `ensures Variant(x, ..) => { P }` (an enum result).
    Variant {
        name: String,
        binders: Vec<(String, Span)>,
        span: Span,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub erased: bool,
    pub name: String,
    pub ty: Type,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    Named {
        path: Vec<String>,
        arguments: Vec<Type>,
    },
    Integer(String),
    /// A boolean literal in a type/index position, such as `IsTrue<true>`.
    Bool(bool),
    Tuple(Vec<Type>),
    Slice(Box<Type>),
    /// `[T; length]`. The second component is a compile-time length expression
    /// (literals, natural/const binders, admitted total logical calls, and
    /// checked integer arithmetic). It is evaluated during executable type
    /// lowering; it is never a runtime value.
    Array(Box<Type>, Box<Type>),
    /// `struct { name: Type, ... }`: an anonymous structural record type with a
    /// canonical field row. Unlike a nominal declaration it has no module-level
    /// name; two occurrences with the same fields intern to one layout.
    /// `open` is set by a trailing `..`: the annotation accepts any record
    /// containing these fields, with unmentioned fields erased at the call
    /// boundary. It is a documented erased-row contract, not row unification.
    Structural {
        fields: Vec<Field>,
        /// A trailing `..` (erased open row) or `..r` (a row variable that
        /// preserves the unmentioned fields through monomorphization).
        open: bool,
        /// `Some(row)` for `..row`: the row variable must be a declared type
        /// generic bound to a concrete structural row at each specialization.
        row: Option<Box<Type>>,
    },
    Borrow {
        /// Optional explicit lifetime, as in `&'a [T]`.
        lifetime: Option<String>,
        mutable: bool,
        inner: Box<Type>,
    },
    /// A lifetime argument in a named type application, as in
    /// `Window<'a, i64>`. It is not a runtime type: it is erased and only
    /// participates in static borrow checking.
    Lifetime(String),
    /// `cap Op ! {e}`: a second-class capability for the declared operation
    /// `Op` whose handler has row `e`. Only a named function parameter type.
    Capability {
        operation: String,
        effects: Vec<Type>,
    },
    /// The receiver type placeholder `Self` inside a trait/impl method
    /// signature. It is replaced by the concrete impl target before runtime
    /// type lowering.
    SelfType,
    /// An omitted lambda parameter or result type (`fn(x) { ... }`), or, as
    /// the only element of a lambda's effect list, an omitted effect row. The
    /// checker fills it from the expected arrow, a generic call, or the
    /// binding's first use, and otherwise asks for the annotation. It never
    /// appears outside a lambda.
    Infer,
    /// `dyn Trait`, `dyn Trait<Arguments, Out = T>`, or `dyn A + B`: a trait
    /// object. Each bound names one trait with its trait arguments and any
    /// explicit associated-type bindings. The checker chooses the closed-world
    /// union or the dynamic fat-object representation and diagnoses every
    /// unsupported use.
    Dyn(Vec<DynBound>),
    Function {
        /// Lifetimes bound by the arrow itself, as in `fn<'a>(&'a [T]) -> &'a [T]`.
        /// The arrow is polymorphic over them: every call picks fresh ones.
        lifetimes: Vec<Lifetime>,
        parameters: Vec<TypeParameter>,
        result: Box<Type>,
        effects: Vec<Type>,
        /// `once fn(...)`: an owning, at-most-once callable closure type.
        /// Plain `fn(...)` is a noncapturing, copyable function pointer.
        call_once: bool,
        /// `linear once fn(...)`: a once callable whose captured linear
        /// obligations must be consumed by exactly one call. It is a linear
        /// value and may not be implicitly or explicitly dropped.
        call_linear: bool,
    },
    Binary {
        op: Kind,
        left: Box<Type>,
        right: Box<Type>,
    },
    Graded {
        inner: Box<Type>,
        grade: Box<Type>,
    },
    /// `{ expression }`: a proposition over runtime values, used by erased
    /// proof parameters. It has no runtime representation.
    Predicate(Box<Expr>),
}
/// A named parameter binds in later parameters and the result type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParameter {
    pub name: Option<String>,
    pub ty: Type,
    pub span: Span,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub tail: Option<Box<Expr>>,
    pub span: Span,
}
// `Let` keeps its initializer inline because the executable checker and
// resolver visit it in place; boxing every branch would obscure ownership and
// span handling for no functional gain.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Let {
        mutable: bool,
        pattern: Pattern,
        ty: Option<Type>,
        value: Expr,
        span: Span,
    },
    Expr(Expr),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Name(String),
    Integer(String),
    /// A decimal float literal. The executable type comes from context; the
    /// default is `f64`.
    Float(String),
    String(String),
    Char(char),
    Bool(bool),
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    /// Anonymous structural record literal: `struct { a: value, b: value }`.
    /// The checked value has the canonical (name-sorted) structural row built
    /// from the field expressions.
    StructuralLiteral(Vec<(String, Expr)>),
    Block(Block),
    Unary {
        op: Kind,
        mutable: bool,
        operand: Box<Expr>,
    },
    Binary {
        op: Kind,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
    },
    /// A lexically scoped, one-shot tail-resumptive effect handler.
    ///
    /// `handle Op: P -> R with h { body }` binds `h` for direct `perform Op(v)`
    /// expressions inside `body`. `h` has the callable contract
    /// `fn(P, linear once fn(R) -> R) -> R` (or the corresponding `once` /
    /// `linear once` mode); the resumption token must be invoked exactly once
    /// and supplies the operation's result. There is no captured continuation
    /// and no multishot operation.
    Handle {
        operation: String,
        parameter: Box<Type>,
        result: Box<Type>,
        handler: Box<Expr>,
        body: Box<Block>,
        /// `handle Op: P -> R as op with h { .. }`: a second-class capability
        /// bound to this activation for the body (EFF-CAP-LEXICAL).
        capability: Option<(String, crate::Span)>,
    },
    /// `perform Op(value)`: call the innermost lexical handler for `Op`.
    Perform {
        operation: String,
        value: Box<Expr>,
    },
    Lambda(Box<Lambda>),
    Specialize {
        callee: Box<Expr>,
        arguments: Vec<Type>,
    },
    /// `value as struct { target: Type from source, ... }`: an explicit
    /// structural conversion with field renaming. Renaming is conversion
    /// metadata, never part of a structural row's runtime identity.
    Cast {
        value: Box<Expr>,
        ty: Type,
    },
    /// `value is Variant`: only inside an `ensures` proposition (ENSURES).
    Is {
        value: Box<Expr>,
        variant: String,
    },
    Field {
        value: Box<Expr>,
        name: String,
    },
    Index {
        value: Box<Expr>,
        index: Box<Expr>,
    },
    /// `value[start..end]` with an omitted start/end meaning the corresponding
    /// end of the owner. This denotes a borrowed slice view, not a copy.
    Slice {
        value: Box<Expr>,
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
    },
    Try(Box<Expr>),
    Return(Option<Box<Expr>>),
    If {
        condition: Box<Expr>,
        then: Block,
        otherwise: Option<Box<Expr>>,
    },
    Match {
        value: Box<Expr>,
        arms: Vec<Arm>,
    },
    /// `Path { field: value, ... }`. `ty` is the path (or specialized path) expression.
    /// `Path { field: value, ..base }` (STRUCT-UPDATE) takes the other fields
    /// from `base`.
    Record {
        ty: Box<Expr>,
        fields: Vec<(String, Expr)>,
        base: Option<Box<Expr>>,
    },
    While {
        condition: Box<Expr>,
        body: Block,
    },
    Loop(Block),
    Break(Option<Box<Expr>>),
    Continue,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Arm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

/// An explicitly typed lambda expression:
///
/// ```text
/// fn(x: i64, y: i64) -> i64 ! {panic} { x + y }
/// ```
///
/// Parameter, result and effect annotations may be omitted
/// ([`TypeKind::Infer`]); the checker infers them locally. A lambda that captures no outer
/// runtime binding is a copyable function pointer (`fn(...)`). A lambda that
/// captures affine owned storage is an owning once-consuming closure
/// (`once fn(...)`); its environment is moved into the closure exactly once.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lambda {
    pub parameters: Vec<Parameter>,
    pub result: Type,
    pub effects: Vec<Type>,
    pub body: Block,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternKind {
    Wildcard,
    Name(Vec<String>),
    Integer(String),
    String(String),
    Char(char),
    Bool(bool),
    Tuple(Vec<Pattern>),
    Slice(Vec<Pattern>),
    /// `..` or `..name` inside a slice/DynArray pattern. The optional name
    /// binds the remaining elements (a `DynArray<T, capacity>` copy).
    Rest(Option<String>),
    Constructor {
        path: Vec<String>,
        fields: Vec<Pattern>,
    },
    Record {
        path: Vec<String>,
        fields: Vec<(String, Pattern)>,
    },
    /// Anonymous structural pattern `struct { a, b: p, .. }`. It matches any
    /// record value that has the named fields; omitted and `..` fields are
    /// ignored (and dropped by the ordinary pattern cleanup rules).
    Structural {
        fields: Vec<(String, Pattern)>,
        rest: bool,
    },
    /// `Type @ pattern`: narrow one heterogeneous-union alternative.
    Type {
        ty: Type,
        inner: Box<Pattern>,
    },
    Or(Vec<Pattern>),
}
