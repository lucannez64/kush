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
    pub attributes: Vec<Node<String>>,
    pub item: Item,
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
    pub ty: Type,
    pub span: Span,
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
    /// The receiver type placeholder `Self` inside a trait/impl method
    /// signature. It is replaced by the concrete impl target before runtime
    /// type lowering.
    SelfType,
    /// `dyn Trait` or `dyn Trait<Arguments>`: a closed-world trait object.
    ///
    /// The object type is represented as the normalized union of every
    /// concrete impl target for the trait. Only traits with a finite, nonempty
    /// set of concrete impls and object-safe owned-receiver methods admit this
    /// type; the checker diagnoses every other use.
    Dyn(Box<Type>),
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
    Lambda(Box<Lambda>),
    Specialize {
        callee: Box<Expr>,
        arguments: Vec<Type>,
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
    Record {
        ty: Box<Expr>,
        fields: Vec<(String, Expr)>,
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
/// Parameter and result types are mandatory. A lambda that captures no outer
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
    Rest,
    Constructor {
        path: Vec<String>,
        fields: Vec<Pattern>,
    },
    Record {
        path: Vec<String>,
        fields: Vec<(String, Pattern)>,
    },
    /// `Type @ pattern`: narrow one heterogeneous-union alternative.
    Type {
        ty: Type,
        inner: Box<Pattern>,
    },
    Or(Vec<Pattern>),
}
