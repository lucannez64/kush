//! Checked executable value subset: monomorphic functions, generic inline enums,
//! and normalized heterogeneous union/intersection value types. Logical proof terms never
//! enter this IR; only this module can construct a checked executable.
pub use crate::eval::MemoryStats;
use crate::{
    Diagnostic, Span, ast,
    coverage::Coverage,
    grades::{self, Grade},
    kernel::{Scalar, Term},
    lexer::Kind,
    resolve::{self, BindingId, BindingKind, Resolution},
    runtime_types::{Enum, FunctionType, ResultShape, Types},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, Diagnostic>;
pub(crate) const PANIC: u8 = 1;
pub(crate) const IO: u8 = 2;
pub(crate) const ALLOC: u8 = 4;
pub(crate) const SUSPEND: u8 = 8;
pub(crate) const EFFECT_BITS: u8 = PANIC | IO | ALLOC | SUSPEND;
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Type {
    I64,
    /// A fixed-width integer other than `i64` (which keeps its own variant).
    Int(crate::int::IntKind),
    /// An IEEE-754 binary32/binary64 value, stored as its raw bits in one word.
    Float(crate::float::FloatKind),
    /// A Unicode scalar value, stored as its code point.
    Char,
    Bool,
    Unit,
    Never,
    Enum(usize),
    Bytes,
    /// A validated UTF-8 text buffer. It has the same one-word native
    /// representation as `Bytes`, but the checker never treats arbitrary bytes
    /// as text: construction is restricted to literals and checked conversion.
    String,
    /// A shared borrowed UTF-8 text view: `&'a str`. The four-word runtime
    /// representation is the same descriptor as a slice view with a byte stride
    /// of one, but the static type is distinct: it is never an element slice,
    /// cannot be made mutable, and always covers a contiguous range of a
    /// validated `String` at Unicode scalar boundaries.
    Str,
    Stdin,
    Stdout,
    Box(usize),
    /// Immutable borrowed owner/reference handle, one word.
    Ref(usize),
    /// Exclusive borrowed nominal-record reference, one word. It is affine: a
    /// `&mut` reference is moved rather than copied and cannot be stored in a
    /// local, returned, or captured by this call-scoped subset.
    RefMut(usize),
    /// A transparent wrapper used only inside a container pointee. It carries
    /// the erased lifetime label declared for a reference element, has exactly
    /// the inner type's runtime representation, and never appears as the type
    /// of a user-visible expression.
    Annotated(usize, u32),
    /// Growable owned vector of a pointee element type.
    Vec(usize),
    /// Immutable borrowed slice view: `(data pointer, length, stride, byte flag)`.
    /// The pointee is the element type. Slices never own their storage.
    Slice(usize),
    /// Exclusive mutable borrowed slice view, same four-word representation.
    /// Mutable views are move-only capabilities.
    SliceMut(usize),
    /// A strict, nonempty subset of an enum's variants (bit per tag). Same
    /// runtime layout as `Enum(id)`; it is a subtype of every superset.
    Variants(usize, u64),
    /// A normalized heterogeneous union. Runtime layout is one discriminator
    /// word followed by the widest alternative; see `runtime_types::UnionType`.
    Union(usize),
    /// A noncapturing, copyable function pointer. One word: the code address.
    Fn(usize),
    /// An owning, at-most-once callable closure. Two words: code address and
    /// an owned environment pointer. The environment header stores its drop
    /// function, so captured storage is released without GC or refcounting.
    /// `function_types[id].linear` marks the linear-once mode: the callable
    /// itself must be consumed by exactly one call.
    Once(usize),
    /// An opaque, affine structured-task handle. One word. Handles are created
    /// only inside a `Task.scope` and may not escape it through data or results.
    Task(usize),
    /// Owning bump-allocator region handle, one word. Values allocated through
    /// `Arena.alloc` retain the region, so the arena value may be dropped while
    /// its boxes remain live.
    Arena,
    /// An owning box allocated inside an `Arena`. One word: a payload pointer
    /// whose preceding header retains the region. Its payload is destroyed
    /// before the region reference is released.
    ArenaBox(usize),
}
impl Type {
    /// The admitted symbolic scalar carrier of a runtime type, if any. Only
    /// these copyable machine values may appear in erased proof indices.
    pub(crate) fn scalar_carrier(self) -> Option<Scalar> {
        match self {
            Type::I64 => Some(Scalar::I64),
            Type::Bool => Some(Scalar::Bool),
            Type::Unit => Some(Scalar::Unit),
            _ => None,
        }
    }
    /// The inline layout index for enums, records, and variant subsets.
    pub(crate) fn layout(self) -> Option<usize> {
        match self {
            Type::Enum(id) | Type::Variants(id, _) => Some(id),
            _ => None,
        }
    }
    /// Forget variant refinements (used for storage and ownership).
    pub(crate) fn full(self) -> Type {
        match self {
            Type::Variants(id, _) => Type::Enum(id),
            ty => ty,
        }
    }
    /// The integer kind of `i64` and the other fixed-width integers.
    pub(crate) fn int_kind(self) -> Option<crate::int::IntKind> {
        match self {
            Type::I64 => Some(crate::int::IntKind::I64),
            Type::Int(kind) => Some(kind),
            _ => None,
        }
    }
    pub(crate) fn int(kind: crate::int::IntKind) -> Type {
        if kind == crate::int::IntKind::I64 {
            Type::I64
        } else {
            Type::Int(kind)
        }
    }
    /// The floating-point kind of `f32`/`f64` values.
    pub(crate) fn float_kind(self) -> Option<crate::float::FloatKind> {
        match self {
            Type::Float(kind) => Some(kind),
            _ => None,
        }
    }
    pub(crate) fn float(kind: crate::float::FloatKind) -> Type {
        Type::Float(kind)
    }
    pub(crate) fn is_union(self) -> bool {
        matches!(self, Type::Union(_))
    }
    /// Whether this type is any slice view (shared or exclusive).
    pub(crate) fn is_slice(self) -> bool {
        matches!(self, Type::Slice(_) | Type::SliceMut(_))
    }
    /// Whether this type is any borrowed view with slice-style provenance:
    /// a shared or exclusive `&[T]` view, or a borrowed UTF-8 `&str`.
    pub(crate) fn is_view(self) -> bool {
        matches!(self, Type::Slice(_) | Type::SliceMut(_) | Type::Str)
    }
    pub(crate) fn is_mut_slice(self) -> bool {
        matches!(self, Type::SliceMut(_))
    }
    /// The pointee of a borrowed owner or record reference.
    pub(crate) fn ref_pointee(self) -> Option<usize> {
        match self {
            Type::Ref(p) | Type::RefMut(p) => Some(p),
            _ => None,
        }
    }
    pub(crate) fn is_ref(self) -> bool {
        matches!(self, Type::Ref(_) | Type::RefMut(_))
    }
    /// The element pointee of a slice view.
    pub(crate) fn slice_element(self) -> Option<usize> {
        match self {
            Type::Slice(p) | Type::SliceMut(p) => Some(p),
            _ => None,
        }
    }
}
/// A stored kernel hypothesis type that is syntactically a machine carrier.
/// Stored runtime-scalar binders are always exactly this form.
fn normalized_scalar(term: &Term) -> Option<Scalar> {
    match term {
        Term::Scalar(scalar) => Some(*scalar),
        _ => None,
    }
}
#[derive(Debug)]
pub struct Executable {
    pub(crate) functions: Vec<Function>,
    pub(crate) entry: Option<usize>,
    pub(crate) enums: Vec<Enum>,
    pub(crate) pointees: Vec<Type>,
    pub(crate) unions: Vec<crate::runtime_types::UnionType>,
    pub(crate) function_types: Vec<FunctionType>,
    /// Erased lifetime names for reference elements stored inside containers.
    /// Checker-only; the runtime representation is one word and carries no
    /// label. Ownership uses this table to recover a declared element lifetime
    /// from a container's pointee type.
    pub(crate) reference_labels: Vec<String>,
    pub(crate) owned_enums: Vec<bool>,
    pub(crate) linear_enums: Vec<bool>,
    pub(crate) certificates: Vec<crate::facts::Certificate>,
    /// Total logical definitions checked by the kernel and erased from the IR.
    pub(crate) logical_definitions: Vec<String>,
    /// Checked nested in-place maps fused into one traversal. This is a
    /// tooling observation, not a source-language effect or proof fact.
    pub(crate) fusions: usize,
    /// Whether any checked body contains a structured-task operation. Task
    /// programs use the cooperative reference scheduler and buffered host I/O.
    pub(crate) uses_tasks: bool,
    /// Own grade tables for every copyable identity above. Keep this last so
    /// tables remain available while all other program metadata is dropped.
    pub(crate) _grade_algebras: Vec<std::sync::Arc<crate::grades::Algebra>>,
}
#[derive(Debug)]
pub(crate) struct Function {
    pub name: String,
    /// Number of initial locals that are runtime parameters. For a capturing
    /// closure this includes the captured values, which arrive from the owned
    /// environment pointer rather than from ordinary call arguments.
    pub parameters: usize,
    /// Number of leading locals captured from a closure environment. `None`
    /// for ordinary functions, noncapturing lambdas, and pure adapters.
    pub closure: Option<usize>,
    pub locals: Vec<Local>,
    pub result: Type,
    pub body: Block,
    pub span: Span,
    pub resources: Vec<Type>,
    pub local_resources: Vec<Option<usize>>,
    /// Usage grade of each runtime parameter (`None` is unannotated).
    pub parameter_grades: Vec<Option<Grade>>,
    /// Static result-transfer contract. Only `@[1]` on an owning or
    /// intrinsically linear result is representable. It is metadata erased at
    /// runtime: payload types and the ABI are unchanged.
    pub result_grade: Option<Grade>,
    /// Outer borrow lifetime of each runtime parameter, when it is a view/ref.
    pub parameter_lifetimes: Vec<Option<String>>,
    /// Declared outer lifetime of a borrowed slice result.
    pub result_lifetime: Option<String>,
    /// Reflexive-transitive outlives relation declared on the signature.
    /// `(long, short)` means `'long: 'short`: storage named by `long` outlives
    /// storage named by `short`. Reflexivity is implicit.
    pub lifetime_bounds: BTreeSet<(String, String)>,
}
#[derive(Debug, Clone, Copy)]
pub(crate) struct Local {
    pub ty: Type,
    pub mutable: bool,
    /// `@[1]` on an owning/linear value: must be consumed exactly once.
    pub linear: bool,
    /// Explicit usage grade, if the binding was annotated.
    pub grade: Option<Grade>,
    pub span: Span,
}
#[derive(Debug)]
pub(crate) struct Block {
    pub statements: Vec<Statement>,
    pub tail: Option<Box<Expr>>,
    pub ty: Type,
}
#[derive(Debug)]
pub(crate) enum Statement {
    Let(usize, Expr),
    Expr(Expr),
}
#[derive(Debug)]
pub(crate) struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
    pub span: Span,
    pub resource: Option<usize>,
}
#[derive(Debug, Clone, Copy)]
pub(crate) enum Target {
    Io(IoOp, Option<ResultShape>),
    Bytes(BytesOp),
    /// Validated UTF-8 text operation (same native buffer representation).
    String(StringOp),
    /// Borrowed UTF-8 text-view operation over the four-word `&str` descriptor.
    Str(StrOp),
    /// Vector operation with its element type.
    Vec(VecOp, Type),
    /// Slice operation with its element type.
    Slice(SliceOp, Type),
    /// Runtime-sized inline array read: `(len, capacity?)` with the element
    /// type used to widen the loaded words.
    DynArray(DynArrayOp, Type),
    Function(usize),
    /// A synthesized borrowed object call reserves its source place while
    /// later arguments evaluate. Mutable calls also return it for write-back.
    ObjectFunction {
        function: usize,
        receiver: Option<usize>,
        mutable: bool,
    },
    Print,
    /// Print any fixed-width integer in decimal.
    PrintInt(crate::int::IntKind),
    /// Print an `f32`/`f64` as its shortest round-trip decimal.
    PrintFloat(crate::float::FloatKind),
    /// Explicit integer builtin: operation, source kind, target kind.
    Int(crate::int::IntOp, crate::int::IntKind, crate::int::IntKind),
    /// Explicit float builtin or conversion.
    Float(crate::float::FloatOp),
    Panic,
}
#[derive(Debug, Clone, Copy)]
pub(crate) enum IoOp {
    Stdin,
    Stdout,
    ReadAll,
    ReadLine,
    ReadChunk,
    Write,
}
impl IoOp {
    fn named(name: &str) -> Option<Self> {
        match name {
            "IO.stdin" => Some(Self::Stdin),
            "IO.stdout" => Some(Self::Stdout),
            "IO.read_all" => Some(Self::ReadAll),
            "IO.read_line" => Some(Self::ReadLine),
            "IO.read_chunk" => Some(Self::ReadChunk),
            "IO.write" => Some(Self::Write),
            _ => None,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum BytesOp {
    WithCapacity,
    Len,
    Capacity,
    Get,
    Push,
    PushReserved,
    Clear,
    Copy,
}
impl BytesOp {
    pub const ALL: [Self; 8] = [
        Self::WithCapacity,
        Self::Len,
        Self::Capacity,
        Self::Get,
        Self::Push,
        Self::PushReserved,
        Self::Clear,
        Self::Copy,
    ];
    pub fn borrowed(self) -> bool {
        matches!(self, Self::Len | Self::Capacity | Self::Get | Self::Copy)
    }
    pub fn symbol(self) -> &'static str {
        match self {
            Self::WithCapacity => "kush_bytes_with_capacity",
            Self::Len => "kush_bytes_len",
            Self::Capacity => "kush_bytes_capacity",
            Self::Get => "kush_bytes_get",
            Self::Push => "kush_bytes_push",
            Self::PushReserved => "kush_bytes_push_reserved",
            Self::Clear => "kush_bytes_clear",
            Self::Copy => "kush_bytes_copy",
        }
    }
    fn named(name: &str) -> Option<Self> {
        match name {
            "Bytes.with_capacity" => Some(Self::WithCapacity),
            "Bytes.len" => Some(Self::Len),
            "Bytes.capacity" => Some(Self::Capacity),
            "Bytes.get" => Some(Self::Get),
            "Bytes.push" => Some(Self::Push),
            "Bytes.push_reserved" => Some(Self::PushReserved),
            "Bytes.clear" => Some(Self::Clear),
            "Bytes.copy" => Some(Self::Copy),
            _ => None,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum StringOp {
    /// Byte length (`String.len`).
    Len,
    /// Unicode scalar count (`String.scalar_len`).
    ScalarLen,
    /// Bounds-checked byte read at a byte index (`String.byte_at`).
    ByteAt,
    /// Scalar-indexed code-point read returning `Option<Char>`.
    ScalarAt { some_tag: usize, none_tag: usize },
    /// Validate an owned byte buffer and return `Result<String, Bytes>`.
    FromUtf8 { ok_tag: usize, err_tag: usize },
    /// Explicit independent copy of the UTF-8 bytes (`String.as_bytes`).
    AsBytes,
    /// Reinterpret an owned `String` as owned `Bytes` without copying.
    IntoBytes,
}
impl StringOp {
    pub fn borrowed(self) -> bool {
        matches!(
            self,
            Self::Len | Self::ScalarLen | Self::ByteAt | Self::ScalarAt { .. } | Self::AsBytes
        )
    }
}
/// Operations on a borrowed `&str` view. View construction (`String.as_str`,
/// `String.substr`, `Str.substr`, and `view[start..end]`) lowers to the same
/// checked range expression as slice views, so only the reads and the explicit
/// owning copy need a builtin target here.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum StrOp {
    /// UTF-8 byte length of the view.
    Len,
    /// Unicode scalar count of the view.
    ScalarLen,
    /// Bounds-checked byte read, returning the byte value `0..=255`.
    ByteAt,
    /// Scalar-indexed code-point read returning `Option<Char>`.
    ScalarAt { some_tag: usize, none_tag: usize },
    /// Explicit allocating copy of the view into an owned `String`.
    ToString,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum VecOp {
    WithCapacity,
    /// Consume and return the same vector allocation, dropping every element
    /// in reverse order exactly once and retaining the allocated capacity.
    Clear,
    /// Consume and return the same vector allocation after ensuring room for
    /// `len + additional` elements. Growth happens at most once and only when
    /// the current capacity is insufficient.
    Reserve,
    /// Return Ok(grown vector) or Err(original vector), never dropping elements.
    TryReserve {
        ok_tag: usize,
        err_tag: usize,
    },
    Len,
    Get,
    /// Unchecked read; the bound was proved statically.
    At,
    Push,
    Set,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SliceOp {
    Len,
    /// Checked read; the reference evaluator/native lowering panics out of bounds.
    Get,
    /// Fallible read returning `Option<T>`; out-of-bounds indices yield `None`.
    TryGet {
        some_tag: usize,
        none_tag: usize,
        /// Layout index of the instantiated `Option<T>` result.
        option: usize,
    },
    /// Unchecked read; the bound was proved statically.
    At,
    /// Checked write through an exclusive mutable view; panics out of bounds.
    Set,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum DynArrayOp {
    /// Runtime length stored in word zero.
    Len,
    /// Checked element read; bounds are checked against the runtime length.
    Get,
}

#[derive(Debug)]
pub(crate) enum ExprKind {
    Constant(i64),
    BytesLiteral(Vec<u8>),
    /// A representation-changing subtype coercion. `Inject` puts an atom into a
    /// union alternative; `Repack` remaps a union value to a wider union.
    Coerce {
        value: Box<Expr>,
        to: Type,
        coercion: Coercion,
    },
    Construct {
        enum_id: usize,
        tag: usize,
        fields: Vec<Expr>,
    },
    Try {
        value: Box<Expr>,
        input: ResultShape,
        output: ResultShape,
    },
    /// A placeholder for a logical argument whose parameter is physically
    /// erased by `@[0]`. It is only ever used as an argument in a synthesized
    /// adapter where the adapter has no source value to forward. Both backends
    /// produce a dummy zero word and the callee's ABI erases the position, so
    /// the expression is never observed, stored, or passed.
    Erased(Type),
    Local(usize),
    Move(usize),
    Borrow(usize),
    BoxNew(Box<Expr>),
    BoxTake(Box<Expr>),
    BoxRead(Box<Expr>),
    /// Consume an owned box, drop its affine payload exactly once after both
    /// arguments are evaluated, and store `payload` in the same allocation.
    /// Checked to require a non-linear old payload and a non-wider new layout.
    BoxReuse {
        owner: Box<Expr>,
        payload: Box<Expr>,
    },
    /// Consume an owned box and store `payload`, reusing the allocation when
    /// its capacity already fits and otherwise growing/moving exactly once.
    /// Unlike `BoxReuse`, a wider payload is accepted. The checked effect row
    /// is `{alloc, panic}`: a growth may allocate and aborts on exhaustion.
    BoxReuseGrow {
        owner: Box<Expr>,
        payload: Box<Expr>,
    },
    /// Fallible `Box.new`: allocate `value` and return `Ok(Box<T>)`, or return
    /// the untouched value in `Err(T)` when the allocator refuses. The runtime
    /// never converts a checked failure into a process abort.
    BoxTryNew {
        value: Box<Expr>,
        shape: ResultShape,
    },
    /// Fallible growth-capable reuse. On failure the original owner is
    /// returned in `Err(Box<T>)` without destroying its payload; because the
    /// new payload must be non-owning, no supplied owner is lost.
    BoxTryReuse {
        owner: Box<Expr>,
        payload: Box<Expr>,
        shape: ResultShape,
    },
    /// Fallible byte-buffer construction. `Ok` carries a buffer with the exact
    /// requested capacity; `Err` returns the requested capacity unchanged.
    BytesTryWithCapacity {
        capacity: Box<Expr>,
        shape: ResultShape,
    },
    /// Create an owning bump-allocator region. The region descriptor is one
    /// logical allocation; its internal chunks are not separately counted.
    ArenaNew,
    /// Allocate `value` in the borrowed arena. The returned box retains the
    /// region until its payload has been dropped.
    ArenaAlloc {
        arena: Box<Expr>,
        value: Box<Expr>,
    },
    /// Read a copyable payload through an `&ArenaBox<T>`.
    ArenaBoxRead(Box<Expr>),
    /// Move a payload out of an owning `ArenaBox<T>` and release its region
    /// reference exactly once.
    ArenaBoxTake(Box<Expr>),
    Drop(Box<Expr>),
    Block(Block),
    Unary(Kind, Box<Expr>),
    Binary(Kind, Box<Expr>, Box<Expr>),
    Assign(usize, Box<Expr>),
    /// Store a copyable field through an exclusive record reference. The
    /// reference is the evaluated pointer (`&mut Record`), `offset` is the word
    /// offset from the record tag, and the value is evaluated once before the
    /// store. Owning, borrowed-view, and nested-owning field replacement is
    /// rejected by the checker.
    RefAssign(Box<Expr>, usize, Box<Expr>),
    /// Read a whole value through a checked reference. Used for a stored
    /// borrowed trait object (`&dyn Trait`/`&mut dyn Trait`); the referent is
    /// copyable, so the read does not duplicate owning storage.
    RefRead(Box<Expr>),
    /// Replace the whole referent through a checked exclusive reference and
    /// return Unit. Used to write a mutated borrowed trait object back.
    RefWrite(Box<Expr>, Box<Expr>),
    Call(Target, Vec<Expr>),
    Return(Box<Expr>),
    If(Box<Expr>, Block, Block),
    Match(Box<Expr>, Vec<Arm>),
    /// A first-class function value: a code pointer plus, for a capturing
    /// lambda or adapter closure, an owned environment containing `captures`.
    FnValue {
        function: usize,
        captures: Vec<Expr>,
    },
    /// Call through a checked `fn(...)` or `once fn(...)` value. The callee's
    /// type selects the signature; an owning closure is consumed by the call.
    CallIndirect {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
    },
    /// Create a structured child task from an owned once callable. The result
    /// type is the task's `T`; the expression's own type is `Task<T>`.
    TaskSpawn {
        body: Box<Expr>,
        result: Type,
        /// The spawned body returns an owning/intrinsically linear payload with
        /// a transfer obligation. The handle is then linear (it must be joined
        /// explicitly) and a cancellation-requested completion transfers the
        /// payload as `Completed` instead of discarding it.
        obligation: bool,
    },
    /// Run a once callable in the current task with a fresh structured scope
    /// frame. The epilogue joins every unjoined child before returning.
    TaskScope {
        body: Box<Expr>,
        result: Type,
        /// The scope body result carries an owning/linear obligation.
        obligation: bool,
        /// When the scope lambda returns the conventional `Result<T,E>`, an
        /// `Err` result requests cancellation of every unjoined child before
        /// the scope epilogue joins them.
        failure: Option<crate::runtime_types::ResultShape>,
    },
    /// Cooperative suspension point. The boolean result reports whether
    /// cancellation has been requested.
    TaskYield,
    /// Read the current task's cancellation request bit without suspending.
    TaskCheckCancel,
    /// Request cancellation of the task borrowed by the argument. The argument
    /// is a `&Task<T>` borrow and the result is Unit.
    TaskCancel(Box<Expr>),
    /// Block until the target task finishes, consume its handle, and produce
    /// `TaskExit<T>`.
    TaskJoin {
        task: Box<Expr>,
        exit: TaskExitShape,
        /// The joined task's payload carries an owning/linear obligation, so
        /// the resulting `TaskExit<T>` transfers it to the caller.
        obligation: bool,
    },
    /// Allocation-preserving in-place vector transform. `callbacks` are
    /// applied left-to-right to every element; their signatures determine the
    /// intermediate layouts. The final `target` must be no wider than
    /// `source`. A checked fusion may contain two pure callback steps.
    VecMap {
        vector: Box<Expr>,
        callbacks: Vec<Expr>,
        source: Type,
        target: Type,
    },
    /// Construct an empty runtime-sized inline array with zeroed capacity.
    DynArrayNew {
        element: Type,
        capacity: usize,
    },
    /// Append one element, consuming and returning the same inline storage.
    /// The runtime length check panics before any out-of-capacity store.
    DynArrayPush {
        array: Box<Expr>,
        value: Box<Expr>,
        element: Type,
        capacity: usize,
    },
    /// Overwrite one initialized slot in place. Copyable elements only; the
    /// inline storage and runtime length are preserved.
    DynArraySet {
        array: Box<Expr>,
        index: Box<Expr>,
        value: Box<Expr>,
        element: Type,
        capacity: usize,
    },
    /// Remove and return the last initialized slot as `(array, element)`.
    /// Copyable elements only, so the removed value cannot duplicate an owner.
    DynArrayPop {
        array: Box<Expr>,
        element: Type,
        capacity: usize,
    },
    /// Read a local without moving it (only to project copyable fields).
    Peek(usize),
    /// Copy the field at a word offset out of a record value.
    Project(Box<Expr>, usize),
    /// Unchecked byte read; the bound was proved statically.
    BytesAt(Box<Expr>, Box<Expr>),
    /// Build an immutable slice view over an inline array, an owned Vec/Bytes,
    /// or another slice. `check` requests a runtime `start <= end <= len` check.
    Slice {
        base: Box<Expr>,
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        element: Type,
        check: bool,
        /// A checked split proven by `Slice.split_at_mut`: the group id and
        /// whether this is the left side. This is checker-only provenance and
        /// has no runtime representation.
        split: Option<(usize, bool)>,
        /// A borrowed text view instead of an element slice: the descriptor has
        /// byte stride one, the result type is `&str`, and a checked range also
        /// verifies that both endpoints are UTF-8 scalar boundaries.
        text: bool,
    },
    While(Box<Expr>, Block),
    Loop(Block),
    /// Leave the innermost loop. The list names resources owned by scopes
    /// inside the loop that must be cleaned up (filled by the ownership pass).
    Break(Option<Box<Expr>>, Vec<usize>),
    Continue(Vec<usize>),
}
#[derive(Debug)]
pub(crate) struct Arm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}
/// The checked `TaskExit<T>` layout used by `Task.join`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TaskExitShape {
    pub completed_tag: usize,
    pub cancelled_tag: usize,
    pub payload: Type,
    pub result: Type,
}
/// Deterministic runtime conversion between equivalent value representations.
#[derive(Debug, Clone)]
pub(crate) enum Coercion {
    /// Store the value in alternative `tag` of the target union.
    Inject { tag: usize },
    /// Remap every source alternative tag to a target alternative tag.
    Repack { map: Vec<usize> },
    /// Rebuild a record in a canonical structural row. `source` is the checked
    /// source record layout, `kept` maps each target field to its source field
    /// and an optional nested representation change, and `drops` lists source
    /// fields absent from the target. The checker guarantees no dropped field
    /// carries a linear obligation.
    Struct {
        source: Type,
        kept: Vec<(usize, usize, Option<Coercion>)>,
        drops: Vec<(usize, Type)>,
    },
}
#[derive(Debug, Clone)]
pub(crate) enum Pattern {
    Any,
    Bind(usize),
    Literal(i64),
    Or(Vec<Pattern>),
    Variant {
        tag: usize,
        fields: Vec<(usize, Pattern)>,
    },
    /// Match one normalized union alternative and apply `inner` to the
    /// narrowed payload. `member` is the runtime type of that payload.
    Type {
        tag: usize,
        member: Type,
        inner: Box<Pattern>,
    },
}
#[derive(Clone)]
struct Signature {
    binding: BindingId,
    name: String,
    /// Runtime parameter types, in order. Erased parameters are absent.
    parameters: Vec<Type>,
    result: Type,
    effects: u8,
    span: Span,
    /// Generic parameter binder -> concrete type, for specialized instances.
    substitution: BTreeMap<BindingId, Type>,
    /// Const natural binder -> compile-time value, for specialized instances.
    consts: BTreeMap<BindingId, usize>,
    /// Abstract grade binder -> concrete compile-time grade.
    grades: BTreeMap<BindingId, Grade>,
    /// Effect row binder -> concrete effect bitset for this instance.
    effect_arguments: BTreeMap<BindingId, u8>,
    /// Where a generic instance was first requested, for diagnostics.
    origin: Option<(Span, String)>,
    /// Usage grade of each runtime parameter (`None` is unannotated).
    parameter_grades: Vec<Option<Grade>>,
    /// Static result-transfer contract; `Some(Finite(1))` means the caller
    /// acquires a linear obligation for the returned owning value.
    result_grade: Option<Grade>,
    parameter_lifetimes: Vec<Option<String>>,
    result_lifetime: Option<String>,
    lifetime_bounds: BTreeSet<(String, String)>,
    /// Concrete `Self` target for an impl method instance.
    self_type: Option<Type>,
    /// Trait specialization that this instance's default body belongs to.
    /// Unqualified method calls on `Self` inside the body prefer it.
    default_trait: Option<(BindingId, TraitArguments)>,
    /// Associated constants of the owning impl, already evaluated for this
    /// instance's specialization. `Self::NAME` resolves here.
    associated_consts: BTreeMap<String, ConstValue>,
}
impl Signature {
    /// Whether logical runtime parameter `index` is physically erased by a
    /// grade-zero contract.
    fn parameter_erased(&self, index: usize) -> bool {
        crate::runtime_types::grade_erases(self.parameter_grades.get(index).copied().flatten())
    }
}
/// Split `T @[grade]` into the type and its grade expression.
fn split_grade(ty: &ast::Type) -> (&ast::Type, Option<&ast::Type>) {
    grades::split(ty)
}
/// Expand an outer chain of transparent executable type aliases so a result
/// contract can be written through an alias:
///
/// ```kush
/// type Handle<T> = Box<T> @[1];
/// fn make() -> Handle<i64> ! { ... } { Box.new(0) }
/// ```
///
/// Only the outermost alias chain is expanded here; nested aliases still go
/// through normal checked type lowering. Grade/const/type arguments are
/// substituted structurally, while lifetime arguments stay erased. Grade
/// parameters are permitted only here, in a result-contract position: the
/// substituted grade is evaluated by [`result_contract`] afterwards, or
/// inferred from the expected arrow contract for a generic function value.
fn expand_result_aliases(
    resolution: &Resolution,
    types: &Types<'_>,
    ty: &ast::Type,
) -> Result<ast::Type> {
    let mut current = ty.clone();
    let mut active = BTreeSet::new();
    for _ in 0..64 {
        let ast::TypeKind::Named { arguments, .. } = &current.kind else {
            return Ok(current);
        };
        let Some(id) = resolution.reference(current.span) else {
            return Ok(current);
        };
        if resolution.bindings[id].kind != BindingKind::Alias {
            return Ok(current);
        }
        let Some((generics, rhs)) = types.alias_definition(id) else {
            return Ok(current);
        };
        let lifetime_arguments = arguments
            .iter()
            .filter(|argument| matches!(argument.kind, ast::TypeKind::Lifetime(_)))
            .count();
        if let Some(expected) = types.alias_lifetime_count(id)
            && lifetime_arguments != expected
        {
            return Err(Diagnostic::new(
                current.span,
                format!(
                    "type alias '{}' expects {expected} lifetime argument(s), found {lifetime_arguments}",
                    resolution.bindings[id].name
                ),
            ));
        }
        let runtime_arguments = arguments
            .iter()
            .filter(|argument| !matches!(argument.kind, ast::TypeKind::Lifetime(_)))
            .collect::<Vec<_>>();
        if runtime_arguments.len() != generics.len() {
            return Err(Diagnostic::new(
                current.span,
                format!(
                    "type alias '{}' expects {} runtime argument(s), found {}",
                    resolution.bindings[id].name,
                    generics.len(),
                    runtime_arguments.len()
                ),
            ));
        }
        if !active.insert(id) {
            return Err(Diagnostic::new(
                current.span,
                format!(
                    "cyclic executable type alias '{}' is not allowed",
                    resolution.bindings[id].name
                ),
            ));
        }
        let mut map = BTreeMap::new();
        for (generic, argument) in generics.iter().zip(runtime_arguments) {
            // Grade arguments are substituted like any other structural
            // argument here. `expand_alias` still rejects them in every
            // non-result alias position, so a grade cannot enter a parameter
            // or stored type through this expansion.
            map.insert(resolution.binder(generic.span).unwrap(), argument);
        }
        current = substitute_alias_type(resolution, rhs, &map);
    }
    Err(Diagnostic::new(
        ty.span,
        "executable type alias expansion exceeds the 64-level budget",
    ))
}

/// Whether `ty` mentions the given binding anywhere, including nested grade
/// expressions and alias arguments.
pub(crate) fn type_mentions_binding(
    resolution: &Resolution,
    ty: &ast::Type,
    binder: BindingId,
) -> bool {
    use ast::TypeKind as K;
    match &ty.kind {
        K::Named { arguments, .. } => {
            resolution.reference(ty.span) == Some(binder)
                || arguments
                    .iter()
                    .any(|argument| type_mentions_binding(resolution, argument, binder))
        }
        K::Tuple(items) => items
            .iter()
            .any(|item| type_mentions_binding(resolution, item, binder)),
        K::Structural(fields) => fields
            .iter()
            .any(|field| type_mentions_binding(resolution, &field.ty, binder)),
        K::Dyn(inner) => type_mentions_binding(resolution, inner, binder),
        K::Slice(inner) => type_mentions_binding(resolution, inner, binder),
        K::Array(element, length) => {
            type_mentions_binding(resolution, element, binder)
                || type_mentions_binding(resolution, length, binder)
        }
        K::Borrow { inner, .. } => type_mentions_binding(resolution, inner, binder),
        K::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_binding(resolution, &parameter.ty, binder))
                || type_mentions_binding(resolution, result, binder)
                || effects
                    .iter()
                    .any(|effect| type_mentions_binding(resolution, effect, binder))
        }
        K::Binary { left, right, .. } => {
            type_mentions_binding(resolution, left, binder)
                || type_mentions_binding(resolution, right, binder)
        }
        K::Graded { inner, grade } => {
            type_mentions_binding(resolution, inner, binder)
                || type_mentions_binding(resolution, grade, binder)
        }
        K::Integer(_) | K::Bool(_) | K::Lifetime(_) | K::SelfType | K::Predicate(_) => false,
    }
}
/// The binder named by a bare grade expression, as in `@[G]`. Composite
/// expressions such as `@[G + 1]` and `@[G * 2]` are not inferable.
pub(crate) fn bare_grade_binder(resolution: &Resolution, grade: &ast::Type) -> Option<BindingId> {
    let ast::TypeKind::Named { arguments, .. } = &grade.kind else {
        return None;
    };
    if !arguments.is_empty() {
        return None;
    }
    resolution.reference(grade.span)
}
/// Split a declared result type into the runtime result type and the evaluated
/// static result grade, expanding outer aliases first. Only `@[1]` on an owning
/// or intrinsically linear result is supported; other grades are rejected
/// explicitly instead of silently discarding the transfer obligation.
fn result_contract(
    resolution: &Resolution,
    types: &Types<'_>,
    grade_substitution: &BTreeMap<BindingId, Grade>,
    ty: &ast::Type,
) -> Result<(ast::Type, Option<Grade>)> {
    let expanded = expand_result_aliases(resolution, types, ty)?;
    let (inner, grade) = split_grade(&expanded);
    let grade = grade
        .map(|grade| grades::evaluate(resolution, grade_substitution, grade))
        .transpose()?;
    Ok((inner.clone(), grade))
}

/// Validate a static result-transfer contract.
///
/// Exactly `@[1]` is representable. On an owning or intrinsically linear
/// result it transfers an owning linear obligation. On a copyable result it
/// transfers a *must-use* obligation: the caller must observe the returned
/// value exactly once on every normal path. The two obligations are distinct
/// even though both use the same `@[1]` surface syntax; `result_grade` alone
/// never makes a copyable value move-owning.
fn validate_result_contract(
    grade: Option<Grade>,
    owning: bool,
    name: &str,
    span: Span,
) -> Result<()> {
    match grade {
        None => Ok(()),
        Some(grade) if grade.is_one() => Ok(()),
        Some(grade) if grade.is_zero() && !owning => Ok(()),
        Some(grade) if grade.is_zero() => Err(Diagnostic::new(
            span,
            format!(
                "a result graded @[0] would silently discard the owning/linear value {name}; use an owning @[1] result contract, consume it inside the function, or return Unit"
            ),
        )),
        Some(grade) if grade.is_many() => Err(Diagnostic::new(
            span,
            "a result graded 'many' could duplicate one owning resource; result contracts currently support exactly @[1] or a copyable @[0]",
        )),
        Some(grade) => Err(Diagnostic::new(
            span,
            format!(
                "a result graded @[{grade}] could duplicate one owning resource; result contracts currently support exactly @[1] or a copyable @[0]"
            ),
        )),
    }
}
/// The runtime type of a direct call expression. A `@[0]` result has no
/// observable payload, so callers see `Unit`.
fn call_result_type(signature: &Signature) -> Type {
    if crate::runtime_types::grade_erases(signature.result_grade) {
        Type::Unit
    } else {
        signature.result
    }
}
/// Outer lifetime annotation of a borrow type, if any.
fn borrow_lifetime(ty: &ast::Type) -> Option<String> {
    match &ty.kind {
        ast::TypeKind::Borrow { lifetime, .. } => lifetime.clone(),
        _ => None,
    }
}
/// Every lifetime name mentioned by a type, including nested borrows.
fn type_lifetimes(ty: &ast::Type, out: &mut BTreeSet<String>) {
    match &ty.kind {
        ast::TypeKind::Lifetime(name) => {
            out.insert(name.clone());
        }
        ast::TypeKind::Borrow {
            lifetime, inner, ..
        } => {
            if let Some(lifetime) = lifetime {
                out.insert(lifetime.clone());
            }
            type_lifetimes(inner, out);
        }
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            type_lifetimes(inner, out);
        }
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
            for argument in arguments {
                type_lifetimes(argument, out);
            }
        }
        ast::TypeKind::Array(inner, length) => {
            type_lifetimes(inner, out);
            type_lifetimes(length, out);
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_lifetimes(left, out);
            type_lifetimes(right, out);
        }
        ast::TypeKind::Function {
            lifetimes,
            parameters,
            result,
            effects,
            ..
        } => {
            // Lifetimes bound by the arrow itself are not free in the type.
            let mut inner = BTreeSet::new();
            for parameter in parameters {
                type_lifetimes(&parameter.ty, &mut inner);
            }
            type_lifetimes(result, &mut inner);
            for effect in effects {
                type_lifetimes(effect, &mut inner);
            }
            for lifetime in lifetimes {
                inner.remove(&lifetime.name);
            }
            out.extend(inner);
        }
        _ => {}
    }
}
/// Collect explicit `return value` expressions while ignoring nested lambdas,
/// whose returns belong to the callable rather than this function body.
fn collect_body_returns<'a>(expr: &'a ast::Expr, out: &mut Vec<&'a ast::Expr>) {
    match &expr.kind {
        ast::ExprKind::Return(Some(value)) => {
            out.push(value);
            collect_body_returns(value, out);
        }
        ast::ExprKind::Lambda(_) | ast::ExprKind::Return(None) | ast::ExprKind::Continue => {}
        ast::ExprKind::Name(_)
        | ast::ExprKind::Integer(_)
        | ast::ExprKind::Float(_)
        | ast::ExprKind::String(_)
        | ast::ExprKind::Char(_)
        | ast::ExprKind::Bool(_) => {}
        ast::ExprKind::Tuple(items) | ast::ExprKind::Array(items) => {
            for item in items {
                collect_body_returns(item, out);
            }
        }
        ast::ExprKind::StructuralLiteral(fields) => {
            for (_, value) in fields {
                collect_body_returns(value, out);
            }
        }
        ast::ExprKind::Block(block) => collect_block_returns(block, out),
        ast::ExprKind::Unary { operand, .. }
        | ast::ExprKind::Try(operand)
        | ast::ExprKind::Field { value: operand, .. }
        | ast::ExprKind::Specialize {
            callee: operand, ..
        } => {
            collect_body_returns(operand, out);
        }
        ast::ExprKind::Slice { value, start, end } => {
            collect_body_returns(value, out);
            if let Some(start) = start {
                collect_body_returns(start, out);
            }
            if let Some(end) = end {
                collect_body_returns(end, out);
            }
        }
        ast::ExprKind::Binary { left, right, .. } => {
            collect_body_returns(left, out);
            collect_body_returns(right, out);
        }
        ast::ExprKind::Index { value, index } => {
            collect_body_returns(value, out);
            collect_body_returns(index, out);
        }
        ast::ExprKind::Call { callee, arguments } => {
            collect_body_returns(callee, out);
            for argument in arguments {
                collect_body_returns(argument, out);
            }
        }
        ast::ExprKind::Handle { handler, body, .. } => {
            collect_body_returns(handler, out);
            collect_block_returns(body, out);
        }
        ast::ExprKind::Perform { value, .. } => collect_body_returns(value, out),
        ast::ExprKind::If {
            condition,
            then,
            otherwise,
        } => {
            collect_body_returns(condition, out);
            collect_block_returns(then, out);
            if let Some(otherwise) = otherwise {
                collect_body_returns(otherwise, out);
            }
        }
        ast::ExprKind::Match { value, arms } => {
            collect_body_returns(value, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_body_returns(guard, out);
                }
                collect_body_returns(&arm.body, out);
            }
        }
        ast::ExprKind::Record { ty, fields } => {
            collect_body_returns(ty, out);
            for (_, field) in fields {
                collect_body_returns(field, out);
            }
        }
        ast::ExprKind::While { condition, body } => {
            collect_body_returns(condition, out);
            collect_block_returns(body, out);
        }
        ast::ExprKind::Loop(body) => collect_block_returns(body, out),
        ast::ExprKind::Break(value) => {
            if let Some(value) = value {
                collect_body_returns(value, out);
            }
        }
    }
}
fn collect_block_returns<'a>(block: &'a ast::Block, out: &mut Vec<&'a ast::Expr>) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } => collect_body_returns(value, out),
            ast::Statement::Expr(expr) => collect_body_returns(expr, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_body_returns(tail, out);
    }
}
/// Automatic fusion equivalence analysis.
///
/// A callback is eligible only when:
///
/// * it is a noncapturing `fn(...)` value;
/// * its declared effect row contains neither `io`, `suspend`, nor `panic`;
/// * its body is structurally total: no loops, no direct or indirect recursion,
///   no indirect calls, and no task operations;
/// * every direct callee is itself eligible.
///
/// This establishes structural totality, not allocation commutativity:
/// refused allocations produce observable values. The merge separately checks
/// that only one allocation stage is active and the other stages cannot change
/// heap ownership, so allocator operations retain their original order.
/// The pass is deliberately conservative: it does not try to prove termination
/// for loops, and it rejects indirect calls and recursion outright.
fn fusion_function_safe(
    index: usize,
    signatures: &[Signature],
    bodies: &[Option<Function>],
    memo: &mut Vec<Option<bool>>,
    visiting: &mut Vec<bool>,
) -> bool {
    if let Some(result) = memo.get(index).copied().flatten() {
        return result;
    }
    if visiting.get(index).copied().unwrap_or(false) {
        // Recursion (direct or mutual) has no checked termination argument.
        return false;
    }
    let Some(signature) = signatures.get(index) else {
        return false;
    };
    if signature.effects & !ALLOC != 0 {
        return false;
    }
    let Some(Some(body)) = bodies.get(index) else {
        return false;
    };
    if visiting.len() <= index {
        visiting.resize(index + 1, false);
    }
    visiting[index] = true;
    let safe = fusion_block_safe(&body.body, signatures, bodies, memo, visiting);
    visiting[index] = false;
    if memo.len() <= index {
        memo.resize(index + 1, None);
    }
    memo[index] = Some(safe);
    safe
}

fn fusion_block_safe(
    block: &Block,
    signatures: &[Signature],
    bodies: &[Option<Function>],
    memo: &mut Vec<Option<bool>>,
    visiting: &mut Vec<bool>,
) -> bool {
    block.statements.iter().all(|statement| match statement {
        Statement::Let(_, value) | Statement::Expr(value) => {
            fusion_expr_safe(value, signatures, bodies, memo, visiting)
        }
    }) && block
        .tail
        .as_ref()
        .is_none_or(|tail| fusion_expr_safe(tail, signatures, bodies, memo, visiting))
}

fn fusion_expr_safe(
    expr: &Expr,
    signatures: &[Signature],
    bodies: &[Option<Function>],
    memo: &mut Vec<Option<bool>>,
    visiting: &mut Vec<bool>,
) -> bool {
    let safe = |value: &Expr,
                signatures: &[Signature],
                bodies: &[Option<Function>],
                memo: &mut Vec<Option<bool>>,
                visiting: &mut Vec<bool>| {
        fusion_expr_safe(value, signatures, bodies, memo, visiting)
    };
    match &expr.kind {
        ExprKind::Constant(_)
        | ExprKind::Erased(_)
        | ExprKind::BytesLiteral(_)
        | ExprKind::Local(_)
        | ExprKind::Move(_)
        | ExprKind::Borrow(_)
        | ExprKind::Peek(_)
        | ExprKind::ArenaNew
        | ExprKind::DynArrayNew { .. } => true,
        // A whole-value reference read/write is never fused: it depends on
        // aliasing storage and has no total, capture-free callback shape.
        ExprKind::RefRead(_) | ExprKind::RefWrite(_, _) => false,
        // No loop has a checked termination argument here.
        ExprKind::While(..) | ExprKind::Loop(_) => false,
        ExprKind::Call(Target::ObjectFunction { .. }, _) => false,
        ExprKind::Call(Target::Function(index), arguments) => {
            fusion_function_safe(*index, signatures, bodies, memo, visiting)
                && arguments
                    .iter()
                    .all(|argument| safe(argument, signatures, bodies, memo, visiting))
        }
        ExprKind::Call(
            Target::Io(..)
            | Target::Print
            | Target::PrintInt(_)
            | Target::PrintFloat(_)
            | Target::Panic,
            _,
        ) => false,
        ExprKind::Call(_, arguments) => arguments
            .iter()
            .all(|argument| safe(argument, signatures, bodies, memo, visiting)),
        // An opaque callable can select an effectful or divergent body.
        ExprKind::CallIndirect { .. } => false,
        ExprKind::TaskSpawn { .. }
        | ExprKind::TaskScope { .. }
        | ExprKind::TaskYield
        | ExprKind::TaskCheckCancel
        | ExprKind::TaskCancel(_)
        | ExprKind::TaskJoin { .. } => false,
        ExprKind::FnValue { function, captures } => {
            captures
                .iter()
                .all(|capture| safe(capture, signatures, bodies, memo, visiting))
                && fusion_function_safe(*function, signatures, bodies, memo, visiting)
        }
        ExprKind::Coerce { value, .. }
        | ExprKind::Try { value, .. }
        | ExprKind::BoxNew(value)
        | ExprKind::BoxTake(value)
        | ExprKind::BoxRead(value)
        | ExprKind::BoxTryNew { value, .. }
        | ExprKind::ArenaBoxRead(value)
        | ExprKind::ArenaBoxTake(value)
        | ExprKind::BytesTryWithCapacity {
            capacity: value, ..
        }
        | ExprKind::Drop(value)
        | ExprKind::Unary(_, value)
        | ExprKind::Assign(_, value)
        | ExprKind::Return(value)
        | ExprKind::Project(value, _) => safe(value, signatures, bodies, memo, visiting),
        ExprKind::ArenaAlloc { arena, value } => {
            safe(arena, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArrayPush { array, value, .. } => {
            safe(array, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArraySet {
            array,
            index,
            value,
            ..
        } => {
            safe(array, signatures, bodies, memo, visiting)
                && safe(index, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArrayPop { array, .. } => safe(array, signatures, bodies, memo, visiting),
        ExprKind::BoxReuse { owner, payload }
        | ExprKind::BoxReuseGrow { owner, payload }
        | ExprKind::BoxTryReuse { owner, payload, .. } => {
            safe(owner, signatures, bodies, memo, visiting)
                && safe(payload, signatures, bodies, memo, visiting)
        }
        ExprKind::RefAssign(reference, _, value) => {
            safe(reference, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::Binary(_, left, right) | ExprKind::BytesAt(left, right) => {
            safe(left, signatures, bodies, memo, visiting)
                && safe(right, signatures, bodies, memo, visiting)
        }
        ExprKind::Construct { fields, .. } => fields
            .iter()
            .all(|field| safe(field, signatures, bodies, memo, visiting)),
        ExprKind::Block(block) => fusion_block_safe(block, signatures, bodies, memo, visiting),
        ExprKind::If(condition, yes, no) => {
            safe(condition, signatures, bodies, memo, visiting)
                && fusion_block_safe(yes, signatures, bodies, memo, visiting)
                && fusion_block_safe(no, signatures, bodies, memo, visiting)
        }
        ExprKind::Match(value, arms) => {
            safe(value, signatures, bodies, memo, visiting)
                && arms.iter().all(|arm| {
                    arm.guard
                        .as_ref()
                        .is_none_or(|guard| safe(guard, signatures, bodies, memo, visiting))
                        && safe(&arm.body, signatures, bodies, memo, visiting)
                })
        }
        ExprKind::VecMap {
            vector, callbacks, ..
        } => {
            safe(vector, signatures, bodies, memo, visiting)
                && callbacks
                    .iter()
                    .all(|callback| safe(callback, signatures, bodies, memo, visiting))
        }
        ExprKind::Slice {
            base, start, end, ..
        } => {
            safe(base, signatures, bodies, memo, visiting)
                && start
                    .as_ref()
                    .is_none_or(|start| safe(start, signatures, bodies, memo, visiting))
                && end
                    .as_ref()
                    .is_none_or(|end| safe(end, signatures, bodies, memo, visiting))
        }
        ExprKind::Break(value, _) => value
            .as_ref()
            .is_none_or(|value| safe(value, signatures, bodies, memo, visiting)),
        // `Continue` carries no expression children.
        ExprKind::Continue(_) => true,
    }
}

/// Select automatic nested in-place map fusion after every body has been
/// checked. A merge is allowed only when every callback in both steps is
/// fusion-safe and the intermediate layout agrees. For a step with a non-empty
/// (alloc-only) effect row, the intermediate must also be non-owning: the
/// fused traversal keeps one intermediate live at a time instead of all of
/// them, and this restriction keeps every drop-order observation identical.
fn automatic_fusion(types: &Types<'_>, functions: &mut Functions<'_>) -> usize {
    let mut memo: Vec<Option<bool>> = vec![None; functions.bodies.len()];
    let mut visiting = vec![false; functions.bodies.len()];
    let mut safety = vec![false; functions.bodies.len()];
    for (index, entry) in safety.iter_mut().enumerate() {
        *entry = fusion_function_safe(
            index,
            &functions.signatures,
            &functions.bodies,
            &mut memo,
            &mut visiting,
        );
    }
    let signatures = &functions.signatures;
    let mut fusions = 0;
    for body in functions.bodies.iter_mut().flatten() {
        fuse_block(&mut body.body, types, signatures, &safety, &mut fusions);
    }
    fusions
}

fn fuse_block(
    block: &mut Block,
    types: &Types<'_>,
    signatures: &[Signature],
    safety: &[bool],
    fusions: &mut usize,
) {
    for statement in &mut block.statements {
        match statement {
            Statement::Let(_, value) | Statement::Expr(value) => {
                fuse_expr(value, types, signatures, safety, fusions)
            }
        }
    }
    if let Some(tail) = &mut block.tail {
        fuse_expr(tail, types, signatures, safety, fusions);
    }
}

fn fuse_expr(
    expr: &mut Expr,
    types: &Types<'_>,
    signatures: &[Signature],
    safety: &[bool],
    fusions: &mut usize,
) {
    let safe_callback = |callback: &Expr| -> bool {
        matches!(
            &callback.kind,
            ExprKind::FnValue { function, captures }
                if captures.is_empty() && safety.get(*function).copied().unwrap_or(false)
        )
    };
    match &mut expr.kind {
        ExprKind::Coerce { value, .. }
        | ExprKind::Try { value, .. }
        | ExprKind::BoxNew(value)
        | ExprKind::BoxTake(value)
        | ExprKind::BoxRead(value)
        | ExprKind::BoxTryNew { value, .. }
        | ExprKind::ArenaBoxRead(value)
        | ExprKind::ArenaBoxTake(value)
        | ExprKind::BytesTryWithCapacity {
            capacity: value, ..
        }
        | ExprKind::Drop(value)
        | ExprKind::Unary(_, value)
        | ExprKind::Assign(_, value)
        | ExprKind::Return(value)
        | ExprKind::Project(value, _)
        | ExprKind::RefRead(value) => fuse_expr(value, types, signatures, safety, fusions),
        ExprKind::RefWrite(reference, value) => {
            fuse_expr(reference, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::ArenaAlloc { arena, value } => {
            fuse_expr(arena, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArrayPush { array, value, .. } => {
            fuse_expr(array, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArraySet {
            array,
            index,
            value,
            ..
        } => {
            fuse_expr(array, types, signatures, safety, fusions);
            fuse_expr(index, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArrayPop { array, .. } => {
            fuse_expr(array, types, signatures, safety, fusions);
        }
        ExprKind::BoxReuse { owner, payload }
        | ExprKind::BoxReuseGrow { owner, payload }
        | ExprKind::BoxTryReuse { owner, payload, .. } => {
            fuse_expr(owner, types, signatures, safety, fusions);
            fuse_expr(payload, types, signatures, safety, fusions);
        }
        ExprKind::RefAssign(reference, _, value) => {
            fuse_expr(reference, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::Binary(_, left, right) | ExprKind::BytesAt(left, right) => {
            fuse_expr(left, types, signatures, safety, fusions);
            fuse_expr(right, types, signatures, safety, fusions);
        }
        ExprKind::Construct { fields, .. } => {
            for field in fields {
                fuse_expr(field, types, signatures, safety, fusions);
            }
        }
        ExprKind::Call(_, arguments) => {
            for argument in arguments {
                fuse_expr(argument, types, signatures, safety, fusions);
            }
        }
        ExprKind::Block(block) => fuse_block(block, types, signatures, safety, fusions),
        ExprKind::If(condition, yes, no) => {
            fuse_expr(condition, types, signatures, safety, fusions);
            fuse_block(yes, types, signatures, safety, fusions);
            fuse_block(no, types, signatures, safety, fusions);
        }
        ExprKind::Match(value, arms) => {
            fuse_expr(value, types, signatures, safety, fusions);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    fuse_expr(guard, types, signatures, safety, fusions);
                }
                fuse_expr(&mut arm.body, types, signatures, safety, fusions);
            }
        }
        ExprKind::FnValue { captures, .. } => {
            for capture in captures {
                fuse_expr(capture, types, signatures, safety, fusions);
            }
        }
        ExprKind::CallIndirect { callee, arguments } => {
            fuse_expr(callee, types, signatures, safety, fusions);
            for argument in arguments {
                fuse_expr(argument, types, signatures, safety, fusions);
            }
        }
        ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
            fuse_expr(body, types, signatures, safety, fusions)
        }
        ExprKind::TaskCancel(value) => fuse_expr(value, types, signatures, safety, fusions),
        ExprKind::TaskJoin { task, .. } => fuse_expr(task, types, signatures, safety, fusions),
        ExprKind::Slice {
            base, start, end, ..
        } => {
            fuse_expr(base, types, signatures, safety, fusions);
            if let Some(start) = start {
                fuse_expr(start, types, signatures, safety, fusions);
            }
            if let Some(end) = end {
                fuse_expr(end, types, signatures, safety, fusions);
            }
        }
        ExprKind::Break(value, _) => {
            if let Some(value) = value {
                fuse_expr(value, types, signatures, safety, fusions);
            }
        }
        ExprKind::VecMap {
            vector,
            callbacks,
            source,
            target: _,
        } => {
            fuse_expr(vector, types, signatures, safety, fusions);
            for callback in callbacks.iter_mut() {
                fuse_expr(callback, types, signatures, safety, fusions);
            }
            let mut merged = Vec::new();
            std::mem::swap(callbacks, &mut merged);
            let mut cursor = std::mem::replace(vector, placeholder_expr(expr.span));
            loop {
                let compatible = match &cursor.kind {
                    ExprKind::VecMap {
                        target: inner_target,
                        callbacks: inner_callbacks,
                        ..
                    } => {
                        *inner_target == *source
                            && inner_callbacks
                                .iter()
                                .chain(merged.iter())
                                .all(safe_callback)
                            && fusion_preserves_allocation_order(
                                types,
                                inner_callbacks.iter().chain(merged.iter()),
                            )
                    }
                    _ => false,
                };
                if !compatible {
                    break;
                }
                let old = std::mem::replace(
                    &mut *cursor,
                    Expr {
                        kind: ExprKind::Constant(0),
                        ty: Type::Unit,
                        span: expr.span,
                        resource: None,
                    },
                );
                let old_ty = old.ty;
                let old_span = old.span;
                let old_resource = old.resource;
                let ExprKind::VecMap {
                    vector: inner_vector,
                    callbacks: mut inner_callbacks,
                    source: inner_source,
                    target: inner_target,
                } = old.kind
                else {
                    unreachable!("checked compatible map")
                };
                let nonempty = inner_callbacks
                    .iter()
                    .chain(merged.iter())
                    .any(|callback| callback_effects(types, callback) != 0);
                if nonempty
                    && crate::runtime_types::type_owns(&types.enums, &types.unions, inner_target, 0)
                {
                    // Restore the untouched layer and stop: an effectful step
                    // must not change when an owning intermediate is dropped.
                    cursor = Box::new(Expr {
                        kind: ExprKind::VecMap {
                            vector: inner_vector,
                            callbacks: inner_callbacks,
                            source: inner_source,
                            target: inner_target,
                        },
                        ty: old_ty,
                        span: old_span,
                        resource: old_resource,
                    });
                    break;
                }
                inner_callbacks.append(&mut merged);
                merged = inner_callbacks;
                *source = inner_source;
                cursor = inner_vector;
                *fusions += 1;
            }
            *callbacks = merged;
            *vector = cursor;
        }
        ExprKind::Constant(_)
        | ExprKind::Erased(_)
        | ExprKind::BytesLiteral(_)
        | ExprKind::Local(_)
        | ExprKind::Move(_)
        | ExprKind::Borrow(_)
        | ExprKind::Peek(_)
        | ExprKind::ArenaNew
        | ExprKind::DynArrayNew { .. }
        | ExprKind::TaskYield
        | ExprKind::TaskCheckCancel
        | ExprKind::Continue(_) => {}
        ExprKind::While(condition, body) => {
            fuse_expr(condition, types, signatures, safety, fusions);
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::Loop(body) => fuse_block(body, types, signatures, safety, fusions),
    }
}

fn callback_effects(types: &Types<'_>, callback: &Expr) -> u8 {
    match callback.ty {
        Type::Fn(id) => types.function_types[id].effects,
        _ => u8::MAX,
    }
}

fn fusion_preserves_allocation_order<'a>(
    types: &Types<'_>,
    callbacks: impl Iterator<Item = &'a Expr>,
) -> bool {
    let callbacks = callbacks.collect::<Vec<_>>();
    let allocating = callbacks
        .iter()
        .filter(|callback| callback_effects(types, callback) != 0)
        .count();
    if allocating == 0 {
        return true;
    }
    if allocating > 1 {
        // Two fallible stages can consume the allocator budget in a different
        // order even when they are total and produce non-owning values.
        return false;
    }
    callbacks.into_iter().all(|callback| {
        if callback_effects(types, callback) != 0 {
            return true;
        }
        let Type::Fn(id) = callback.ty else {
            return false;
        };
        let signature = &types.function_types[id];
        signature
            .parameters
            .iter()
            .copied()
            .chain(std::iter::once(signature.result))
            .all(|ty| !crate::runtime_types::type_owns(&types.enums, &types.unions, ty, 0))
    })
}

fn placeholder_expr(span: Span) -> Box<Expr> {
    Box::new(Expr {
        kind: ExprKind::Constant(0),
        ty: Type::Unit,
        span,
        resource: None,
    })
}

/// Parameter lifetimes that the returned value syntactically derives from. A
/// direct name, field projection, or slice of a parameter carries that
/// parameter's lifetime; block/if/match value positions keep the branches that
/// actually produce the result. This is a conservative inference seed only:
/// the ownership pass still checks every returned origin against the chosen
/// lifetime, so a missed path becomes a checked dangling-borrow error rather
/// than an unsound widening.
fn value_lifetime_candidates(
    resolution: &Resolution,
    expr: &ast::Expr,
    parameter_lifetimes: &BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
    out: &mut BTreeSet<String>,
) {
    match &expr.kind {
        ast::ExprKind::Name(_) => {
            if let Some(id) = resolution.reference(expr.span)
                && let Some(lifetime) = parameter_lifetimes.get(&id)
            {
                out.insert(lifetime.clone());
            }
        }
        ast::ExprKind::Field { value, .. } => {
            // A field projection of a multi-lifetime record parameter inherits
            // exactly that field's declared lifetime. Nested paths use the
            // record's field names, not its erased layout indices.
            if let Some((id, path)) = field_chain(resolution, expr)
                && let Some(fields) = parameter_field_lifetimes.get(&id)
                && let Some(lifetime) = fields.get(&path.join("."))
            {
                out.insert(lifetime.clone());
                return;
            }
            value_lifetime_candidates(
                resolution,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Unary { operand: value, .. } | ast::ExprKind::Try(value) => {
            value_lifetime_candidates(
                resolution,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Slice {
            value, start, end, ..
        } => {
            // Only the sliced base supplies the returned storage; endpoints
            // are integers and cannot name a borrow lifetime.
            let _ = (start, end);
            value_lifetime_candidates(
                resolution,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Block(block) => {
            block_value_lifetime_candidates(
                resolution,
                block,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::If {
            then, otherwise, ..
        } => {
            block_value_lifetime_candidates(
                resolution,
                then,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
            if let Some(otherwise) = otherwise {
                value_lifetime_candidates(
                    resolution,
                    otherwise,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                    out,
                );
            }
        }
        ast::ExprKind::Match { arms, .. } => {
            for arm in arms {
                value_lifetime_candidates(
                    resolution,
                    &arm.body,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                    out,
                );
            }
        }
        _ => {}
    }
}
fn block_value_lifetime_candidates(
    resolution: &Resolution,
    block: &ast::Block,
    parameter_lifetimes: &BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
    out: &mut BTreeSet<String>,
) {
    let mut returns = Vec::new();
    collect_block_returns(block, &mut returns);
    for returned in returns {
        value_lifetime_candidates(
            resolution,
            returned,
            parameter_lifetimes,
            parameter_field_lifetimes,
            out,
        );
    }
    if let Some(tail) = &block.tail {
        value_lifetime_candidates(
            resolution,
            tail,
            parameter_lifetimes,
            parameter_field_lifetimes,
            out,
        );
    }
}
/// The parameter binder and named field path of a projection chain rooted at a
/// parameter name.
fn field_chain(resolution: &Resolution, expr: &ast::Expr) -> Option<(BindingId, Vec<String>)> {
    match &expr.kind {
        ast::ExprKind::Name(_) => Some((resolution.reference(expr.span)?, Vec::new())),
        ast::ExprKind::Field { value, name } => {
            let (id, mut path) = field_chain(resolution, value)?;
            path.push(name.clone());
            Some((id, path))
        }
        _ => None,
    }
}
/// Map each borrowed field path of a parameter type to its declared lifetime,
/// using source field names. Container element leaves use the container field's
/// name; a direct slice or reference field uses its own name.
fn collect_parameter_field_lifetimes(
    types: &crate::runtime_types::Types<'_>,
    ty: Type,
    out: &mut BTreeMap<String, String>,
) {
    fn names(types: &crate::runtime_types::Types<'_>, ty: Type, path: &[usize]) -> Option<String> {
        let mut current = ty;
        let mut names = Vec::with_capacity(path.len());
        for index in path {
            let id = current.layout().filter(|id| types.enums[*id].record)?;
            let variant = &types.enums[id].variants[0];
            names.push(variant.names.get(*index)?.clone());
            current = *variant.fields.get(*index)?;
        }
        Some(names.join("."))
    }
    for leaf in crate::runtime_types::borrow_leaves(types, ty) {
        let Some(lifetime) = leaf.lifetime else {
            continue;
        };
        if let Some(name) = names(types, ty, &leaf.path) {
            out.insert(name, lifetime);
        }
    }
}
/// Whether `long` outlives `short` under a reflexive-transitive bound set.
/// Every lifetime outlives itself; declared bounds supply the strict steps.
pub(crate) fn outlives(bounds: &BTreeSet<(String, String)>, long: &str, short: &str) -> bool {
    long == short || bounds.contains(&(long.to_owned(), short.to_owned()))
}
/// Validate declared function lifetime binders and build the transitive closure
/// of their outlives bounds. Bounds name declared lifetimes only, duplicates and
/// cycles are rejected, and a self bound is accepted as reflexivity.
pub(crate) fn build_lifetime_bounds(
    lifetimes: &[ast::Lifetime],
) -> Result<BTreeSet<(String, String)>> {
    let declared = lifetimes
        .iter()
        .map(|lifetime| lifetime.name.as_str())
        .collect::<BTreeSet<_>>();
    let mut edges = BTreeSet::new();
    let mut spans = BTreeMap::new();
    let mut seen_bounds = BTreeSet::new();
    for lifetime in lifetimes {
        for bound in &lifetime.bounds {
            if !declared.contains(bound.name.as_str()) {
                return Err(Diagnostic::new(
                    bound.span,
                    format!(
                        "outlives bound refers to undeclared lifetime '{}'; declare it in the function's lifetime parameter list",
                        bound.name
                    ),
                ));
            }
            if !seen_bounds.insert((lifetime.name.clone(), bound.name.clone())) {
                return Err(Diagnostic::new(
                    bound.span,
                    format!(
                        "duplicate outlives bound '{}: {}'",
                        lifetime.name, bound.name
                    ),
                ));
            }
            // A self bound is satisfied by reflexivity and contributes no edge.
            if bound.name == lifetime.name {
                continue;
            }
            edges.insert((lifetime.name.clone(), bound.name.clone()));
            spans.insert((lifetime.name.clone(), bound.name.clone()), bound.span);
        }
    }
    let mut closure = edges;
    loop {
        let mut added = Vec::new();
        for (long, short) in &closure {
            for (other_long, other_short) in &closure {
                if short == other_long {
                    let edge = (long.clone(), other_short.clone());
                    if !closure.contains(&edge) {
                        added.push(edge);
                    }
                }
            }
        }
        if added.is_empty() {
            break;
        }
        closure.extend(added);
    }
    // A cycle makes the members equal, which needs one shared lifetime rather
    // than a mutually bounded pair. Rejecting it keeps the order a strict DAG.
    if let Some(((long, short), span)) = spans
        .iter()
        .find(|((long, short), _)| closure.contains(&(short.clone(), long.clone())))
    {
        return Err(Diagnostic::new(
            *span,
            format!(
                "cyclic outlives bounds are not supported: '{long}' and '{short}' would be the same lifetime; use one lifetime parameter"
            ),
        ));
    }
    Ok(closure)
}
fn is_grade_generic(resolution: &Resolution, generic: &ast::Generic) -> bool {
    generic.bound.as_ref().is_some_and(|bound| {
        resolution.reference(bound.span).is_some_and(|id| {
            resolution.bindings[id].kind == BindingKind::Builtin
                && resolution.bindings[id].name == "Grade"
        })
    })
}
/// Whether a generic binder is a compile-time natural `<N: Nat>`.
fn is_const_generic(resolution: &Resolution, generic: &ast::Generic) -> bool {
    crate::runtime_types::is_const_generic(resolution, generic)
}
/// The first row variable that does *not* declare an exclusion for `effect`.
///
/// A contract such as `#[noalloc]` on an effect-polymorphic function is sound
/// only when every row variable in the signature's effect row excludes that
/// effect. An unconstrained variable, or a mix of constrained and unconstrained
/// variables, keeps the old rejection.
fn first_unexcluded_effect_variable(
    resolution: &Resolution,
    function: &ast::Function,
    variables: &[BindingId],
    effect: u8,
) -> Result<Option<BindingId>> {
    for variable in variables {
        let generic = function
            .generics
            .iter()
            .find(|generic| resolution.binder(generic.span) == Some(*variable));
        let excluded = generic
            .map(|generic| crate::runtime_types::effect_excludes(resolution, generic))
            .transpose()?
            .flatten()
            .unwrap_or(0);
        // A lower bound `+ effect` guarantees the forbidden effect is present,
        // so it is never a valid `#[noalloc]`/`#[nosuspend]` specialization.
        let included = generic
            .map(|generic| crate::runtime_types::effect_includes(resolution, generic))
            .transpose()?
            .flatten()
            .unwrap_or(0);
        if excluded & effect == 0 || included & effect != 0 {
            return Ok(Some(*variable));
        }
    }
    Ok(None)
}
/// Render a concrete effect set for diagnostics, in declaration order.
fn effect_names(bits: u8) -> String {
    [
        (PANIC, "panic"),
        (IO, "io"),
        (ALLOC, "alloc"),
        (SUSPEND, "suspend"),
    ]
    .into_iter()
    .filter_map(|(bit, name)| (bits & bit != 0).then_some(name))
    .collect::<Vec<_>>()
    .join(", ")
}
/// An executable `fn` declaration before specialization.
#[derive(Clone, Copy)]
struct Declared<'a> {
    ast: &'a ast::Function,
    span: Span,
    /// Concrete `Self` target for an impl method. Ordinary functions are `None`
    /// and reject any stray `Self` during type lowering.
    self_ty: Option<Type>,
    /// Index into `Functions::default_specializations` for a trait default
    /// method materialized for one impl. The entry supplies the trait's
    /// concrete type/Nat/Grade/effect arguments, which are substituted into the
    /// default body's signature exactly like `Self`.
    default_specialization: Option<usize>,
    /// Associated values of the impl that owns this method. `Self::Item` and
    /// `Self::CONST` normalize through this entry.
    impl_associated: Option<usize>,
    /// Index into `Functions::impl_headers` when the method belongs to a
    /// generic impl. Its receiver type and impl generics are supplied per
    /// instance by `MethodDefinition::impl_arguments`.
    impl_template: Option<usize>,
}
/// One method declared by a trait: its declaration span and signature, with an
/// optional default body borrowed from the module AST.
#[derive(Clone, Copy)]
struct TraitMethod<'a> {
    span: Span,
    function: &'a ast::Function,
}
/// One associated item declared by a trait.
#[derive(Debug, Clone)]
enum TraitAssociated {
    /// An associated type declaration, optionally with a default type that an
    /// impl inherits when it omits `type Name = ...`.
    Type {
        /// A default type, substituted with the impl's trait arguments and
        /// materialized per impl. It may mention the trait's parameters but
        /// not `Self`; `Self::Other` is permitted and checked for cycles.
        default: Option<ast::Type>,
    },
    Const {
        ty: ast::Type,
        /// A default value inherited by impls that omit the constant.
        default: Option<ast::Expr>,
    },
}
/// One declared trait: its generic parameters, associated items, and method
/// declarations.
#[derive(Clone)]
struct TraitDefinition<'a> {
    generics: Vec<ast::Generic>,
    associated: BTreeMap<String, TraitAssociated>,
    /// Associated item names in declaration order. Constant defaults may
    /// reference earlier constants, so inheritance evaluates in this order.
    associated_order: Vec<String>,
    methods: BTreeMap<String, TraitMethod<'a>>,
}
/// A checked compile-time associated constant. Scalar values carry their bit
/// representation; tuples and inline arrays of constants carry recursively
/// checked element values. The value is substituted wherever the constant is
/// named, so it has no runtime storage, address, or accessor function.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ConstValue {
    ty: Type,
    /// Scalar bit representation. Aggregate values use `elements`.
    bits: i64,
    /// Element values for a tuple or inline-array constant; empty for scalars.
    elements: Vec<ConstValue>,
}
impl ConstValue {
    fn scalar(ty: Type, bits: i64) -> Self {
        Self {
            ty,
            bits,
            elements: Vec::new(),
        }
    }
    fn aggregate(ty: Type, elements: Vec<ConstValue>) -> Self {
        Self {
            ty,
            bits: 0,
            elements,
        }
    }
}
/// Associated values supplied by one impl, from which `Self::Item` projections
/// and `Self::CONST` references are normalized for that impl's methods and
/// inherited defaults.
#[derive(Debug, Clone, Default)]
struct ImplAssociated {
    types: BTreeMap<String, ast::Type>,
    consts: BTreeMap<String, ConstValue>,
}
/// Canonical, checked arguments that select one trait specialization. Each
/// vector is in declaration order among parameters of that category, exactly
/// like a function instance key.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TraitArguments {
    pub(crate) types: Vec<Type>,
    pub(crate) consts: Vec<usize>,
    pub(crate) grades: Vec<Grade>,
    pub(crate) effects: Vec<u8>,
}
/// Concrete arguments for the generic parameters of one impl header. Stored by
/// index so `MethodDefinition` stays `Copy`.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
struct ImplArguments {
    types: Vec<Type>,
    consts: Vec<usize>,
    grades: Vec<Grade>,
    effects: Vec<u8>,
}
/// One generic or blanket impl header. The self type and trait arguments are
/// patterns over `generics`; concrete receivers are matched against them by
/// first-order unification, and the unique most-specific matching impl wins.
#[derive(Debug, Clone)]
struct ImplHeader {
    /// `None` for an inherent `impl<T> Type<T>` block.
    trait_id: Option<BindingId>,
    generics: Vec<ast::Generic>,
    self_ty: ast::Type,
    /// Raw trait argument patterns, aligned with the trait's generic
    /// parameters. Empty for inherent impls.
    trait_arguments: Vec<ast::Type>,
    associated: ImplAssociated,
    methods: BTreeMap<String, MethodDefinition>,
    span: Span,
    /// Concrete lowered header for monomorphic impls, used by coherence and by
    /// exact lookup. `None` for generic headers.
    concrete: Option<(TraitArguments, Type)>,
}
/// One match of a generic impl header against a concrete obligation.
#[derive(Debug, Clone)]
struct ImplMatch {
    header: usize,
    arguments: ImplArguments,
}
/// One interned generic-impl instantiation.
#[derive(Debug, Clone)]
struct ImplInstantiation {
    header: usize,
    arguments: ImplArguments,
    self_type: Type,
    trait_arguments: TraitArguments,
}
/// The category of one generic binder. Function generics and trait parameters
/// use the same classification; only ordinary types are runtime values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GenericCategory {
    Type,
    Const,
    Grade,
    Effect,
}
fn generic_category(resolution: &Resolution, generic: &ast::Generic) -> GenericCategory {
    if is_grade_generic(resolution, generic) {
        GenericCategory::Grade
    } else if is_const_generic(resolution, generic) {
        GenericCategory::Const
    } else if crate::runtime_types::is_effect_generic(resolution, generic) {
        GenericCategory::Effect
    } else {
        GenericCategory::Type
    }
}
/// Whether a type can be the declared type of an associated constant. Scalar
/// machine values and finite tuples/inline arrays of such values have a
/// canonical compile-time representation.
fn const_scalar_type(types: &Types<'_>, ty: Type) -> bool {
    fn allowed(types: &Types<'_>, ty: Type, depth: usize) -> bool {
        if depth >= 8 {
            return false;
        }
        if matches!(ty, Type::I64 | Type::Int(_) | Type::Bool | Type::Char) {
            return true;
        }
        let Some(layout) = ty.layout() else {
            return false;
        };
        if let Some((element, _)) = types.enums[layout].array {
            return allowed(types, element, depth + 1);
        }
        types.enums[layout].tuple
            && types.enums[layout].variants[0]
                .fields
                .iter()
                .all(|field| allowed(types, *field, depth + 1))
    }
    allowed(types, ty, 0)
}
/// Evaluate a constant expression for an associated constant. The subset is
/// deliberately compile-time only: scalar literals, tuple/array literals of
/// constants, earlier associated constants of the same impl, checked integer
/// arithmetic, shifts, boolean operators, and integer comparisons. Calls,
/// effects, and runtime values are rejected, so an associated constant can
/// never hide work at a use site.
fn evaluate_associated_const(
    types: &Types<'_>,
    expr: &ast::Expr,
    expected: Type,
    consts: &BTreeMap<String, ConstValue>,
) -> Result<ConstValue> {
    match expected {
        Type::Bool => {
            let value = evaluate_const_bool(expr, consts, 0)?;
            Ok(ConstValue::scalar(Type::Bool, i64::from(value)))
        }
        Type::Char => match &expr.kind {
            ast::ExprKind::Char(ch) => {
                Ok(ConstValue::scalar(Type::Char, i64::from(u32::from(*ch))))
            }
            ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
                const_reference(types, consts, name, Type::Char)
            }
            _ => Err(Diagnostic::new(
                expr.span,
                "a Char associated constant must be a character literal or another Char constant",
            )),
        },
        Type::I64 | Type::Int(_) => {
            let value = evaluate_const_int(expr, consts)?;
            let kind = expected.int_kind().expect("integer constant type");
            let bits = kind.encode(value).ok_or_else(|| {
                Diagnostic::new(
                    expr.span,
                    format!(
                        "associated constant value {value} is outside the range of {}",
                        kind.name()
                    ),
                )
            })?;
            Ok(ConstValue::scalar(expected, bits))
        }
        _ => {
            let Some(layout) = expected.layout() else {
                return Err(Diagnostic::new(
                    expr.span,
                    "associated constants must have a compile-time scalar, tuple, or inline-array type",
                ));
            };
            if let Some((element, length)) = types.enums[layout].array {
                let items = match &expr.kind {
                    ast::ExprKind::Array(items) => items.clone(),
                    ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
                        return const_reference(types, consts, name, expected);
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            expr.span,
                            "an array associated constant must be an array literal or an earlier constant of the same type",
                        ));
                    }
                };
                if items.len() != length {
                    return Err(Diagnostic::new(
                        expr.span,
                        format!(
                            "array associated constant has {} element(s), but its type needs {length}",
                            items.len()
                        ),
                    ));
                }
                let mut elements = Vec::with_capacity(items.len());
                for item in &items {
                    elements.push(evaluate_associated_const(types, item, element, consts)?);
                }
                return Ok(ConstValue::aggregate(expected, elements));
            }
            if types.enums[layout].tuple {
                let field_types = types.enums[layout].variants[0].fields.clone();
                let items = match &expr.kind {
                    ast::ExprKind::Tuple(items) => items.clone(),
                    ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
                        return const_reference(types, consts, name, expected);
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            expr.span,
                            "a tuple associated constant must be a tuple literal or an earlier constant of the same type",
                        ));
                    }
                };
                if items.len() != field_types.len() {
                    return Err(Diagnostic::new(
                        expr.span,
                        format!(
                            "tuple associated constant has {} element(s), but its type needs {}",
                            items.len(),
                            field_types.len()
                        ),
                    ));
                }
                let mut elements = Vec::with_capacity(items.len());
                for (item, field_ty) in items.iter().zip(field_types) {
                    elements.push(evaluate_associated_const(types, item, field_ty, consts)?);
                }
                return Ok(ConstValue::aggregate(expected, elements));
            }
            Err(Diagnostic::new(
                expr.span,
                "associated constants must have a compile-time scalar, tuple, or inline-array type",
            ))
        }
    }
}
/// Lower one checked compile-time constant to an ordinary checked expression.
/// Scalars are literals; tuples and arrays reconstruct their canonical layout
/// from recursively lowered elements.
fn const_value_expr(value: &ConstValue, span: Span) -> Result<Expr> {
    let kind = if let Some(layout) = value.ty.layout() {
        let fields = value
            .elements
            .iter()
            .map(|element| const_value_expr(element, span))
            .collect::<Result<Vec<_>>>()?;
        ExprKind::Construct {
            enum_id: layout,
            tag: 0,
            fields,
        }
    } else {
        ExprKind::Constant(value.bits)
    };
    Ok(Expr {
        kind,
        ty: value.ty,
        span,
        resource: None,
    })
}
fn const_reference(
    types: &Types<'_>,
    consts: &BTreeMap<String, ConstValue>,
    name: &str,
    expected: Type,
) -> Result<ConstValue> {
    let Some(value) = consts.get(name) else {
        return Err(Diagnostic::new(
            Span::default(),
            format!(
                "unknown associated constant '{name}'; constants may reference earlier constants of the same impl"
            ),
        ));
    };
    if value.ty != expected {
        return Err(Diagnostic::new(
            Span::default(),
            format!(
                "associated constant '{name}' has type {}, not {}",
                types.name(value.ty),
                types.name(expected)
            ),
        ));
    }
    Ok(value.clone())
}
fn evaluate_const_int(expr: &ast::Expr, consts: &BTreeMap<String, ConstValue>) -> Result<i128> {
    match &expr.kind {
        ast::ExprKind::Integer(text) => text
            .parse::<i128>()
            .map_err(|_| Diagnostic::new(expr.span, "integer literal is too large for a constant")),
        ast::ExprKind::Unary {
            op: crate::lexer::Kind::Minus,
            operand,
            ..
        } => Ok(-evaluate_const_int(operand, consts)?),
        ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
            let Some(value) = consts.get(name) else {
                return Err(Diagnostic::new(
                    expr.span,
                    format!(
                        "unknown associated constant '{name}'; constants may reference earlier constants of the same impl"
                    ),
                ));
            };
            if !value.elements.is_empty() {
                return Err(Diagnostic::new(
                    expr.span,
                    "this associated constant is an aggregate, not an integer",
                ));
            }
            match value.ty.int_kind() {
                Some(kind) => Ok(kind.decode(value.bits)),
                None => Err(Diagnostic::new(
                    expr.span,
                    "this associated constant is not an integer",
                )),
            }
        }
        ast::ExprKind::Binary { op, left, right } => {
            let left = evaluate_const_int(left, consts)?;
            let right = evaluate_const_int(right, consts)?;
            use crate::lexer::Kind;
            let value = match op {
                Kind::Plus => left.checked_add(right),
                Kind::Minus => left.checked_sub(right),
                Kind::Star => left.checked_mul(right),
                Kind::Slash => left.checked_div(right),
                Kind::Percent => left.checked_rem(right),
                Kind::Shl => u32::try_from(right)
                    .ok()
                    .and_then(|shift| left.checked_shl(shift)),
                Kind::Shr => u32::try_from(right)
                    .ok()
                    .and_then(|shift| left.checked_shr(shift)),
                Kind::Amp => Some(left & right),
                Kind::Pipe => Some(left | right),
                Kind::Caret => Some(left ^ right),
                _ => {
                    return Err(Diagnostic::new(
                        expr.span,
                        "this operator is not supported in an integer associated constant",
                    ));
                }
            };
            value.ok_or_else(|| {
                Diagnostic::new(
                    expr.span,
                    "associated constant arithmetic overflows or divides by zero",
                )
            })
        }
        _ => Err(Diagnostic::new(
            expr.span,
            "associated constant values must be literals, earlier constants, and checked arithmetic",
        )),
    }
}
fn evaluate_const_bool(
    expr: &ast::Expr,
    consts: &BTreeMap<String, ConstValue>,
    depth: usize,
) -> Result<bool> {
    if depth >= 64 {
        return Err(Diagnostic::new(
            expr.span,
            "associated constant expression is too deeply nested",
        ));
    }
    match &expr.kind {
        ast::ExprKind::Bool(value) => Ok(*value),
        ast::ExprKind::Name(name) | ast::ExprKind::Field { name, .. } => {
            let Some(value) = consts.get(name) else {
                return Err(Diagnostic::new(
                    expr.span,
                    format!("unknown associated constant '{name}'"),
                ));
            };
            match value.ty {
                Type::Bool if value.elements.is_empty() => Ok(value.bits != 0),
                _ => Err(Diagnostic::new(
                    expr.span,
                    "this associated constant is not a Bool",
                )),
            }
        }
        ast::ExprKind::Unary {
            op: crate::lexer::Kind::Bang,
            operand,
            ..
        } => Ok(!evaluate_const_bool(operand, consts, depth + 1)?),
        ast::ExprKind::Binary { op, left, right } => {
            use crate::lexer::Kind;
            match op {
                Kind::AmpAmp => {
                    let left = evaluate_const_bool(left, consts, depth + 1)?;
                    Ok(left && evaluate_const_bool(right, consts, depth + 1)?)
                }
                Kind::PipePipe => {
                    let left = evaluate_const_bool(left, consts, depth + 1)?;
                    Ok(left || evaluate_const_bool(right, consts, depth + 1)?)
                }
                Kind::Eq | Kind::Ne | Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge => {
                    let left = evaluate_const_int(left, consts)?;
                    let right = evaluate_const_int(right, consts)?;
                    Ok(match op {
                        Kind::Eq => left == right,
                        Kind::Ne => left != right,
                        Kind::Lt => left < right,
                        Kind::Le => left <= right,
                        Kind::Gt => left > right,
                        Kind::Ge => left >= right,
                        _ => unreachable!(),
                    })
                }
                _ => Err(Diagnostic::new(
                    expr.span,
                    "this operator is not supported in a Bool associated constant",
                )),
            }
        }
        _ => Err(Diagnostic::new(
            expr.span,
            "Bool associated constant values must be literals, earlier constants, comparisons, and boolean operators",
        )),
    }
}
/// One statically dispatched method: its checked function binding and visibility.
#[derive(Debug, Clone, Copy)]
struct MethodDefinition {
    binding: BindingId,
    public: bool,
    unit: usize,
    /// Index into `Functions::impl_instantiations` for a method selected from a
    /// generic impl. Concrete methods leave this `None`.
    impl_arguments: Option<usize>,
}
/// Key of a checked function instance: binding plus type, grade, effect, and
/// natural const arguments.
type InstanceKey = (
    BindingId,
    Vec<Type>,
    Vec<Grade>,
    Vec<usize>,
    Vec<u8>,
    Option<usize>,
);
/// One receiver type's trait-provided methods, each with the specialization
/// arguments that select it.
type TraitMethodTable = BTreeMap<String, Vec<(BindingId, TraitArguments, MethodDefinition)>>;
/// Type, grade, const, and effect arguments of one specialization.
type GenericArguments = (Vec<Type>, Vec<Grade>, Vec<usize>, Vec<u8>);
/// Generic arguments and checked values produced by inference.
type Inferred = (Vec<Type>, Vec<Grade>, Vec<usize>, Vec<u8>, Vec<Expr>);
/// Function instances. A monomorphic function has one instance; a generic
/// function gets one per distinct list of type arguments that is used.
struct Functions<'a> {
    declared: BTreeMap<BindingId, Declared<'a>>,
    signatures: Vec<Signature>,
    /// Checked bodies aligned with `signatures`; `None` still needs checking,
    /// `Some` is a synthetic lambda/adapter body.
    bodies: Vec<Option<Function>>,
    instances: BTreeMap<InstanceKey, usize>,
    pending: Vec<usize>,
    /// Synthetic function adapter cache, keyed by optional static source
    /// function index and the source/target arrow types.
    adapter_cache: BTreeMap<(Option<usize>, Type, Type), usize>,
    certificates: Vec<crate::facts::Certificate>,
    /// Checked nested map fusions produced while specializing bodies.
    fusions: usize,
    /// Set when any body uses a structured-task operation.
    uses_tasks: bool,
    /// Task body functions whose binding-based linear result must be rejected
    /// once their body has been checked.
    /// Monotonic counter for compiler-internal elided input lifetimes. The
    /// generated names are not surface syntax, so they cannot collide with a
    /// declared lifetime name.
    elided_lifetimes: usize,
    /// Declared traits and their method signatures (with `Self` still
    /// symbolic). Used for exact impl-signature comparison and to materialize
    /// inherited default bodies.
    traits: BTreeMap<BindingId, TraitDefinition<'a>>,
    /// Inherent methods keyed by concrete receiver type and method name.
    inherent: BTreeMap<Type, BTreeMap<String, MethodDefinition>>,
    /// Trait methods keyed by trait binding, canonical trait arguments, and
    /// concrete receiver type, then method name.
    trait_impls: BTreeMap<(BindingId, TraitArguments, Type), BTreeMap<String, MethodDefinition>>,
    /// Every trait method available for a concrete receiver type, for
    /// unqualified dispatch and deterministic ambiguity diagnostics.
    methods_by_type: BTreeMap<Type, TraitMethodTable>,
    /// Trait specializations inherited by materialized default methods, indexed
    /// by `Declared::default_specialization`.
    default_specializations: Vec<(BindingId, TraitArguments)>,
    /// Associated values of each impl, indexed by `Declared::impl_associated`.
    impl_associated: Vec<ImplAssociated>,
    /// Inherent associated constants keyed by the nominal target type.
    inherent_consts: BTreeMap<Type, BTreeMap<String, ConstValue>>,
    /// Associated constants of every trait impl, keyed by trait, canonical
    /// trait arguments, and receiver type. Used by `Type.CONST` projections.
    trait_consts: BTreeMap<(BindingId, TraitArguments, Type), BTreeMap<String, ConstValue>>,
    /// Associated values of every trait impl, keyed like `trait_impls`.
    trait_associated: BTreeMap<(BindingId, TraitArguments, Type), ImplAssociated>,
    /// Every declared impl header, concrete or generic, in declaration order.
    /// Coherence comparisons and generic dispatch both use this table.
    impl_headers: Vec<ImplHeader>,
    /// Deduplicated instantiations of generic impl headers. A method selected
    /// from `impl_headers[i]` points here so its body is monomorphized once per
    /// concrete impl-argument list.
    impl_instantiations: Vec<ImplInstantiation>,
    impl_instantiation_cache: BTreeMap<(usize, ImplArguments), usize>,
    /// Closed-world trait objects keyed by their runtime union type. One union
    /// may represent several traits when their concrete member sets coincide;
    /// unqualified dispatch then requires an unambiguous trait method name.
    object_traits: BTreeMap<Type, Vec<(BindingId, TraitArguments)>>,
    /// Checked dynamic-dispatch functions, one per `(trait, arguments, method)`.
    dynamic_dispatch: BTreeMap<(BindingId, TraitArguments, String), (usize, Type)>,
    /// Associated-type values agreed by every concrete impl of one object
    /// specialization. Used for `Self.Item` in object-safe method signatures.
    object_associated: BTreeMap<(BindingId, TraitArguments), BTreeMap<String, Type>>,
    logical: &'a crate::check::LogicalEnvironment,
}
const MAX_FUNCTIONS: usize = 256;

/// Check one in-memory file. Only standard-library modules can be imported.
pub fn check(source: &str) -> Result<Executable> {
    let program = crate::program::load_source("<input>", source).map_err(|(_, e)| e)?;
    check_program(&program)
}
/// Check a loaded multi-module program. Only the root module may define `main`.
pub fn check_program(program: &crate::program::Program) -> Result<Executable> {
    let module = &program.module;
    let mut resolution = resolve::resolve_program(program)?;
    // Default trait methods inherited by an impl need one synthetic function
    // binding per (impl, method) pair. Allocate them before `Types` borrows the
    // resolver table: the table cannot be mutated once type lowering holds it.
    let default_bindings = collect_default_bindings(module, &mut resolution)?;
    crate::grades::validate_algebras(&mut resolution)?;
    let resolution = &resolution;
    // Total functions and aliases are erased and checked by the trusted kernel
    // before any executable body can cite them as proof evidence.
    let logical = crate::check::check_program(module, resolution)?;
    let mut types = Types::new(module, resolution, &logical)?;
    let mut functions = Functions {
        declared: BTreeMap::new(),
        signatures: Vec::new(),
        bodies: Vec::new(),
        instances: BTreeMap::new(),
        pending: Vec::new(),
        adapter_cache: BTreeMap::new(),
        certificates: Vec::new(),
        fusions: 0,
        uses_tasks: false,
        elided_lifetimes: 0,
        traits: BTreeMap::new(),
        inherent: BTreeMap::new(),
        trait_impls: BTreeMap::new(),
        methods_by_type: BTreeMap::new(),
        default_specializations: Vec::new(),
        impl_associated: Vec::new(),
        inherent_consts: BTreeMap::new(),
        trait_consts: BTreeMap::new(),
        trait_associated: BTreeMap::new(),
        impl_headers: Vec::new(),
        impl_instantiations: Vec::new(),
        impl_instantiation_cache: BTreeMap::new(),
        object_traits: BTreeMap::new(),
        dynamic_dispatch: BTreeMap::new(),
        object_associated: BTreeMap::new(),
        logical: &logical,
    };
    let mut monomorphic = Vec::new();
    for declaration in &module.items {
        let span = declaration.item.span;
        if !declaration.attributes.is_empty()
            && !matches!(
                declaration.item.kind,
                ast::ItemKind::Function(_)
                    | ast::ItemKind::Enum { .. }
                    | ast::ItemKind::Struct { .. }
            )
        {
            return Err(Diagnostic::new(
                span,
                "attributes apply to functions, enums, and structs only",
            ));
        }
        let function = matches!(declaration.item.kind, ast::ItemKind::Function(_));
        for attribute in &declaration.attributes {
            let valid = if function {
                matches!(attribute.kind.as_str(), "noalloc" | "nosuspend")
            } else {
                attribute.kind == "linear"
            };
            if !valid {
                return Err(Diagnostic::new(
                    attribute.span,
                    if function {
                        "functions support the #[noalloc] and #[nosuspend] contracts"
                    } else {
                        "data declarations support only the #[linear] attribute"
                    },
                ));
            }
        }
        let f = match &declaration.item.kind {
            ast::ItemKind::Module(_)
            | ast::ItemKind::Enum { .. }
            | ast::ItemKind::Prop { .. }
            | ast::ItemKind::Struct { .. }
            | ast::ItemKind::Trait { .. }
            | ast::ItemKind::Impl { .. }
            | ast::ItemKind::GradeAlgebra(_)
            | ast::ItemKind::Use(_) => continue,
            ast::ItemKind::Alias { .. } => continue,
            ast::ItemKind::Function(f) => f,
        };
        if f.total {
            // Checked by the logical kernel above and erased from runtime IR.
            continue;
        }
        for parameter in &f.parameters {
            if parameter.erased && split_grade(&parameter.ty).1.is_some() {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "erased parameters are already absent at runtime and cannot carry a usage grade",
                ));
            }
        }
        validate_erased_parameters(resolution, &logical, f)?;
        validate_length_templates(resolution, f)?;
        if f.body.is_none() {
            return Err(Diagnostic::new(
                span,
                "executable functions require a body; foreign declarations are not implemented",
            ));
        }
        if f.parameters.len() > 64 {
            return Err(Diagnostic::new(
                span,
                "executable limit exceeded (64 parameters)",
            ));
        }
        for generic in &f.generics {
            if let Some(bound) = &generic.bound {
                let binding = resolution
                    .reference(bound.span)
                    .map(|id| &resolution.bindings[id]);
                let supported = match binding {
                    Some(binding) if binding.kind == BindingKind::Builtin => {
                        matches!(binding.name.as_str(), "Type" | "Grade" | "Nat" | "Effects")
                    }
                    Some(binding) if binding.kind == BindingKind::Trait => {
                        matches!(&bound.kind, ast::TypeKind::Named { .. })
                    }
                    _ => false,
                };
                if !supported {
                    return Err(Diagnostic::new(
                        generic.span,
                        "executable generic parameters must be types, grades, compile-time naturals, effect rows, or declared traits ('T: Type', 'G: Grade', 'N: Nat', 'e: Effects', 'T: Trait')",
                    ));
                }
            }
        }
        let (fixed_effects, effect_variables) =
            crate::runtime_types::effect_bits_partial(resolution, &f.effects)?;
        let noalloc = declaration.attributes.iter().any(|a| a.kind == "noalloc");
        if noalloc {
            if fixed_effects & ALLOC != 0 {
                return Err(Diagnostic::new(
                    span,
                    "noalloc contract forbids the alloc effect",
                ));
            }
            if let Some(variable) =
                first_unexcluded_effect_variable(resolution, f, &effect_variables, ALLOC)?
            {
                return Err(Diagnostic::new(
                    resolution.bindings[variable].span,
                    "noalloc contracts cannot be effect-polymorphic: the effect row variable may be specialized with 'alloc', so the noalloc guarantee would depend on specialization",
                ));
            }
        }
        let nosuspend = declaration.attributes.iter().any(|a| a.kind == "nosuspend");
        if nosuspend {
            if fixed_effects & SUSPEND != 0 {
                return Err(Diagnostic::new(
                    span,
                    "nosuspend contract forbids the suspend effect",
                ));
            }
            if let Some(variable) =
                first_unexcluded_effect_variable(resolution, f, &effect_variables, SUSPEND)?
            {
                return Err(Diagnostic::new(
                    resolution.bindings[variable].span,
                    "nosuspend contracts cannot be effect-polymorphic: the effect row variable may be specialized with 'suspend', so the nosuspend guarantee would depend on specialization",
                ));
            }
        }
        let binding = resolution.declarations[&span.start];
        if f.name == "main"
            && !f.generics.is_empty()
            && resolution.unit_of.get(&binding) == Some(&0)
        {
            return Err(Diagnostic::new(span, "main must not be generic"));
        }
        functions.declared.insert(
            binding,
            Declared {
                ast: f,
                span,
                self_ty: None,
                default_specialization: None,
                impl_associated: None,
                impl_template: None,
            },
        );
        if f.generics.is_empty() {
            monomorphic.push(binding);
        }
    }
    let method_bindings = collect_methods(
        module,
        resolution,
        &default_bindings,
        &mut types,
        &logical,
        &mut functions,
    )?;
    prepare_trait_objects(&mut types, resolution, &mut functions)?;
    // Generic methods are monomorphized on demand at each call site. Only
    // monomorphic methods get an eagerly checked instance here.
    monomorphic.extend(method_bindings.into_iter().filter(|binding| {
        let declared = functions.declared[binding];
        // A generic impl method is instantiated only after dispatch
        // selects concrete impl arguments; it has no `Self` otherwise.
        declared.ast.generics.is_empty() && declared.impl_template.is_none()
    }));
    for binding in monomorphic {
        functions.instance(
            &mut types,
            resolution,
            binding,
            vec![],
            vec![],
            vec![],
            vec![],
            None,
            None,
        )?;
    }
    let mut entry = None;
    while let Some(index) = functions.pending.pop() {
        if functions.bodies[index].is_some() {
            continue;
        }
        let sig = functions.signatures[index].clone();
        let f = functions.declared[&sig.binding].ast;
        if sig.name == "main" && resolution.unit_of.get(&sig.binding) == Some(&0) {
            if !sig.parameters.is_empty() || !matches!(sig.result, Type::I64 | Type::Unit) {
                return Err(Diagnostic::new(
                    sig.span,
                    "main must have no parameters and return i64 or Unit",
                ));
            }
            if sig.result_grade.is_some() {
                return Err(Diagnostic::new(
                    sig.span,
                    "main cannot carry a result usage contract; its process result has no caller to transfer or erase it",
                ));
            }
            entry = Some(index);
        }
        let mut checker = Checker {
            resolution,
            types: &mut types,
            functions: &mut functions,
            substitution: sig.substitution.clone(),
            consts: sig.consts.clone(),
            grades: sig.grades.clone(),
            effect_arguments: sig.effect_arguments.clone(),
            locals: Vec::new(),
            slots: BTreeMap::new(),
            result: sig.result,
            parameter_lifetimes: sig.parameter_lifetimes.clone(),
            result_grade: sig.result_grade,
            effects: sig.effects,
            depth: 0,
            loops: Vec::new(),
            facts: crate::facts::Facts::default(),
            proofs: BTreeMap::new(),
            logical: &logical,
            kernel_locals: Vec::new(),
            kernel_types: BTreeMap::new(),
            kernel_proofs: BTreeMap::new(),
            scope_depth: 0,
            next_split: 0,
            self_type: sig.self_type,
            default_trait: sig.default_trait.clone(),
            associated_consts: sig.associated_consts.clone(),
            unit: resolution.unit_of.get(&sig.binding).copied().unwrap_or(0),
            field_place: false,
            binding: sig.binding,
            scalar_epochs: BTreeMap::new(),
            kernel_aliases: BTreeMap::new(),
            handlers: Vec::new(),
            effect_constraints: Vec::new(),
        };
        let body = (|| {
            let mut runtime = sig.parameters.iter().zip(&sig.parameter_grades);
            for p in &f.parameters {
                if p.erased {
                    checker.assume_parameter(p)?;
                } else {
                    let (ty, grade) = runtime.next().unwrap();
                    let slot = checker.bind(p.span, *ty, false)?;
                    checker.locals[slot].grade = *grade;
                    checker.locals[slot].linear =
                        grade.is_some_and(Grade::is_one) && checker.owned_type(*ty);
                    checker.validate_grade(*grade, *ty, p.ty.span, false)?;
                    let id = resolution.binder(p.span).unwrap();
                    checker.admit_scalar_index(id, *ty, p.span)?;
                }
            }
            let body = checker.block(f.body.as_ref().unwrap(), Some(sig.result))?;
            if body.ty != Type::Never
                && !(sig.result_grade.is_some_and(Grade::is_zero) && body.ty == Type::Unit)
            {
                checker.expect(body.ty, sig.result, sig.span)?;
            }
            if body.ty != Type::Never
                && let Some(tail) = &body.tail
                && checker.observes_copyable_result(tail)
                && !checker.transfers_copyable_result_from(tail)
            {
                return Err(Diagnostic::new(
                    tail.span,
                    "this function returns a copyable result with the must-use `@[1]` contract through an ungraded result; annotate the result as '@[1]' so every caller inherits exactly one observation, or observe the value inside the function",
                ));
            }
            Ok(body)
        })();
        let body = body.map_err(|mut e: Diagnostic| {
            if let Some((span, text)) = &sig.origin {
                e = e.with_note(
                    *span,
                    format!("in the specialization {text} requested here"),
                );
            }
            e
        })?;
        // A copyable `@[0]` result has no payload at runtime. The value is
        // still computed for effects (and for type checking against the
        // declared result), then erased in the callee. `Drop` is a checked
        // no-op for copyable values; an owning result is rejected by the
        // contract validator before this point.
        let mut body = body;
        if sig.result_grade.is_some_and(Grade::is_zero) && body.ty != Type::Never {
            let span = body.tail.as_deref().map_or(sig.span, |tail| tail.span);
            let tail = body.tail.take().unwrap_or_else(|| {
                Box::new(Expr {
                    kind: ExprKind::Constant(0),
                    ty: Type::Unit,
                    span,
                    resource: None,
                })
            });
            let erased = Expr {
                kind: ExprKind::Drop(tail),
                ty: Type::Unit,
                span,
                resource: None,
            };
            body.tail = Some(Box::new(erased));
            body.ty = Type::Unit;
        }
        let obligation = checker.return_obligation(&body);
        if let Some(span) = obligation
            && sig.result_grade.is_none()
            && !checker.linear_type(sig.result)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' returns a linear obligation through an ungraded result; annotate the result as '-> {} @[1]' so every caller must consume it, or consume the value inside this function",
                    sig.name,
                    checker.types.name(sig.result)
                ),
            ));
        }
        let locals = checker.locals;
        functions.bodies[index] = Some(Function {
            name: sig.name.clone(),
            parameters: sig.parameters.len(),
            closure: None,
            locals,
            result: sig.result,
            body,
            span: sig.span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: sig.parameter_grades.clone(),
            result_grade: sig.result_grade,
            parameter_lifetimes: sig.parameter_lifetimes.clone(),
            result_lifetime: sig.result_lifetime.clone(),
            lifetime_bounds: sig.lifetime_bounds.clone(),
        });
    }
    // Re-check every proof certificate without the search that produced it.
    if let Some(bad) = functions
        .certificates
        .iter()
        .find(|c| !crate::facts::verify(c))
    {
        return Err(Diagnostic::new(
            bad.span,
            format!(
                "internal error: proof certificate for '{}' failed independent checking",
                bad.obligation
            ),
        ));
    }
    // Fusion selection runs only after every body exists, so it can inspect
    // callee effect rows and structural termination instead of guessing from
    // source types while bodies are still being checked.
    let automatic = automatic_fusion(&types, &mut functions);
    functions.fusions += automatic;
    let mut executable = Executable {
        _grade_algebras: resolution.lowered_algebras.values().cloned().collect(),
        fusions: functions.fusions,
        uses_tasks: functions.uses_tasks,
        certificates: functions.certificates,
        functions: functions.bodies.into_iter().map(Option::unwrap).collect(),
        entry,
        enums: types.enums,
        pointees: types.pointees,
        unions: types.unions,
        function_types: types.function_types,
        reference_labels: types.reference_labels,
        owned_enums: vec![],
        linear_enums: vec![],
        logical_definitions: logical.definitions.clone(),
    };
    crate::ownership::check(&mut executable)?;
    crate::grades::check(&executable)?;
    Ok(executable)
}
/// A span-insensitive key for the simple expression forms admitted in erased
/// predicate parameters. Unsupported compound forms fall back to their debug
/// form: that can only reject a contract, never accept two different ones.
fn expr_key(expr: &ast::Expr) -> String {
    use ast::ExprKind as E;
    match &expr.kind {
        E::Name(name) => name.clone(),
        E::Integer(value) | E::Float(value) => value.clone(),
        E::String(value) => format!("{value:?}"),
        E::Char(value) => format!("'{value}'"),
        E::Bool(value) => value.to_string(),
        E::Handle { .. } | E::Perform { .. } => format!("{:?}", expr.kind),
        E::Tuple(items) => format!(
            "({})",
            items.iter().map(expr_key).collect::<Vec<_>>().join(",")
        ),
        E::Array(items) => format!(
            "[{}]",
            items.iter().map(expr_key).collect::<Vec<_>>().join(",")
        ),
        E::Unary {
            op,
            mutable,
            operand,
        } => format!(
            "{op:?}{}{}",
            if *mutable { " mut" } else { "" },
            expr_key(operand)
        ),
        E::Binary { op, left, right } => {
            format!("({op:?} {} {})", expr_key(left), expr_key(right))
        }
        E::Call { callee, arguments } => format!(
            "{}({})",
            expr_key(callee),
            arguments.iter().map(expr_key).collect::<Vec<_>>().join(",")
        ),
        E::Specialize { callee, arguments } => format!(
            "{}::<{}>",
            expr_key(callee),
            arguments.iter().map(type_key).collect::<Vec<_>>().join(",")
        ),
        E::Field { value, name } => format!("{}.{name}", expr_key(value)),
        E::Index { value, index } => format!("{}[{}]", expr_key(value), expr_key(index)),
        E::Slice { value, start, end } => format!(
            "{}[{}..{}]",
            expr_key(value),
            start.as_deref().map(expr_key).unwrap_or_default(),
            end.as_deref().map(expr_key).unwrap_or_default()
        ),
        E::Try(value) => format!("{}?", expr_key(value)),
        E::Return(Some(value)) => format!("return {}", expr_key(value)),
        E::Return(None) => "return".to_owned(),
        E::Break(Some(value)) => format!("break {}", expr_key(value)),
        E::Break(None) => "break".to_owned(),
        E::Continue => "continue".to_owned(),
        E::Block(_)
        | E::Lambda(_)
        | E::If { .. }
        | E::Match { .. }
        | E::Record { .. }
        | E::StructuralLiteral(_)
        | E::While { .. }
        | E::Loop(_) => format!("{expr:?}"),
    }
}
/// Split a checked projection chain into its root reference expression and the
/// combined word offset from the record tag. Used only for field assignments
/// through `&mut Record`; reads use the ordinary `Project` expression.
fn split_reference_projection(expr: Expr) -> Option<(Expr, usize)> {
    let ExprKind::Project(base, offset) = expr.kind else {
        return None;
    };
    let base = *base;
    if base.ty.is_ref() {
        return Some((base, offset));
    }
    let (root, inner) = split_reference_projection(base)?;
    Some((root, inner + offset))
}
/// A span-insensitive canonical spelling of a declared type. Used only to
/// compare trait method contracts with their impls; it deliberately treats
/// `Self` as one stable placeholder because both sides must spell it the same
/// way.
fn type_key(ty: &ast::Type) -> String {
    match &ty.kind {
        ast::TypeKind::Named { path, arguments } => {
            let mut text = path.join(".");
            if !arguments.is_empty() {
                text.push('<');
                text.push_str(&arguments.iter().map(type_key).collect::<Vec<_>>().join(","));
                text.push('>');
            }
            text
        }
        ast::TypeKind::Dyn(inner) => format!("dyn {}", type_key(inner)),
        ast::TypeKind::Structural(fields) => {
            let mut fields = fields
                .iter()
                .map(|field| (field.name.clone(), field.ty.clone()))
                .collect::<Vec<_>>();
            fields.sort_by(|left, right| left.0.cmp(&right.0));
            format!(
                "struct{{{}}}",
                fields
                    .iter()
                    .map(|(name, ty)| format!("{name}:{}", type_key(ty)))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        }
        ast::TypeKind::Integer(value) => value.clone(),
        ast::TypeKind::Bool(value) => format!("bool:{value}"),
        ast::TypeKind::Tuple(items) => {
            format!(
                "({})",
                items.iter().map(type_key).collect::<Vec<_>>().join(",")
            )
        }
        ast::TypeKind::Slice(inner) => format!("[{}]", type_key(inner)),
        ast::TypeKind::Array(inner, length) => {
            format!("[{};{}]", type_key(inner), type_key(length))
        }
        ast::TypeKind::Borrow {
            lifetime,
            mutable,
            inner,
        } => format!(
            "&{}{}{}",
            lifetime
                .as_ref()
                .map(|lifetime| format!("'{lifetime} "))
                .unwrap_or_default(),
            if *mutable { "mut " } else { "" },
            type_key(inner)
        ),
        ast::TypeKind::Lifetime(name) => format!("'{name}"),
        ast::TypeKind::SelfType => "Self".to_owned(),
        ast::TypeKind::Function {
            lifetimes,
            parameters,
            result,
            effects,
            call_once,
            call_linear,
        } => {
            let lifetimes = lifetimes
                .iter()
                .map(|lifetime| {
                    let mut text = lifetime.name.clone();
                    for bound in &lifetime.bounds {
                        text.push_str(&format!(":{}", bound.name));
                    }
                    text
                })
                .collect::<Vec<_>>()
                .join(",");
            let mut effects = effects.iter().map(type_key).collect::<Vec<_>>();
            effects.sort();
            effects.dedup();
            let effects = effects.join(",");
            format!(
                "{}fn<{lifetimes}>({})->{} ! {{ {effects} }}",
                if *call_linear {
                    "linear "
                } else if *call_once {
                    "once "
                } else {
                    ""
                },
                parameters
                    .iter()
                    .map(|parameter| type_key(&parameter.ty))
                    .collect::<Vec<_>>()
                    .join(","),
                type_key(result),
            )
        }
        ast::TypeKind::Binary { op, left, right } => {
            format!("{} {op:?} {}", type_key(left), type_key(right))
        }
        ast::TypeKind::Graded { inner, grade } => {
            format!("{} @[{}]", type_key(inner), type_key(grade))
        }
        ast::TypeKind::Predicate(expr) => format!("<predicate {}>", expr_key(expr)),
    }
}
/// Capture-avoiding alpha-normalization of one method signature for exact
/// trait/impl contract comparison.
///
/// Method generic parameters are renamed to unspellable canonical tokens first,
/// then `Self` and the trait's generic parameters are substituted. Trait
/// arguments are closed types (generic impls are rejected), so the substituted
/// text cannot be captured by a method binder. Parameter names stay part of
/// the contract because erased propositions may name earlier parameters.
struct ContractNames {
    types: BTreeMap<String, String>,
    lifetimes: BTreeMap<String, String>,
    self_ty: Option<ast::Type>,
    /// Trait parameter name -> concrete impl argument, applied after alpha
    /// renaming so a global type name cannot capture a method binder.
    trait_arguments: BTreeMap<String, ast::Type>,
    /// Associated type name -> impl-supplied value. Both the trait signature
    /// and the impl signature normalize `Self::Name` through this map, so the
    /// exact comparison sees the same type on both sides.
    associated_types: BTreeMap<String, ast::Type>,
}
impl ContractNames {
    fn new(
        resolution: &Resolution,
        function: &ast::Function,
        self_ty: Option<&ast::Type>,
        trait_arguments: Option<&BTreeMap<String, ast::Type>>,
        associated_types: Option<&BTreeMap<String, ast::Type>>,
    ) -> Self {
        let mut types = BTreeMap::new();
        for (index, generic) in function.generics.iter().enumerate() {
            let prefix = match generic_category(resolution, generic) {
                GenericCategory::Type => "T",
                GenericCategory::Const => "N",
                GenericCategory::Grade => "G",
                GenericCategory::Effect => "E",
            };
            types.insert(generic.name.clone(), format!("${prefix}{index}"));
        }
        let lifetimes = function
            .lifetimes
            .iter()
            .enumerate()
            .map(|(index, lifetime)| (lifetime.name.clone(), format!("$L{index}")))
            .collect();
        Self {
            types,
            lifetimes,
            self_ty: self_ty.cloned(),
            trait_arguments: trait_arguments.cloned().unwrap_or_default(),
            associated_types: associated_types.cloned().unwrap_or_default(),
        }
    }
    fn name(&self, name: &str) -> Option<ast::Type> {
        if let Some(token) = self.types.get(name) {
            return Some(ast::Type::new(
                ast::TypeKind::Named {
                    path: vec![token.clone()],
                    arguments: Vec::new(),
                },
                Span::default(),
            ));
        }
        self.trait_arguments.get(name).cloned()
    }
    fn ty(&self, ty: &ast::Type) -> ast::Type {
        let kind = match &ty.kind {
            ast::TypeKind::Named { path, arguments } => {
                if arguments.is_empty()
                    && path.len() == 1
                    && let Some(replacement) = self.name(&path[0])
                {
                    return replacement;
                }
                if arguments.is_empty()
                    && path.len() == 2
                    && path[0] == "Self"
                    && let Some(value) = self.associated_types.get(&path[1])
                {
                    return self.ty(value);
                }
                ast::TypeKind::Named {
                    path: path.clone(),
                    arguments: arguments.iter().map(|argument| self.ty(argument)).collect(),
                }
            }
            ast::TypeKind::SelfType => {
                if let Some(self_ty) = &self.self_ty {
                    return self_ty.clone();
                }
                ast::TypeKind::SelfType
            }
            ast::TypeKind::Dyn(inner) => ast::TypeKind::Dyn(Box::new(self.ty(inner))),
            ast::TypeKind::Lifetime(name) => ast::TypeKind::Lifetime(self.lifetime(name)),
            ast::TypeKind::Borrow {
                lifetime,
                mutable,
                inner,
            } => ast::TypeKind::Borrow {
                lifetime: lifetime.as_deref().map(|name| self.lifetime(name)),
                mutable: *mutable,
                inner: Box::new(self.ty(inner)),
            },
            ast::TypeKind::Tuple(items) => {
                ast::TypeKind::Tuple(items.iter().map(|item| self.ty(item)).collect())
            }
            ast::TypeKind::Structural(fields) => ast::TypeKind::Structural(
                fields
                    .iter()
                    .map(|field| ast::Field {
                        name: field.name.clone(),
                        ty: self.ty(&field.ty),
                        span: field.span,
                    })
                    .collect(),
            ),
            ast::TypeKind::Slice(inner) => ast::TypeKind::Slice(Box::new(self.ty(inner))),
            ast::TypeKind::Array(inner, length) => {
                ast::TypeKind::Array(Box::new(self.ty(inner)), Box::new(self.ty(length)))
            }
            ast::TypeKind::Binary { op, left, right } => ast::TypeKind::Binary {
                op: op.clone(),
                left: Box::new(self.ty(left)),
                right: Box::new(self.ty(right)),
            },
            ast::TypeKind::Graded { inner, grade } => ast::TypeKind::Graded {
                inner: Box::new(self.ty(inner)),
                grade: Box::new(self.ty(grade)),
            },
            ast::TypeKind::Function {
                lifetimes,
                parameters,
                result,
                effects,
                call_once,
                call_linear,
            } => ast::TypeKind::Function {
                lifetimes: lifetimes
                    .iter()
                    .map(|lifetime| ast::Lifetime {
                        name: self.lifetime(&lifetime.name),
                        span: lifetime.span,
                        bounds: lifetime
                            .bounds
                            .iter()
                            .map(|bound| ast::LifetimeBound {
                                name: self.lifetime(&bound.name),
                                span: bound.span,
                            })
                            .collect(),
                    })
                    .collect(),
                parameters: parameters
                    .iter()
                    .map(|parameter| ast::TypeParameter {
                        name: parameter.name.clone(),
                        ty: self.ty(&parameter.ty),
                        span: parameter.span,
                    })
                    .collect(),
                result: Box::new(self.ty(result)),
                effects: effects.iter().map(|effect| self.ty(effect)).collect(),
                call_once: *call_once,
                call_linear: *call_linear,
            },
            ast::TypeKind::Integer(value) => ast::TypeKind::Integer(value.clone()),
            ast::TypeKind::Bool(value) => ast::TypeKind::Bool(*value),
            ast::TypeKind::Predicate(expression) => ast::TypeKind::Predicate(expression.clone()),
        };
        ast::Type::new(kind, ty.span)
    }
    fn lifetime(&self, name: &str) -> String {
        self.lifetimes
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    }
}
/// The conservative exact method contract after alpha-renaming method
/// parameters and substituting `Self` and trait arguments: generic categories
/// and bounds, effect-exclusion sets, lifetimes, parameter names/types, erasure
/// markers, result type, and the effect row (order-insensitive).
fn method_contract_key(
    resolution: &Resolution,
    function: &ast::Function,
    self_ty: Option<&ast::Type>,
    trait_arguments: Option<&BTreeMap<String, ast::Type>>,
    associated_types: Option<&BTreeMap<String, ast::Type>>,
) -> Result<String> {
    let names = ContractNames::new(
        resolution,
        function,
        self_ty,
        trait_arguments,
        associated_types,
    );
    let mut lifetimes = String::new();
    for lifetime in &function.lifetimes {
        lifetimes.push_str(&names.lifetime(&lifetime.name));
        for bound in &lifetime.bounds {
            lifetimes.push_str(&format!(":{}", names.lifetime(&bound.name)));
        }
        lifetimes.push(',');
    }
    let mut generics = String::new();
    for generic in &function.generics {
        let category = generic_category(resolution, generic);
        generics.push_str(&format!("${category:?}"));
        if let Some(bound) = &generic.bound {
            generics.push_str(&format!(": {}", type_key(&names.ty(bound))));
        }
        // Compare the canonical concrete set, so a trait and impl that spell
        // the same union in a different order remain alpha-equivalent while a
        // stricter or looser implementation still differs.
        if let Some(included) = crate::runtime_types::effect_includes(resolution, generic)? {
            generics.push_str(&format!(" + {included:#b}"));
        }
        if let Some(excluded) = crate::runtime_types::effect_excludes(resolution, generic)? {
            generics.push_str(&format!(" - {excluded:#b}"));
        }
        generics.push(',');
    }
    let parameters = function
        .parameters
        .iter()
        .map(|parameter| {
            format!(
                "{}{}: {}",
                if parameter.erased { "erased " } else { "" },
                parameter.name,
                type_key(&names.ty(&parameter.ty))
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let mut effects = function
        .effects
        .iter()
        .map(|effect| type_key(&names.ty(effect)))
        .collect::<Vec<_>>();
    effects.sort();
    effects.dedup();
    Ok(format!(
        "generics=<{generics}> <{lifetimes}>({parameters}) -> {} ! {{{}}}",
        type_key(&names.ty(&function.result)),
        effects.join(", ")
    ))
}
/// Evaluate concrete trait-specialization arguments in a declaration order that
/// mirrors function instance keys. Trait arguments are static identity, never
/// runtime values.
#[allow(clippy::too_many_arguments)]
fn evaluate_trait_arguments(
    types: &mut Types<'_>,
    resolution: &Resolution,
    logical: &crate::check::LogicalEnvironment,
    generics: &[ast::Generic],
    arguments: &[ast::Type],
    substitution: &crate::runtime_types::Subst,
    trait_name: &str,
    span: Span,
) -> Result<TraitArguments> {
    if generics.len() != arguments.len() {
        return Err(Diagnostic::new(
            span,
            format!(
                "trait '{trait_name}' expects {} argument(s), found {}",
                generics.len(),
                arguments.len()
            ),
        ));
    }
    let mut out = TraitArguments::default();
    for (generic, argument) in generics.iter().zip(arguments) {
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                let ty = types.ty_in(argument, substitution)?;
                let ty = types.full(ty, argument.span)?;
                if crate::runtime_types::has_borrow(types, ty) {
                    return Err(Diagnostic::new(
                        argument.span,
                        format!(
                            "trait argument for '{}' cannot be a borrowed type; references are call-scoped and cannot be erased through a generic trait parameter",
                            generic.name
                        ),
                    ));
                }
                out.types.push(ty);
            }
            GenericCategory::Const => out.consts.push(crate::length::eval_type(
                resolution,
                logical,
                &substitution.consts,
                argument,
            )?),
            GenericCategory::Grade => out.grades.push(crate::grades::evaluate(
                resolution,
                &substitution.grades,
                argument,
            )?),
            GenericCategory::Effect => out.effects.push(crate::runtime_types::effect_bits_with(
                resolution,
                std::slice::from_ref(argument),
                &substitution.effects,
            )?),
        }
    }
    Ok(out)
}
/// Seed one specialization substitution with a trait's concrete arguments for a
/// materialized default method. Trait parameters are classified exactly like
/// function generics, and their declaration order matches the argument vectors
/// produced by [`evaluate_trait_arguments`].
fn insert_trait_arguments(
    resolution: &Resolution,
    generics: &[ast::Generic],
    arguments: &TraitArguments,
    substitution: &mut crate::runtime_types::Subst,
    consts: &mut BTreeMap<BindingId, usize>,
    grades: &mut BTreeMap<BindingId, Grade>,
    effects: &mut BTreeMap<BindingId, u8>,
) {
    let mut types = arguments.types.iter();
    let mut const_values = arguments.consts.iter();
    let mut grade_values = arguments.grades.iter();
    let mut effect_values = arguments.effects.iter();
    for generic in generics {
        let Some(binder) = resolution.binder(generic.span) else {
            continue;
        };
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                if let Some(ty) = types.next() {
                    substitution.types.insert(binder, *ty);
                }
            }
            GenericCategory::Const => {
                if let Some(value) = const_values.next() {
                    consts.insert(binder, *value);
                }
            }
            GenericCategory::Grade => {
                if let Some(grade) = grade_values.next() {
                    grades.insert(binder, *grade);
                }
            }
            GenericCategory::Effect => {
                if let Some(bits) = effect_values.next() {
                    effects.insert(binder, *bits);
                }
            }
        }
    }
}
/// Render one trait specialization for diagnostics, in declared parameter order.
fn trait_specialization_name(
    resolution: &Resolution,
    types: &Types<'_>,
    generics: &[ast::Generic],
    arguments: &TraitArguments,
) -> String {
    let mut type_index = 0;
    let mut const_index = 0;
    let mut grade_index = 0;
    let mut effect_index = 0;
    let mut parts = Vec::new();
    for generic in generics {
        let part = match generic_category(resolution, generic) {
            GenericCategory::Type => {
                let ty = arguments.types[type_index];
                type_index += 1;
                types.name(ty)
            }
            GenericCategory::Const => {
                let value = arguments.consts[const_index];
                const_index += 1;
                value.to_string()
            }
            GenericCategory::Grade => {
                let grade = arguments.grades[grade_index];
                grade_index += 1;
                grade.to_string()
            }
            GenericCategory::Effect => {
                let row = arguments.effects[effect_index];
                effect_index += 1;
                let names = [(1u8, "io"), (2, "alloc"), (4, "panic"), (8, "suspend")]
                    .into_iter()
                    .filter_map(|(bit, name)| (row & bit != 0).then_some(name))
                    .collect::<Vec<_>>();
                if names.is_empty() {
                    "{}".to_owned()
                } else {
                    format!("{{{}}}", names.join(", "))
                }
            }
        };
        parts.push(part);
    }
    parts.join(", ")
}
/// A trait receiver is owned `Self` or a single shared/exclusive borrow of
/// `Self`. Lifetimes on the borrow are erased contract metadata and remain
/// part of the exact signature comparison.
fn valid_trait_receiver(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::SelfType => true,
        ast::TypeKind::Borrow { inner, .. } => matches!(inner.kind, ast::TypeKind::SelfType),
        _ => false,
    }
}
/// Check one method receiver against the concrete impl target and return the
/// runtime receiver type. Owned receivers are the target by value; borrowed
/// receivers are `&Target`/`&mut Target` and are limited to nominal records,
/// with no exclusive borrow of a record that already has borrowed fields.
fn checked_method_receiver(
    types: &mut Types<'_>,
    receiver_ty: &ast::Type,
    self_key: Type,
) -> Result<Type> {
    let subst = crate::runtime_types::Subst {
        self_type: Some(self_key),
        ..Default::default()
    };
    let expected_receiver = match &receiver_ty.kind {
        ast::TypeKind::Borrow { mutable, .. } => {
            if self_key.layout().is_none() || !types.enums[self_key.layout().unwrap()].record {
                return Err(Diagnostic::new(
                    receiver_ty.span,
                    "borrowed receivers are supported only for nominal record targets in this subset",
                ));
            }
            let inner = match &receiver_ty.kind {
                ast::TypeKind::Borrow { inner, .. } => inner,
                _ => unreachable!(),
            };
            if types.ty_in(inner, &subst)? != self_key {
                return Err(Diagnostic::new(
                    receiver_ty.span,
                    "a borrowed method receiver must borrow the impl target type, as in 'self: &Self' or 'self: &mut Self'",
                ));
            }
            if *mutable && types.enums[self_key.layout().unwrap()].borrowed {
                return Err(Diagnostic::new(
                    receiver_ty.span,
                    "an exclusive '&mut self' receiver is not supported for a record with borrowed fields; borrow it shared, or update through an owning value",
                ));
            }
            if *mutable {
                Type::RefMut(types.pointer(self_key))
            } else {
                Type::Ref(types.pointer(self_key))
            }
        }
        _ => self_key,
    };
    let receiver_type = types.ty_in(receiver_ty, &subst)?;
    if receiver_type != expected_receiver {
        return Err(Diagnostic::new(
            receiver_ty.span,
            "a method receiver must borrow the impl target type exactly, as in '&Self' or '&mut Self', or be the target type by value",
        ));
    }
    Ok(expected_receiver)
}
/// Collect every `Self::Name` projection mentioned by a type. Used to validate
/// associated type defaults and reject cyclic default chains before lowering.
fn type_self_associations(ty: &ast::Type, out: &mut BTreeSet<String>) {
    match &ty.kind {
        ast::TypeKind::Named { path, arguments } => {
            if path.len() == 2 && path[0] == "Self" {
                out.insert(path[1].clone());
            }
            for argument in arguments {
                type_self_associations(argument, out);
            }
        }
        ast::TypeKind::Tuple(items) => {
            for item in items {
                type_self_associations(item, out);
            }
        }
        ast::TypeKind::Structural(fields) => {
            for field in fields {
                type_self_associations(&field.ty, out);
            }
        }
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Borrow { inner, .. }
        | ast::TypeKind::Dyn(inner) => type_self_associations(inner, out),
        ast::TypeKind::Array(inner, length) => {
            type_self_associations(inner, out);
            type_self_associations(length, out);
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_self_associations(left, out);
            type_self_associations(right, out);
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            for parameter in parameters {
                type_self_associations(&parameter.ty, out);
            }
            type_self_associations(result, out);
            for effect in effects {
                type_self_associations(effect, out);
            }
        }
        ast::TypeKind::Integer(_)
        | ast::TypeKind::Bool(_)
        | ast::TypeKind::Lifetime(_)
        | ast::TypeKind::SelfType
        | ast::TypeKind::Predicate(_) => {}
    }
}

/// Validate an associated type default graph: every `Self::Name` must name a
/// declared associated type, and no default may depend on itself directly or
/// transitively. A cycle has no finite lowered representation, so it is
/// rejected at the trait declaration instead of surfacing as a depth error at
/// an arbitrary use site.
fn validate_associated_type_defaults(associated: &[ast::Associated]) -> Result<()> {
    let declared = associated
        .iter()
        .filter_map(|item| match item {
            ast::Associated::Type { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut defaults: BTreeMap<String, (ast::Type, Span)> = BTreeMap::new();
    for item in associated {
        let ast::Associated::Type {
            name,
            value: Some(default),
            span,
        } = item
        else {
            continue;
        };
        let mut references = BTreeSet::new();
        type_self_associations(default, &mut references);
        for reference in &references {
            if !declared.contains(reference) {
                return Err(Diagnostic::new(
                    default.span,
                    format!(
                        "associated type default references 'Self::{reference}', which is not a declared associated type"
                    ),
                ));
            }
        }
        defaults.insert(name.clone(), (default.clone(), *span));
    }
    // Depth-first search with an explicit color map: 1 = on the current path,
    // 2 = finished. A back edge names the cycle.
    let mut color: BTreeMap<String, u8> = BTreeMap::new();
    fn visit(
        name: &str,
        defaults: &BTreeMap<String, (ast::Type, Span)>,
        color: &mut BTreeMap<String, u8>,
        path: &mut Vec<String>,
    ) -> Result<()> {
        match color.get(name).copied().unwrap_or(0) {
            2 => return Ok(()),
            1 => {
                let start = path.iter().position(|item| item == name).unwrap_or(0);
                let mut cycle = path[start..].to_vec();
                cycle.push(name.to_owned());
                let (_, span) = defaults.get(name).expect("cycle node has a default");
                return Err(Diagnostic::new(
                    *span,
                    format!(
                        "associated type default cycle: {}; each default must resolve to a finite type",
                        cycle.join(" -> ")
                    ),
                ));
            }
            _ => {}
        }
        let Some((default, _)) = defaults.get(name) else {
            return Ok(());
        };
        color.insert(name.to_owned(), 1);
        path.push(name.to_owned());
        let mut references = BTreeSet::new();
        type_self_associations(default, &mut references);
        for reference in references {
            visit(&reference, defaults, color, path)?;
        }
        path.pop();
        color.insert(name.to_owned(), 2);
        Ok(())
    }
    for name in defaults.keys() {
        visit(name, &defaults, &mut color, &mut Vec::new())?;
    }
    Ok(())
}
fn type_mentions_self(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::SelfType => true,
        ast::TypeKind::Named { path, arguments } => {
            path.first().is_some_and(|name| name == "Self")
                || arguments.iter().any(type_mentions_self)
        }
        ast::TypeKind::Tuple(arguments) => arguments.iter().any(type_mentions_self),
        ast::TypeKind::Structural(fields) => {
            fields.iter().any(|field| type_mentions_self(&field.ty))
        }
        ast::TypeKind::Dyn(inner) => type_mentions_self(inner),
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            type_mentions_self(inner)
        }
        ast::TypeKind::Borrow { inner, .. } => type_mentions_self(inner),
        ast::TypeKind::Array(inner, length) => {
            type_mentions_self(inner) || type_mentions_self(length)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_mentions_self(left) || type_mentions_self(right)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_self(&parameter.ty))
                || type_mentions_self(result)
                || effects.iter().any(type_mentions_self)
        }
        ast::TypeKind::Lifetime(_)
        | ast::TypeKind::Integer(_)
        | ast::TypeKind::Bool(_)
        | ast::TypeKind::Predicate(_) => false,
    }
}

/// Like [`type_mentions_self`], but `Self.Assoc` for an associated type that is
/// agreed by every object impl is a concrete ABI type and is allowed.
fn type_mentions_self_outside_assoc(ty: &ast::Type, allowed: &BTreeSet<String>) -> bool {
    match &ty.kind {
        ast::TypeKind::SelfType => true,
        ast::TypeKind::Named { path, arguments } => {
            if path.len() == 2
                && path[0] == "Self"
                && arguments.is_empty()
                && allowed.contains(&path[1])
            {
                return false;
            }
            path.first().is_some_and(|name| name == "Self")
                || arguments
                    .iter()
                    .any(|argument| type_mentions_self_outside_assoc(argument, allowed))
        }
        ast::TypeKind::Tuple(arguments) => arguments
            .iter()
            .any(|argument| type_mentions_self_outside_assoc(argument, allowed)),
        ast::TypeKind::Dyn(inner) => type_mentions_self_outside_assoc(inner, allowed),
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            type_mentions_self_outside_assoc(inner, allowed)
        }
        ast::TypeKind::Borrow { inner, .. } => type_mentions_self_outside_assoc(inner, allowed),
        ast::TypeKind::Array(inner, length) => {
            type_mentions_self_outside_assoc(inner, allowed)
                || type_mentions_self_outside_assoc(length, allowed)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_mentions_self_outside_assoc(left, allowed)
                || type_mentions_self_outside_assoc(right, allowed)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_self_outside_assoc(&parameter.ty, allowed))
                || type_mentions_self_outside_assoc(result, allowed)
                || effects
                    .iter()
                    .any(|effect| type_mentions_self_outside_assoc(effect, allowed))
        }
        _ => false,
    }
}

/// Allocate one synthetic function binding for every trait default that an impl
/// inherits, keyed by the impl declaration's start offset and the method name.
/// This is a syntactic pre-pass: it does not type-check, and it must run before
/// type lowering borrows the resolver table. Impls that are later rejected may
/// leave unused bindings behind; they never enter the checked program.
fn collect_default_bindings(
    module: &ast::Module,
    resolution: &mut Resolution,
) -> Result<BTreeMap<(usize, String), BindingId>> {
    let mut traits = BTreeMap::new();
    for declaration in &module.items {
        if let ast::ItemKind::Trait { methods, .. } = &declaration.item.kind {
            let id = resolution.declarations[&declaration.item.span.start];
            traits.insert(
                id,
                methods
                    .iter()
                    .map(|method| {
                        (
                            method.function.name.clone(),
                            method.function.body.is_some(),
                            method.span,
                        )
                    })
                    .collect::<Vec<_>>(),
            );
        }
    }
    let mut bindings = BTreeMap::new();
    for declaration in &module.items {
        let ast::ItemKind::Impl {
            trait_path: Some(trait_path),
            methods,
            ..
        } = &declaration.item.kind
        else {
            continue;
        };
        let Some(trait_id) = resolution.reference(trait_path.span) else {
            continue;
        };
        let Some(declared) = traits.get(&trait_id) else {
            continue;
        };
        // The body is checked in the module that declares the trait: that is
        // where its free names were resolved, so a private helper of the trait's
        // module stays callable even when the impl lives in another module.
        let unit = resolution.unit_of.get(&trait_id).copied().unwrap_or(0);
        let public = resolution.public.contains(&trait_id);
        let implemented = methods
            .iter()
            .map(|method| method.function.name.as_str())
            .collect::<BTreeSet<_>>();
        for (name, has_body, span) in declared {
            if !*has_body || implemented.contains(name.as_str()) {
                continue;
            }
            let binding = resolution.synthesize_method(name, *span, unit, public);
            bindings.insert((declaration.item.span.start, name.clone()), binding);
        }
    }
    Ok(bindings)
}
/// Collect declared traits and concrete impls, validate their contracts, and
/// register every impl method as an ordinary checked function. Static dispatch
/// lowers a method call to `Target::Function`, so there are no vtables, trait
/// values, or runtime dispatch tables.
fn collect_methods<'a>(
    module: &'a ast::Module,
    resolution: &Resolution,
    default_bindings: &BTreeMap<(usize, String), BindingId>,
    types: &mut Types<'a>,
    logical: &crate::check::LogicalEnvironment,
    functions: &mut Functions<'a>,
) -> Result<Vec<BindingId>> {
    let mut bindings = Vec::new();
    let mut trait_methods_to_check = Vec::new();
    for declaration in &module.items {
        let ast::ItemKind::Trait {
            name,
            generics,
            associated,
            methods,
        } = &declaration.item.kind
        else {
            continue;
        };
        let id = resolution.declarations[&declaration.item.span.start];
        validate_associated_type_defaults(associated)?;
        let mut associated_items = BTreeMap::new();
        for item in associated {
            match item {
                ast::Associated::Type { name, value, .. } => {
                    if let Some(default) = value {
                        let associated_names = associated
                            .iter()
                            .filter_map(|item| {
                                matches!(item, ast::Associated::Type { .. })
                                    .then_some(item.name().to_owned())
                            })
                            .collect();
                        if type_mentions_self_outside_assoc(default, &associated_names) {
                            return Err(Diagnostic::new(
                                default.span,
                                "an associated type default may not mention bare 'Self'; write a concrete type, a trait parameter, or a projection 'Self::Other'",
                            ));
                        }
                        // Validate the default's own syntax now. Trait
                        // parameters are still symbolic here, so only
                        // structurally invalid defaults are rejected at the
                        // declaration; per-impl lowering validates concrete
                        // substitutions.
                        let consts = generics
                            .iter()
                            .filter(|generic| {
                                crate::runtime_types::is_const_generic(resolution, generic)
                            })
                            .filter_map(|generic| resolution.binder(generic.span))
                            .collect::<BTreeSet<_>>();
                        validate_type_template(resolution, default, &consts, false, true)?;
                    }
                    associated_items.insert(
                        name.clone(),
                        TraitAssociated::Type {
                            default: value.clone(),
                        },
                    );
                }
                ast::Associated::Const {
                    name, ty, value, ..
                } => {
                    if type_mentions_self(ty) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "an associated constant's type may not mention 'Self'; write a concrete scalar type",
                        ));
                    }
                    let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                    if !const_scalar_type(types, lowered) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "associated constants must have a compile-time scalar, tuple, or inline-array type; scalar types are i8/i16/i32/i64/u8/u16/u32/u64, Bool, or Char",
                        ));
                    }
                    associated_items.insert(
                        name.clone(),
                        TraitAssociated::Const {
                            ty: ty.clone(),
                            default: value.clone(),
                        },
                    );
                }
            }
        }
        for generic in generics {
            if let Some(bound) = &generic.bound {
                match resolution
                    .reference(bound.span)
                    .map(|id| &resolution.bindings[id])
                {
                    Some(binding)
                        if binding.kind == BindingKind::Builtin
                            && matches!(
                                binding.name.as_str(),
                                "Type" | "Nat" | "Grade" | "Effects"
                            ) => {}
                    Some(binding) if binding.kind == BindingKind::Trait => {
                        return Err(Diagnostic::new(
                            generic.span,
                            "trait parameters with trait bounds are not supported in this subset; put the bound on the function type parameter that uses this trait, as in 'fn f<T: Trait<...>>(value: T)'",
                        ));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            generic.span,
                            "trait parameter bounds must name Type, Nat, Grade, or Effects",
                        ));
                    }
                }
            }
            if generic_category(resolution, generic) == GenericCategory::Effect {
                return Err(Diagnostic::new(
                    generic.span,
                    "effect-row parameters are not supported on traits; declare the effect parameter on the generic function or method that needs it",
                ));
            }
        }
        let mut signatures = BTreeMap::new();
        for method in methods {
            let f = &method.function;
            if f.total {
                return Err(Diagnostic::new(
                    method.span,
                    "trait methods are executable declarations and cannot be 'total'",
                ));
            }
            if let Some(method_generic) = f
                .generics
                .iter()
                .find(|method_generic| generics.iter().any(|g| g.name == method_generic.name))
            {
                return Err(Diagnostic::new(
                    method_generic.span,
                    format!(
                        "method parameter '{}' must be distinct from the trait's parameters to avoid capture; rename one of them",
                        method_generic.name
                    ),
                ));
            }
            if Checker::builtin_method(&f.name) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "trait method '{}' uses a reserved builtin method name; builtin receiver methods take precedence, so choose another name",
                        f.name
                    ),
                ));
            }
            let Some(receiver) = f.parameters.first() else {
                return Err(Diagnostic::new(
                    method.span,
                    "a trait method must declare an owned receiver as its first parameter: 'self: Self'",
                ));
            };
            if receiver.erased || receiver.name != "self" {
                return Err(Diagnostic::new(
                    receiver.span,
                    "the first method parameter must be the receiver, written 'self: Self'",
                ));
            }
            if !valid_trait_receiver(&receiver.ty) {
                return Err(Diagnostic::new(
                    receiver.ty.span,
                    "a trait method receiver must be written 'self: Self', 'self: &Self', 'self: &mut Self', '&self', or '&mut self'",
                ));
            }
            for parameter in &f.parameters {
                if parameter.erased && type_mentions_self(&parameter.ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "erased method parameters may not mention 'Self' in this subset",
                    ));
                }
            }
            validate_erased_parameters(resolution, logical, f)?;
            validate_length_templates(resolution, f)?;
            if signatures
                .insert(
                    f.name.clone(),
                    TraitMethod {
                        span: method.span,
                        function: f,
                    },
                )
                .is_some()
            {
                return Err(Diagnostic::new(
                    method.span,
                    format!("duplicate method '{}' in trait '{name}'", f.name),
                ));
            }
            trait_methods_to_check.push(f);
        }
        functions.traits.insert(
            id,
            TraitDefinition {
                generics: generics.clone(),
                associated: associated_items,
                associated_order: associated
                    .iter()
                    .map(|item| item.name().to_owned())
                    .collect(),
                methods: signatures,
            },
        );
    }
    for declaration in &module.items {
        let ast::ItemKind::Impl {
            generics: impl_generics,
            trait_path,
            self_ty,
            associated,
            methods,
        } = &declaration.item.kind
        else {
            continue;
        };
        let span = declaration.item.span;
        let trait_id = match trait_path {
            Some(trait_path) => {
                let id = resolution.reference(trait_path.span).ok_or_else(|| {
                    Diagnostic::new(trait_path.span, "trait path did not resolve")
                })?;
                if resolution.bindings[id].kind != BindingKind::Trait {
                    return Err(Diagnostic::new(
                        trait_path.span,
                        format!(
                            "'{}' is not a declared trait; an impl must name 'impl Trait for Type' or provide an inherent 'impl Type'",
                            resolution.bindings[id].name
                        ),
                    ));
                }
                Some(id)
            }
            None => None,
        };
        if !impl_generics.is_empty() {
            bindings.extend(collect_generic_impl(
                span,
                impl_generics,
                trait_path.as_ref(),
                trait_id,
                self_ty,
                associated,
                methods,
                default_bindings,
                resolution,
                types,
                logical,
                functions,
            )?);
            continue;
        }
        let self_key = types.ty_in(self_ty, &crate::runtime_types::Subst::default())?;
        if matches!(
            self_key,
            Type::Ref(_)
                | Type::RefMut(_)
                | Type::Slice(_)
                | Type::SliceMut(_)
                | Type::Str
                | Type::Task(_)
                | Type::Stdin
                | Type::Stdout
                | Type::Never
        ) || crate::runtime_types::has_borrow(types, self_key)
        {
            return Err(Diagnostic::new(
                self_ty.span,
                "impls require an owned, non-borrowed concrete type; borrowed records, views, references, and task handles cannot be impl targets in this subset",
            ));
        }
        if trait_id.is_none() && self_key.layout().is_none() {
            return Err(Diagnostic::new(
                self_ty.span,
                "inherent impls require a nominal record or enum type",
            ));
        }
        let record_fields = self_key
            .layout()
            .filter(|id| types.enums[*id].record)
            .map(|id| {
                types.enums[id].variants[0]
                    .names
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>()
            })
            .unwrap_or_default();
        let trait_definition = trait_id.and_then(|id| functions.traits.get(&id).cloned());
        let trait_methods = trait_definition
            .as_ref()
            .map(|definition| definition.methods.clone())
            .unwrap_or_default();
        let trait_generics = trait_definition
            .as_ref()
            .map(|definition| definition.generics.clone())
            .unwrap_or_default();
        let trait_argument_ast = match trait_path {
            Some(ast::Type {
                kind: ast::TypeKind::Named { arguments, .. },
                ..
            }) => arguments.as_slice(),
            _ => &[],
        };
        let trait_arguments = if let Some(trait_id) = trait_id {
            for argument in trait_argument_ast {
                if type_mentions_self(argument) {
                    return Err(Diagnostic::new(
                        argument.span,
                        "'Self' cannot appear in a trait's specialization arguments; write the concrete impl target type",
                    ));
                }
            }
            evaluate_trait_arguments(
                types,
                resolution,
                logical,
                &trait_generics,
                trait_argument_ast,
                &crate::runtime_types::Subst::default(),
                &resolution.bindings[trait_id].name,
                span,
            )?
        } else {
            TraitArguments::default()
        };
        let trait_argument_names = trait_generics
            .iter()
            .zip(trait_argument_ast)
            .map(|(generic, argument)| (generic.name.clone(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut impl_associated = ImplAssociated::default();
        let trait_associated = trait_definition
            .as_ref()
            .map(|definition| definition.associated.clone())
            .unwrap_or_default();
        let mut provided = BTreeSet::new();
        for item in associated {
            match item {
                ast::Associated::Type { name, value, span } => {
                    let Some(value) = value else {
                        return Err(Diagnostic::new(
                            *span,
                            "an associated type in an impl requires a value: 'type Name = Type;'",
                        ));
                    };
                    if type_mentions_self(value) {
                        return Err(Diagnostic::new(
                            value.span,
                            "an associated type value may not mention 'Self'; write a concrete type",
                        ));
                    }
                    if trait_id.is_some()
                        && !matches!(
                            trait_associated.get(name),
                            Some(TraitAssociated::Type { .. })
                        )
                    {
                        return Err(Diagnostic::new(
                            *span,
                            format!(
                                "associated type '{name}' is not declared by the implemented trait"
                            ),
                        ));
                    }
                    if trait_id.is_none() {
                        return Err(Diagnostic::new(
                            *span,
                            "inherent impls define associated constants only; associated types require a trait declaration",
                        ));
                    }
                    if !provided.insert(name.clone()) {
                        return Err(Diagnostic::new(
                            *span,
                            format!("duplicate item '{name}' in one impl"),
                        ));
                    }
                    // Lower the value once so a malformed or cyclic projection
                    // is diagnosed at the impl rather than at an arbitrary use.
                    types.ty_in(value, &crate::runtime_types::Subst::default())?;
                    impl_associated.types.insert(name.clone(), value.clone());
                }
                ast::Associated::Const {
                    name,
                    ty,
                    value,
                    span,
                } => {
                    if type_mentions_self(ty) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "an associated constant's type may not mention 'Self'; write a concrete scalar type",
                        ));
                    }
                    let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                    if !const_scalar_type(types, lowered) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "associated constants must have a compile-time scalar, tuple, or inline-array type; scalar types are i8/i16/i32/i64/u8/u16/u32/u64, Bool, or Char",
                        ));
                    }
                    if trait_id.is_some()
                        && !matches!(
                            trait_associated.get(name),
                            Some(TraitAssociated::Const { .. })
                        )
                    {
                        return Err(Diagnostic::new(
                            *span,
                            format!(
                                "associated constant '{name}' is not declared by the implemented trait"
                            ),
                        ));
                    }
                    if !provided.insert(name.clone()) {
                        return Err(Diagnostic::new(
                            *span,
                            format!("duplicate item '{name}' in one impl"),
                        ));
                    }
                    let declared_ty = match trait_associated.get(name) {
                        Some(TraitAssociated::Const { ty: declared, .. }) => {
                            Some(types.ty_in(declared, &crate::runtime_types::Subst::default())?)
                        }
                        _ => None,
                    };
                    if let Some(declared_ty) = declared_ty
                        && declared_ty != lowered
                    {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "associated constant '{name}' must have the declared type {}",
                                types.name(declared_ty)
                            ),
                        ));
                    }
                    let Some(value) = value else {
                        // A default in the trait is inherited below.
                        continue;
                    };
                    let checked =
                        evaluate_associated_const(types, value, lowered, &impl_associated.consts)?;
                    impl_associated.consts.insert(name.clone(), checked);
                }
            }
        }
        if let Some(trait_id) = trait_id {
            let associated_order = trait_definition
                .as_ref()
                .map(|definition| definition.associated_order.clone())
                .unwrap_or_default();
            for name in &associated_order {
                let Some(item) = trait_associated.get(name) else {
                    continue;
                };
                match item {
                    TraitAssociated::Type { default } => {
                        if !impl_associated.types.contains_key(name) {
                            let Some(default) = default else {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "missing associated type '{name}' for trait '{}' on {}",
                                        resolution.bindings[trait_id].name,
                                        types.name(self_key)
                                    ),
                                ));
                            };
                            impl_associated.types.insert(name.clone(), default.clone());
                        }
                    }
                    TraitAssociated::Const { ty, default } => {
                        if impl_associated.consts.contains_key(name) {
                            continue;
                        }
                        let Some(default) = default else {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "missing associated constant '{name}' for trait '{}' on {}",
                                    resolution.bindings[trait_id].name,
                                    types.name(self_key)
                                ),
                            ));
                        };
                        let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                        let checked = evaluate_associated_const(
                            types,
                            default,
                            lowered,
                            &impl_associated.consts,
                        )?;
                        impl_associated.consts.insert(name.clone(), checked);
                    }
                }
            }
        }
        let associated_index =
            (!impl_associated.types.is_empty() || !impl_associated.consts.is_empty()).then(|| {
                functions.impl_associated.push(impl_associated.clone());
                functions.impl_associated.len() - 1
            });
        if trait_id.is_none() && !impl_associated.consts.is_empty() {
            functions
                .inherent_consts
                .insert(self_key, impl_associated.consts.clone());
        }
        let mut definitions = BTreeMap::new();
        for method in methods {
            let f = &method.function;
            if f.total {
                return Err(Diagnostic::new(
                    method.span,
                    "impl methods are executable declarations and cannot be 'total'",
                ));
            }
            let Some(receiver) = f.parameters.first() else {
                return Err(Diagnostic::new(
                    method.span,
                    "a method must declare a receiver as its first parameter: 'self: Self'/'self: &Self'/'self: &mut Self' or the concrete target type",
                ));
            };
            if receiver.erased || receiver.name != "self" {
                return Err(Diagnostic::new(
                    receiver.span,
                    "the first method parameter must be the receiver, written 'self: Self', 'self: &Self', 'self: &mut Self', or the concrete target type",
                ));
            }
            checked_method_receiver(types, &receiver.ty, self_key)?;
            if Checker::builtin_method(&f.name) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' uses a reserved builtin method name; builtin receiver methods take precedence, so choose another name",
                        f.name
                    ),
                ));
            }
            if record_fields.contains(&f.name) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' collides with a record field of the same name; field projection takes precedence in dot-call syntax, so rename the method",
                        f.name
                    ),
                ));
            }
            if trait_id.is_some() {
                let Some(expected) = trait_methods.get(&f.name) else {
                    return Err(Diagnostic::new(
                        method.span,
                        format!(
                            "method '{}' is not declared by the implemented trait",
                            f.name
                        ),
                    ));
                };
                if method_contract_key(
                    resolution,
                    expected.function,
                    Some(self_ty),
                    Some(&trait_argument_names),
                    Some(&impl_associated.types),
                )? != method_contract_key(
                    resolution,
                    f,
                    Some(self_ty),
                    None,
                    Some(&impl_associated.types),
                )? {
                    return Err(Diagnostic::new(
                        method.span,
                        format!(
                            "method '{}' does not match the trait signature exactly; parameters, parameter grades, erasure markers, result type, generic parameters and bounds, effect exclusions, lifetimes, effects, and substituted trait arguments must match",
                            f.name
                        ),
                    ));
                }
            }
            for parameter in &f.parameters {
                if parameter.erased && type_mentions_self(&parameter.ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "erased method parameters may not mention 'Self' in this subset",
                    ));
                }
            }
            validate_erased_parameters(resolution, logical, f)?;
            validate_length_templates(resolution, f)?;
            let binding = resolution.method(method.span).ok_or_else(|| {
                Diagnostic::new(method.span, "internal error: impl method has no binding")
            })?;
            let definition = MethodDefinition {
                binding,
                public: method.public,
                unit: resolution.unit_of.get(&binding).copied().unwrap_or(0),
                impl_arguments: None,
            };
            if definitions.insert(f.name.clone(), definition).is_some() {
                return Err(Diagnostic::new(
                    method.span,
                    format!("duplicate method '{}' in one impl", f.name),
                ));
            }
            functions.declared.insert(
                binding,
                Declared {
                    ast: f,
                    span: method.span,
                    self_ty: Some(self_key),
                    default_specialization: None,
                    impl_associated: associated_index,
                    impl_template: None,
                },
            );
            bindings.push(binding);
        }
        if let Some(trait_id) = trait_id {
            let trait_public = resolution.public.contains(&trait_id);
            let impl_unit = resolution.item_units.get(&span.start).copied().unwrap_or(0);
            for (name, method) in &trait_methods {
                if definitions.contains_key(name) {
                    continue;
                }
                if method.function.body.is_none() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "missing implementation of trait method '{name}' for {}",
                            types.name(self_key)
                        ),
                    ));
                }
                // An inherited default is materialized as a fresh checked
                // function specialized to this impl's `Self` and trait
                // arguments. It is never shared with another impl: `Self` and
                // trait parameters are substituted per impl.
                let receiver = method
                    .function
                    .parameters
                    .first()
                    .expect("trait receiver was validated at declaration");
                checked_method_receiver(types, &receiver.ty, self_key)?;
                if record_fields.contains(name) {
                    return Err(Diagnostic::new(
                        method.span,
                        format!(
                            "inherited default method '{name}' collides with a record field of the same name; field projection takes precedence in dot-call syntax, so rename the method"
                        ),
                    ));
                }
                let binding = *default_bindings
                    .get(&(span.start, name.clone()))
                    .ok_or_else(|| {
                        Diagnostic::new(
                            method.span,
                            "internal error: inherited default method has no binding",
                        )
                    })?;
                let index = functions.default_specializations.len();
                functions
                    .default_specializations
                    .push((trait_id, trait_arguments.clone()));
                functions.declared.insert(
                    binding,
                    Declared {
                        ast: method.function,
                        span: method.span,
                        self_ty: Some(self_key),
                        default_specialization: Some(index),
                        impl_associated: associated_index,
                        impl_template: None,
                    },
                );
                definitions.insert(
                    name.clone(),
                    MethodDefinition {
                        binding,
                        public: trait_public,
                        unit: impl_unit,
                        impl_arguments: None,
                    },
                );
                bindings.push(binding);
            }
            let specialization = if trait_generics.is_empty() {
                resolution.bindings[trait_id].name.clone()
            } else {
                format!(
                    "{}<{}>",
                    resolution.bindings[trait_id].name,
                    trait_specialization_name(resolution, types, &trait_generics, &trait_arguments)
                )
            };
            if functions
                .trait_impls
                .insert(
                    (trait_id, trait_arguments.clone(), self_key),
                    definitions.clone(),
                )
                .is_some()
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "duplicate implementation of trait '{specialization}' for {}",
                        types.name(self_key)
                    ),
                ));
            }
            for (name, definition) in &definitions {
                functions
                    .methods_by_type
                    .entry(self_key)
                    .or_default()
                    .entry(name.clone())
                    .or_default()
                    .push((trait_id, trait_arguments.clone(), *definition));
            }
            if !impl_associated.consts.is_empty() {
                functions.trait_consts.insert(
                    (trait_id, trait_arguments.clone(), self_key),
                    impl_associated.consts.clone(),
                );
            }
            functions.trait_associated.insert(
                (trait_id, trait_arguments.clone(), self_key),
                impl_associated.clone(),
            );
        } else {
            let inherent = functions.inherent.entry(self_key).or_default();
            for (name, definition) in definitions {
                if inherent.insert(name.clone(), definition).is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "duplicate inherent method '{name}' for {}",
                            types.name(self_key)
                        ),
                    ));
                }
            }
        }
        // Record every concrete impl as a ground header too. Coherence compares
        // it with generic headers: a concrete receiver is an instance of a
        // matching blanket/generic header, which is the specialization axis.
        functions.impl_headers.push(ImplHeader {
            trait_id,
            generics: Vec::new(),
            self_ty: self_ty.clone(),
            trait_arguments: trait_argument_ast.to_vec(),
            associated: impl_associated.clone(),
            methods: match trait_id {
                Some(trait_id) => functions
                    .trait_impls
                    .get(&(trait_id, trait_arguments.clone(), self_key))
                    .cloned()
                    .unwrap_or_default(),
                None => functions
                    .inherent
                    .get(&self_key)
                    .cloned()
                    .unwrap_or_default(),
            },
            span,
            concrete: Some((trait_arguments.clone(), self_key)),
        });
    }
    // Declaration-time coherence. Two impl headers that can apply to the same
    // receiver and trait specialization must be specialization-comparable: one
    // must be an instance of the other. Incomparable overlaps are rejected
    // rather than resolved by declaration order.
    for (left_index, left) in functions.impl_headers.iter().enumerate() {
        for right in functions.impl_headers.iter().skip(left_index + 1) {
            if left.trait_id != right.trait_id {
                continue;
            }
            if left.concrete.is_some() && right.concrete.is_some() {
                // Exact duplicate concrete impls are diagnosed by the exact
                // trait-impl table; distinct concrete headers are disjoint.
                continue;
            }
            if !headers_overlap(resolution, left, right) {
                continue;
            }
            // Several inherent impls for the same type may coexist when their
            // method names are disjoint. Trait impls always repeat the trait's
            // method set, so any equivalent trait header is a duplicate.
            if left.trait_id.is_none()
                && !left
                    .methods
                    .keys()
                    .any(|name| right.methods.contains_key(name))
            {
                continue;
            }
            let left_covers = header_subsumes(resolution, left, right);
            let right_covers = header_subsumes(resolution, right, left);
            let left_label = impl_header_label(resolution, types, left);
            let right_label = impl_header_label(resolution, types, right);
            if left_covers && right_covers {
                return Err(Diagnostic::new(
                    right.span,
                    format!(
                        "duplicate implementation: {left_label} and {right_label} cover the same receiver and trait specialization; keep one impl",
                    ),
                ));
            }
            if !left_covers && !right_covers {
                return Err(Diagnostic::new(
                    right.span,
                    format!(
                        "overlapping implementations {left_label} and {right_label} are incomparable: neither pattern is more specific, so dispatch has no deterministic winner; make the impls disjoint or specialize one pattern",
                    ),
                ));
            }
        }
    }
    // Trait-bound arity is a declaration property. It is checked once every
    // trait definition is registered, including bounds on ordinary functions
    // and on generic methods that are never instantiated.
    for function in functions
        .declared
        .values()
        .map(|declared| declared.ast)
        .chain(trait_methods_to_check)
    {
        for generic in &function.generics {
            let Some(bound) = &generic.bound else {
                continue;
            };
            let Some(trait_id) = resolution.reference(bound.span) else {
                continue;
            };
            if resolution.bindings[trait_id].kind != BindingKind::Trait {
                continue;
            }
            let arguments = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.len(),
                _ => 0,
            };
            let expected = functions.traits[&trait_id].generics.len();
            if arguments != expected {
                return Err(Diagnostic::new(
                    generic.span,
                    format!(
                        "trait '{}' expects {expected} argument(s), found {arguments}",
                        resolution.bindings[trait_id].name
                    ),
                ));
            }
        }
    }
    Ok(bindings)
}

/// Build the closed-world representation of every usable trait object after
/// all impls are known. A trait is object-safe here only when:
///
/// - it has no generic or blanket impls, so the member set is finite;
/// - every trait parameter is an ordinary type (no Nat/Grade/Effect arguments);
/// - every method takes an owned `self: Self` receiver, has no method generics
///   or lifetimes, and mentions neither `Self` nor erased proof parameters in
///   its remaining parameters or result;
/// - every concrete impl of one specialization agrees on each associated type
///   and constant value used by the object.
///
/// The object is the normalized union of the concrete impl targets. Borrowed
/// receivers are rejected rather than silently copying or moving a derived
/// payload; supporting them needs a checked borrowed-trait-object capability.
fn prepare_trait_objects<'a>(
    types: &mut Types<'a>,
    resolution: &Resolution,
    functions: &mut Functions<'a>,
) -> Result<()> {
    let traits = functions
        .traits
        .iter()
        .map(|(id, definition)| (*id, definition.clone()))
        .collect::<Vec<_>>();
    for (trait_id, definition) in traits {
        let trait_name = resolution.bindings[trait_id].name.clone();
        let mut reason: Option<String> = None;
        for generic in &definition.generics {
            if generic_category(resolution, generic) != GenericCategory::Type {
                reason = Some(format!(
                    "trait parameter '{}' is not an ordinary type; dyn objects support type parameters only",
                    generic.name
                ));
                break;
            }
        }
        let associated_type_names = definition
            .associated
            .iter()
            .filter_map(|(name, item)| {
                matches!(item, TraitAssociated::Type { .. }).then_some(name.clone())
            })
            .collect::<BTreeSet<_>>();
        if reason.is_none() {
            for (name, method) in &definition.methods {
                let f = method.function;
                let Some(receiver) = f.parameters.first() else {
                    continue;
                };
                match &receiver.ty.kind {
                    ast::TypeKind::SelfType => {}
                    ast::TypeKind::Borrow {
                        mutable: false,
                        inner,
                        ..
                    } if matches!(inner.kind, ast::TypeKind::SelfType) => {}
                    ast::TypeKind::Borrow {
                        mutable: true,
                        inner,
                        ..
                    } if matches!(inner.kind, ast::TypeKind::SelfType) => {}
                    _ => {
                        reason = Some(format!(
                            "method '{name}' receiver must be 'self: Self', 'self: &Self', '&self', 'self: &mut Self', or '&mut self'"
                        ));
                        break;
                    }
                }
                if !f.generics.is_empty() {
                    reason = Some(format!(
                        "method '{name}' is generic; a generic method cannot be dispatched through a dyn object without runtime type arguments"
                    ));
                    break;
                }
                if !f.lifetimes.is_empty() {
                    reason = Some(format!(
                        "method '{name}' has lifetime parameters; dyn objects cannot erase an exact-use or borrow contract"
                    ));
                    break;
                }
                if let Some(parameter) = f.parameters[1..].iter().find(|parameter| {
                    parameter.erased
                        || type_mentions_self_outside_assoc(&parameter.ty, &associated_type_names)
                }) {
                    reason = Some(if parameter.erased {
                        format!(
                            "method '{name}' has an erased proof parameter; proof terms cannot be erased through dynamic dispatch"
                        )
                    } else {
                        format!(
                            "method '{name}' mentions 'Self' in a non-receiver parameter, so its ABI would differ per impl"
                        )
                    });
                    break;
                }
                if type_mentions_self_outside_assoc(&f.result, &associated_type_names) {
                    reason = Some(format!(
                        "method '{name}' mentions 'Self' in its result, so dynamic dispatch would erase the concrete result type"
                    ));
                    break;
                }
            }
        }
        if reason.is_none()
            && functions
                .impl_headers
                .iter()
                .any(|header| header.trait_id == Some(trait_id) && header.concrete.is_none())
        {
            reason = Some(format!(
                "trait '{trait_name}' has a generic or blanket impl, so its set of concrete members is open"
            ));
        }
        let mut groups: BTreeMap<TraitArguments, Vec<Type>> = BTreeMap::new();
        let mut object_associated: BTreeMap<TraitArguments, BTreeMap<String, Type>> =
            BTreeMap::new();
        if reason.is_none() {
            let mut concrete: Vec<(TraitArguments, Type, ImplAssociated)> = Vec::new();
            for header in &functions.impl_headers {
                if header.trait_id == Some(trait_id)
                    && let Some((arguments, member)) = &header.concrete
                {
                    concrete.push((arguments.clone(), *member, header.associated.clone()));
                }
            }
            if reason.is_none() {
                if concrete.is_empty() {
                    reason = Some(format!("trait '{trait_name}' has no concrete impls"));
                } else {
                    let mut associated_consts: BTreeMap<
                        TraitArguments,
                        BTreeMap<String, ConstValue>,
                    > = BTreeMap::new();
                    for (arguments, member, associated) in &concrete {
                        groups.entry(arguments.clone()).or_default().push(*member);
                        // A default associated type may mention the trait's
                        // type, Nat, Grade, or effect parameters. Lower it with
                        // this specialization's arguments, exactly like a
                        // method signature, so two impls using the same
                        // default do not spuriously disagree.
                        let mut member_substitution = crate::runtime_types::Subst::default();
                        let mut member_consts = BTreeMap::new();
                        let mut member_grades = BTreeMap::new();
                        let mut member_effects = BTreeMap::new();
                        insert_trait_arguments(
                            resolution,
                            &definition.generics,
                            arguments,
                            &mut member_substitution,
                            &mut member_consts,
                            &mut member_grades,
                            &mut member_effects,
                        );
                        member_substitution.consts = member_consts;
                        member_substitution.grades = member_grades;
                        member_substitution.effects = member_effects;
                        member_substitution.associated_types = associated.types.clone();
                        let types_entry = object_associated.entry(arguments.clone()).or_default();
                        for (name, value) in &associated.types {
                            let lowered = types.ty_in(value, &member_substitution)?;
                            if let Some(previous) = types_entry.get(name)
                                && *previous != lowered
                            {
                                reason = Some(format!(
                                    "impls of trait '{trait_name}' disagree on associated type '{name}'; a dyn object needs one projected type"
                                ));
                                break;
                            }
                            types_entry.insert(name.clone(), lowered);
                        }
                        let consts_entry = associated_consts.entry(arguments.clone()).or_default();
                        for (name, value) in &associated.consts {
                            if let Some(previous) = consts_entry.get(name)
                                && previous != value
                            {
                                reason = Some(format!(
                                    "impls of trait '{trait_name}' disagree on associated constant '{name}'; a dyn object would have ambiguous constant projection"
                                ));
                                break;
                            }
                            consts_entry.insert(name.clone(), value.clone());
                        }
                        if reason.is_some() {
                            break;
                        }
                    }
                }
            }
        }
        for (arguments, mut members) in groups {
            members.sort();
            members.dedup();
            let shared_receiver = definition.methods.values().any(|method| {
                matches!(
                    method
                        .function
                        .parameters
                        .first()
                        .map(|parameter| &parameter.ty.kind),
                    Some(ast::TypeKind::Borrow { mutable: false, .. })
                )
            });
            if shared_receiver
                && let Some(member) = members.iter().find(|member| {
                    crate::runtime_types::type_owns(&types.enums, &types.unions, **member, 0)
                })
            {
                reason = Some(format!(
                    "a method borrows '&self', but object member '{}' owns storage; a shared dispatch would move the object. Use an owned receiver or make every member copyable",
                    types.name(*member)
                ));
                break;
            }
            let object = match types.union(members, resolution.bindings[trait_id].span) {
                Ok(object) => object,
                Err(error) => {
                    // A trait with many impls that is never used as `dyn` must
                    // not make an otherwise valid program fail.
                    reason = Some(format!(
                        "cannot build a closed-world union: {}",
                        error.message
                    ));
                    break;
                }
            };
            if let Some(values) = object_associated.get(&arguments) {
                functions
                    .object_associated
                    .insert((trait_id, arguments.clone()), values.clone());
            }
            types
                .dyn_objects
                .insert((trait_id, arguments.clone()), object);
            functions
                .object_traits
                .entry(object)
                .or_default()
                .push((trait_id, arguments));
        }
        if let Some(reason) = reason {
            types.dyn_errors.insert(trait_id, reason);
        }
    }
    for entries in functions.object_traits.values_mut() {
        entries.sort();
        entries.dedup();
    }
    Ok(())
}
/// Validate that a generic impl's self type or trait argument is a first-order
/// pattern over its declared type parameters and nominal types. Borrows,
/// slices, function arrows, aliases, and associated projections cannot appear in
/// an impl header: their runtime representation would make coherence depend on
/// an unresolved lifetime or expansion.
fn validate_impl_pattern(
    resolution: &Resolution,
    types: &Types<'_>,
    pattern: &ast::Type,
    generics: &BTreeSet<BindingId>,
    const_binders: &BTreeSet<BindingId>,
    what: &str,
) -> Result<()> {
    match &pattern.kind {
        ast::TypeKind::Named { path, arguments } => {
            if path.len() == 2 {
                return Err(Diagnostic::new(
                    pattern.span,
                    format!(
                        "an impl {what} may not contain the associated projection '{}'; write the impl parameter or a nominal type",
                        path.join(".")
                    ),
                ));
            }
            let id = resolution.reference(pattern.span).ok_or_else(|| {
                Diagnostic::new(pattern.span, format!("impl {what} did not resolve"))
            })?;
            let binding = &resolution.bindings[id];
            match binding.kind {
                BindingKind::Generic | BindingKind::Parameter => {
                    if !generics.contains(&id) {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "impl {what} names '{}', which is not one of this impl's parameters",
                                binding.name
                            ),
                        ));
                    }
                    if !arguments.is_empty() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "an impl type parameter cannot take type arguments",
                        ));
                    }
                }
                BindingKind::Builtin | BindingKind::Data => {}
                BindingKind::Alias => {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "transparent aliases are not supported in generic impl headers; write the expanded nominal type",
                    ));
                }
                _ => {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!("'{}' cannot appear in a generic impl header", binding.name),
                    ));
                }
            }
            for argument in arguments {
                validate_impl_pattern(resolution, types, argument, generics, const_binders, what)?;
            }
            Ok(())
        }
        ast::TypeKind::Tuple(items) => {
            for item in items {
                validate_impl_pattern(resolution, types, item, generics, const_binders, what)?;
            }
            Ok(())
        }
        ast::TypeKind::Array(element, length) => {
            validate_impl_pattern(resolution, types, element, generics, const_binders, what)?;
            // A header length may be a literal or a bare natural parameter.
            // Arithmetic would make declaration-time coherence depend on an
            // evaluator, so it is rejected here and must be written into the
            // trait arguments or a concrete array length instead.
            let simple = matches!(length.kind, ast::TypeKind::Integer(_))
                || pattern_binder(resolution, length).is_some_and(|id| const_binders.contains(&id));
            if !simple {
                return Err(Diagnostic::new(
                    length.span,
                    "an impl header array length must be an integer literal or a natural parameter",
                ));
            }
            validate_length_template(resolution, length, const_binders)?;
            Ok(())
        }
        ast::TypeKind::Integer(_) | ast::TypeKind::Bool(_) => Ok(()),
        ast::TypeKind::Structural(_) => Err(Diagnostic::new(
            pattern.span,
            format!(
                "an impl {what} may not be an anonymous structural record; declare a nominal record and use it in the impl header"
            ),
        )),
        ast::TypeKind::Dyn(_) => Err(Diagnostic::new(
            pattern.span,
            format!("an impl {what} may not be a trait object; name the concrete receiver"),
        )),
        ast::TypeKind::Borrow { .. }
        | ast::TypeKind::Slice(_)
        | ast::TypeKind::Function { .. }
        | ast::TypeKind::Graded { .. }
        | ast::TypeKind::Binary { .. }
        | ast::TypeKind::Lifetime(_)
        | ast::TypeKind::Predicate(_)
        | ast::TypeKind::SelfType => Err(Diagnostic::new(
            pattern.span,
            format!(
                "an impl {what} must be an owned nominal type pattern built from the impl's type parameters; borrows, slices, arrows, unions, grades, lifetimes, predicates, and 'Self' are not supported (searched {})",
                types.name(Type::Unit)
            ),
        )),
    }
}
/// The binder of a bare type parameter pattern, if `ty` is one.
fn pattern_binder(resolution: &Resolution, ty: &ast::Type) -> Option<BindingId> {
    let ast::TypeKind::Named { path, arguments } = &ty.kind else {
        return None;
    };
    if path.len() != 1 || !arguments.is_empty() {
        return None;
    }
    let id = resolution.reference(ty.span)?;
    (resolution.bindings[id].kind == BindingKind::Generic).then_some(id)
}
/// Bindings produced by matching one impl header pattern. Type, natural,
/// grade, and effect parameters are solved together because a single header may
/// mention all four categories while its receiver and trait arguments must agree
/// on each binding.
#[derive(Debug, Clone, Default)]
struct PatternBindings {
    types: BTreeMap<BindingId, Type>,
    consts: BTreeMap<BindingId, usize>,
    grades: BTreeMap<BindingId, Grade>,
    effects: BTreeMap<BindingId, u8>,
}
impl PatternBindings {
    fn subst(&self) -> crate::runtime_types::Subst {
        crate::runtime_types::Subst {
            types: self.types.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effects.clone(),
            ..Default::default()
        }
    }
}
/// Whether a pattern still contains a generic binder absent from `bindings`.
fn pattern_has_unbound(
    resolution: &Resolution,
    ty: &ast::Type,
    bindings: &PatternBindings,
) -> bool {
    if let Some(id) = pattern_binder(resolution, ty) {
        return !bindings.types.contains_key(&id);
    }
    match &ty.kind {
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => arguments
            .iter()
            .any(|argument| pattern_has_unbound(resolution, argument, bindings)),
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => {
            pattern_has_unbound(resolution, inner, bindings)
        }
        ast::TypeKind::Borrow { inner, .. } => pattern_has_unbound(resolution, inner, bindings),
        ast::TypeKind::Array(inner, length) => {
            pattern_has_unbound(resolution, inner, bindings)
                || pattern_has_unbound(resolution, length, bindings)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            pattern_has_unbound(resolution, left, bindings)
                || pattern_has_unbound(resolution, right, bindings)
        }
        _ => false,
    }
}
/// Match one compile-time natural pattern (an array length or a `Nat` trait
/// argument). A bare unbound natural binder captures `actual`; any other
/// pattern must evaluate to that exact natural under the bindings already
/// solved.
fn match_const_pattern(
    resolution: &Resolution,
    logical: &crate::check::LogicalEnvironment,
    pattern: &ast::Type,
    actual: usize,
    bindings: &mut PatternBindings,
) -> Result<bool> {
    if let Some(id) = pattern_binder(resolution, pattern) {
        if let Some(existing) = bindings.consts.get(&id) {
            return Ok(*existing == actual);
        }
        bindings.consts.insert(id, actual);
        return Ok(true);
    }
    let subst = bindings.subst();
    let expected = crate::length::eval_type(resolution, logical, &subst.consts, pattern)?;
    Ok(expected == actual)
}
/// Match one grade pattern (a `Grade` trait argument). A bare unbound grade
/// binder captures `actual`; any other pattern must evaluate to that grade under
/// the bindings already solved.
fn match_grade_pattern(
    resolution: &Resolution,
    pattern: &ast::Type,
    actual: Grade,
    bindings: &mut PatternBindings,
) -> Result<bool> {
    if let Some(id) = pattern_binder(resolution, pattern) {
        if let Some(existing) = bindings.grades.get(&id) {
            return Ok(*existing == actual);
        }
        bindings.grades.insert(id, actual);
        return Ok(true);
    }
    let grades = crate::grades::evaluate(resolution, &bindings.grades, pattern)?;
    Ok(grades == actual)
}
/// First-order match of an impl type pattern against a concrete runtime type.
fn match_type_pattern(
    resolution: &Resolution,
    types: &mut Types<'_>,
    pattern: &ast::Type,
    actual: Type,
    bindings: &mut PatternBindings,
    depth: usize,
) -> Result<bool> {
    if depth >= 64 {
        return Err(Diagnostic::new(
            pattern.span,
            "generic impl matching exceeded its nesting budget",
        ));
    }
    if let Some(id) = pattern_binder(resolution, pattern) {
        if let Some(existing) = bindings.types.get(&id) {
            return Ok(*existing == actual);
        }
        if actual == Type::Never
            || actual.is_view()
            || matches!(actual, Type::Ref(_) | Type::RefMut(_))
        {
            return Ok(false);
        }
        bindings.types.insert(id, actual.full());
        return Ok(true);
    }
    if !pattern_has_unbound(resolution, pattern, bindings) {
        let subst = bindings.subst();
        return Ok(types.ty_in(pattern, &subst)? == actual);
    }
    match &pattern.kind {
        ast::TypeKind::Named { arguments, .. } => {
            let Some(id) = resolution.reference(pattern.span) else {
                return Ok(false);
            };
            let binding = &resolution.bindings[id];
            match (binding.kind, binding.name.as_str(), actual) {
                (BindingKind::Builtin, "Box", Type::Box(pointer))
                | (BindingKind::Builtin, "Vec", Type::Vec(pointer))
                    if arguments.len() == 1 =>
                {
                    let pointee = types.pointees[pointer];
                    match_type_pattern(
                        resolution,
                        types,
                        &arguments[0],
                        pointee,
                        bindings,
                        depth + 1,
                    )
                }
                (BindingKind::Data, _, Type::Enum(layout))
                    if types.enums[layout].definition == id =>
                {
                    let actual_arguments = types.enums[layout].arguments.clone();
                    let actual_consts = types.enums[layout].consts.clone();
                    let kinds = types.generic_kinds(id);
                    let mut actual_types = actual_arguments.iter();
                    let mut actual_consts = actual_consts.iter();
                    for (argument, is_const) in arguments.iter().zip(kinds) {
                        if is_const {
                            let Some(value) = actual_consts.next() else {
                                return Ok(false);
                            };
                            if !match_const_pattern(
                                resolution,
                                types.logical(),
                                argument,
                                *value,
                                bindings,
                            )? {
                                return Ok(false);
                            }
                        } else {
                            let Some(actual) = actual_types.next() else {
                                return Ok(false);
                            };
                            if !match_type_pattern(
                                resolution,
                                types,
                                argument,
                                *actual,
                                bindings,
                                depth + 1,
                            )? {
                                return Ok(false);
                            }
                        }
                    }
                    Ok(true)
                }
                _ => Ok(false),
            }
        }
        ast::TypeKind::Tuple(items) => {
            let Some(layout) = actual.layout().filter(|layout| types.enums[*layout].tuple) else {
                return Ok(false);
            };
            let elements = types.enums[layout].arguments.clone();
            if elements.len() != items.len() {
                return Ok(false);
            }
            for (item, element) in items.iter().zip(elements) {
                if !match_type_pattern(resolution, types, item, element, bindings, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        ast::TypeKind::Array(element, length) => {
            let Some(layout) = actual.layout() else {
                return Ok(false);
            };
            let Some((actual_element, actual_length)) = types.enums[layout].array else {
                return Ok(false);
            };
            Ok(
                match_const_pattern(resolution, types.logical(), length, actual_length, bindings)?
                    && match_type_pattern(
                        resolution,
                        types,
                        element,
                        actual_element,
                        bindings,
                        depth + 1,
                    )?,
            )
        }
        _ => Ok(false),
    }
}
/// Match an impl header's raw trait arguments against the concrete arguments an
/// obligation requires, by the trait's declared generic categories.
#[allow(clippy::too_many_arguments)]
fn match_trait_argument_patterns(
    resolution: &Resolution,
    types: &mut Types<'_>,
    logical: &crate::check::LogicalEnvironment,
    generics: &[ast::Generic],
    patterns: &[ast::Type],
    required: &TraitArguments,
    bindings: &mut PatternBindings,
) -> Result<bool> {
    if patterns.len() != generics.len() {
        return Ok(false);
    }
    let (mut type_index, mut const_index, mut grade_index, mut effect_index) = (0, 0, 0, 0);
    for (generic, pattern) in generics.iter().zip(patterns) {
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                let Some(actual) = required.types.get(type_index) else {
                    return Ok(false);
                };
                type_index += 1;
                if !match_type_pattern(resolution, types, pattern, *actual, bindings, 0)? {
                    return Ok(false);
                }
            }
            GenericCategory::Const => {
                let Some(actual) = required.consts.get(const_index) else {
                    return Ok(false);
                };
                const_index += 1;
                if !match_const_pattern(resolution, logical, pattern, *actual, bindings)? {
                    return Ok(false);
                }
            }
            GenericCategory::Grade => {
                let Some(actual) = required.grades.get(grade_index) else {
                    return Ok(false);
                };
                grade_index += 1;
                if !match_grade_pattern(resolution, pattern, *actual, bindings)? {
                    return Ok(false);
                }
            }
            GenericCategory::Effect => {
                let Some(actual) = required.effects.get(effect_index) else {
                    return Ok(false);
                };
                effect_index += 1;
                if let Some(id) = pattern_binder(resolution, pattern) {
                    if let Some(existing) = bindings.effects.get(&id) {
                        if *existing != *actual {
                            return Ok(false);
                        }
                    } else {
                        bindings.effects.insert(id, *actual);
                    }
                    continue;
                }
                let effects = crate::runtime_types::effect_bits_with(
                    resolution,
                    std::slice::from_ref(pattern),
                    &bindings.effects,
                )?;
                if effects != *actual {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}
/// Pack solved header bindings into the category-ordered impl argument list.
/// Missing type bindings cannot occur for a constrained header; a missing
/// const/grade binding falls back to the category identity only so diagnostics
/// stay deterministic instead of indexing out of bounds.
fn solved_impl_arguments(
    resolution: &Resolution,
    generics: &[ast::Generic],
    bindings: &PatternBindings,
) -> ImplArguments {
    let mut out = ImplArguments::default();
    for generic in generics {
        let binder = resolution.binder(generic.span).unwrap();
        match generic_category(resolution, generic) {
            GenericCategory::Type => out
                .types
                .push(bindings.types.get(&binder).copied().unwrap_or(Type::Unit)),
            GenericCategory::Const => out
                .consts
                .push(bindings.consts.get(&binder).copied().unwrap_or(0)),
            GenericCategory::Grade => out.grades.push(
                bindings
                    .grades
                    .get(&binder)
                    .copied()
                    .unwrap_or(Grade::Finite(0)),
            ),
            GenericCategory::Effect => out
                .effects
                .push(bindings.effects.get(&binder).copied().unwrap_or(0)),
        }
    }
    out
}
/// Build the full substitution of one solved impl header: type, natural, grade,
/// and effect parameters in declaration order.
fn impl_arguments_subst(
    resolution: &Resolution,
    generics: &[ast::Generic],
    arguments: &ImplArguments,
) -> crate::runtime_types::Subst {
    let mut out = crate::runtime_types::Subst::default();
    let (mut type_index, mut const_index, mut grade_index, mut effect_index) = (0, 0, 0, 0);
    for generic in generics {
        let Some(binder) = resolution.binder(generic.span) else {
            continue;
        };
        match generic_category(resolution, generic) {
            GenericCategory::Type => {
                if let Some(ty) = arguments.types.get(type_index) {
                    out.types.insert(binder, *ty);
                }
                type_index += 1;
            }
            GenericCategory::Const => {
                if let Some(value) = arguments.consts.get(const_index) {
                    out.consts.insert(binder, *value);
                }
                const_index += 1;
            }
            GenericCategory::Grade => {
                if let Some(value) = arguments.grades.get(grade_index) {
                    out.grades.insert(binder, *value);
                }
                grade_index += 1;
            }
            GenericCategory::Effect => {
                if let Some(value) = arguments.effects.get(effect_index) {
                    out.effects.insert(binder, *value);
                }
                effect_index += 1;
            }
        }
    }
    out
}
/// Replace a mapped binder and recursively expand its value.
fn expand_pattern(
    resolution: &Resolution,
    ty: &ast::Type,
    map: &BTreeMap<BindingId, ast::Type>,
    depth: usize,
) -> ast::Type {
    if depth >= 64 {
        return ty.clone();
    }
    if let Some(id) = pattern_binder(resolution, ty)
        && let Some(value) = map.get(&id)
    {
        return expand_pattern(resolution, value, map, depth + 1);
    }
    let kind = match &ty.kind {
        ast::TypeKind::Named { path, arguments } => ast::TypeKind::Named {
            path: path.clone(),
            arguments: arguments
                .iter()
                .map(|argument| expand_pattern(resolution, argument, map, depth + 1))
                .collect(),
        },
        ast::TypeKind::Tuple(items) => ast::TypeKind::Tuple(
            items
                .iter()
                .map(|item| expand_pattern(resolution, item, map, depth + 1))
                .collect(),
        ),
        ast::TypeKind::Array(inner, length) => ast::TypeKind::Array(
            Box::new(expand_pattern(resolution, inner, map, depth + 1)),
            Box::new(expand_pattern(resolution, length, map, depth + 1)),
        ),
        ast::TypeKind::Borrow {
            lifetime,
            mutable,
            inner,
        } => ast::TypeKind::Borrow {
            lifetime: lifetime.clone(),
            mutable: *mutable,
            inner: Box::new(expand_pattern(resolution, inner, map, depth + 1)),
        },
        ast::TypeKind::Slice(inner) => {
            ast::TypeKind::Slice(Box::new(expand_pattern(resolution, inner, map, depth + 1)))
        }
        other => other.clone(),
    };
    ast::Type::new(kind, ty.span)
}
/// Unify two type patterns. Binders in `flexible` may be assigned; every other
/// binder is rigid and compares by identity. Used both for overlap detection
/// (both sides flexible) and specificity (only the more general side flexible).
fn unify_ast_patterns(
    resolution: &Resolution,
    left: &ast::Type,
    right: &ast::Type,
    flexible: &BTreeSet<BindingId>,
    map: &mut BTreeMap<BindingId, ast::Type>,
    depth: usize,
) -> bool {
    if depth >= 64 {
        return false;
    }
    let left = expand_pattern(resolution, left, map, 0);
    let right = expand_pattern(resolution, right, map, 0);
    if let Some(id) = pattern_binder(resolution, &left)
        && flexible.contains(&id)
    {
        if pattern_binder(resolution, &right) == Some(id) {
            return true;
        }
        if type_references_any_binder(resolution, &right, &BTreeSet::from([id])) {
            return false;
        }
        map.insert(id, right);
        return true;
    }
    if let Some(id) = pattern_binder(resolution, &right)
        && flexible.contains(&id)
    {
        if type_references_any_binder(resolution, &left, &BTreeSet::from([id])) {
            return false;
        }
        map.insert(id, left);
        return true;
    }
    match (&left.kind, &right.kind) {
        (
            ast::TypeKind::Named {
                arguments: left_arguments,
                ..
            },
            ast::TypeKind::Named {
                arguments: right_arguments,
                ..
            },
        ) => {
            if resolution.reference(left.span) != resolution.reference(right.span)
                || left_arguments.len() != right_arguments.len()
            {
                return false;
            }
            left_arguments
                .iter()
                .zip(right_arguments)
                .all(|(left, right)| {
                    unify_ast_patterns(resolution, left, right, flexible, map, depth + 1)
                })
        }
        (ast::TypeKind::Tuple(left), ast::TypeKind::Tuple(right)) => {
            left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| {
                    unify_ast_patterns(resolution, left, right, flexible, map, depth + 1)
                })
        }
        (
            ast::TypeKind::Array(left_element, left_length),
            ast::TypeKind::Array(right_element, right_length),
        ) => {
            unify_ast_patterns(
                resolution,
                left_element,
                right_element,
                flexible,
                map,
                depth + 1,
            ) && type_key(left_length) == type_key(right_length)
        }
        (
            ast::TypeKind::Borrow {
                mutable: left_mutable,
                inner: left_inner,
                ..
            },
            ast::TypeKind::Borrow {
                mutable: right_mutable,
                inner: right_inner,
                ..
            },
        ) => {
            left_mutable == right_mutable
                && unify_ast_patterns(
                    resolution,
                    left_inner,
                    right_inner,
                    flexible,
                    map,
                    depth + 1,
                )
        }
        (ast::TypeKind::Slice(left), ast::TypeKind::Slice(right)) => {
            unify_ast_patterns(resolution, left, right, flexible, map, depth + 1)
        }
        _ => type_key(&left) == type_key(&right),
    }
}
/// Whether `general` can produce `specific`: every parameter of `general` is
/// flexible, every parameter of `specific` is rigid.
fn header_subsumes(resolution: &Resolution, general: &ImplHeader, specific: &ImplHeader) -> bool {
    let flexible = header_binders(resolution, general);
    let mut map = BTreeMap::new();
    if !unify_ast_patterns(
        resolution,
        &general.self_ty,
        &specific.self_ty,
        &flexible,
        &mut map,
        0,
    ) {
        return false;
    }
    general
        .trait_arguments
        .iter()
        .zip(&specific.trait_arguments)
        .all(|(general, specific)| {
            unify_ast_patterns(resolution, general, specific, &flexible, &mut map, 0)
        })
        && general.trait_arguments.len() == specific.trait_arguments.len()
}
/// Whether two impl headers can apply to one receiver and specialization.
fn headers_overlap(resolution: &Resolution, left: &ImplHeader, right: &ImplHeader) -> bool {
    let mut flexible = header_binders(resolution, left);
    flexible.extend(header_binders(resolution, right));
    let mut map = BTreeMap::new();
    if !unify_ast_patterns(
        resolution,
        &left.self_ty,
        &right.self_ty,
        &flexible,
        &mut map,
        0,
    ) {
        return false;
    }
    left.trait_arguments.len() == right.trait_arguments.len()
        && left
            .trait_arguments
            .iter()
            .zip(&right.trait_arguments)
            .all(|(left, right)| {
                unify_ast_patterns(resolution, left, right, &flexible, &mut map, 0)
            })
}
fn impl_header_label(resolution: &Resolution, types: &Types<'_>, header: &ImplHeader) -> String {
    let trait_name = match header.trait_id {
        Some(trait_id) => {
            let name = &resolution.bindings[trait_id].name;
            if header.trait_arguments.is_empty() {
                format!("trait '{name}'")
            } else {
                let arguments = header
                    .trait_arguments
                    .iter()
                    .map(type_key)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("trait '{name}<{arguments}>'")
            }
        }
        None => "an inherent impl".to_owned(),
    };
    let receiver = match header.concrete {
        Some((_, ty)) => types.name(ty),
        None => type_key(&header.self_ty),
    };
    let prefix = if header.generics.is_empty() {
        "impl".to_owned()
    } else {
        format!(
            "impl<{}>",
            header
                .generics
                .iter()
                .map(|generic| generic.name.clone())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!("{prefix} {trait_name} for {receiver}")
}
fn header_binders(resolution: &Resolution, header: &ImplHeader) -> BTreeSet<BindingId> {
    header
        .generics
        .iter()
        .filter_map(|generic| resolution.binder(generic.span))
        .collect()
}
/// Collect one generic or blanket impl. Its methods are registered once, as
/// templates; each concrete receiver match gets a checked instance keyed by the
/// impl argument list. Associated values are supplied to that instance exactly
/// like a concrete impl's.
#[allow(clippy::too_many_arguments)]
fn collect_generic_impl<'a>(
    span: Span,
    generics: &'a [ast::Generic],
    trait_path: Option<&ast::Type>,
    trait_id: Option<BindingId>,
    self_ty: &'a ast::Type,
    associated: &'a [ast::Associated],
    methods: &'a [ast::Method],
    default_bindings: &BTreeMap<(usize, String), BindingId>,
    resolution: &Resolution,
    types: &mut Types<'a>,
    logical: &crate::check::LogicalEnvironment,
    functions: &mut Functions<'a>,
) -> Result<Vec<BindingId>> {
    let mut generic_ids = BTreeSet::new();
    for generic in generics {
        // Every binder category is admitted. Dispatch solves a natural from an
        // array length or `Nat` trait argument, a grade from a `Grade` trait
        // argument, and an effect row from an effect argument; a parameter that
        // no pattern determines is rejected by the constrained-parameter check
        // below.
        if generic.excludes.is_some() || generic.includes.is_some() {
            return Err(Diagnostic::new(
                generic.span,
                "effect-row bounds are not supported on impl parameters",
            ));
        }
        let id = resolution
            .binder(generic.span)
            .ok_or_else(|| Diagnostic::new(generic.span, "impl parameter did not resolve"))?;
        generic_ids.insert(id);
        if let Some(bound) = &generic.bound {
            let Some(bound_id) = resolution.reference(bound.span) else {
                return Err(Diagnostic::new(
                    bound.span,
                    "impl parameter bound did not resolve",
                ));
            };
            let binding = &resolution.bindings[bound_id];
            if binding.kind == BindingKind::Builtin {
                let expected = match generic_category(resolution, generic) {
                    GenericCategory::Type => "Type",
                    GenericCategory::Const => "Nat",
                    GenericCategory::Grade => "Grade",
                    GenericCategory::Effect => "Effects",
                };
                if binding.name != expected {
                    return Err(Diagnostic::new(
                        bound.span,
                        format!(
                            "impl parameter '{}' must be bounded by '{expected}' for its category",
                            generic.name
                        ),
                    ));
                }
                continue;
            }
            if binding.kind != BindingKind::Trait {
                return Err(Diagnostic::new(
                    bound.span,
                    "impl type parameters may be bounded only by declared traits, as in 'impl<T: Show> Show for Box<T>'",
                ));
            }
            if generic_category(resolution, generic) != GenericCategory::Type {
                return Err(Diagnostic::new(
                    bound.span,
                    "only an ordinary type parameter may carry a trait bound on an impl header",
                ));
            }
            let arguments = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.len(),
                _ => 0,
            };
            let expected = functions.traits[&bound_id].generics.len();
            if arguments != expected {
                return Err(Diagnostic::new(
                    generic.span,
                    format!(
                        "trait '{}' expects {expected} argument(s), found {arguments}",
                        resolution.bindings[bound_id].name
                    ),
                ));
            }
        }
    }
    let trait_definition = trait_id.and_then(|id| functions.traits.get(&id).cloned());
    let trait_methods = trait_definition
        .as_ref()
        .map(|definition| definition.methods.clone())
        .unwrap_or_default();
    let trait_generics = trait_definition
        .as_ref()
        .map(|definition| definition.generics.clone())
        .unwrap_or_default();
    let trait_associated = trait_definition
        .as_ref()
        .map(|definition| definition.associated.clone())
        .unwrap_or_default();
    let trait_argument_ast = match trait_path {
        Some(ast::Type {
            kind: ast::TypeKind::Named { arguments, .. },
            ..
        }) => arguments.clone(),
        _ => Vec::new(),
    };
    if let Some(trait_id) = trait_id
        && trait_argument_ast.len() != trait_generics.len()
    {
        let name = resolution.bindings[trait_id].name.clone();
        return Err(Diagnostic::new(
            span,
            format!(
                "trait '{name}' expects {} argument(s), found {}",
                trait_generics.len(),
                trait_argument_ast.len()
            ),
        ));
    }
    for argument in &trait_argument_ast {
        if type_mentions_self(argument) {
            return Err(Diagnostic::new(
                argument.span,
                "'Self' cannot appear in a trait's specialization arguments; write a concrete impl target or an impl type parameter",
            ));
        }
    }
    let const_binders = generics
        .iter()
        .filter(|generic| is_const_generic(resolution, generic))
        .filter_map(|generic| resolution.binder(generic.span))
        .collect::<BTreeSet<_>>();
    validate_impl_pattern(
        resolution,
        types,
        self_ty,
        &generic_ids,
        &const_binders,
        "self type",
    )?;
    for argument in &trait_argument_ast {
        validate_impl_pattern(
            resolution,
            types,
            argument,
            &generic_ids,
            &const_binders,
            "trait argument",
        )?;
    }
    // Every declared parameter must be determined by the self type or the
    // trait arguments. An unconstrained parameter would make dispatch choose
    // an arbitrary representative and silently make coherence order-dependent.
    for generic in generics {
        let binder = resolution
            .binder(generic.span)
            .expect("impl parameter has a binder");
        let mut used = type_references_any_binder(resolution, self_ty, &BTreeSet::from([binder]));
        for argument in &trait_argument_ast {
            used |= type_references_any_binder(resolution, argument, &BTreeSet::from([binder]));
        }
        if !used {
            return Err(Diagnostic::new(
                generic.span,
                format!(
                    "impl parameter '{}' is unconstrained: it does not appear in the self type or trait arguments, so dispatch cannot solve it uniquely",
                    generic.name
                ),
            ));
        }
    }
    if trait_id.is_none()
        && !matches!(
            &self_ty.kind,
            ast::TypeKind::Named { path, .. }
                if path.len() == 1
                    && resolution
                        .reference(self_ty.span)
                        .is_some_and(|id| resolution.bindings[id].kind == BindingKind::Data)
        )
        && !matches!(&self_ty.kind, ast::TypeKind::Named { .. })
    {
        return Err(Diagnostic::new(
            self_ty.span,
            "an inherent generic impl must target a nominal record or enum pattern",
        ));
    }
    let mut impl_associated = ImplAssociated::default();
    let mut provided = BTreeSet::new();
    for item in associated {
        match item {
            ast::Associated::Type { name, value, span } => {
                let Some(value) = value else {
                    return Err(Diagnostic::new(
                        *span,
                        "an associated type in an impl requires a value: 'type Name = Type;'",
                    ));
                };
                if trait_id.is_some()
                    && !matches!(
                        trait_associated.get(name),
                        Some(TraitAssociated::Type { .. })
                    )
                {
                    return Err(Diagnostic::new(
                        *span,
                        format!(
                            "associated type '{name}' is not declared by the implemented trait"
                        ),
                    ));
                }
                if trait_id.is_none() {
                    return Err(Diagnostic::new(
                        *span,
                        "inherent impls define associated constants only; associated types require a trait declaration",
                    ));
                }
                if !provided.insert(name.clone()) {
                    return Err(Diagnostic::new(
                        *span,
                        format!("duplicate item '{name}' in one impl"),
                    ));
                }
                impl_associated.types.insert(name.clone(), value.clone());
            }
            ast::Associated::Const {
                name,
                ty,
                value,
                span,
            } => {
                if type_mentions_self(ty) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "an associated constant's type may not mention 'Self'; write a concrete scalar type",
                    ));
                }
                if type_references_any_binder(resolution, ty, &generic_ids) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "an associated constant type in a generic impl may not depend on the impl's type parameters",
                    ));
                }
                let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                if !const_scalar_type(types, lowered) {
                    return Err(Diagnostic::new(
                        ty.span,
                        "associated constants must have a compile-time scalar, tuple, or inline-array type; scalar types are i8/i16/i32/i64/u8/u16/u32/u64, Bool, or Char",
                    ));
                }
                if trait_id.is_some()
                    && !matches!(
                        trait_associated.get(name),
                        Some(TraitAssociated::Const { .. })
                    )
                {
                    return Err(Diagnostic::new(
                        *span,
                        format!(
                            "associated constant '{name}' is not declared by the implemented trait"
                        ),
                    ));
                }
                if !provided.insert(name.clone()) {
                    return Err(Diagnostic::new(
                        *span,
                        format!("duplicate item '{name}' in one impl"),
                    ));
                }
                if let Some(declared) = trait_associated.get(name)
                    && let TraitAssociated::Const { ty: declared, .. } = declared
                {
                    let declared =
                        types.ty_in(declared, &crate::runtime_types::Subst::default())?;
                    if declared != lowered {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "associated constant '{name}' must have the declared type {}",
                                types.name(declared)
                            ),
                        ));
                    }
                }
                let Some(value) = value else {
                    continue;
                };
                if expression_mentions_generic(resolution, value, &generic_ids) {
                    return Err(Diagnostic::new(
                        value.span,
                        "an associated constant value in a generic impl may not depend on the impl's type parameters",
                    ));
                }
                let checked =
                    evaluate_associated_const(types, value, lowered, &impl_associated.consts)?;
                impl_associated.consts.insert(name.clone(), checked);
            }
        }
    }
    if let Some(trait_id) = trait_id {
        let associated_order = trait_definition
            .as_ref()
            .map(|definition| definition.associated_order.clone())
            .unwrap_or_default();
        for name in &associated_order {
            let Some(item) = trait_associated.get(name) else {
                continue;
            };
            match item {
                TraitAssociated::Type { default } => {
                    if !impl_associated.types.contains_key(name) {
                        let Some(default) = default else {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "missing associated type '{name}' for trait '{}' on this impl",
                                    resolution.bindings[trait_id].name
                                ),
                            ));
                        };
                        impl_associated.types.insert(name.clone(), default.clone());
                    }
                }
                TraitAssociated::Const { ty, default } => {
                    if impl_associated.consts.contains_key(name) {
                        continue;
                    }
                    let Some(default) = default else {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "missing associated constant '{name}' for trait '{}'",
                                resolution.bindings[trait_id].name
                            ),
                        ));
                    };
                    let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                    let checked = evaluate_associated_const(
                        types,
                        default,
                        lowered,
                        &impl_associated.consts,
                    )?;
                    impl_associated.consts.insert(name.clone(), checked);
                }
            }
        }
    }
    let associated_index =
        (!impl_associated.types.is_empty() || !impl_associated.consts.is_empty()).then(|| {
            functions.impl_associated.push(impl_associated.clone());
            functions.impl_associated.len() - 1
        });
    let header_index = functions.impl_headers.len();
    functions.impl_headers.push(ImplHeader {
        trait_id,
        generics: generics.to_vec(),
        self_ty: self_ty.clone(),
        trait_arguments: trait_argument_ast.clone(),
        associated: impl_associated.clone(),
        methods: BTreeMap::new(),
        span,
        concrete: None,
    });
    let trait_argument_names = trait_generics
        .iter()
        .zip(&trait_argument_ast)
        .map(|(generic, argument)| (generic.name.clone(), argument.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut definitions = BTreeMap::new();
    let mut bindings = Vec::new();
    for method in methods {
        let f = &method.function;
        if f.total {
            return Err(Diagnostic::new(
                method.span,
                "impl methods are executable declarations and cannot be 'total'",
            ));
        }
        if let Some(collision) = f.generics.iter().find(|generic| {
            generics
                .iter()
                .any(|impl_generic| impl_generic.name == generic.name)
        }) {
            return Err(Diagnostic::new(
                collision.span,
                format!(
                    "method parameter '{}' must be distinct from the impl's parameters to avoid capture; rename one of them",
                    collision.name
                ),
            ));
        }
        let Some(receiver) = f.parameters.first() else {
            return Err(Diagnostic::new(
                method.span,
                "a method must declare a receiver as its first parameter: 'self: Self' or 'self: &Self'",
            ));
        };
        if receiver.erased || receiver.name != "self" {
            return Err(Diagnostic::new(
                receiver.span,
                "the first method parameter must be the receiver, written 'self: Self', 'self: &Self', 'self: &mut Self', or the concrete target type",
            ));
        }
        checked_generic_method_receiver(types, &receiver.ty, self_ty, &generic_ids, resolution)?;
        if Checker::builtin_method(&f.name) {
            return Err(Diagnostic::new(
                method.span,
                format!(
                    "method '{}' uses a reserved builtin method name; builtin receiver methods take precedence, so choose another name",
                    f.name
                ),
            ));
        }
        if trait_id.is_some() {
            let Some(expected) = trait_methods.get(&f.name) else {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' is not declared by the implemented trait",
                        f.name
                    ),
                ));
            };
            if method_contract_key(
                resolution,
                expected.function,
                Some(self_ty),
                Some(&trait_argument_names),
                Some(&impl_associated.types),
            )? != method_contract_key(
                resolution,
                f,
                Some(self_ty),
                None,
                Some(&impl_associated.types),
            )? {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' does not match the trait signature exactly; parameters, parameter grades, erasure markers, result type, generic parameters and bounds, effect exclusions, lifetimes, effects, and substituted trait arguments must match",
                        f.name
                    ),
                ));
            }
        }
        for parameter in &f.parameters {
            if parameter.erased && type_mentions_self(&parameter.ty) {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "erased method parameters may not mention 'Self' in this subset",
                ));
            }
        }
        validate_erased_parameters(resolution, logical, f)?;
        validate_length_templates(resolution, f)?;
        let binding = resolution.method(method.span).ok_or_else(|| {
            Diagnostic::new(method.span, "internal error: impl method has no binding")
        })?;
        let definition = MethodDefinition {
            binding,
            public: method.public,
            unit: resolution.unit_of.get(&binding).copied().unwrap_or(0),
            impl_arguments: None,
        };
        if definitions.insert(f.name.clone(), definition).is_some() {
            return Err(Diagnostic::new(
                method.span,
                format!("duplicate method '{}' in one impl", f.name),
            ));
        }
        functions.declared.insert(
            binding,
            Declared {
                ast: f,
                span: method.span,
                self_ty: None,
                default_specialization: None,
                impl_associated: associated_index,
                impl_template: Some(header_index),
            },
        );
        bindings.push(binding);
    }
    if let Some(trait_id) = trait_id {
        let trait_public = resolution.public.contains(&trait_id);
        let impl_unit = resolution.item_units.get(&span.start).copied().unwrap_or(0);
        for (name, method) in &trait_methods {
            if definitions.contains_key(name) {
                continue;
            }
            if method.function.body.is_none() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "missing implementation of trait method '{name}' for {}",
                        type_key(self_ty)
                    ),
                ));
            }
            let receiver = method
                .function
                .parameters
                .first()
                .expect("trait receiver was validated at declaration");
            checked_generic_method_receiver(
                types,
                &receiver.ty,
                self_ty,
                &generic_ids,
                resolution,
            )?;
            let binding = *default_bindings
                .get(&(span.start, name.clone()))
                .ok_or_else(|| {
                    Diagnostic::new(
                        method.span,
                        "internal error: inherited default method has no binding",
                    )
                })?;
            let index = functions.default_specializations.len();
            functions
                .default_specializations
                .push((trait_id, TraitArguments::default()));
            functions.declared.insert(
                binding,
                Declared {
                    ast: method.function,
                    span: method.span,
                    self_ty: None,
                    default_specialization: Some(index),
                    impl_associated: associated_index,
                    impl_template: Some(header_index),
                },
            );
            definitions.insert(
                name.clone(),
                MethodDefinition {
                    binding,
                    public: trait_public,
                    unit: impl_unit,
                    impl_arguments: None,
                },
            );
            bindings.push(binding);
        }
    }
    functions.impl_headers[header_index].methods = definitions;
    Ok(bindings)
}
/// Whether a type expression mentions any of the given generic binders.
fn type_references_any_binder(
    resolution: &Resolution,
    ty: &ast::Type,
    binders: &BTreeSet<BindingId>,
) -> bool {
    let mentions = |ty: &ast::Type| type_references_any_binder(resolution, ty, binders);
    match &ty.kind {
        ast::TypeKind::Named { arguments, .. } => {
            resolution
                .reference(ty.span)
                .is_some_and(|id| binders.contains(&id))
                || arguments.iter().any(mentions)
        }
        ast::TypeKind::Tuple(items) => items.iter().any(mentions),
        ast::TypeKind::Slice(inner) | ast::TypeKind::Graded { inner, .. } => mentions(inner),
        ast::TypeKind::Borrow { inner, .. } => mentions(inner),
        ast::TypeKind::Array(inner, length) => mentions(inner) || mentions(length),
        ast::TypeKind::Binary { left, right, .. } => mentions(left) || mentions(right),
        ast::TypeKind::Function {
            parameters, result, ..
        } => parameters.iter().any(|parameter| mentions(&parameter.ty)) || mentions(result),
        _ => false,
    }
}
/// Whether an expression mentions any of the given generic binders. Used to
/// reject associated-constant values that would require generic const
/// evaluation, which is not part of this subset.
fn expression_mentions_generic(
    resolution: &Resolution,
    expr: &ast::Expr,
    binders: &BTreeSet<BindingId>,
) -> bool {
    match &expr.kind {
        ast::ExprKind::Name(_) | ast::ExprKind::Field { .. } => resolution
            .reference(expr.span)
            .is_some_and(|id| binders.contains(&id)),
        _ => false,
    }
}
/// Validate a method receiver written against a generic impl header. The
/// receiver must be `Self`/the concrete pattern by value or a shared/exclusive
/// nominal-record borrow of it.
fn checked_generic_method_receiver(
    types: &mut Types<'_>,
    receiver: &ast::Type,
    self_ty: &ast::Type,
    generics: &BTreeSet<BindingId>,
    resolution: &Resolution,
) -> Result<()> {
    let shape = match &receiver.kind {
        ast::TypeKind::SelfType => return Ok(()),
        ast::TypeKind::Borrow { inner, .. } => {
            if !matches!(inner.kind, ast::TypeKind::SelfType) {
                return Err(Diagnostic::new(
                    receiver.span,
                    "a generic impl receiver may borrow only 'Self' (write 'self: &Self' or '&self')",
                ));
            }
            true
        }
        ast::TypeKind::Named { .. } => {
            // The concrete pattern itself is accepted when it is syntactically
            // the header self type.
            if type_key(receiver) == type_key(self_ty) {
                return Ok(());
            }
            return Err(Diagnostic::new(
                receiver.span,
                "a generic impl receiver must be written 'self: Self', 'self: &Self', or 'self: &mut Self'",
            ));
        }
        _ => {
            return Err(Diagnostic::new(
                receiver.span,
                "a generic impl receiver must be written 'self: Self', 'self: &Self', or 'self: &mut Self'",
            ));
        }
    };
    let _ = (types, generics, resolution, shape);
    Ok(())
}

/// The receiver mode of a trait method declaration. Dynamic dispatch mirrors
/// the three statically checked modes, but mutable dispatch additionally writes
/// the updated object back to the caller's local.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReceiverMode {
    Owned,
    Shared,
    Mutable,
}
fn trait_receiver_mode(method: &ast::Function) -> ReceiverMode {
    match method
        .parameters
        .first()
        .map(|parameter| &parameter.ty.kind)
    {
        Some(ast::TypeKind::Borrow { mutable: true, .. }) => ReceiverMode::Mutable,
        Some(ast::TypeKind::Borrow { mutable: false, .. }) => ReceiverMode::Shared,
        _ => ReceiverMode::Owned,
    }
}

impl<'a> Functions<'a> {
    /// The concrete self type of a method instance, if it belongs to an impl.
    fn self_type_for(&self, binding: BindingId, impl_arguments: Option<usize>) -> Option<Type> {
        if let Some(index) = impl_arguments {
            return Some(self.impl_instantiations[index].self_type);
        }
        self.declared
            .get(&binding)
            .and_then(|declared| declared.self_ty)
    }
    /// The concrete trait specialization of a method instance. Concrete impl
    /// methods and inherited defaults derive it from the impl registration;
    /// generic impls derive it from the selected instantiation.
    fn trait_arguments_for(
        &self,
        binding: BindingId,
        impl_arguments: Option<usize>,
    ) -> Option<TraitArguments> {
        if let Some(index) = impl_arguments {
            return Some(self.impl_instantiations[index].trait_arguments.clone());
        }
        let declared = self.declared.get(&binding)?;
        let index = declared.default_specialization?;
        Some(self.default_specializations[index].1.clone())
    }
    /// Intern one concrete instantiation of a generic impl header and compute
    /// its receiver type and trait specialization. Deduplicated so each method
    /// body is checked once per impl-argument list.
    fn intern_impl(
        &mut self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        header: usize,
        arguments: ImplArguments,
    ) -> Result<usize> {
        if let Some(index) = self
            .impl_instantiation_cache
            .get(&(header, arguments.clone()))
        {
            return Ok(*index);
        }
        let definition = self.impl_headers[header].clone();
        let substitution = impl_arguments_subst(resolution, &definition.generics, &arguments);
        let self_type = types.ty_in(&definition.self_ty, &substitution)?;
        let trait_arguments = match definition.trait_id {
            Some(trait_id) => {
                let generics = self.traits[&trait_id].generics.clone();
                evaluate_trait_arguments(
                    types,
                    resolution,
                    self.logical,
                    &generics,
                    &definition.trait_arguments,
                    &substitution,
                    &resolution.bindings[trait_id].name,
                    definition.span,
                )?
            }
            None => TraitArguments::default(),
        };
        let index = self.impl_instantiations.len();
        self.impl_instantiations.push(ImplInstantiation {
            header,
            arguments: arguments.clone(),
            self_type,
            trait_arguments,
        });
        self.impl_instantiation_cache
            .insert((header, arguments), index);
        Ok(index)
    }
    /// Whether a trait obligation is met by an exact concrete impl or by at
    /// least one applicable generic impl. Used for impl-header bounds and
    /// bounded-generic discharge.
    fn obligation_holds(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        trait_id: BindingId,
        required: &TraitArguments,
        self_ty: Type,
        depth: usize,
    ) -> Result<bool> {
        if self
            .trait_impls
            .contains_key(&(trait_id, required.clone(), self_ty))
        {
            return Ok(true);
        }
        if depth >= 8 {
            return Ok(false);
        }
        Ok(!self
            .matching_impls(types, resolution, trait_id, required, self_ty, depth + 1)?
            .is_empty())
    }
    /// All generic impls of `trait_id` whose header pattern matches the
    /// concrete receiver and trait arguments, with their generic parameters
    /// solved. Declaration-time coherence guarantees that any two matches are
    /// specialization-comparable; dispatch still checks for a unique most
    /// specific match.
    fn matching_impls(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        trait_id: BindingId,
        required: &TraitArguments,
        self_ty: Type,
        depth: usize,
    ) -> Result<Vec<ImplMatch>> {
        if depth >= 8 {
            return Ok(Vec::new());
        }
        let definition = self.traits[&trait_id].clone();
        let mut out = Vec::new();
        for (index, header) in self.impl_headers.iter().enumerate() {
            if header.trait_id != Some(trait_id) || header.concrete.is_some() {
                continue;
            }
            let mut bindings = PatternBindings::default();
            if !match_type_pattern(
                resolution,
                types,
                &header.self_ty,
                self_ty,
                &mut bindings,
                0,
            )? {
                continue;
            }
            if !match_trait_argument_patterns(
                resolution,
                types,
                self.logical,
                &definition.generics,
                &header.trait_arguments,
                required,
                &mut bindings,
            )? {
                continue;
            }
            let solved = solved_impl_arguments(resolution, &header.generics, &bindings);
            let mut bounds_hold = true;
            for generic in &header.generics {
                let Some(bound) = &generic.bound else {
                    continue;
                };
                let Some(bound_trait) = resolution.reference(bound.span) else {
                    continue;
                };
                if resolution.bindings[bound_trait].kind != BindingKind::Trait {
                    continue;
                }
                let argument_ast = match &bound.kind {
                    ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                    _ => Vec::new(),
                };
                let bound_generics = self.traits[&bound_trait].generics.clone();
                let subst = bindings.subst();
                let required_bound = evaluate_trait_arguments(
                    types,
                    resolution,
                    self.logical,
                    &bound_generics,
                    &argument_ast,
                    &subst,
                    &resolution.bindings[bound_trait].name,
                    generic.span,
                )?;
                let actual = bindings
                    .types
                    .get(&resolution.binder(generic.span).unwrap())
                    .copied()
                    .expect("matched header parameter is solved");
                if !self.obligation_holds(
                    types,
                    resolution,
                    bound_trait,
                    &required_bound,
                    actual,
                    depth + 1,
                )? {
                    bounds_hold = false;
                    break;
                }
            }
            if bounds_hold {
                out.push(ImplMatch {
                    header: index,
                    arguments: solved,
                });
            }
        }
        Ok(out)
    }
    /// Match only the self-type pattern of an impl header against a concrete
    /// receiver. Used by unqualified dispatch, which must discover every trait
    /// that could provide a name before selecting a specialization.
    fn match_header_for_receiver(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        header_index: usize,
        self_ty: Type,
        depth: usize,
    ) -> Result<Option<ImplMatch>> {
        let header = self.impl_headers[header_index].clone();
        if header.concrete.is_some() {
            return Ok(None);
        }
        let mut bindings = PatternBindings::default();
        if !match_type_pattern(
            resolution,
            types,
            &header.self_ty,
            self_ty,
            &mut bindings,
            0,
        )? {
            return Ok(None);
        }
        // Unqualified dispatch sees only the receiver. A parameter determined
        // solely by a trait argument cannot be solved here; returning `None`
        // leaves the call to explicit qualification instead of instantiating an
        // arbitrary representative.
        for generic in &header.generics {
            let binder = resolution.binder(generic.span).unwrap();
            let solved = match generic_category(resolution, generic) {
                GenericCategory::Type => bindings.types.contains_key(&binder),
                GenericCategory::Const => bindings.consts.contains_key(&binder),
                GenericCategory::Grade => bindings.grades.contains_key(&binder),
                GenericCategory::Effect => bindings.effects.contains_key(&binder),
            };
            if !solved {
                return Ok(None);
            }
        }
        let arguments = solved_impl_arguments(resolution, &header.generics, &bindings);
        for generic in &header.generics {
            let Some(bound) = &generic.bound else {
                continue;
            };
            let Some(bound_trait) = resolution.reference(bound.span) else {
                continue;
            };
            if resolution.bindings[bound_trait].kind != BindingKind::Trait {
                continue;
            }
            let argument_ast = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                _ => Vec::new(),
            };
            let bound_generics = self.traits[&bound_trait].generics.clone();
            let subst = bindings.subst();
            let required = evaluate_trait_arguments(
                types,
                resolution,
                self.logical,
                &bound_generics,
                &argument_ast,
                &subst,
                &resolution.bindings[bound_trait].name,
                generic.span,
            )?;
            let actual = bindings
                .types
                .get(&resolution.binder(generic.span).unwrap())
                .copied()
                .expect("matched header parameter is solved");
            if !self.obligation_holds(
                types,
                resolution,
                bound_trait,
                &required,
                actual,
                depth + 1,
            )? {
                return Ok(None);
            }
        }
        Ok(Some(ImplMatch {
            header: header_index,
            arguments,
        }))
    }
    /// The concrete trait specialization produced by one solved impl header.
    fn trait_arguments_for_match(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        header_index: usize,
        arguments: &ImplArguments,
    ) -> Result<TraitArguments> {
        let header = self.impl_headers[header_index].clone();
        let Some(trait_id) = header.trait_id else {
            return Ok(TraitArguments::default());
        };
        if let Some(index) = self
            .impl_instantiation_cache
            .get(&(header_index, arguments.clone()))
        {
            return Ok(self.impl_instantiations[*index].trait_arguments.clone());
        }
        let subst = impl_arguments_subst(resolution, &header.generics, arguments);
        // The trait arguments may themselves mention impl type parameters; the
        // substitution above already covers every category.
        let generics = self.traits[&trait_id].generics.clone();
        evaluate_trait_arguments(
            types,
            resolution,
            self.logical,
            &generics,
            &header.trait_arguments,
            &subst,
            &resolution.bindings[trait_id].name,
            header.span,
        )
    }
    /// Pick the unique most-specific match. Coherence has already rejected
    /// incomparable overlaps; a remaining tie is an internal ambiguity error
    /// rather than an arbitrary declaration-order choice.
    fn select_most_specific(
        &self,
        resolution: &Resolution,
        matches: &[ImplMatch],
    ) -> Option<ImplMatch> {
        if matches.len() == 1 {
            return matches.first().cloned();
        }
        let mut candidates = Vec::new();
        for candidate in matches {
            let mut dominated = false;
            for other in matches {
                if candidate.header == other.header && candidate.arguments == other.arguments {
                    continue;
                }
                let a = &self.impl_headers[candidate.header];
                let b = &self.impl_headers[other.header];
                if header_subsumes(resolution, a, b) && !header_subsumes(resolution, b, a) {
                    // The other header is more specific.
                    dominated = true;
                    break;
                }
            }
            if !dominated {
                candidates.push(candidate.clone());
            }
        }
        (candidates.len() == 1).then(|| candidates.remove(0))
    }

    /// A fresh, unspellable identity for one elided input borrow. Every elided
    /// input gets its own identity, so independent inputs never collapse into a
    /// single inferred lifetime.
    fn fresh_elided_lifetime(&mut self) -> String {
        let index = self.elided_lifetimes;
        self.elided_lifetimes += 1;
        format!("<elided lifetime {index}>")
    }
    /// The proposition of an erased parameter, over earlier runtime parameters.
    fn proposition(
        &self,
        resolution: &Resolution,
        parameter: &ast::Parameter,
    ) -> Result<crate::facts::Proposition> {
        let f = self
            .declared
            .values()
            .find(|d| d.ast.parameters.iter().any(|p| std::ptr::eq(p, parameter)))
            .map(|d| d.ast)
            .expect("parameter of a declared function");
        proposition_of(resolution, f, parameter)
    }
    /// Find or create the instance of `binding` for a concrete list of type,
    /// grade, and compile-time natural arguments. New instances are queued for
    /// body checking.
    #[allow(clippy::too_many_arguments)]
    fn instance(
        &mut self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        binding: BindingId,
        type_arguments: Vec<Type>,
        grade_arguments: Vec<Grade>,
        const_arguments: Vec<usize>,
        effect_arguments: Vec<u8>,
        impl_arguments: Option<usize>,
        origin: Option<Span>,
    ) -> Result<usize> {
        let key = (
            binding,
            type_arguments,
            grade_arguments,
            const_arguments,
            effect_arguments,
            impl_arguments,
        );
        if let Some(index) = self.instances.get(&key) {
            return Ok(*index);
        }
        let declared = self.declared[&binding];
        let f = declared.ast;
        if self.signatures.len() >= MAX_FUNCTIONS {
            return Err(Diagnostic::new(
                origin.unwrap_or(declared.span),
                "executable limit exceeded (256 function instances); polymorphic recursion cannot be specialized",
            ));
        }
        let mut type_generics = Vec::new();
        let mut grade_generics = Vec::new();
        let mut const_generics = Vec::new();
        let mut effect_generics = Vec::new();
        for generic in &f.generics {
            if is_grade_generic(resolution, generic) {
                grade_generics.push(generic);
            } else if is_const_generic(resolution, generic) {
                const_generics.push(generic);
            } else if crate::runtime_types::is_effect_generic(resolution, generic) {
                effect_generics.push(generic);
            } else {
                type_generics.push(generic);
            }
        }
        if type_generics.len() != key.1.len()
            || grade_generics.len() != key.2.len()
            || const_generics.len() != key.3.len()
            || effect_generics.len() != key.4.len()
        {
            return Err(Diagnostic::new(
                origin.unwrap_or(declared.span),
                "internal error: generic specialization argument count does not match its category",
            ));
        }
        // Every explicit, inferred, or forwarded effect argument reaches this
        // single specialization point, including arguments for methods and
        // materialized trait defaults. A bounded binder `<e: Effects - ...>`
        // restricts which concrete rows are valid, and `<e: Effects + ...>`
        // requires bits in every specialization; neither hides or subtracts an
        // effect from the declaration's own row.
        for (generic, effects) in effect_generics.iter().zip(&key.4) {
            let excluded = crate::runtime_types::effect_excludes(resolution, generic)?.unwrap_or(0);
            let illegal = effects & excluded;
            if illegal != 0 {
                return Err(Diagnostic::new(
                    origin.unwrap_or(generic.span),
                    format!(
                        "effect argument {{{}}} for '{}' includes {}, which is excluded by '<{}: Effects - {}>'",
                        effect_names(*effects),
                        generic.name,
                        effect_names(illegal),
                        generic.name,
                        effect_names(excluded)
                    ),
                ));
            }
            let included = crate::runtime_types::effect_includes(resolution, generic)?.unwrap_or(0);
            let missing = included & !effects;
            if missing != 0 {
                return Err(Diagnostic::new(
                    origin.unwrap_or(generic.span),
                    format!(
                        "effect argument {{{}}} for '{}' omits {}, which is required by '<{}: Effects + {}>'",
                        effect_names(*effects),
                        generic.name,
                        effect_names(missing),
                        generic.name,
                        effect_names(included)
                    ),
                ));
            }
        }
        if key
            .1
            .iter()
            .any(|ty| crate::runtime_types::has_borrow(types, *ty))
        {
            return Err(Diagnostic::new(
                origin.unwrap_or(declared.span),
                "a borrowed record cannot be passed through an ordinary generic type parameter; lifetimes are not erased at this boundary",
            ));
        }
        let mut substitution = crate::runtime_types::Subst {
            self_type: declared.self_ty,
            ..Default::default()
        };
        for (g, ty) in type_generics.iter().zip(&key.1) {
            substitution
                .types
                .insert(resolution.binder(g.span).unwrap(), *ty);
        }
        let mut const_substitution = const_generics
            .iter()
            .zip(&key.3)
            .map(|(g, value)| (resolution.binder(g.span).unwrap(), *value))
            .collect::<BTreeMap<_, _>>();
        let mut grade_substitution = grade_generics
            .iter()
            .zip(&key.2)
            .map(|(g, grade)| (resolution.binder(g.span).unwrap(), *grade))
            .collect::<BTreeMap<_, _>>();
        let mut effect_substitution = effect_generics
            .iter()
            .zip(&key.4)
            .map(|(g, effects)| (resolution.binder(g.span).unwrap(), *effects))
            .collect::<BTreeMap<_, _>>();
        // A generic impl supplies concrete values for its own parameters. They
        // join the same substitution maps as the method's generics; the
        // declaration rejects a method binder that reuses an impl parameter
        // name, so the keys cannot collide.
        if let Some(index) = impl_arguments {
            let instantiation = self.impl_instantiations[index].clone();
            let header = self.impl_headers[instantiation.header].clone();
            for (generic, ty) in header.generics.iter().zip(&instantiation.arguments.types) {
                substitution
                    .types
                    .insert(resolution.binder(generic.span).unwrap(), *ty);
            }
        }
        // A materialized trait default also needs its trait's concrete
        // arguments. `Self` is substituted above and trait parameters are
        // ordinary binders, so they join the same substitution maps. Method
        // parameters may not reuse a trait parameter name, so the keys cannot
        // collide.
        if let Some(index) = declared.default_specialization {
            let (trait_id, stored) = self.default_specializations[index].clone();
            let arguments = self
                .trait_arguments_for(binding, impl_arguments)
                .unwrap_or(stored);
            let definition = self.traits[&trait_id].clone();
            insert_trait_arguments(
                resolution,
                &definition.generics,
                &arguments,
                &mut substitution,
                &mut const_substitution,
                &mut grade_substitution,
                &mut effect_substitution,
            );
        }
        substitution.consts = const_substitution.clone();
        substitution.grades = grade_substitution.clone();
        substitution.effects = effect_substitution.clone();
        // Normalize `Self::Item` through this impl's associated values. The
        // value is an AST type, so it is lowered with the same substitution
        // and may mention the impl's generic parameters.
        let mut associated_consts = BTreeMap::new();
        if let Some(index) = declared.impl_associated {
            let associated = self.impl_associated[index].clone();
            substitution.associated_types = associated.types;
            associated_consts = associated.consts;
        }
        // `Self` for a generic impl is its header pattern lowered with the
        // concrete impl arguments selected by dispatch.
        let instantiated_self =
            impl_arguments.map(|index| self.impl_instantiations[index].self_type);
        substitution.self_type = instantiated_self.or(declared.self_ty);
        // Projections in an impl's own associated values may depend on a bound
        // of an impl parameter, as in `impl<T: Show> Wrap for W<T> { type Out =
        // T.Out; }`. Install those projections before lowering signatures.
        if let Some(index) = impl_arguments {
            let instantiation = self.impl_instantiations[index].clone();
            let header = self.impl_headers[instantiation.header].clone();
            for (generic, actual) in header.generics.iter().zip(&instantiation.arguments.types) {
                let Some(bound) = &generic.bound else {
                    continue;
                };
                let Some(trait_id) = resolution.reference(bound.span) else {
                    continue;
                };
                if resolution.bindings[trait_id].kind != BindingKind::Trait {
                    continue;
                }
                let argument_ast = match &bound.kind {
                    ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                    _ => Vec::new(),
                };
                let definition = self.traits[&trait_id].clone();
                let required = evaluate_trait_arguments(
                    types,
                    resolution,
                    self.logical,
                    &definition.generics,
                    &argument_ast,
                    &substitution,
                    &resolution.bindings[trait_id].name,
                    generic.span,
                )?;
                let binder = resolution.binder(generic.span).unwrap();
                if let Some(associated) = self
                    .trait_associated
                    .get(&(trait_id, required.clone(), *actual))
                    .cloned()
                {
                    for (name, value) in associated.types {
                        let lowered = types.ty_in(&value, &substitution)?;
                        substitution.projections.insert((binder, name), lowered);
                    }
                } else if let Some(selected) = self.select_most_specific(
                    resolution,
                    &self.matching_impls(types, resolution, trait_id, &required, *actual, 0)?,
                ) {
                    let selected_header = self.impl_headers[selected.header].clone();
                    let mut impl_substitution = substitution.clone();
                    for (impl_generic, ty) in selected_header
                        .generics
                        .iter()
                        .zip(&selected.arguments.types)
                    {
                        impl_substitution
                            .types
                            .insert(resolution.binder(impl_generic.span).unwrap(), *ty);
                    }
                    for (name, value) in selected_header.associated.types {
                        let lowered = types.ty_in(&value, &impl_substitution)?;
                        substitution.projections.insert((binder, name), lowered);
                    }
                }
            }
        }
        // Trait bounds are discharged at specialization time, before the body
        // is checked. A missing impl is an error even when the body never calls
        // a trait method. Bound arguments are substituted through this
        // instance's generic arguments, so `T: Convert<U>` selects the impl for
        // the concrete `U`.
        for (generic, actual) in type_generics.iter().zip(&key.1) {
            let Some(bound) = &generic.bound else {
                continue;
            };
            let Some(trait_id) = resolution.reference(bound.span) else {
                continue;
            };
            if resolution.bindings[trait_id].kind != BindingKind::Trait {
                continue;
            }
            let bound_arguments = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                _ => Vec::new(),
            };
            let definition = self.traits[&trait_id].clone();
            let required = evaluate_trait_arguments(
                types,
                resolution,
                self.logical,
                &definition.generics,
                &bound_arguments,
                &substitution,
                &resolution.bindings[trait_id].name,
                generic.span,
            )?;
            if !self.obligation_holds(types, resolution, trait_id, &required, *actual, 0)? {
                let trait_name = &resolution.bindings[trait_id].name;
                let specialization = if definition.generics.is_empty() {
                    trait_name.clone()
                } else {
                    format!(
                        "{trait_name}<{}>",
                        trait_specialization_name(
                            resolution,
                            types,
                            &definition.generics,
                            &required
                        )
                    )
                };
                return Err(Diagnostic::new(
                    generic.span,
                    format!(
                        "type '{}' does not implement trait '{specialization}' required by '{}: {}'",
                        types.name(*actual),
                        generic.name,
                        specialization
                    ),
                ));
            }
            let binder = resolution
                .binder(generic.span)
                .expect("generic parameter has a binder");
            if let Some(associated) = self
                .trait_associated
                .get(&(trait_id, required.clone(), *actual))
                .cloned()
            {
                for (name, value) in associated.types {
                    let lowered = types.ty_in(&value, &substitution)?;
                    substitution.projections.insert((binder, name), lowered);
                }
            } else {
                // A generic impl supplies the projection. Solve it and lower
                // the associated value with both the method's and the impl's
                // parameters substituted.
                let matches =
                    self.matching_impls(types, resolution, trait_id, &required, *actual, 0)?;
                if let Some(selected) = self.select_most_specific(resolution, &matches) {
                    let header = self.impl_headers[selected.header].clone();
                    let mut impl_substitution = substitution.clone();
                    for (impl_generic, ty) in header.generics.iter().zip(&selected.arguments.types)
                    {
                        impl_substitution
                            .types
                            .insert(resolution.binder(impl_generic.span).unwrap(), *ty);
                    }
                    for (name, value) in header.associated.types {
                        let lowered = types.ty_in(&value, &impl_substitution)?;
                        substitution.projections.insert((binder, name), lowered);
                    }
                }
            }
        }
        let mut parameters = Vec::new();
        let mut parameter_grades = Vec::new();
        let mut parameter_lifetimes = Vec::new();
        let mut parameter_binder_lifetimes = BTreeMap::new();
        let mut parameter_field_lifetimes: BTreeMap<BindingId, BTreeMap<String, String>> =
            BTreeMap::new();
        let mut declared_lifetimes = BTreeSet::new();
        let mut input_lifetimes: Vec<(String, Span, Option<String>)> = Vec::new();
        for lifetime in &f.lifetimes {
            if !declared_lifetimes.insert(lifetime.name.clone()) {
                return Err(Diagnostic::new(
                    lifetime.span,
                    format!("duplicate lifetime parameter '{}'", lifetime.name),
                ));
            }
            if f.generics
                .iter()
                .any(|generic| generic.name == lifetime.name)
            {
                return Err(Diagnostic::new(
                    lifetime.span,
                    "lifetime parameters must be distinct from type, natural, grade, and effect generics",
                ));
            }
        }
        let lifetime_bounds = build_lifetime_bounds(&f.lifetimes)?;
        for p in f.parameters.iter().filter(|p| !p.erased) {
            let (ty, grade) = split_grade(&p.ty);
            parameters.push(types.ty_in(ty, &substitution)?);
            parameter_grades.push(
                grade
                    .map(|grade| grades::evaluate(resolution, &grade_substitution, grade))
                    .transpose()?,
            );
            let mut used = BTreeSet::new();
            type_lifetimes(ty, &mut used);
            if let Some(unknown) = used.iter().find(|name| !declared_lifetimes.contains(*name)) {
                return Err(Diagnostic::new(
                    p.ty.span,
                    format!(
                        "undeclared lifetime '{unknown}'; declare it in the function's lifetime parameter list"
                    ),
                ));
            }
            let explicit_lifetime = borrow_lifetime(ty);
            let lifetime = match &explicit_lifetime {
                Some(name) => Some(name.clone()),
                None if matches!(&ty.kind, ast::TypeKind::Borrow { .. }) => {
                    // Each elided input borrow is independent. It gets a fresh
                    // internal identity rather than a shared default lifetime.
                    Some(self.fresh_elided_lifetime())
                }
                None => None,
            };
            if let Some(name) = &lifetime
                && !input_lifetimes
                    .iter()
                    .any(|(existing, _, _)| existing == name)
            {
                input_lifetimes.push((name.clone(), p.ty.span, explicit_lifetime));
            }
            parameter_lifetimes.push(lifetime.clone());
            let binder = resolution.binder(p.span);
            if let (Some(binder), Some(name)) = (binder, &lifetime) {
                parameter_binder_lifetimes.insert(binder, name.clone());
            }
            if let Some(binder) = binder {
                let mut fields = BTreeMap::new();
                collect_parameter_field_lifetimes(
                    types,
                    parameters.last().copied().unwrap(),
                    &mut fields,
                );
                if !fields.is_empty() {
                    parameter_field_lifetimes.insert(binder, fields);
                }
            }
            // A by-value borrowed record contributes one candidate per field
            // lifetime, so elided slice results can be inferred from a single
            // record source exactly as from a single slice parameter.
            if crate::runtime_types::is_borrowed_record(types, parameters.last().copied().unwrap())
            {
                let mut record_lifetimes = BTreeSet::new();
                for leaf in
                    crate::runtime_types::borrow_leaves(types, parameters.last().copied().unwrap())
                {
                    if let Some(name) = leaf.lifetime {
                        record_lifetimes.insert(name.clone());
                        if !input_lifetimes
                            .iter()
                            .any(|(existing, _, _)| existing == &name)
                        {
                            input_lifetimes.push((name.clone(), p.ty.span, Some(name)));
                        }
                    }
                }
                if let Some(binder) = binder
                    && record_lifetimes.len() == 1
                    && !parameter_binder_lifetimes.contains_key(&binder)
                {
                    parameter_binder_lifetimes
                        .insert(binder, record_lifetimes.into_iter().next().unwrap());
                }
            }
        }
        let (result_ty, result_grade) =
            result_contract(resolution, types, &grade_substitution, &f.result)?;
        let result = types.ty_in(&result_ty, &substitution)?;
        validate_result_contract(
            result_grade,
            crate::runtime_types::type_owns(&types.enums, &types.unions, result, 0),
            &types.name(result),
            f.result.span,
        )?;
        let mut used = BTreeSet::new();
        type_lifetimes(&f.result, &mut used);
        if let Some(unknown) = used.iter().find(|name| !declared_lifetimes.contains(*name)) {
            return Err(Diagnostic::new(
                f.result.span,
                format!(
                    "undeclared lifetime '{unknown}'; declare it in the function's lifetime parameter list"
                ),
            ));
        }
        // Lifetime analysis intentionally uses the written result type, not the
        // alias-expanded runtime type, so an alias result keeps the existing
        // explicit-lifetime requirement. Result *grades* are separate metadata
        // and are already split above.
        let written_result = split_grade(&f.result).0;
        let explicit_result_lifetime = borrow_lifetime(written_result);
        let result_lifetime = match explicit_result_lifetime {
            Some(lifetime) => Some(lifetime),
            None if (result.is_view() || result.is_ref())
                && matches!(&written_result.kind, ast::TypeKind::Borrow { .. }) =>
            {
                // Conservative elision: infer only when the input side names
                // exactly one distinct borrow lifetime. Independent anonymous
                // inputs stay independent, so their result is ambiguous.
                match input_lifetimes.as_slice() {
                    [] => {
                        return Err(Diagnostic::new(
                            f.result.span,
                            "this borrowed slice result cannot be returned: the function has no borrowed input to infer its lifetime from. Add a borrowed slice parameter or annotate the result explicitly",
                        ));
                    }
                    [(lifetime, _, _)] => Some(lifetime.clone()),
                    candidates => {
                        // More than one input lifetime exists. Infer from the
                        // function body only when every returned value is
                        // syntactically rooted in one parameter lifetime. The
                        // ownership pass still checks that lifetime against
                        // every returned origin, so this seed never widens a
                        // borrow beyond what the body actually returns.
                        let mut returned = Vec::new();
                        if let Some(body) = &f.body {
                            collect_block_returns(body, &mut returned);
                            if let Some(tail) = &body.tail {
                                returned.push(tail);
                            }
                        }
                        let mut body_lifetimes = BTreeSet::new();
                        for value in returned {
                            value_lifetime_candidates(
                                resolution,
                                value,
                                &parameter_binder_lifetimes,
                                &parameter_field_lifetimes,
                                &mut body_lifetimes,
                            );
                        }
                        let inferred = body_lifetimes.iter().cloned().collect::<Vec<_>>();
                        if let [only] = inferred.as_slice() {
                            Some(only.clone())
                        } else {
                            let mut diagnostic = Diagnostic::new(
                                f.result.span,
                                if inferred.is_empty() {
                                    format!(
                                        "cannot infer this borrowed slice result's lifetime: the function has {} distinct input borrow lifetimes and its body does not return one directly. Annotate the returned input and the result with one explicit lifetime, as in 'fn f<'a>(s: &'a [i64]) -> &'a [i64]'",
                                        candidates.len()
                                    )
                                } else {
                                    format!(
                                        "cannot infer this borrowed slice result's lifetime from the function body: return positions mention {} distinct parameter lifetimes. Annotate the returned input and the result with one shared lifetime",
                                        inferred.len()
                                    )
                                },
                            );
                            for (_, span, explicit) in candidates {
                                diagnostic = diagnostic.with_note(
                                    *span,
                                    match explicit {
                                        Some(name) => {
                                            format!(
                                                "candidate input lifetime '{name}' declared here"
                                            )
                                        }
                                        None => "candidate elided input borrow declared here"
                                            .to_string(),
                                    },
                                );
                            }
                            return Err(diagnostic);
                        }
                    }
                }
            }
            None => None,
        };
        if result.is_view() {
            let Some(lifetime) = &result_lifetime else {
                return Err(Diagnostic::new(
                    f.result.span,
                    if result.is_mut_slice() {
                        "a borrowed '&mut [T]' result cannot be returned without an explicit lifetime, as in '-> &'a mut [T]'"
                    } else if result == Type::Str {
                        "a borrowed '&str' result cannot be returned without an explicit lifetime, as in '-> &'a str'"
                    } else {
                        "a borrowed slice result cannot be returned without an explicit lifetime, as in '-> &'a [T]'"
                    },
                ));
            };
            let matching = parameter_lifetimes
                .iter()
                .zip(parameters.iter())
                .filter(|(parameter, ty)| {
                    parameter
                        .as_ref()
                        .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                        || crate::runtime_types::borrow_leaves(types, **ty)
                            .iter()
                            .any(|leaf| {
                                leaf.lifetime
                                    .as_ref()
                                    .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                            })
                })
                .collect::<Vec<_>>();
            if matching.is_empty() {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "result lifetime '{lifetime}' does not appear on any parameter that outlives it; a borrowed return must be tied to caller-owned storage. Declare an outlives bound such as 'fn f<'long: 'short, 'short>(s: &'long [i64]) -> &'short [i64]'"
                    ),
                ));
            }
            if result.is_mut_slice()
                && !matching.iter().any(|(_, ty)| {
                    ty.is_mut_slice()
                        || crate::runtime_types::borrow_leaves(types, **ty)
                            .iter()
                            .any(|leaf| {
                                leaf.mutable
                                    && leaf.lifetime.as_ref().is_some_and(|name| {
                                        outlives(&lifetime_bounds, name, lifetime)
                                    })
                            })
                })
            {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "an exclusive '&mut [T]' result lifetime '{lifetime}' must appear on an exclusive '&mut [T]' parameter that outlives it; shared storage cannot be returned mutably"
                    ),
                ));
            }
        } else if result.is_ref() {
            let pointee = result.ref_pointee().expect("reference pointee");
            // A returned reference must name the caller-owned storage of a
            // matching reference parameter. Nominal records, Box, Vec, Bytes,
            // and String all have stable caller-owned storage when reached
            // through such a parameter; a reference to a by-value parameter or
            // a local remains a dangling-borrow error in the ownership pass.
            let result_pointee = types.pointees[pointee].full();
            let Some(lifetime) = &result_lifetime else {
                return Err(Diagnostic::new(
                    f.result.span,
                    "a borrowed reference result requires a declared result lifetime, as in '-> &'a Record' or '-> &'a mut Record'",
                ));
            };
            let matching = parameter_lifetimes
                .iter()
                .zip(parameters.iter())
                .filter(|(parameter, ty)| {
                    ty.is_ref()
                        && ty
                            .ref_pointee()
                            .is_some_and(|p| types.pointees[p].full() == result_pointee)
                        && parameter
                            .as_ref()
                            .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                })
                .collect::<Vec<_>>();
            // A reference element stored in a by-value container parameter is
            // backed by caller-owned storage too; its declared element
            // lifetime supplies the same outlives relation.
            let container_leaf = parameters.iter().any(|ty| {
                crate::runtime_types::borrow_leaves(types, *ty)
                    .iter()
                    .any(|leaf| {
                        leaf.lifetime
                            .as_ref()
                            .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                    })
            });
            if matching.is_empty() && !container_leaf {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "reference result lifetime '{lifetime}' does not appear on any reference parameter to the same '{}' pointee that outlives it; a returned reference must borrow caller-owned storage",
                        types.name(result_pointee)
                    ),
                ));
            }
            if matches!(result, Type::RefMut(_))
                && !matching.iter().any(|(_, ty)| matches!(ty, Type::RefMut(_)))
                && !parameters.iter().any(|ty| {
                    crate::runtime_types::borrow_leaves(types, *ty)
                        .iter()
                        .any(|leaf| {
                            leaf.mutable
                                && leaf
                                    .lifetime
                                    .as_ref()
                                    .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                        })
                })
            {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "an exclusive '&mut {}' result lifetime '{lifetime}' must appear on an exclusive '&mut' parameter to the same pointee that outlives it; shared storage cannot be returned mutably",
                        types.name(result_pointee)
                    ),
                ));
            }
        } else if result
            .layout()
            .is_some_and(|layout| types.enums[layout].borrowed)
            || crate::runtime_types::is_reference_container(types, result)
        {
            // A returned borrowed record may mention only declared lifetime
            // parameters that also describe some parameter's borrowed field.
            for leaf in crate::runtime_types::borrow_leaves(types, result) {
                let Some(lifetime) = &leaf.lifetime else {
                    return Err(Diagnostic::new(
                        f.result.span,
                        "internal error: borrowed record result leaf has no declared field lifetime",
                    ));
                };
                if !declared_lifetimes.contains(lifetime) {
                    return Err(Diagnostic::new(
                        f.result.span,
                        format!(
                            "undeclared lifetime '{lifetime}' in a borrowed record result; declare it in the function's lifetime parameter list"
                        ),
                    ));
                }
                let carried =
                    parameter_lifetimes
                        .iter()
                        .zip(parameters.iter())
                        .any(|(parameter, ty)| {
                            (parameter
                                .as_ref()
                                .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                                && (!leaf.mutable
                                    || ty.is_mut_slice()
                                    || matches!(ty, Type::RefMut(_))))
                                || crate::runtime_types::borrow_leaves(types, *ty).iter().any(
                                    |parameter_leaf| {
                                        parameter_leaf.lifetime.as_ref().is_some_and(|name| {
                                            outlives(&lifetime_bounds, name, lifetime)
                                        }) && (!leaf.mutable || parameter_leaf.mutable)
                                    },
                                )
                        });
                if !carried {
                    return Err(Diagnostic::new(
                        f.result.span,
                        if leaf.mutable {
                            format!(
                                "exclusive borrowed record result lifetime '{lifetime}' does not appear on an exclusive '&mut [T]' parameter or mutable record-field parameter that outlives it; a returned mutable field must borrow caller-owned exclusive storage"
                            )
                        } else {
                            format!(
                                "borrowed record result lifetime '{lifetime}' does not appear on any parameter that outlives it; a returned record must borrow caller-owned storage"
                            )
                        },
                    ));
                }
            }
        }
        if crate::runtime_types::contains_task(types, result) {
            return Err(Diagnostic::new(
                f.result.span,
                "a function cannot return a task handle; a child handle must not escape its scope",
            ));
        }
        if parameters.iter().map(|ty| types.width(*ty)).sum::<usize>() > 128 {
            return Err(Diagnostic::new(
                declared.span,
                "function parameters exceed the 128-word ABI limit",
            ));
        }
        let specialized =
            !key.1.is_empty() || !key.2.is_empty() || !key.3.is_empty() || !key.4.is_empty();
        let name = if !specialized {
            f.name.clone()
        } else {
            let mut type_values = key.1.iter();
            let mut grade_values = key.2.iter();
            let mut const_values = key.3.iter();
            let mut effect_values = key.4.iter();
            let arguments = f
                .generics
                .iter()
                .filter_map(|generic| {
                    if is_grade_generic(resolution, generic) {
                        grade_values.next().map(|grade| grade.to_string())
                    } else if is_const_generic(resolution, generic) {
                        const_values.next().map(|value| value.to_string())
                    } else if crate::runtime_types::is_effect_generic(resolution, generic) {
                        effect_values.next().map(|effects| {
                            let names = [
                                (PANIC, "panic"),
                                (IO, "io"),
                                (ALLOC, "alloc"),
                                (SUSPEND, "suspend"),
                            ]
                            .into_iter()
                            .filter_map(|(bit, name)| (*effects & bit != 0).then_some(name))
                            .collect::<Vec<_>>();
                            format!("{{{}}}", names.join(", "))
                        })
                    } else {
                        type_values.next().map(|ty| types.name(*ty))
                    }
                })
                .collect::<Vec<_>>();
            format!("{}::<{}>", f.name, arguments.join(", "))
        };
        let effects =
            crate::runtime_types::effect_bits_with(resolution, &f.effects, &effect_substitution)?;
        let default_trait = declared
            .default_specialization
            .map(|index| self.default_specializations[index].clone());
        let index = self.signatures.len();
        self.signatures.push(Signature {
            binding,
            origin: origin
                .filter(|_| specialized)
                .map(|span| (span, format!("'{name}'"))),
            name,
            parameters,
            result,
            effects,
            span: declared.span,
            substitution: substitution.types,
            consts: const_substitution,
            grades: grade_substitution,
            effect_arguments: effect_substitution,
            parameter_grades,
            result_grade,
            parameter_lifetimes,
            result_lifetime,
            lifetime_bounds,
            self_type: substitution.self_type,
            default_trait,
            associated_consts,
        });
        self.instances.insert(key, index);
        self.bodies.push(None);
        self.pending.push(index);
        Ok(index)
    }
    /// Register a synthetic, already-checked function body (lambda or adapter).
    /// Synthetic entries share the same index space as declared instances, so
    /// an `FnValue` code pointer stays stable.
    fn add_synthetic(&mut self, signature: Signature, function: Function) -> Result<usize> {
        if self.signatures.len() >= MAX_FUNCTIONS {
            return Err(Diagnostic::new(
                function.span,
                "executable limit exceeded (256 function instances); lambda/adapters require more instances",
            ));
        }
        let index = self.signatures.len();
        self.signatures.push(signature);
        self.bodies.push(Some(function));
        Ok(index)
    }
}

/// Translate `{ a < b && ... }` syntactically. Only earlier runtime parameters,
/// integer constants, `+`/`-` by constants, and `Bytes.len`/`Vec.len` of a
/// parameter may appear.
pub(crate) fn proposition_of(
    resolution: &Resolution,
    f: &ast::Function,
    parameter: &ast::Parameter,
) -> Result<crate::facts::Proposition> {
    use crate::facts::ParamTerm;
    let ast::TypeKind::Predicate(body) = &parameter.ty.kind else {
        return Err(Diagnostic::new(
            parameter.ty.span,
            "erased executable parameters must be propositions written '{ ... }'",
        ));
    };
    let mut indices = BTreeMap::new();
    for p in f.parameters.iter().filter(|p| !p.erased) {
        if std::ptr::eq(p, parameter) {
            break;
        }
        indices.insert(resolution.binder(p.span).unwrap(), indices.len());
    }
    let position = f
        .parameters
        .iter()
        .position(|p| std::ptr::eq(p, parameter))
        .unwrap();
    for p in f.parameters[..position].iter().filter(|p| !p.erased) {
        let _ = p;
    }
    let mut runtime_before = BTreeMap::new();
    for p in f.parameters[..position].iter().filter(|p| !p.erased) {
        runtime_before.insert(resolution.binder(p.span).unwrap(), runtime_before.len());
    }
    let unsupported = |span| {
        Diagnostic::new(
            span,
            "propositions support integer comparisons of earlier parameters, constants, 'x + c', and Bytes.len/Vec.len/Slice.len, joined by '&&'",
        )
    };
    fn text(e: &ast::Expr) -> String {
        match &e.kind {
            ast::ExprKind::Name(n) | ast::ExprKind::Integer(n) => n.clone(),
            ast::ExprKind::Field { value, name } => format!("{}.{name}", text(value)),
            ast::ExprKind::Call { callee, arguments } => format!(
                "{}({})",
                text(callee),
                arguments.iter().map(text).collect::<Vec<_>>().join(", ")
            ),
            ast::ExprKind::Unary { operand, .. } => format!("-{}", text(operand)),
            ast::ExprKind::Binary { op, left, right } => {
                let op = match op {
                    Kind::Lt => "<",
                    Kind::Le => "<=",
                    Kind::Gt => ">",
                    Kind::Ge => ">=",
                    Kind::EqEq => "==",
                    Kind::Plus => "+",
                    Kind::Minus => "-",
                    Kind::AmpAmp => "&&",
                    _ => "?",
                };
                format!("{} {op} {}", text(left), text(right))
            }
            _ => "?".into(),
        }
    }
    let linear = |e: &ast::Expr| -> Result<(ParamTerm, i128)> {
        fn go(
            e: &ast::Expr,
            resolution: &Resolution,
            params: &BTreeMap<BindingId, usize>,
            unsupported: &dyn Fn(Span) -> Diagnostic,
        ) -> Result<(ParamTerm, i128)> {
            match &e.kind {
                ast::ExprKind::Integer(n) => {
                    Ok((ParamTerm::Zero, n.parse().map_err(|_| unsupported(e.span))?))
                }
                ast::ExprKind::Unary {
                    op: Kind::Minus,
                    operand,
                    ..
                } => match go(operand, resolution, params, unsupported)? {
                    (ParamTerm::Zero, n) => Ok((ParamTerm::Zero, -n)),
                    _ => Err(unsupported(e.span)),
                },
                ast::ExprKind::Name(_) => resolution
                    .reference(e.span)
                    .and_then(|id| params.get(&id))
                    .map(|i| (ParamTerm::Param(*i), 0))
                    .ok_or_else(|| {
                        Diagnostic::new(
                            e.span,
                            "a proposition may mention only runtime parameters declared before it",
                        )
                    }),
                ast::ExprKind::Binary {
                    op: op @ (Kind::Plus | Kind::Minus),
                    left,
                    right,
                } => {
                    let l = go(left, resolution, params, unsupported)?;
                    let r = go(right, resolution, params, unsupported)?;
                    let sign = if *op == Kind::Plus { 1 } else { -1 };
                    match (l, r) {
                        ((t, a), (ParamTerm::Zero, b)) => Ok((t, a + sign * b)),
                        ((ParamTerm::Zero, a), (t, b)) if sign == 1 => Ok((t, a + b)),
                        _ => Err(unsupported(e.span)),
                    }
                }
                ast::ExprKind::Call { callee, arguments } if arguments.len() == 1 => {
                    let builtin = resolution.reference(callee.span).is_some_and(|id| {
                        let b = &resolution.bindings[id];
                        b.kind == BindingKind::Builtin
                            && matches!(b.name.as_str(), "Bytes.len" | "Vec.len" | "Slice.len")
                    });
                    match (builtin, go(&arguments[0], resolution, params, unsupported)?) {
                        (true, (ParamTerm::Param(i), 0)) => Ok((ParamTerm::Len(i), 0)),
                        _ => Err(unsupported(e.span)),
                    }
                }
                _ => Err(unsupported(e.span)),
            }
        }
        go(e, resolution, &runtime_before, &unsupported)
    };
    let mut atoms = Vec::new();
    let mut pending = vec![body.as_ref()];
    while let Some(e) = pending.pop() {
        match &e.kind {
            ast::ExprKind::Binary {
                op: Kind::AmpAmp,
                left,
                right,
            } => {
                pending.push(right);
                pending.push(left);
            }
            ast::ExprKind::Binary {
                op: op @ (Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq),
                left,
                right,
            } => {
                let (l, lc) = linear(left)?;
                let (r, rc) = linear(right)?;
                atoms.push((l, lc, op.clone(), r, rc));
            }
            _ => return Err(unsupported(e.span)),
        }
    }
    let _ = indices;
    Ok(crate::facts::Proposition {
        atoms,
        text: text(body),
    })
}
/// Validate every erased logical parameter of a function signature, in order.
/// A parameter type is an open kernel type: it may mention checked logical
/// definitions, *earlier erased kernel binders*, and earlier immutable runtime
/// scalars (`i64`, `Bool`, `Unit`) used as symbolic indices. Runtime type
/// generics, mutable locals, grades, const naturals, and owning data never enter
/// this context. Call-site checking substitutes the actual scalar terms and
/// earlier proof terms.
fn validate_erased_parameters(
    resolution: &Resolution,
    logical: &crate::check::LogicalEnvironment,
    f: &ast::Function,
) -> Result<()> {
    let mut bindings: Vec<(BindingId, Term)> = Vec::new();
    for parameter in &f.parameters {
        let id = resolution.binder(parameter.span).unwrap();
        if parameter.erased {
            if matches!(parameter.ty.kind, ast::TypeKind::Predicate(_)) {
                continue;
            }
            let term = crate::check::elaborate_type(resolution, logical, &bindings, &parameter.ty)
                .map_err(|e| {
                    Diagnostic::new(
                        e.span,
                        format!(
                            "erased parameters must be arithmetic '{{ ... }}' propositions or logical types with closed checked dependencies: {}",
                            e.message
                        ),
                    )
                })?;
            let context = bindings
                .iter()
                .map(|(_, ty)| ty.clone())
                .collect::<Vec<_>>();
            logical.kernel.sort_open(&term, &context).map_err(|e| {
                Diagnostic::new(
                    parameter.ty.span,
                    format!("invalid erased logical parameter: {e}"),
                )
            })?;
            bindings.push((id, term));
            continue;
        }
        // A plain runtime scalar parameter is a symbolic index binder. Its type
        // must itself be an admitted machine carrier; other runtime types are
        // omitted from the kernel context so any proof mention fails loudly.
        let Ok(term) = crate::check::elaborate_type(
            resolution,
            logical,
            &bindings,
            split_grade(&parameter.ty).0,
        ) else {
            continue;
        };
        let context = bindings
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>();
        let Ok(Some(carrier)) = logical.kernel.scalar_open(&term, &context) else {
            continue;
        };
        bindings.push((id, Term::Scalar(carrier)));
    }
    Ok(())
}
/// Check array lengths in a function signature before specialization. This
/// catches unbound, type/grade, and runtime-dependent lengths even when the
/// generic function is never instantiated; concrete lengths are still checked
/// during specialization.
fn validate_length_templates(resolution: &Resolution, f: &ast::Function) -> Result<()> {
    let types = f
        .parameters
        .iter()
        .filter(|parameter| !parameter.erased)
        .map(|parameter| &parameter.ty)
        .chain(std::iter::once(&f.result))
        .collect::<Vec<_>>();
    validate_type_templates_for(resolution, &f.generics, &types)
}

/// Validate array lengths and natural-const usage in a signature or data
/// declaration before any specialization. Concrete lengths are still checked
/// when an instance is created.
pub(crate) fn validate_type_templates_for(
    resolution: &Resolution,
    generics: &[ast::Generic],
    types: &[&ast::Type],
) -> Result<()> {
    let consts = generics
        .iter()
        .filter(|generic| is_const_generic(resolution, generic))
        .map(|generic| resolution.binder(generic.span).unwrap())
        .collect::<BTreeSet<_>>();
    for ty in types {
        validate_type_template(resolution, ty, &consts, false, false)?;
    }
    Ok(())
}

fn validate_type_template(
    resolution: &Resolution,
    ty: &ast::Type,
    consts: &BTreeSet<BindingId>,
    in_length: bool,
    as_argument: bool,
) -> Result<()> {
    match &ty.kind {
        ast::TypeKind::Array(element, length) => {
            validate_type_template(resolution, element, consts, false, false)?;
            validate_length_template(resolution, length, consts)
        }
        ast::TypeKind::Dyn(inner) => validate_type_template(resolution, inner, consts, false, true),
        ast::TypeKind::Named { arguments, .. } => {
            if let Some(id) = resolution.reference(ty.span) {
                let binding = &resolution.bindings[id];
                if binding.kind == BindingKind::Generic {
                    if in_length && !consts.contains(&id) {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "array length parameter '{}' must be a compile-time natural ('N: Nat'), not a type or grade parameter",
                                binding.name
                            ),
                        ));
                    }
                    if !in_length && !as_argument && consts.contains(&id) {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "natural const parameter '{}' is not a runtime type; use it only as an array length or compile-time index",
                                binding.name
                            ),
                        ));
                    }
                }
                if in_length && matches!(binding.kind, BindingKind::Parameter | BindingKind::Local)
                {
                    return Err(Diagnostic::new(
                        ty.span,
                        "array length depends on a runtime value; use Vec<T> or an immutable &[T] view for a length that is not statically known",
                    ));
                }
            }
            for argument in arguments {
                validate_type_template(resolution, argument, consts, in_length, true)?;
            }
            Ok(())
        }
        ast::TypeKind::Tuple(items) => {
            for item in items {
                validate_type_template(resolution, item, consts, in_length, false)?;
            }
            Ok(())
        }
        ast::TypeKind::Structural(fields) => {
            for field in fields {
                validate_type_template(resolution, &field.ty, consts, false, false)?;
            }
            Ok(())
        }
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Borrow { inner, .. }
        | ast::TypeKind::Graded { inner, .. } => {
            validate_type_template(resolution, inner, consts, in_length, false)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            for parameter in parameters {
                validate_type_template(resolution, &parameter.ty, consts, false, false)?;
            }
            validate_type_template(resolution, result, consts, false, false)?;
            for effect in effects {
                validate_type_template(resolution, effect, consts, false, false)?;
            }
            Ok(())
        }
        ast::TypeKind::Binary { left, right, .. } => {
            validate_type_template(resolution, left, consts, in_length, false)?;
            validate_type_template(resolution, right, consts, in_length, false)
        }
        ast::TypeKind::Predicate(_) => Ok(()),
        ast::TypeKind::Lifetime(_) | ast::TypeKind::SelfType => Ok(()),
        ast::TypeKind::Integer(_) | ast::TypeKind::Bool(_) => Ok(()),
    }
}

fn validate_length_template(
    resolution: &Resolution,
    ty: &ast::Type,
    consts: &BTreeSet<BindingId>,
) -> Result<()> {
    validate_type_template(resolution, ty, consts, true, false)
}

/// Whether a surface type mentions a particular binding. Used to decide whether
/// a runtime scalar must be frozen as a symbolic kernel index at a call: an
/// unrelated scalar argument keeps its ordinary evaluation.
fn type_references_binding(resolution: &Resolution, ty: &ast::Type, id: BindingId) -> bool {
    match &ty.kind {
        ast::TypeKind::Named { arguments, .. } => {
            resolution.reference(ty.span) == Some(id)
                || arguments
                    .iter()
                    .any(|argument| type_references_binding(resolution, argument, id))
        }
        ast::TypeKind::Tuple(items) => items
            .iter()
            .any(|item| type_references_binding(resolution, item, id)),
        ast::TypeKind::Structural(fields) => fields
            .iter()
            .any(|field| type_references_binding(resolution, &field.ty, id)),
        ast::TypeKind::Dyn(inner) => type_references_binding(resolution, inner, id),
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Borrow { inner, .. }
        | ast::TypeKind::Graded { inner, .. } => type_references_binding(resolution, inner, id),
        ast::TypeKind::Array(element, length) => {
            type_references_binding(resolution, element, id)
                || type_references_binding(resolution, length, id)
        }
        ast::TypeKind::Function {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_references_binding(resolution, &parameter.ty, id))
                || type_references_binding(resolution, result, id)
                || effects
                    .iter()
                    .any(|effect| type_references_binding(resolution, effect, id))
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_references_binding(resolution, left, id)
                || type_references_binding(resolution, right, id)
        }
        ast::TypeKind::Integer(_)
        | ast::TypeKind::Bool(_)
        | ast::TypeKind::Lifetime(_)
        | ast::TypeKind::SelfType
        | ast::TypeKind::Predicate(_) => false,
    }
}

/// An integer literal checked against the range of its contextual type.
fn int_literal(text: &str, negative: bool, ty: Type, span: Span) -> Result<i64> {
    let kind = ty.int_kind().unwrap_or(crate::int::IntKind::I64);
    let magnitude = text.parse::<i128>().ok();
    magnitude
        .map(|m| if negative { -m } else { m })
        .and_then(|value| kind.encode(value))
        .ok_or_else(|| {
            Diagnostic::new(
                span,
                format!(
                    "integer literal is outside the {} range ({}..={})",
                    kind.name(),
                    kind.min(),
                    kind.max()
                ),
            )
        })
}
fn is_int_literal(expr: &ast::Expr) -> bool {
    match &expr.kind {
        ast::ExprKind::Integer(_) => true,
        ast::ExprKind::Unary {
            op: Kind::Minus,
            operand,
            ..
        } => matches!(operand.kind, ast::ExprKind::Integer(_)),
        _ => false,
    }
}
/// A nonnegative or negated decimal float literal.
fn is_float_literal(expr: &ast::Expr) -> bool {
    match &expr.kind {
        ast::ExprKind::Float(_) => true,
        ast::ExprKind::Unary {
            op: Kind::Minus,
            operand,
            ..
        } => matches!(operand.kind, ast::ExprKind::Float(_)),
        _ => false,
    }
}
#[allow(dead_code)]
fn integer(text: &str, negative: bool, span: Span) -> Result<i64> {
    let value = if negative {
        format!("-{text}")
    } else {
        text.to_owned()
    };
    value
        .parse()
        .map_err(|_| Diagnostic::new(span, "integer literal is outside the i64 range"))
}
struct Loop {
    /// Result type of `break value` (None for `while`).
    value: Option<Type>,
    is_while: bool,
    /// Type expected of the whole loop expression, for `break` values.
    expected: Option<Type>,
}
/// One inclusion constraint on an effect row during a call: the declared row
/// `fixed | e1 | e2 ...` must cover the actual callable row. Constraints are
/// accumulated across every higher-order argument before a finite solver picks
/// a unique minimal specialization.
#[derive(Debug, Clone)]
struct EffectConstraint {
    fixed: u8,
    variables: Vec<BindingId>,
    actual: u8,
    span: Span,
}

/// One lexical effect-handler binding. The handler is materialized in a hidden
/// local so `perform` can call it and the ownership pass can enforce the
/// callable's one-shot/linear contract.
struct HandlerScope {
    operation: String,
    parameter: Type,
    result: Type,
    slot: usize,
    handler_parameter: Type,
    handler_result: Type,
    effects: u8,
}

struct Checker<'a, 't> {
    types: &'t mut Types<'a>,
    resolution: &'a Resolution,
    functions: &'t mut Functions<'a>,
    substitution: BTreeMap<BindingId, Type>,
    /// Concrete values of this instance's compile-time natural parameters.
    consts: BTreeMap<BindingId, usize>,
    /// Concrete values of this instance's abstract grade parameters.
    grades: BTreeMap<BindingId, Grade>,
    /// Concrete effect rows of this instance's `e: Effects` parameters.
    effect_arguments: BTreeMap<BindingId, u8>,
    locals: Vec<Local>,
    slots: BTreeMap<BindingId, usize>,
    result: Type,
    /// Declared or freshly elided lifetime of each runtime parameter of the
    /// function currently being checked. Lambda captures inherit a declared
    /// parameter lifetime so a captured slice keeps the caller's identity.
    parameter_lifetimes: Vec<Option<String>>,
    /// Static result-transfer contract of the function/lambda currently being
    /// checked. Distinguishes owning `@[1]` transfers from must-use copyable
    /// transfers when a returned value is observed.
    result_grade: Option<Grade>,
    effects: u8,
    depth: usize,
    loops: Vec<Loop>,
    facts: crate::facts::Facts,
    /// Erased proof parameters in scope: binder -> proposition.
    proofs: BTreeMap<BindingId, crate::facts::Proposition>,
    /// Checked logical definitions and their kernel names.
    logical: &'a crate::check::LogicalEnvironment,
    /// Kernel binders in scope order: symbolic runtime scalars followed by
    /// erased logical/arithmetic evidence. A runtime scalar contributes its
    /// carrier type, so `Var(i)` is the symbolic value itself.
    kernel_locals: Vec<BindingId>,
    /// Kernel type of each binder in `kernel_locals` (including symbolic
    /// runtime scalars).
    kernel_types: BTreeMap<BindingId, Term>,
    /// Kernel type of each erased logical parameter in scope. Only these are
    /// evidence; a runtime scalar is never a proof and has no runtime-erased
    /// meaning.
    kernel_proofs: BTreeMap<BindingId, Term>,
    /// Lexical `Task.scope` nesting. `Task.spawn` is legal only when nonzero.
    /// Nested function values reset this to zero so spawn cannot be smuggled
    /// into a callback that outlives its scope.
    scope_depth: usize,
    /// Monotonic id for checked `Slice.split_at_mut` pairs in this body.
    next_split: usize,
    /// Concrete `Self` target when checking an impl method body.
    self_type: Option<Type>,
    /// Trait specialization of the default body being checked, if any. An
    /// unqualified method call on `Self` prefers this specialization.
    default_trait: Option<(BindingId, TraitArguments)>,
    /// Associated constants of the impl that owns this body, already evaluated
    /// for this specialization. `Self::NAME` projects them.
    associated_consts: BTreeMap<String, ConstValue>,
    /// Module unit of the function being checked, for method visibility.
    unit: usize,
    /// The current field expression is a place used to derive a subview
    /// (`&mut record.field[..]`), not a copied field value.
    field_place: bool,
    /// Binding of the function or method body being checked. Used to resolve
    /// `T.NAME` associated-constant projections through `T`'s trait bound.
    binding: BindingId,
    /// Version of each admitted symbolic runtime scalar local. Assignments
    /// append a fresh kernel binder and increment this counter, so later proof
    /// uses denote the new value while already-shifted proof types denote the
    /// old hypothesis. A mutable capture is still rejected because a closure
    /// environment would observe an unsynchronized runtime location.
    scalar_epochs: BTreeMap<BindingId, u32>,
    /// Snapshot positions in `kernel_locals` for scalar aliases introduced by
    /// `let alias = scalar_name`. The position is absolute, so a later
    /// assignment to the source appends a new binder and leaves the alias
    /// denoting the value copied at binding time.
    kernel_aliases: BTreeMap<BindingId, usize>,
    /// Lexically active effect handlers, innermost last. A handler is visible
    /// only to direct `perform` expressions in the same function body.
    handlers: Vec<HandlerScope>,
    /// Pending effect-row inclusion constraints for the current inference
    /// group. `infer` takes a mark and solves them after every argument has
    /// contributed its evidence.
    effect_constraints: Vec<EffectConstraint>,
}
impl Checker<'_, '_> {
    fn nested<T>(&mut self, span: Span, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        if self.depth >= 128 {
            return Err(Diagnostic::new(
                span,
                "executable checking nesting budget exhausted",
            ));
        }
        self.depth += 1;
        let result = f(self);
        self.depth -= 1;
        result
    }
    /// The type of an integer literal: its expected integer type, else i64.
    fn literal_type(&self, expected: Option<Type>) -> Type {
        let expected = expected.map(|t| match t {
            Type::Union(id) => self.types.unions[id]
                .members
                .iter()
                .copied()
                .find(|m| m.int_kind().is_some())
                .unwrap_or(t),
            t => t,
        });
        match expected.and_then(Type::int_kind) {
            Some(kind) => Type::int(kind),
            None => Type::I64,
        }
    }
    /// The type of a float literal: a contextual `f32`/`f64` (including a
    /// float union alternative), else the default `f64`.
    fn float_literal_type(&self, expected: Option<Type>) -> Type {
        let expected = expected.map(|t| match t {
            Type::Union(id) => self.types.unions[id]
                .members
                .iter()
                .copied()
                .find(|m| m.float_kind().is_some())
                .unwrap_or(t),
            t => t,
        });
        match expected.and_then(Type::float_kind) {
            Some(kind) => Type::float(kind),
            None => Type::float(crate::float::FloatKind::F64),
        }
    }
    /// Both operands must be the same float type.
    fn same_float(&self, left: Type, right: Type, span: Span) -> Result<Type> {
        let left_kind = left.float_kind();
        let right_kind = right.float_kind();
        match (left, right, left_kind, right_kind) {
            (Type::Never, other, _, _) | (other, Type::Never, _, _) => {
                Ok(if other == Type::Never {
                    Type::float(crate::float::FloatKind::F64)
                } else {
                    other
                })
            }
            (_, _, Some(a), Some(b)) if a == b => Ok(left),
            (_, _, Some(_), Some(_)) => Err(Diagnostic::new(
                span,
                format!(
                    "floating-point operands must have the same type, found {} and {}; convert one explicitly with Float.try_to_f32 or Float.to_f64",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
            _ => Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: this operator needs two floats of one type, found {} and {}",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
        }
    }
    /// Both operands must be the same integer type.
    fn same_int(&self, left: Type, right: Type, span: Span) -> Result<Type> {
        let left_kind = left.int_kind();
        let right_kind = right.int_kind();
        match (left, right, left_kind, right_kind) {
            (Type::Never, other, _, _) | (other, Type::Never, _, _) => {
                Ok(if other == Type::Never {
                    Type::I64
                } else {
                    other
                })
            }
            (_, _, Some(a), Some(b)) if a == b => Ok(left),
            (_, _, Some(_), Some(_)) => Err(Diagnostic::new(
                span,
                format!(
                    "integer operands must have the same type, found {} and {}; convert one with Int.convert, Int.try_convert, or Int.truncate",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
            _ => Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: this operator needs integer operands, found {} and {}",
                    self.types.name(left),
                    self.types.name(right)
                ),
            )),
        }
    }
    /// `(a, b, ...)`: elements are evaluated left to right, in layout order.
    /// If an element diverges, later source elements are unreachable and are
    /// not checked: a `return` or `?` in an earlier field must not make a later
    /// field's obligations look reachable.
    fn tuple_value(
        &mut self,
        values: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if let Some(expected) = expected
            && let Some(layout) = expected.layout().filter(|id| self.types.enums[*id].tuple)
        {
            let arity = self.types.enums[layout].arguments.len();
            if arity != values.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "tuple expression has {} elements, but the expected tuple type has {}",
                        values.len(),
                        arity
                    ),
                ));
            }
        }
        let candidates = self.expected_tuple_elements(expected, values.len());
        if candidates.len() > 1 {
            let mut accepted = Vec::new();
            let mut first_error = None;
            for candidate in &candidates {
                let mut fields = Vec::with_capacity(values.len());
                let mut failed = None;
                for (index, value) in values.iter().enumerate() {
                    match self.expr_expected(value, Some(candidate[index])) {
                        Ok(value) => match self.coerce(value, candidate[index], span) {
                            Ok(value) => fields.push(value),
                            Err(error) => {
                                failed = Some(error);
                                break;
                            }
                        },
                        Err(error) => {
                            failed = Some(error);
                            break;
                        }
                    }
                }
                if failed.is_none() {
                    accepted.push((candidate.clone(), fields));
                } else if first_error.is_none() {
                    first_error = failed;
                }
            }
            let (elements, fields) = match accepted.len() {
                1 => accepted.pop().expect("one accepted tuple alternative"),
                0 => {
                    return Err(
                        first_error.expect("a tuple literal candidate always attempts one element")
                    );
                }
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this tuple literal fits several union alternatives; add an explicit annotation",
                    ));
                }
            };
            let ty = self.types.tuple(elements, span)?;
            let value = Expr {
                kind: ExprKind::Construct {
                    enum_id: ty.layout().unwrap(),
                    tag: 0,
                    fields,
                },
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let wanted = candidates.into_iter().next();
        let mut fields = Vec::with_capacity(values.len());
        for (index, value) in values.iter().enumerate() {
            let hint = wanted.as_ref().map(|w| w[index]);
            let value = self.expr_expected(value, hint)?;
            if value.ty == Type::Never {
                fields.push(value);
                return Ok(Expr {
                    kind: ExprKind::Block(Block {
                        statements: fields.into_iter().map(Statement::Expr).collect(),
                        tail: None,
                        ty: Type::Never,
                    }),
                    ty: Type::Never,
                    span,
                    resource: None,
                });
            }
            let value = match &wanted {
                Some(elements) => {
                    let span = value.span;
                    self.coerce(value, elements[index], span)?
                }
                None => value,
            };
            fields.push(value);
        }
        let elements = match wanted {
            Some(elements) => elements,
            None => fields
                .iter()
                .map(|field| self.types.full(field.ty, field.span))
                .collect::<Result<Vec<_>>>()?,
        };
        let ty = self.types.tuple(elements, span)?;
        let value = Expr {
            kind: ExprKind::Construct {
                enum_id: ty.layout().unwrap(),
                tag: 0,
                fields,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Element hints from an expected tuple type, or from the unique tuple
    /// alternative of an expected union with the same arity. An ambiguous
    /// union deliberately supplies no hints: each element stays independently
    /// typed and the whole tuple is injected into the union afterwards.
    fn expected_tuple_elements(&self, expected: Option<Type>, arity: usize) -> Vec<Vec<Type>> {
        let elements = |ty: Type| {
            ty.layout()
                .filter(|id| {
                    self.types.enums[*id].tuple && self.types.enums[*id].arguments.len() == arity
                })
                .map(|id| self.types.enums[id].arguments.clone())
        };
        match expected {
            Some(Type::Union(id)) => self.types.unions[id]
                .members
                .iter()
                .filter_map(|member| elements(*member))
                .collect(),
            Some(ty) => elements(ty).into_iter().collect(),
            None => Vec::new(),
        }
    }
    /// Whether `name` is one of the builtin methods eligible for receiver
    /// syntax. Builtin dispatch is checked first and the name is reserved:
    /// user-defined methods may not reuse it, so there is no ambiguous
    /// reinterpretation between a builtin and an impl method.
    fn builtin_method(name: &str) -> bool {
        matches!(
            name,
            "len"
                | "capacity"
                | "get"
                | "at"
                | "try_get"
                | "push"
                | "push_reserved"
                | "clear"
                | "reserve"
                | "try_reserve"
                | "copy"
                | "set"
                | "as_bytes"
                | "as_str"
                | "bytes"
                | "substr"
                | "to_string"
                | "byte_at"
                | "scalar_at"
                | "scalar_len"
                | "from_utf8"
                | "take"
                | "read"
                | "code"
                | "convert"
                | "try_convert"
                | "truncate"
                | "wrapping_add"
                | "wrapping_sub"
                | "wrapping_mul"
                | "saturating_add"
                | "saturating_sub"
                | "saturating_mul"
                | "checked_add"
                | "checked_sub"
                | "checked_mul"
                | "abs"
                | "sqrt"
                | "is_nan"
                | "is_infinite"
                | "is_finite"
                | "to_f64"
                | "try_to_f32"
                | "try_to_int"
        )
    }
    /// Auto-borrow an owning receiver for a read-only builtin. The receiver is
    /// already checked exactly once; only a direct local may become `&name`,
    /// matching the existing borrow rules. A value that is already a reference
    /// is passed through unchanged.
    fn method_borrow(&mut self, first: Expr) -> Result<Expr> {
        if matches!(first.ty, Type::Ref(_)) {
            return Ok(first);
        }
        if !matches!(
            first.ty,
            Type::Box(_) | Type::Bytes | Type::String | Type::Vec(_) | Type::Task(_)
        ) {
            return Err(Diagnostic::new(
                first.span,
                format!(
                    "this builtin method needs an immutable borrow, but a temporary {} cannot be borrowed; bind it to a local first",
                    self.types.name(first.ty)
                ),
            ));
        }
        let ExprKind::Local(slot) = first.kind else {
            return Err(Diagnostic::new(
                first.span,
                "borrow an owned Box/Bytes/String/Vec/Task local directly; temporary borrows are not supported",
            ));
        };
        let ty = self.locals[slot].ty;
        Ok(Expr {
            kind: ExprKind::Borrow(slot),
            ty: Type::Ref(self.types.pointer(ty)),
            span: first.span,
            resource: None,
        })
    }
    /// Receiver-style call to an existing builtin. The receiver is checked
    /// before the remaining arguments and appears first in the lowered call, so
    /// evaluation order, loan retention, effects, proofs, and Option/Result
    /// shapes are exactly those of the namespace form.
    fn method_call(
        &mut self,
        receiver: &ast::Expr,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let first = self.expr(receiver)?;
        if first.ty == Type::Never {
            return Ok(first);
        }
        let ty = first.ty;
        let integer_method = ty.int_kind().is_some()
            && matches!(
                name,
                "convert"
                    | "try_convert"
                    | "truncate"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "wrapping_mul"
                    | "saturating_add"
                    | "saturating_sub"
                    | "saturating_mul"
                    | "checked_add"
                    | "checked_sub"
                    | "checked_mul"
            );
        let float_method = ty.float_kind().is_some()
            && matches!(
                name,
                "abs"
                    | "sqrt"
                    | "is_nan"
                    | "is_infinite"
                    | "is_finite"
                    | "to_f64"
                    | "try_to_f32"
                    | "try_to_int"
            );
        if explicit.is_some() && !integer_method && !float_method {
            return Err(Diagnostic::new(
                span,
                format!("builtin method '{name}' takes no type arguments"),
            ));
        }
        let unsupported = |c: &Self| {
            Diagnostic::new(
                span,
                format!(
                    "no supported builtin method '{name}' for {}; this name is reserved for builtin dispatch, so choose a non-reserved name for a user-defined method",
                    c.types.name(ty)
                ),
            )
        };
        // Scalar/text/box receiver forms.
        if ty.int_kind().is_some()
            && matches!(
                name,
                "convert"
                    | "try_convert"
                    | "truncate"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "wrapping_mul"
                    | "saturating_add"
                    | "saturating_sub"
                    | "saturating_mul"
                    | "checked_add"
                    | "checked_sub"
                    | "checked_mul"
            )
        {
            let canonical = format!("Int.{name}");
            return self.int_call_with(
                Some(first),
                &canonical,
                explicit,
                arguments,
                expected,
                span,
            );
        }
        if name == "code" && ty == Type::Char {
            return self.int_call_with(
                Some(first),
                "Char.code",
                explicit,
                arguments,
                expected,
                span,
            );
        }
        if ty.float_kind().is_some() && float_method {
            let canonical = format!("Float.{name}");
            return self.float_call_with(
                Some(first),
                &canonical,
                explicit,
                arguments,
                expected,
                span,
            );
        }
        if name == "take" && matches!(ty, Type::Box(_)) {
            if explicit.is_some() || !arguments.is_empty() {
                return Err(Diagnostic::new(span, "Box.take takes no arguments"));
            }
            let Type::Box(index) = ty else { unreachable!() };
            let result = self.types.pointees[index];
            return Ok(Expr {
                kind: ExprKind::BoxTake(Box::new(first)),
                ty: result,
                span,
                resource: None,
            });
        }
        if name == "read" && matches!(ty, Type::Box(_) | Type::Ref(_)) {
            if explicit.is_some() || !arguments.is_empty() {
                return Err(Diagnostic::new(span, "Box.read takes no arguments"));
            }
            let first = self.method_borrow(first)?;
            let Type::Ref(pointer) = first.ty else {
                unreachable!()
            };
            let Type::Box(index) = self.types.pointees[pointer] else {
                return Err(unsupported(self));
            };
            let result = self.types.pointees[index];
            return Ok(Expr {
                kind: ExprKind::BoxRead(Box::new(first)),
                ty: result,
                span,
                resource: None,
            });
        }
        // Collection and text methods dispatch on the receiver type.
        let pointee = |c: &Self, ty: Type| match ty {
            Type::Ref(p) => Some(c.types.pointees[p]),
            other => Some(other),
        };
        let base = pointee(self, ty);
        if name == "len" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Len, first, arguments, expected, span);
        }
        if name == "capacity" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Capacity, first, arguments, expected, span);
        }
        if name == "get" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Get, first, arguments, expected, span);
        }
        if name == "copy" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Copy, first, arguments, expected, span);
        }
        if name == "push" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Push, first, arguments, expected, span);
        }
        if name == "push_reserved" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::PushReserved, first, arguments, expected, span);
        }
        if name == "clear" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Clear, first, arguments, expected, span);
        }
        if name == "from_utf8" && matches!(base, Some(Type::Bytes)) {
            return self.string_call_with("String.from_utf8", first, arguments, expected, span);
        }
        if name == "at" && matches!(base, Some(Type::Bytes)) {
            let first = self.method_borrow(first)?;
            return self.vec_call_with("Bytes.at", first, arguments, expected, span);
        }
        if matches!(base, Some(Type::Slice(_)) | Some(Type::SliceMut(_))) {
            let method = match name {
                "len" | "get" | "try_get" | "at" | "set" => name,
                _ => return Err(unsupported(self)),
            };
            return self.slice_call_with(
                &format!("Slice.{method}"),
                first,
                arguments,
                expected,
                span,
            );
        }
        if matches!(base, Some(Type::Vec(_))) {
            let (method, borrow) = match name {
                "len" | "get" | "at" => (name, true),
                "clear" | "push" | "reserve" | "try_reserve" | "set" => (name, false),
                _ => return Err(unsupported(self)),
            };
            let first = if borrow {
                self.method_borrow(first)?
            } else {
                first
            };
            return self.vec_call_with(&format!("Vec.{method}"), first, arguments, expected, span);
        }
        if matches!(base, Some(Type::String)) {
            let (method, borrow) = match name {
                "len" | "scalar_len" | "byte_at" | "scalar_at" | "as_bytes" | "as_str"
                | "substr" => (name, true),
                "bytes" => (name, false),
                _ => return Err(unsupported(self)),
            };
            let first = if borrow {
                self.method_borrow(first)?
            } else {
                first
            };
            return self.string_call_with(
                &format!("String.{method}"),
                first,
                arguments,
                expected,
                span,
            );
        }
        if matches!(base, Some(Type::Str)) {
            let method = match name {
                "len" | "scalar_len" | "byte_at" | "scalar_at" | "to_string" | "substr" => name,
                _ => return Err(unsupported(self)),
            };
            return self.str_call_with(&format!("Str.{method}"), first, arguments, expected, span);
        }
        Err(unsupported(self))
    }
    /// The field `name` of a record type, as a word offset and field type.
    fn record_field_of_type(&self, ty: Type, name: &str) -> Option<(usize, Type)> {
        let id = ty.layout().filter(|id| self.types.enums[*id].record)?;
        let variant = &self.types.enums[id].variants[0];
        let index = variant.names.iter().position(|field| field == name)?;
        let offset = 1 + variant.fields[..index]
            .iter()
            .map(|field| self.types.width(*field))
            .sum::<usize>();
        Some((offset, variant.fields[index]))
    }
    /// Whether an expression is a pure place: a local name or a field chain
    /// rooted at one. Such receivers use the same non-moving read path as
    /// ordinary field projection.
    fn is_place(&self, expr: &ast::Expr) -> bool {
        match &expr.kind {
            ast::ExprKind::Name(name) if name != "_" => self.slot(expr.span).is_ok(),
            ast::ExprKind::Field { value, .. }
                if self.resolution.reference(expr.span).is_none() =>
            {
                self.is_place(value)
            }
            _ => false,
        }
    }
    /// Recognize `receiver.Trait.method` and the generic-trait spelling
    /// `receiver.Trait::<Arguments>.method` as explicitly qualified static
    /// dispatch. The resolver recorded the trait binding on the
    /// `receiver.Trait` selector node.
    fn qualified_method<'x>(
        &self,
        target: &'x ast::Expr,
    ) -> Option<(&'x ast::Expr, &'x str, BindingId, Option<&'x [ast::Type]>)> {
        let ast::ExprKind::Field { value, name } = &target.kind else {
            return None;
        };
        match &value.kind {
            ast::ExprKind::Field {
                value: receiver, ..
            } => {
                let id = self.resolution.reference(value.span)?;
                (self.resolution.bindings[id].kind == BindingKind::Trait).then_some((
                    receiver.as_ref(),
                    name.as_str(),
                    id,
                    None,
                ))
            }
            ast::ExprKind::Specialize { callee, arguments } => {
                let ast::ExprKind::Field {
                    value: receiver, ..
                } = &callee.kind
                else {
                    return None;
                };
                let id = self.resolution.reference(callee.span)?;
                (self.resolution.bindings[id].kind == BindingKind::Trait).then_some((
                    receiver.as_ref(),
                    name.as_str(),
                    id,
                    Some(arguments.as_slice()),
                ))
            }
            _ => None,
        }
    }
    /// Resolve one explicitly supplied trait specialization at the call site.
    #[allow(clippy::too_many_arguments)]
    fn call_site_trait_arguments(
        &mut self,
        trait_id: BindingId,
        explicit: Option<&[ast::Type]>,
        span: Span,
    ) -> Result<TraitArguments> {
        let definition = self.functions.traits[&trait_id].clone();
        let trait_name = self.resolution.bindings[trait_id].name.clone();
        if definition.generics.is_empty() {
            if explicit.is_some_and(|explicit| !explicit.is_empty()) {
                return Err(Diagnostic::new(
                    span,
                    format!("trait '{trait_name}' takes no type arguments"),
                ));
            }
            return Ok(TraitArguments::default());
        }
        let Some(explicit) = explicit else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "trait '{trait_name}' is generic; qualify the call with its arguments, as in 'receiver.{trait_name}::<...>.method(...)'"
                ),
            ));
        };
        let substitution = crate::runtime_types::Subst {
            types: self.substitution.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effect_arguments.clone(),
            lifetimes: BTreeMap::new(),
            self_type: self.self_type,
            associated_types: BTreeMap::new(),
            projections: BTreeMap::new(),
            self_projections: BTreeMap::new(),
        };
        evaluate_trait_arguments(
            self.types,
            self.resolution,
            self.logical,
            &definition.generics,
            explicit,
            &substitution,
            &trait_name,
            span,
        )
    }
    fn lookup_method(
        &mut self,
        ty: Type,
        name: &str,
        trait_id: Option<(BindingId, TraitArguments)>,
        span: Span,
    ) -> Result<MethodDefinition> {
        let key = ty.full();
        if let Some((trait_id, trait_arguments)) = trait_id {
            let definition = self.functions.traits[&trait_id].clone();
            let trait_name = self.resolution.bindings[trait_id].name.clone();
            let specialization = if definition.generics.is_empty() {
                trait_name.clone()
            } else {
                format!(
                    "{trait_name}<{}>",
                    trait_specialization_name(
                        self.resolution,
                        self.types,
                        &definition.generics,
                        &trait_arguments
                    )
                )
            };
            if let Some(methods) =
                self.functions
                    .trait_impls
                    .get(&(trait_id, trait_arguments.clone(), key))
            {
                return methods.get(name).copied().ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!("trait '{specialization}' has no method '{name}'"),
                    )
                });
            }
            let mut matches = self.functions.matching_impls(
                self.types,
                self.resolution,
                trait_id,
                &trait_arguments,
                key,
                0,
            )?;
            matches.retain(|candidate| {
                self.functions.impl_headers[candidate.header]
                    .methods
                    .contains_key(name)
            });
            let selected = self
                .functions
                .select_most_specific(self.resolution, &matches);
            let Some(selected) = selected else {
                if matches.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "type '{}' does not implement trait '{specialization}'",
                            self.types.name(ty)
                        ),
                    ));
                }
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "method '{name}' on '{}' has several incomparable generic impls; coherence requires a unique most-specific impl",
                        self.types.name(ty)
                    ),
                ));
            };
            let index = self.functions.intern_impl(
                self.types,
                self.resolution,
                selected.header,
                selected.arguments,
            )?;
            let mut definition = *self.functions.impl_headers[selected.header]
                .methods
                .get(name)
                .expect("candidate was filtered by method name");
            definition.impl_arguments = Some(index);
            return Ok(definition);
        }
        if let Some(definition) = self
            .functions
            .inherent
            .get(&key)
            .and_then(|methods| methods.get(name))
        {
            return Ok(*definition);
        }
        // Generic inherent impls apply only when no exact inherent method
        // exists; a concrete `impl Type` is always more specific.
        if let Some(generic) = self.generic_method_candidates(key, name, None, span)? {
            return Ok(generic);
        }
        let mut candidates = self
            .functions
            .methods_by_type
            .get(&key)
            .and_then(|methods| methods.get(name))
            .cloned()
            .unwrap_or_default();
        candidates.sort_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        // Inside a materialized default body, an unqualified call on `Self`
        // prefers the enclosing trait specialization (the enclosing trait
        // itself when it is not generic). Without this, a generic trait
        // implemented at several specializations could not call its own
        // sibling methods from a default body without redundant qualification.
        if candidates.len() > 1
            && self
                .self_type
                .is_some_and(|self_type| self_type.full() == key)
            && let Some((enclosing_trait, enclosing_arguments)) = &self.default_trait
        {
            let matching = candidates
                .iter()
                .filter(|(trait_id, arguments, _)| {
                    trait_id == enclosing_trait && arguments == enclosing_arguments
                })
                .cloned()
                .collect::<Vec<_>>();
            if let [single] = matching.as_slice() {
                return Ok(single.2);
            }
        }
        // Add applicable generic impls for every trait. Per trait, the unique
        // most-specific header wins; a concrete impl of the same trait and
        // arguments still supersedes a generic one.
        let mut generic_by_trait: BTreeMap<BindingId, Vec<ImplMatch>> = BTreeMap::new();
        for header_index in 0..self.functions.impl_headers.len() {
            let Some(trait_id) = self.functions.impl_headers[header_index].trait_id else {
                continue;
            };
            if self.functions.impl_headers[header_index].concrete.is_some()
                || !self.functions.impl_headers[header_index]
                    .methods
                    .contains_key(name)
            {
                continue;
            }
            if let Some(candidate) = self.functions.match_header_for_receiver(
                self.types,
                self.resolution,
                header_index,
                key,
                0,
            )? {
                generic_by_trait
                    .entry(trait_id)
                    .or_default()
                    .push(candidate);
            }
        }
        let mut generic_candidates = Vec::new();
        for (trait_id, matches) in generic_by_trait {
            let Some(selected) = self
                .functions
                .select_most_specific(self.resolution, &matches)
            else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "method '{name}' on '{}' has several incomparable generic impls of trait '{}'",
                        self.types.name(ty),
                        self.resolution.bindings[trait_id].name
                    ),
                ));
            };
            let required = self.functions.trait_arguments_for_match(
                self.types,
                self.resolution,
                selected.header,
                &selected.arguments,
            )?;
            if self
                .functions
                .trait_impls
                .contains_key(&(trait_id, required.clone(), key))
            {
                continue;
            }
            if !self.functions.impl_headers[selected.header]
                .methods
                .contains_key(name)
            {
                continue;
            }
            let index = self.functions.intern_impl(
                self.types,
                self.resolution,
                selected.header,
                selected.arguments,
            )?;
            let mut definition = *self.functions.impl_headers[selected.header]
                .methods
                .get(name)
                .expect("filtered by method name");
            definition.impl_arguments = Some(index);
            generic_candidates.push((trait_id, required, definition));
        }
        // Deduplicate identical (trait, arguments) generic candidates that can
        // arise when several specializations of the same trait match.
        generic_candidates.sort_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        generic_candidates.dedup_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        candidates.extend(generic_candidates);
        candidates.sort_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        match candidates.as_slice() {
            [] => Err(Diagnostic::new(
                span,
                format!(
                    "no method '{name}' for '{}'; define an inherent method, implement a trait, or check the receiver type",
                    self.types.name(ty)
                ),
            )),
            [single] => Ok(single.2),
            many => {
                let traits = many
                    .iter()
                    .map(|(trait_id, arguments, _)| {
                        let def = &self.functions.traits[trait_id];
                        if def.generics.is_empty() {
                            self.resolution.bindings[*trait_id].name.clone()
                        } else {
                            format!(
                                "{}<{}>",
                                self.resolution.bindings[*trait_id].name,
                                trait_specialization_name(
                                    self.resolution,
                                    self.types,
                                    &def.generics,
                                    arguments
                                )
                            )
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                Err(Diagnostic::new(
                    span,
                    format!(
                        "method '{name}' on '{}' is ambiguous: it is provided by traits {traits}. Disambiguate as 'receiver.Trait.method(...)' or 'receiver.Trait::<...>.method(...)' for a generic trait",
                        self.types.name(ty)
                    ),
                ))
            }
        }
    }
    /// Generic inherent method lookup. Returns `None` when no generic inherent
    /// impl matches; several incomparable matches are an ambiguity error.
    fn generic_method_candidates(
        &mut self,
        key: Type,
        name: &str,
        trait_id: Option<BindingId>,
        span: Span,
    ) -> Result<Option<MethodDefinition>> {
        let mut matches = Vec::new();
        for (header_index, header) in self.functions.impl_headers.iter().enumerate() {
            if header.trait_id != trait_id
                || header.concrete.is_some()
                || !header.methods.contains_key(name)
            {
                continue;
            }
            if trait_id.is_some() {
                continue;
            }
            if let Some(candidate) = self.functions.match_header_for_receiver(
                self.types,
                self.resolution,
                header_index,
                key,
                0,
            )? {
                matches.push(candidate);
            }
        }
        if matches.is_empty() {
            return Ok(None);
        }
        let selected = self
            .functions
            .select_most_specific(self.resolution, &matches);
        let Some(selected) = selected else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "inherent method '{name}' on '{}' has several incomparable generic impls",
                    self.types.name(key)
                ),
            ));
        };
        let index = self.functions.intern_impl(
            self.types,
            self.resolution,
            selected.header,
            selected.arguments,
        )?;
        let mut definition = *self.functions.impl_headers[selected.header]
            .methods
            .get(name)
            .expect("candidate was filtered by method name");
        definition.impl_arguments = Some(index);
        Ok(Some(definition))
    }
    /// Whether this method's declared receiver is `&self` (`Some(false)`) or
    /// `&mut self` (`Some(true)`), or is taken by value (`None`).
    fn method_receiver_borrow(&self, binding: BindingId) -> Option<bool> {
        let f = self.functions.declared.get(&binding)?.ast;
        match &f.parameters.first()?.ty.kind {
            ast::TypeKind::Borrow { mutable, .. } => Some(*mutable),
            _ => None,
        }
    }
    fn check_method_visibility(
        &self,
        definition: MethodDefinition,
        name: &str,
        span: Span,
    ) -> Result<()> {
        if definition.public || definition.unit == self.unit {
            return Ok(());
        }
        let module = self
            .resolution
            .units
            .get(definition.unit)
            .map(|path| path.join("."))
            .filter(|path| !path.is_empty())
            .unwrap_or_else(|| "<root>".to_owned());
        Err(Diagnostic::new(
            span,
            format!("method '{name}' is private to module '{module}'; mark it 'pub'"),
        ))
    }
    /// Check a user-defined receiver-style call. The receiver is checked
    /// exactly once before the remaining arguments and lowers to the same
    /// `Target::Function` call node as a namespace call.
    #[allow(clippy::too_many_arguments)]
    fn user_method_call(
        &mut self,
        receiver_ast: &ast::Expr,
        name: &str,
        trait_id: Option<BindingId>,
        trait_arguments_ast: Option<&[ast::Type]>,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let trait_arguments = match trait_id {
            Some(trait_id) => {
                Some(self.call_site_trait_arguments(trait_id, trait_arguments_ast, span)?)
            }
            None => None,
        };
        let trait_selection = trait_id.zip(trait_arguments);
        // Field projection wins over an unqualified method with the same name.
        // Method declarations that would collide with a record field are
        // rejected when the impl is registered, so this cannot silently make a
        // method unreachable.
        let mut receiver = if self.is_place(receiver_ast) {
            self.place(receiver_ast)?
        } else {
            self.expr(receiver_ast)?
        };
        if receiver.ty == Type::Never {
            return Ok(receiver);
        }
        if let Some(pointer) = receiver.ty.ref_pointee() {
            let pointee = self.types.pointees[pointer];
            if matches!(pointee, Type::Union(_))
                && self.functions.object_traits.contains_key(&pointee)
            {
                return self.dynamic_method_call(
                    receiver,
                    name,
                    trait_selection.clone(),
                    arguments,
                    expected,
                    span,
                );
            }
        }
        if matches!(receiver.ty, Type::Union(_))
            && self.functions.object_traits.contains_key(&receiver.ty)
        {
            return self.dynamic_method_call(
                receiver,
                name,
                trait_selection.clone(),
                arguments,
                expected,
                span,
            );
        }
        let lookup_ty = match receiver.ty.ref_pointee() {
            Some(pointer) if self.types.pointees[pointer].layout().is_some() => {
                self.types.pointees[pointer]
            }
            _ => receiver.ty,
        };
        if trait_id.is_none()
            && !receiver.ty.is_ref()
            && self.record_field_of_type(receiver.ty, name).is_some()
        {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "'{name}' is a callable record field, and field projection takes precedence over method dispatch: a projected field call takes no explicit type arguments"
                    ),
                ));
            }
            let callee = self.project_field(receiver, name, receiver_ast.span, None)?;
            return self.indirect_call_checked(callee, arguments, expected, span);
        }
        let definition = self.lookup_method(lookup_ty, name, trait_selection, span)?;
        self.check_method_visibility(definition, name, span)?;
        if let Some(mutable) = self.method_receiver_borrow(definition.binding) {
            if receiver.ty.is_ref() {
                return Err(Diagnostic::new(
                    receiver_ast.span,
                    "calling a borrowed method through an existing reference is not supported in this call-scoped subset; call it on the owning local, or pass the reference to an ordinary function",
                ));
            }
            let (ExprKind::Peek(slot) | ExprKind::Local(slot)) = receiver.kind else {
                return Err(Diagnostic::new(
                    receiver_ast.span,
                    "a borrowed method receiver must be a direct local binding; borrowed temporaries and projected receivers are not supported",
                ));
            };
            if mutable {
                if !self.locals[slot].mutable {
                    return Err(Diagnostic::new(
                        receiver_ast.span,
                        "cannot mutably borrow an immutable binding; declare it with let mut",
                    ));
                }
                if lookup_ty
                    .layout()
                    .is_some_and(|id| self.types.enums[id].borrowed)
                {
                    return Err(Diagnostic::new(
                        receiver_ast.span,
                        "cannot mutably borrow a record with borrowed fields; only its owning metadata may be updated through an owning value",
                    ));
                }
            }
            let pointee = self.types.pointer(lookup_ty);
            let ty = if mutable {
                Type::RefMut(pointee)
            } else {
                Type::Ref(pointee)
            };
            receiver = Expr {
                kind: ExprKind::Borrow(slot),
                ty,
                span: receiver_ast.span,
                resource: None,
            };
        } else {
            if receiver.ty.is_ref() {
                return Err(Diagnostic::new(
                    receiver_ast.span,
                    "this method takes its receiver by value, but the receiver is a borrowed reference; call an '&self'/'&mut self' method or pass the owner itself",
                ));
            }
            // A direct local receiver is consumed by an owned method. A Peek
            // was a non-moving read for field detection; switch it to Local so
            // the normal ownership pass sees one move.
            if let ExprKind::Peek(slot) = &receiver.kind {
                let slot = *slot;
                let ty = receiver.ty;
                let receiver_span = receiver.span;
                receiver = Expr {
                    kind: ExprKind::Local(slot),
                    ty,
                    span: receiver_span,
                    resource: None,
                };
            }
        }
        self.invoke_method(
            definition.binding,
            definition.impl_arguments,
            receiver_ast,
            receiver,
            explicit,
            arguments,
            expected,
            span,
        )
    }
    /// Resolve `T.NAME` for a generic parameter `T` with a trait bound. The
    /// concrete constant is selected by the same impl solver used for `T.Out`;
    /// the projection is a compile-time literal for the current specialization.
    fn generic_associated_const(
        &mut self,
        binder: BindingId,
        name: &str,
        span: Span,
    ) -> Result<Option<ConstValue>> {
        let Some(declared) = self.functions.declared.get(&self.binding).copied() else {
            return Ok(None);
        };
        let impl_generic = declared.impl_template.and_then(|template| {
            self.functions.impl_headers[template]
                .generics
                .iter()
                .find(|generic| self.resolution.binder(generic.span) == Some(binder))
        });
        let Some(generic) = declared
            .ast
            .generics
            .iter()
            .find(|generic| self.resolution.binder(generic.span) == Some(binder))
            .or(impl_generic)
        else {
            return Ok(None);
        };
        let Some(bound) = &generic.bound else {
            return Ok(None);
        };
        let Some(trait_id) = self.resolution.reference(bound.span) else {
            return Ok(None);
        };
        if self.resolution.bindings[trait_id].kind != BindingKind::Trait {
            return Ok(None);
        }
        let Some(actual) = self.substitution.get(&binder).copied() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project associated constant '{name}' from an unspecialized generic parameter '{}'",
                    self.resolution.bindings[binder].name
                ),
            ));
        };
        let definition = self.functions.traits[&trait_id].clone();
        let argument_ast = match &bound.kind {
            ast::TypeKind::Named { arguments, .. } => arguments.clone(),
            _ => Vec::new(),
        };
        let substitution = crate::runtime_types::Subst {
            types: self.substitution.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effect_arguments.clone(),
            lifetimes: BTreeMap::new(),
            self_type: self.self_type,
            associated_types: BTreeMap::new(),
            projections: BTreeMap::new(),
            self_projections: BTreeMap::new(),
        };
        let required = evaluate_trait_arguments(
            self.types,
            self.resolution,
            self.functions.logical,
            &definition.generics,
            &argument_ast,
            &substitution,
            &self.resolution.bindings[trait_id].name,
            generic.span,
        )?;
        if let Some(values) = self
            .functions
            .trait_consts
            .get(&(trait_id, required.clone(), actual))
        {
            return Ok(values.get(name).cloned());
        }
        let matches = self.functions.matching_impls(
            self.types,
            self.resolution,
            trait_id,
            &required,
            actual,
            0,
        )?;
        if let Some(selected) = self
            .functions
            .select_most_specific(self.resolution, &matches)
        {
            return Ok(self.functions.impl_headers[selected.header]
                .associated
                .consts
                .get(name)
                .cloned());
        }
        Ok(None)
    }
    /// Dynamic dispatch on a closed-world trait object. Returns `None` when the
    /// receiver's union does not represent a trait providing this name, so the
    /// ordinary static path can produce its usual diagnostic.
    #[allow(clippy::too_many_arguments)]
    fn dynamic_method_call(
        &mut self,
        receiver: Expr,
        name: &str,
        trait_selection: Option<(BindingId, TraitArguments)>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        // A stored borrowed object is a reference to the same closed-world
        // union. Dispatch reads a copy through the reference; a copyable object
        // has value semantics, so this neither moves nor duplicates owning
        // storage. Mutable dispatch writes the updated object back through an
        // exclusive reference.
        let reference_slot = match &receiver.kind {
            ExprKind::Peek(slot) | ExprKind::Local(slot) => Some((*slot, receiver.ty)),
            _ => None,
        };
        let borrowed_object = receiver.ty.ref_pointee().map(|pointer| {
            let pointee = self.types.pointees[pointer];
            (pointee, receiver.ty)
        });
        let object_ty = borrowed_object
            .map(|(object, _)| object)
            .unwrap_or(receiver.ty);
        let Some(entries) = self.functions.object_traits.get(&object_ty).cloned() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "no dynamic method '{name}' is available for '{}'",
                    self.types.name(object_ty)
                ),
            ));
        };
        if borrowed_object.is_some()
            && (crate::runtime_types::type_owns(
                &self.types.enums,
                &self.types.unions,
                object_ty,
                0,
            ) || self.linear_type(object_ty))
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a stored borrowed trait object must have copyable members; '{}' owns storage or is linear. Store the object by value or in Box<dyn Trait>",
                    self.types.name(object_ty)
                ),
            ));
        }
        let entry = if let Some((trait_id, arguments)) = trait_selection {
            entries
                .iter()
                .find(|(id, args)| *id == trait_id && *args == arguments)
                .cloned()
        } else {
            let matching = entries
                .iter()
                .filter(|(trait_id, _)| self.functions.traits[trait_id].methods.contains_key(name))
                .cloned()
                .collect::<Vec<_>>();
            match matching.as_slice() {
                [] => {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "no trait represented by '{}' declares dynamic method '{name}'; qualify an object trait or use a static impl",
                            self.types.name(receiver.ty)
                        ),
                    ));
                }
                [single] => Some(single.clone()),
                _ => {
                    let traits = matching
                        .iter()
                        .map(|(id, _)| self.resolution.bindings[*id].name.clone())
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "dynamic method '{name}' is provided by traits {traits}; disambiguate as 'receiver.Trait.method(...)'"
                        ),
                    ));
                }
            }
        };
        let Some((trait_id, trait_arguments)) = entry else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "trait object '{}' does not represent the requested trait specialization",
                    self.types.name(receiver.ty)
                ),
            ));
        };
        let method = self.functions.traits[&trait_id]
            .methods
            .get(name)
            .map(|method| method.function)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "trait '{}' has no method '{name}'",
                        self.resolution.bindings[trait_id].name
                    ),
                )
            })?;
        let receiver_mode = trait_receiver_mode(method);
        let (dispatcher, method_result) =
            self.dynamic_dispatcher(trait_id, &trait_arguments, name, receiver_mode, span)?;
        let signature = self.functions.signatures[dispatcher].clone();
        if arguments.len() + 1 != signature.parameters.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count for dynamic method '{name}': expected {}, found {}",
                    signature.parameters.len().saturating_sub(1),
                    arguments.len()
                ),
            ));
        }
        self.require(signature.effects, span)?;
        let mut writeback = None;
        let mut receiver = if let Some((object, reference_ty)) = borrowed_object {
            match (reference_ty, receiver_mode) {
                (Type::Ref(_), ReceiverMode::Mutable) => {
                    return Err(Diagnostic::new(
                        span,
                        "cannot call an exclusive dynamic method through a shared '&dyn' reference; bind the object with '&mut' or call on the owning local",
                    ));
                }
                (_, ReceiverMode::Owned) => {
                    return Err(Diagnostic::new(
                        span,
                        "cannot call an owning dynamic method through a borrowed trait object; call it on the owning value instead",
                    ));
                }
                (Type::RefMut(_), ReceiverMode::Mutable) => {
                    let Some((slot, _)) = reference_slot else {
                        return Err(Diagnostic::new(
                            span,
                            "a mutable borrowed trait-object call requires a reference binding, as in '&mut object'",
                        ));
                    };
                    writeback = Some(Expr {
                        kind: ExprKind::Peek(slot),
                        ty: reference_ty,
                        span,
                        resource: None,
                    });
                }
                _ => {}
            }
            Expr {
                kind: ExprKind::RefRead(Box::new(receiver)),
                ty: object,
                span,
                resource: None,
            }
        } else {
            receiver
        };
        if let ExprKind::Peek(slot) = &receiver.kind {
            let slot = *slot;
            let ty = receiver.ty;
            let receiver_span = receiver.span;
            receiver = Expr {
                kind: ExprKind::Local(slot),
                ty,
                span: receiver_span,
                resource: None,
            };
        }
        if receiver_mode == ReceiverMode::Mutable
            && borrowed_object.is_none()
            && let ExprKind::Local(slot) = receiver.kind
            && !self.locals[slot].mutable
        {
            return Err(Diagnostic::new(
                span,
                "a mutable dynamic method requires a mutable object binding; declare it with 'let mut'",
            ));
        }
        let mut values = vec![receiver];
        for (argument, ty) in arguments.iter().zip(&signature.parameters[1..]) {
            let value = self.expr_expected(argument, Some(*ty))?;
            values.push(self.coerce(value, *ty, span)?);
        }
        if receiver_mode == ReceiverMode::Mutable {
            // The receiver was rewritten to a local/parameter place when it is
            // one. Move the object into the dispatcher, which returns the
            // updated object and the method result, then store the updated
            // object back into the same place. A temporary receiver is consumed
            // and its updated value is dropped because no later read can
            // observe it.
            let direct_slot = match &values[0].kind {
                ExprKind::Local(slot) => Some(*slot),
                _ => None,
            };
            let object = signature.parameters[0];
            let result_ty = method_result;
            let tuple_ty = self.types.tuple(vec![object, result_ty], span)?;
            let tmp = self.temp(tuple_ty, span)?;
            let extracted = self.temp(result_ty, span)?;
            let call = Expr {
                kind: ExprKind::Call(
                    Target::ObjectFunction {
                        function: dispatcher,
                        receiver: direct_slot.or(reference_slot.map(|(slot, _)| slot)),
                        mutable: true,
                    },
                    values,
                ),
                ty: tuple_ty,
                span,
                resource: None,
            };
            let object_width = self.types.width(object);
            let (pattern, arm_body) = if let Some(slot) = direct_slot {
                let updated = self.temp(object, span)?;
                (
                    Pattern::Variant {
                        tag: 0,
                        fields: vec![
                            (1, Pattern::Bind(updated)),
                            (1 + object_width, Pattern::Bind(extracted)),
                        ],
                    },
                    Block {
                        statements: vec![Statement::Expr(Expr {
                            kind: ExprKind::Assign(
                                slot,
                                Box::new(Expr {
                                    kind: ExprKind::Local(updated),
                                    ty: object,
                                    span,
                                    resource: None,
                                }),
                            ),
                            ty: Type::Unit,
                            span,
                            resource: None,
                        })],
                        tail: Some(Box::new(Expr {
                            kind: ExprKind::Local(extracted),
                            ty: result_ty,
                            span,
                            resource: None,
                        })),
                        ty: result_ty,
                    },
                )
            } else if let Some(reference) = writeback {
                let updated = self.temp(object, span)?;
                (
                    Pattern::Variant {
                        tag: 0,
                        fields: vec![
                            (1, Pattern::Bind(updated)),
                            (1 + object_width, Pattern::Bind(extracted)),
                        ],
                    },
                    Block {
                        statements: vec![Statement::Expr(Expr {
                            kind: ExprKind::RefWrite(
                                Box::new(reference),
                                Box::new(Expr {
                                    kind: ExprKind::Local(updated),
                                    ty: object,
                                    span,
                                    resource: None,
                                }),
                            ),
                            ty: Type::Unit,
                            span,
                            resource: None,
                        })],
                        tail: Some(Box::new(Expr {
                            kind: ExprKind::Local(extracted),
                            ty: result_ty,
                            span,
                            resource: None,
                        })),
                        ty: result_ty,
                    },
                )
            } else {
                (
                    Pattern::Variant {
                        tag: 0,
                        fields: vec![
                            (1, Pattern::Any),
                            (1 + object_width, Pattern::Bind(extracted)),
                        ],
                    },
                    Block {
                        statements: Vec::new(),
                        tail: Some(Box::new(Expr {
                            kind: ExprKind::Local(extracted),
                            ty: result_ty,
                            span,
                            resource: None,
                        })),
                        ty: result_ty,
                    },
                )
            };
            let block = Block {
                statements: vec![Statement::Let(tmp, call)],
                tail: Some(Box::new(Expr {
                    kind: ExprKind::Match(
                        Box::new(Expr {
                            kind: ExprKind::Local(tmp),
                            ty: tuple_ty,
                            span,
                            resource: None,
                        }),
                        vec![Arm {
                            pattern,
                            guard: None,
                            body: Expr {
                                kind: ExprKind::Block(arm_body),
                                ty: result_ty,
                                span,
                                resource: None,
                            },
                        }],
                    ),
                    ty: result_ty,
                    span,
                    resource: None,
                })),
                ty: result_ty,
            };
            let value = Expr {
                kind: ExprKind::Block(block),
                ty: result_ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let value = Expr {
            kind: ExprKind::Call(
                if receiver_mode == ReceiverMode::Shared {
                    Target::ObjectFunction {
                        function: dispatcher,
                        receiver: reference_slot.map(|(slot, _)| slot),
                        mutable: false,
                    }
                } else {
                    Target::Function(dispatcher)
                },
                values,
            ),
            ty: call_result_type(&signature),
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Build (or reuse) the checked dispatcher for one object method. The
    /// dispatcher takes the object union by value, matches its concrete
    /// alternative, and calls that impl's method. No vtable, erasure, or
    /// runtime allocation is introduced, and every alternative remains an
    /// ordinary checked function call.
    fn dynamic_dispatcher(
        &mut self,
        trait_id: BindingId,
        trait_arguments: &TraitArguments,
        name: &str,
        receiver_mode: ReceiverMode,
        span: Span,
    ) -> Result<(usize, Type)> {
        let key = (trait_id, trait_arguments.clone(), name.to_owned());
        if let Some(entry) = self.functions.dynamic_dispatch.get(&key) {
            return Ok(*entry);
        }
        let definition = self.functions.traits[&trait_id].clone();
        let method = definition
            .methods
            .get(name)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "trait '{}' has no method '{name}'",
                        self.resolution.bindings[trait_id].name
                    ),
                )
            })?
            .function;
        let object = self
            .types
            .dyn_objects
            .get(&(trait_id, trait_arguments.clone()))
            .copied()
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "internal error: trait object has no closed-world representation",
                )
            })?;
        let members = self.types.union_members(object);
        let mut substitution = crate::runtime_types::Subst::default();
        let mut consts = BTreeMap::new();
        let mut grades = BTreeMap::new();
        let mut effects = BTreeMap::new();
        insert_trait_arguments(
            self.resolution,
            &definition.generics,
            trait_arguments,
            &mut substitution,
            &mut consts,
            &mut grades,
            &mut effects,
        );
        substitution.consts = consts;
        substitution.grades = grades;
        substitution.effects = effects;
        substitution.self_projections = self
            .functions
            .object_associated
            .get(&(trait_id, trait_arguments.clone()))
            .cloned()
            .unwrap_or_default();
        let shared_receiver = receiver_mode == ReceiverMode::Shared;
        let mutable_receiver = receiver_mode == ReceiverMode::Mutable;
        let mut parameters = vec![object];
        let mut parameter_grades = vec![None];
        for parameter in &method.parameters[1..] {
            let (ty, grade) = split_grade(&parameter.ty);
            parameters.push(self.types.ty_in(ty, &substitution)?);
            parameter_grades.push(
                grade
                    .map(|grade| grades::evaluate(self.resolution, &substitution.grades, grade))
                    .transpose()?,
            );
        }
        let (result, result_grade) = result_contract(
            self.resolution,
            self.types,
            &substitution.grades,
            &method.result,
        )?;
        let result = self.types.ty_in(&result, &substitution)?;
        if result_grade.is_some_and(|grade| !grade.is_zero()) || self.linear_type(result) {
            return Err(Diagnostic::new(
                span,
                "a dynamic method cannot return an owning/exact-use @[1] contract; consume the object statically or return an ordinary or erased copyable value",
            ));
        }
        let result_erased = result_grade.is_some_and(Grade::is_zero);
        let method_value_type = if result_erased { Type::Unit } else { result };
        // A mutable dispatcher returns `(updated object, method result)` so the
        // caller can write the mutated object back into its direct local. Other
        // modes return the method result directly.
        let function_result = if mutable_receiver {
            self.types.tuple(vec![object, method_value_type], span)?
        } else {
            method_value_type
        };
        let mut locals = parameters
            .iter()
            .map(|ty| Local {
                ty: *ty,
                mutable: false,
                linear: false,
                grade: None,
                span,
            })
            .collect::<Vec<_>>();
        let mut total_effects = 0u8;
        let mut signatures = Vec::new();
        for member in &members {
            let Some(impl_methods) =
                self.functions
                    .trait_impls
                    .get(&(trait_id, trait_arguments.clone(), *member))
            else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' has no impl for method '{name}'",
                        self.types.name(*member)
                    ),
                ));
            };
            let Some(definition) = impl_methods.get(name) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' does not implement dynamic method '{name}'",
                        self.types.name(*member)
                    ),
                ));
            };
            let index = self.functions.instance(
                self.types,
                self.resolution,
                definition.binding,
                vec![],
                vec![],
                vec![],
                vec![],
                definition.impl_arguments,
                Some(span),
            )?;
            let signature = self.functions.signatures[index].clone();
            if signature.parameters.len() != parameters.len()
                || signature.parameters[1..] != parameters[1..]
                || signature.parameter_grades[1..] != parameter_grades[1..]
                || signature.result != result
                || signature.result_grade != result_grade
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' has a different ABI for method '{name}'; object-safe methods must have identical non-receiver parameter and result types and usage contracts across impls",
                        self.types.name(*member)
                    ),
                ));
            }
            total_effects |= signature.effects;
            signatures.push((index, *member));
        }
        let mut arms = Vec::new();
        for (tag, (index, member)) in signatures.into_iter().enumerate() {
            let payload = locals.len();
            locals.push(Local {
                ty: member,
                mutable: false,
                linear: false,
                grade: None,
                span,
            });
            let receiver_argument = if mutable_receiver {
                Expr {
                    kind: ExprKind::Borrow(payload),
                    ty: Type::RefMut(self.types.pointer(member)),
                    span,
                    resource: None,
                }
            } else if shared_receiver {
                Expr {
                    kind: ExprKind::Borrow(payload),
                    ty: Type::Ref(self.types.pointer(member)),
                    span,
                    resource: None,
                }
            } else {
                Expr {
                    kind: ExprKind::Local(payload),
                    ty: member,
                    span,
                    resource: None,
                }
            };
            let mut call_arguments = vec![receiver_argument];
            for (slot, ty) in parameters.iter().enumerate().skip(1) {
                call_arguments.push(
                    if crate::runtime_types::grade_erases(parameter_grades[slot]) {
                        // The dispatcher's own parameter is physically absent;
                        // never read its unmaterialized local.
                        Expr {
                            kind: ExprKind::Erased(*ty),
                            ty: *ty,
                            span,
                            resource: None,
                        }
                    } else {
                        Expr {
                            kind: ExprKind::Local(slot),
                            ty: *ty,
                            span,
                            resource: None,
                        }
                    },
                );
            }
            let method_call = Expr {
                kind: ExprKind::Call(Target::Function(index), call_arguments),
                ty: method_value_type,
                span,
                resource: None,
            };
            let body = if mutable_receiver {
                // The method must run before the mutated payload is read. Bind
                // its result in a hidden local, then build the tuple in the
                // required field order `(updated object, result)`.
                let result_slot = locals.len();
                locals.push(Local {
                    ty: method_value_type,
                    mutable: false,
                    linear: false,
                    grade: None,
                    span,
                });
                let updated_union = Expr {
                    kind: ExprKind::Coerce {
                        value: Box::new(Expr {
                            kind: ExprKind::Move(payload),
                            ty: member,
                            span,
                            resource: None,
                        }),
                        to: object,
                        coercion: Coercion::Inject { tag },
                    },
                    ty: object,
                    span,
                    resource: None,
                };
                let tuple_layout = function_result
                    .layout()
                    .expect("mutable dispatcher result is a tuple layout");
                Expr {
                    kind: ExprKind::Block(Block {
                        statements: vec![Statement::Let(result_slot, method_call)],
                        tail: Some(Box::new(Expr {
                            kind: ExprKind::Construct {
                                enum_id: tuple_layout,
                                tag: 0,
                                fields: vec![
                                    updated_union,
                                    Expr {
                                        kind: ExprKind::Local(result_slot),
                                        ty: method_value_type,
                                        span,
                                        resource: None,
                                    },
                                ],
                            },
                            ty: function_result,
                            span,
                            resource: None,
                        })),
                        ty: function_result,
                    }),
                    ty: function_result,
                    span,
                    resource: None,
                }
            } else {
                method_call
            };
            arms.push(Arm {
                pattern: Pattern::Type {
                    tag,
                    member,
                    inner: Box::new(Pattern::Bind(payload)),
                },
                guard: None,
                body,
            });
        }
        let scrutinee = Expr {
            kind: ExprKind::Local(0),
            ty: object,
            span,
            resource: None,
        };
        let body = Block {
            statements: Vec::new(),
            tail: Some(Box::new(Expr {
                kind: ExprKind::Match(Box::new(scrutinee), arms),
                ty: function_result,
                span,
                resource: None,
            })),
            ty: function_result,
        };
        let function = Function {
            name: format!(
                "<dyn {}::{}>",
                self.resolution.bindings[trait_id].name, name
            ),
            parameters: parameters.len(),
            closure: None,
            locals,
            result: function_result,
            body,
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: parameter_grades.clone(),
            result_grade: if mutable_receiver { None } else { result_grade },
            parameter_lifetimes: vec![None; parameters.len()],
            result_lifetime: None,
            lifetime_bounds: BTreeSet::new(),
        };
        let signature = Signature {
            binding: usize::MAX,
            name: function.name.clone(),
            parameters,
            result: function_result,
            effects: total_effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades,
            result_grade: if mutable_receiver { None } else { result_grade },
            parameter_lifetimes: vec![None; function.parameters],
            result_lifetime: None,
            lifetime_bounds: BTreeSet::new(),
            self_type: None,
            default_trait: None,
            associated_consts: BTreeMap::new(),
        };
        let index = self.functions.add_synthetic(signature, function)?;
        self.functions
            .dynamic_dispatch
            .insert(key, (index, method_value_type));
        Ok((index, method_value_type))
    }
    /// The trait-argument substitution of an inherited default method, if the
    /// method was materialized from a trait default. Generic method inference
    /// uses it to resolve trait parameters that appear in the declared
    /// signature, exactly like `Self`.
    fn default_method_substitution(
        &self,
        binding: BindingId,
        impl_arguments: Option<usize>,
    ) -> Option<crate::runtime_types::Subst> {
        let declared = self.functions.declared[&binding];
        let index = declared.default_specialization?;
        let (trait_id, _) = self.functions.default_specializations[index].clone();
        let definition = &self.functions.traits[&trait_id];
        let mut substitution = crate::runtime_types::Subst {
            self_type: self.functions.self_type_for(binding, impl_arguments),
            ..Default::default()
        };
        let arguments = self
            .functions
            .trait_arguments_for(binding, impl_arguments)
            .unwrap_or_default();
        let mut consts = BTreeMap::new();
        let mut grades = BTreeMap::new();
        let mut effects = BTreeMap::new();
        insert_trait_arguments(
            self.resolution,
            &definition.generics,
            &arguments,
            &mut substitution,
            &mut consts,
            &mut grades,
            &mut effects,
        );
        substitution.consts = consts;
        substitution.grades = grades;
        substitution.effects = effects;
        Some(substitution)
    }
    /// Lower one statically dispatched method call to an ordinary checked
    /// function call whose first argument is the receiver.
    #[allow(clippy::too_many_arguments)]
    fn invoke_method(
        &mut self,
        binding: BindingId,
        impl_arguments: Option<usize>,
        receiver_ast: &ast::Expr,
        receiver: Expr,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let f = self.functions.declared[&binding].ast;
        if f.parameters.len() != arguments.len() + 1 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count for method '{}': expected {}, found {}",
                    f.name,
                    f.parameters.len().saturating_sub(1),
                    arguments.len()
                ),
            ));
        }
        if explicit.is_some() && f.generics.is_empty() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "method '{}' is not generic: non-generic methods take no explicit type arguments",
                    f.name
                ),
            ));
        }
        let mut prechecked = None;
        let mut generic_arguments = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        if !f.generics.is_empty() {
            let pairs = f.parameters[1..]
                .iter()
                .zip(arguments)
                .filter(|(parameter, _)| !parameter.erased)
                .map(|(parameter, argument)| (&parameter.ty, argument))
                .collect::<Vec<_>>();
            let what = format!("method '{}'", f.name);
            let self_type = self.functions.self_type_for(binding, impl_arguments);
            let base = self.default_method_substitution(binding, impl_arguments);
            let hint = match expected {
                Some(expected) => Some((self.result_type_hint(&f.result)?, expected)),
                None => None,
            };
            let (types, grades, consts, effects, values) = self.infer(
                &f.generics,
                explicit,
                &pairs,
                hint.as_ref()
                    .map(|(declared, expected)| (declared, *expected)),
                true,
                self_type,
                base.as_ref(),
                &what,
                span,
            )?;
            generic_arguments = (types, grades, consts, effects);
            prechecked = Some(values.into_iter());
        }
        let index = self.functions.instance(
            self.types,
            self.resolution,
            binding,
            generic_arguments.0,
            generic_arguments.1,
            generic_arguments.2,
            generic_arguments.3,
            impl_arguments,
            Some(span),
        )?;
        let signature = self.functions.signatures[index].clone();
        self.require(signature.effects, span)?;
        let mut signature_types = signature.parameters.iter();
        let parameter_types = f
            .parameters
            .iter()
            .map(|parameter| {
                if parameter.erased {
                    None
                } else {
                    Some(*signature_types.next().expect("runtime parameter"))
                }
            })
            .collect::<Vec<_>>();
        let mut callee_binders = Vec::new();
        let mut callee_types = Vec::new();
        let mut callee_actuals = Vec::new();
        let mut diverges = false;
        let mut values = Vec::with_capacity(f.parameters.len());
        // The receiver occupies runtime position zero. If a later erased
        // logical parameter names it as a symbolic scalar, record that binder
        // exactly as `user_call` does for ordinary arguments.
        let receiver_type = parameter_types[0].expect("method receiver is not erased");
        let receiver_binder = self.resolution.binder(f.parameters[0].span).unwrap();
        if f.parameters[1..].iter().any(|later| {
            later.erased
                && !matches!(later.ty.kind, ast::TypeKind::Predicate(_))
                && type_references_binding(self.resolution, &later.ty, receiver_binder)
        }) {
            let actual = self.scalar_argument(receiver_ast, receiver_type, span)?;
            callee_binders.push(receiver_binder);
            callee_types.push(Term::Scalar(
                receiver_type.scalar_carrier().expect("scalar receiver"),
            ));
            callee_actuals.push(actual);
        }
        values.push(receiver);
        let mut checked_arguments = prechecked.map(|values| values.into_iter());
        for (offset, (parameter, evidence)) in f.parameters[1..].iter().zip(arguments).enumerate() {
            let position = offset + 1;
            if !parameter.erased {
                let ty = parameter_types[position].expect("runtime parameter");
                let binder = self.resolution.binder(parameter.span).unwrap();
                if !diverges
                    && let Some(carrier) = ty.scalar_carrier()
                    && f.parameters[position + 1..].iter().any(|later| {
                        later.erased
                            && !matches!(later.ty.kind, ast::TypeKind::Predicate(_))
                            && type_references_binding(self.resolution, &later.ty, binder)
                    })
                {
                    let actual = self.scalar_argument(evidence, ty, span)?;
                    callee_binders.push(binder);
                    callee_types.push(Term::Scalar(carrier));
                    callee_actuals.push(actual);
                }
                let value = match checked_arguments.as_mut() {
                    Some(values) => values
                        .next()
                        .expect("inferred method argument in runtime order"),
                    None => self.expr_expected(evidence, Some(ty))?,
                };
                diverges |= value.ty == Type::Never;
                values.push(value);
                continue;
            }
            if diverges {
                continue;
            }
            if matches!(parameter.ty.kind, ast::TypeKind::Predicate(_)) {
                let proposition = proposition_of(self.resolution, f, parameter)?;
                self.discharge(&proposition, &values, evidence, span)?;
            } else {
                self.discharge_kernel_call(
                    parameter,
                    evidence,
                    &mut callee_binders,
                    &mut callee_types,
                    &mut callee_actuals,
                    span,
                )?;
            }
        }
        let mut coerced = Vec::with_capacity(values.len());
        for (value, ty) in values.into_iter().zip(&signature.parameters) {
            diverges |= value.ty == Type::Never;
            coerced.push(self.coerce(value, *ty, span)?);
        }
        let ty = if diverges {
            Type::Never
        } else {
            call_result_type(&signature)
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Function(index), coerced),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Byte-buffer builtin with an already checked receiver.
    fn bytes_method(
        &mut self,
        op: BytesOp,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = match op {
            BytesOp::Len | BytesOp::Capacity | BytesOp::Copy | BytesOp::Clear => 0,
            BytesOp::Get | BytesOp::Push | BytesOp::PushReserved => 1,
            BytesOp::WithCapacity => {
                return Err(Diagnostic::new(
                    span,
                    "Bytes.with_capacity is constructed as Bytes.with_capacity(n), not as a method",
                ));
            }
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "this byte method expects {wanted} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        let first = if op.borrowed() {
            self.method_borrow(first)?
        } else {
            if first.ty != Type::Bytes {
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "this byte method consumes an owned Bytes value, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
            first
        };
        let effects = match op {
            BytesOp::Len | BytesOp::Capacity | BytesOp::Clear => 0,
            BytesOp::Get | BytesOp::PushReserved => PANIC,
            _ => ALLOC | PANIC,
        };
        self.require(effects, span)?;
        let mut values = vec![first];
        if matches!(op, BytesOp::Get | BytesOp::Push | BytesOp::PushReserved) {
            let value = self.expr_expected(&rest[0], Some(Type::I64))?;
            self.expect(value.ty, Type::I64, value.span)?;
            values.push(value);
        }
        let ty = match op {
            BytesOp::Len | BytesOp::Capacity | BytesOp::Get => Type::I64,
            _ => Type::Bytes,
        };
        let ty = if values.iter().any(|value| value.ty == Type::Never) {
            Type::Never
        } else {
            ty
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Bytes(op), values),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }

    /// Explicit integer and character builtins.
    fn int_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.int_call_with(None, name, explicit, arguments, expected, span)
    }
    /// Integer/Char builtin with an already checked first argument for method
    /// syntax. `first` is the receiver; `arguments` holds only the remaining
    /// source arguments. Evaluation order and target inference are unchanged.
    fn int_call_with(
        &mut self,
        first: Option<Expr>,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        use crate::int::{ArithOp, IntKind, IntOp};
        let first_count = usize::from(first.is_some());
        let arity = match name {
            "print_int" | "Int.convert" | "Int.try_convert" | "Int.truncate" | "Char.code"
            | "Char.from_code" => 1,
            _ => 2,
        };
        if first_count + arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} argument(s), found {}",
                    first_count + arguments.len()
                ),
            ));
        }
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let option = |c: &mut Self, payload: Type| -> Result<crate::runtime_types::OptionShape> {
            let id = c
                .resolution
                .slice_options
                .get(&(span.start, span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(span, format!("{name} requires Option<T> in scope"))
                })?;
            c.types.option(id, payload, span)
        };
        let int_arg =
            |c: &mut Self, arg: &ast::Expr, hint: Option<Type>| -> Result<(Expr, IntKind)> {
                let value = c.expr_expected(arg, hint)?;
                match value.ty.int_kind() {
                    Some(kind) => Ok((value, kind)),
                    None if value.ty == Type::Never => Ok((value, IntKind::I64)),
                    None => Err(Diagnostic::new(
                        arg.span,
                        format!(
                            "{name} expects an integer, found {}",
                            c.types.name(value.ty)
                        ),
                    )),
                }
            };
        let first_kind = |c: &Self, value: &Expr| -> Result<IntKind> {
            value.ty.int_kind().ok_or_else(|| {
                Diagnostic::new(
                    value.span,
                    format!(
                        "{name} expects an integer, found {}",
                        c.types.name(value.ty)
                    ),
                )
            })
        };
        match name {
            "print_int" => {
                let (value, kind) = int_arg(self, &arguments[0], None)?;
                self.require(IO | PANIC, span)?;
                return Ok(unit(
                    ExprKind::Call(Target::PrintInt(kind), vec![value]),
                    Type::Unit,
                ));
            }
            "Char.code" => {
                let value = match first {
                    Some(value) => value,
                    None => self.expr_expected(&arguments[0], Some(Type::Char))?,
                };
                self.expect(value.ty, Type::Char, value.span)?;
                let ty = Type::Int(IntKind::U32);
                if let Some(expected) = expected {
                    self.expect(ty, expected, span)?;
                }
                return Ok(unit(
                    ExprKind::Call(
                        Target::Int(IntOp::Convert, IntKind::U32, IntKind::U32),
                        vec![value],
                    ),
                    ty,
                ));
            }
            "Char.from_code" => {
                let (value, kind) =
                    int_arg(self, &arguments[first_count], Some(Type::Int(IntKind::U32)))?;
                if kind != IntKind::U32 {
                    return Err(Diagnostic::new(
                        arguments[first_count].span,
                        "Char.from_code expects a u32 code point",
                    ));
                }
                let shape = option(self, Type::Char)?;
                let op = IntOp::CharFromCode {
                    some_tag: shape.some_tag,
                    none_tag: shape.none_tag,
                };
                return Ok(unit(
                    ExprKind::Call(Target::Int(op, kind, kind), vec![value]),
                    shape.result,
                ));
            }
            _ => {}
        }
        // The target integer type comes from `::<T>` or the expected type.
        let explicit_target = match explicit {
            Some([ty]) => {
                let ty = self.ty(ty)?;
                Some(ty.int_kind().ok_or_else(|| {
                    Diagnostic::new(span, format!("{name} needs an integer type argument"))
                })?)
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    format!("{name} takes one type argument"),
                ));
            }
            None => None,
        };
        let optional = matches!(
            name,
            "Int.try_convert" | "Int.checked_add" | "Int.checked_sub" | "Int.checked_mul"
        );
        let expected_target = expected.and_then(|e| {
            if optional {
                e.layout()
                    .and_then(|id| self.types.enums[id].arguments.first().copied())
            } else {
                Some(e)
            }
        });
        if arity == 1 {
            let target = explicit_target
                .or_else(|| expected_target.and_then(Type::int_kind))
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!("{name} needs a target integer type: annotate the result or write {name}::<T>(...)"),
                    )
                })?;
            let (value, source) = match first {
                Some(value) => {
                    let kind = first_kind(self, &value)?;
                    (value, kind)
                }
                None => int_arg(self, &arguments[0], None)?,
            };
            let op = match name {
                "Int.convert" => {
                    if !source.fits_in(target) {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "Int.convert from {} to {} could lose information; use Int.try_convert (checked) or Int.truncate (wrapping)",
                                source.name(),
                                target.name()
                            ),
                        ));
                    }
                    IntOp::Convert
                }
                "Int.truncate" => IntOp::Truncate,
                _ => {
                    let shape = option(self, Type::int(target))?;
                    IntOp::TryConvert {
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    }
                }
            };
            let ty = match op {
                IntOp::TryConvert { .. } => option(self, Type::int(target))?.result,
                _ => Type::int(target),
            };
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(Target::Int(op, source, target), vec![value]),
                ty,
            ));
        }
        // Two-operand arithmetic: both operands share the result's kind.
        let hint = explicit_target
            .or_else(|| expected_target.and_then(Type::int_kind))
            .map(Type::int);
        let (left, right) = match first {
            Some(left) => {
                let kind = first_kind(self, &left)?;
                let (right, _) = int_arg(self, &arguments[0], Some(Type::int(kind)))?;
                (left, right)
            }
            None if is_int_literal(&arguments[0]) && !is_int_literal(&arguments[1]) => {
                let (right, kind) = int_arg(self, &arguments[1], hint)?;
                let (left, _) = int_arg(self, &arguments[0], Some(Type::int(kind)))?;
                (left, right)
            }
            None => {
                let (left, kind) = int_arg(self, &arguments[0], hint)?;
                let (right, _) = int_arg(self, &arguments[1], Some(Type::int(kind)))?;
                (left, right)
            }
        };
        let kind = self
            .same_int(left.ty, right.ty, span)?
            .int_kind()
            .unwrap_or(IntKind::I64);
        let arith = match name.rsplit('_').next() {
            Some("add") => ArithOp::Add,
            Some("sub") => ArithOp::Sub,
            Some("mul") => ArithOp::Mul,
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unknown integer builtin {name}"),
                ));
            }
        };
        let (op, ty) = if name.starts_with("Int.wrapping_") {
            (IntOp::Wrapping(arith), Type::int(kind))
        } else if name.starts_with("Int.saturating_") {
            (IntOp::Saturating(arith), Type::int(kind))
        } else {
            let shape = option(self, Type::int(kind))?;
            (
                IntOp::Checked(arith, shape.some_tag, shape.none_tag),
                shape.result,
            )
        };
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        Ok(unit(
            ExprKind::Call(Target::Int(op, kind, kind), vec![left, right]),
            ty,
        ))
    }
    /// Check one float-builtin operand. `first` is the already checked method
    /// receiver; otherwise the remaining source argument is checked with the
    /// target's kind as a literal hint.
    fn float_argument(
        &mut self,
        first: Option<Expr>,
        argument: Option<&ast::Expr>,
        hint: Option<crate::float::FloatKind>,
        name: &str,
    ) -> Result<(Expr, crate::float::FloatKind)> {
        let value = match first {
            Some(value) => value,
            None => {
                let argument = argument.expect("checked float builtin arity");
                self.expr_expected(argument, hint.map(Type::float))?
            }
        };
        match value.ty.float_kind() {
            Some(kind) => Ok((value, kind)),
            None if value.ty == Type::Never => Ok((value, crate::float::FloatKind::F64)),
            None => Err(Diagnostic::new(
                value.span,
                format!(
                    "{name} expects a floating-point value, found {}",
                    self.types.name(value.ty)
                ),
            )),
        }
    }
    /// Check the integer source of an integer -> float conversion.
    fn int_argument(
        &mut self,
        first: Option<Expr>,
        argument: Option<&ast::Expr>,
        name: &str,
    ) -> Result<(Expr, crate::int::IntKind)> {
        let value = match first {
            Some(value) => value,
            None => {
                let argument = argument.expect("checked int builtin arity");
                self.expr_expected(argument, None)?
            }
        };
        match value.ty.int_kind() {
            Some(kind) => Ok((value, kind)),
            None if value.ty == Type::Never => Ok((value, crate::int::IntKind::I64)),
            None => Err(Diagnostic::new(
                value.span,
                format!(
                    "{name} expects an integer, found {}",
                    self.types.name(value.ty)
                ),
            )),
        }
    }
    /// Explicit float builtins and conversions. Every operation is unary; the
    /// receiver form is checked before these arguments and appears first.
    fn float_call_with(
        &mut self,
        first: Option<Expr>,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        use crate::float::{FloatKind, FloatOp};
        let first_count = usize::from(first.is_some());
        if first_count + arguments.len() != 1 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects 1 argument, found {}",
                    first_count + arguments.len()
                ),
            ));
        }
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let option = |c: &mut Self, payload: Type| -> Result<crate::runtime_types::OptionShape> {
            let id = c
                .resolution
                .slice_options
                .get(&(span.start, span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(span, format!("{name} requires Option<T> in scope"))
                })?;
            c.types.option(id, payload, span)
        };
        // Fixed-result operations need no target annotation.
        let simple = match name {
            "Float.abs" => Some(FloatOp::Abs(FloatKind::F64)),
            "Float.sqrt" => Some(FloatOp::Sqrt(FloatKind::F64)),
            "Float.is_nan" => Some(FloatOp::IsNan(FloatKind::F64)),
            "Float.is_infinite" => Some(FloatOp::IsInfinite(FloatKind::F64)),
            "Float.is_finite" => Some(FloatOp::IsFinite(FloatKind::F64)),
            _ => None,
        };
        if let Some(base) = simple {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    format!("{name} takes no type arguments"),
                ));
            }
            let hint = expected.and_then(Type::float_kind);
            let (value, kind) = self.float_argument(first, arguments.first(), hint, name)?;
            let op = match base {
                FloatOp::Abs(_) => FloatOp::Abs(kind),
                FloatOp::Sqrt(_) => FloatOp::Sqrt(kind),
                FloatOp::IsNan(_) => FloatOp::IsNan(kind),
                FloatOp::IsInfinite(_) => FloatOp::IsInfinite(kind),
                FloatOp::IsFinite(_) => FloatOp::IsFinite(kind),
                _ => unreachable!(),
            };
            let ty = match op {
                FloatOp::IsNan(_) | FloatOp::IsInfinite(_) | FloatOp::IsFinite(_) => Type::Bool,
                _ => Type::float(kind),
            };
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(ExprKind::Call(Target::Float(op), vec![value]), ty));
        }
        if name == "print_float" {
            if explicit.is_some() {
                return Err(Diagnostic::new(span, "print_float takes no type arguments"));
            }
            let (value, kind) = self.float_argument(first, arguments.first(), None, name)?;
            self.require(IO | PANIC, span)?;
            return Ok(unit(
                ExprKind::Call(Target::PrintFloat(kind), vec![value]),
                Type::Unit,
            ));
        }
        if name == "Float.to_f64" {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    "Float.to_f64 takes no type arguments",
                ));
            }
            let hint = expected
                .and_then(Type::float_kind)
                .filter(|k| *k == FloatKind::F64);
            let (value, kind) = self.float_argument(first, arguments.first(), hint, name)?;
            if let Some(expected) = expected {
                self.expect(Type::float(FloatKind::F64), expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(Target::Float(FloatOp::ToF64(kind)), vec![value]),
                Type::float(FloatKind::F64),
            ));
        }
        if name == "Float.try_to_f32" {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    "Float.try_to_f32 takes no type arguments",
                ));
            }
            let (value, kind) = self.float_argument(first, arguments.first(), None, name)?;
            let shape = option(self, Type::float(FloatKind::F32))?;
            let ty = shape.result;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(
                    Target::Float(FloatOp::TryToF32 {
                        source: kind,
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    }),
                    vec![value],
                ),
                ty,
            ));
        }
        let explicit_kind = match explicit {
            Some([ty]) => Some(self.ty(ty)?),
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    format!("{name} takes one type argument"),
                ));
            }
            None => None,
        };
        if name == "Float.try_to_int" {
            if let Some(ty) = explicit_kind
                && ty.int_kind().is_none()
            {
                return Err(Diagnostic::new(
                    span,
                    "Float.try_to_int needs an integer type argument",
                ));
            }
            let target = explicit_kind
                .and_then(Type::int_kind)
                .or_else(|| {
                    expected.and_then(|e| {
                        e.layout()
                            .and_then(|id| self.types.enums[id].arguments.first().copied())
                            .and_then(Type::int_kind)
                    })
                })
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        "Float.try_to_int needs a target integer type: annotate the Option result or write Float.try_to_int::<i64>(...)",
                    )
                })?;
            let (value, source) = self.float_argument(first, arguments.first(), None, name)?;
            let shape = option(self, Type::int(target))?;
            let ty = shape.result;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(
                    Target::Float(FloatOp::TryToInt {
                        source,
                        target,
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    }),
                    vec![value],
                ),
                ty,
            ));
        }
        // Integer -> float forms choose their target float from `::<T>` or the
        // expected type.
        let target = explicit_kind
            .and_then(Type::float_kind)
            .or_else(|| expected.and_then(Type::float_kind))
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "{name} needs a target float type: annotate the result or write {name}::<f32|f64>(...)"
                    ),
                )
            })?;
        if let Some(ty) = explicit_kind
            && ty.float_kind().is_none()
        {
            return Err(Diagnostic::new(
                span,
                format!("{name} needs an f32 or f64 type argument"),
            ));
        }
        let (value, source) = self.int_argument(first, arguments.first(), name)?;
        let (op, ty) = match name {
            "Float.from_int" => {
                if source.bits() > target.mantissa_bits() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "Float.from_int cannot represent every {} value exactly in {}; use Float.try_from_int (checked at runtime) or Float.from_int_rounded (documented rounding)",
                            source.name(),
                            target.name()
                        ),
                    ));
                }
                (FloatOp::FromInt { source, target }, Type::float(target))
            }
            "Float.from_int_rounded" => (
                FloatOp::FromIntRounded { source, target },
                Type::float(target),
            ),
            "Float.try_from_int" => {
                let shape = option(self, Type::float(target))?;
                (
                    FloatOp::TryFromInt {
                        source,
                        target,
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    },
                    shape.result,
                )
            }
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unknown float builtin {name}"),
                ));
            }
        };
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        Ok(unit(ExprKind::Call(Target::Float(op), vec![value]), ty))
    }
    /// Checked UTF-8 text builtins. Construction is restricted to a literal or
    /// the fallible conversion from an owned byte buffer; arbitrary bytes are
    /// never treated as text without validation.
    fn string_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if explicit.is_some() {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        if name == "String.from" {
            if arguments.len() != 1 {
                return Err(Diagnostic::new(
                    span,
                    "String.from expects exactly one string literal",
                ));
            }
            let ast::ExprKind::String(text) = &arguments[0].kind else {
                return Err(Diagnostic::new(
                    arguments[0].span,
                    "String.from requires exactly one string literal; use String.from_utf8 for runtime bytes",
                ));
            };
            self.require(ALLOC | PANIC, span)?;
            let value = Expr {
                kind: ExprKind::BytesLiteral(text.as_bytes().to_vec()),
                ty: Type::String,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if arguments.is_empty() {
            return Err(Diagnostic::new(span, format!("{name} expects a receiver")));
        }
        let first = self.expr(&arguments[0])?;
        self.string_call_with(name, first, &arguments[1..], expected, span)
    }
    /// The checked receiver of a text builtin is already evaluated exactly
    /// once. `rest` contains only the remaining source arguments.
    fn string_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = if matches!(name, "String.from_utf8" | "String.bytes") {
            0
        } else if matches!(name, "String.byte_at" | "String.scalar_at") {
            1
        } else if name == "String.substr" {
            2
        } else {
            0
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {wanted} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        let borrowed = matches!(
            name,
            "String.len"
                | "String.scalar_len"
                | "String.byte_at"
                | "String.scalar_at"
                | "String.as_bytes"
                | "String.as_str"
                | "String.substr"
        );
        let first = if first.ty == Type::Never {
            return Ok(first);
        } else if borrowed {
            match first.ty {
                Type::Ref(p) if self.types.pointees[p] == Type::String => first,
                _ => {
                    return Err(Diagnostic::new(
                        first.span,
                        format!(
                            "{name} expects an immutable &String, found {}; borrow an owned local with &name",
                            self.types.name(first.ty)
                        ),
                    ));
                }
            }
        } else if name == "String.from_utf8" {
            if first.ty != Type::Bytes {
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "String.from_utf8 consumes an owned Bytes value, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
            first
        } else if name == "String.bytes" {
            if first.ty != Type::String {
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "String.bytes consumes an owned String, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
            first
        } else {
            return Err(Diagnostic::new(
                span,
                format!("unknown text builtin {name}"),
            ));
        };
        match name {
            "String.as_str" => self.text_view_from_expr(first, None, None, span, expected),
            "String.substr" => {
                self.text_view_from_expr(first, Some(&rest[0]), Some(&rest[1]), span, expected)
            }
            "String.len" | "String.scalar_len" => {
                let op = if name == "String.len" {
                    StringOp::Len
                } else {
                    StringOp::ScalarLen
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(op), vec![first]),
                    ty: Type::I64,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.byte_at" => {
                let index = self.expr_expected(&rest[0], Some(Type::I64))?;
                self.expect(index.ty, Type::I64, index.span)?;
                self.require(PANIC, span)?;
                let ty = if index.ty == Type::Never {
                    Type::Never
                } else {
                    Type::I64
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(StringOp::ByteAt), vec![first, index]),
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.scalar_at" => {
                let index = self.expr_expected(&rest[0], Some(Type::I64))?;
                self.expect(index.ty, Type::I64, index.span)?;
                let option = self
                    .resolution
                    .slice_options
                    .get(&(span.start, span.end))
                    .copied()
                    .ok_or_else(|| {
                        Diagnostic::new(span, "String.scalar_at requires Option<Char> in scope")
                    })?;
                let shape = self.types.option(option, Type::Char, span)?;
                let op = StringOp::ScalarAt {
                    some_tag: shape.some_tag,
                    none_tag: shape.none_tag,
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(op), vec![first, index]),
                    ty: shape.result,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.from_utf8" => {
                let (ty, shape) = self.types.result_type(Type::String, Type::Bytes, span)?;
                let op = StringOp::FromUtf8 {
                    ok_tag: shape.ok_tag,
                    err_tag: shape.err_tag,
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(op), vec![first]),
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.as_bytes" => {
                self.require(ALLOC | PANIC, span)?;
                let value = Expr {
                    kind: ExprKind::Call(Target::String(StringOp::AsBytes), vec![first]),
                    ty: Type::Bytes,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.bytes" => {
                let value = Expr {
                    kind: ExprKind::Call(Target::String(StringOp::IntoBytes), vec![first]),
                    ty: Type::Bytes,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            _ => Err(Diagnostic::new(
                span,
                format!("unknown text builtin {name}"),
            )),
        }
    }
    fn str_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if explicit.is_some() {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        if arguments.is_empty() {
            return Err(Diagnostic::new(span, format!("{name} expects a receiver")));
        }
        let first = self.expr(&arguments[0])?;
        self.str_call_with(name, first, &arguments[1..], expected, span)
    }
    /// The checked receiver of a borrowed text builtin is already evaluated
    /// exactly once. A text view is a copyable shared descriptor, so reads do
    /// not move it and the owner's loan stays governed by the binding's last
    /// use.
    fn str_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = match name {
            "Str.len" | "Str.scalar_len" | "Str.to_string" => 0,
            "Str.byte_at" | "Str.scalar_at" => 1,
            "Str.substr" => 2,
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unknown borrowed text builtin {name}"),
                ));
            }
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {wanted} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        if first.ty == Type::Never {
            return Ok(first);
        }
        if first.ty != Type::Str {
            return Err(Diagnostic::new(
                first.span,
                format!(
                    "{name} expects a borrowed &str text view, found {}; create one with String.as_str or String.substr",
                    self.types.name(first.ty)
                ),
            ));
        }
        if name == "Str.substr" {
            return self.text_view_from_expr(first, Some(&rest[0]), Some(&rest[1]), span, expected);
        }
        if name == "Str.to_string" {
            self.require(ALLOC | PANIC, span)?;
            let value = Expr {
                kind: ExprKind::Call(Target::Str(StrOp::ToString), vec![first]),
                ty: Type::String,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if name == "Str.len" || name == "Str.scalar_len" {
            let op = if name == "Str.len" {
                StrOp::Len
            } else {
                StrOp::ScalarLen
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Str(op), vec![first]),
                ty: Type::I64,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let index = self.expr_expected(&rest[0], Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        if name == "Str.byte_at" {
            self.require(PANIC, span)?;
            let ty = if index.ty == Type::Never {
                Type::Never
            } else {
                Type::I64
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Str(StrOp::ByteAt), vec![first, index]),
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let option = self
            .resolution
            .slice_options
            .get(&(span.start, span.end))
            .copied()
            .ok_or_else(|| Diagnostic::new(span, "Str.scalar_at requires Option<Char> in scope"))?;
        let shape = self.types.option(option, Type::Char, span)?;
        let op = StrOp::ScalarAt {
            some_tag: shape.some_tag,
            none_tag: shape.none_tag,
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Str(op), vec![first, index]),
            ty: shape.result,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    fn require(&self, effects: u8, span: Span) -> Result<()> {
        let missing = effects & !self.effects;
        if missing == 0 {
            return Ok(());
        }
        let names = [
            (IO, "io"),
            (ALLOC, "alloc"),
            (PANIC, "panic"),
            (SUSPEND, "suspend"),
        ]
        .into_iter()
        .filter_map(|(bit, name)| (missing & bit != 0).then_some(name))
        .collect::<Vec<_>>();
        Err(Diagnostic::new(
            span,
            format!(
                "operation requires effects {{{}}}; add them to the function signature",
                names.join(", ")
            ),
        ))
    }
    fn ty(&mut self, ty: &ast::Type) -> Result<Type> {
        let subst = crate::runtime_types::Subst {
            types: self.substitution.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effect_arguments.clone(),
            lifetimes: BTreeMap::new(),
            self_type: self.self_type,
            associated_types: BTreeMap::new(),
            projections: BTreeMap::new(),
            self_projections: BTreeMap::new(),
        };
        self.types.ty_in(ty, &subst)
    }
    /// Strip an outer result-transfer grade (through transparent aliases) for
    /// call-site inference. The grade itself is validated when the concrete
    /// instance is created, so no grade variables need to be bound here.
    fn result_type_hint(&self, ty: &ast::Type) -> Result<ast::Type> {
        let expanded = expand_result_aliases(self.resolution, self.types, ty)?;
        Ok(split_grade(&expanded).0.clone())
    }
    fn mask(&self, ty: Type) -> u64 {
        crate::runtime_types::mask_of(ty, &self.types.enums)
    }
    /// Normalized subtyping over variant sets, heterogeneous unions, and
    /// `Never`. Intersections are already eliminated during type lowering.
    fn subtype(&self, actual: Type, expected: Type) -> bool {
        self.types.subtype(actual, expected)
    }
    fn expect(&self, actual: Type, expected: Type, span: Span) -> Result<()> {
        if self.subtype(actual, expected) {
            return Ok(());
        }
        let mut message = format!(
            "type mismatch: expected {}, found {}",
            self.types.name(expected),
            self.types.name(actual)
        );
        if actual.layout().is_some()
            && actual.layout() == expected.layout()
            && self.mask(actual) & self.mask(expected) != 0
        {
            let extra = self.mask(actual) & !self.mask(expected);
            let missing = self.types.name(crate::runtime_types::refine(
                &self.types.enums,
                actual.layout().unwrap(),
                extra,
            ));
            message.push_str(&format!(" (the value may also be {missing})"));
        }
        Err(Diagnostic::new(span, message))
    }
    /// A subtype whose runtime representation is already identical: a variant
    /// mask can be typed as the full enum with no tag change.
    fn same_layout(&self, actual: Type, expected: Type) -> bool {
        self.types.same_representation(actual, expected)
            || (actual.layout().is_some()
                && actual.layout() == expected.layout()
                && self.subtype(actual, expected))
    }
    /// Insert the deterministic runtime conversion needed to use `value` as
    /// `expected`. Same-layout refinements stay narrow (no runtime work); atom
    /// injection and union repacking become explicit `Coerce` nodes.
    fn coerce(&mut self, value: Expr, expected: Type, span: Span) -> Result<Expr> {
        if value.ty == Type::Never || value.ty == expected {
            return Ok(value);
        }
        if self.types.is_structural(expected) {
            return self.coerce_struct(value, expected, span);
        }
        if !self.subtype(value.ty, expected) {
            self.expect(value.ty, expected, span)?;
            debug_assert!(false, "expect returned for a non-subtype");
        }
        if self.same_layout(value.ty, expected) {
            return Ok(value);
        }
        if matches!(value.ty, Type::Fn(_) | Type::Once(_))
            && matches!(expected, Type::Fn(_) | Type::Once(_))
        {
            return self.coerce_function(value, expected, span);
        }
        let Type::Union(target_id) = expected else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "internal error: no representation conversion from {} to {}",
                    self.types.name(value.ty),
                    self.types.name(expected)
                ),
            ));
        };
        let target_members = self.types.unions[target_id].members.clone();
        let coercion = if let Type::Union(source_id) = value.ty {
            let source_members = self.types.unions[source_id].members.clone();
            let mut map = Vec::with_capacity(source_members.len());
            for member in source_members {
                let Some(tag) = target_members.iter().position(|target| {
                    self.subtype(member, *target)
                        && self.union_member_representation_compatible(member, *target)
                }) else {
                    if target_members
                        .iter()
                        .any(|target| self.subtype(member, *target))
                    {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "repacking callable union alternative {} as {} would change its callable representation; bind it as an explicit 'once fn' value first",
                                self.types.name(member),
                                self.types.name(expected)
                            ),
                        ));
                    }
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "internal error: union member {} has no target alternative in {}",
                            self.types.name(member),
                            self.types.name(expected)
                        ),
                    ));
                };
                map.push(tag);
            }
            Coercion::Repack { map }
        } else {
            let Some(tag) = target_members
                .iter()
                .position(|target| self.subtype(value.ty, *target))
            else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "internal error: {} has no alternative in {}",
                        self.types.name(value.ty),
                        self.types.name(expected)
                    ),
                ));
            };
            // A callable atom may need its checked adapter (for example a pure
            // `fn` used in a `once fn` alternative, which needs a null-env
            // thunk). Adapt before injecting; a raw payload copy would change
            // the indirect-call ABI.
            let member = target_members[tag];
            let value = if Self::function_parts(value.ty).is_some()
                && Self::function_parts(member).is_some()
            {
                self.coerce_function(value, member, span)?
            } else {
                value
            };
            let ty = expected;
            return Ok(Expr {
                kind: ExprKind::Coerce {
                    value: Box::new(value),
                    to: expected,
                    coercion: Coercion::Inject { tag },
                },
                ty,
                span,
                resource: None,
            });
        };
        let ty = expected;
        Ok(Expr {
            kind: ExprKind::Coerce {
                value: Box::new(value),
                to: expected,
                coercion,
            },
            ty,
            span,
            resource: None,
        })
    }
    /// A checked width/row conversion into an anonymous structural record.
    /// Fields are matched by name, the target row is canonical (sorted), and
    /// omitted source fields are dropped by the runtime conversion. A nested
    /// representation change in a retained field is rejected explicitly: the
    /// supported fragment copies fields that already have the target
    /// representation, while width/order changes still require a real
    /// conversion. This is a deliberate limit, not a silent relabeling.
    fn coerce_struct(&mut self, value: Expr, expected: Type, span: Span) -> Result<Expr> {
        let coercion = self.struct_coercion(value.ty, expected, span, 0)?;
        Ok(Expr {
            kind: ExprKind::Coerce {
                value: Box::new(value),
                to: expected,
                coercion,
            },
            ty: expected,
            span,
            resource: None,
        })
    }
    /// Build the checked field mapping for a record-to-structural conversion.
    /// A retained field may itself need a nested structural conversion or an
    /// atom-to-union injection; union-to-union repacking is rejected because it
    /// needs its own control flow and should be written as an explicit field
    /// conversion. The depth budget keeps nested rows finite.
    fn struct_coercion(
        &mut self,
        source: Type,
        expected: Type,
        span: Span,
        depth: usize,
    ) -> Result<Coercion> {
        if depth >= 32 {
            return Err(Diagnostic::new(
                span,
                "structural field coercion nesting budget exhausted (32)",
            ));
        }
        let Some(target_row) = self.types.structural_row(expected) else {
            return Err(Diagnostic::new(
                span,
                "internal error: structural conversion target is not a structural record",
            ));
        };
        let Some(source_layout) = source.layout().filter(|id| self.types.enums[*id].record) else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: expected {}, found {}",
                    self.types.name(expected),
                    self.types.name(source)
                ),
            ));
        };
        let source_variant = self.types.enums[source_layout].variants[0].clone();
        if !self.subtype(source, expected) {
            for (name, target_ty) in &target_row {
                let Some(index) = source_variant.names.iter().position(|n| n == name) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot convert {} to {}: the source row has no field '{name}'",
                            self.types.name(source),
                            self.types.name(expected)
                        ),
                    ));
                };
                let source_ty = source_variant.fields[index];
                if !self.subtype(source_ty, *target_ty) {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot convert field '{name}' from {} to {} in structural record conversion",
                            self.types.name(source_ty),
                            self.types.name(*target_ty)
                        ),
                    ));
                }
            }
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot convert {} to {}: a width-erased field carries a linear obligation or changes a borrowed leaf",
                    self.types.name(source),
                    self.types.name(expected)
                ),
            ));
        }
        let mut kept = Vec::with_capacity(target_row.len());
        for (target_index, (name, target_ty)) in target_row.iter().enumerate() {
            let source_index = source_variant
                .names
                .iter()
                .position(|source| source == name)
                .expect("structural subtype has every target field");
            let source_ty = source_variant.fields[source_index];
            let nested = self.nested_field_coercion(source_ty, *target_ty, span, depth + 1)?;
            kept.push((target_index, source_index, nested));
        }
        let mut drops = Vec::new();
        for (source_index, source_ty) in source_variant.fields.iter().enumerate() {
            if target_row
                .iter()
                .any(|(name, _)| source_variant.names[source_index] == *name)
            {
                continue;
            }
            if crate::runtime_types::contains_linear(self.types, *source_ty) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot erase field '{}' of type {} through structural width subtyping: it carries a linear obligation that the target cannot consume",
                        source_variant.names[source_index],
                        self.types.name(*source_ty)
                    ),
                ));
            }
            drops.push((source_index, *source_ty));
        }
        drops.reverse();
        Ok(Coercion::Struct {
            source,
            kept,
            drops,
        })
    }
    /// A nested field conversion that stays inside the structural conversion's
    /// own representation. Only two cases need work: a nested structural row
    /// (recursive field mapping) and an atom injected into a union alternative.
    fn nested_field_coercion(
        &mut self,
        source: Type,
        target: Type,
        span: Span,
        depth: usize,
    ) -> Result<Option<Coercion>> {
        if self.same_layout(source, target) {
            return Ok(None);
        }
        if !self.subtype(source, target) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot convert field from {} to {}",
                    self.types.name(source),
                    self.types.name(target)
                ),
            ));
        }
        if self.types.is_structural(target) {
            return Ok(Some(self.struct_coercion(source, target, span, depth)?));
        }
        let Type::Union(target_id) = target else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "structural field would need an unsupported nested representation change from {} to {}; convert the field explicitly before the structural coercion",
                    self.types.name(source),
                    self.types.name(target)
                ),
            ));
        };
        let target_members = self.types.unions[target_id].members.clone();
        if let Type::Union(source_id) = source {
            let source_members = self.types.unions[source_id].members.clone();
            let mut map = Vec::with_capacity(source_members.len());
            for member in source_members {
                let Some(tag) = target_members.iter().position(|target| {
                    self.subtype(member, *target)
                        && self.union_member_representation_compatible(member, *target)
                }) else {
                    if target_members
                        .iter()
                        .any(|target| self.subtype(member, *target))
                    {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "nested union field conversion from {} to {} would change a callable representation; adapt the field explicitly first",
                                self.types.name(source),
                                self.types.name(target)
                            ),
                        ));
                    }
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "internal error: nested union member {} has no target alternative in {}",
                            self.types.name(member),
                            self.types.name(target)
                        ),
                    ));
                };
                map.push(tag);
            }
            return Ok(Some(Coercion::Repack { map }));
        }
        let Some(tag) = target_members
            .iter()
            .position(|member| self.subtype(source, *member))
        else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "internal error: field {} has no alternative in {}",
                    self.types.name(source),
                    self.types.name(target)
                ),
            ));
        };
        if Self::function_parts(source).is_some()
            && Self::function_parts(target_members[tag]).is_some()
        {
            return Err(Diagnostic::new(
                span,
                "a callable field cannot be converted to a union alternative inside a structural coercion; adapt the field explicitly first",
            ));
        }
        Ok(Some(Coercion::Inject { tag }))
    }
    /// Whether a union-to-union repack can copy a member's payload words
    /// directly. Callable members may only cross when the calling convention
    /// and parameter/result representations are identical.
    fn union_member_representation_compatible(&self, source: Type, target: Type) -> bool {
        match (Self::function_parts(source), Self::function_parts(target)) {
            (Some((source_id, source_once)), Some((target_id, target_once))) => {
                source_once == target_once && {
                    let source = &self.types.function_types[source_id];
                    let target = &self.types.function_types[target_id];
                    !self.arrow_rep_change(source, target)
                }
            }
            (None, None) => true,
            _ => false,
        }
    }
    /// Coerce a value-position block to a join type, synthesizing a unit tail
    /// when a `Unit` branch must be injected into a union.
    fn coerce_block(&mut self, mut block: Block, target: Type, span: Span) -> Result<Block> {
        if block.ty == Type::Never || self.same_layout(block.ty, target) {
            return Ok(block);
        }
        if !self.subtype(block.ty, target) {
            self.expect(block.ty, target, span)?;
        }
        let tail = match block.tail.take() {
            Some(tail) => *tail,
            None => Expr {
                kind: ExprKind::Constant(0),
                ty: Type::Unit,
                span,
                resource: None,
            },
        };
        let tail = self.coerce(tail, target, span)?;
        block.tail = Some(Box::new(tail));
        block.ty = target;
        Ok(block)
    }
    /// Whether a union alternative may be narrowed to `requested` by copying
    /// its payload words. Enum variant masks share a layout; callable
    /// alternatives require the same calling convention and identical
    /// parameter/result representations, because a pattern has no place to
    /// insert an adapter.
    fn narrow_representation_compatible(&self, member: Type, requested: Type) -> bool {
        if self.same_layout(member, requested) {
            return true;
        }
        match (member, requested) {
            (Type::Fn(a), Type::Fn(b)) | (Type::Once(a), Type::Once(b)) => {
                let source = &self.types.function_types[a];
                let target = &self.types.function_types[b];
                !self.arrow_rep_change(source, target)
            }
            _ => false,
        }
    }
    /// Split a callable type into its signature table index and call mode.
    fn function_parts(ty: Type) -> Option<(usize, bool)> {
        match ty {
            Type::Fn(id) => Some((id, false)),
            Type::Once(id) => Some((id, true)),
            _ => None,
        }
    }
    /// The underlying static function index of a function value, through a
    /// checked coercion wrapper. Used to validate task-body result obligations.
    fn callable_function(expr: &Expr) -> Option<usize> {
        match &expr.kind {
            ExprKind::FnValue { function, .. } => Some(*function),
            ExprKind::Coerce { value, .. } => Self::callable_function(value),
            _ => None,
        }
    }
    /// Whether moving between these arrow types changes the word
    /// representation of an argument or result. Such conversions require a
    /// checked adapter; same-layout variance needs no runtime work.
    ///
    /// Grade-zero parameters are physically absent. A `@[0]` source parameter
    /// used where a non-erased contract is expected (or the reverse) therefore
    /// changes the calling convention even when the logical parameter lists
    /// are identical. Treating that as a raw compatible cast would shift every
    /// later argument.
    fn arrow_rep_change(&self, source: &FunctionType, target: &FunctionType) -> bool {
        if source.parameters.len() != target.parameters.len() {
            return true;
        }
        let mut rep_change = false;
        for index in 0..source.parameters.len() {
            let source_erased = source.parameter_erased(index);
            let target_erased = target.parameter_erased(index);
            if source_erased != target_erased
                || (!source_erased
                    && !self.same_layout(source.parameters[index], target.parameters[index]))
            {
                rep_change = true;
            }
        }
        let source_result_erased = crate::runtime_types::grade_erases(source.result_grade);
        let target_result_erased = crate::runtime_types::grade_erases(target.result_grade);
        if source_result_erased != target_result_erased
            || (!source_result_erased && !self.same_layout(source.result, target.result))
        {
            rep_change = true;
        }
        rep_change
    }
    /// Coerce a function value to a supertype. Pure-to-once is a null-env
    /// padding operation with no allocation. Representation-changing variance
    /// is compiled to a checked adapter function, never a function-pointer cast.
    fn coerce_function(&mut self, value: Expr, expected: Type, span: Span) -> Result<Expr> {
        let actual = value.ty;
        let (Some((source_id, source_once)), Some((target_id, target_once))) =
            (Self::function_parts(actual), Self::function_parts(expected))
        else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: expected {}, found {}",
                    self.types.name(expected),
                    self.types.name(actual)
                ),
            ));
        };
        let source = self.types.function_types[source_id].clone();
        let target = self.types.function_types[target_id].clone();
        let rep_change = self.arrow_rep_change(&source, &target);
        if !source_once && target_once {
            // A once callable has a different calling convention (an
            // environment argument). A static pure source is wrapped by a
            // no-allocation thunk that ignores the null environment; a dynamic
            // pure source is captured by an allocating once adapter.
            if let ExprKind::FnValue { function, captures } = &value.kind
                && captures.is_empty()
            {
                let function = *function;
                let adapted = if rep_change {
                    let pure = self.pure_adapter(function, target_id, span)?;
                    let ExprKind::FnValue { function, captures } = pure.kind else {
                        unreachable!("pure adapter is a function value")
                    };
                    debug_assert!(captures.is_empty());
                    function
                } else {
                    function
                };
                return self.once_thunk(adapted, target_id, span);
            }
            return self.closure_adapter(value, target_id, span);
        }
        if !rep_change {
            let mut value = value;
            value.ty = expected;
            return Ok(value);
        }
        if source_once {
            return self.closure_adapter(value, target_id, span);
        }
        if let ExprKind::FnValue { function, captures } = &value.kind
            && captures.is_empty()
        {
            return self.pure_adapter(*function, target_id, span);
        }
        Err(Diagnostic::new(
            span,
            "representation-changing conversion of a dynamic pure function value would need a capturing adapter; bind it with an explicit 'once fn' type or use a direct function name",
        ))
    }
    /// Reject an adapter whose body allocates but whose arrow effect row does
    /// not expose `alloc`/`panic`.
    fn check_adapter_effects(
        &self,
        body: &Block,
        signature: &FunctionType,
        span: Span,
    ) -> Result<()> {
        if block_allocates(body) && signature.effects & (ALLOC | PANIC) != ALLOC | PANIC {
            return Err(Diagnostic::new(
                span,
                "this function-value conversion needs a capturing adapter; add 'alloc' and 'panic' to the target arrow effect row",
            ));
        }
        Ok(())
    }
    /// Register a synthetic adapter body with a checked callable signature.
    #[allow(clippy::too_many_arguments)]
    fn register_adapter(
        &mut self,
        name: &str,
        signature: &FunctionType,
        capture_types: Vec<Type>,
        env_parameter: bool,
        locals: Vec<Local>,
        body: Block,
        span: Span,
    ) -> Result<usize> {
        let captures = capture_types.len();
        let mut parameter_grades = vec![None; captures];
        parameter_grades.extend(signature.parameter_grades.iter().copied());
        // The adapter is checked against the callable's borrow contract, like
        // a named function with the same explicit lifetimes.
        let mut parameter_lifetimes = vec![None; captures];
        parameter_lifetimes.extend(
            (0..signature.parameters.len())
                .map(|i| signature.borrows.parameters.get(i).cloned().flatten()),
        );
        let function = Function {
            name: name.to_owned(),
            parameters: captures + signature.parameters.len(),
            closure: (captures != 0)
                .then_some(captures)
                .or(env_parameter.then_some(0)),
            locals,
            result: signature.result,
            body,
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades,
            result_grade: signature.result_grade,
            parameter_lifetimes: parameter_lifetimes.clone(),
            result_lifetime: signature.borrows.result.clone(),
            lifetime_bounds: signature.borrows.bounds.clone(),
        };
        let synthetic = Signature {
            associated_consts: BTreeMap::new(),
            binding: usize::MAX,
            name: name.to_owned(),
            parameters: signature.parameters.clone(),
            result: signature.result,
            effects: signature.effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades: signature.parameter_grades.clone(),
            result_grade: signature.result_grade,
            parameter_lifetimes: parameter_lifetimes[captures..].to_vec(),
            result_lifetime: signature.borrows.result.clone(),
            lifetime_bounds: signature.borrows.bounds.clone(),
            self_type: None,
            default_trait: None,
        };
        self.functions.add_synthetic(synthetic, function)
    }
    /// A pure, noncapturing adapter for a statically known source function.
    /// It has the target parameter/result representation and directly calls the
    /// source, applying only checked value coercions.
    fn pure_adapter(&mut self, source: usize, target_id: usize, span: Span) -> Result<Expr> {
        let key = (Some(source), Type::Fn(0), Type::Fn(target_id));
        if let Some(index) = self.functions.adapter_cache.get(&key).copied() {
            return Ok(Expr {
                kind: ExprKind::FnValue {
                    function: index,
                    captures: vec![],
                },
                ty: Type::Fn(target_id),
                span,
                resource: None,
            });
        }
        let target = self.types.function_types[target_id].clone();
        let source_signature = self.functions.signatures[source].clone();
        let locals = target
            .parameters
            .iter()
            .map(|ty| Local {
                ty: *ty,
                mutable: false,
                linear: false,
                grade: None,
                span,
            })
            .collect::<Vec<_>>();
        let mut arguments = Vec::with_capacity(target.parameters.len());
        for (index, (target_parameter, source_parameter)) in target
            .parameters
            .iter()
            .zip(&source_signature.parameters)
            .enumerate()
        {
            if target.parameter_erased(index) || source_signature.parameter_erased(index) {
                // One side of this conversion has no physical slot. The
                // adapter must not read an unmaterialized local or treat the
                // value as ABI-compatible; the erased position is evaluated as
                // a dummy and dropped by the callee's own erasure.
                arguments.push(Expr {
                    kind: ExprKind::Erased(*source_parameter),
                    ty: *source_parameter,
                    span,
                    resource: None,
                });
                continue;
            }
            let argument = Expr {
                kind: ExprKind::Local(index),
                ty: *target_parameter,
                span,
                resource: None,
            };
            arguments.push(self.coerce(argument, *source_parameter, span)?);
        }
        let erased_result = crate::runtime_types::grade_erases(source_signature.result_grade);
        let call = Expr {
            kind: ExprKind::Call(Target::Function(source), arguments),
            ty: if erased_result {
                Type::Unit
            } else {
                source_signature.result
            },
            span,
            resource: None,
        };
        let result = if erased_result {
            call
        } else {
            self.coerce(call, target.result, span)?
        };
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(result)),
            ty: if crate::runtime_types::grade_erases(target.result_grade) {
                Type::Unit
            } else {
                target.result
            },
        };
        self.check_adapter_effects(&body, &target, span)?;
        let pure_id = self.types.function_type_with(
            target.parameters.clone(),
            target.result,
            target.effects,
            target.parameter_grades.clone(),
            target.result_grade,
            false,
            false,
            target.borrows.clone(),
        );
        let index =
            self.register_adapter("fn adapter", &target, vec![], false, locals, body, span)?;
        self.functions.adapter_cache.insert(key, index);
        Ok(Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![],
            },
            ty: Type::Fn(pure_id),
            span,
            resource: None,
        })
    }
    /// A no-allocation once-callable thunk for a statically known pure source.
    /// The once ABI passes an environment word; this wrapper ignores it and
    /// directly calls the source function.
    fn once_thunk(&mut self, source: usize, target_id: usize, span: Span) -> Result<Expr> {
        let key = (Some(source), Type::Once(0), Type::Fn(target_id));
        if let Some(index) = self.functions.adapter_cache.get(&key).copied() {
            return Ok(Expr {
                kind: ExprKind::FnValue {
                    function: index,
                    captures: vec![],
                },
                ty: Type::Once(target_id),
                span,
                resource: None,
            });
        }
        let target = self.types.function_types[target_id].clone();
        let source_signature = self.functions.signatures[source].clone();
        let locals = target
            .parameters
            .iter()
            .map(|ty| Local {
                ty: *ty,
                mutable: false,
                linear: false,
                grade: None,
                span,
            })
            .collect::<Vec<_>>();
        let mut arguments = Vec::with_capacity(target.parameters.len());
        for (index, (target_parameter, source_parameter)) in target
            .parameters
            .iter()
            .zip(&source_signature.parameters)
            .enumerate()
        {
            if target.parameter_erased(index) || source_signature.parameter_erased(index) {
                // One side of this conversion has no physical slot. The
                // adapter must not read an unmaterialized local or treat the
                // value as ABI-compatible; the erased position is evaluated as
                // a dummy and dropped by the callee's own erasure.
                arguments.push(Expr {
                    kind: ExprKind::Erased(*source_parameter),
                    ty: *source_parameter,
                    span,
                    resource: None,
                });
                continue;
            }
            let argument = Expr {
                kind: ExprKind::Local(index),
                ty: *target_parameter,
                span,
                resource: None,
            };
            arguments.push(self.coerce(argument, *source_parameter, span)?);
        }
        let erased_result = crate::runtime_types::grade_erases(source_signature.result_grade);
        let call = Expr {
            kind: ExprKind::Call(Target::Function(source), arguments),
            ty: if erased_result {
                Type::Unit
            } else {
                source_signature.result
            },
            span,
            resource: None,
        };
        let result = if erased_result {
            call
        } else {
            self.coerce(call, target.result, span)?
        };
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(result)),
            ty: if crate::runtime_types::grade_erases(target.result_grade) {
                Type::Unit
            } else {
                target.result
            },
        };
        self.check_adapter_effects(&body, &target, span)?;
        let index =
            self.register_adapter("once fn thunk", &target, vec![], true, locals, body, span)?;
        self.functions.adapter_cache.insert(key, index);
        Ok(Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![],
            },
            ty: Type::Once(target_id),
            span,
            resource: None,
        })
    }
    /// A once-consuming capturing adapter. The source callable is moved into
    /// the closure environment exactly once; a call consumes it and the
    /// callee's normal cleanup drops any remaining captures.
    fn closure_adapter(&mut self, value: Expr, target_id: usize, span: Span) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        let target = self.types.function_types[target_id].clone();
        let source_ty = value.ty;
        let (source_id, _) = Self::function_parts(source_ty).expect("checked callable");
        let source = self.types.function_types[source_id].clone();
        let mut locals = vec![Local {
            ty: source_ty,
            mutable: false,
            linear: false,
            grade: None,
            span,
        }];
        locals.extend(target.parameters.iter().map(|ty| Local {
            ty: *ty,
            mutable: false,
            linear: false,
            grade: None,
            span,
        }));
        let callee = Expr {
            kind: ExprKind::Local(0),
            ty: source_ty,
            span,
            resource: None,
        };
        let mut arguments = Vec::with_capacity(target.parameters.len());
        for (index, (target_parameter, source_parameter)) in
            target.parameters.iter().zip(&source.parameters).enumerate()
        {
            if target.parameter_erased(index) || source.parameter_erased(index) {
                arguments.push(Expr {
                    kind: ExprKind::Erased(*source_parameter),
                    ty: *source_parameter,
                    span,
                    resource: None,
                });
                continue;
            }
            let argument = Expr {
                kind: ExprKind::Local(index + 1),
                ty: *target_parameter,
                span,
                resource: None,
            };
            arguments.push(self.coerce(argument, *source_parameter, span)?);
        }
        let erased_result = crate::runtime_types::grade_erases(source.result_grade);
        let call = Expr {
            kind: ExprKind::CallIndirect {
                callee: Box::new(callee),
                arguments,
            },
            ty: if erased_result {
                Type::Unit
            } else {
                source.result
            },
            span,
            resource: None,
        };
        let result = if erased_result {
            call
        } else {
            self.coerce(call, target.result, span)?
        };
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(result)),
            ty: if crate::runtime_types::grade_erases(target.result_grade) {
                Type::Unit
            } else {
                target.result
            },
        };
        self.check_adapter_effects(&body, &target, span)?;
        let index = self.register_adapter(
            "once fn adapter",
            &target,
            vec![source_ty],
            false,
            locals,
            body,
            span,
        )?;
        Ok(Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![value],
            },
            ty: Type::Once(target_id),
            span,
            resource: None,
        })
    }
    /// Least upper bound for branch results: a normalized algebraic union.
    fn join(&mut self, left: Type, right: Type, span: Span) -> Result<Type> {
        if left == Type::Never {
            return Ok(right);
        }
        if right == Type::Never {
            return Ok(left);
        }
        self.types.union(vec![left, right], span)
    }
    fn local_name(&self, slot: usize) -> String {
        self.slots.iter().find(|(_, s)| **s == slot).map_or_else(
            || format!("_{slot}"),
            |(id, _)| self.resolution.bindings[*id].name.clone(),
        )
    }
    /// An erased proof parameter. Arithmetic `{ ... }` parameters become
    /// difference-constraint facts; other parameters elaborate to an open
    /// logical type relative to earlier erased kernel binders and are checked
    /// by the trusted kernel.
    fn assume_parameter(&mut self, parameter: &ast::Parameter) -> Result<()> {
        let id = self.resolution.binder(parameter.span).unwrap();
        if !matches!(parameter.ty.kind, ast::TypeKind::Predicate(_)) {
            let bindings = self.kernel_bindings();
            let ty = crate::check::elaborate_type(
                self.resolution,
                self.logical,
                &bindings,
                &parameter.ty,
            )
            .map_err(|e| {
                Diagnostic::new(
                    e.span,
                    format!(
                        "erased parameters must be arithmetic '{{ ... }}' propositions or logical types with checked dependencies: {}",
                        e.message
                    ),
                )
            })?;
            let context = self.kernel_context();
            self.logical.kernel.sort_open(&ty, &context).map_err(|e| {
                Diagnostic::new(
                    parameter.ty.span,
                    format!("invalid erased logical parameter: {e}"),
                )
            })?;
            // A hypothesis type is interpreted in the prefix of binders before
            // its own position, so appending a later binder does not change its
            // de Bruijn indices. The elaborated type is stored as-is.
            self.kernel_proofs.insert(id, ty.clone());
            self.kernel_types.insert(id, ty);
            self.kernel_locals.push(id);
            return Ok(());
        }
        let proposition = self.functions.proposition(self.resolution, parameter)?;
        let mut constraints = Vec::new();
        let params = self.parameter_slots();
        for (l, lc, op, r, rc) in &proposition.atoms {
            let term = |t: &crate::facts::ParamTerm, c: i128| {
                use crate::facts::{Linear, ParamTerm, Term};
                match t {
                    ParamTerm::Zero => Linear(Term::Zero, c),
                    ParamTerm::Param(i) => Linear(Term::Var(params[*i], 0), c),
                    ParamTerm::Len(i) => Linear(Term::Len(params[*i], 0), c),
                }
            };
            crate::facts::compare(term(l, *lc), op, term(r, *rc), &mut constraints);
        }
        self.facts.add(constraints);
        self.proofs.insert(id, proposition);
        Ok(())
    }
    /// Slots of runtime parameters, in order (they are the first locals).
    fn parameter_slots(&self) -> Vec<usize> {
        (0..self.locals.len()).collect()
    }
    /// Prove a callee's erased precondition for the given runtime arguments.
    fn discharge(
        &mut self,
        proposition: &crate::facts::Proposition,
        arguments: &[Expr],
        evidence: &ast::Expr,
        span: Span,
    ) -> Result<()> {
        use crate::facts::{Constraint, Linear, ParamTerm, Term};
        match &evidence.kind {
            ast::ExprKind::Name(name) if name == "_" => {}
            ast::ExprKind::Name(_)
                if self
                    .resolution
                    .reference(evidence.span)
                    .is_some_and(|id| self.proofs.contains_key(&id)) => {}
            _ => {
                return Err(Diagnostic::new(
                    evidence.span,
                    "an erased argument must be '_' (prove from context) or the name of an erased proof parameter",
                ));
            }
        }
        let mut goals: Vec<Constraint> = Vec::new();
        for (l, lc, op, r, rc) in &proposition.atoms {
            let term = |t: &ParamTerm, c: i128| -> Result<Linear> {
                Ok(match t {
                    ParamTerm::Zero => Linear(Term::Zero, c),
                    ParamTerm::Param(i) => {
                        let Linear(t, k) = self.facts.linear(&arguments[*i]).ok_or_else(|| {
                            Diagnostic::new(
                                arguments[*i].span,
                                "this argument appears in a proof obligation; use a local, a constant, or 'local + constant'",
                            )
                        })?;
                        Linear(t, k + c)
                    }
                    ParamTerm::Len(i) => {
                        let slot = crate::facts::owner_slot(&arguments[*i]).ok_or_else(|| {
                            Diagnostic::new(
                                arguments[*i].span,
                                "pass a named buffer here so its length can appear in a proof obligation",
                            )
                        })?;
                        Linear(Term::Len(slot, self.facts.version(slot)), c)
                    }
                })
            };
            crate::facts::compare(term(l, *lc)?, op, term(r, *rc)?, &mut goals);
        }
        for goal in goals {
            let Some(steps) = self.facts.prove(goal) else {
                let known = self.facts.snapshot(goal);
                let names = (0..self.locals.len())
                    .map(|s| self.local_name(s))
                    .collect::<Vec<_>>();
                return Err(crate::facts::failure(
                    span,
                    &proposition.text,
                    &known,
                    &|slot| names[slot].clone(),
                ));
            };
            let hypotheses = self.facts.snapshot(goal);
            self.functions.certificates.push(crate::facts::Certificate {
                span,
                obligation: proposition.text.clone(),
                goal,
                steps,
                hypotheses,
            });
        }
        Ok(())
    }
    /// All kernel binders in scope order, each paired with its hypothesis type.
    fn kernel_bindings(&self) -> Vec<(BindingId, Term)> {
        self.kernel_locals
            .iter()
            .map(|id| (*id, self.kernel_types[id].clone()))
            .collect()
    }
    fn kernel_context(&self) -> Vec<Term> {
        self.kernel_locals
            .iter()
            .map(|id| self.kernel_types[id].clone())
            .collect()
    }
    /// Alias bindings in the form the evidence elaborator uses: an alias name
    /// resolves to the binder that was copied at its binding site.
    fn kernel_alias_sources(&self) -> BTreeMap<BindingId, usize> {
        self.kernel_aliases
            .iter()
            .filter(|(_, position)| **position < self.kernel_locals.len())
            .map(|(alias, position)| (*alias, *position))
            .collect()
    }
    /// Admit a runtime scalar binding as a symbolic kernel index. Mutable
    /// bindings are admitted at their current version; [`Self::renew_scalar_index`]
    /// appends a fresh binder on assignment. The mutable local itself is never
    /// a stable proof object: proofs are erased, cannot be bound to runtime
    /// locals, and each use translates the *current* version at its call site.
    fn admit_scalar_index(&mut self, id: BindingId, ty: Type, _span: Span) -> Result<()> {
        if let Some(carrier) = ty.scalar_carrier() {
            self.kernel_types.insert(id, Term::Scalar(carrier));
            self.kernel_locals.push(id);
            self.scalar_epochs.insert(id, 0);
        }
        Ok(())
    }

    /// Record that a mutable scalar local was assigned. Every stored kernel
    /// proof type is shifted to keep its old outer hypotheses at the same
    /// binding, then a fresh binder for the new value is appended. The de
    /// Bruijn shift is essential: growing the context at the nearest end must
    /// not reinterpret an earlier `Eq<i64, n, n>` as a different variable.
    fn renew_scalar_index(&mut self, slot: usize) -> Result<()> {
        let ty = self.locals[slot].ty;
        let Some(carrier) = ty.scalar_carrier() else {
            return Ok(());
        };
        let Some(id) = self
            .slots
            .iter()
            .find_map(|(id, candidate)| (*candidate == slot).then_some(*id))
        else {
            return Ok(());
        };
        let _ = self.locals[slot].span;
        self.kernel_aliases.remove(&id);
        self.kernel_types.insert(id, Term::Scalar(carrier));
        self.kernel_locals.push(id);
        *self.scalar_epochs.entry(id).or_insert(0) += 1;
        Ok(())
    }
    /// The current absolute position of a symbolic scalar binder. An alias
    /// resolves to the position that was copied at its binding site.
    fn kernel_position(&self, id: BindingId) -> Option<usize> {
        if let Some(position) = self.kernel_aliases.get(&id) {
            return Some(*position);
        }
        self.kernel_locals.iter().rposition(|local| *local == id)
    }
    /// Record that `id` is a by-value scalar copy of the current version of
    /// `source`. The alias keeps the source's evaluation-point binder instead
    /// of introducing a fresh unconstrained index.
    fn alias_scalar_index(&mut self, id: BindingId, source: BindingId) -> bool {
        let Some(position) = self.kernel_position(source) else {
            return false;
        };
        self.kernel_aliases.insert(id, position);
        true
    }
    /// The de Bruijn term for an in-scope symbolic runtime scalar local. The
    /// innermost binder wins, matching lexical shadowing and captures.
    fn kernel_local_term(&self, id: BindingId) -> Option<Term> {
        let position = self.kernel_position(id)?;
        let index = self.kernel_locals.len().checked_sub(1 + position)?;
        Some(Term::Var(index))
    }
    /// Translate one evaluated runtime scalar argument into a kernel term in the
    /// caller's context. Only canonical literals and immutable, in-scope scalar
    /// locals are accepted: a proof must be frozen at its source evaluation
    /// point and must not reinterpret a mutable local's final value.
    fn scalar_argument(&self, expr: &ast::Expr, ty: Type, span: Span) -> Result<Term> {
        let Some(carrier) = ty.scalar_carrier() else {
            return Err(Diagnostic::new(
                span,
                "only i64, Bool, and Unit runtime values can be symbolic proof indices",
            ));
        };
        let literal_error = || {
            Diagnostic::new(
                expr.span,
                "a symbolic proof index must be an integer, boolean, or unit literal, or the name of an immutable scalar local; evaluate the expression into a named immutable local first",
            )
        };
        match (carrier, &expr.kind) {
            (Scalar::I64, ast::ExprKind::Integer(text)) => {
                if let Ok(value) = text.parse::<i64>() {
                    return Ok(Term::i64(value));
                }
                Err(Diagnostic::new(
                    expr.span,
                    "machine integer literal is outside the i64 range",
                ))
            }
            (
                Scalar::I64,
                ast::ExprKind::Unary {
                    op: Kind::Minus,
                    operand,
                    ..
                },
            ) => {
                let ast::ExprKind::Integer(text) = &operand.kind else {
                    return Err(literal_error());
                };
                integer(text, true, expr.span).map(Term::i64)
            }
            (Scalar::Bool, ast::ExprKind::Bool(value)) => Ok(Term::boolean(*value)),
            (Scalar::Unit, ast::ExprKind::Tuple(values)) if values.is_empty() => Ok(Term::unit()),
            (_, ast::ExprKind::Name(_) | ast::ExprKind::Field { .. }) => {
                let Some(id) = self.resolution.reference(expr.span) else {
                    return Err(literal_error());
                };
                if let Some(term) = self.kernel_local_term(id) {
                    // The runtime type checker already established the scalar
                    // carrier; this guard keeps the kernel context authoritative.
                    if self.kernel_types.get(&id).and_then(normalized_scalar) == Some(carrier) {
                        return Ok(if carrier == Scalar::Unit {
                            // Canonical singleton encoding for Unit.
                            Term::unit()
                        } else {
                            term
                        });
                    }
                    return Err(Diagnostic::new(
                        expr.span,
                        "this scalar local has a different carrier from the indexed parameter",
                    ));
                }
                if self.slots.contains_key(&id) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a mutable runtime value cannot index an erased proof; bind an immutable local at the evaluation point",
                    ));
                }
                Err(literal_error())
            }
            _ => Err(literal_error()),
        }
    }
    /// Check one erased logical argument at a call site. The declared type is
    /// elaborated in the callee's open context (caller erased binders followed
    /// by earlier erased binders of this callee), validated as a type, and then
    /// the actual earlier proof terms are substituted before checking the
    /// evidence in the caller context.
    #[allow(clippy::too_many_arguments)]
    fn discharge_kernel_call(
        &mut self,
        parameter: &ast::Parameter,
        evidence: &ast::Expr,
        callee_binders: &mut Vec<BindingId>,
        callee_types: &mut Vec<Term>,
        callee_actuals: &mut Vec<Term>,
        span: Span,
    ) -> Result<()> {
        if matches!(&evidence.kind, ast::ExprKind::Name(name) if name == "_") {
            return Err(Diagnostic::new(
                evidence.span,
                "cannot discharge a logical proposition by arithmetic search; pass a named proof",
            ));
        }
        let mut context = self.kernel_context();
        context.extend(callee_types.iter().cloned());
        let mut bindings = self.kernel_bindings();
        for (id, ty) in callee_binders.iter().zip(callee_types.iter()) {
            bindings.push((*id, ty.clone()));
        }
        let expected =
            crate::check::elaborate_type(self.resolution, self.logical, &bindings, &parameter.ty)
                .map_err(|e| {
                Diagnostic::new(
                    e.span,
                    format!("invalid erased logical proposition: {}", e.message),
                )
            })?;
        let inferred = self
            .logical
            .kernel
            .sort_open(&expected, &context)
            .map_err(|e| {
                Diagnostic::new(
                    span,
                    format!("invalid dependent erased parameter type: {e}"),
                )
            })?;
        let _ = inferred;
        let caller_context = self.kernel_context();
        let caller_expected = self
            .logical
            .kernel
            .substitute_outer(&expected, callee_actuals)
            .map_err(|e| {
                Diagnostic::new(
                    span,
                    format!("internal error: dependent erased substitution failed: {e}"),
                )
            })?;
        let term = crate::check::elaborate_value_with_aliases(
            self.resolution,
            self.logical,
            &self.kernel_bindings(),
            evidence,
            &self.kernel_alias_sources(),
        )
        .map_err(|e| {
            Diagnostic::new(
                e.span,
                format!(
                    "erased argument must be a checked logical proof term: {}",
                    e.message
                ),
            )
        })?;
        // A runtime scalar may occur inside a proof term (as an index), but the
        // evidence itself must be a logical value, never a runtime observation.
        if self.evidence_is_runtime_scalar(&term) {
            return Err(Diagnostic::new(
                evidence.span,
                "a runtime scalar is a symbolic index, not erased evidence; construct a checked proof term instead",
            ));
        }
        self.logical
            .kernel
            .check_open(&term, &caller_expected, &caller_context)
            .map_err(|e| {
                Diagnostic::new(
                    span,
                    format!("proof does not establish the erased proposition: {e}"),
                )
            })?;
        callee_binders.push(self.resolution.binder(parameter.span).unwrap());
        callee_types.push(expected);
        callee_actuals.push(term);
        Ok(())
    }
    /// Whether an elaborated evidence term is exactly an in-scope runtime scalar
    /// variable (rather than a logical value whose indices mention one).
    fn evidence_is_runtime_scalar(&self, term: &Term) -> bool {
        let Term::Var(index) = term else {
            return false;
        };
        let Some(position) = self.kernel_locals.len().checked_sub(1 + index) else {
            return false;
        };
        let Some(id) = self.kernel_locals.get(position) else {
            return false;
        };
        !self.kernel_proofs.contains_key(id)
            && self
                .kernel_types
                .get(id)
                .and_then(normalized_scalar)
                .is_some()
    }
    fn bind(&mut self, span: Span, ty: Type, mutable: bool) -> Result<usize> {
        if self.locals.len() >= 1024 {
            return Err(Diagnostic::new(
                span,
                "function exceeds the 1024-local limit",
            ));
        }
        let Some(id) = self.resolution.binder(span) else {
            return Err(Diagnostic::new(
                span,
                "unsupported executable binding pattern",
            ));
        };
        let slot = self.locals.len();
        self.locals.push(Local {
            ty,
            mutable,
            linear: false,
            grade: None,
            span,
        });
        self.slots.insert(id, slot);
        Ok(slot)
    }
    /// Allocate a checked local with no source binder. Used only for compiler
    /// temporaries whose evaluation must happen exactly once, such as the
    /// midpoint and implicit parent of a checked mutable split.
    fn fresh_local(&mut self, span: Span, ty: Type) -> Result<usize> {
        if self.locals.len() >= 1024 {
            return Err(Diagnostic::new(
                span,
                "function exceeds the 1024-local limit",
            ));
        }
        let slot = self.locals.len();
        self.locals.push(Local {
            ty,
            mutable: false,
            linear: false,
            grade: None,
            span,
        });
        Ok(slot)
    }
    fn slot(&self, span: Span) -> Result<usize> {
        self.resolution
            .reference(span)
            .and_then(|id| self.slots.get(&id))
            .copied()
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "expected a scalar local value; function values are not supported yet",
                )
            })
    }
    fn block(&mut self, block: &ast::Block, expected: Option<Type>) -> Result<Block> {
        self.nested(block.span, |c| {
            let mark = c.facts.mark();
            let kernel_mark = c.kernel_locals.len();
            let result = c.statements(
                &block.statements,
                block.tail.as_deref(),
                block.span,
                expected,
            );
            c.facts.reset(mark);
            c.kernel_locals.truncate(kernel_mark);
            result
        })
    }
    /// Elaborate the restricted borrow-pair statement
    ///
    /// ```text
    /// let (left, right) = Slice.split_at_mut(view, mid);
    /// ```
    ///
    /// The pair is not a storable value. It lowers to one checked midpoint
    /// local plus two ordinary slice views whose ranges are exactly
    /// `[0, mid)` and `[mid, len)`. Ownership checking marks the pair as a
    /// checked split rather than granting a general sibling exemption.
    fn split_binding(
        &mut self,
        mutable: bool,
        pattern: &ast::Pattern,
        annotation: Option<&ast::Type>,
        value: &ast::Expr,
        span: Span,
    ) -> Result<Option<Vec<Statement>>> {
        let ast::PatternKind::Tuple(parts) = &pattern.kind else {
            return Ok(None);
        };
        let ast::ExprKind::Call { callee, arguments } = &value.kind else {
            return Ok(None);
        };
        let Some(id) = self.resolution.reference(callee.span) else {
            return Ok(None);
        };
        let binding = &self.resolution.bindings[id];
        if binding.kind != BindingKind::Builtin || binding.name != "Slice.split_at_mut" {
            return Ok(None);
        }
        if mutable {
            return Err(Diagnostic::new(
                pattern.span,
                "split borrow bindings are move-only views and cannot be declared with 'let mut'",
            ));
        }
        if annotation.is_some() {
            return Err(Diagnostic::new(
                pattern.span,
                "a split borrow pair takes its view types from the receiver; omit the binding annotation",
            ));
        }
        if arguments.len() != 2 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Slice.split_at_mut expects 2 arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        let [left_name, right_name] = parts.as_slice() else {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut must destructure into exactly two names: let (left, right) = ...",
            ));
        };
        let (ast::PatternKind::Name(left_path), ast::PatternKind::Name(right_path)) =
            (&left_name.kind, &right_name.kind)
        else {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut binds exactly two simple local names; wildcards, fields, and nested patterns are not supported",
            ));
        };
        if left_path.len() != 1 || right_path.len() != 1 {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut binds exactly two simple local names",
            ));
        }
        if left_path == right_path {
            return Err(Diagnostic::new(
                pattern.span,
                "Slice.split_at_mut requires two distinct binding names",
            ));
        }

        // Evaluate the receiver exactly once. A named mutable view is used
        // directly; an explicit `&mut owner[..]` or `&mut parent[..]` becomes
        // a hidden parent capability so the midpoint is always split from one
        // stable checked view.
        let (parent_slot, parent_statement) = if matches!(arguments[0].kind, ast::ExprKind::Name(_))
        {
            let slot = self.slot(arguments[0].span)?;
            match self.locals[slot].ty {
                Type::SliceMut(_) => (slot, None),
                other => {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!(
                            "Slice.split_at_mut requires an exclusive '&mut [T]' view or '&mut owner[..]'; found {}",
                            self.types.name(other)
                        ),
                    )
                    .with_note(
                        self.locals[slot].span,
                        "bind a mutable slice view first, or pass &mut owner[..]",
                    ));
                }
            }
        } else if matches!(
            &arguments[0].kind,
            ast::ExprKind::Unary {
                op: Kind::Amp,
                mutable: true,
                operand,
            } if matches!(operand.kind, ast::ExprKind::Slice { .. })
        ) {
            let checked = self.expr(&arguments[0])?;
            let Type::SliceMut(_) = checked.ty else {
                return Err(Diagnostic::new(
                    arguments[0].span,
                    "Slice.split_at_mut requires an exclusive '&mut [T]' receiver",
                ));
            };
            let slot = self.fresh_local(arguments[0].span, checked.ty)?;
            (slot, Some(Statement::Let(slot, checked)))
        } else {
            return Err(Diagnostic::new(
                arguments[0].span,
                "Slice.split_at_mut receiver must be a mutable slice-view local or an explicit '&mut owner[..]' / '&mut parent[..]' reborrow",
            ));
        };
        let Type::SliceMut(pointer) = self.locals[parent_slot].ty else {
            unreachable!("split parent was checked as an exclusive slice")
        };
        let element = self.types.pointees[pointer];
        if self.owned_type(element) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot split a slice view over owning or linear elements ({}); element reads would move owners",
                    self.types.name(element)
                ),
            ));
        }
        let midpoint = self.expr_expected(&arguments[1], Some(Type::I64))?;
        self.expect(midpoint.ty, Type::I64, midpoint.span)?;
        if midpoint.ty == Type::Never {
            return Err(Diagnostic::new(
                midpoint.span,
                "the midpoint of Slice.split_at_mut must produce an i64 value",
            ));
        }
        self.require(PANIC, span)?;
        let mid_slot = self.fresh_local(arguments[1].span, Type::I64)?;
        let group = self.next_split;
        self.next_split += 1;
        let view_ty = Type::SliceMut(pointer);
        let left_slot = self.bind(left_name.span, view_ty, false)?;
        let right_slot = self.bind(right_name.span, view_ty, false)?;
        let base = |span: Span| Expr {
            kind: ExprKind::Local(parent_slot),
            ty: view_ty,
            span,
            resource: None,
        };
        let mid = |span: Span| Expr {
            kind: ExprKind::Local(mid_slot),
            ty: Type::I64,
            span,
            resource: None,
        };
        let mut left = self.slice_from_expr(
            base(left_name.span),
            None,
            Some(mid(left_name.span)),
            element,
            true,
            true,
            left_name.span,
            None,
        )?;
        let mut right = self.slice_from_expr(
            base(right_name.span),
            Some(mid(right_name.span)),
            None,
            element,
            true,
            true,
            right_name.span,
            None,
        )?;
        if let ExprKind::Slice { split, .. } = &mut left.kind {
            *split = Some((group, true));
        }
        if let ExprKind::Slice { split, .. } = &mut right.kind {
            *split = Some((group, false));
        }
        let mut statements = Vec::with_capacity(4);
        if let Some(parent) = parent_statement {
            statements.push(parent);
        }
        statements.push(Statement::Let(mid_slot, midpoint));
        statements.push(Statement::Let(left_slot, left));
        statements.push(Statement::Let(right_slot, right));
        Ok(Some(statements))
    }
    /// Check a statement sequence. A destructuring `let` turns the rest of the
    /// sequence into the body of a single-arm match, so its bindings scope over it.
    fn statements(
        &mut self,
        statements: &[ast::Statement],
        tail: Option<&ast::Expr>,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Block> {
        let mut checked = Vec::new();
        let mut diverges = false;
        for (index, statement) in statements.iter().enumerate() {
            if diverges {
                return Err(Diagnostic::new(
                    span,
                    "unreachable statement after return/panic/break",
                ));
            }
            match statement {
                ast::Statement::Let {
                    mutable,
                    pattern,
                    ty,
                    value,
                    ..
                } => {
                    if let Some(generated) =
                        self.split_binding(*mutable, pattern, ty.as_ref(), value, span)?
                    {
                        checked.extend(generated);
                        continue;
                    }
                    let (annotation, grade) = match ty {
                        Some(ty) => {
                            let (inner, grade) = split_grade(ty);
                            let grade = grade
                                .map(|grade| grades::evaluate(self.resolution, &self.grades, grade))
                                .transpose()?;
                            (Some(self.ty(inner)?), grade)
                        }
                        None => (None, None),
                    };
                    let value = self.expr_expected(value, annotation)?;
                    if value.ty.is_ref() && *mutable {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "reference bindings are immutable: a reborrow derives from the stored reference, so assign a new reference by binding a fresh 'let' instead of rebinding it",
                        ));
                    }
                    if value.ty.is_view() && *mutable {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "borrowed views are not mutable bindings and cannot be reassigned; bind them with 'let' without 'mut'",
                        ));
                    }
                    diverges = value.ty == Type::Never;
                    let ty = match annotation {
                        Some(ty) => ty,
                        // Mutable locals keep the declared enum, not one variant.
                        None if *mutable => self.types.full(value.ty, pattern.span)?,
                        None => value.ty,
                    };
                    if (!matches!(&pattern.kind, ast::PatternKind::Name(path) if path.len() == 1)
                        || self.is_constructor_pattern(pattern))
                        && !diverges
                    {
                        if grade.is_some() {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "usage grades require a simple name binding; destructure first, then annotate each binding separately",
                            ));
                        }
                        if *mutable {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "destructuring let bindings are immutable; rebind a field with 'let mut' afterwards",
                            ));
                        }
                        return self.destructure(
                            checked,
                            pattern,
                            value,
                            ty,
                            (&statements[index + 1..], tail),
                            span,
                            expected,
                        );
                    }
                    let slot = self.bind(pattern.span, ty, *mutable)?;
                    // Both immutable and mutable scalar bindings are symbolic
                    // index candidates. A mutable one is versioned: assignment
                    // appends a new binder instead of reinterpreting an old
                    // proof at the final value.
                    let id = self.resolution.binder(pattern.span).unwrap();
                    // `let alias = scalar` is a by-value copy. Keeping the
                    // source's current kernel binder lets proofs about the
                    // source value apply to the alias, while a later assignment
                    // to the source appends a new binder and leaves the alias
                    // frozen at the copied version.
                    let alias_source = match &value.kind {
                        ExprKind::Local(source_slot) => {
                            self.slots.iter().find_map(|(candidate, slot)| {
                                (*slot == *source_slot).then_some(*candidate)
                            })
                        }
                        _ => None,
                    };
                    self.admit_scalar_index(id, ty, pattern.span)?;
                    if let Some(source) = alias_source
                        && ty.scalar_carrier().is_some()
                    {
                        self.alias_scalar_index(id, source);
                    }
                    self.facts.define(slot, &value);
                    let must_use = self.copyable_result_grade(&value);
                    if let Some(required) = must_use
                        && let Some(annotation) = grade
                        && annotation != required
                    {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "a copyable result with the must-use @[{required}] contract cannot be bound to a local graded @[{annotation}]; bind it ungraded or as @[{required}]"
                            ),
                        ));
                    }
                    self.locals[slot].grade = grade.or(must_use);
                    self.locals[slot].linear = self.value_moves_linear(&value)
                        || (self.locals[slot].grade.is_some_and(Grade::is_one)
                            && self.owned_type(ty));
                    if !diverges {
                        self.validate_grade(grade, ty, pattern.span, true)?;
                    }
                    checked.push(Statement::Let(slot, value));
                }
                ast::Statement::Expr(expr) => {
                    let before = self.facts.clone();
                    let expr = self.expr(expr)?;
                    if expr.ty != Type::Never && self.observes_copyable_result(&expr) {
                        return Err(Diagnostic::new(
                            expr.span,
                            "this copyable result has the must-use `@[1]` contract and its value is discarded by an expression statement; bind it with 'let' and observe it exactly once, or pass it to a call",
                        ));
                    }
                    diverges = expr.ty == Type::Never;
                    // `if c { return; }` establishes `!c` for the rest of the block.
                    if let ExprKind::If(condition, yes, no) = &expr.kind
                        && self.facts.same_versions(&before)
                    {
                        if yes.ty == Type::Never && no.ty != Type::Never {
                            let facts = self.facts.condition(condition, false);
                            self.facts.add(facts);
                        } else if no.ty == Type::Never && yes.ty != Type::Never {
                            let facts = self.facts.condition(condition, true);
                            self.facts.add(facts);
                        }
                    }
                    checked.push(Statement::Expr(expr));
                }
            }
        }
        if let (true, Some(tail)) = (diverges, tail) {
            return Err(Diagnostic::new(
                tail.span,
                "unreachable expression after return/panic/break",
            ));
        }
        let tail = tail
            .map(|tail| self.expr_expected_result(tail, expected).map(Box::new))
            .transpose()?;
        let ty = if diverges {
            Type::Never
        } else {
            tail.as_ref().map_or(Type::Unit, |tail| tail.ty)
        };
        Ok(Block {
            statements: checked,
            tail,
            ty,
        })
    }
    fn is_constructor_pattern(&self, pattern: &ast::Pattern) -> bool {
        self.resolution
            .reference(pattern.span)
            .is_some_and(|id| self.resolution.bindings[id].kind == BindingKind::Constructor)
    }

    /// Exact usage grade evidenced by an already-checked argument expression.
    /// Only forms that carry one annotated binding are used for inference;
    /// everything else stays unknown instead of defaulting to one.
    fn expression_grade(&self, expr: &Expr) -> Option<Grade> {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => self.locals[*slot].grade,
            ExprKind::Coerce { value, .. } => self.expression_grade(value),
            ExprKind::Block(block) => block
                .tail
                .as_ref()
                .and_then(|tail| self.expression_grade(tail)),
            ExprKind::If(_, yes, no) => {
                let left = (yes.ty != Type::Never)
                    .then(|| {
                        yes.tail
                            .as_ref()
                            .and_then(|tail| self.expression_grade(tail))
                    })
                    .flatten();
                let right = (no.ty != Type::Never)
                    .then(|| {
                        no.tail
                            .as_ref()
                            .and_then(|tail| self.expression_grade(tail))
                    })
                    .flatten();
                match (left, right) {
                    (Some(left), Some(right)) if left == right => Some(left),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    /// Whether this expression evaluates to a copyable result carrying the
    /// must-use `@[1]` contract. The obligation is transferred through value
    /// positions (`let`, assignment, `return`, blocks, branches, match arms,
    /// loop break values, and coercions) and is discharged by an observation:
    /// a call argument, aggregate field, read, match scrutinee, or `?` operand.
    /// It is never an owning/linear move, even though it uses the same literal
    /// `@[1]` surface grade.
    fn copyable_result_grade(&self, expr: &Expr) -> Option<Grade> {
        match &expr.kind {
            ExprKind::Call(
                Target::Function(index)
                | Target::ObjectFunction {
                    function: index, ..
                },
                _,
            ) => self.functions.signatures.get(*index).and_then(|signature| {
                signature
                    .result_grade
                    .filter(|grade| grade.is_one() && !self.owned_type(signature.result))
            }),
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) => {
                    self.types.function_types.get(id).and_then(|signature| {
                        signature
                            .result_grade
                            .filter(|grade| grade.is_one() && !self.owned_type(signature.result))
                    })
                }
                _ => None,
            },
            ExprKind::Coerce { value, .. } => self.copyable_result_grade(value),
            ExprKind::Block(block) => block
                .tail
                .as_ref()
                .and_then(|tail| self.copyable_result_grade(tail)),
            ExprKind::If(_, yes, no) => (yes.ty != Type::Never)
                .then(|| {
                    yes.tail
                        .as_ref()
                        .and_then(|tail| self.copyable_result_grade(tail))
                })
                .flatten()
                .or_else(|| {
                    (no.ty != Type::Never)
                        .then(|| {
                            no.tail
                                .as_ref()
                                .and_then(|tail| self.copyable_result_grade(tail))
                        })
                        .flatten()
                }),
            ExprKind::Match(_, arms) => arms.iter().find_map(|arm| {
                (arm.body.ty != Type::Never)
                    .then(|| self.copyable_result_grade(&arm.body))
                    .flatten()
            }),
            ExprKind::Loop(body) => crate::ownership::loop_break_values(body)
                .into_iter()
                .find_map(|value| self.copyable_result_grade(value)),
            // A copyable `@[1]` task result is delivered as `Completed` on both
            // the normal and cancellation paths. Joining the (linear) handle
            // produces a must-use `TaskExit<T>`; a scope returns the must-use
            // value directly.
            ExprKind::TaskJoin { obligation, .. } | ExprKind::TaskScope { obligation, .. } => {
                (*obligation && !self.owned_type(expr.ty)).then_some(Grade::ONE)
            }
            _ => None,
        }
    }
    fn copyable_result_obligation(&self, expr: &Expr) -> bool {
        self.copyable_result_grade(expr).is_some()
    }
    /// Whether a returned value would observe a copyable must-use obligation.
    /// An owning `@[1]` result is a move instead and is handled by the
    /// ownership pass.
    fn observes_copyable_result(&self, expr: &Expr) -> bool {
        self.copyable_result_obligation(expr) && !self.owned_type(expr.ty)
    }
    /// Whether a returned copyable must-use obligation may be transferred to
    /// the current function result. Only a matching `@[1]` copyable result
    /// contract can carry it; otherwise the caller would receive an ordinary
    /// value with no obligation.
    /// Whether a returned must-use obligation matches the current result
    /// contract. Exact grade equality is required: a custom algebra's `one` is
    /// not silently equated with the builtin exactly-one observation.
    fn transfers_copyable_result_from(&self, expr: &Expr) -> bool {
        !self.owned_type(self.result)
            && self.result_grade.is_some()
            && self.result_grade == self.copyable_result_grade(expr)
    }
    /// Propagate binding obligations before lambda types and capture slots are
    /// elaborated. The ownership pass independently validates consumption later.
    ///
    /// A call whose checked signature declares a `@[1]` result contract returns
    /// an owning linear resource obligation even though its runtime type is
    /// merely owning. The obligation is derived from the already-created
    /// signature, so it is known before closure capture typing and synthetic
    /// capture locals. A copyable `@[1]` result is a must-use obligation, not a
    /// move, and is tracked by the grade pass instead.
    fn value_moves_linear(&self, expr: &Expr) -> bool {
        if self.linear_type(expr.ty) {
            return true;
        }
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => self.locals[*slot].linear,
            ExprKind::Call(
                Target::Function(index)
                | Target::ObjectFunction {
                    function: index, ..
                },
                _,
            ) => self
                .functions
                .signatures
                .get(*index)
                .is_some_and(|signature| {
                    signature.result_grade.is_some_and(Grade::is_one)
                        && self.owned_type(signature.result)
                }),
            ExprKind::Call(
                Target::Vec(VecOp::Reserve | VecOp::Clear | VecOp::TryReserve { .. }, _),
                args,
            ) => args
                .first()
                .is_some_and(|owner| self.value_moves_linear(owner)),
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) => {
                    self.types.function_types.get(id).is_some_and(|signature| {
                        signature.result_grade.is_some_and(Grade::is_one)
                            && self.owned_type(signature.result)
                    })
                }
                _ => false,
            },
            ExprKind::Block(b) => b.tail.as_ref().is_some_and(|e| self.value_moves_linear(e)),
            ExprKind::If(_, a, b) => [a, b].iter().any(|b| {
                b.ty != Type::Never && b.tail.as_ref().is_some_and(|e| self.value_moves_linear(e))
            }),
            ExprKind::Match(_, arms) => arms
                .iter()
                .any(|a| a.body.ty != Type::Never && self.value_moves_linear(&a.body)),
            ExprKind::Loop(b) => crate::ownership::loop_break_values(b)
                .into_iter()
                .any(|e| self.value_moves_linear(e)),
            ExprKind::Construct { fields, .. } => fields.iter().any(|e| self.value_moves_linear(e)),
            ExprKind::FnValue { captures, .. } => {
                captures.iter().any(|e| self.value_moves_linear(e))
            }
            ExprKind::BoxNew(e)
            | ExprKind::Try { value: e, .. }
            | ExprKind::Coerce { value: e, .. } => self.value_moves_linear(e),
            ExprKind::BoxTake(e) if self.owned_type(expr.ty) => self.value_moves_linear(e),
            // Reuse returns an owner carrying the old binding obligation.
            ExprKind::BoxReuse { owner, payload }
            | ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. }
            | ExprKind::ArenaAlloc {
                arena: owner,
                value: payload,
            } => self.value_moves_linear(owner) || self.value_moves_linear(payload),
            ExprKind::BoxTryNew { value, .. }
            | ExprKind::BytesTryWithCapacity {
                capacity: value, ..
            }
            | ExprKind::ArenaBoxTake(value) => self.value_moves_linear(value),
            // In-place map returns the same vector owner it consumed.
            ExprKind::VecMap { vector, .. } => self.value_moves_linear(vector),
            ExprKind::DynArrayPush { array, value, .. } => {
                self.value_moves_linear(array) || self.value_moves_linear(value)
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                self.value_moves_linear(array)
                    || self.value_moves_linear(index)
                    || self.value_moves_linear(value)
            }
            ExprKind::DynArrayPop { array, .. } => self.value_moves_linear(array),
            // A task/scope whose result carries an owning or linear obligation
            // transfers it to the handle (or to the joined TaskExit).
            ExprKind::TaskSpawn { obligation, .. }
            | ExprKind::TaskScope { obligation, .. }
            | ExprKind::TaskJoin { obligation, .. } => *obligation,
            _ => false,
        }
    }
    /// Whether any normal return of `block` transfers a binding-based or
    /// graded result obligation. Intrinsic linear result types carry their
    /// obligation in the type itself and are reported by the caller separately.
    ///
    /// This walks every `return` expression, including returns nested in
    /// arguments, branches, and loops, plus the block's tail value. It is
    /// deliberately syntactic and conservative: the ownership pass later
    /// revalidates the same obligation on each path.
    fn return_obligation(&self, block: &Block) -> Option<Span> {
        fn find(checker: &Checker, expr: &Expr) -> Option<Span> {
            match &expr.kind {
                ExprKind::Return(value) => checker
                    .value_moves_linear(value)
                    .then_some(value.span)
                    .or_else(|| find(checker, value)),
                ExprKind::Block(block) => find_in_block(checker, block),
                ExprKind::If(condition, yes, no) => find(checker, condition)
                    .or_else(|| find_in_block(checker, yes))
                    .or_else(|| find_in_block(checker, no)),
                ExprKind::Match(scrutinee, arms) => find(checker, scrutinee).or_else(|| {
                    arms.iter().find_map(|arm| {
                        arm.guard
                            .as_ref()
                            .and_then(|guard| find(checker, guard))
                            .or_else(|| find(checker, &arm.body))
                    })
                }),
                ExprKind::Loop(block) => find_in_block(checker, block),
                ExprKind::While(condition, block) => {
                    find(checker, condition).or_else(|| find_in_block(checker, block))
                }
                ExprKind::Call(_, arguments)
                | ExprKind::Construct {
                    fields: arguments, ..
                } => arguments
                    .iter()
                    .find_map(|argument| find(checker, argument)),
                ExprKind::CallIndirect { callee, arguments } => {
                    find(checker, callee).or_else(|| {
                        arguments
                            .iter()
                            .find_map(|argument| find(checker, argument))
                    })
                }
                ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
                    find(checker, body)
                }
                ExprKind::Unary(_, inner)
                | ExprKind::BoxNew(inner)
                | ExprKind::BoxTake(inner)
                | ExprKind::BoxRead(inner)
                | ExprKind::BoxTryNew { value: inner, .. }
                | ExprKind::BytesTryWithCapacity {
                    capacity: inner, ..
                }
                | ExprKind::ArenaBoxRead(inner)
                | ExprKind::ArenaBoxTake(inner)
                | ExprKind::Drop(inner)
                | ExprKind::Project(inner, _)
                | ExprKind::Coerce { value: inner, .. }
                | ExprKind::Assign(_, inner)
                | ExprKind::Break(Some(inner), _)
                | ExprKind::Try { value: inner, .. }
                | ExprKind::TaskCancel(inner)
                | ExprKind::TaskJoin { task: inner, .. } => find(checker, inner),
                ExprKind::Binary(_, left, right) | ExprKind::BytesAt(left, right) => {
                    find(checker, left).or_else(|| find(checker, right))
                }
                ExprKind::RefAssign(reference, _, value) => {
                    find(checker, reference).or_else(|| find(checker, value))
                }
                ExprKind::BoxReuse { owner, payload }
                | ExprKind::ArenaAlloc {
                    arena: owner,
                    value: payload,
                } => find(checker, owner).or_else(|| find(checker, payload)),
                ExprKind::ArenaNew => None,
                ExprKind::DynArrayPush { array, value, .. } => {
                    find(checker, array).or_else(|| find(checker, value))
                }
                ExprKind::DynArraySet {
                    array,
                    index,
                    value,
                    ..
                } => find(checker, array)
                    .or_else(|| find(checker, index))
                    .or_else(|| find(checker, value)),
                ExprKind::DynArrayPop { array, .. } => find(checker, array),
                ExprKind::DynArrayNew { .. } => None,
                ExprKind::VecMap {
                    vector, callbacks, ..
                } => find(checker, vector).or_else(|| {
                    callbacks
                        .iter()
                        .find_map(|callback| find(checker, callback))
                }),
                ExprKind::Slice {
                    base, start, end, ..
                } => find(checker, base)
                    .or_else(|| start.as_deref().and_then(|e| find(checker, e)))
                    .or_else(|| end.as_deref().and_then(|e| find(checker, e))),
                ExprKind::FnValue { captures, .. } => {
                    captures.iter().find_map(|capture| find(checker, capture))
                }
                _ => None,
            }
        }
        fn find_in_block(checker: &Checker, block: &Block) -> Option<Span> {
            block
                .statements
                .iter()
                .find_map(|statement| match statement {
                    Statement::Let(_, value) | Statement::Expr(value) => find(checker, value),
                })
                .or_else(|| block.tail.as_deref().and_then(|tail| find(checker, tail)))
        }
        find_in_block(self, block).or_else(|| {
            let tail = block.tail.as_deref()?;
            self.value_moves_linear(tail).then_some(tail.span)
        })
    }
    fn linear_pattern(&mut self, pattern: &Pattern, linear: bool) {
        if linear {
            let mut slots = std::collections::BTreeSet::new();
            crate::ownership::pattern_bindings(pattern, &mut slots);
            for slot in slots {
                if self.owned_type(self.locals[slot].ty) {
                    self.locals[slot].linear = true;
                }
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn destructure(
        &mut self,
        mut checked: Vec<Statement>,
        pattern: &ast::Pattern,
        value: Expr,
        ty: Type,
        rest: (&[ast::Statement], Option<&ast::Expr>),
        span: Span,
        expected: Option<Type>,
    ) -> Result<Block> {
        let pattern_ir = self.pattern(pattern, ty, &mut BTreeMap::new())?;
        if self.observes_copyable_result(&value) {
            return Err(Diagnostic::new(
                pattern.span,
                "a copyable result with the must-use `@[1]` contract must be bound to a simple name or observed directly; destructuring would split off the obligation without a tracked destination",
            ));
        }
        self.linear_pattern(&pattern_ir, self.value_moves_linear(&value));
        let mut coverage = Coverage::new(pattern.span);
        coverage.add(&pattern_ir);
        if coverage.useful(&Pattern::Any, ty, &self.types.enums, &self.types.unions)? {
            return Err(Diagnostic::new(
                pattern.span,
                "let patterns must be irrefutable; use match for patterns that can fail",
            ));
        }
        let body = {
            let kernel_mark = self.kernel_locals.len();
            let body = self.statements(rest.0, rest.1, span, expected);
            self.kernel_locals.truncate(kernel_mark);
            body
        }?;
        let result = body.ty;
        let body = Expr {
            kind: ExprKind::Block(body),
            ty: result,
            span,
            resource: None,
        };
        let matched = Expr {
            kind: ExprKind::Match(
                Box::new(value),
                vec![Arm {
                    pattern: pattern_ir,
                    guard: None,
                    body,
                }],
            ),
            ty: result,
            span,
            resource: None,
        };
        let ty = matched.ty;
        checked.push(Statement::Expr(matched));
        let _ = ty;
        // The match is the block's final value.
        let Statement::Expr(tail) = checked.pop().unwrap() else {
            unreachable!()
        };
        Ok(Block {
            statements: checked,
            ty: tail.ty,
            tail: Some(Box::new(tail)),
        })
    }
    fn expr(&mut self, expr: &ast::Expr) -> Result<Expr> {
        self.expr_expected(expr, None)
    }
    /// Whether an expected type is the enclosing function's erased result.
    /// Such a position accepts `Unit` as the erased value in addition to the
    /// declared copyable payload type.
    fn erased_result_context(&self, expected: Option<Type>) -> bool {
        self.result_grade.is_some_and(Grade::is_zero) && expected == Some(self.result)
    }
    /// Check a value in a possible erased-result position. A nested call to
    /// another erased-result function produces `Unit`; returning it through an
    /// erased result is well-typed and carries no payload. Every other value is
    /// checked against the declared payload type normally.
    fn expr_expected_result(&mut self, expr: &ast::Expr, expected: Option<Type>) -> Result<Expr> {
        if !self.erased_result_context(expected) {
            return self.expr_expected(expr, expected);
        }
        let value = self.expr(expr)?;
        if matches!(value.ty, Type::Unit | Type::Never) {
            return Ok(value);
        }
        let span = value.span;
        self.coerce(value, self.result, span)
    }
    /// Erase an expression's value in an erased-result position while keeping
    /// its effects and cleanup. `Drop` is a checked no-op for the copyable
    /// payload types admitted by `@[0]`.
    fn erase_value(&mut self, value: Expr, span: Span) -> Expr {
        if matches!(value.ty, Type::Unit | Type::Never) {
            return value;
        }
        Expr {
            kind: ExprKind::Drop(Box::new(value)),
            ty: Type::Unit,
            span,
            resource: None,
        }
    }
    fn erase_block_value(&mut self, mut block: Block, span: Span) -> Block {
        if matches!(block.ty, Type::Unit | Type::Never) {
            return block;
        }
        let tail = block.tail.take().expect("non-unit block has a tail");
        block.tail = Some(Box::new(self.erase_value(*tail, span)));
        block.ty = Type::Unit;
        block
    }
    fn expr_expected(&mut self, expr: &ast::Expr, expected: Option<Type>) -> Result<Expr> {
        self.nested(expr.span, |c| {
            let span = expr.span;
            if let Some(id) = c.logical_data_root(expr)
                && (c.logical.data.contains_key(&id)
                    || c.logical.constructors.contains_key(&id))
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "'{}' belongs to a total logical data type and has no runtime value; use it only in an erased proof argument",
                        c.resolution.bindings[id].name
                    ),
                ));
            }
            if let ast::ExprKind::Handle {
                operation,
                parameter,
                result,
                handler,
                body,
            } = &expr.kind
            {
                return c.handle_effect(
                    operation,
                    parameter,
                    result,
                    handler,
                    body,
                    expected,
                    span,
                );
            }
            if let ast::ExprKind::Perform { operation, value } = &expr.kind {
                return c.perform_effect(operation, value, expected, span);
            }
            if c.constructor_target(expr).is_some() {
                return c.construct(expr, None, expected, span);
            }
            if let ast::ExprKind::Lambda(lambda) = &expr.kind {
                return c.lambda(lambda, span, expected, false);
            }
            if matches!(
                expr.kind,
                ast::ExprKind::Name(_) | ast::ExprKind::Field { .. }
            ) && let Some(id) = c.resolution.reference(span)
                && c.functions.declared.contains_key(&id)
            {
                return c.function_value(id, None, expected, span);
            }
            if let ast::ExprKind::Specialize { callee, arguments } = &expr.kind
                && let Some(id) = c.resolution.reference(callee.span)
                && c.functions.declared.contains_key(&id)
            {
                return c.function_value(id, Some(arguments), expected, span);
            }
            // `u8.MAX`, `i32.MIN`, ...: integer range constants.
            if matches!(expr.kind, ast::ExprKind::Field { .. })
                && let Some(id) = c.resolution.reference(span)
                && c.resolution.bindings[id].kind == BindingKind::Builtin
                && let Some((kind, bound)) = c.resolution.bindings[id].name.split_once('.')
                && let Some(kind) = crate::int::IntKind::named(kind)
                && matches!(bound, "MIN" | "MAX")
            {
                let value = if bound == "MIN" { kind.min() } else { kind.max() };
                let ty = Type::int(kind);
                if let Some(expected) = expected {
                    c.expect(ty, expected, span)?;
                }
                return Ok(Expr {
                    kind: ExprKind::Constant(kind.encode(value).unwrap()),
                    ty,
                    span,
                    resource: None,
                });
            }
            // `Self.NAME` and `Type.NAME`: associated constants. They are
            // compile-time substitutions with the declared scalar type, so the
            // lowered expression is an ordinary literal and has no storage or
            // accessor call.
            if let ast::ExprKind::Field { value, name } = &expr.kind {
                if matches!(&value.kind, ast::ExprKind::Name(root) if root == "Self") {
                    let Some(value) = c.associated_consts.get(name).cloned() else {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "unknown associated constant '{name}'; an impl must define it or inherit a trait default"
                            ),
                        ));
                    };
                    let node = const_value_expr(&value, span)?;
                    return match expected {
                        Some(expected) => c.coerce(node, expected, span),
                        None => Ok(node),
                    };
                }
                if let Some(id) = c.resolution.reference(span)
                    && matches!(
                        c.resolution.bindings[id].kind,
                        BindingKind::Generic | BindingKind::Parameter
                    )
                    && let Some(value) = c.generic_associated_const(id, name, span)?
                {
                    let node = const_value_expr(&value, span)?;
                    return match expected {
                        Some(expected) => c.coerce(node, expected, span),
                        None => Ok(node),
                    };
                }
                if let Some(id) = c.resolution.reference(span)
                    && c.resolution.bindings[id].kind == BindingKind::Data
                    && let Some(layout) = c.types.nominal_by_binding(id)
                {
                    let nominal = Type::Enum(layout);
                    let mut candidates = Vec::new();
                    if let Some(value) = c
                        .functions
                        .inherent_consts
                        .get(&nominal)
                        .and_then(|values| values.get(name))
                    {
                        candidates.push(value.clone());
                    }
                    for ((_, _, receiver), values) in &c.functions.trait_consts {
                        if *receiver == nominal
                            && let Some(value) = values.get(name)
                            && !candidates.contains(value)
                        {
                            candidates.push(value.clone());
                        }
                    }
                    match candidates.as_slice() {
                        [] => {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "type '{}' has no associated constant '{name}'",
                                    c.types.name(nominal)
                                ),
                            ));
                        }
                        [value] => {
                            let node = const_value_expr(value, span)?;
                            return match expected {
                                Some(expected) => c.coerce(node, expected, span),
                                None => Ok(node),
                            };
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "associated constant '{name}' of '{}' is ambiguous between several traits; qualify it through that trait's method",
                                    c.types.name(nominal)
                                ),
                            ));
                        }
                    }
                }
            }
            let (kind, ty) = match &expr.kind {
                ast::ExprKind::Integer(text) => {
                    let ty = c.literal_type(expected);
                    (ExprKind::Constant(int_literal(text, false, ty, span)?), ty)
                }
                ast::ExprKind::Float(text) => {
                    let ty = c.float_literal_type(expected);
                    let kind = ty.float_kind().expect("float literal type");
                    (ExprKind::Constant(crate::float::literal(text, kind, span)?), ty)
                }
                ast::ExprKind::String(text) => {
                    c.require(ALLOC | PANIC, span)?;
                    (
                        ExprKind::BytesLiteral(text.as_bytes().to_vec()),
                        Type::String,
                    )
                }
                ast::ExprKind::Char(ch) => (ExprKind::Constant(i64::from(u32::from(*ch))), Type::Char),
                ast::ExprKind::Bool(b) => (ExprKind::Constant(i64::from(*b)), Type::Bool),
                ast::ExprKind::Tuple(values) if values.len() >= 2 => {
                    return c.tuple_value(values, expected, span);
                }
                ast::ExprKind::Tuple(values) if values.len() == 1 => {
                    return Err(Diagnostic::new(
                        span,
                        "one-element tuples are not supported; write '()' for unit or omit the trailing comma",
                    ));
                }
                ast::ExprKind::Tuple(values) if values.is_empty() => {
                    (ExprKind::Constant(0), Type::Unit)
                }
                ast::ExprKind::Name(name) if name == "_" => {
                    return Err(Diagnostic::new(
                        span,
                        "'_' is a proof hole; it is only valid as an erased argument",
                    ));
                }
                ast::ExprKind::Name(_) => {
                    if let Some(id) = c.resolution.reference(span) {
                        if c.logical.names.contains_key(&id) {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "'{}' is a checked logical definition and has no runtime value; use it only in an erased proof argument",
                                    c.resolution.bindings[id].name
                                ),
                            ));
                        }
                        if c.logical.data.contains_key(&id)
                            || c.logical.constructors.contains_key(&id)
                        {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "'{}' belongs to a total logical data type and has no runtime value; use it only in an erased proof argument",
                                    c.resolution.bindings[id].name
                                ),
                            ));
                        }
                        if c.kernel_proofs.contains_key(&id) {
                            return Err(Diagnostic::new(
                                span,
                                "erased logical proofs have no runtime value; pass them only to erased parameters",
                            ));
                        }
                        if c.proofs.contains_key(&id) {
                            return Err(Diagnostic::new(
                                span,
                                "erased proofs have no runtime value; pass them only to erased parameters",
                            ));
                        }
                    }
                    let slot = c.slot(span)?;
                    (ExprKind::Local(slot), c.locals[slot].ty)
                }
                ast::ExprKind::Field { value, name }
                    if c.resolution.reference(span).is_none() =>
                {
                    return c.field(value, name, span, expected);
                }
                ast::ExprKind::Record { ty, fields } => {
                    return c.record(ty, fields, span, expected);
                }
                ast::ExprKind::StructuralLiteral(fields) => {
                    return c.structural_literal(fields, expected, span);
                }
                ast::ExprKind::Array(values) => {
                    let candidates = c.expected_array(expected, values.len());
                    if !candidates.is_empty() {
                        if values.len() != candidates[0].2 {
                            return Err(Diagnostic::new(
                                span,
                                "array literal length differs from its type",
                            ));
                        }
                        // Accumulate constraints instead of committing to the
                        // first union alternative: every candidate array layout
                        // is tried, and exactly one must accept every element.
                        let mut accepted = Vec::new();
                        let mut first_error = None;
                        for (id, element, _) in &candidates {
                            let mut fields = Vec::with_capacity(values.len());
                            let mut failed = None;
                            for value in values {
                                match c.expr_expected(value, Some(*element)) {
                                    Ok(value) => fields.push(value),
                                    Err(error) => {
                                        failed = Some(error);
                                        break;
                                    }
                                }
                            }
                            if failed.is_none() {
                                accepted.push((*id, fields));
                            } else if first_error.is_none() {
                                first_error = failed;
                            }
                        }
                        let (id, fields) = match accepted.len() {
                            1 => accepted.pop().expect("one accepted candidate"),
                            0 => {
                                return Err(first_error.expect(
                                    "an array literal candidate always attempts one element",
                                ));
                            }
                            _ => {
                                return Err(Diagnostic::new(
                                    span,
                                    "this array literal fits several union alternatives; add an explicit annotation or type arguments",
                                ));
                            }
                        };
                        let ty = if fields.iter().any(|v| v.ty == Type::Never) {
                            Type::Never
                        } else {
                            Type::Enum(id)
                        };
                        let value = Expr {
                            kind: ExprKind::Construct {
                                enum_id: id,
                                tag: 0,
                                fields,
                            },
                            ty,
                            span,
                            resource: None,
                        };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    return c.vec_literal(values, span, expected);
                }
                ast::ExprKind::Index { value, index } => {
                    let base = c.place(value)?;
                    if base.ty == Type::Str {
                        return Err(Diagnostic::new(
                            span,
                            "a &str view is not indexed by a single index; use Str.byte_at or Str.scalar_at, or take a checked byte-range subview with view[start..end]",
                        ));
                    }
                    if let Some(pointer) = base.ty.slice_element() {
                        let element = c.types.pointees[pointer];
                        if c.owned_type(element) {
                            return Err(Diagnostic::new(
                                span,
                                "indexing a slice copies the element, but it owns resources or is linear",
                            ));
                        }
                        c.require(PANIC, span)?;
                        let index = c.expr_expected(index, Some(Type::I64))?;
                        c.expect(index.ty, Type::I64, index.span)?;
                        let ty = if index.ty == Type::Never {
                            Type::Never
                        } else {
                            element
                        };
                        let value = Expr {
                            kind: ExprKind::Call(
                                Target::Slice(SliceOp::Get, element),
                                vec![base, index],
                            ),
                            ty,
                            span,
                            resource: None,
                        };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    let Some((element, length)) =
                        base.ty.layout().and_then(|id| c.types.enums[id].array)
                    else {
                        return Err(Diagnostic::new(
                            span,
                            "index syntax requires an inline array or a &[T] slice view",
                        ));
                    };
                    if let Some(position) = crate::length::eval_expr(
                        c.resolution,
                        c.logical,
                        &c.consts,
                        index,
                    )? {
                        if position >= length {
                            return Err(Diagnostic::new(
                                index.span,
                                "array index out of bounds",
                            ));
                        }
                        if c.owned_type(element) {
                            return Err(Diagnostic::new(
                                span,
                                "indexing cannot copy owned or linear array elements; destructure or slice instead",
                            ));
                        }
                        let value = Expr {
                            kind: ExprKind::Project(
                                Box::new(base),
                                1 + position * c.types.width(element),
                            ),
                            ty: element,
                            span,
                            resource: None,
                        };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    // Dynamic indexing lowers to a whole-array slice view and a
                    // checked element read. The view only lives for this
                    // expression, so it cannot dangle.
                    if c.owned_type(element) {
                        return Err(Diagnostic::new(
                            span,
                            "dynamic indexing copies the element, but it owns resources or is linear",
                        ));
                    }
                    c.require(PANIC, span)?;
                    let view = c.slice_from_expr(base, None, None, element, false, false, span, None)?;
                    let index = c.expr_expected(index, Some(Type::I64))?;
                    c.expect(index.ty, Type::I64, index.span)?;
                    let ty = if index.ty == Type::Never {
                        Type::Never
                    } else {
                        element
                    };
                    let value = Expr {
                        kind: ExprKind::Call(
                            Target::Slice(SliceOp::Get, element),
                            vec![view, index],
                        ),
                        ty,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => c.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                ast::ExprKind::Slice { value, start, end } => {
                    return c.slice_view(
                        value,
                        start.as_deref(),
                        end.as_deref(),
                        false,
                        span,
                        expected,
                    );
                }
                ast::ExprKind::While { condition, body } => {
                    c.bump_assigned(body);
                    let condition = c.expr(condition)?;
                    c.expect(condition.ty, Type::Bool, condition.span)?;
                    let mark = c.facts.mark();
                    let facts = c.facts.condition(&condition, true);
                    c.facts.add(facts);
                    c.loops.push(Loop { value: None, is_while: true, expected: None });
                    let body = c.block(body, Some(Type::Unit));
                    c.loops.pop();
                    c.facts.reset(mark);
                    let body = body?;
                    c.expect(body.ty, Type::Unit, span)?;
                    (ExprKind::While(Box::new(condition), body), Type::Unit)
                }
                ast::ExprKind::Loop(body) => {
                    c.bump_assigned(body);
                    c.loops.push(Loop { value: Some(Type::Never), is_while: false, expected });
                    let body = c.block(body, Some(Type::Unit));
                    let state = c.loops.pop().unwrap();
                    let body = body?;
                    c.expect(body.ty, Type::Unit, span)?;
                    (ExprKind::Loop(body), state.value.unwrap())
                }
                ast::ExprKind::Break(value) => {
                    let Some(state) = c.loops.last() else {
                        return Err(Diagnostic::new(span, "'break' outside of a loop"));
                    };
                    let value = match value {
                        Some(value) if state.is_while => {
                            return Err(Diagnostic::new(
                                value.span,
                                "'break' with a value is only allowed in 'loop'; 'while' always produces Unit",
                            ));
                        }
                        Some(value) => {
                            let wanted = state.expected.or(state.value.filter(|t| *t != Type::Never).map(Type::full));
                            let value = c.expr_expected(value, wanted)?;
                            if value.ty.is_view() {
                                return Err(Diagnostic::new(
                                    value.span,
                                    "a borrowed view cannot escape a loop; use it inside the loop body",
                                ));
                            }
                            let previous = c.loops.last().unwrap().value.unwrap();
                            let joined = c.join(previous, value.ty, value.span)?;
                            c.loops.last_mut().unwrap().value = Some(joined);
                            Some(Box::new(value))
                        }
                        None => {
                            if state.is_while {
                                None
                            } else {
                                let previous = state.value.unwrap();
                                let wanted = state.expected.unwrap_or_else(|| {
                                    if previous == Type::Never {
                                        Type::Unit
                                    } else {
                                        previous.full()
                                    }
                                });
                                let unit = Expr {
                                    kind: ExprKind::Constant(0),
                                    ty: Type::Unit,
                                    span,
                                    resource: None,
                                };
                                let value = c.coerce(unit, wanted, span)?;
                                let joined = c.join(previous, value.ty, span)?;
                                c.loops.last_mut().unwrap().value = Some(joined);
                                Some(Box::new(value))
                            }
                        }
                    };
                    (ExprKind::Break(value, vec![]), Type::Never)
                }
                ast::ExprKind::Continue => {
                    if c.loops.is_empty() {
                        return Err(Diagnostic::new(span, "'continue' outside of a loop"));
                    }
                    (ExprKind::Continue(vec![]), Type::Never)
                }
                ast::ExprKind::Block(block) => {
                    let block = c.block(block, expected)?;
                    let ty = block.ty;
                    (ExprKind::Block(block), ty)
                }
                ast::ExprKind::Unary {
                    op: Kind::Minus,
                    operand,
                    ..
                } if matches!(operand.kind, ast::ExprKind::Integer(_)) => {
                    let ast::ExprKind::Integer(text) = &operand.kind else {
                        unreachable!()
                    };
                    let ty = c.literal_type(expected);
                    (ExprKind::Constant(int_literal(text, true, ty, span)?), ty)
                }
                ast::ExprKind::Unary { op: Kind::Amp, mutable, operand } => {
                    // Explicit reborrow: `&*p` narrows an existing reference
                    // for one call without consuming the reference binding, and
                    // `&mut *p` may only reborrow an exclusive reference. The
                    // runtime representation is the existing one-word pointer,
                    // so the reborrow lowers to the reference local itself; the
                    // ownership pass keeps the source capability live and
                    // records the underlying storage provenance.
                    if let ast::ExprKind::Unary {
                        op: Kind::Star,
                        operand: target,
                        ..
                    } = &operand.kind
                    {
                        let ast::ExprKind::Name(_) = &target.kind else {
                            return Err(Diagnostic::new(
                                span,
                                "an explicit reborrow names one reference binding, as in '&*p' or '&mut *p'",
                            ));
                        };
                        let slot = c.slot(target.span)?;
                        let ty = c.locals[slot].ty;
                        let Some(pointer) = ty.ref_pointee() else {
                            return Err(Diagnostic::new(
                                target.span,
                                format!(
                                    "explicit reborrow expects a reference binding, found {}",
                                    c.types.name(ty)
                                ),
                            ));
                        };
                        if *mutable && !matches!(ty, Type::RefMut(_)) {
                            return Err(Diagnostic::new(
                                span,
                                "cannot reborrow a shared reference as exclusive '&mut *p'; shared storage cannot be upgraded",
                            ));
                        }
                        let reborrow = if *mutable {
                            Type::RefMut(pointer)
                        } else {
                            Type::Ref(pointer)
                        };
                        return Ok(Expr {
                            kind: ExprKind::Local(slot),
                            ty: reborrow,
                            span,
                            resource: None,
                        });
                    }
                    if let ast::ExprKind::Slice { value, start, end } = &operand.kind {
                        return c.slice_view(
                            value,
                            start.as_deref(),
                            end.as_deref(),
                            *mutable,
                            span,
                            expected,
                        );
                    }
                    if !matches!(operand.kind, ast::ExprKind::Name(_)) {
                        return Err(Diagnostic::new(
                            span,
                            "borrow a direct local binding; temporary borrows are not supported, and mutable owner borrows of temporaries, fields, and index results are rejected (mutable slice views use '&mut name[..]')",
                        ));
                    }
                    let slot = c.slot(operand.span)?;
                    let ty = c.locals[slot].ty;
                    let record = ty
                        .layout()
                        .is_some_and(|id| c.types.enums[id].record);
                    let object = matches!(ty, Type::Union(_))
                        && c.functions.object_traits.contains_key(&ty);
                    if record || object {
                        if *mutable {
                            if !c.locals[slot].mutable {
                                return Err(Diagnostic::new(
                                    span,
                                    "cannot mutably borrow an immutable binding; declare it with let mut",
                                ));
                            }
                            if record
                                && c.types.enums[ty.layout().expect("record layout")].borrowed
                            {
                                return Err(Diagnostic::new(
                                    span,
                                    "cannot mutably borrow a record with borrowed fields; only owned metadata of an owning record may be updated through '&mut Record'",
                                ));
                            }
                            (ExprKind::Borrow(slot), Type::RefMut(c.types.pointer(ty)))
                        } else {
                            (ExprKind::Borrow(slot), Type::Ref(c.types.pointer(ty)))
                        }
                    } else {
                        if *mutable {
                            return Err(Diagnostic::new(
                                span,
                                "mutable owner borrows are not supported; borrow records with '&mut name', or use '&mut name[..]' for a mutable slice view",
                            ));
                        }
                        if !matches!(
                            ty,
                            Type::Box(_)
                                | Type::Arena
                                | Type::ArenaBox(_)
                                | Type::Bytes
                                | Type::String
                                | Type::Vec(_)
                        ) {
                            return Err(Diagnostic::new(
                                span,
                                "borrowing supports immutable &Box<T>, &Arena, &Bytes, &String, &Vec<T>, &Record, and &[T] slice views",
                            ));
                        }
                        (ExprKind::Borrow(slot), Type::Ref(c.types.pointer(ty)))
                    }
                }
                ast::ExprKind::Unary { op, operand, .. } => {
                    let hint = expected
                        .filter(|t| t.int_kind().is_some() || t.float_kind().is_some());
                    let operand = c.expr_expected(operand, hint)?;
                    let ty = match op {
                        Kind::Minus if operand.ty.float_kind().is_some() => {
                            if operand.ty == Type::Never {
                                Type::float(crate::float::FloatKind::F64)
                            } else {
                                operand.ty
                            }
                        }
                        Kind::Minus => {
                            match operand.ty.int_kind() {
                                Some(kind) if kind.signed() => {}
                                Some(kind) => {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!("cannot negate an unsigned {} value", kind.name()),
                                    ));
                                }
                                None => c.expect(operand.ty, Type::I64, span)?,
                            }
                            c.require(PANIC, span)?;
                            if operand.ty == Type::Never { Type::I64 } else { operand.ty }
                        }
                        Kind::Bang if operand.ty.int_kind().is_some() => operand.ty,
                        Kind::Bang => {
                            c.expect(operand.ty, Type::Bool, span)?;
                            Type::Bool
                        }
                        Kind::Star => {
                            return Err(Diagnostic::new(
                                span,
                                "dereferencing a reference is supported only as an explicit reborrow '&*p' or '&mut *p'; read fields through 'p.field' and pass the reference itself to a call",
                            ));
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                span,
                                "borrowing is not supported by the scalar executable subset",
                            ));
                        }
                    };
                    let ty = if operand.ty == Type::Never {
                        Type::Never
                    } else {
                        ty
                    };
                    (ExprKind::Unary(op.clone(), Box::new(operand)), ty)
                }
                ast::ExprKind::Binary {
                    op: Kind::Eq,
                    left,
                    right,
                } => {
                    if let ast::ExprKind::Name(_) = left.kind {
                        let slot = c.slot(left.span)?;
                        if !c.locals[slot].mutable {
                            return Err(Diagnostic::new(
                                left.span,
                                "cannot assign to an immutable binding; declare it with let mut",
                            ));
                        }
                        let value = c.expr_expected(right, Some(c.locals[slot].ty))?;
                        c.expect(value.ty, c.locals[slot].ty, right.span)?;
                        if let Some(required) = c.copyable_result_grade(&value)
                            && !c.locals[slot].grade.is_some_and(|grade| grade == required)
                        {
                            return Err(Diagnostic::new(
                                right.span,
                                format!(
                                    "this copyable result has the must-use @[{required}] contract; assigning it to a binding with another grade would lose the obligation. Bind it with `let` or assign it to a matching @[{required}] binding"
                                ),
                            ));
                        }
                        c.locals[slot].linear |= c.value_moves_linear(&value);
                        c.facts.assign(slot, &value);
                        c.renew_scalar_index(slot)?;
                        let ty = if value.ty == Type::Never {
                            Type::Never
                        } else {
                            Type::Unit
                        };
                        (ExprKind::Assign(slot, Box::new(value)), ty)
                    } else if matches!(left.kind, ast::ExprKind::Field { .. })
                        && c.is_place(left)
                    {
                        let target = c.place(left)?;
                        let field_ty = target.ty;
                        let Some((reference, offset)) = split_reference_projection(target) else {
                            return Err(Diagnostic::new(
                                left.span,
                                "field assignment requires an exclusive '&mut Record' receiver; update owning locals by rebinding them instead",
                            ));
                        };
                        let Some(pointer) = reference.ty.ref_pointee() else {
                            return Err(Diagnostic::new(
                                left.span,
                                "field assignment requires an exclusive '&mut Record' receiver",
                            ));
                        };
                        if !matches!(reference.ty, Type::RefMut(_)) {
                            return Err(Diagnostic::new(
                                left.span,
                                "cannot write through a shared reference; the receiver must be an exclusive '&mut Record'",
                            ));
                        }
                        if c.types.pointees[pointer].layout().is_none() {
                            return Err(Diagnostic::new(
                                left.span,
                                "field assignment through a reference is supported only for nominal records",
                            ));
                        }
                        if c.owned_type(field_ty)
                            || c.linear_type(field_ty)
                            || field_ty.is_view()
                            || field_ty
                                .layout()
                                .is_some_and(|id| c.types.enums[id].borrowed)
                            || field_ty
                                .layout()
                                .is_some_and(|id| c.types.enums[id].mutable_borrow)
                        {
                            return Err(Diagnostic::new(
                                left.span,
                                "only copyable, non-owning, non-borrowed record fields may be replaced through '&mut Record'; destructure or update an owning value for owned fields",
                            ));
                        }
                        let value = c.expr_expected(right, Some(field_ty))?;
                        c.expect(value.ty, field_ty, right.span)?;
                        let ty = if value.ty == Type::Never {
                            Type::Never
                        } else {
                            Type::Unit
                        };
                        (
                            ExprKind::RefAssign(Box::new(reference), offset, Box::new(value)),
                            ty,
                        )
                    } else {
                        return Err(Diagnostic::new(
                            left.span,
                            "assignment requires a mutable local name or a field of an exclusive '&mut Record' receiver",
                        ));
                    }
                }
                ast::ExprKind::Binary { op, left: left_ast, right: right_ast } => {
                    let arithmetic = matches!(
                        op,
                        Kind::Plus | Kind::Minus | Kind::Star | Kind::Slash | Kind::Percent
                            | Kind::Amp | Kind::Pipe | Kind::Caret
                    );
                    let compares = matches!(
                        op,
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne
                    );
                    let hint = if arithmetic || matches!(op, Kind::Shl | Kind::Shr) {
                        expected.filter(|t| t.int_kind().is_some() || t.float_kind().is_some())
                    } else {
                        None
                    };
                    // A literal takes its type from the other operand, so
                    // `x + 1.5` and `0.5 < x` work for both float widths. A
                    // literal operand is pure, so checking the other side first
                    // does not change evaluation order.
                    let literal = is_int_literal(left_ast) || is_float_literal(left_ast);
                    let other_literal = is_int_literal(right_ast) || is_float_literal(right_ast);
                    let (left, right) = if (arithmetic || compares) && literal && !other_literal {
                        let right = c.expr_expected(right_ast, hint)?;
                        let left = c.expr_expected(
                            left_ast,
                            right
                                .ty
                                .int_kind()
                                .map(Type::int)
                                .or_else(|| right.ty.float_kind().map(Type::float))
                                .or(hint),
                        )?;
                        (left, right)
                    } else {
                        let left = c.expr_expected(left_ast, hint)?;
                        // The right operand of && / || runs only when the left is true / false.
                        let mark = c.facts.mark();
                        if matches!(op, Kind::AmpAmp | Kind::PipePipe) {
                            let facts = c.facts.condition(&left, *op == Kind::AmpAmp);
                            c.facts.add(facts);
                        }
                        let right_hint = if arithmetic || compares {
                            left.ty
                                .int_kind()
                                .map(Type::int)
                                .or_else(|| left.ty.float_kind().map(Type::float))
                        } else {
                            None
                        };
                        let right = c.expr_expected(right_ast, right_hint);
                        c.facts.reset(mark);
                        (left, right?)
                    };
                    let ty = match op {
                        Kind::Plus | Kind::Minus | Kind::Star | Kind::Slash | Kind::Percent
                        | Kind::Amp | Kind::Pipe | Kind::Caret => {
                            if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                                if !matches!(
                                    op,
                                    Kind::Plus
                                        | Kind::Minus
                                        | Kind::Star
                                        | Kind::Slash
                                        | Kind::Percent
                                ) {
                                    return Err(Diagnostic::new(
                                        span,
                                        "floating-point values support +, -, *, /, %, comparisons, and unary -, but not bitwise operators",
                                    ));
                                }
                                c.same_float(left.ty, right.ty, span)?
                            } else {
                                let ty = c.same_int(left.ty, right.ty, span)?;
                                if !matches!(op, Kind::Amp | Kind::Pipe | Kind::Caret) {
                                    c.require(PANIC, span)?;
                                }
                                ty
                            }
                        }
                        Kind::Shl | Kind::Shr => {
                            if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                                return Err(Diagnostic::new(
                                    span,
                                    "floating-point values support +, -, *, /, %, comparisons, and unary -, but not shifts",
                                ));
                            }
                            let ty = c.same_int(left.ty, left.ty, span)?;
                            c.same_int(right.ty, right.ty, right_ast.span)?;
                            c.require(PANIC, span)?;
                            ty
                        }
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge => {
                            if left.ty.float_kind().is_some() || right.ty.float_kind().is_some() {
                                c.same_float(left.ty, right.ty, span)?;
                            } else if left.ty == Type::Char || right.ty == Type::Char {
                                c.expect(left.ty, Type::Char, span)?;
                                c.expect(right.ty, Type::Char, span)?;
                            } else {
                                c.same_int(left.ty, right.ty, span)?;
                            }
                            Type::Bool
                        }
                        Kind::EqEq | Kind::Ne => {
                            let opaque = |t: Type| {
                                t.layout().is_some()
                                    || t.is_union()
                                    || matches!(
                                        t,
                                        Type::Box(_)
                                            | Type::Bytes
                                            | Type::String
                                            | Type::Stdin
                                            | Type::Stdout
                                            | Type::Ref(_)
                                            | Type::RefMut(_)
                                            | Type::Vec(_)
                                            | Type::Slice(_)
                                            | Type::SliceMut(_)
                                            | Type::Task(_)
                                    )
                            };
                            if opaque(left.ty) || opaque(right.ty)
                            {
                                return Err(Diagnostic::new(
                                    span,
                                    "enum equality and opaque-handle equality are not supported; union values must be narrowed with a match first. Equality requires integers, floats, Char, Bool, or Unit",
                                ));
                            }
                            if left.ty != Type::Never
                                && right.ty != Type::Never
                                && left.ty != right.ty
                            {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "equality operands must have the same type, found {} and {}",
                                        c.types.name(left.ty),
                                        c.types.name(right.ty)
                                    ),
                                ));
                            }
                            Type::Bool
                        }
                        Kind::AmpAmp | Kind::PipePipe => {
                            c.expect(left.ty, Type::Bool, span)?;
                            c.expect(right.ty, Type::Bool, span)?;
                            Type::Bool
                        }
                        _ => return Err(Diagnostic::new(span, "unsupported executable operator")),
                    };
                    let ty = if left.ty == Type::Never
                        || (right.ty == Type::Never && !matches!(op, Kind::AmpAmp | Kind::PipePipe))
                    {
                        Type::Never
                    } else {
                        ty
                    };
                    (
                        ExprKind::Binary(op.clone(), Box::new(left), Box::new(right)),
                        ty,
                    )
                }
                ast::ExprKind::Call { callee, arguments } => {
                    if c.constructor_target(callee).is_some() {
                        return c.construct(callee, Some(arguments), expected, span);
                    }
                    let (target_expr, explicit) = match &callee.kind {
                        ast::ExprKind::Specialize { callee, arguments } => (callee.as_ref(), Some(arguments.as_slice())),
                        _ => (callee.as_ref(), None),
                    };
                    let Some(id) = c.resolution.reference(target_expr.span) else {
                        if let ast::ExprKind::Field { value, name } = &target_expr.kind {
                            if let Some((receiver, method, trait_id, trait_arguments)) =
                                c.qualified_method(target_expr)
                            {
                                return c.user_method_call(
                                    receiver,
                                    method,
                                    Some(trait_id),
                                    trait_arguments,
                                    explicit,
                                    arguments,
                                    expected,
                                    span,
                                );
                            }
                            if Self::builtin_method(name) {
                                return c.method_call(
                                    value, name, explicit, arguments, expected, span,
                                );
                            }
                            return c.user_method_call(
                                value, name, None, None, explicit, arguments, expected, span,
                            );
                        }
                        if explicit.is_some() {
                            return Err(Diagnostic::new(
                                callee.span,
                                "type arguments apply only to a generic named function",
                            ));
                        }
                        return c.indirect_call(callee, arguments, expected, span);
                    };
                    let binding = &c.resolution.bindings[id];
                    if c.logical.names.contains_key(&id) {
                        return Err(Diagnostic::new(
                            callee.span,
                            format!(
                                "checked logical definition '{}' is erased and cannot be called at runtime; pass it only as an erased proof argument",
                                binding.name
                            ),
                        ));
                    }
                    if c.logical.data.contains_key(&id) || c.logical.constructors.contains_key(&id) {
                        return Err(Diagnostic::new(
                            callee.span,
                            format!(
                                "'{}' belongs to a total logical data type and is erased before runtime lowering; pass it only as an erased proof argument",
                                binding.name
                            ),
                        ));
                    }
                    if c.functions.declared.contains_key(&id) {
                        return c.user_call(id, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Task.") {
                        return c.task_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("DynArray.") {
                        return c.dyn_array_call(
                            &binding.name.clone(),
                            explicit,
                            arguments,
                            expected,
                            span,
                        );
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Vec.") || binding.name == "Bytes.at" {
                        return c.vec_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Slice.") {
                        return c.slice_call(&binding.name.clone(), explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("String.") {
                        let name = binding.name.clone();
                        return c.string_call(&name, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name.starts_with("Str.") {
                        let name = binding.name.clone();
                        return c.str_call(&name, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin
                        && (binding.name.starts_with("Int.")
                            || binding.name.starts_with("Char.")
                            || binding.name == "print_int")
                    {
                        let name = binding.name.clone();
                        return c.int_call(&name, explicit, arguments, expected, span);
                    }
                    if binding.kind == BindingKind::Builtin
                        && (binding.name.starts_with("Float.") || binding.name == "print_float")
                    {
                        let name = binding.name.clone();
                        return c.float_call_with(
                            None,
                            &name,
                            explicit,
                            arguments,
                            expected,
                            span,
                        );
                    }
                    if explicit.is_some() {
                        return Err(Diagnostic::new(callee.span, "this callee takes no type arguments"));
                    }
                    if binding.kind == BindingKind::Builtin
                        && matches!(
                            binding.name.as_str(),
                            "Arena.new" | "Arena.alloc" | "ArenaBox.read" | "ArenaBox.take"
                        )
                    {
                        let name = binding.name.as_str();
                        let arity = match name {
                            "Arena.new" => 0,
                            "Arena.alloc" => 2,
                            _ => 1,
                        };
                        if arguments.len() != arity {
                            return Err(Diagnostic::new(
                                span,
                                format!("{name} requires exactly {arity} argument(s)"),
                            ));
                        }
                        match name {
                            "Arena.new" => return c.arena_new(span),
                            "Arena.alloc" => {
                                return c.arena_alloc(&arguments[0], &arguments[1], expected, span);
                            }
                            "ArenaBox.read" => {
                                return c.arena_box_read(&arguments[0], span);
                            }
                            _ => return c.arena_box_take(&arguments[0], span),
                        }
                    }
                    if binding.kind == BindingKind::Builtin && binding.name == "Bytes.try_with_capacity" {
                        if arguments.len() != 1 {
                            return Err(Diagnostic::new(
                                span,
                                "Bytes.try_with_capacity takes exactly one capacity argument",
                            ));
                        }
                        return c.bytes_try_with_capacity(&arguments[0], expected, span);
                    }
                    if binding.kind == BindingKind::Builtin && binding.name == "Bytes.from" {
                        if let [ast::Node { kind: ast::ExprKind::String(text), .. }] = arguments.as_slice() {
                            c.require(ALLOC | PANIC, span)?;
                            let value = Expr { kind: ExprKind::BytesLiteral(text.as_bytes().to_vec()), ty: Type::Bytes, span, resource: None };
                            return match expected {
                                Some(expected) => c.coerce(value, expected, span),
                                None => Ok(value),
                            };
                        }
                        return Err(Diagnostic::new(span, "Bytes.from requires exactly one string literal; general runtime strings are deferred"));
                    }
                    if binding.kind == BindingKind::Builtin && matches!(binding.name.as_str(), "Box.new" | "Box.take" | "Box.read" | "Box.reuse" | "Box.reuse_grow" | "Box.try_new" | "Box.try_reuse" | "drop") {
                        let name = binding.name.as_str();
                        let arity = if matches!(name, "Box.reuse" | "Box.reuse_grow" | "Box.try_reuse") { 2 } else { 1 };
                        if arguments.len() != arity { return Err(Diagnostic::new(span, format!("{name} requires exactly {arity} argument(s)"))); }
                        match name {
                            "Box.reuse" => return c.box_reuse(&arguments[0], &arguments[1], expected, span),
                            "Box.reuse_grow" => return c.box_reuse_grow(&arguments[0], &arguments[1], expected, span),
                            "Box.try_new" => return c.box_try_new(&arguments[0], expected, span),
                            "Box.try_reuse" => return c.box_try_reuse(&arguments[0], &arguments[1], expected, span),
                            _ => {}
                        }
                        let expected_inner = if name == "Box.new" { expected.and_then(|ty| if let Type::Box(index) = ty { Some(c.types.pointees[index]) } else { None }) } else { None };
                        let arg = c.expr_expected(&arguments[0], expected_inner)?;
                        let (kind, ty) = match name {
                            "Box.new" => {
                                c.require(ALLOC | PANIC, span)?;
                                if arg.ty == Type::Never { return Err(Diagnostic::new(span, "Box.new cannot store a divergent value")); }
                                if crate::runtime_types::has_borrow(c.types, arg.ty) && !arg.ty.is_ref() { return Err(Diagnostic::new(span, "Box.new can store a reference element or an ordinary value, but not a slice view, borrowed record, or text view; keep those in a lexical record")); }
                                if crate::runtime_types::contains_task(c.types, arg.ty) { return Err(Diagnostic::new(span, "task handles cannot be stored in Box; join them in the scope that owns them")); }
                                let pointee = match expected_inner {
                                    Some(inner) if matches!(inner, Type::Annotated(..)) => inner,
                                    _ => c.types.full(arg.ty, span)?,
                                };
                                let ty = Type::Box(c.types.pointer(pointee)); (ExprKind::BoxNew(Box::new(arg)), ty)
                            }
                            "Box.take" => { let Type::Box(index) = arg.ty else { return Err(Diagnostic::new(span, "Box.take requires an owned Box<T>")); }; let ty = c.unannotate(c.types.pointees[index]); (ExprKind::BoxTake(Box::new(arg)), ty) }
                            "Box.read" => { let Type::Ref(index) = arg.ty else { return Err(Diagnostic::new(span, "Box.read requires an immutable &Box<T>")); }; let Type::Box(inner) = c.types.pointees[index] else { return Err(Diagnostic::new(span, "Box.read requires an immutable &Box<T>, not another borrow type")); }; let payload = c.types.pointees[inner]; if matches!(c.unannotate(payload), Type::RefMut(_)) { return Err(Diagnostic::new(span, "Box.read cannot copy an exclusive reference element; move it out with Box.take")); } let ty = c.unannotate(payload); (ExprKind::BoxRead(Box::new(arg)), ty) }
                            _ => { if matches!(arg.ty, Type::Ref(_) | Type::RefMut(_)) { return Err(Diagnostic::new(span, "drop consumes owned/copy values, not borrowed handles")); } (ExprKind::Drop(Box::new(arg)), Type::Unit) }
                        };
                        let value = Expr { kind, ty, span, resource: None };
                        return match expected {
                            Some(expected) => c.coerce(value, expected, span),
                            None => Ok(value),
                        };
                    }
                    let bytes_op = (binding.kind == BindingKind::Builtin).then(|| BytesOp::named(&binding.name)).flatten();
                    let io_op = (binding.kind == BindingKind::Builtin).then(|| IoOp::named(&binding.name)).flatten();
                    let (target, parameters, result, effects) = if let Some(op) = io_op {
                        match op {
                            IoOp::Stdin => (Target::Io(op, None), vec![], Type::Stdin, IO),
                            IoOp::Stdout => (Target::Io(op, None), vec![], Type::Stdout, IO),
                            IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk | IoOp::Write => {
                                let ok = if matches!(op, IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk) { Type::Bytes } else { Type::Unit };
                                let result = c.types.io_result(ok, span)?;
                                let shape = c.types.result(result, span)?;
                                let parameters = if matches!(op, IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk) {
                                    vec![Type::Stdin, Type::Bytes]
                                } else {
                                    vec![Type::Stdout, Type::Ref(c.types.pointer(Type::Bytes))]
                                };
                                (Target::Io(op, Some(shape)), parameters, result, IO)
                            }
                        }
                    } else if let Some(op) = bytes_op {
                        let borrowed = Type::Ref(c.types.pointer(Type::Bytes));
                        let parameters = match op {
                            BytesOp::Clear => vec![Type::Bytes], BytesOp::WithCapacity => vec![Type::I64], BytesOp::Len | BytesOp::Capacity | BytesOp::Copy => vec![borrowed],
                            BytesOp::Get => vec![borrowed, Type::I64], BytesOp::Push | BytesOp::PushReserved => vec![Type::Bytes, Type::I64],
                        };
                        let result = match op { BytesOp::Len | BytesOp::Capacity | BytesOp::Get => Type::I64, _ => Type::Bytes };
                        let effects = match op { BytesOp::Len | BytesOp::Capacity | BytesOp::Clear => 0, BytesOp::Get | BytesOp::PushReserved => PANIC, _ => ALLOC | PANIC };
                        (Target::Bytes(op), parameters, result, effects)
                    } else if binding.kind == BindingKind::Builtin && binding.name == "print_i64" {
                        (Target::Print, vec![Type::I64], Type::Unit, IO | PANIC)
                    } else if binding.kind == BindingKind::Builtin && binding.name == "panic" {
                        (Target::Panic, vec![], Type::Never, PANIC)
                    } else {
                        if explicit.is_some() {
                            return Err(Diagnostic::new(
                                callee.span,
                                "this callee takes no type arguments",
                            ));
                        }
                        return c.indirect_call(callee, arguments, expected, span);
                    };
                    if parameters.len() != arguments.len() {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "wrong argument count: expected {}, found {}",
                                parameters.len(),
                                arguments.len()
                            ),
                        ));
                    }
                    c.require(effects, span)?;
                    let mut args = Vec::new();
                    let mut diverges = false;
                    for (arg, ty) in arguments.iter().zip(parameters) {
                        let arg = c.expr_expected(arg, Some(ty))?;
                        c.expect(arg.ty, ty, arg.span)?;
                        diverges |= arg.ty == Type::Never;
                        args.push(arg);
                    }
                    (
                        ExprKind::Call(target, args),
                        if diverges { Type::Never } else { result },
                    )
                }
                ast::ExprKind::Return(value) => {
                    let value = if let Some(value) = value {
                        c.expr_expected_result(value, Some(c.result))?
                    } else {
                        let unit = Expr {
                            kind: ExprKind::Constant(0),
                            ty: Type::Unit,
                            span,
                            resource: None,
                        };
                        c.coerce(unit, c.result, span)?
                    };
                    if !(c.erased_result_context(Some(c.result)) && value.ty == Type::Unit) {
                        c.expect(value.ty, c.result, span)?;
                    }
                    if c.observes_copyable_result(&value)
                        && !c.transfers_copyable_result_from(&value)
                    {
                        return Err(Diagnostic::new(
                            value.span,
                            "this returns a copyable result with the must-use `@[1]` contract through an ungraded result; annotate the function result as '@[1]' so every caller inherits exactly one observation, or observe the value here",
                        ));
                    }
                    (ExprKind::Return(Box::new(value)), Type::Never)
                }
                ast::ExprKind::If {
                    condition,
                    then,
                    otherwise,
                } => {
                    let condition = c.expr(condition)?;
                    c.expect(condition.ty, Type::Bool, condition.span)?;
                    let baseline = c.facts.clone();
                    let facts = c.facts.condition(&condition, true);
                    c.facts.add(facts);
                    let has_else = otherwise.is_some();
                    let then_expected = if has_else { expected } else { Some(Type::Unit) };
                    let then = c.block(then, then_expected);
                    let then_facts = c.facts.clone();
                    c.facts = baseline.clone();
                    let then = then?;
                    let otherwise = if let Some(otherwise) = otherwise {
                        let facts = c.facts.condition(&condition, false);
                        c.facts.add(facts);
                        let context = match expected {
                            Some(expected) => Some(expected),
                            None if c.needs_context(otherwise) && then.ty != Type::Never => {
                                Some(c.types.full(then.ty, span)?)
                            }
                            None => None,
                        };
                        let tail = c.expr_expected_result(otherwise, context);

                        let tail = tail?;
                        let ty = tail.ty;
                        Block {
                            statements: vec![],
                            tail: Some(Box::new(tail)),
                            ty,
                        }
                    } else {
                        Block {
                            statements: vec![],
                            tail: None,
                            ty: Type::Unit,
                        }
                    };
                    c.facts = crate::facts::Facts::branch_join(&baseline, &then_facts, &c.facts);
                    let (then, otherwise, ty) = if has_else {
                        if c.erased_result_context(expected)
                            && (then.ty == Type::Unit || otherwise.ty == Type::Unit)
                        {
                            (c.erase_block_value(then, span), c.erase_block_value(otherwise, span), Type::Unit)
                        } else {
                            let ty = c.join(then.ty, otherwise.ty, span)?;
                            let then = c.coerce_block(then, ty, span)?;
                            let otherwise = c.coerce_block(otherwise, ty, span)?;
                            (then, otherwise, ty)
                        }
                    } else {
                        // An `if` without `else` is a statement: the taken
                        // branch must produce Unit, never an implicit optional
                        // union value.
                        let then = c.coerce_block(then, Type::Unit, span)?;
                        (then, otherwise, Type::Unit)
                    };
                    (ExprKind::If(Box::new(condition), then, otherwise), ty)
                }
                ast::ExprKind::Try(value) => {
                    let value = c.expr(value)?;
                    let input = c.types.result(value.ty, span)?;
                    let output = c.types.result(c.result, span)?;
                    c.expect(input.error, output.error, span)?;
                    if !c.same_layout(input.error, output.error) {
                        return Err(Diagnostic::new(
                            span,
                            "'?' cannot repack a heterogeneous error type; widen the operand explicitly or match the error before returning",
                        ));
                    }
                    let ty = input.ok;
                    (
                        ExprKind::Try {
                            value: Box::new(value),
                            input,
                            output,
                        },
                        ty,
                    )
                }
                ast::ExprKind::Match { value, arms } => {
                    let value = c.expr(value)?;
                    if matches!(value.ty, Type::Never | Type::Ref(_) | Type::RefMut(_)) || value.ty.is_view() {
                        return Err(Diagnostic::new(
                            value.span,
                            "cannot match a divergent, borrowed-reference, or borrowed-view expression (including &str)",
                        ));
                    }
                    let mut coverage = Coverage::new(span);
                    // Variants excluded by the scrutinee's type need no arm.
                    if let Type::Variants(id, mask) = value.ty {
                        for (tag, variant) in c.types.enums[id].variants.iter().enumerate() {
                            if mask & (1 << tag) == 0 {
                                coverage.add(&Pattern::Variant {
                                    tag,
                                    fields: variant.fields.iter().map(|_| (0, Pattern::Any)).collect(),
                                });
                            }
                        }
                    }
                    let mut result = Type::Never;
                    let mut checked = Vec::new();
                    // Variants still possible after earlier unguarded arms.
                    let mut remaining = c.mask(value.ty);
                    for arm in arms {
                        let pattern = c.pattern_refined(&arm.pattern, value.ty, remaining)?;
                        c.linear_pattern(&pattern, c.value_moves_linear(&value));
                        if !coverage.useful(&pattern, value.ty, &c.types.enums, &c.types.unions)? {
                            return Err(Diagnostic::new(arm.span, "unreachable match arm/pattern"));
                        }
                        let mark = c.facts.mark();
                        let guard = arm.guard.as_ref().map(|guard| c.expr(guard)).transpose()?;
                        if let Some(guard) = &guard {
                            c.expect(guard.ty, Type::Bool, guard.span)?;
                            let facts = c.facts.condition(guard, true);
                            c.facts.add(facts);
                        }
                        let context = match expected {
                            Some(expected) => Some(expected),
                            None if c.needs_context(&arm.body) && result != Type::Never => {
                                Some(c.types.full(result, span)?)
                            }
                            None => None,
                        };
                        let body = c.expr_expected_result(&arm.body, context);
                        c.facts.reset(mark);
                        let body = body?;
                        result = c.join(result, body.ty, body.span)?;
                        if guard.is_none() {
                            remaining &= !covered_variants(&pattern);
                        }
                        if guard.is_none() {
                            coverage.add(&pattern);
                        }
                        checked.push(Arm {
                            pattern,
                            guard,
                            body,
                        });
                    }
                    if coverage.useful(&Pattern::Any, value.ty, &c.types.enums, &c.types.unions)? {
                        return Err(Diagnostic::new(
                            span,
                            "non-exhaustive match; add missing cases or an unguarded catch-all",
                        ));
                    }
                    if c.erased_result_context(expected)
                        && (checked.iter().any(|arm| {
                            arm.body.ty == Type::Unit || arm.body.ty == Type::Never
                        }))
                    {
                        for arm in &mut checked {
                            if arm.body.ty == Type::Never {
                                continue;
                            }
                            let placeholder = Expr {
                                kind: ExprKind::Constant(0),
                                ty: Type::Unit,
                                span: arm.body.span,
                                resource: None,
                            };
                            let body = std::mem::replace(&mut arm.body, placeholder);
                            arm.body = c.erase_value(body, span);
                        }
                        result = Type::Unit;
                    }
                    if result != Type::Never && result != expected.unwrap_or(Type::Never) {
                        for arm in &mut checked {
                            if arm.body.ty == Type::Never {
                                continue;
                            }
                            let placeholder = Expr {
                                kind: ExprKind::Constant(0),
                                ty: Type::Unit,
                                span: arm.body.span,
                                resource: None,
                            };
                            let body = std::mem::replace(&mut arm.body, placeholder);
                            arm.body = c.coerce(body, result, span)?;
                        }
                    }
                    (ExprKind::Match(Box::new(value), checked), result)
                }
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this expression is not implemented in the executable subset yet",
                    ));
                }
            };
            let expr = Expr {
                kind,
                ty,
                span,
                resource: None,
            };
            if let Some(expected) = expected {
                return c.coerce(expr, expected, span);
            }
            Ok(expr)
        })
    }
    /// Whether checking `expr` needs an expected type to infer a generic
    /// constructor/record. Used only to preserve that inference for a later
    /// branch without forcing an unrelated branch into an earlier type.
    fn needs_context(&self, expr: &ast::Expr) -> bool {
        if let Some((id, arguments)) = self.constructor_target(expr) {
            let (owner, _) = self.types.owner(id);
            if arguments.is_empty() && self.types.generic_count(owner) != 0 {
                return true;
            }
        }
        match &expr.kind {
            ast::ExprKind::Block(block) => block
                .tail
                .as_deref()
                .is_some_and(|tail| self.needs_context(tail)),
            ast::ExprKind::If {
                then, otherwise, ..
            } => {
                then.tail
                    .as_deref()
                    .is_some_and(|tail| self.needs_context(tail))
                    || otherwise
                        .as_deref()
                        .is_some_and(|otherwise| self.needs_context(otherwise))
            }
            ast::ExprKind::Match { arms, .. } => {
                arms.iter().any(|arm| self.needs_context(&arm.body))
            }
            ast::ExprKind::Record { ty, .. } => {
                if matches!(ty.kind, ast::ExprKind::Specialize { .. }) {
                    return false;
                }
                self.resolution.reference(ty.span).is_some_and(|id| {
                    self.types.is_record(id) && !self.types.record_fields(id).0.is_empty()
                })
            }
            _ => false,
        }
    }
    /// The binding at the root of a name/field/specialization expression, used
    /// to reject erased logical data before any runtime meaning is invented.
    fn logical_data_root(&self, expr: &ast::Expr) -> Option<BindingId> {
        match &expr.kind {
            ast::ExprKind::Name(_) | ast::ExprKind::Field { .. } => {
                self.resolution.reference(expr.span)
            }
            ast::ExprKind::Specialize { callee, .. } => self.logical_data_root(callee),
            _ => None,
        }
    }
    fn constructor_target<'e>(&self, expr: &'e ast::Expr) -> Option<(BindingId, &'e [ast::Type])> {
        let (base, arguments) = match &expr.kind {
            ast::ExprKind::Specialize { callee, arguments } => {
                (callee.as_ref(), arguments.as_slice())
            }
            _ => (expr, &[][..]),
        };
        let id = self.resolution.reference(base.span)?;
        (self.resolution.bindings[id].kind == BindingKind::Constructor
            && !self.logical.constructors.contains_key(&id))
        .then_some((id, arguments))
    }
    fn construct(
        &mut self,
        callee: &ast::Expr,
        values: Option<&[ast::Expr]>,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let (id, arguments) = self.constructor_target(callee).unwrap();
        let (owner, tag) = self.types.owner(id);
        let mut expected_layout = None;
        if let Some(index) = expected.and_then(Type::layout) {
            if self.types.enums[index].definition != owner {
                return Err(Diagnostic::new(
                    span,
                    "constructor belongs to a different enum than the expected type",
                ));
            }
            expected_layout = Some(index);
        } else if arguments.is_empty()
            && let Some(Type::Union(union)) = expected
        {
            let matching = self.types.unions[union]
                .members
                .iter()
                .filter_map(|member| {
                    member
                        .layout()
                        .filter(|index| self.types.enums[*index].definition == owner)
                })
                .collect::<Vec<_>>();
            match matching.as_slice() {
                [] => {}
                [index] => expected_layout = Some(*index),
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this constructor fits several union alternatives; write explicit type arguments",
                    ));
                }
            }
        }
        let enum_id = if arguments.is_empty() {
            if let Some(index) = expected_layout {
                index
            } else {
                if self.types.generic_count(owner) != 0 {
                    return Err(Diagnostic::new(
                        span,
                        "generic constructor needs an expected enum type or explicit constructor::<type arguments>",
                    ));
                }
                self.types
                    .instantiate(owner, vec![], vec![], vec![], span)?
            }
        } else {
            let kinds = self.types.generic_kinds(owner);
            if arguments.len() != kinds.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "constructor expects {} type arguments, found {}",
                        kinds.len(),
                        arguments.len()
                    ),
                ));
            }
            let mut args = Vec::new();
            let mut consts = Vec::new();
            for (argument, is_const) in arguments.iter().zip(kinds) {
                if is_const {
                    consts.push(crate::length::eval_type(
                        self.resolution,
                        self.logical,
                        &self.consts,
                        argument,
                    )?);
                } else {
                    let ty = self.ty(argument)?;
                    args.push(self.types.full(ty, span)?);
                }
            }
            self.types.instantiate(owner, args, consts, vec![], span)?
        };
        let variant = self.types.enums[enum_id].variants[tag].clone();
        if variant.tuple != values.is_some() {
            return Err(Diagnostic::new(
                span,
                "tuple variants require a call; unit variants are values without parentheses",
            ));
        }
        let values = values.unwrap_or(&[]);
        if values.len() != variant.fields.len() {
            return Err(Diagnostic::new(span, "wrong enum payload arity"));
        }
        if self.types.enums[enum_id].name == "TaskExit"
            && variant
                .fields
                .iter()
                .any(|ty| crate::runtime_types::has_borrow(self.types, *ty))
        {
            return Err(Diagnostic::new(
                span,
                "TaskExit<T> with a borrowed payload is produced only by Task.join; construct the record first, or join the child task and match its result",
            ));
        }
        let mut fields = Vec::new();
        let mut diverges = false;
        for (value, ty) in values.iter().zip(variant.fields) {
            let value = self.expr_expected(value, Some(ty))?;
            diverges |= value.ty == Type::Never;
            fields.push(value);
        }
        // A constructor's principal type is its single variant.
        let ty = if diverges {
            Type::Never
        } else {
            crate::runtime_types::refine(&self.types.enums, enum_id, 1 << tag)
        };
        let value = Expr {
            kind: ExprKind::Construct {
                enum_id,
                tag,
                fields,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    fn temp(&mut self, ty: Type, span: Span) -> Result<usize> {
        if self.locals.len() >= 1024 {
            return Err(Diagnostic::new(
                span,
                "function exceeds the 1024-local limit",
            ));
        }
        self.locals.push(Local {
            ty,
            mutable: false,
            linear: false,
            grade: None,
            span,
        });
        Ok(self.locals.len() - 1)
    }
    /// Check an explicitly typed lambda. Captures are discovered from resolved
    /// names; a noncapturing lambda is a copyable function pointer, while a
    /// lambda capturing affine owned storage is an owning once-consuming
    /// closure. Capturing a linear `@[1]`/`#[linear]` obligation produces a
    /// `linear once fn` value whose environment must be consumed by a call.
    fn lambda(
        &mut self,
        lambda: &ast::Lambda,
        span: Span,
        expected: Option<Type>,
        scope_root: bool,
    ) -> Result<Expr> {
        let captures = self.lambda_captures(lambda);
        let once = !captures.is_empty();
        if once && matches!(expected, Some(Type::Fn(_))) {
            return Err(Diagnostic::new(
                span,
                "a capturing lambda has an owned environment and must be used as 'once fn(...)'; it cannot be a copyable 'fn(...)' value",
            ));
        }
        let mut capture_linear = false;
        if let Some(slot) = captures
            .iter()
            .find(|slot| self.locals[**slot].ty == Type::Str)
        {
            return Err(Diagnostic::new(
                span,
                "a lambda or task cannot capture a borrowed '&str' text view; call a named function with an explicit lifetime instead",
            )
            .with_note(self.locals[*slot].span, "text view declared here"));
        }
        let borrowed_capture = captures.iter().any(|slot| {
            self.locals[*slot].ty.is_slice()
                || self.carrier_type(self.locals[*slot].ty)
                || crate::runtime_types::is_reference_container(self.types, self.locals[*slot].ty)
        });
        for slot in &captures {
            let local = self.locals[*slot];
            let ty = local.ty;
            if crate::runtime_types::contains_task_exit_borrow(self.types, ty) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda or task cannot capture TaskExit<T> with a borrowed payload; match it inside the scope that joined it",
                )
                .with_note(local.span, "joined borrowed result declared here"));
            }
            if matches!(ty, Type::Ref(_) | Type::RefMut(_)) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda cannot capture a borrowed owner reference; pass it as an explicit call argument while its owner is live",
                )
                .with_note(self.locals[*slot].span, "captured borrow declared here"));
            }
            if matches!(ty, Type::Task(_)) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda cannot capture a task handle; join it in the scope that owns it",
                )
                .with_note(self.locals[*slot].span, "task handle declared here"));
            }
            if local.grade.is_some_and(Grade::is_zero) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda cannot capture a value graded @[0]; grade zero forbids every observation, including moving it into a closure environment",
                )
                .with_note(local.span, "grade @[0] binding declared here"));
            }
            if let Some(grade) = local.grade
                && !grade.is_one()
                && !grade.is_zero()
                && !grade.is_many()
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "a lambda cannot capture a value graded @[{grade}]; a closure may be called zero or one time, so the exact use obligation cannot be transferred. Leave the value ungraded or observe it before constructing the closure"
                    ),
                )
                .with_note(local.span, "graded binding declared here"));
            }
            if local.linear || local.grade.is_some_and(Grade::is_one) || self.linear_type(ty) {
                capture_linear = true;
            }
        }
        let linear = once && capture_linear;
        if linear
            && matches!(expected, Some(Type::Once(id)) if !self.types.function_types[id].linear)
        {
            return Err(Diagnostic::new(
                span,
                "a lambda capturing linear obligations must be used as 'linear once fn(...)'; widening it to an affine 'once fn(...)' would allow an uncalled closure to drop those obligations",
            ));
        }
        if once {
            self.require(ALLOC | PANIC, span)?;
        }
        let mut parameters = Vec::with_capacity(lambda.parameters.len());
        let mut parameter_grades = Vec::with_capacity(lambda.parameters.len());
        for parameter in &lambda.parameters {
            if parameter.erased {
                return Err(Diagnostic::new(
                    parameter.span,
                    "lambda parameters cannot be erased proof parameters; function values have no erased argument list",
                ));
            }
            let (inner, grade) = split_grade(&parameter.ty);
            let grade = grade
                .map(|grade| grades::evaluate(self.resolution, &self.grades, grade))
                .transpose()?;
            let ty = self.ty(inner)?;
            // Slice parameters have independent lifetimes. A lambda may also
            // take a record with borrowed slice fields by value; its per-field
            // contract travels in the callable's borrow signature.
            if !ty.is_slice()
                && !ty.is_ref()
                && !crate::runtime_types::is_borrowed_record(self.types, ty)
                && !crate::runtime_types::is_reference_container(self.types, ty)
                && !crate::runtime_types::is_borrowed_task_exit(self.types, ty)
                && crate::runtime_types::has_borrow(self.types, ty)
            {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "a function value cannot take an owner reference or &str text-view parameter; references, slice views, reference containers, and records with borrowed fields are supported",
                ));
            }
            self.validate_grade(grade, ty, parameter.ty.span, false)?;
            parameters.push(ty);
            parameter_grades.push(grade);
        }
        let (result_inner, result_grade) =
            result_contract(self.resolution, self.types, &self.grades, &lambda.result)?;
        let result = self.ty(&result_inner)?;
        validate_result_contract(
            result_grade,
            self.owned_type(result),
            &self.types.name(result),
            lambda.result.span,
        )?;
        if result.is_view() && !result.is_slice() {
            return Err(Diagnostic::new(
                lambda.result.span,
                "a lambda cannot return a borrowed '&str' text view; use a named function or a slice view",
            ));
        }
        if crate::runtime_types::contains_task(self.types, result) {
            return Err(Diagnostic::new(
                lambda.result.span,
                "a function value cannot return a task handle; a child handle must not escape its scope",
            ));
        }
        let effects = crate::runtime_types::effect_bits_with(
            self.resolution,
            &lambda.effects,
            &self.effect_arguments,
        )?;
        let lambda_lifetimes = parameters
            .iter()
            .enumerate()
            .map(|(index, ty)| (ty.is_slice() || ty.is_ref()).then(|| format!("<lambda {index}>")))
            .collect::<Vec<_>>();
        let capture_lifetimes = captures
            .iter()
            .enumerate()
            .map(|(index, slot)| {
                self.locals[*slot].ty.is_slice().then(|| {
                    self.parameter_lifetimes
                        .get(*slot)
                        .cloned()
                        .flatten()
                        .unwrap_or_else(|| format!("<lambda capture {index}>"))
                })
            })
            .collect::<Vec<_>>();
        let parameter_leaves = parameters
            .iter()
            .map(|ty| {
                if crate::runtime_types::is_borrowed_record(self.types, *ty)
                    || crate::runtime_types::is_reference_container(self.types, *ty)
                    || crate::runtime_types::is_borrowed_task_exit(self.types, *ty)
                {
                    crate::runtime_types::borrow_leaves(self.types, *ty)
                } else {
                    Vec::new()
                }
            })
            .collect::<Vec<_>>();
        // Labels available from call parameters and from the closure
        // environment. Ambiguity between these origins is rejected: a scoped
        // capture result is only expressible when exactly one capture supplies
        // it, and a parameter result must stay on the parameter contract.
        let parameter_slice_mutability = lambda_lifetimes
            .iter()
            .enumerate()
            .filter_map(|(index, label)| {
                label.as_ref().map(|label| {
                    (
                        label.clone(),
                        parameters[index].is_mut_slice()
                            || matches!(parameters[index], Type::RefMut(_)),
                    )
                })
            })
            .collect::<BTreeMap<_, _>>();
        let mut parameter_leaf_labels: BTreeMap<String, bool> = BTreeMap::new();
        for leaves in &parameter_leaves {
            for leaf in leaves {
                if let Some(label) = &leaf.lifetime {
                    parameter_leaf_labels
                        .entry(label.clone())
                        .and_modify(|mutable| *mutable |= leaf.mutable)
                        .or_insert(leaf.mutable);
                }
            }
        }
        let capture_slice_labels = capture_lifetimes
            .iter()
            .enumerate()
            .filter_map(|(index, label)| {
                label.as_ref().and_then(|label| {
                    self.locals[captures[index]]
                        .ty
                        .is_slice()
                        .then(|| (label.clone(), index))
                })
            })
            .collect::<BTreeMap<_, _>>();
        let mut capture_leaf_labels: BTreeMap<String, Vec<(usize, Vec<usize>, bool)>> =
            BTreeMap::new();
        for (index, slot) in captures.iter().enumerate() {
            let ty = self.locals[*slot].ty;
            if !crate::runtime_types::is_borrowed_record(self.types, ty) {
                continue;
            }
            for leaf in crate::runtime_types::borrow_leaves(self.types, ty) {
                if let Some(label) = &leaf.lifetime {
                    capture_leaf_labels.entry(label.clone()).or_default().push((
                        index,
                        leaf.path,
                        leaf.mutable,
                    ));
                }
            }
        }
        let mut candidates = Vec::new();
        candidates.extend(parameter_slice_mutability.keys().cloned());
        candidates.extend(parameter_leaf_labels.keys().cloned());
        candidates.extend(capture_slice_labels.keys().cloned());
        candidates.extend(capture_leaf_labels.keys().cloned());
        candidates.sort();
        candidates.dedup();
        let mut lambda_result_lifetime = None;
        let mut borrow_result_lifetime = None;
        let mut borrow_result_leaves: Vec<crate::runtime_types::BorrowLeaf> = Vec::new();
        let mut capture_result = crate::runtime_types::CaptureResultSig::default();
        let mut capture_result_used = false;
        if result.is_slice() {
            let explicit = borrow_lifetime(&lambda.result);
            if !once
                && (explicit.is_some()
                    || lambda
                        .parameters
                        .iter()
                        .any(|parameter| borrow_lifetime(&parameter.ty).is_some()))
            {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "slice-returning lambdas use lifetime elision; use a named function for explicit lifetime binders",
                ));
            }
            let lifetime = match explicit {
                Some(name) => {
                    if !candidates.contains(&name) {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            format!(
                                "the lambda result lifetime '{name}' does not appear on a borrowed parameter, captured view, or captured record field; a lambda cannot return a borrow for an outer lifetime it does not receive"
                            ),
                        ));
                    }
                    name
                }
                None => match candidates.as_slice() {
                    [only] => only.clone(),
                    [] => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "a slice-returning lambda needs exactly one borrowed parameter, captured view, or captured record field to borrow from",
                        ));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "cannot infer this lambda result's lifetime from several borrowed parameters or captures; a scoped callable result must have exactly one possible origin",
                        ));
                    }
                },
            };
            let mut parameter_sources = Vec::new();
            if let Some(mutable) = parameter_slice_mutability.get(&lifetime) {
                parameter_sources.push(*mutable);
            }
            if let Some(mutable) = parameter_leaf_labels.get(&lifetime) {
                parameter_sources.push(*mutable);
            }
            let mut capture_sources = Vec::new();
            if let Some(index) = capture_slice_labels.get(&lifetime) {
                let mutable = self.locals[captures[*index]].ty.is_mut_slice();
                capture_sources.push((*index, None, mutable));
            }
            if let Some(leaves) = capture_leaf_labels.get(&lifetime) {
                capture_sources.extend(
                    leaves
                        .iter()
                        .map(|(capture, path, mutable)| (*capture, Some(path.clone()), *mutable)),
                );
            }
            if !parameter_sources.is_empty() && !capture_sources.is_empty() {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "this lambda result borrows from both a call parameter and a captured view; a scoped capture result and a parameter result cannot be mixed or unified",
                ));
            }
            if capture_sources.is_empty() {
                if parameter_sources.is_empty() {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "the lambda result lifetime '{lifetime}' is not outlived by any borrowed parameter, so no call could produce it"
                        ),
                    ));
                }
                if result.is_mut_slice() && !parameter_sources.iter().any(|mutable| *mutable) {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "an exclusive slice result requires an exclusive slice parameter or exclusive record field",
                    ));
                }
                lambda_result_lifetime = Some(lifetime.clone());
                borrow_result_lifetime = Some(lifetime);
            } else {
                let [(capture, path, mutable)] = capture_sources.as_slice() else {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "cannot infer this lambda result's capture origin: several captured views or record fields carry the same lifetime",
                    ));
                };
                if result.is_mut_slice() && !*mutable {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "an exclusive slice result cannot be borrowed from a shared captured view or shared captured record field",
                    ));
                }
                capture_result.slice = Some(crate::runtime_types::CaptureSliceSig {
                    capture: *capture,
                    path: path.clone(),
                    mutable: *mutable,
                });
                capture_result_used = true;
                // The child function still needs the declared result lifetime
                // for its own return check; the callable's visible result
                // lifetime stays empty because the environment is the source.
                lambda_result_lifetime = Some(lifetime);
            }
        } else if result.is_ref() {
            let explicit = borrow_lifetime(&lambda.result);
            let lifetime = match explicit {
                Some(name) => {
                    if !candidates.contains(&name) {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            format!(
                                "the lambda result lifetime '{name}' does not appear on a reference parameter, borrowed container, or borrowed record field"
                            ),
                        ));
                    }
                    name
                }
                None => match candidates.as_slice() {
                    [only] => only.clone(),
                    [] => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "a reference-returning lambda needs exactly one borrowed parameter, container, or record field to borrow from",
                        ));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "cannot infer this lambda reference result's lifetime from several borrowed inputs; use a named function or an explicit result lifetime",
                        ));
                    }
                },
            };
            if capture_slice_labels.contains_key(&lifetime)
                || capture_leaf_labels.contains_key(&lifetime)
            {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "a lambda cannot return a reference borrowed from a captured local or capture environment; derive the reference from a call parameter instead",
                ));
            }
            let parameter_mutability = parameter_slice_mutability
                .get(&lifetime)
                .copied()
                .into_iter()
                .chain(parameter_leaf_labels.get(&lifetime).copied());
            let sources = parameter_mutability.clone().collect::<Vec<_>>();
            if sources.is_empty() {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "the lambda reference result is not outlived by any reference parameter or borrowed field",
                ));
            }
            if matches!(result, Type::RefMut(_)) && !sources.iter().any(|mutable| *mutable) {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "an exclusive reference result requires an exclusive reference parameter or exclusive borrowed field",
                ));
            }
            lambda_result_lifetime = Some(lifetime.clone());
            borrow_result_lifetime = Some(lifetime);
        } else if crate::runtime_types::is_borrowed_record(self.types, result)
            || crate::runtime_types::is_reference_container(self.types, result)
            || crate::runtime_types::is_borrowed_task_exit(self.types, result)
        {
            let leaves = crate::runtime_types::borrow_leaves(self.types, result);
            let mut parameter_leaves = Vec::new();
            let mut capture_leaves = Vec::new();
            let slice_captures = capture_slice_labels.values().copied().collect::<Vec<_>>();
            for leaf in leaves {
                let Some(label) = &leaf.lifetime else {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "internal error: borrowed lambda result leaf has no lifetime",
                    ));
                };
                let parameter_source = parameter_leaf_labels
                    .get(label)
                    .copied()
                    .or_else(|| parameter_slice_mutability.get(label).copied());
                let capture_sources = capture_leaf_labels.get(label);
                let capture_slice_source = capture_slice_labels.get(label).copied().or_else(|| {
                    (slice_captures.len() == 1 && capture_sources.is_none())
                        .then(|| slice_captures[0])
                });
                if parameter_source.is_some()
                    && (capture_sources.is_some() || capture_slice_source.is_some())
                {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "the lambda result field lifetime '{label}' has both a call-parameter and a captured origin; the two cannot be unified"
                        ),
                    ));
                }
                if let Some(mutable) = parameter_source {
                    if leaf.mutable && !mutable {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "an exclusive result field requires an exclusive borrowed parameter field",
                        ));
                    }
                    parameter_leaves.push(leaf);
                    continue;
                }
                let Some(sources) = capture_sources else {
                    if let Some(capture) = capture_slice_source {
                        // A payload slice field may be built directly from a
                        // captured slice view of the same declared lifetime.
                        let mutable = self.locals[captures[capture]].ty.is_mut_slice();
                        if leaf.mutable && !mutable {
                            return Err(Diagnostic::new(
                                lambda.result.span,
                                "an exclusive result field cannot be borrowed from a shared captured slice view",
                            ));
                        }
                        capture_leaves.push(crate::runtime_types::CaptureLeafSig {
                            path: leaf.path,
                            capture,
                            mutable,
                        });
                        continue;
                    }
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "the lambda result field lifetime '{label}' is not outlived by any borrowed parameter or captured record field"
                        ),
                    ));
                };
                let matching = sources
                    .iter()
                    .filter(|(_, path, _)| *path == leaf.path)
                    .collect::<Vec<_>>();
                let [(capture, _, mutable)] = matching.as_slice() else {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "cannot infer this lambda result field's capture origin: field path {:?} is not supplied by exactly one captured record",
                            leaf.path
                        ),
                    ));
                };
                if leaf.mutable && !*mutable {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "an exclusive result field cannot be borrowed from a shared captured record field",
                    ));
                }
                capture_leaves.push(crate::runtime_types::CaptureLeafSig {
                    path: leaf.path,
                    capture: *capture,
                    mutable: *mutable,
                });
            }
            if !capture_leaves.is_empty() && !parameter_leaves.is_empty() {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "this lambda returns a record mixing captured and call-parameter borrows; split the record or return one origin at a time",
                ));
            }
            if capture_leaves.is_empty() {
                borrow_result_leaves = parameter_leaves;
            } else {
                capture_result.leaves = capture_leaves;
                capture_result_used = true;
            }
        }
        let mut borrows = crate::runtime_types::BorrowSig::canonical_with_leaves(
            &lambda_lifetimes,
            borrow_result_lifetime.as_ref(),
            &parameter_leaves,
            &borrow_result_leaves,
            &BTreeSet::new(),
        );
        if capture_result_used {
            borrows.capture_result = Some(capture_result);
        }
        let function_type = self.types.function_type_with(
            parameters.clone(),
            result,
            effects,
            parameter_grades.clone(),
            result_grade,
            once,
            linear,
            borrows,
        );
        let capture_types = captures
            .iter()
            .map(|slot| self.locals[*slot].ty)
            .collect::<Vec<_>>();
        let capture_obligations = captures
            .iter()
            .map(|slot| {
                let local = self.locals[*slot];
                (
                    local.grade,
                    local.linear
                        || local.grade.is_some_and(Grade::is_one)
                        || self.linear_type(local.ty),
                )
            })
            .collect::<Vec<_>>();
        let capture_exprs = captures
            .iter()
            .map(|slot| Expr {
                kind: ExprKind::Local(*slot),
                ty: self.locals[*slot].ty,
                span: self.locals[*slot].span,
                resource: None,
            })
            .collect::<Vec<_>>();
        // Check the lambda body in a fresh function context.
        let capture_mutable = captures
            .iter()
            .map(|slot| self.locals[*slot].mutable)
            .collect::<Vec<_>>();
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_slots = std::mem::take(&mut self.slots);
        let saved_result = self.result;
        let saved_parameter_lifetimes = std::mem::take(&mut self.parameter_lifetimes);
        let saved_result_grade = self.result_grade;
        let saved_effects = self.effects;
        let saved_loops = std::mem::take(&mut self.loops);
        let saved_facts = std::mem::take(&mut self.facts);
        let capture_ids = captures
            .iter()
            .map(|slot| {
                saved_slots
                    .iter()
                    .find(|(_, outer)| *outer == slot)
                    .map(|(id, _)| *id)
            })
            .collect::<Vec<_>>();
        let kernel_mark = self.kernel_locals.len();
        let saved_scope_depth = self.scope_depth;
        // A handler is lexical to direct performs in the enclosing function
        // body, never to indirect calls. A lambda is a separate callable, so it
        // cannot capture the hidden handler local by name.
        let saved_handlers = std::mem::take(&mut self.handlers);
        let mut child_parameter_lifetimes = capture_lifetimes.clone();
        child_parameter_lifetimes.extend(lambda_lifetimes.clone());
        let checked = (|| {
            self.scope_depth = if scope_root { saved_scope_depth + 1 } else { 0 };
            self.parameter_lifetimes = child_parameter_lifetimes.clone();
            for (ty, (grade, linear)) in capture_types.iter().zip(&capture_obligations) {
                self.locals.push(Local {
                    ty: *ty,
                    mutable: false,
                    linear: *linear,
                    grade: *grade,
                    span,
                });
            }
            // Rebuild the binder map for captures from the outer checker.
            let mut capture_binders = BTreeMap::new();
            for (id, outer_slot) in &saved_slots {
                if let Some(position) = captures.iter().position(|slot| slot == outer_slot) {
                    capture_binders.insert(*id, position);
                }
            }
            self.slots = capture_binders;
            // Captured immutable scalars are frozen in the closure environment
            // at construction, so they are sound symbolic indices for proof
            // terms in the body. Mutable captures stay rejected conservatively.
            for ((id, ty), mutable) in capture_ids
                .iter()
                .zip(capture_types.iter())
                .zip(capture_mutable.iter())
            {
                if let Some(id) = id
                    && !*mutable
                {
                    self.admit_scalar_index(*id, *ty, Span::default())?;
                }
            }
            for (parameter, ty) in lambda.parameters.iter().zip(&parameters) {
                let slot = self.bind(parameter.span, *ty, false)?;
                self.locals[slot].grade = parameter_grades[slot - captures.len()];
                self.locals[slot].linear = parameter_grades[slot - captures.len()]
                    .is_some_and(Grade::is_one)
                    && self.owned_type(*ty);
                let id = self.resolution.binder(parameter.span).unwrap();
                self.admit_scalar_index(id, *ty, parameter.span)?;
            }
            self.result = result;
            self.result_grade = result_grade;
            self.effects = effects;
            self.loops.clear();
            self.facts = crate::facts::Facts::default();
            let body = self.block(&lambda.body, Some(result))?;
            self.expect(body.ty, result, span)?;
            if body.ty != Type::Never
                && let Some(tail) = &body.tail
                && self.observes_copyable_result(tail)
                && !self.transfers_copyable_result_from(tail)
            {
                return Err(Diagnostic::new(
                    tail.span,
                    "this lambda returns a copyable result with the must-use `@[1]` contract through an ungraded result; annotate the result as '@[1]' so every caller inherits exactly one observation, or observe the value inside the lambda",
                ));
            }
            // The lambda's own locals are in scope here, so the result-transfer
            // obligation is derived before restoring the outer checker state.
            let obligation = self.return_obligation(&body);
            Ok((body, obligation))
        })();
        self.kernel_locals.truncate(kernel_mark);
        self.scope_depth = saved_scope_depth;
        self.handlers = saved_handlers;
        let locals = std::mem::take(&mut self.locals);
        self.locals = saved_locals;
        self.slots = saved_slots;
        self.result = saved_result;
        self.parameter_lifetimes = saved_parameter_lifetimes;
        self.result_grade = saved_result_grade;
        self.effects = saved_effects;
        self.loops = saved_loops;
        self.facts = saved_facts;
        let (body, obligation) = checked?;
        if let Some(span) = obligation
            && result_grade.is_none()
            && !self.linear_type(result)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "this lambda returns a linear obligation through an ungraded result; annotate the result as '-> {} @[1]' so every caller must consume it, or consume the value inside the lambda",
                    self.types.name(result)
                ),
            ));
        }
        let mut grades = vec![None; captures.len()];
        grades.extend(parameter_grades.iter().copied());
        let name = if once { "once lambda" } else { "lambda" };
        let signature = Signature {
            binding: usize::MAX,
            name: name.to_owned(),
            parameters,
            result,
            effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades: parameter_grades.clone(),
            result_grade,
            parameter_lifetimes: lambda_lifetimes.clone(),
            result_lifetime: lambda_result_lifetime.clone(),
            lifetime_bounds: BTreeSet::new(),
            self_type: None,
            default_trait: None,
            associated_consts: BTreeMap::new(),
        };
        let function = Function {
            name: name.to_owned(),
            parameters: captures.len() + lambda.parameters.len(),
            closure: once.then_some(captures.len()),
            locals,
            result,
            body,
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: grades,
            result_grade,
            parameter_lifetimes: {
                let mut lifetimes = capture_lifetimes.clone();
                lifetimes.extend(lambda_lifetimes);
                lifetimes
            },
            result_lifetime: lambda_result_lifetime,
            lifetime_bounds: BTreeSet::new(),
        };
        let index = self.functions.add_synthetic(signature, function)?;
        let ty = if once {
            Type::Once(function_type)
        } else {
            Type::Fn(function_type)
        };
        let value = Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: capture_exprs,
            },
            ty,
            span,
            resource: None,
        };
        if borrowed_capture
            && expected.is_some_and(|expected| expected != ty)
            && !expected.is_some_and(|expected| matches!(expected, Type::Once(_)))
        {
            return Err(Diagnostic::new(
                span,
                "a lambda with borrowed slice captures cannot be coerced to a union or non-once function type; call it directly or bind it with its exact 'once fn(...)' type",
            ));
        }
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Outer local slots referenced by a lambda body. Resolution already maps
    /// every occurrence to its exact binder, so filtering by the current slot
    /// map removes lambda parameters, lambda locals, and type/grade binders.
    fn lambda_captures(&self, lambda: &ast::Lambda) -> Vec<usize> {
        let mut ids = BTreeSet::new();
        collect_lambda_refs(self.resolution, &lambda.body, &mut ids);
        ids.iter()
            .filter_map(|id| self.slots.get(id).copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
    /// Whether values of `ty` carry a declared `#[linear]` obligation.
    fn linear_type(&self, ty: Type) -> bool {
        // Reachability over the finite type graph, not recursive unfolding:
        // binary recursive data would otherwise cause exponential work.
        let mut pending = vec![ty];
        let mut seen = std::collections::BTreeSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            match ty {
                Type::Box(p) | Type::Vec(p) => pending.push(self.types.pointees[p]),
                Type::Enum(id) | Type::Variants(id, _) => {
                    if self.types.enums[id].linear {
                        return true;
                    }
                    pending.extend(
                        self.types.enums[id]
                            .variants
                            .iter()
                            .flat_map(|v| v.fields.iter())
                            .copied(),
                    );
                }
                Type::Union(id) => pending.extend(self.types.unions[id].members.iter().copied()),
                Type::Once(id) if self.types.function_types[id].linear => return true,
                _ => {}
            }
        }
        false
    }
    /// A named or explicitly specialized function used as a value.
    fn function_value(
        &mut self,
        id: BindingId,
        explicit: Option<&[ast::Type]>,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let f = self.functions.declared[&id].ast;
        if f.parameters.iter().any(|parameter| parameter.erased) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' has erased proof parameters and cannot be a first-class value; call it directly so the obligation is discharged at the call site",
                    f.name
                ),
            ));
        }
        if explicit.is_some() && f.generics.is_empty() {
            return Err(Diagnostic::new(
                span,
                format!("'{}' is not generic; remove the type arguments", f.name),
            ));
        }
        let what = format!("'{}'", f.name);
        let (type_arguments, grade_arguments, const_arguments, effect_arguments) = match explicit {
            Some(list) => {
                let (types, grades, consts, effects, _) = self.infer(
                    &f.generics,
                    Some(list),
                    &[],
                    None,
                    false,
                    None,
                    None,
                    &what,
                    span,
                )?;
                (types, grades, consts, effects)
            }
            None if f.generics.is_empty() => (vec![], vec![], vec![], vec![]),
            None => self.infer_function_value(f, expected, &what, span)?,
        };
        let index = self.functions.instance(
            self.types,
            self.resolution,
            id,
            type_arguments,
            grade_arguments,
            const_arguments,
            effect_arguments,
            None,
            Some(span),
        )?;
        let signature = self.functions.signatures[index].clone();
        // Slice parameters/results and borrowed record fields carry their
        // lifetime contract in the callable type. Owner references and text
        // views remain direct-call only.
        if signature
            .parameters
            .iter()
            .chain([&signature.result])
            .any(|ty| {
                !ty.is_slice()
                    && !ty.is_ref()
                    && !crate::runtime_types::is_borrowed_record(self.types, *ty)
                    && !crate::runtime_types::is_reference_container(self.types, *ty)
                    && !crate::runtime_types::is_borrowed_task_exit(self.types, *ty)
                    && crate::runtime_types::has_borrow(self.types, *ty)
            })
        {
            return Err(Diagnostic::new(
                span,
                "a function value cannot carry an owner reference or &str text view in a parameter or result type; use references, slice views, or records with borrowed fields",
            ));
        }
        let parameter_lifetimes = signature
            .parameters
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                (ty.is_slice() || ty.is_ref()).then(|| {
                    signature
                        .parameter_lifetimes
                        .get(i)
                        .cloned()
                        .flatten()
                        .unwrap_or_else(|| format!("<unnamed {i}>"))
                })
            })
            .collect::<Vec<_>>();
        let parameter_leaves = signature
            .parameters
            .iter()
            .map(|ty| {
                if crate::runtime_types::is_borrowed_record(self.types, *ty)
                    || crate::runtime_types::is_reference_container(self.types, *ty)
                    || crate::runtime_types::is_borrowed_task_exit(self.types, *ty)
                {
                    crate::runtime_types::borrow_leaves(self.types, *ty)
                } else {
                    Vec::new()
                }
            })
            .collect::<Vec<_>>();
        let result_lifetime = signature
            .result
            .is_slice()
            .then(|| signature.result_lifetime.clone())
            .flatten();
        let result_lifetime = if signature.result.is_ref() {
            signature.result_lifetime.clone()
        } else {
            result_lifetime
        };
        let result_leaves =
            if crate::runtime_types::is_borrowed_record(self.types, signature.result)
                || crate::runtime_types::is_reference_container(self.types, signature.result)
                || crate::runtime_types::is_borrowed_task_exit(self.types, signature.result)
            {
                crate::runtime_types::borrow_leaves(self.types, signature.result)
            } else {
                Vec::new()
            };
        let function_type = self.types.function_type_with(
            signature.parameters.clone(),
            signature.result,
            signature.effects,
            signature.parameter_grades.clone(),
            signature.result_grade,
            false,
            false,
            crate::runtime_types::BorrowSig::canonical_with_leaves(
                &parameter_lifetimes,
                result_lifetime.as_ref(),
                &parameter_leaves,
                &result_leaves,
                &signature.lifetime_bounds,
            ),
        );
        let value = Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![],
            },
            ty: Type::Fn(function_type),
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Infer type/const arguments of a generic function used as a value from an
    /// expected arrow type. A usage grade may also be inferred when it is the
    /// entire outer result grade and the expected arrow carries the concrete
    /// `@[1]` transfer contract; every other grade use stays explicit.
    fn infer_function_value(
        &mut self,
        f: &ast::Function,
        expected: Option<Type>,
        what: &str,
        span: Span,
    ) -> Result<GenericArguments> {
        let Some((id, _)) = expected.and_then(Checker::function_parts) else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a generic function value needs an expected 'fn(...)' type or explicit '::<...>' specialization for {what}"
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        let runtime = f
            .parameters
            .iter()
            .filter(|p| !p.erased)
            .collect::<Vec<_>>();
        if runtime.len() != signature.parameters.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "function value for {what} expects {} runtime arguments, but the target arrow type has {}",
                    runtime.len(),
                    signature.parameters.len()
                ),
            ));
        }
        let mut type_vars = Vec::new();
        let mut grade_vars = Vec::new();
        let mut const_vars = Vec::new();
        let mut effect_vars = Vec::new();
        for generic in &f.generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            if is_grade_generic(self.resolution, generic) {
                grade_vars.push(binder);
            } else if is_const_generic(self.resolution, generic) {
                const_vars.push(binder);
            } else if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                effect_vars.push(binder);
            } else {
                type_vars.push(binder);
            }
        }
        let mut subst = crate::runtime_types::Subst::default();
        let constraint_mark = self.effect_constraints.len();
        for (parameter, actual) in runtime.iter().zip(&signature.parameters) {
            self.unify(
                split_grade(&parameter.ty).0,
                *actual,
                &type_vars,
                &const_vars,
                &effect_vars,
                &mut subst,
                span,
            )?;
        }
        let expanded_result = expand_result_aliases(self.resolution, self.types, &f.result)?;
        let (declared_result, result_grade) = split_grade(&expanded_result);
        self.unify(
            declared_result,
            signature.result,
            &type_vars,
            &const_vars,
            &effect_vars,
            &mut subst,
            span,
        )?;
        // The expected arrow's effect row is also evidence: the source may
        // perform only effects permitted by the target. This is accumulated
        // with constraints from callable parameters, then solved as one group.
        let (fixed, variables) =
            crate::runtime_types::effect_bits_partial(self.resolution, &f.effects)?;
        let effect_generics = f
            .generics
            .iter()
            .filter(|generic| crate::runtime_types::is_effect_generic(self.resolution, generic))
            .collect::<Vec<_>>();
        if !variables.is_empty() {
            self.effect_constraints.push(EffectConstraint {
                fixed,
                variables,
                actual: signature.effects,
                span,
            });
        }
        self.solve_effect_constraints(constraint_mark, &effect_generics, &mut subst, span)?;
        // General grade inference for a generic function value. The expected
        // arrow supplies concrete grades for its parameters and result. All
        // equations are solved simultaneously in the decidable natural or
        // finite-algebra fragment. A binder that reaches an underlying runtime
        // type, that has no expected-grade evidence, or whose equation has no
        // unique solution remains an explicit-specialization error. Unknown
        // grades are never guessed as one.
        let mut grades = Vec::new();
        if !grade_vars.is_empty() {
            let mut constraints = runtime
                .iter()
                .zip(&signature.parameter_grades)
                .filter_map(|(parameter, expected)| {
                    let declared = split_grade(&parameter.ty).1?;
                    let expected = (*expected)?;
                    Some((declared, expected))
                })
                .collect::<Vec<_>>();
            if let Some(declared) = result_grade
                && let Some(expected) = signature.result_grade
            {
                constraints.push((declared, expected));
            }
            let solved =
                grades::solve_all(self.resolution, &self.grades, &grade_vars, &constraints)?
                    .unwrap_or_default();
            for binder in &grade_vars {
                let name = &self.resolution.bindings[*binder].name;
                let in_underlying_type = runtime.iter().any(|parameter| {
                    type_mentions_binding(self.resolution, split_grade(&parameter.ty).0, *binder)
                }) || type_mentions_binding(
                    self.resolution,
                    declared_result,
                    *binder,
                );
                let reason = if in_underlying_type {
                    "it occurs in an underlying parameter or result type, where a usage grade cannot be inferred".to_owned()
                } else if let Some(value) = solved.get(binder) {
                    subst.grades.insert(*binder, *value);
                    grades.push(*value);
                    continue;
                } else if result_grade.is_none()
                    && !runtime
                        .iter()
                        .any(|parameter| split_grade(&parameter.ty).1.is_some())
                {
                    "the declaration has no grade expression for the expected arrow to determine"
                        .to_owned()
                } else {
                    "no expected parameter/result grade uniquely determines it, or its grade equation is outside the decidable natural/finite-algebra fragment".to_owned()
                };
                return Err(Diagnostic::new(
                    self.resolution.bindings[*binder].span,
                    format!(
                        "cannot infer usage grade parameter '{name}' of {what}: {reason}. Specialize it explicitly with '::<...>'"
                    ),
                ));
            }
        }
        let mut types = Vec::new();
        for generic in f.generics.iter() {
            let binder = self.resolution.binder(generic.span).unwrap();
            if is_grade_generic(self.resolution, generic) {
                continue;
            }
            if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                continue;
            }
            if is_const_generic(self.resolution, generic) {
                let Some(value) = subst.consts.get(&binder) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer natural parameter '{}' of {what}; specialize explicitly with '::<...>'",
                            generic.name
                        ),
                    ));
                };
                let _ = value;
            } else {
                let Some(ty) = subst.types.get(&binder) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer type parameter '{}' of {what}; specialize explicitly with '::<...>'",
                            generic.name
                        ),
                    ));
                };
                types.push(*ty);
            }
        }
        let consts = f
            .generics
            .iter()
            .filter(|generic| is_const_generic(self.resolution, generic))
            .map(|generic| {
                subst
                    .consts
                    .get(&self.resolution.binder(generic.span).unwrap())
                    .copied()
                    .ok_or_else(|| {
                        Diagnostic::new(
                            span,
                            format!(
                                "cannot infer natural parameter '{}' of {what}; specialize explicitly with '::<...>'",
                                generic.name
                            ),
                        )
                    })
            })
            .collect::<Result<Vec<_>>>()?;
        let effects = f
            .generics
            .iter()
            .filter(|generic| crate::runtime_types::is_effect_generic(self.resolution, generic))
            .map(|generic| {
                subst
                    .effects
                    .get(&self.resolution.binder(generic.span).unwrap())
                    .copied()
                    .ok_or_else(|| {
                        Diagnostic::new(
                            span,
                            format!(
                                "cannot infer effect row parameter '{}' of {what}; specialize explicitly with '::<...>'",
                                generic.name
                            ),
                        )
                    })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok((types, grades, consts, effects))
    }
    /// Indirect call through a function-typed value.
    fn indirect_call(
        &mut self,
        callee: &ast::Expr,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let callee = self.expr(callee)?;
        self.indirect_call_checked(callee, arguments, expected, span)
    }
    /// Indirect call with an already checked callee value. Shared by the
    /// ordinary field-projection call path and method dispatch, so receiver
    /// evaluation happens exactly once.
    fn indirect_call_checked(
        &mut self,
        callee: Expr,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let Some((id, _)) = Self::function_parts(callee.ty) else {
            return Err(Diagnostic::new(
                callee.span,
                format!(
                    "this value is not an executable function; expected fn(...) or once fn(...), found {}",
                    self.types.name(callee.ty)
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        if signature.parameters.len() != arguments.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count: expected {}, found {}",
                    signature.parameters.len(),
                    arguments.len()
                ),
            ));
        }
        self.require(signature.effects, span)?;
        let mut diverges = false;
        let mut values = Vec::with_capacity(arguments.len());
        for (argument, parameter) in arguments.iter().zip(&signature.parameters) {
            // An arrow's record lifetimes are instantiated afresh at each
            // call, exactly like a direct call. The argument constructs a
            // record with its own inferred labels; the call boundary relates
            // those labels to the arrow's declared ones.
            let wanted = self.types.freshen_borrows(*parameter, argument.span)?;
            let value = self.expr_expected(argument, Some(wanted))?;
            diverges |= value.ty == Type::Never;
            values.push(self.coerce(value, *parameter, argument.span)?);
        }
        let ty = if diverges {
            Type::Never
        } else if signature.result_erased() {
            Type::Unit
        } else {
            signature.result
        };
        let value = Expr {
            kind: ExprKind::CallIndirect {
                callee: Box::new(callee),
                arguments: values,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Reject grades that would duplicate or discard owning/linear storage.
    fn validate_grade(
        &self,
        grade: Option<Grade>,
        ty: Type,
        span: Span,
        allow_affine_drop: bool,
    ) -> Result<()> {
        if !self.owned_type(ty) {
            return Ok(());
        }
        match grade {
            None => Ok(()),
            Some(grade) if grade.is_one() => Ok(()),
            Some(grade) if grade.is_zero() => {
                if self.linear_type(ty) {
                    Err(Diagnostic::new(
                        span,
                        format!(
                            "grade @[0] would silently discard the linear obligation of {}; consume it with grade @[1] or leave it ungraded",
                            self.types.name(ty)
                        ),
                    ))
                } else if allow_affine_drop {
                    // Affine owned storage may be initialized and dropped
                    // eagerly: the binding itself is not materialized, but the
                    // value is destroyed exactly once at the binding site.
                    Ok(())
                } else {
                    Err(Diagnostic::new(
                        span,
                        format!(
                            "grade @[0] would silently discard the owning/linear value {}; consume it with grade @[1] or leave it ungraded",
                            self.types.name(ty)
                        ),
                    ))
                }
            }
            Some(grade) if grade.is_many() => Err(Diagnostic::new(
                span,
                format!(
                    "grade 'many' allows duplication, but {} owns resources or is linear",
                    self.types.name(ty)
                ),
            )),
            Some(grade) => Err(Diagnostic::new(
                span,
                format!(
                    "grade @[{grade}] would duplicate the owning/linear value {}; owning and linear values support only @[1]",
                    self.types.name(ty)
                ),
            )),
        }
    }
    /// Checked unique-box reuse. The allocation comes from `owner`; the old
    /// affine payload is destroyed exactly once after both arguments have been
    /// evaluated, and the new payload is stored in the same storage. There is
    /// no allocating fallback and no implicit destruction of linear payloads.
    fn box_reuse(
        &mut self,
        owner: &ast::Expr,
        payload: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let owner = self.expr(owner)?;
        if owner.ty == Type::Never {
            let payload = self.expr(payload)?;
            return Ok(Expr {
                kind: ExprKind::BoxReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Box(old_index) = owner.ty else {
            return Err(Diagnostic::new(
                owner.span,
                "Box.reuse requires an owned Box<T> as its first argument",
            ));
        };
        let old = self.types.pointees[old_index];
        if self.linear_type(old) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.reuse cannot implicitly drop the linear payload {}; take it out and consume it explicitly",
                    self.types.name(old)
                ),
            ));
        }
        if self.value_moves_linear(&owner) && self.owned_type(old) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse cannot discard an owned payload that may carry a propagated linear obligation; take and consume it explicitly",
            ));
        }
        let expected_inner = expected.and_then(|ty| {
            if let Type::Box(index) = ty {
                Some(self.types.pointees[index])
            } else {
                None
            }
        });
        let payload = self.expr_expected(payload, expected_inner)?;
        if payload.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::BoxReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse cannot store a borrowed reference or slice view (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let new = match expected_inner {
            Some(expected) => expected,
            None => self.types.full(payload.ty, span)?,
        };
        let payload = self.coerce(payload, new, span)?;
        let old_width = self.types.width(old);
        let new_width = self.types.width(new);
        if new_width > old_width {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.reuse cannot store {} ({new_width} word(s)) in an allocation sized for {} ({old_width} word(s)); there is no allocating fallback. Allocate a new Box or reduce the payload layout",
                    self.types.name(new),
                    self.types.name(old)
                ),
            ));
        }
        let ty = Type::Box(self.types.pointer(new));
        let value = Expr {
            kind: ExprKind::BoxReuse {
                owner: Box::new(owner),
                payload: Box::new(payload),
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Checked widening reuse. This is the explicit allocating fallback: a
    /// payload wider than the old one may grow and move the allocation. It
    /// requires `{alloc, panic}` and is therefore illegal under `#[noalloc]`.
    /// The old payload is still destroyed exactly once before any new storage
    /// is written, and the returned owner keeps every obligation of the old
    /// owner and of the new payload.
    fn box_reuse_grow(
        &mut self,
        owner: &ast::Expr,
        payload: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let owner = self.expr(owner)?;
        if owner.ty == Type::Never {
            let payload = self.expr(payload)?;
            return Ok(Expr {
                kind: ExprKind::BoxReuseGrow {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Box(old_index) = owner.ty else {
            return Err(Diagnostic::new(
                owner.span,
                "Box.reuse_grow requires an owned Box<T> as its first argument",
            ));
        };
        let old = self.types.pointees[old_index];
        if self.linear_type(old) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.reuse_grow cannot implicitly drop the linear payload {}; take it out and consume it explicitly",
                    self.types.name(old)
                ),
            ));
        }
        if self.value_moves_linear(&owner) && self.owned_type(old) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse_grow cannot discard an owned payload that may carry a propagated linear obligation; take and consume it explicitly",
            ));
        }
        self.require(ALLOC | PANIC, span)?;
        let expected_inner = expected.and_then(|ty| {
            if let Type::Box(index) = ty {
                Some(self.types.pointees[index])
            } else {
                None
            }
        });
        let payload = self.expr_expected(payload, expected_inner)?;
        if payload.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::BoxReuseGrow {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.reuse_grow cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let new = match expected_inner {
            Some(expected) => expected,
            None => self.types.full(payload.ty, span)?,
        };
        let payload = self.coerce(payload, new, span)?;
        let ty = Type::Box(self.types.pointer(new));
        let value = Expr {
            kind: ExprKind::BoxReuseGrow {
                owner: Box::new(owner),
                payload: Box::new(payload),
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Fallible box construction. The payload is moved into the `Ok` box on
    /// success and returned unchanged in `Err` on failure, so no owner is
    /// destroyed or silently duplicated by a rejected allocation.
    fn box_try_new(
        &mut self,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC, span)?;
        let expected_shape = expected.and_then(|ty| self.types.result(ty, span).ok());
        let expected_inner = expected_shape.and_then(|shape| match shape.ok {
            Type::Box(index) => Some(self.types.pointees[index]),
            _ => None,
        });
        let value = self.expr_expected(value, expected_inner)?;
        if value.ty == Type::Never {
            let shape = expected_shape.unwrap_or(ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            });
            return Ok(Expr {
                kind: ExprKind::BoxTryNew {
                    value: Box::new(value),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.try_new cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let pointee = self.types.full(value.ty, span)?;
        let value = self.coerce(value, pointee, span)?;
        let ok = Type::Box(self.types.pointer(pointee));
        let (ty, shape) = self.types.result_type(ok, pointee, span)?;
        let expression = Expr {
            kind: ExprKind::BoxTryNew {
                value: Box::new(value),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Fallible growth-capable reuse. On allocation failure the old owner is
    /// returned untouched in `Err`. The new payload must be non-owning, so the
    /// failure path preserves every supplied owner exactly.
    fn box_try_reuse(
        &mut self,
        owner: &ast::Expr,
        payload: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let owner = self.expr(owner)?;
        if owner.ty == Type::Never {
            let payload = self.expr(payload)?;
            let shape = ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            };
            return Ok(Expr {
                kind: ExprKind::BoxTryReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Box(old_index) = owner.ty else {
            return Err(Diagnostic::new(
                owner.span,
                "Box.try_reuse requires an owned Box<T> as its first argument",
            ));
        };
        let old = self.types.pointees[old_index];
        if self.linear_type(old) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.try_reuse cannot implicitly drop the linear payload {}; take it out and consume it explicitly",
                    self.types.name(old)
                ),
            ));
        }
        if self.value_moves_linear(&owner) && self.owned_type(old) {
            return Err(Diagnostic::new(
                span,
                "Box.try_reuse cannot discard an owned payload that may carry a propagated linear obligation; take and consume it explicitly",
            ));
        }
        self.require(ALLOC, span)?;
        let expected_shape = expected.and_then(|ty| self.types.result(ty, span).ok());
        let expected_inner = expected_shape.and_then(|shape| match shape.ok {
            Type::Box(index) => Some(self.types.pointees[index]),
            _ => None,
        });
        let payload = self.expr_expected(payload, expected_inner)?;
        if payload.ty == Type::Never {
            let shape = expected_shape.unwrap_or(ResultShape {
                ok_tag: 0,
                err_tag: 1,
                ok: Type::Unit,
                error: Type::Unit,
            });
            return Ok(Expr {
                kind: ExprKind::BoxTryReuse {
                    owner: Box::new(owner),
                    payload: Box::new(payload),
                    shape,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "Box.try_reuse cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, payload.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Box; join them in the scope that owns them",
            ));
        }
        let new = match expected_inner {
            Some(expected) => expected,
            None => self.types.full(payload.ty, span)?,
        };
        if self.owned_type(new) || self.linear_type(new) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Box.try_reuse requires a non-owning new payload so a failed allocation can preserve every supplied owner; {} owns resources. Use Box.reuse_grow for an aborting swap, or consume the owner first",
                    self.types.name(new)
                ),
            ));
        }
        let payload = self.coerce(payload, new, span)?;
        let ok = Type::Box(self.types.pointer(new));
        let error = Type::Box(self.types.pointer(old));
        let (ty, shape) = self.types.result_type(ok, error, span)?;
        let expression = Expr {
            kind: ExprKind::BoxTryReuse {
                owner: Box::new(owner),
                payload: Box::new(payload),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Fallible byte-buffer construction with an exact requested capacity.
    fn bytes_try_with_capacity(
        &mut self,
        capacity: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC, span)?;
        let capacity = self.expr_expected(capacity, Some(Type::I64))?;
        self.expect(capacity.ty, Type::I64, capacity.span)?;
        let (ty, shape) = self.types.result_type(Type::Bytes, Type::I64, span)?;
        let expression = Expr {
            kind: ExprKind::BytesTryWithCapacity {
                capacity: Box::new(capacity),
                shape,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Create one owning bump-allocator region.
    fn arena_new(&mut self, span: Span) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        Ok(Expr {
            kind: ExprKind::ArenaNew,
            ty: Type::Arena,
            span,
            resource: None,
        })
    }
    /// Check `Arena.alloc(&arena, value)`. The borrow keeps the arena value
    /// live for the duration of the call; the returned `ArenaBox` carries its
    /// own region reference, so dropping the arena binding does not invalidate
    /// it.
    fn arena_alloc(
        &mut self,
        arena: &ast::Expr,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.require(ALLOC | PANIC, span)?;
        let expected_inner = expected.and_then(|ty| {
            if let Type::ArenaBox(index) = ty {
                Some(self.types.pointees[index])
            } else {
                None
            }
        });
        let pointer = self.types.pointer(Type::Arena);
        let arena = self.expr_expected(arena, Some(Type::Ref(pointer)))?;
        self.expect(arena.ty, Type::Ref(pointer), arena.span)?;
        let value = self.expr_expected(value, expected_inner)?;
        if value.ty == Type::Never {
            return Ok(Expr {
                kind: ExprKind::ArenaAlloc {
                    arena: Box::new(arena),
                    value: Box::new(value),
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        if crate::runtime_types::has_borrow(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "Arena.alloc cannot store a borrowed reference, slice view, or borrowed record (including &str text views)",
            ));
        }
        if crate::runtime_types::contains_task(self.types, value.ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Arena; join them in the scope that owns them",
            ));
        }
        let pointee = self.types.full(value.ty, span)?;
        if self.linear_type(pointee) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Arena.alloc cannot place the linear value {} in a region that destroys its contents implicitly; consume it inside the region scope instead",
                    self.types.name(pointee)
                ),
            ));
        }
        if self.value_moves_linear(&value) && self.owned_type(pointee) {
            return Err(Diagnostic::new(
                span,
                "Arena.alloc cannot store an owned payload that may carry a propagated linear obligation; consume it explicitly",
            ));
        }
        let value = self.coerce(value, pointee, span)?;
        let ty = Type::ArenaBox(self.types.pointer(pointee));
        let expression = Expr {
            kind: ExprKind::ArenaAlloc {
                arena: Box::new(arena),
                value: Box::new(value),
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(expression, expected, span),
            None => Ok(expression),
        }
    }
    /// Read a copyable payload through `&ArenaBox<T>`. Ownership rejects
    /// copying an owning payload, exactly as for `Box.read`.
    fn arena_box_read(&mut self, value: &ast::Expr, span: Span) -> Result<Expr> {
        let value = self.expr_expected(value, None)?;
        let Type::Ref(index) = value.ty else {
            return Err(Diagnostic::new(
                span,
                "ArenaBox.read requires an immutable &ArenaBox<T>",
            ));
        };
        let Type::ArenaBox(inner) = self.types.pointees[index] else {
            return Err(Diagnostic::new(
                span,
                "ArenaBox.read requires an immutable &ArenaBox<T>, not another borrow type",
            ));
        };
        let ty = self.types.pointees[inner];
        Ok(Expr {
            kind: ExprKind::ArenaBoxRead(Box::new(value)),
            ty,
            span,
            resource: None,
        })
    }
    /// Move the payload out of an owning `ArenaBox<T>`.
    fn arena_box_take(&mut self, value: &ast::Expr, span: Span) -> Result<Expr> {
        let value = self.expr(value)?;
        let Type::ArenaBox(index) = value.ty else {
            return Err(Diagnostic::new(
                span,
                "ArenaBox.take requires an owned ArenaBox<T>",
            ));
        };
        let ty = self.types.pointees[index];
        Ok(Expr {
            kind: ExprKind::ArenaBoxTake(Box::new(value)),
            ty,
            span,
            resource: None,
        })
    }
    /// Strip the checker-only lifetime annotation from a container element.
    /// The annotation has no runtime representation and never reaches a
    /// user-visible expression type.
    fn unannotate(&self, ty: Type) -> Type {
        match ty {
            Type::Annotated(p, _) => self.types.pointees[p],
            ty => ty,
        }
    }
    /// Whether values of `ty` own heap storage (computed from layouts).
    fn carrier_type(&self, ty: Type) -> bool {
        ty.layout().is_some_and(|id| self.types.enums[id].borrowed)
    }
    fn owned_type(&self, ty: Type) -> bool {
        fn go(types: &Types<'_>, ty: Type, depth: usize) -> bool {
            match ty {
                Type::Box(_)
                | Type::Arena
                | Type::ArenaBox(_)
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::Once(_)
                | Type::Task(_) => true,
                Type::Enum(id) | Type::Variants(id, _) if depth < 64 => {
                    types.enums[id].linear
                        || types.enums[id]
                            .variants
                            .iter()
                            .any(|v| v.fields.iter().any(|f| go(types, *f, depth + 1)))
                }
                Type::Union(id) if depth < 64 => types.unions[id]
                    .members
                    .iter()
                    .any(|member| go(types, *member, depth + 1)),
                _ => false,
            }
        }
        go(self.types, ty, 0)
    }
    /// A non-moving read of a local or a nested record field of one.
    fn place(&mut self, expr: &ast::Expr) -> Result<Expr> {
        match &expr.kind {
            ast::ExprKind::Name(name) if name != "_" => {
                if let Ok(slot) = self.slot(expr.span) {
                    return Ok(Expr {
                        kind: ExprKind::Peek(slot),
                        ty: self.locals[slot].ty,
                        span: expr.span,
                        resource: None,
                    });
                }
            }
            ast::ExprKind::Field { value, name }
                if self.resolution.reference(expr.span).is_none() =>
            {
                let base = self.place(value)?;
                if base.ty.is_ref() {
                    let pointer = base.ty.ref_pointee().expect("reference pointee");
                    let pointee = self.types.pointees[pointer];
                    let (offset, ty) = self.record_offset(pointee, name, expr.span)?;
                    if self.owned_type(ty)
                        || self.linear_type(ty)
                        || ty.is_view()
                        || ty.is_ref()
                        || ty.layout().is_some_and(|id| self.types.enums[id].borrowed)
                        || ty
                            .layout()
                            .is_some_and(|id| self.types.enums[id].mutable_borrow)
                    {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "field '{name}' cannot be read through a record reference because it owns storage or contains a borrow; destructure an owning value instead"
                            ),
                        ));
                    }
                    return Ok(Expr {
                        kind: ExprKind::Project(Box::new(base), offset),
                        ty,
                        span: expr.span,
                        resource: None,
                    });
                }
                let (offset, ty) = self.field_offset(&base, name, expr.span)?;
                return Ok(Expr {
                    kind: ExprKind::Project(Box::new(base), offset),
                    ty,
                    span: expr.span,
                    resource: None,
                });
            }
            _ => {}
        }
        let value = self.expr(expr)?;
        if self.owned_type(value.ty) {
            return Err(Diagnostic::new(
                expr.span,
                "bind this owned value to a local before reading its fields",
            ));
        }
        Ok(value)
    }
    fn field_offset(&self, base: &Expr, name: &str, span: Span) -> Result<(usize, Type)> {
        if base.ty.layout().is_none() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "field access requires a record value, found {}",
                    self.types.name(base.ty)
                ),
            ));
        }
        self.record_offset(base.ty, name, span)
    }
    fn record_offset(&self, ty: Type, name: &str, span: Span) -> Result<(usize, Type)> {
        let Some(id) = ty.layout().filter(|id| self.types.enums[*id].record) else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "field access requires a record value, found {}",
                    self.types.name(ty)
                ),
            ));
        };
        let variant = &self.types.enums[id].variants[0];
        let Some(index) = variant.names.iter().position(|n| n == name) else {
            return if self.types.enums[id].tuple {
                Err(Diagnostic::new(
                    span,
                    format!(
                        "tuple {} has no element '{name}' (elements: {})",
                        self.types.name(ty),
                        variant.names.join(", ")
                    ),
                ))
            } else {
                Err(Diagnostic::new(
                    span,
                    format!(
                        "record {} has no field '{name}' (fields: {})",
                        self.types.name(ty),
                        variant.names.join(", ")
                    ),
                ))
            };
        };
        let offset = 1 + variant.fields[..index]
            .iter()
            .map(|t| self.types.width(*t))
            .sum::<usize>();
        Ok((offset, variant.fields[index]))
    }
    fn field(
        &mut self,
        value: &ast::Expr,
        name: &str,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let base = self.place(value)?;
        if base.ty.is_ref() {
            let pointer = base.ty.ref_pointee().expect("reference pointee");
            let pointee = self.types.pointees[pointer];
            let (offset, ty) = self.record_offset(pointee, name, span)?;
            if self.owned_type(ty)
                || self.linear_type(ty)
                || ty.is_view()
                || ty.is_ref()
                || ty.layout().is_some_and(|id| self.types.enums[id].borrowed)
                || ty
                    .layout()
                    .is_some_and(|id| self.types.enums[id].mutable_borrow)
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "field '{name}' cannot be read through a record reference because it owns storage or contains a borrow; destructure an owning value instead"
                    ),
                ));
            }
            let projected = Expr {
                kind: ExprKind::Project(Box::new(base), offset),
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(projected, expected, span),
                None => Ok(projected),
            };
        }
        self.project_field(base, name, span, expected)
    }
    /// Checked field projection from an already checked place. Shared by
    /// ordinary field access and callable-field method syntax so both reject
    /// owned, exclusive, and nested-exclusive projections identically.
    fn project_field(
        &mut self,
        base: Expr,
        name: &str,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let (offset, ty) = self.field_offset(&base, name, span)?;
        if ty.is_mut_slice() && !self.field_place {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project exclusive field '{name}' out of a record; destructure the record first, as in 'let R {{ {name}, .. }} = value;', or derive a subview with '&mut value.{name}[..]'"
                ),
            ));
        }
        if matches!(ty, Type::RefMut(_)) && !self.field_place {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project exclusive reference field '{name}' out of a record; destructure the record first, as in 'let R {{ {name}, .. }} = value;'"
                ),
            ));
        }
        if !self.field_place
            && ty
                .layout()
                .is_some_and(|id| self.types.enums[id].mutable_borrow)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project field '{name}' directly: it contains an exclusive '&mut [T]' field. Destructure the parent record first"
                ),
            ));
        }
        if self.owned_type(ty) {
            let record = self.types.name(base.ty);
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot move owned field '{name}' out of {record}; destructure the record instead: let {} {{ {name}: value }} = ...;",
                    record.split('<').next().unwrap_or(&record)
                ),
            ));
        }
        let value = Expr {
            kind: ExprKind::Project(Box::new(base), offset),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Whether `ty` mentions a type or const variable that is not yet inferred.
    fn mentions(
        &self,
        ty: &ast::Type,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &crate::runtime_types::Subst,
    ) -> bool {
        match &ty.kind {
            ast::TypeKind::Named { arguments, .. } => {
                self.resolution.reference(ty.span).is_some_and(|id| {
                    (type_vars.contains(&id) && !subst.types.contains_key(&id))
                        || (const_vars.contains(&id) && !subst.consts.contains_key(&id))
                        || (effect_vars.contains(&id) && !subst.effects.contains_key(&id))
                }) || arguments
                    .iter()
                    .any(|a| self.mentions(a, type_vars, const_vars, effect_vars, subst))
            }
            ast::TypeKind::Borrow { inner, .. }
            | ast::TypeKind::Slice(inner)
            | ast::TypeKind::Graded { inner, .. } => {
                self.mentions(inner, type_vars, const_vars, effect_vars, subst)
            }
            ast::TypeKind::Array(inner, length) => {
                self.mentions(inner, type_vars, const_vars, effect_vars, subst)
                    || self.const_mentions(length, const_vars, subst)
            }
            ast::TypeKind::Binary { left, right, .. } => {
                self.mentions(left, type_vars, const_vars, effect_vars, subst)
                    || self.mentions(right, type_vars, const_vars, effect_vars, subst)
            }
            ast::TypeKind::Tuple(items) => items
                .iter()
                .any(|a| self.mentions(a, type_vars, const_vars, effect_vars, subst)),
            ast::TypeKind::Function {
                parameters,
                result,
                effects,
                ..
            } => {
                parameters.iter().any(|parameter| {
                    self.mentions(&parameter.ty, type_vars, const_vars, effect_vars, subst)
                }) || self.mentions(result, type_vars, const_vars, effect_vars, subst)
                    || effects.iter().any(|effect| {
                        self.mentions(effect, type_vars, const_vars, effect_vars, subst)
                    })
            }
            _ => false,
        }
    }
    fn const_mentions(
        &self,
        ty: &ast::Type,
        const_vars: &[BindingId],
        subst: &crate::runtime_types::Subst,
    ) -> bool {
        match &ty.kind {
            ast::TypeKind::Named { arguments, .. } => {
                self.resolution
                    .reference(ty.span)
                    .is_some_and(|id| const_vars.contains(&id) && !subst.consts.contains_key(&id))
                    || arguments
                        .iter()
                        .any(|a| self.const_mentions(a, const_vars, subst))
            }
            ast::TypeKind::Binary { left, right, .. } => {
                self.const_mentions(left, const_vars, subst)
                    || self.const_mentions(right, const_vars, subst)
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| self.const_mentions(&parameter.ty, const_vars, subst))
                    || self.const_mentions(result, const_vars, subst)
            }
            _ => false,
        }
    }
    /// Solve a declared union pattern with exactly one bare type variable and
    /// a concrete fixed part, such as `T | i64`. The residual actual
    /// alternatives that are not covered by the fixed part determine `T`.
    ///
    /// This is deliberately a decidable residual-union rule, not row
    /// subtraction: the fixed alternatives must not mention any inference
    /// variable, and a second variable alternative is left to the ordinary
    /// error path instead of being partitioned arbitrarily. If every actual
    /// alternative is already covered by the fixed part, `T` has no unique
    /// residual binding (it could be `Never`, the fixed type itself, or a
    /// wider union), so the call is rejected rather than defaulting.
    #[allow(clippy::too_many_arguments)]
    fn unify_union_pattern(
        &mut self,
        pattern: &ast::Type,
        actual: Type,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<bool> {
        fn flatten<'a>(pattern: &'a ast::Type, out: &mut Vec<&'a ast::Type>) {
            match &pattern.kind {
                ast::TypeKind::Binary {
                    op: crate::lexer::Kind::Pipe,
                    left,
                    right,
                } => {
                    flatten(left, out);
                    flatten(right, out);
                }
                _ => out.push(pattern),
            }
        }
        let mut alternatives = Vec::new();
        flatten(pattern, &mut alternatives);
        let mut variable: Option<&ast::Type> = None;
        let mut fixed = Vec::new();
        for alternative in alternatives {
            let is_variable = matches!(
                &alternative.kind,
                ast::TypeKind::Named { path, arguments }
                    if arguments.is_empty()
                        && path.len() == 1
                        && self
                            .resolution
                            .reference(alternative.span)
                            .is_some_and(|id| type_vars.contains(&id))
            );
            if is_variable {
                if variable.is_some() {
                    return Ok(false);
                }
                variable = Some(alternative);
            } else if self.mentions(alternative, type_vars, const_vars, effect_vars, subst) {
                // A non-bare variable alternative needs real backtracking over
                // its shape. Leave that to the ordinary inference path.
                return Ok(false);
            } else {
                fixed.push(alternative);
            }
        }
        let Some(variable) = variable else {
            return Ok(false);
        };
        if fixed.is_empty() {
            return Ok(false);
        }
        let fixed_ty = {
            let mut types = Vec::with_capacity(fixed.len());
            for alternative in &fixed {
                types.push(self.types.ty_in(alternative, subst)?);
            }
            self.types.union(types, span)?
        };
        let mut residual = Vec::new();
        for member in self.types.union_members(actual) {
            if !self.subtype(member, fixed_ty) {
                residual.push(member);
            }
        }
        let variable_id = self
            .resolution
            .reference(variable.span)
            .expect("checked union-pattern variable reference");
        let residual = self.types.union(residual, span)?;
        if residual == Type::Never {
            if let Some(bound) = subst.types.get(&variable_id).copied() {
                let covered = self.types.union(vec![bound, fixed_ty], span)?;
                if !self.subtype(actual, covered) {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "union pattern '{}' does not cover the actual type {} for the inferred type parameter",
                            self.types.name(covered),
                            self.types.name(actual)
                        ),
                    ));
                }
                return Ok(true);
            }
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer type parameter '{}' from the union pattern: every actual alternative of {} is already covered by the fixed part, so the residual binding is not unique. Specialize it explicitly with '::<...>'",
                    self.resolution.bindings[variable_id].name,
                    self.types.name(actual)
                ),
            ));
        }
        self.unify(
            variable,
            residual,
            type_vars,
            const_vars,
            effect_vars,
            subst,
            span,
        )?;
        Ok(true)
    }
    /// First-order matching of a declared type against an actual type.
    #[allow(clippy::too_many_arguments)]
    fn unify(
        &mut self,
        pattern: &ast::Type,
        actual: Type,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        // First-order inference through a union actual. Instead of reading the
        // first union alternative that happens to bind a variable, every
        // alternative contributes a constraint. A variable must receive the
        // same binding from every alternative that constrains it; otherwise the
        // union does not determine one specialization and the call is
        // ambiguous. A bare type variable is not distributed: it captures the
        // whole normalized union, as before.
        let bare_variable = matches!(
            &pattern.kind,
            ast::TypeKind::Named { path, arguments }
                if arguments.is_empty()
                    && self.resolution.reference(pattern.span).is_some_and(|id| type_vars.contains(&id))
                    && path.len() == 1
        );
        if matches!(
            &pattern.kind,
            ast::TypeKind::Binary {
                op: crate::lexer::Kind::Pipe,
                ..
            }
        ) && self.unify_union_pattern(
            pattern,
            actual,
            type_vars,
            const_vars,
            effect_vars,
            subst,
            span,
        )? {
            return Ok(());
        }
        if let Type::Union(id) = actual
            && !bare_variable
        {
            let members = self.types.unions[id].members.clone();
            let mut merged = subst.clone();
            let mut constrained = false;
            for member in members {
                let mut candidate = subst.clone();
                self.unify(
                    pattern,
                    member,
                    type_vars,
                    const_vars,
                    effect_vars,
                    &mut candidate,
                    span,
                )?;
                for variable in type_vars {
                    if let Some(value) = candidate.types.get(variable).copied() {
                        match merged.types.get(variable).copied() {
                            Some(previous) if previous != value => {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "union alternatives disagree on type parameter '{}': one alternative requires {} and another requires {}. Specialize it explicitly with '::<...>'",
                                        self.resolution.bindings[*variable].name,
                                        self.types.name(previous),
                                        self.types.name(value)
                                    ),
                                ));
                            }
                            Some(_) => {}
                            None => {
                                merged.types.insert(*variable, value);
                                constrained = true;
                            }
                        }
                    }
                }
                for variable in const_vars {
                    if let Some(value) = candidate.consts.get(variable).copied() {
                        match merged.consts.get(variable).copied() {
                            Some(previous) if previous != value => {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "union alternatives disagree on natural parameter '{}': one alternative requires {previous} and another requires {value}",
                                        self.resolution.bindings[*variable].name
                                    ),
                                ));
                            }
                            Some(_) => {}
                            None => {
                                merged.consts.insert(*variable, value);
                                constrained = true;
                            }
                        }
                    }
                }
            }
            if constrained {
                *subst = merged;
            }
            return Ok(());
        }
        match &pattern.kind {
            ast::TypeKind::Lifetime(_) => {}
            ast::TypeKind::Named { path, arguments } => {
                let Some(id) = self.resolution.reference(pattern.span) else {
                    return Ok(());
                };
                // `T::Item` is an associated projection, not the binder `T`
                // itself: a concrete result type never determines `T` through
                // its projection. The projection is normalized after `T` is
                // inferred from the argument types.
                if path.len() == 2
                    && arguments.is_empty()
                    && self.resolution.bindings[id].kind == BindingKind::Generic
                    && self.resolution.bindings[id].name == path[0]
                {
                    return Ok(());
                }
                let arguments = arguments
                    .iter()
                    .filter(|argument| !matches!(argument.kind, ast::TypeKind::Lifetime(_)))
                    .collect::<Vec<_>>();
                if type_vars.contains(&id) && arguments.is_empty() {
                    if actual != Type::Never
                        && !matches!(actual, Type::Ref(_) | Type::RefMut(_))
                        && !actual.is_view()
                    {
                        let full = self.types.full(actual, span)?;
                        subst.types.entry(id).or_insert(full);
                    }
                    return Ok(());
                }
                let kind = self.resolution.bindings[id].kind;
                if kind == BindingKind::Alias {
                    if let Some((generics, body)) = self.types.alias_definition(id)
                        && generics.len() == arguments.len()
                    {
                        let map = generics
                            .iter()
                            .zip(arguments.iter().copied())
                            .map(|(generic, argument)| {
                                (self.resolution.binder(generic.span).unwrap(), argument)
                            })
                            .collect::<BTreeMap<_, _>>();
                        let expanded = substitute_alias_type(self.resolution, body, &map);
                        self.unify(
                            &expanded,
                            actual,
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                    return Ok(());
                }
                let b = &self.resolution.bindings[id];
                match (b.kind, b.name.as_str(), actual) {
                    (BindingKind::Builtin, "Box", Type::Box(p))
                    | (BindingKind::Builtin, "Vec", Type::Vec(p))
                        if arguments.len() == 1 =>
                    {
                        let pointee = self.types.pointees[p];
                        self.unify(
                            arguments[0],
                            pointee,
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                    (BindingKind::Data, _, _) => {
                        if let Some(layout) = actual.layout()
                            && self.types.enums[layout].definition == id
                        {
                            let actual_args = self.types.enums[layout].arguments.clone();
                            let actual_consts = self.types.enums[layout].consts.clone();
                            let kinds = self.types.generic_kinds(id);
                            let mut types = actual_args.iter();
                            let mut consts = actual_consts.iter();
                            for (argument, is_const) in arguments.iter().zip(kinds) {
                                if is_const {
                                    if let Some(value) = consts.next() {
                                        self.unify_length(
                                            argument, *value, const_vars, subst, span,
                                        )?;
                                    }
                                } else if let Some(actual) = types.next() {
                                    self.unify(
                                        argument,
                                        *actual,
                                        type_vars,
                                        const_vars,
                                        effect_vars,
                                        subst,
                                        span,
                                    )?;
                                }
                            }
                        }
                    }
                    _ => {}
                };
            }
            ast::TypeKind::Borrow {
                lifetime: _,
                mutable,
                inner,
            } => match (actual, &inner.kind) {
                (Type::Ref(p), _) | (Type::RefMut(p), _) => {
                    let pointee = self.types.pointees[p];
                    self.unify(
                        inner,
                        pointee,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                (Type::Slice(p), ast::TypeKind::Slice(element)) if !*mutable => {
                    let pointee = self.types.pointees[p];
                    self.unify(
                        element,
                        pointee,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                (Type::SliceMut(p), ast::TypeKind::Slice(element)) if *mutable => {
                    let pointee = self.types.pointees[p];
                    self.unify(
                        element,
                        pointee,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                _ => {}
            },
            ast::TypeKind::Function {
                parameters,
                result,
                effects,
                ..
            } => {
                let signature = match actual {
                    Type::Fn(id) | Type::Once(id) => self.types.function_types[id].clone(),
                    _ => return Ok(()),
                };
                if signature.parameters.len() != parameters.len() {
                    return Ok(());
                }
                for (parameter, actual) in parameters.iter().zip(&signature.parameters) {
                    let (inner, _) = split_grade(&parameter.ty);
                    self.unify(
                        inner,
                        *actual,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                self.unify(
                    result,
                    signature.result,
                    type_vars,
                    const_vars,
                    effect_vars,
                    subst,
                    span,
                )?;
                self.unify_effects(effects, signature.effects, effect_vars, subst, span)?;
            }
            ast::TypeKind::Tuple(items) => {
                if items.len() == 1 {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "one-element tuples are not supported; write '()' for unit or omit the trailing comma",
                    ));
                }
                if let Some(layout) = actual.layout().filter(|l| self.types.enums[*l].tuple) {
                    let elements = self.types.enums[layout].arguments.clone();
                    if elements.len() != items.len() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "tuple type has {} elements, but the value has {}",
                                items.len(),
                                elements.len()
                            ),
                        ));
                    }
                    for (item, element) in items.iter().zip(elements) {
                        self.unify(
                            item,
                            element,
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                }
            }
            ast::TypeKind::Array(element, length) => {
                if let Some(layout) = actual.layout()
                    && let Some((actual_element, actual_length)) = self.types.enums[layout].array
                {
                    self.unify(
                        element,
                        actual_element,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                    self.unify_length(length, actual_length, const_vars, subst, span)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    /// Accumulate one effect-row inclusion constraint from a callable
    /// argument. A declared row `{fixed | e1 | e2}` must cover the actual
    /// callable row. Constraints from every higher-order argument are solved
    /// together by [`Self::solve_effect_constraints`], so a variable that gets
    /// evidence from several positions is the union of that evidence instead of
    /// the first argument winning. Hiding an actual effect is impossible: a
    /// solution is accepted only when every constraint is covered.
    fn unify_effects(
        &mut self,
        declared: &[ast::Type],
        actual: u8,
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        let (fixed, variables) =
            crate::runtime_types::effect_bits_partial(self.resolution, declared)?;
        if variables.is_empty() {
            // Concrete rows are still checked by the final arrow coercion.
            return Ok(());
        }
        for variable in &variables {
            if !effect_vars.contains(variable) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "effect parameter '{}' is not in scope here",
                        self.resolution.bindings[*variable].name
                    ),
                ));
            }
        }
        // A variable already fixed by an explicit specialization is folded
        // into the concrete part of the constraint.
        let mut fixed = fixed;
        for variable in &variables {
            if let Some(value) = subst.effects.get(variable) {
                fixed |= *value;
            }
        }
        let variables = variables
            .into_iter()
            .filter(|variable| !subst.effects.contains_key(variable))
            .collect::<Vec<_>>();
        if variables.is_empty() && actual & !fixed != 0 {
            return Err(self.effect_row_mismatch(actual, fixed, span));
        }
        if !variables.is_empty() {
            self.effect_constraints.push(EffectConstraint {
                fixed,
                variables,
                actual,
                span,
            });
        }
        Ok(())
    }
    fn effect_row_mismatch(&self, actual: u8, covered: u8, span: Span) -> Diagnostic {
        let missing = actual & !covered;
        let names = (0..4)
            .filter(|bit| missing & (1 << bit) != 0)
            .map(|bit| match 1u8 << bit {
                crate::executable::PANIC => "panic",
                crate::executable::IO => "io",
                crate::executable::ALLOC => "alloc",
                _ => "suspend",
            })
            .collect::<Vec<_>>();
        Diagnostic::new(
            span,
            format!(
                "effect row mismatch: the callable argument requires {{{}}}, which is not covered by the specialized effect row",
                names.join(", ")
            ),
        )
    }
    /// Solve accumulated row constraints by finite enumeration.
    ///
    /// The effect universe has four concrete bits. For `n` unbound row
    /// variables the solver considers at most `16^n` assignments; the budget is
    /// 4096 assignments, so up to three variables are always exhaustive and a
    /// larger group is rejected with an explicit request for specialization.
    /// A solver result must be *unique componentwise-minimal*: every variable
    /// assignment is a subset of every other valid assignment. If several
    /// incomparable minimal solutions exist, the call is ambiguous and the
    /// diagnostic asks for explicit `::<...>` arguments. A variable that no
    /// constraint mentions is also rejected instead of defaulting to `{}`,
    /// because doing so could hide an effect promised by the caller.
    fn solve_effect_constraints(
        &mut self,
        mark: usize,
        effect_generics: &[&ast::Generic],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        if mark >= self.effect_constraints.len() {
            return Ok(());
        }
        let constraints = self.effect_constraints.split_off(mark);
        let mut allowed: BTreeMap<BindingId, u8> = BTreeMap::new();
        let mut required: BTreeMap<BindingId, u8> = BTreeMap::new();
        for generic in effect_generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            let excluded =
                crate::runtime_types::effect_excludes(self.resolution, generic)?.unwrap_or(0);
            let included =
                crate::runtime_types::effect_includes(self.resolution, generic)?.unwrap_or(0);
            allowed.insert(binder, EFFECT_BITS & !excluded);
            required.insert(binder, included);
        }
        let mut mentioned = BTreeSet::new();
        for constraint in &constraints {
            mentioned.extend(constraint.variables.iter().copied());
        }
        for generic in effect_generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            if !subst.effects.contains_key(&binder) && !mentioned.contains(&binder) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot infer effect row parameter '{}' of this call: no callable argument mentions it. Pass a callable whose effects constrain the row, or specialize it explicitly with '::<...>'",
                        generic.name
                    ),
                ));
            }
        }
        let mut unbound = Vec::new();
        for generic in effect_generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            if !subst.effects.contains_key(&binder) {
                unbound.push(binder);
            }
        }
        if unbound.is_empty() {
            for generic in effect_generics {
                let binder = self.resolution.binder(generic.span).unwrap();
                let included =
                    crate::runtime_types::effect_includes(self.resolution, generic)?.unwrap_or(0);
                if let Some(bits) = subst.effects.get(&binder) {
                    let missing = included & !*bits;
                    if missing != 0 {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "specialized effect row for '{}' omits {}, which is required by '<{}: Effects + {}>'",
                                generic.name,
                                effect_names(missing),
                                generic.name,
                                effect_names(included)
                            ),
                        ));
                    }
                }
            }
            for constraint in constraints {
                let covered = constraint.fixed
                    | constraint
                        .variables
                        .iter()
                        .filter_map(|variable| subst.effects.get(variable).copied())
                        .fold(0, |left, right| left | right);
                if constraint.actual & !covered != 0 {
                    return Err(self.effect_row_mismatch(
                        constraint.actual,
                        covered,
                        constraint.span,
                    ));
                }
            }
            return Ok(());
        }
        let mut assignments: u128 = 1;
        for _ in &unbound {
            assignments *= 16;
        }
        if assignments > 4096 {
            return Err(Diagnostic::new(
                span,
                "effect-row constraint group exceeds the finite solver budget (more than three unbound row variables); specialize the effect rows explicitly with '::<...>'",
            ));
        }
        let mut solutions: Vec<BTreeMap<BindingId, u8>> = vec![BTreeMap::new()];
        for variable in &unbound {
            let maximum = allowed.get(variable).copied().unwrap_or(EFFECT_BITS);
            let minimum = required.get(variable).copied().unwrap_or(0);
            let mut next = Vec::new();
            for solution in &solutions {
                for bits in 0..=EFFECT_BITS {
                    if bits & !maximum != 0 || bits & minimum != minimum {
                        continue;
                    }
                    let mut candidate = solution.clone();
                    candidate.insert(*variable, bits);
                    next.push(candidate);
                }
            }
            solutions = next;
        }
        let valid = solutions
            .into_iter()
            .filter(|solution| {
                constraints.iter().all(|constraint| {
                    let covered = constraint.fixed
                        | constraint
                            .variables
                            .iter()
                            .filter_map(|variable| solution.get(variable).copied())
                            .fold(0, |left, right| left | right);
                    constraint.actual & !covered == 0
                })
            })
            .collect::<Vec<_>>();
        if valid.is_empty() {
            let first = &constraints[0];
            let reachable = first.fixed
                | first
                    .variables
                    .iter()
                    .filter_map(|variable| allowed.get(variable).copied())
                    .fold(0, |left, right| left | right);
            let excluded = first.actual & !reachable;
            if excluded != 0 {
                let names = (0..4)
                    .filter(|bit| excluded & (1 << bit) != 0)
                    .map(|bit| match 1u8 << bit {
                        crate::executable::PANIC => "panic",
                        crate::executable::IO => "io",
                        crate::executable::ALLOC => "alloc",
                        _ => "suspend",
                    })
                    .collect::<Vec<_>>();
                fn effect_spelling(ty: &ast::Type) -> String {
                    match &ty.kind {
                        ast::TypeKind::Named { path, .. } => path.join("."),
                        ast::TypeKind::Binary {
                            op: crate::lexer::Kind::Pipe,
                            left,
                            right,
                        } => format!("{} | {}", effect_spelling(left), effect_spelling(right)),
                        _ => "concrete effects".to_owned(),
                    }
                }
                let variables = first
                    .variables
                    .iter()
                    .map(|variable| format!("'{}'", self.resolution.bindings[*variable].name))
                    .collect::<Vec<_>>()
                    .join(", ");
                let bound = first.variables.first().and_then(|variable| {
                    effect_generics
                        .iter()
                        .find(|generic| {
                            self.resolution.binder(generic.span).as_ref() == Some(variable)
                        })
                        .and_then(|generic| generic.excludes.as_ref())
                        .map(|excludes| {
                            format!(
                                "<{}: Effects - {}>",
                                self.resolution.bindings[*variable].name,
                                effect_spelling(excludes)
                            )
                        })
                });
                let bound = bound.unwrap_or_else(|| format!("the bound on {variables}"));
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "effect {} is excluded by '{bound}', but the callable argument requires it",
                        names
                            .iter()
                            .map(|name| format!("'{name}'"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                ));
            }
            return Err(Diagnostic::new(
                first.span,
                format!(
                    "no specialization of the effect row parameters satisfies every callable argument; the actual row {:#06b} conflicts with another argument",
                    first.actual
                ),
            ));
        }
        let minimal = valid
            .iter()
            .filter(|candidate| {
                !valid.iter().any(|other| {
                    other != *candidate
                        && other.iter().all(|(variable, bits)| {
                            bits & !candidate.get(variable).copied().unwrap_or(0) == 0
                        })
                })
            })
            .collect::<Vec<_>>();
        if minimal.len() != 1 {
            let names = unbound
                .iter()
                .map(|variable| format!("'{}'", self.resolution.bindings[*variable].name))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Diagnostic::new(
                span,
                format!(
                    "effect row parameters {names} have several incomparable minimal solutions; the callable arguments do not identify one row. Specialize them explicitly with '::<...>'"
                ),
            ));
        }
        for (variable, bits) in minimal[0] {
            subst.effects.insert(*variable, *bits);
        }
        Ok(())
    }
    /// Infer or check one array-length expression against an actual length. A
    /// bare unbound const parameter is inferred; every other expression is
    /// evaluated with the current const substitution.
    fn unify_length(
        &self,
        declared: &ast::Type,
        actual: usize,
        const_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        if let ast::TypeKind::Named { arguments, .. } = &declared.kind
            && arguments.is_empty()
            && let Some(id) = self.resolution.reference(declared.span)
            && const_vars.contains(&id)
        {
            match subst.consts.get(&id) {
                Some(value) if *value != actual => {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "array length mismatch: a previous argument bound the length parameter to {value}, but this argument has length {actual}"
                        ),
                    ));
                }
                Some(_) => return Ok(()),
                None => {
                    subst.consts.insert(id, actual);
                    return Ok(());
                }
            }
        }
        match crate::length::eval_type(self.resolution, self.logical, &subst.consts, declared) {
            Ok(value) if value == actual => Ok(()),
            Ok(value) => Err(Diagnostic::new(
                span,
                format!("array length mismatch: expected {value}, found {actual}"),
            )),
            Err(error) => Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer the array length parameter from length {actual} or check its declared length: {}",
                    error.message
                ),
            )),
        }
    }
    /// Check values against declared types, inferring type and const variables
    /// left to right. Returns type, grade, and const arguments plus the checked
    /// values. `base` carries substitutions already fixed by the callee, such as
    /// the trait arguments of an inherited default method; declared parameter
    /// types that mention them resolve instead of looking like unbound type
    /// parameters.
    #[allow(clippy::too_many_arguments)]
    fn infer(
        &mut self,
        generics: &[ast::Generic],
        explicit: Option<&[ast::Type]>,
        pairs: &[(&ast::Type, &ast::Expr)],
        result: Option<(&ast::Type, Type)>,
        freshen_borrowed_arguments: bool,
        self_type: Option<Type>,
        base: Option<&crate::runtime_types::Subst>,
        what: &str,
        span: Span,
    ) -> Result<Inferred> {
        let mut type_generics = Vec::new();
        let mut const_generics = Vec::new();
        let mut grade_generics = Vec::new();
        let mut effect_generics = Vec::new();
        for generic in generics {
            if is_grade_generic(self.resolution, generic) {
                grade_generics.push(generic);
            } else if is_const_generic(self.resolution, generic) {
                const_generics.push(generic);
            } else if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                effect_generics.push(generic);
            } else {
                type_generics.push(generic);
            }
        }
        let type_vars = type_generics
            .iter()
            .map(|generic| self.resolution.binder(generic.span).unwrap())
            .collect::<Vec<_>>();
        let const_vars = const_generics
            .iter()
            .map(|generic| self.resolution.binder(generic.span).unwrap())
            .collect::<Vec<_>>();
        let effect_vars = effect_generics
            .iter()
            .map(|generic| self.resolution.binder(generic.span).unwrap())
            .collect::<Vec<_>>();
        let mut subst = base.cloned().unwrap_or_default();
        subst.self_type = self_type;
        let constraint_mark = self.effect_constraints.len();
        let mut grade_arguments = Vec::new();
        if let Some(list) = explicit {
            if list.len() != generics.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "{what} expects {} type/grade/const/effect arguments, found {}",
                        generics.len(),
                        list.len()
                    ),
                ));
            }
            let mut type_index = 0;
            let mut const_index = 0;
            for (generic, argument) in generics.iter().zip(list) {
                if is_grade_generic(self.resolution, generic) {
                    grade_arguments.push(grades::evaluate(
                        self.resolution,
                        &self.grades,
                        argument,
                    )?);
                } else if is_const_generic(self.resolution, generic) {
                    let value = crate::length::eval_type(
                        self.resolution,
                        self.logical,
                        &self.consts,
                        argument,
                    )?;
                    subst.consts.insert(const_vars[const_index], value);
                    const_index += 1;
                } else if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                    let binder = self.resolution.binder(generic.span).unwrap();
                    let value = crate::runtime_types::effect_bits_with(
                        self.resolution,
                        std::slice::from_ref(argument),
                        &self.effect_arguments,
                    )?;
                    subst.effects.insert(binder, value);
                } else {
                    let ty = self.ty(argument)?;
                    let ty = self.types.full(ty, span)?;
                    subst.types.insert(type_vars[type_index], ty);
                    type_index += 1;
                }
            }
        } else {
            if let Some((declared, expected)) = result {
                self.unify(
                    declared,
                    expected,
                    &type_vars,
                    &const_vars,
                    &effect_vars,
                    &mut subst,
                    span,
                )?;
            }
        }
        let parameter_grade_exprs = pairs
            .iter()
            .map(|(declared, _)| split_grade(declared).1.cloned())
            .collect::<Vec<_>>();
        let mut values = Vec::new();
        for (declared, value) in pairs.iter() {
            let (declared, _) = split_grade(declared);
            if let (ast::TypeKind::Array(element, length), ast::ExprKind::Array(items)) =
                (&declared.kind, &value.kind)
            {
                let checked = self.infer_array_argument(
                    element,
                    length,
                    items,
                    &type_vars,
                    &const_vars,
                    &effect_vars,
                    &mut subst,
                    span,
                )?;
                values.push(checked);
                continue;
            }
            let wanted = if self.mentions(declared, &type_vars, &const_vars, &effect_vars, &subst) {
                None
            } else {
                Some(self.types.ty_in(declared, &subst)?)
            };
            // A call argument's record lifetimes are instantiated from the
            // argument value, not forced to the callee's declaration names.
            // Freshening keeps the construction checked against local
            // provenance while the call boundary relates the two sets.
            let wanted = match wanted {
                Some(ty) if freshen_borrowed_arguments => {
                    Some(self.types.freshen_borrows(ty, value.span)?)
                }
                other => other,
            };
            let value = self.expr_expected(value, wanted)?;
            self.unify(
                declared,
                value.ty,
                &type_vars,
                &const_vars,
                &effect_vars,
                &mut subst,
                span,
            )?;
            values.push(value);
        }
        self.solve_effect_constraints(constraint_mark, &effect_generics, &mut subst, span)?;
        // General grade inference for direct calls: solve grade parameters from
        // explicitly graded arguments. All equations are accumulated and solved
        // simultaneously; an ungraded argument never invents a grade.
        if explicit.is_none() && !grade_generics.is_empty() {
            let binders = grade_generics
                .iter()
                .map(|generic| self.resolution.binder(generic.span).unwrap())
                .collect::<Vec<_>>();
            let constraints = parameter_grade_exprs
                .iter()
                .zip(&values)
                .filter_map(|(grade_expr, value)| {
                    let grade_expr = grade_expr.as_ref()?;
                    let actual = self.expression_grade(value)?;
                    Some((grade_expr, actual))
                })
                .collect::<Vec<_>>();
            let solved = grades::solve_all(self.resolution, &self.grades, &binders, &constraints)?
                .unwrap_or_default();
            for (generic, binder) in grade_generics.iter().zip(&binders) {
                let Some(value) = solved.get(binder) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer usage grade parameter '{}' of {what}: no argument is explicitly graded @[{}] or its grade equation has no unique solution in the decidable natural/finite-algebra fragment. Specialize it explicitly with '::<...>'",
                            generic.name, generic.name
                        ),
                    ));
                };
                grade_arguments.push(*value);
            }
        }
        let mut type_arguments = Vec::new();
        for (var, generic) in type_vars.iter().zip(&type_generics) {
            let Some(ty) = subst.types.get(var) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot infer type parameter '{}' of {what}; write explicit type arguments with ::<...>",
                        generic.name
                    ),
                ));
            };
            type_arguments.push(*ty);
        }
        let mut const_arguments = Vec::new();
        for (var, generic) in const_vars.iter().zip(&const_generics) {
            let Some(value) = subst.consts.get(var) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot infer natural length parameter '{}' of {what}; pass an inline array argument or specialize it explicitly with ::<...>",
                        generic.name
                    ),
                ));
            };
            const_arguments.push(*value);
        }
        let mut effect_arguments = Vec::new();
        for (var, generic) in effect_vars.iter().zip(&effect_generics) {
            let Some(value) = subst.effects.get(var) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot infer effect row parameter '{}' of {what}; pass a callable argument whose effects identify the row, or specialize it explicitly with ::<...>",
                        generic.name
                    ),
                ));
            };
            effect_arguments.push(*value);
        }
        Ok((
            type_arguments,
            grade_arguments,
            const_arguments,
            effect_arguments,
            values,
        ))
    }
    /// Check an inline array literal directly against a parametric array
    /// parameter such as `[T; N]`. This is what makes length inference
    /// unambiguous: the literal's length binds `N`, and its first element
    /// binds an unconstrained element type. Without this path the literal
    /// would default to a `Vec<T>` because there is no complete expected type.
    #[allow(clippy::too_many_arguments)]
    fn infer_array_argument(
        &mut self,
        element_decl: &ast::Type,
        length_decl: &ast::Type,
        items: &[ast::Expr],
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<Expr> {
        let known = if self.mentions(element_decl, type_vars, const_vars, effect_vars, subst) {
            None
        } else {
            Some(self.types.ty_in(element_decl, subst)?)
        };
        let mut checked = Vec::new();
        for item in items {
            if let (
                ast::TypeKind::Array(inner_element, inner_length),
                ast::ExprKind::Array(inner),
            ) = (&element_decl.kind, &item.kind)
            {
                checked.push(self.infer_array_argument(
                    inner_element,
                    inner_length,
                    inner,
                    type_vars,
                    const_vars,
                    effect_vars,
                    subst,
                    span,
                )?);
            } else {
                checked.push(self.expr_expected(item, known)?);
            }
        }
        let element = match known {
            Some(element) => element,
            None => {
                let Some(first) = checked.iter().find(|value| value.ty != Type::Never) else {
                    return Err(Diagnostic::new(
                        span,
                        "cannot infer the element type of an empty array literal; annotate the binding or specialize the function explicitly",
                    ));
                };
                let first = self.types.full(first.ty, span)?;
                self.unify(
                    element_decl,
                    first,
                    type_vars,
                    const_vars,
                    effect_vars,
                    subst,
                    span,
                )?;
                if self.mentions(element_decl, type_vars, const_vars, effect_vars, subst) {
                    return Err(Diagnostic::new(
                        span,
                        "cannot infer the array element type; write explicit type arguments with ::<...>",
                    ));
                }
                self.types.ty_in(element_decl, subst)?
            }
        };
        self.unify_length(length_decl, items.len(), const_vars, subst, span)?;
        if self.const_mentions(length_decl, const_vars, subst) {
            return Err(Diagnostic::new(
                span,
                "cannot infer the natural array length parameter; write explicit specialization with ::<...>",
            ));
        }
        let ty = self.types.array(element, items.len(), span)?;
        let Type::Enum(layout) = ty else {
            unreachable!("array construction returns an enum layout")
        };
        let mut diverges = false;
        let mut fields = Vec::with_capacity(checked.len());
        for value in checked {
            let at = value.span;
            let value = self.coerce(value, element, at)?;
            diverges |= value.ty == Type::Never;
            fields.push(value);
        }
        Ok(Expr {
            kind: ExprKind::Construct {
                enum_id: layout,
                tag: 0,
                fields,
            },
            ty: if diverges {
                Type::Never
            } else {
                Type::Enum(layout)
            },
            span,
            resource: None,
        })
    }
    /// Check one of the built-in structured-task operations.
    fn task_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.functions.uses_tasks = true;
        match name {
            "Task.scope" => {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        "Task.scope takes no type arguments; its result is the scope lambda's result",
                    ));
                }
                if arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "Task.scope expects one scope lambda, found {} arguments",
                            arguments.len()
                        ),
                    ));
                }
                let (body, result, _, result_grade) =
                    self.task_callable(&arguments[0], true, false, "Task.scope", span)?;
                if crate::runtime_types::is_reference_container(self.types, result) {
                    return Err(Diagnostic::new(
                        span,
                        "a task scope cannot return a reference element container; keep the container lexical and return the borrowed record it was built from",
                    ));
                }
                if crate::runtime_types::contains_task(self.types, result) {
                    return Err(Diagnostic::new(
                        span,
                        "Task.scope cannot return a task handle; a child handle must not escape its scope",
                    ));
                }
                if result_grade.is_some_and(|grade| !grade.is_one()) {
                    return Err(Diagnostic::new(
                        span,
                        "a task result supports exactly @[1] (owning transfer or copyable must-use) or no grade",
                    ));
                }
                let obligation =
                    self.linear_type(result) || result_grade.is_some_and(Grade::is_one);
                let failure = self.types.result(result, span).ok();
                let value = Expr {
                    kind: ExprKind::TaskScope {
                        body: Box::new(body),
                        result,
                        obligation,
                        failure,
                    },
                    ty: result,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "Task.spawn" => {
                if arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "Task.spawn expects one task lambda, found {} arguments",
                            arguments.len()
                        ),
                    ));
                }
                if self.scope_depth == 0 {
                    return Err(Diagnostic::new(
                        span,
                        "Task.spawn requires an enclosing Task.scope; detached tasks are not supported",
                    ));
                }
                let (mut body, result, _, result_grade) =
                    self.task_callable(&arguments[0], false, true, "Task.spawn", span)?;
                if crate::runtime_types::contains_task_exit_borrow(self.types, result) {
                    return Err(Diagnostic::new(
                        span,
                        "a task cannot return TaskExit<T>; a joined borrow is lexical to the enclosing scope, and a task result is joined explicitly",
                    ));
                }
                if crate::runtime_types::contains_task(self.types, result) {
                    return Err(Diagnostic::new(
                        span,
                        "a task cannot return a task handle; a child handle must not escape its scope",
                    ));
                }
                if result == Type::Never {
                    return Err(Diagnostic::new(
                        span,
                        "Task<T> cannot use Never as its result type; a task that cannot return cannot be joined",
                    ));
                }
                if result_grade.is_some_and(|grade| !grade.is_one()) {
                    return Err(Diagnostic::new(
                        span,
                        "a task result supports exactly @[1] (owning transfer or copyable must-use) or no grade",
                    ));
                }
                let wanted = match (explicit, expected) {
                    (Some([ty]), _) => {
                        let lowered = self.ty(ty)?;
                        Some(self.types.full(lowered, span)?)
                    }
                    (Some(_), _) => {
                        return Err(Diagnostic::new(
                            span,
                            "Task.spawn accepts at most one result type argument",
                        ));
                    }
                    (None, Some(Type::Task(p))) => Some(self.types.pointees[p]),
                    (None, Some(other)) => {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "Task.spawn produces Task<T>, but the expected type is {}",
                                self.types.name(other)
                            ),
                        ));
                    }
                    (None, None) => None,
                };
                let result = match wanted {
                    Some(wanted) => {
                        self.expect(result, wanted, span)?;
                        if !self.same_layout(result, wanted) {
                            let (id, _) = Self::function_parts(body.ty).unwrap();
                            let signature = self.types.function_types[id].clone();
                            let target = self.types.function_type_with(
                                vec![],
                                wanted,
                                signature.effects,
                                vec![],
                                signature.result_grade,
                                true,
                                signature.linear,
                                crate::runtime_types::BorrowSig::default(),
                            );
                            body = self.coerce(body, Type::Once(target), span)?;
                        }
                        wanted
                    }
                    None => result,
                };
                let obligation =
                    self.linear_type(result) || result_grade.is_some_and(Grade::is_one);
                let handle = Type::Task(self.types.pointer(result));
                let value = Expr {
                    kind: ExprKind::TaskSpawn {
                        body: Box::new(body),
                        result,
                        obligation,
                    },
                    ty: handle,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "Task.yield" => {
                if explicit.is_some() || !arguments.is_empty() {
                    return Err(Diagnostic::new(span, "Task.yield takes no arguments"));
                }
                self.require(SUSPEND, span)?;
                Ok(Expr {
                    kind: ExprKind::TaskYield,
                    ty: Type::Bool,
                    span,
                    resource: None,
                })
            }
            "Task.check_cancel" => {
                if explicit.is_some() || !arguments.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        "Task.check_cancel takes no arguments",
                    ));
                }
                Ok(Expr {
                    kind: ExprKind::TaskCheckCancel,
                    ty: Type::Bool,
                    span,
                    resource: None,
                })
            }
            "Task.cancel" => {
                if explicit.is_some() || arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        "Task.cancel expects one '&task' argument",
                    ));
                }
                let ast::ExprKind::Unary {
                    op: Kind::Amp,
                    mutable: false,
                    operand,
                } = &arguments[0].kind
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        "Task.cancel borrows the handle: write Task.cancel(&task)",
                    ));
                };
                let slot = self.slot(operand.span)?;
                let ty = self.locals[slot].ty;
                if !matches!(ty, Type::Task(_)) {
                    return Err(Diagnostic::new(
                        operand.span,
                        format!(
                            "Task.cancel expects &Task<T>, found {}",
                            self.types.name(ty)
                        ),
                    ));
                }
                let reference = Expr {
                    kind: ExprKind::Borrow(slot),
                    ty: Type::Ref(self.types.pointer(ty)),
                    span: operand.span,
                    resource: None,
                };
                Ok(Expr {
                    kind: ExprKind::TaskCancel(Box::new(reference)),
                    ty: Type::Unit,
                    span,
                    resource: None,
                })
            }
            "Task.join" => {
                if explicit.is_some() || arguments.len() != 1 {
                    return Err(Diagnostic::new(
                        span,
                        "Task.join expects one Task<T> handle",
                    ));
                }
                let task = self.expr(&arguments[0])?;
                let Type::Task(p) = task.ty else {
                    return Err(Diagnostic::new(
                        task.span,
                        format!(
                            "Task.join expects Task<T>, found {}",
                            self.types.name(task.ty)
                        ),
                    ));
                };
                let payload = self.types.pointees[p];
                self.require(SUSPEND, span)?;
                let exit = self.types.task_exit(payload, span)?;
                let ty = exit.result;
                let obligation = self.linear_type(payload) || self.value_moves_linear(&task);
                let value = Expr {
                    kind: ExprKind::TaskJoin {
                        task: Box::new(task),
                        exit,
                        obligation,
                    },
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            _ => Err(Diagnostic::new(
                span,
                format!("unsupported task operation '{name}'"),
            )),
        }
    }
    /// Check a task/scope body as an owned once callable with no parameters.
    /// `scope_root` marks the immediate `Task.scope` lambda, whose body may
    /// spawn. Every other function value resets lexical scope depth.
    fn task_callable(
        &mut self,
        argument: &ast::Expr,
        scope_root: bool,
        static_body: bool,
        what: &str,
        span: Span,
    ) -> Result<(Expr, Type, u8, Option<Grade>)> {
        let value = if scope_root {
            let ast::ExprKind::Lambda(lambda) = &argument.kind else {
                return Err(Diagnostic::new(
                    argument.span,
                    format!(
                        "{what} requires an inline, explicitly typed lambda so its scope is lexical"
                    ),
                ));
            };
            self.lambda(lambda, argument.span, None, true)?
        } else {
            let saved = self.scope_depth;
            self.scope_depth = 0;
            let value = self.expr(argument);
            self.scope_depth = saved;
            value?
        };
        let Some((id, _)) = Self::function_parts(value.ty) else {
            return Err(Diagnostic::new(
                value.span,
                format!(
                    "{what} expects an owned once callable with no parameters, found {}",
                    self.types.name(value.ty)
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        if !signature.parameters.is_empty() {
            return Err(Diagnostic::new(
                value.span,
                format!("{what} expects a callable with no parameters"),
            ));
        }
        let result = signature.result;
        let effects = signature.effects | ALLOC | PANIC | SUSPEND;
        self.require(effects, span)?;
        let static_function = Self::callable_function(&value);
        if static_body && static_function.is_none() {
            return Err(Diagnostic::new(
                value.span,
                format!(
                    "{what} requires a statically known function or lambda body so cancellation cleanup can be checked; bind a named function or use an inline lambda"
                ),
            ));
        }
        let target = self.types.function_type_with(
            vec![],
            result,
            effects,
            vec![],
            signature.result_grade,
            true,
            signature.linear,
            signature.borrows.clone(),
        );
        let value = self.coerce(value, Type::Once(target), span)?;
        Ok((value, result, effects, signature.result_grade))
    }
    fn user_call(
        &mut self,
        id: BindingId,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let f = self.functions.declared[&id].ast;
        if arguments.len() != f.parameters.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count for '{}': expected {}, found {}",
                    f.name,
                    f.parameters.len(),
                    arguments.len()
                ),
            ));
        }
        if explicit.is_some() && f.generics.is_empty() {
            return Err(Diagnostic::new(
                span,
                format!("'{}' is not generic; remove the type arguments", f.name),
            ));
        }
        let pairs = f
            .parameters
            .iter()
            .zip(arguments)
            .filter(|(p, _)| !p.erased)
            .map(|(p, a)| (&p.ty, a))
            .collect::<Vec<_>>();
        let what = format!("'{}'", f.name);
        let hint = match expected {
            Some(expected) => Some((self.result_type_hint(&f.result)?, expected)),
            None => None,
        };
        let (type_arguments, grade_arguments, const_arguments, effect_arguments, values) = self
            .infer(
                &f.generics,
                explicit,
                &pairs,
                hint.as_ref()
                    .map(|(declared, expected)| (declared, *expected)),
                true,
                None,
                None,
                &what,
                span,
            )?;
        let index = self.functions.instance(
            self.types,
            self.resolution,
            id,
            type_arguments,
            grade_arguments,
            const_arguments,
            effect_arguments,
            None,
            Some(span),
        )?;
        let signature = self.functions.signatures[index].clone();
        self.require(signature.effects, span)?;
        let mut diverges = false;
        let mut coerced = Vec::with_capacity(values.len());
        for (value, ty) in values.into_iter().zip(&signature.parameters) {
            diverges |= value.ty == Type::Never;
            coerced.push(self.coerce(value, *ty, span)?);
        }
        let values = coerced;
        // Runtime parameter types aligned with the source parameter list. Erased
        // parameters are absent from the runtime signature.
        let mut signature_types = signature.parameters.iter();
        let parameter_types = f
            .parameters
            .iter()
            .map(|parameter| {
                if parameter.erased {
                    None
                } else {
                    Some(*signature_types.next().expect("runtime parameter"))
                }
            })
            .collect::<Vec<_>>();
        // Dependent erased parameters are checked left to right. A later
        // parameter type may mention an earlier erased kernel binder or an
        // immutable runtime scalar used as a symbolic index; the call-site
        // substitutes the actual scalar/proof terms.
        let mut callee_binders = Vec::new();
        let mut callee_types = Vec::new();
        let mut callee_actuals = Vec::new();
        for (position, (parameter, evidence)) in f.parameters.iter().zip(arguments).enumerate() {
            if !parameter.erased {
                let binder = self.resolution.binder(parameter.span).unwrap();
                if !diverges
                    && let Some(carrier) = parameter_types[position].and_then(Type::scalar_carrier)
                    && f.parameters[position + 1..].iter().any(|later| {
                        later.erased
                            && !matches!(later.ty.kind, ast::TypeKind::Predicate(_))
                            && type_references_binding(self.resolution, &later.ty, binder)
                    })
                {
                    let actual = self.scalar_argument(
                        &arguments[position],
                        parameter_types[position].unwrap(),
                        span,
                    )?;
                    callee_binders.push(binder);
                    callee_types.push(Term::Scalar(carrier));
                    callee_actuals.push(actual);
                }
                continue;
            }
            if diverges {
                continue;
            }
            if matches!(parameter.ty.kind, ast::TypeKind::Predicate(_)) {
                let proposition = proposition_of(self.resolution, f, parameter)?;
                self.discharge(&proposition, &values, evidence, span)?;
            } else {
                self.discharge_kernel_call(
                    parameter,
                    evidence,
                    &mut callee_binders,
                    &mut callee_types,
                    &mut callee_actuals,
                    span,
                )?;
            }
        }
        let ty = if diverges {
            Type::Never
        } else {
            call_result_type(&signature)
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Function(index), values),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    fn record(
        &mut self,
        path: &ast::Expr,
        fields: &[(String, ast::Expr)],
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let (base, explicit) = match &path.kind {
            ast::ExprKind::Specialize { callee, arguments } => {
                (callee.as_ref(), Some(arguments.as_slice()))
            }
            _ => (path, None),
        };
        let id = self
            .resolution
            .reference(base.span)
            .filter(|id| self.types.is_record(*id))
            .ok_or_else(|| Diagnostic::new(base.span, "expected a record (struct) type name"))?;
        let (generics, declared) = self.types.record_fields(id);
        for (name, value) in fields {
            if !declared.iter().any(|f| f.name == *name) {
                return Err(Diagnostic::new(
                    value.span,
                    format!("record has no field '{name}'"),
                ));
            }
        }
        if let Some(missing) = declared
            .iter()
            .find(|f| !fields.iter().any(|(n, _)| *n == f.name))
        {
            return Err(Diagnostic::new(
                span,
                format!("missing field '{}' in record literal", missing.name),
            ));
        }
        // Values are checked and evaluated in source order.
        let pairs = fields
            .iter()
            .map(|(name, value)| {
                (
                    &declared.iter().find(|f| f.name == *name).unwrap().ty,
                    value,
                )
            })
            .collect::<Vec<_>>();
        let mut expected_layout = expected
            .and_then(Type::layout)
            .filter(|l| self.types.enums[*l].definition == id);
        if explicit.is_none()
            && expected_layout.is_none()
            && let Some(Type::Union(union)) = expected
        {
            let matching = self.types.unions[union]
                .members
                .iter()
                .filter_map(|member| {
                    member
                        .layout()
                        .filter(|layout| self.types.enums[*layout].definition == id)
                })
                .collect::<Vec<_>>();
            match matching.as_slice() {
                [] => {}
                [layout] => expected_layout = Some(*layout),
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this record literal fits several union alternatives; write explicit type arguments",
                    ));
                }
            }
        }
        let declared_lifetimes = self.types.record_lifetimes(id);
        let mut explicit_lifetimes = Vec::new();
        let mut explicit_types: Vec<ast::Type> = Vec::new();
        let mut seen_type = false;
        if let Some(arguments) = explicit {
            for argument in arguments {
                if let ast::TypeKind::Lifetime(name) = &argument.kind {
                    if seen_type {
                        return Err(Diagnostic::new(
                            span,
                            "record lifetime arguments must precede type arguments",
                        ));
                    }
                    explicit_lifetimes.push(name.clone());
                } else {
                    seen_type = true;
                    explicit_types.push(argument.clone());
                }
            }
        }
        if explicit.is_some() && explicit_lifetimes.len() != declared_lifetimes.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "this record expects {} lifetime argument(s), found {}",
                    declared_lifetimes.len(),
                    explicit_lifetimes.len()
                ),
            ));
        }
        let (arguments, consts, lifetimes, values) =
            if let (None, Some(layout)) = (explicit, expected_layout) {
                let arguments = self.types.enums[layout].arguments.clone();
                let consts = self.types.enums[layout].consts.clone();
                let lifetimes = self.types.enums[layout].lifetimes.clone();
                let mut subst = crate::runtime_types::Subst::default();
                let mut type_index = 0;
                let mut const_index = 0;
                for (generic, is_const) in generics.iter().zip(self.types.generic_kinds(id)) {
                    let binder = self.resolution.binder(generic.span).unwrap();
                    if is_const {
                        subst.consts.insert(binder, consts[const_index]);
                        const_index += 1;
                    } else {
                        subst.types.insert(binder, arguments[type_index]);
                        type_index += 1;
                    }
                }
                for (declared, actual) in declared_lifetimes.iter().zip(&lifetimes) {
                    subst
                        .lifetimes
                        .insert(declared.name.clone(), actual.clone());
                }
                let mut values = Vec::new();
                for (declared, value) in &pairs {
                    let wanted = self.types.ty_in(declared, &subst)?;
                    values.push(self.expr_expected(value, Some(wanted))?);
                }
                (arguments, consts, lifetimes, values)
            } else {
                let (arguments, _grades, consts, _effects, values) = self.infer(
                    generics,
                    if explicit.is_some() {
                        Some(explicit_types.as_slice())
                    } else {
                        None
                    },
                    &pairs,
                    None,
                    // Nested borrowed fields must be inferred from their
                    // actual values, not from the enclosing declaration's
                    // lifetime names. The final construct validates explicit
                    // outer lifetime relationships against field provenance.
                    true,
                    None,
                    None,
                    "this record",
                    span,
                )?;
                let lifetimes = if explicit.is_some() {
                    explicit_lifetimes
                } else {
                    (0..declared_lifetimes.len())
                        .map(|_| self.types.fresh_lifetime("inferred record lifetime"))
                        .collect()
                };
                (arguments, consts, lifetimes, values)
            };
        let layout = self
            .types
            .instantiate(id, arguments, consts, lifetimes, span)?;
        let variant = self.types.enums[layout].variants[0].clone();
        let mut diverges = false;
        for ((name, _), value) in fields.iter().zip(&values) {
            let index = variant.names.iter().position(|n| n == name).unwrap();
            self.expect(value.ty, variant.fields[index], value.span)?;
            diverges |= value.ty == Type::Never;
        }
        let order = fields
            .iter()
            .map(|(name, _)| variant.names.iter().position(|n| n == name).unwrap())
            .collect::<Vec<_>>();
        let ty = if diverges {
            Type::Never
        } else {
            Type::Enum(layout)
        };
        let construct = if order.iter().enumerate().all(|(i, o)| i == *o) {
            Expr {
                kind: ExprKind::Construct {
                    enum_id: layout,
                    tag: 0,
                    fields: values,
                },
                ty,
                span,
                resource: None,
            }
        } else {
            // Evaluate in source order into temporaries, then build in layout order.
            let mut statements = Vec::new();
            let mut slots = vec![0; order.len()];
            for (value, index) in values.into_iter().zip(&order) {
                let slot = self.temp(variant.fields[*index], value.span)?;
                self.locals[slot].linear = self.value_moves_linear(&value);
                slots[*index] = slot;
                statements.push(Statement::Let(slot, value));
            }
            let fields = slots
                .iter()
                .zip(&variant.fields)
                .map(|(slot, ty)| Expr {
                    kind: ExprKind::Local(*slot),
                    ty: *ty,
                    span,
                    resource: None,
                })
                .collect();
            let tail = Expr {
                kind: ExprKind::Construct {
                    enum_id: layout,
                    tag: 0,
                    fields,
                },
                ty: Type::Enum(layout),
                span,
                resource: None,
            };
            Expr {
                kind: ExprKind::Block(Block {
                    statements,
                    tail: Some(Box::new(tail)),
                    ty,
                }),
                ty,
                span,
                resource: None,
            }
        };
        match expected {
            Some(expected) => self.coerce(construct, expected, span),
            None => Ok(construct),
        }
    }
    /// Check an anonymous structural record literal. Fields are evaluated in
    /// source order (effects and ownership stay left-to-right) and the value is
    /// built in the canonical name-sorted row. An expected structural row is a
    /// field-type hint, and the ordinary subtype coercion then performs any
    /// width or nested representation change.
    fn structural_literal(
        &mut self,
        fields: &[(String, ast::Expr)],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        // An expected union of structural rows is treated as a finite set of
        // candidates. Each candidate supplies field-type hints; the literal
        // must be accepted by exactly one. Committing to the first alternative
        // would silently choose a representation.
        let mut candidates = Vec::new();
        match expected {
            Some(expected) if self.types.is_structural(expected) => {
                if let Some(row) = self.types.structural_row(expected) {
                    candidates.push((expected, row));
                }
            }
            Some(Type::Union(id)) => {
                for member in self.types.unions[id].members.clone() {
                    if let Some(row) = self.types.structural_row(member) {
                        candidates.push((member, row));
                    }
                }
            }
            _ => {}
        }
        let mut accepted = Vec::new();
        let mut first_error = None;
        if candidates.len() > 1 {
            for (member, row) in &candidates {
                match self.structural_literal_fields(fields, Some(row), span) {
                    Ok((value, source)) if self.subtype(source, *member) => accepted.push(value),
                    Ok(_) => {}
                    Err(error) => {
                        if first_error.is_none() {
                            first_error = Some(error);
                        }
                    }
                }
            }
        }
        let construct = match accepted.len() {
            0 if candidates.len() > 1 => {
                // Report the first candidate's real field-type error rather
                // than an opaque union mismatch.
                if let Some(error) = first_error {
                    return Err(error);
                }
                let (_, row) = &candidates[0];
                self.structural_literal_fields(fields, Some(row), span)?.0
            }
            1 => accepted.pop().expect("one accepted literal"),
            _ if accepted.len() > 1 => {
                return Err(Diagnostic::new(
                    span,
                    "this structural record literal fits several union alternatives; add an explicit annotation",
                ));
            }
            _ => {
                let row = candidates.first().map(|(_, row)| row);
                self.structural_literal_fields(fields, row, span)?.0
            }
        };
        match expected {
            Some(expected) => self.coerce(construct, expected, span),
            None => Ok(construct),
        }
    }
    /// Build one structural literal with an optional candidate-row hint.
    fn structural_literal_fields(
        &mut self,
        fields: &[(String, ast::Expr)],
        target_row: Option<&Vec<(String, Type)>>,
        span: Span,
    ) -> Result<(Expr, Type)> {
        let mut values = Vec::with_capacity(fields.len());
        let mut diverges = false;
        for (name, value) in fields {
            let hint = target_row
                .and_then(|row| row.iter().find(|(field, _)| field == name))
                .map(|(_, ty)| *ty);
            let value = self.expr_expected(value, hint)?;
            diverges |= value.ty == Type::Never;
            values.push((name.clone(), value));
        }
        let source_row = values
            .iter()
            .map(|(name, value)| (name.clone(), value.ty))
            .collect::<Vec<_>>();
        let ty = self.types.structural(source_row, span)?;
        let canonical = self
            .types
            .structural_row(ty)
            .expect("a checked structural literal has a structural row");
        let source = ty;
        let construct = if values
            .iter()
            .map(|(name, _)| name)
            .eq(canonical.iter().map(|(name, _)| name))
        {
            Expr {
                kind: ExprKind::Construct {
                    enum_id: ty.layout().expect("structural layout"),
                    tag: 0,
                    fields: values.into_iter().map(|(_, value)| value).collect(),
                },
                ty,
                span,
                resource: None,
            }
        } else {
            let mut statements = Vec::with_capacity(values.len());
            let mut by_name = BTreeMap::new();
            for (name, value) in values {
                let field_ty = value.ty;
                let slot = self.temp(field_ty, value.span)?;
                self.locals[slot].linear = self.value_moves_linear(&value);
                statements.push(Statement::Let(slot, value));
                by_name.insert(name, slot);
            }
            let fields = canonical
                .iter()
                .map(|(name, field_ty)| Expr {
                    kind: ExprKind::Local(by_name[name]),
                    ty: *field_ty,
                    span,
                    resource: None,
                })
                .collect();
            let tail = Expr {
                kind: ExprKind::Construct {
                    enum_id: ty.layout().expect("structural layout"),
                    tag: 0,
                    fields,
                },
                ty,
                span,
                resource: None,
            };
            Expr {
                kind: ExprKind::Block(Block {
                    statements,
                    tail: Some(Box::new(tail)),
                    ty,
                }),
                ty,
                span,
                resource: None,
            }
        };
        let type_out = if diverges { Type::Never } else { ty };
        Ok((
            Expr {
                ty: type_out,
                ..construct
            },
            source,
        ))
    }
    fn record_pattern(
        &mut self,
        pattern: &ast::Pattern,
        fields: &[(String, ast::Pattern)],
        ty: Type,
        bindings: &mut BTreeMap<String, (usize, Type)>,
    ) -> Result<Pattern> {
        let id = self
            .resolution
            .reference(pattern.span)
            .filter(|id| self.types.is_record(*id))
            .ok_or_else(|| {
                Diagnostic::new(pattern.span, "expected a record type in this pattern")
            })?;
        let Some(layout) = ty
            .layout()
            .filter(|l| self.types.enums[*l].definition == id)
        else {
            return Err(Diagnostic::new(
                pattern.span,
                format!(
                    "record pattern does not match a value of type {}",
                    self.types.name(ty)
                ),
            ));
        };
        let variant = self.types.enums[layout].variants[0].clone();
        let mut checked = Vec::new();
        let mut offset = 1;
        for (index, field_ty) in variant.fields.iter().enumerate() {
            let sub = fields.iter().find(|(n, _)| *n == variant.names[index]);
            let p = match sub {
                Some((_, p)) => self.pattern(p, *field_ty, bindings)?,
                None => Pattern::Any,
            };
            checked.push((offset, p));
            offset += self.types.width(*field_ty);
        }
        if let Some((name, p)) = fields.iter().find(|(n, _)| !variant.names.contains(n)) {
            return Err(Diagnostic::new(
                p.span,
                format!("record has no field '{name}'"),
            ));
        }
        Ok(Pattern::Variant {
            tag: 0,
            fields: checked,
        })
    }
    /// A catch-all binding is typed by the variants not yet matched.
    fn pattern_refined(
        &mut self,
        pattern: &ast::Pattern,
        ty: Type,
        remaining: u64,
    ) -> Result<Pattern> {
        if let Some(id) = ty.layout()
            && matches!(&pattern.kind, ast::PatternKind::Name(p) if p.len() == 1)
            && !self.is_constructor_pattern(pattern)
            && remaining & self.mask(ty) != 0
        {
            let refined =
                crate::runtime_types::refine(&self.types.enums, id, remaining & self.mask(ty));
            return self.pattern(pattern, refined, &mut BTreeMap::new());
        }
        self.pattern(pattern, ty, &mut BTreeMap::new())
    }
    /// Contextual inline-array construction. A union context selects an
    /// alternative array whose length matches the literal; an exact array
    /// context keeps the declared length so the usual mismatch error is clear.
    fn expected_array(&self, expected: Option<Type>, length: usize) -> Vec<(usize, Type, usize)> {
        let candidates = |expected: Type| -> Vec<(usize, Type, usize)> {
            let Some(id) = expected.layout() else {
                return Vec::new();
            };
            let Some((element, declared)) = self.types.enums[id].array else {
                return Vec::new();
            };
            vec![(id, element, declared)]
        };
        match expected {
            Some(Type::Union(id)) => self.types.unions[id]
                .members
                .iter()
                .copied()
                .filter_map(|member| {
                    let id = member.layout()?;
                    let (element, declared) = self.types.enums[id].array?;
                    (declared == length).then_some((id, element, declared))
                })
                .collect(),
            Some(expected) => candidates(expected),
            None => Vec::new(),
        }
    }
    fn vec_literal(
        &mut self,
        values: &[ast::Expr],
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let candidates = match expected {
            Some(Type::Vec(p)) => vec![self.types.pointees[p]],
            Some(Type::Union(id)) => {
                let mut elements = Vec::new();
                for member in self.types.unions[id].members.iter() {
                    if let Type::Vec(p) = member
                        && !elements.contains(&self.types.pointees[*p])
                    {
                        elements.push(self.types.pointees[*p]);
                    }
                }
                elements
            }
            _ => Vec::new(),
        };
        if values.len() > 4096 {
            return Err(Diagnostic::new(
                span,
                "vector literals are limited to 4096 elements",
            ));
        }
        self.require(ALLOC | PANIC, span)?;
        let mut element = match candidates.len() {
            0 => None,
            1 => Some(candidates[0]),
            _ => {
                // Accumulate element constraints over every union
                // alternative; the literal must identify exactly one.
                let mut accepted = Vec::new();
                let mut first_error = None;
                for candidate in &candidates {
                    let mut checked = Vec::with_capacity(values.len());
                    let mut failed = None;
                    for value in values {
                        match self.expr_expected(value, Some(*candidate)) {
                            Ok(value) => checked.push(value),
                            Err(error) => {
                                failed = Some(error);
                                break;
                            }
                        }
                    }
                    if failed.is_none() {
                        accepted.push((*candidate, checked));
                    } else if first_error.is_none() {
                        first_error = failed;
                    }
                }
                let (element, checked) = match accepted.len() {
                    1 => accepted.pop().expect("one accepted vector element"),
                    0 => {
                        return Err(first_error
                            .expect("a vector literal candidate always attempts one element"));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            span,
                            "this vector literal fits several union alternatives; annotate the element type or write Vec::<T>::new",
                        ));
                    }
                };
                let ty = Type::Vec(self.types.pointer(element));
                let mut current = Expr {
                    kind: ExprKind::Call(
                        Target::Vec(VecOp::WithCapacity, element),
                        vec![Expr {
                            kind: ExprKind::Constant(values.len() as i64),
                            ty: Type::I64,
                            span,
                            resource: None,
                        }],
                    ),
                    ty,
                    span,
                    resource: None,
                };
                for value in checked {
                    self.expect(value.ty, element, value.span)?;
                    let diverges = value.ty == Type::Never;
                    current = Expr {
                        kind: ExprKind::Call(
                            Target::Vec(VecOp::Push, element),
                            vec![current, value],
                        ),
                        ty: if diverges { Type::Never } else { ty },
                        span,
                        resource: None,
                    };
                }
                return match expected {
                    Some(expected) => self.coerce(current, expected, span),
                    None => Ok(current),
                };
            }
        };
        let mut checked = Vec::new();
        for value in values {
            let value = self.expr_expected(value, element)?;
            if element.is_none() && value.ty != Type::Never {
                element = Some(self.types.full(value.ty, span)?);
            }
            checked.push(value);
        }
        let Some(element) = element else {
            return Err(Diagnostic::new(
                span,
                "cannot infer the element type of an empty vector; annotate it: let v: Vec<T> = [];",
            ));
        };
        if matches!(element, Type::RefMut(_) | Type::Never)
            || matches!(element, Type::Annotated(_, _) if matches!(self.unannotate(element), Type::RefMut(_)))
            || element.is_view()
        {
            return Err(Diagnostic::new(
                span,
                "vectors cannot store exclusive references, slice views, or text views; a vector read copies its element, so an exclusive reference element is not admitted",
            ));
        }
        let ty = Type::Vec(self.types.pointer(element));
        let mut current = Expr {
            kind: ExprKind::Call(
                Target::Vec(VecOp::WithCapacity, element),
                vec![Expr {
                    kind: ExprKind::Constant(values.len() as i64),
                    ty: Type::I64,
                    span,
                    resource: None,
                }],
            ),
            ty,
            span,
            resource: None,
        };
        for value in checked {
            self.expect(value.ty, element, value.span)?;
            let diverges = value.ty == Type::Never;
            current = Expr {
                kind: ExprKind::Call(Target::Vec(VecOp::Push, element), vec![current, value]),
                ty: if diverges { Type::Never } else { ty },
                span,
                resource: None,
            };
        }
        match expected {
            Some(expected) => self.coerce(current, expected, span),
            None => Ok(current),
        }
    }
    /// A compile-time nonnegative index in a range endpoint, when it is one.
    /// This reuses the same checked natural evaluator as array indices, so
    /// const parameters and admitted total logical computations are folded and
    /// negative or overflowing constants are rejected.
    fn constant_bound(&self, expr: &ast::Expr) -> Option<Result<usize>> {
        match crate::length::eval_expr(self.resolution, self.logical, &self.consts, expr) {
            Ok(Some(value)) => Some(Ok(value)),
            Ok(None) => None,
            Err(error) => Some(Err(error)),
        }
    }
    /// Build a slice view over a local owner or another slice view.
    fn slice_view(
        &mut self,
        value: &ast::Expr,
        start: Option<&ast::Expr>,
        end: Option<&ast::Expr>,
        mutable: bool,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let (base, element, static_length) = if let ast::ExprKind::Slice {
            value: inner,
            start: inner_start,
            end: inner_end,
        } = &value.kind
        {
            let base = self.slice_view(
                inner,
                inner_start.as_deref(),
                inner_end.as_deref(),
                mutable,
                value.span,
                None,
            )?;
            if base.ty == Type::Str {
                if mutable {
                    return Err(Diagnostic::new(
                        value.span,
                        "mutable borrowed text '&mut str' is not supported; text views are immutable",
                    ));
                }
                return self.text_view_from_expr(base, start, end, span, expected);
            }
            let Some(pointer) = base.ty.slice_element() else {
                unreachable!("slice construction has slice type")
            };
            (base, self.types.pointees[pointer], None)
        } else if matches!(value.kind, ast::ExprKind::Field { .. }) {
            // A nested record-field borrow: `outer.inner.view[..]`. The root is
            // still a direct local owner; the projection is checked by the
            // ownership pass, which keeps the field path and its owner loaned.
            let old_place = self.field_place;
            self.field_place = true;
            let checked = self.expr(value);
            self.field_place = old_place;
            let base = checked?;
            let Some(pointer) = base.ty.slice_element() else {
                return Err(Diagnostic::new(
                    value.span,
                    format!(
                        "only a borrowed slice field can be sub-sliced through a record projection, found {}",
                        self.types.name(base.ty)
                    ),
                ));
            };
            if mutable && !base.ty.is_mut_slice() {
                return Err(Diagnostic::new(
                    value.span,
                    "cannot create an exclusive '&mut [T]' view from a shared record field; shared storage cannot be upgraded",
                ));
            }
            (base, self.types.pointees[pointer], None)
        } else {
            let slot = self.slot(value.span).map_err(|_| {
                Diagnostic::new(
                    value.span,
                    "a slice or text view must borrow a local array, Vec, Bytes, String, view, or record field; bind the owner to a local first",
                )
            })?;
            let ty = self.locals[slot].ty;
            if ty == Type::Str {
                if mutable {
                    return Err(Diagnostic::new(
                        value.span,
                        "mutable borrowed text '&mut str' is not supported; text views are immutable",
                    ));
                }
                let base = Expr {
                    kind: ExprKind::Local(slot),
                    ty: Type::Str,
                    span: value.span,
                    resource: None,
                };
                return self.text_view_from_expr(base, start, end, span, expected);
            }
            if mutable && !self.locals[slot].mutable && !ty.is_slice() {
                return Err(Diagnostic::new(
                    value.span,
                    "cannot create an exclusive '&mut [T]' view of an immutable binding; declare the owner with 'let mut'",
                )
                .with_note(self.locals[slot].span, "owner declared here"));
            }
            if let Some((element, length)) = ty.layout().and_then(|id| self.types.enums[id].array) {
                (
                    Expr {
                        kind: ExprKind::Peek(slot),
                        ty,
                        span: value.span,
                        resource: None,
                    },
                    element,
                    Some(length),
                )
            } else if let Type::Vec(pointer) = ty {
                let element = self.types.pointees[pointer];
                let owner = self.types.pointer(ty);
                (
                    Expr {
                        kind: ExprKind::Borrow(slot),
                        ty: Type::Ref(owner),
                        span: value.span,
                        resource: None,
                    },
                    element,
                    None,
                )
            } else if ty == Type::Bytes {
                (
                    Expr {
                        kind: ExprKind::Borrow(slot),
                        ty: Type::Ref(self.types.pointer(Type::Bytes)),
                        span: value.span,
                        resource: None,
                    },
                    Type::I64,
                    None,
                )
            } else if ty == Type::String {
                return Err(Diagnostic::new(
                    value.span,
                    "String does not support byte slicing; use String.byte_at or String.scalar_at, convert explicitly with String.as_bytes, or borrow text with String.as_str / String.substr",
                ));
            } else if let Type::SliceMut(pointer) = ty {
                // A mutable view may be narrowed to a shared or exclusive
                // child. Ownership checking records the parent capability and
                // rejects shared-to-mutable upgrades.
                (
                    Expr {
                        kind: ExprKind::Local(slot),
                        ty,
                        span: value.span,
                        resource: None,
                    },
                    self.types.pointees[pointer],
                    None,
                )
            } else if let Type::Slice(pointer) = ty {
                if mutable {
                    return Err(Diagnostic::new(
                        value.span,
                        "a shared '&[T]' view cannot be upgraded to an exclusive '&mut [T]' view",
                    ));
                }
                (
                    Expr {
                        kind: ExprKind::Local(slot),
                        ty,
                        span: value.span,
                        resource: None,
                    },
                    self.types.pointees[pointer],
                    None,
                )
            } else {
                return Err(Diagnostic::new(
                    value.span,
                    format!(
                        "cannot slice {}; bind an inline array, Vec<T>, Bytes, or &[T] view to a local first",
                        self.types.name(ty)
                    ),
                ));
            }
        };
        if self.owned_type(element) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot form a slice view over owning or linear elements ({}); element reads would copy an owner",
                    self.types.name(element)
                ),
            ));
        }
        let mut checked = false;
        let mut start_constant = None;
        let mut end_constant = None;
        if let Some(length) = static_length {
            let start_value = match start {
                Some(start) => self.constant_bound(start).transpose()?,
                None => Some(0),
            };
            let end_value = match end {
                Some(end) => self.constant_bound(end).transpose()?,
                None => Some(length),
            };
            if let (Some(start_value), Some(end_value)) = (start_value, end_value) {
                if start_value > end_value || end_value > length {
                    return Err(Diagnostic::new(
                        span,
                        format!("slice range is out of bounds for an array of length {length}"),
                    ));
                }
            } else {
                checked = true;
            }
            start_constant = start_value;
            end_constant = end_value;
        } else {
            checked = start.is_some() || end.is_some();
        }
        if checked {
            self.require(PANIC, span)?;
        }
        let number = |value: usize, span: Span| -> Result<Expr> {
            let value = i64::try_from(value).map_err(|_| {
                Diagnostic::new(span, "slice bound is too large for a runtime i64 index")
            })?;
            Ok(Expr {
                kind: ExprKind::Constant(value),
                ty: Type::I64,
                span,
                resource: None,
            })
        };
        let start = match (start, start_constant) {
            (Some(start), Some(value)) => Some(number(value, start.span)?),
            (Some(start), None) => Some(self.expr_expected(start, Some(Type::I64))?),
            (None, _) => None,
        };
        let end = match (end, end_constant) {
            (Some(end), Some(value)) => Some(number(value, end.span)?),
            (Some(end), None) => Some(self.expr_expected(end, Some(Type::I64))?),
            (None, Some(value)) => Some(number(value, span)?),
            (None, None) => None,
        };
        if let Some(start) = &start {
            self.expect(start.ty, Type::I64, start.span)?;
        }
        if let Some(end) = &end {
            self.expect(end.ty, Type::I64, end.span)?;
        }
        self.slice_from_expr(base, start, end, element, checked, mutable, span, expected)
    }
    #[allow(clippy::too_many_arguments)]
    fn slice_from_expr(
        &mut self,
        base: Expr,
        start: Option<Expr>,
        end: Option<Expr>,
        element: Type,
        check: bool,
        mutable: bool,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        if check {
            self.require(PANIC, span)?;
        }
        let pointer = self.types.pointer(element);
        let ty = if mutable {
            Type::SliceMut(pointer)
        } else {
            Type::Slice(pointer)
        };
        let value = Expr {
            kind: ExprKind::Slice {
                base: Box::new(base),
                start: start.map(Box::new),
                end: end.map(Box::new),
                element,
                check,
                split: None,
                text: false,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Build a checked borrowed text view over `base`, which must be a
    /// `&String` borrow or another `&str` view. Any supplied bound adds a
    /// runtime `0 <= start <= end <= byte length` check plus UTF-8 scalar
    /// boundary checks at both endpoints; these are enforced in both backends.
    fn text_view_from_expr(
        &mut self,
        base: Expr,
        start: Option<&ast::Expr>,
        end: Option<&ast::Expr>,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let check = start.is_some() || end.is_some();
        if check {
            self.require(PANIC, span)?;
        }
        let start = match start {
            Some(start) => {
                let value = self.expr_expected(start, Some(Type::I64))?;
                self.expect(value.ty, Type::I64, value.span)?;
                Some(value)
            }
            None => None,
        };
        let end = match end {
            Some(end) => {
                let value = self.expr_expected(end, Some(Type::I64))?;
                self.expect(value.ty, Type::I64, value.span)?;
                Some(value)
            }
            None => None,
        };
        let value = Expr {
            kind: ExprKind::Slice {
                base: Box::new(base),
                start: start.map(Box::new),
                end: end.map(Box::new),
                element: Type::I64,
                check,
                split: None,
                text: true,
            },
            ty: Type::Str,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    fn slice_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if explicit.is_some() {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        let expected_arguments = match name {
            "Slice.len" => 1,
            "Slice.get" => 2,
            "Slice.try_get" => 2,
            "Slice.set" => 3,
            "Slice.split_at_mut" => 2,
            _ => 3,
        };
        if arguments.len() != expected_arguments {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {expected_arguments} arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        if name == "Slice.split_at_mut" {
            return Err(Diagnostic::new(
                span,
                "Slice.split_at_mut produces a restricted nonescaping borrow pair; use it directly as let (left, right) = Slice.split_at_mut(view, mid);",
            ));
        }
        let first = self.expr(&arguments[0])?;
        self.slice_call_with(name, first, &arguments[1..], expected, span)
    }
    /// Slice builtin with an already checked receiver (function call or method
    /// syntax). The receiver is evaluated exactly once, before `rest`.
    fn slice_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = match name {
            "Slice.len" => 0,
            "Slice.get" | "Slice.try_get" => 1,
            "Slice.set" => 2,
            _ => 2,
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {} argument(s) after its receiver, found {}",
                    wanted,
                    rest.len()
                ),
            ));
        }
        let Some(pointer) = first.ty.slice_element() else {
            if first.ty == Type::Never {
                return Ok(first);
            }
            return Err(Diagnostic::new(
                first.span,
                format!(
                    "{name} expects a &[T] or &mut [T] slice view, found {}",
                    self.types.name(first.ty)
                ),
            ));
        };
        let mutable_view = first.ty == Type::SliceMut(pointer);
        if name == "Slice.set" && !mutable_view {
            return Err(Diagnostic::new(
                first.span,
                "Slice.set requires an exclusive mutable view '&mut [T]'; a shared '&[T]' view cannot be written",
            ));
        }
        let element = self.types.pointees[pointer];
        if self.owned_type(element) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} copies the element, but {} owns resources or is linear",
                    self.types.name(element)
                ),
            ));
        }
        if name == "Slice.len" {
            let ty = Type::I64;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(Expr {
                kind: ExprKind::Call(Target::Slice(SliceOp::Len, element), vec![first]),
                ty,
                span,
                resource: None,
            });
        }
        let index = self.expr_expected(&rest[0], Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        if name == "Slice.try_get" {
            if self.owned_type(element) || self.linear_type(element) {
                return Err(Diagnostic::new(
                    span,
                    "Slice.try_get can only copy elements; owning or linear elements cannot be returned by value from a slice view",
                ));
            }
            // The result is the conventional Option<T> shape, so a user
            // declaration may name its variants in either order.
            let option = self
                .resolution
                .slice_options
                .get(&(span.start, span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(span, "Slice.try_get requires Option<T> in scope")
                })?;
            let shape = self.types.option(option, element, span)?;
            let ty = shape.result;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            let op = SliceOp::TryGet {
                some_tag: shape.some_tag,
                none_tag: shape.none_tag,
                option: shape
                    .result
                    .layout()
                    .expect("the conventional Option is an enum layout"),
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Slice(op, element), vec![first, index]),
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if name == "Slice.set" {
            let value = self.expr_expected(&rest[1], Some(element))?;
            self.expect(value.ty, element, value.span)?;
            if self.owned_type(value.ty) || self.linear_type(value.ty) {
                return Err(Diagnostic::new(
                    value.span,
                    "Slice.set can only store copyable elements; moving an owner into a slice view is not supported",
                ));
            }
            self.require(PANIC, span)?;
            let values = vec![first, index, value];
            return Ok(Expr {
                kind: ExprKind::Call(Target::Slice(SliceOp::Set, element), values),
                ty: Type::Unit,
                span,
                resource: None,
            });
        }
        let values = vec![first, index];
        if name == "Slice.get" {
            self.require(PANIC, span)?;
        } else {
            use crate::facts::{ParamTerm, Proposition};
            let proposition = Proposition {
                atoms: vec![
                    (ParamTerm::Zero, 0, Kind::Le, ParamTerm::Param(1), 0),
                    (ParamTerm::Param(1), 0, Kind::Lt, ParamTerm::Len(0), 0),
                ],
                text: "0 <= index && index < Slice.len(slice)".to_owned(),
            };
            self.discharge(&proposition, &values, &rest[1], span)?;
        }
        let ty = if values.iter().any(|value| value.ty == Type::Never) {
            Type::Never
        } else {
            element
        };
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        let op = if name == "Slice.get" {
            SliceOp::Get
        } else {
            SliceOp::At
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Slice(op, element), values),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Check one lexically scoped, one-shot tail-resumptive handler.
    ///
    /// The handler is an ordinary first-class callable of type
    /// `fn(P, linear once fn(R) -> R) -> R` (or `once`/`linear once`). It is
    /// evaluated once and stored in a hidden local. `perform` calls it with the
    /// payload and a fresh identity resumption token. The token is linear, so
    /// the handler must invoke it exactly once on every normal path; invoking it
    /// twice is a use-after-move, and returning without invoking it is an
    /// unconsumed linear obligation. There is no captured continuation, so a
    /// second resumption (multishot) is unrepresentable.
    #[allow(clippy::too_many_arguments)]
    fn handle_effect(
        &mut self,
        operation: &str,
        parameter: &ast::Type,
        result: &ast::Type,
        handler: &ast::Expr,
        body: &ast::Block,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let parameter_ty = self.ty(parameter)?;
        let result_ty = self.ty(result)?;
        if matches!(parameter_ty, Type::Never) || matches!(result_ty, Type::Never) {
            return Err(Diagnostic::new(
                span,
                "a handled operation cannot use Never as its payload or result type",
            ));
        }
        let handler_value = self.expr(handler)?;
        let Some((handler_id, _)) = Self::function_parts(handler_value.ty) else {
            return Err(Diagnostic::new(
                handler.span,
                "an effect handler must be a first-class fn/once fn value",
            ));
        };
        let signature = self.types.function_types[handler_id].clone();
        let resume_ty = self.resume_type(result_ty);
        if signature.parameters.len() != 2 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "an effect handler takes the payload and one linear resumption token, found {} parameter(s)",
                    signature.parameters.len()
                ),
            ));
        }
        if signature.parameters[1] != resume_ty {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler's second parameter must be exactly 'linear once fn({}) -> {}'",
                    self.types.name(result_ty),
                    self.types.name(result_ty)
                ),
            ));
        }
        if !self.subtype(parameter_ty, signature.parameters[0]) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler parameter accepts {}, which is not a supertype of the performed payload {}",
                    self.types.name(signature.parameters[0]),
                    self.types.name(parameter_ty)
                ),
            ));
        }
        if !self.subtype(signature.result, result_ty) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "the handler returns {}, which is not a subtype of the operation result {}",
                    self.types.name(signature.result),
                    self.types.name(result_ty)
                ),
            ));
        }
        self.require(signature.effects, span)?;
        let handler_type = handler_value.ty;
        let slot = self.fresh_local(span, handler_type)?;
        self.locals[slot].linear = signature.linear;
        self.handlers.push(HandlerScope {
            operation: operation.to_owned(),
            parameter: parameter_ty,
            result: result_ty,
            slot,
            handler_parameter: signature.parameters[0],
            handler_result: signature.result,
            effects: signature.effects,
        });
        let checked = self.block(body, expected);
        self.handlers.pop();
        let inner = checked?;
        let ty = inner.ty;
        Ok(Expr {
            kind: ExprKind::Block(Block {
                statements: vec![Statement::Let(slot, handler_value)],
                tail: Some(Box::new(Expr {
                    kind: ExprKind::Block(inner),
                    ty,
                    span,
                    resource: None,
                })),
                ty,
            }),
            ty,
            span,
            resource: None,
        })
    }
    /// Intern the resumption callable type `linear once fn(R) -> R`.
    fn resume_type(&mut self, result: Type) -> Type {
        let id = self.types.function_type_with(
            vec![result],
            result,
            0,
            vec![None],
            None,
            true,
            true,
            crate::runtime_types::BorrowSig::default(),
        );
        Type::Once(id)
    }
    /// Build the identity resumption value. The linear contract is enforced by
    /// the ordinary callable ownership rules; no hidden continuation or stack
    /// pointer exists, so a token that is transferred and called normally is
    /// still a one-shot operation result.
    fn resume_value(&mut self, result: Type, span: Span) -> Result<Expr> {
        let ty = self.resume_type(result);
        let Type::Once(id) = ty else {
            unreachable!("resume type is once")
        };
        let signature = self.types.function_types[id].clone();
        let locals = vec![Local {
            ty: result,
            mutable: false,
            linear: false,
            grade: None,
            span,
        }];
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(Expr {
                kind: ExprKind::Local(0),
                ty: result,
                span,
                resource: None,
            })),
            ty: result,
        };
        let function = self.register_adapter(
            "effect resume",
            &signature,
            vec![],
            true,
            locals,
            body,
            span,
        )?;
        Ok(Expr {
            kind: ExprKind::FnValue {
                function,
                captures: vec![],
            },
            ty,
            span,
            resource: None,
        })
    }
    /// Check a direct `perform` against the innermost lexical handler.
    fn perform_effect(
        &mut self,
        operation: &str,
        value: &ast::Expr,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let Some(scope) = self
            .handlers
            .iter()
            .rev()
            .find(|scope| scope.operation == operation)
        else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "perform '{operation}' has no lexically enclosing handler; handlers cover direct performs in the same function body only"
                ),
            ));
        };
        let (parameter, result, slot, handler_parameter, handler_result, effects) = (
            scope.parameter,
            scope.result,
            scope.slot,
            scope.handler_parameter,
            scope.handler_result,
            scope.effects,
        );
        let handler_ty = self.locals[slot].ty;
        self.require(effects, span)?;
        let payload = self.expr_expected(value, Some(parameter))?;
        let payload = self.coerce(payload, handler_parameter, span)?;
        let resume = self.resume_value(result, span)?;
        let call = Expr {
            kind: ExprKind::CallIndirect {
                callee: Box::new(Expr {
                    kind: ExprKind::Local(slot),
                    ty: handler_ty,
                    span,
                    resource: None,
                }),
                arguments: vec![payload, resume],
            },
            ty: handler_result,
            span,
            resource: None,
        };
        let call = self.coerce(call, result, span)?;
        match expected {
            Some(expected) => self.coerce(call, expected, span),
            None => Ok(call),
        }
    }
    /// Runtime-sized inline array constructors and reads. The capacity is a
    /// compile-time bound; only the length is dynamic. `DynArray.new` and
    /// `DynArray.push` preserve the inline representation (no heap allocation),
    /// while `DynArray.len`/`DynArray.get` borrow the value for the call, so a
    /// view into the dynamic stack storage cannot escape its lexical owner.
    fn dyn_array_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let from_expected = expected.and_then(|ty| {
            ty.layout()
                .and_then(|id| self.types.enums[id].dynamic_array)
        });
        let explicit_layout = match explicit {
            Some([element_ty, capacity_ty]) => {
                let element = self.ty(element_ty)?;
                let element = self.types.full(element, span)?;
                let capacity = crate::length::eval_type(
                    self.resolution,
                    self.logical,
                    &self.consts,
                    capacity_ty,
                )?;
                Some((element, capacity))
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    "DynArray expects two arguments: an element type and a compile-time capacity",
                ));
            }
            None => None,
        };
        match name {
            "DynArray.new" => {
                let (element, capacity) = explicit_layout.or(from_expected).ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        "cannot infer the DynArray element type and capacity; annotate the binding or write DynArray.new::<T, capacity>()",
                    )
                })?;
                let ty = self.types.dynamic_array(element, capacity, span)?;
                if !arguments.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.new takes no value arguments; push elements with DynArray.push",
                    ));
                }
                let value = Expr {
                    kind: ExprKind::DynArrayNew { element, capacity },
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "DynArray.push" => {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.push infers its element type from the array argument",
                    ));
                }
                if arguments.len() != 2 {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.push takes the array and one element",
                    ));
                }
                let array = if let Some(expected) = expected {
                    self.expr_expected(&arguments[0], Some(expected))?
                } else {
                    self.expr(&arguments[0])?
                };
                let Some((element, capacity)) = array
                    .ty
                    .layout()
                    .and_then(|id| self.types.enums[id].dynamic_array)
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        "DynArray.push requires a runtime-sized inline array",
                    ));
                };
                let ty = array.ty;
                let value = self.expr_expected(&arguments[1], Some(element))?;
                self.expect(value.ty, element, arguments[1].span)?;
                self.require(PANIC, span)?;
                let value = Expr {
                    kind: ExprKind::DynArrayPush {
                        array: Box::new(array),
                        value: Box::new(value),
                        element,
                        capacity,
                    },
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "DynArray.set" | "DynArray.pop" => {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes no type arguments"),
                    ));
                }
                let wanted = if name == "DynArray.set" { 3 } else { 1 };
                if arguments.len() != wanted {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes {wanted} argument(s)"),
                    ));
                }
                let array = if let Some(expected) = expected {
                    // `pop` returns a tuple, so its array position cannot use
                    // the whole expected type as a hint; only `set` can.
                    if name == "DynArray.set" {
                        self.expr_expected(&arguments[0], Some(expected))?
                    } else {
                        self.expr(&arguments[0])?
                    }
                } else {
                    self.expr(&arguments[0])?
                };
                let Some((element, capacity)) = array
                    .ty
                    .layout()
                    .and_then(|id| self.types.enums[id].dynamic_array)
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!("{name} requires a runtime-sized inline array"),
                    ));
                };
                if self.owned_type(element) || self.linear_type(element) || element.is_view() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "{name} moves or copies its element; owning, linear, and view elements need an explicit consuming operation"
                        ),
                    ));
                }
                if name == "DynArray.set" {
                    let index = self.expr_expected(&arguments[1], Some(Type::I64))?;
                    self.expect(index.ty, Type::I64, arguments[1].span)?;
                    let value = self.expr_expected(&arguments[2], Some(element))?;
                    self.expect(value.ty, element, arguments[2].span)?;
                    self.require(PANIC, span)?;
                    let ty = array.ty;
                    let value = Expr {
                        kind: ExprKind::DynArraySet {
                            array: Box::new(array),
                            index: Box::new(index),
                            value: Box::new(value),
                            element,
                            capacity,
                        },
                        ty,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => self.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                self.require(PANIC, span)?;
                let ty = self.types.tuple(vec![array.ty, element], span)?;
                let value = Expr {
                    kind: ExprKind::DynArrayPop {
                        array: Box::new(array),
                        element,
                        capacity,
                    },
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "DynArray.len" | "DynArray.get" => {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes no type arguments"),
                    ));
                }
                let wanted = if name == "DynArray.get" { 2 } else { 1 };
                if arguments.len() != wanted {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes {wanted} argument(s)"),
                    ));
                }
                let array = self.expr(&arguments[0])?;
                let Some(pointer) = array.ty.ref_pointee() else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!("{name} requires a '&DynArray<T, capacity>' borrow"),
                    ));
                };
                let ty = self.types.pointees[pointer];
                let Some((element, _capacity)) = ty
                    .layout()
                    .and_then(|id| self.types.enums[id].dynamic_array)
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!("{name} requires a borrow of a runtime-sized inline array"),
                    ));
                };
                if name == "DynArray.len" {
                    let value = Expr {
                        kind: ExprKind::Call(
                            Target::DynArray(DynArrayOp::Len, element),
                            vec![array],
                        ),
                        ty: Type::I64,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => self.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                if self.owned_type(element) || self.linear_type(element) || element.is_view() {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.get copies its element; owning, linear, and view elements need an explicit consuming operation",
                    ));
                }
                self.require(PANIC, span)?;
                let index = self.expr_expected(&arguments[1], Some(Type::I64))?;
                self.expect(index.ty, Type::I64, arguments[1].span)?;
                let value = Expr {
                    kind: ExprKind::Call(
                        Target::DynArray(DynArrayOp::Get, element),
                        vec![array, index],
                    ),
                    ty: element,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            _ => Err(Diagnostic::new(
                span,
                format!("unsupported DynArray operation '{name}'"),
            )),
        }
    }
    fn vec_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let arity = match name {
            "Vec.new" => 0,
            "Vec.with_capacity" | "Vec.len" | "Vec.pop" | "Vec.clear" => 1,
            "Vec.get" | "Vec.push" | "Vec.map_in_place" | "Vec.reserve" | "Vec.try_reserve" => 2,
            "Vec.map_chain_in_place" => 3,
            _ => 3,
        };
        if arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        if name == "Vec.pop" {
            return Err(Diagnostic::new(
                span,
                "Vec.pop is not available yet; read with Vec.get/Vec.at and rebuild",
            ));
        }
        if explicit.is_some()
            && !matches!(
                name,
                "Vec.new" | "Vec.with_capacity" | "Vec.map_in_place" | "Vec.map_chain_in_place"
            )
        {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        if name == "Vec.map_in_place" {
            return self.vec_map_call(explicit, arguments, expected, span);
        }
        if name == "Vec.map_chain_in_place" {
            return self.vec_map_chain_call(explicit, arguments, expected, span);
        }
        if matches!(name, "Vec.new" | "Vec.with_capacity") {
            let element = match (explicit, expected) {
                (Some([t]), _) => {
                    let ty = self.ty(t)?;
                    self.types.full(ty, span)?
                }
                (Some(_), _) => return Err(Diagnostic::new(span, "Vec expects one element type")),
                (None, Some(Type::Vec(p))) => self.types.pointees[p],
                (None, Some(Type::Union(id))) => {
                    let mut elements = Vec::new();
                    for member in self.types.unions[id].members.iter() {
                        if let Type::Vec(p) = member
                            && !elements.contains(&self.types.pointees[*p])
                        {
                            elements.push(self.types.pointees[*p]);
                        }
                    }
                    match elements.as_slice() {
                        [element] => *element,
                        [] => {
                            return Err(Diagnostic::new(
                                span,
                                "the expected union has no Vec<T> alternative for this constructor",
                            ));
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                span,
                                "this empty vector constructor fits several union alternatives; write the element type explicitly as Vec.new::<T>()",
                            ));
                        }
                    }
                }
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer the element type; annotate the binding (let v: Vec<T> = {name}(...)) or write {name}::<T>(...)"
                        ),
                    ));
                }
            };
            if matches!(element, Type::RefMut(_) | Type::Never)
                || matches!(element, Type::Annotated(_, _) if matches!(self.unannotate(element), Type::RefMut(_)))
                || element.is_view()
            {
                return Err(Diagnostic::new(
                    span,
                    "vectors cannot store exclusive references, slice views, or text views; a vector read copies its element, so an exclusive reference element is not admitted",
                ));
            }
            if crate::runtime_types::contains_task(self.types, element) {
                return Err(Diagnostic::new(
                    span,
                    "task handles cannot be stored in Vec; join them in the scope that owns them",
                ));
            }
            self.require(ALLOC | PANIC, span)?;
            let capacity = if name == "Vec.new" {
                unit(ExprKind::Constant(0), Type::I64)
            } else {
                let c = self.expr_expected(&arguments[0], Some(Type::I64))?;
                self.expect(c.ty, Type::I64, c.span)?;
                c
            };
            let ty = if capacity.ty == Type::Never {
                Type::Never
            } else {
                Type::Vec(self.types.pointer(element))
            };
            let value = unit(
                ExprKind::Call(Target::Vec(VecOp::WithCapacity, element), vec![capacity]),
                ty,
            );
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let first = self.expr(&arguments[0])?;
        self.vec_call_with(name, first, &arguments[1..], expected, span)
    }
    /// Vector/Bytes `.at` builtin with an already checked receiver. The
    /// receiver is evaluated exactly once, before `rest`.
    fn vec_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let arity = match name {
            "Vec.len" | "Vec.clear" => 0,
            "Vec.get" | "Vec.push" | "Vec.reserve" | "Vec.try_reserve" => 1,
            _ => 2,
        };
        if rest.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        let buffer = match (name, first.ty) {
            ("Bytes.at", Type::Ref(p)) if self.types.pointees[p] == Type::Bytes => Type::Bytes,
            ("Vec.len" | "Vec.get" | "Vec.at", Type::Ref(p))
                if matches!(self.types.pointees[p], Type::Vec(_)) =>
            {
                self.types.pointees[p]
            }
            (
                "Vec.push" | "Vec.set" | "Vec.clear" | "Vec.reserve" | "Vec.try_reserve",
                Type::Vec(_),
            ) => first.ty,
            (_, Type::Never) => return Ok(first),
            _ => {
                let wanted = match name {
                    "Bytes.at" => "&Bytes",
                    "Vec.push" | "Vec.set" | "Vec.clear" | "Vec.reserve" | "Vec.try_reserve" => {
                        "an owned Vec<T> (it is consumed and returned)"
                    }
                    _ => "&Vec<T>",
                };
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "{name} expects {wanted}, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
        };
        let element = match buffer {
            Type::Vec(p) => self.types.pointees[p],
            _ => Type::I64,
        };
        let mut values = vec![first];
        let index_position = matches!(name, "Vec.get" | "Vec.at" | "Vec.set" | "Bytes.at");
        if index_position {
            let index = self.expr_expected(&rest[0], Some(Type::I64))?;
            self.expect(index.ty, Type::I64, index.span)?;
            values.push(index);
        }
        if matches!(name, "Vec.push" | "Vec.set") {
            let value = self.expr_expected(&rest[arity - 1], Some(element))?;
            self.expect(value.ty, element, value.span)?;
            if crate::runtime_types::contains_task(self.types, value.ty) {
                return Err(Diagnostic::new(
                    value.span,
                    "task handles cannot be stored in Vec; join them in the scope that owns them",
                ));
            }
            values.push(value);
        }
        if matches!(name, "Vec.reserve" | "Vec.try_reserve") {
            let additional = self.expr_expected(&rest[0], Some(Type::I64))?;
            self.expect(additional.ty, Type::I64, additional.span)?;
            values.push(additional);
        }
        if matches!(name, "Vec.get" | "Vec.at") && self.owned_type(element) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} copies the element, but {} owns resources",
                    self.types.name(element)
                ),
            ));
        }
        let (op, effects, ty) = match name {
            "Vec.len" => (VecOp::Len, 0, Type::I64),
            "Vec.clear" => (VecOp::Clear, 0, buffer),
            "Vec.reserve" => (VecOp::Reserve, ALLOC | PANIC, buffer),
            "Vec.try_reserve" => {
                let (result, shape) = self.types.result_type(buffer, buffer, span)?;
                (
                    VecOp::TryReserve {
                        ok_tag: shape.ok_tag,
                        err_tag: shape.err_tag,
                    },
                    ALLOC,
                    result,
                )
            }
            "Vec.get" => (VecOp::Get, PANIC, self.unannotate(element)),
            "Vec.at" | "Bytes.at" => (VecOp::At, 0, self.unannotate(element)),
            "Vec.push" => (VecOp::Push, ALLOC | PANIC, buffer),
            _ => (VecOp::Set, PANIC, buffer),
        };
        self.require(effects, span)?;
        if values.iter().any(|v| v.ty == Type::Never) {
            return Ok(unit(
                ExprKind::Call(Target::Vec(op, element), values),
                Type::Never,
            ));
        }
        if op == VecOp::At {
            use crate::facts::{ParamTerm, Proposition};
            let proposition = Proposition {
                atoms: vec![
                    (ParamTerm::Zero, 0, Kind::Le, ParamTerm::Param(1), 0),
                    (ParamTerm::Param(1), 0, Kind::Lt, ParamTerm::Len(0), 0),
                ],
                text: format!(
                    "0 <= index && index < {}.len(buffer)",
                    if buffer == Type::Bytes {
                        "Bytes"
                    } else {
                        "Vec"
                    }
                ),
            };
            self.discharge(&proposition, &values, &rest[1], span)?;
        }
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        if name == "Bytes.at" {
            let index = values.pop().unwrap();
            let bytes = values.pop().unwrap();
            let value = unit(
                ExprKind::BytesAt(Box::new(bytes), Box::new(index)),
                Type::I64,
            );
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let value = unit(ExprKind::Call(Target::Vec(op, element), values), ty);
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Check an allocation-preserving `Vec.map_in_place(values, f)`.
    ///
    /// The callback must be a copyable `fn(T) -> U ! {e}`. Its effects are
    /// required by the enclosing function, so a `noalloc` function rejects an
    /// allocating callback independently of any optimization. `once` and
    /// linear-once callbacks are rejected because the transform would duplicate
    /// the callable across elements. The result layout must be no wider than
    /// the source element layout, because the vector allocation is preserved.
    fn vec_map_call(
        &mut self,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let vector = self.expr(&arguments[0])?;
        let Type::Vec(index) = vector.ty else {
            if vector.ty == Type::Never {
                let _ = self.expr(&arguments[1])?;
                return Ok(vector);
            }
            return Err(Diagnostic::new(
                vector.span,
                format!(
                    "Vec.map_in_place consumes an owned Vec<T>; found {} (borrows and slice views cannot be transformed in place)",
                    self.types.name(vector.ty)
                ),
            ));
        };
        let source = self.types.pointees[index];
        if crate::runtime_types::has_borrow(self.types, source) {
            return Err(Diagnostic::new(
                span,
                "Vec.map_in_place cannot transform a vector of borrowed reference elements; the in-place callback would repack or copy a loan descriptor",
            ));
        }
        if self.linear_type(source) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "vectors cannot hold linear values; in-place transformation cannot consume {}",
                    self.types.name(source)
                ),
            ));
        }
        let callback = self.expr(&arguments[1])?;
        if callback.ty == Type::Never {
            // Unreachable, but keep the callback in the IR so evaluation order
            // and any pending-owner cleanup remain explicit.
            let target = match explicit {
                Some([ty]) => self.ty(ty)?,
                Some(_) => {
                    return Err(Diagnostic::new(
                        span,
                        "Vec.map_in_place accepts at most one result element type",
                    ));
                }
                None => source,
            };
            return Ok(Expr {
                kind: ExprKind::VecMap {
                    vector: Box::new(vector),
                    callbacks: vec![callback],
                    source,
                    target,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Fn(callback_id) = callback.ty else {
            if matches!(callback.ty, Type::Once(_)) {
                return Err(Diagnostic::new(
                    callback.span,
                    "Vec.map_in_place calls its callback once per element; a once or linear-once callback cannot be duplicated. Use a noncapturing fn value",
                ));
            }
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place expects a noncapturing fn(T) -> U value, found {}",
                    self.types.name(callback.ty)
                ),
            ));
        };
        let signature = self.types.function_types[callback_id].clone();
        if signature.parameters.len() != 1 {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place expects a one-argument callback, found {} parameters",
                    signature.parameters.len()
                ),
            ));
        }
        let parameter = signature.parameters[0];
        if signature.parameter_erased(0) {
            return Err(Diagnostic::new(
                callback.span,
                "Vec.map_in_place cannot use a callback whose element parameter is graded @[0]; the transform still passes each element to the callback",
            ));
        }
        if signature.result_erased() {
            return Err(Diagnostic::new(
                callback.span,
                "Vec.map_in_place cannot use a callback whose result is graded @[0]; the transform stores each returned element",
            ));
        }
        if !self.subtype(source, parameter) || !self.same_layout(source, parameter) {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place callback parameter {} must accept the vector element {} with the same runtime layout",
                    self.types.name(parameter),
                    self.types.name(source)
                ),
            ));
        }
        self.require(signature.effects, span)?;
        let target = match explicit {
            Some([ty]) => {
                let target = self.ty(ty)?;
                self.types.full(target, span)?
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    "Vec.map_in_place accepts at most one result element type",
                ));
            }
            None => match expected {
                Some(Type::Vec(p)) => self.types.pointees[p],
                _ => signature.result,
            },
        };
        if !self.subtype(signature.result, target) || !self.same_layout(signature.result, target) {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place callback returns {}, but the result element layout is {}; an in-place transform cannot insert a representation-changing coercion",
                    self.types.name(signature.result),
                    self.types.name(target)
                ),
            ));
        }
        if matches!(target, Type::Ref(_) | Type::RefMut(_) | Type::Never) || target.is_view() {
            return Err(Diagnostic::new(
                span,
                "vector elements must be concrete runtime values, not references, slice views, or Never",
            ));
        }
        if self.linear_type(target) {
            return Err(Diagnostic::new(
                span,
                "Vec.map_in_place cannot store linear result elements in a vector",
            ));
        }
        if crate::runtime_types::contains_task(self.types, target) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Vec; join them in the scope that owns them",
            ));
        }
        let source_width = self.types.width(source);
        let target_width = self.types.width(target);
        if target_width > source_width {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_in_place cannot widen elements from {source_width} to {target_width} word(s) in the preserved allocation; build a new Vec<{}> instead",
                    self.types.name(target)
                ),
            ));
        }
        // Automatic fusion is selected after all bodies are checked, where the
        // analysis can inspect callee effect rows, recursion, and loops. The
        // operation still records the explicit nested map structure here.
        let (vector, mut callbacks, source) = (Box::new(vector), Vec::new(), source);
        callbacks.push(callback);
        let ty = Type::Vec(self.types.pointer(target));
        let value = Expr {
            kind: ExprKind::VecMap {
                vector,
                callbacks,
                source,
                target,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Check the explicit interleaved transform
    /// `Vec.map_chain_in_place(values, f, g)`.
    ///
    /// The order is fixed by the operation: every element sees `f` and then
    /// `g` before the next element starts (`f(0), g(0), f(1), g(1), ...`).
    /// This is not compiler-selected fusion: both callbacks are always kept in
    /// the IR, their effects are required independently, and no nested map or
    /// chain is flattened automatically. Intermediate callback results may use
    /// a wider transient SSA layout than the source element; only the final
    /// element layout has to fit the preserved allocation.
    fn vec_map_chain_call(
        &mut self,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let vector = self.expr(&arguments[0])?;
        if vector.ty == Type::Never {
            // The receiver diverges before either callback is evaluated, but
            // still check both callback expressions for diagnostics and
            // effect demands.
            let _ = self.expr(&arguments[1])?;
            let _ = self.expr(&arguments[2])?;
            return Ok(vector);
        }
        let Type::Vec(index) = vector.ty else {
            return Err(Diagnostic::new(
                vector.span,
                format!(
                    "Vec.map_chain_in_place consumes an owned Vec<T>; found {} (borrows and slice views cannot be transformed in place)",
                    self.types.name(vector.ty)
                ),
            ));
        };
        let source = self.types.pointees[index];
        if crate::runtime_types::has_borrow(self.types, source) {
            return Err(Diagnostic::new(
                span,
                "Vec.map_chain_in_place cannot transform a vector of borrowed reference elements; the in-place chain would repack or copy a loan descriptor",
            ));
        }
        if self.linear_type(source) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "vectors cannot hold linear values; an in-place chain cannot consume {}",
                    self.types.name(source)
                ),
            ));
        }
        // Callback expressions are evaluated exactly once, left to right,
        // before the element loop starts; an empty vector still evaluates both.
        let first = self.expr(&arguments[1])?;
        let second = self.expr(&arguments[2])?;
        let explicit_target = match explicit {
            Some([ty]) => {
                let target = self.ty(ty)?;
                Some(self.types.full(target, span)?)
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    "Vec.map_chain_in_place accepts at most one result element type",
                ));
            }
            None => None,
        };
        let never = |vector: Box<Expr>, callbacks, target: Type| Expr {
            kind: ExprKind::VecMap {
                vector,
                callbacks,
                source,
                target,
            },
            ty: Type::Never,
            span,
            resource: None,
        };
        if first.ty == Type::Never {
            // Evaluating the first callback value diverges, so the second
            // callback expression is unreachable. Keep the first callback in
            // the IR so its evaluation and cleanup are explicit.
            return Ok(never(
                Box::new(vector),
                vec![first],
                explicit_target.unwrap_or(source),
            ));
        }
        if second.ty == Type::Never {
            return Ok(never(
                Box::new(vector),
                vec![first, second],
                explicit_target.unwrap_or(source),
            ));
        }
        let intermediate = self.vec_map_chain_step(&first, source, "first", span)?;
        self.vec_map_chain_payload(intermediate, first.span, "first")?;
        let result = self.vec_map_chain_step(&second, intermediate, "second", span)?;
        self.vec_map_chain_payload(result, second.span, "second")?;
        let target = explicit_target.unwrap_or(match expected {
            Some(Type::Vec(p)) => self.types.pointees[p],
            _ => result,
        });
        if !self.subtype(result, target) || !self.same_layout(result, target) {
            return Err(Diagnostic::new(
                second.span,
                format!(
                    "Vec.map_chain_in_place second callback returns {}, but the final result element layout is {}; an in-place chain cannot insert a representation-changing coercion",
                    self.types.name(result),
                    self.types.name(target)
                ),
            ));
        }
        self.vec_map_chain_payload(target, span, "final")?;
        let source_width = self.types.width(source);
        let target_width = self.types.width(target);
        if target_width > source_width {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_chain_in_place cannot widen elements from {source_width} to {target_width} word(s) in the preserved allocation; build a new Vec<{}> instead",
                    self.types.name(target)
                ),
            ));
        }
        let ty = Type::Vec(self.types.pointer(target));
        let value = Expr {
            kind: ExprKind::VecMap {
                vector: Box::new(vector),
                callbacks: vec![first, second],
                source,
                target,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Check one reusable `fn(T) -> U` step of a chain against its input type.
    fn vec_map_chain_step(
        &mut self,
        callback: &Expr,
        input: Type,
        position: &str,
        span: Span,
    ) -> Result<Type> {
        let Type::Fn(id) = callback.ty else {
            if matches!(callback.ty, Type::Once(_)) {
                return Err(Diagnostic::new(
                    callback.span,
                    "Vec.map_chain_in_place calls each callback once per element; a once or linear-once callback cannot be reused across elements. Use noncapturing fn values",
                ));
            }
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place expects a noncapturing fn(T) -> U value for its {position} callback, found {}",
                    self.types.name(callback.ty)
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        if signature.parameters.len() != 1 {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place {position} callback must take exactly one argument, found {} parameters",
                    signature.parameters.len()
                ),
            ));
        }
        let parameter = signature.parameters[0];
        if signature.parameter_erased(0) || signature.result_erased() {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place {position} callback cannot erase its element parameter or result; every element is observed and every result is stored"
                ),
            ));
        }
        if !self.subtype(input, parameter) || !self.same_layout(input, parameter) {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place {position} callback parameter {} must accept {} with the same runtime layout",
                    self.types.name(parameter),
                    self.types.name(input)
                ),
            ));
        }
        self.require(signature.effects, span)?;
        Ok(signature.result)
    }
    /// Reject payloads a vector slot cannot represent, including transient
    /// chain results. Linear obligations, views, task handles, and `Never`
    /// cannot be moved through an in-place element slot.
    fn vec_map_chain_payload(&self, ty: Type, span: Span, position: &str) -> Result<()> {
        if matches!(ty, Type::Ref(_) | Type::RefMut(_) | Type::Never) || ty.is_view() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_chain_in_place cannot carry the {position} value {}; references, slice views, and Never are not concrete vector payloads",
                    self.types.name(ty)
                ),
            ));
        }
        if self.linear_type(ty) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_chain_in_place cannot store linear {position} elements in a vector"
                ),
            ));
        }
        if crate::runtime_types::contains_task(self.types, ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Vec; join them in the scope that owns them",
            ));
        }
        Ok(())
    }
    /// Facts about locals assigned anywhere in a loop body do not survive
    /// into it: the next iteration may observe the new value.
    fn bump_assigned(&mut self, body: &ast::Block) {
        type Out<'e> = Vec<(Span, &'e ast::Expr)>;
        fn block<'e>(b: &'e ast::Block, out: &mut Out<'e>) {
            for s in &b.statements {
                match s {
                    ast::Statement::Let { value, .. } => expr(value, out),
                    ast::Statement::Expr(e) => expr(e, out),
                }
            }
            if let Some(t) = &b.tail {
                expr(t, out);
            }
        }
        fn expr<'e>(e: &'e ast::Expr, out: &mut Out<'e>) {
            use ast::ExprKind as K;
            match &e.kind {
                K::Binary {
                    op: Kind::Eq,
                    left,
                    right,
                } => {
                    out.push((left.span, right));
                    expr(right, out);
                }
                K::Binary { left, right, .. }
                | K::Index {
                    value: left,
                    index: right,
                } => {
                    expr(left, out);
                    expr(right, out);
                }
                K::Slice { value, start, end } => {
                    expr(value, out);
                    if let Some(start) = start {
                        expr(start, out);
                    }
                    if let Some(end) = end {
                        expr(end, out);
                    }
                }
                K::Unary { operand, .. } | K::Try(operand) | K::Field { value: operand, .. } => {
                    expr(operand, out)
                }
                K::Return(Some(v)) | K::Break(Some(v)) => expr(v, out),
                K::Tuple(vs) | K::Array(vs) => vs.iter().for_each(|v| expr(v, out)),
                K::Call { callee, arguments } => {
                    expr(callee, out);
                    arguments.iter().for_each(|v| expr(v, out));
                }
                K::Specialize { callee, .. } => expr(callee, out),
                K::Block(b) | K::Loop(b) => block(b, out),
                K::While { condition, body } => {
                    expr(condition, out);
                    block(body, out);
                }
                K::If {
                    condition,
                    then,
                    otherwise,
                } => {
                    expr(condition, out);
                    block(then, out);
                    if let Some(o) = otherwise {
                        expr(o, out);
                    }
                }
                K::Match { value, arms } => {
                    expr(value, out);
                    for arm in arms {
                        if let Some(g) = &arm.guard {
                            expr(g, out);
                        }
                        expr(&arm.body, out);
                    }
                }
                K::Record { fields, .. } => fields.iter().for_each(|(_, v)| expr(v, out)),
                _ => {}
            }
        }
        let mut assignments = Vec::new();
        block(body, &mut assignments);
        // Per slot: +1 if every update is `x = x + c` (c >= 0), -1 if every
        // update is `x = x - c` (c >= 0), 0 otherwise.
        let mut direction: BTreeMap<usize, i8> = BTreeMap::new();
        for (span, value) in &assignments {
            let Ok(slot) = self.slot(*span) else { continue };
            let step =
                match &value.kind {
                    ast::ExprKind::Binary {
                        op: op @ (Kind::Plus | Kind::Minus),
                        left,
                        right,
                    } if matches!(&left.kind, ast::ExprKind::Name(_))
                        && self.slot(left.span) == Ok(slot)
                        && matches!(&right.kind, ast::ExprKind::Integer(_)) =>
                    {
                        if *op == Kind::Plus { 1 } else { -1 }
                    }
                    _ => 0,
                };
            direction
                .entry(slot)
                .and_modify(|d| {
                    if *d != step {
                        *d = 0
                    }
                })
                .or_insert(step);
        }
        for (slot, step) in direction {
            if step == 0 {
                self.facts.bump(slot);
            } else {
                self.facts.bump_monotone(slot, step > 0);
            }
        }
    }
    fn pattern(
        &mut self,
        pattern: &ast::Pattern,
        ty: Type,
        bindings: &mut BTreeMap<String, (usize, Type)>,
    ) -> Result<Pattern> {
        self.nested(pattern.span, |c| {
            if let ast::PatternKind::Type { ty: declared, inner } = &pattern.kind {
                let requested = c.ty(declared)?;
                if requested.is_union() {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "a narrowing pattern must name one union alternative, not another union",
                    ));
                }
                let Type::Union(id) = ty else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "type patterns narrow a heterogeneous union; the scrutinee has type {}",
                            c.types.name(ty)
                        ),
                    ));
                };
                let members = c.types.unions[id].members.clone();
                let Some((tag, _member)) = members.iter().enumerate().find(|(_, member)| {
                    c.subtype(**member, requested)
                        && c.narrow_representation_compatible(**member, requested)
                }) else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "{} is not an alternative of {} that can be narrowed without a representation adapter",
                            c.types.name(requested),
                            c.types.name(ty)
                        ),
                    ));
                };
                let inner = c.pattern(inner, requested, bindings)?;
                return Ok(Pattern::Type {
                    tag,
                    member: requested,
                    inner: Box::new(inner),
                });
            }
            if let ast::PatternKind::Structural { fields, rest: _ } = &pattern.kind {
                let record_layout = |c: &Checker, ty: Type| {
                    ty.layout()
                        .filter(|layout| c.types.enums[*layout].record)
                };
                let (member, narrowed) = if let Type::Union(id) = ty {
                    let members = c.types.unions[id].members.clone();
                    let mut matches = Vec::new();
                    for (tag, member) in members.into_iter().enumerate() {
                        let Some(layout) = record_layout(c, member) else {
                            continue;
                        };
                        let variant = &c.types.enums[layout].variants[0];
                        if fields.iter().all(|(name, _)| variant.names.contains(name)) {
                            matches.push((tag, member));
                        }
                    }
                    match matches.as_slice() {
                        [] => {
                            return Err(Diagnostic::new(
                                pattern.span,
                                format!(
                                    "structural pattern does not match any record alternative of {}",
                                    c.types.name(ty)
                                ),
                            ));
                        }
                        [one] => (one.1, true),
                        _ => {
                            return Err(Diagnostic::new(
                                pattern.span,
                                "this structural pattern matches several union alternatives; narrow with 'Type @ pattern' first",
                            ));
                        }
                    }
                } else {
                    (ty, false)
                };
                let Some(layout) = record_layout(c, member) else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "a structural pattern matches a record value, found {}",
                            c.types.name(member)
                        ),
                    ));
                };
                let variant = c.types.enums[layout].variants[0].clone();
                let mut checked = Vec::new();
                let mut offset = 1;
                for (index, field_ty) in variant.fields.iter().enumerate() {
                    let sub = fields.iter().find(|(n, _)| *n == variant.names[index]);
                    let p = match sub {
                        Some((_, p)) => c.pattern(p, *field_ty, bindings)?,
                        None => Pattern::Any,
                    };
                    checked.push((offset, p));
                    offset += c.types.width(*field_ty);
                }
                if let Some((name, p)) = fields.iter().find(|(n, _)| !variant.names.contains(n)) {
                    return Err(Diagnostic::new(
                        p.span,
                        format!("record has no field '{name}'"),
                    ));
                }
                let inner = Pattern::Variant {
                    tag: 0,
                    fields: checked,
                };
                if narrowed {
                    let tag = match ty {
                        Type::Union(id) => c.types.unions[id]
                            .members
                            .iter()
                            .position(|candidate| *candidate == member)
                            .expect("narrowed member is in the union"),
                        _ => unreachable!("only a union can be narrowed here"),
                    };
                    return Ok(Pattern::Type {
                        tag,
                        member,
                        inner: Box::new(inner),
                    });
                }
                return Ok(inner);
            }
            // Constructor, record, and array/variant patterns can narrow a
            // union directly when exactly one alternative has the right shape.
            if let Type::Union(id) = ty {
                let members = c.types.unions[id].members.clone();
                if let Some(owner) = c
                    .resolution
                    .reference(pattern.span)
                    .filter(|id| c.resolution.bindings[*id].kind == BindingKind::Constructor)
                {
                    let (owner, _) = c.types.owner(owner);
                    let found = members.iter().enumerate().find(|(_, member)| {
                        member
                            .layout()
                            .is_some_and(|layout| c.types.enums[layout].definition == owner)
                    });
                    let ambiguous = members
                        .iter()
                        .filter(|member| {
                            member
                                .layout()
                                .is_some_and(|layout| c.types.enums[layout].definition == owner)
                        })
                        .count()
                        > 1;
                    if ambiguous {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "this constructor matches several union alternatives; narrow with 'Type @ pattern' first",
                        ));
                    }
                    let Some((tag, member)) = found else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "this constructor's enum is not an alternative of the union scrutinee",
                        ));
                    };
                    let member = *member;
                    let inner = c.pattern(pattern, member, bindings)?;
                    return Ok(Pattern::Type {
                        tag,
                        member,
                        inner: Box::new(inner),
                    });
                }
                if let ast::PatternKind::Record { fields, .. } = &pattern.kind {
                    let Some(definition) = c
                        .resolution
                        .reference(pattern.span)
                        .filter(|id| c.types.is_record(*id))
                    else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "expected a record type in this pattern",
                        ));
                    };
                    let found = members.iter().enumerate().find(|(_, member)| {
                        member
                            .layout()
                            .is_some_and(|layout| c.types.enums[layout].definition == definition)
                    });
                    let ambiguous = members
                        .iter()
                        .filter(|member| {
                            member.layout().is_some_and(|layout| {
                                c.types.enums[layout].definition == definition
                            })
                        })
                        .count()
                        > 1;
                    if ambiguous {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "this record pattern matches several union alternatives; narrow with 'Type @ pattern' first",
                        ));
                    }
                    let Some((tag, member)) = found else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "record {} is not an alternative of {}",
                                c.resolution.bindings[definition].name,
                                c.types.name(ty)
                            ),
                        ));
                    };
                    let member = *member;
                    let inner = c.record_pattern(pattern, fields, member, bindings)?;
                    return Ok(Pattern::Type {
                        tag,
                        member,
                        inner: Box::new(inner),
                    });
                }
                if matches!(
                    pattern.kind,
                    ast::PatternKind::Integer(_)
                        | ast::PatternKind::Bool(_)
                        | ast::PatternKind::Slice(_)
                        | ast::PatternKind::Tuple(_)
                ) {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "narrow a heterogeneous union with 'Type @ pattern' before matching a literal or array payload",
                    ));
                }
            }
            if let Some(id) = c.resolution.reference(pattern.span)
                && c.resolution.bindings[id].kind == BindingKind::Constructor
            {
                let (owner, tag) = c.types.owner(id);
                let Some(index) = ty.layout() else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "enum constructor pattern requires an enum value",
                    ));
                };
                if c.types.enums[index].definition != owner {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "pattern constructor belongs to a different enum",
                    ));
                }
                if c.mask(ty) & (1 << tag) == 0 {
                    return Err(Diagnostic::new(
                        pattern.span,
                        format!(
                            "variant {} is excluded by the scrutinee type {}",
                            c.types.enums[index].variants[tag].name,
                            c.types.name(ty)
                        ),
                    ));
                }
                let variant = c.types.enums[index].variants[tag].clone();
                let fields = match &pattern.kind {
                    ast::PatternKind::Constructor { fields, .. } if variant.tuple => {
                        fields.as_slice()
                    }
                    ast::PatternKind::Name(_) if !variant.tuple => &[][..],
                    _ => {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "enum pattern payload syntax does not match the variant",
                        ));
                    }
                };
                if fields.len() != variant.fields.len() {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "wrong enum pattern payload arity",
                    ));
                }
                let mut offset = 1;
                let mut checked = Vec::new();
                for (field, ty) in fields.iter().zip(variant.fields) {
                    checked.push((offset, c.pattern(field, ty, bindings)?));
                    offset += c.types.width(ty);
                }
                return Ok(Pattern::Variant {
                    tag,
                    fields: checked,
                });
            }
            if let ast::PatternKind::Slice(parts) = &pattern.kind {
                let Some((element, length)) = ty.layout().and_then(|id| c.types.enums[id].array)
                else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "array pattern requires an inline array",
                    ));
                };
                if parts.len() != length {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "array pattern length differs from its type",
                    ));
                }
                let mut fields = Vec::new();
                for (i, part) in parts.iter().enumerate() {
                    fields.push((
                        1 + i * c.types.width(element),
                        c.pattern(part, element, bindings)?,
                    ));
                }
                return Ok(Pattern::Variant { tag: 0, fields });
            }
            if let ast::PatternKind::Record { fields, .. } = &pattern.kind {
                return c.record_pattern(pattern, fields, ty, bindings);
            }
            match &pattern.kind {
                ast::PatternKind::Wildcard => Ok(Pattern::Any),
                ast::PatternKind::Name(path) if path.len() == 1 => {
                    if let Some((slot, previous)) = bindings.get(&path[0]) {
                        c.expect(ty, *previous, pattern.span)?;
                        return Ok(Pattern::Bind(*slot));
                    }
                    let slot = c.bind(pattern.span, ty, false)?;
                    bindings.insert(path[0].clone(), (slot, ty));
                    Ok(Pattern::Bind(slot))
                }
                ast::PatternKind::Integer(text) => {
                    let kind = match ty.int_kind() {
                        Some(kind) => kind,
                        None => {
                            c.expect(ty, Type::I64, pattern.span)?;
                            crate::int::IntKind::I64
                        }
                    };
                    let value = text
                        .parse::<i128>()
                        .ok()
                        .and_then(|v| kind.encode(v))
                        .ok_or_else(|| {
                            Diagnostic::new(
                                pattern.span,
                                format!("pattern is outside the {} range", kind.name()),
                            )
                        })?;
                    Ok(Pattern::Literal(value))
                }
                ast::PatternKind::Char(ch) => {
                    c.expect(ty, Type::Char, pattern.span)?;
                    Ok(Pattern::Literal(i64::from(u32::from(*ch))))
                }
                ast::PatternKind::Bool(value) => {
                    c.expect(ty, Type::Bool, pattern.span)?;
                    Ok(Pattern::Literal(i64::from(*value)))
                }
                ast::PatternKind::Tuple(values) if values.len() >= 2 => {
                    let Some(layout) = ty.layout().filter(|l| c.types.enums[*l].tuple) else {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!("tuple pattern does not match a value of type {}", c.types.name(ty)),
                        ));
                    };
                    let elements = c.types.enums[layout].arguments.clone();
                    if elements.len() != values.len() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!("tuple pattern has {} elements, but the value has {}", values.len(), elements.len()),
                        ));
                    }
                    let mut fields = Vec::new();
                    let mut offset = 1;
                    for (value, element) in values.iter().zip(elements) {
                        fields.push((offset, c.pattern(value, element, bindings)?));
                        offset += c.types.width(element);
                    }
                    Ok(Pattern::Variant { tag: 0, fields })
                }
                ast::PatternKind::Tuple(values) if values.is_empty() => {
                    c.expect(ty, Type::Unit, pattern.span)?;
                    Ok(Pattern::Literal(0))
                }
                ast::PatternKind::Tuple(values) if values.len() == 1 => Err(Diagnostic::new(
                    pattern.span,
                    "one-element tuple patterns are not supported; write '()' for unit or omit the trailing comma",
                )),
                ast::PatternKind::Or(patterns) => Ok(Pattern::Or(
                    patterns
                        .iter()
                        .map(|p| c.pattern(p, ty, bindings))
                        .collect::<Result<_>>()?,
                )),
                _ => Err(Diagnostic::new(pattern.span, "unsupported runtime pattern")),
            }
        })
    }
}

impl Executable {
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }
    /// Erased proof obligations discharged at compile time, each with a
    /// certificate that was re-checked independently of the search.
    pub fn certificates(&self) -> &[crate::facts::Certificate] {
        &self.certificates
    }
    /// Total logical definitions that were kernel-checked and erased.
    pub fn logical_definitions(&self) -> &[String] {
        &self.logical_definitions
    }
    /// Checked nested in-place map fusions. Diagnostics-only observation.
    pub fn fusion_count(&self) -> usize {
        self.fusions
    }
    pub(crate) fn entry(&self) -> Result<usize> {
        self.entry.ok_or_else(|| {
            Diagnostic::new(
                Span::default(),
                "a runnable executable needs fn main() -> Unit or i64",
            )
        })
    }
    pub(crate) fn width(&self, ty: Type) -> usize {
        crate::runtime_types::width(&self.enums, &self.unions, &self.function_types, ty)
    }
    pub(crate) fn owns(&self, ty: Type) -> bool {
        match ty {
            Type::Box(_)
            | Type::Arena
            | Type::ArenaBox(_)
            | Type::Bytes
            | Type::String
            | Type::Vec(_)
            | Type::Once(_)
            | Type::Task(_) => true,
            Type::Enum(id) | Type::Variants(id, _) => self.owned_enums[id],
            Type::Union(id) => self.unions[id]
                .members
                .iter()
                .any(|member| self.owns(*member)),
            _ => false,
        }
    }
}

/// Substitute alias generic binders with argument type expressions. This is
/// structural, span-preserving substitution used only for first-order
/// inference through a generic alias; actual elaboration still goes through
/// `Types::lower`, which applies the full checked substitution.
pub(crate) fn substitute_alias_type(
    resolution: &Resolution,
    ty: &ast::Type,
    map: &BTreeMap<BindingId, &ast::Type>,
) -> ast::Type {
    use ast::TypeKind as K;
    let kind = match &ty.kind {
        K::Named { path, arguments } => {
            if arguments.is_empty()
                && let Some(id) = resolution.reference(ty.span)
                && let Some(replacement) = map.get(&id)
            {
                return (*replacement).clone();
            }
            K::Named {
                path: path.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_alias_type(resolution, argument, map))
                    .collect(),
            }
        }
        K::Dyn(inner) => K::Dyn(Box::new(substitute_alias_type(resolution, inner, map))),
        K::Integer(value) => K::Integer(value.clone()),
        K::Bool(value) => K::Bool(*value),
        K::Lifetime(name) => K::Lifetime(name.clone()),
        K::Tuple(items) => K::Tuple(
            items
                .iter()
                .map(|item| substitute_alias_type(resolution, item, map))
                .collect(),
        ),
        K::Structural(fields) => K::Structural(
            fields
                .iter()
                .map(|field| ast::Field {
                    name: field.name.clone(),
                    ty: substitute_alias_type(resolution, &field.ty, map),
                    span: field.span,
                })
                .collect(),
        ),
        K::Slice(inner) => K::Slice(Box::new(substitute_alias_type(resolution, inner, map))),
        K::Array(element, length) => K::Array(
            Box::new(substitute_alias_type(resolution, element, map)),
            Box::new(substitute_alias_type(resolution, length, map)),
        ),
        K::Borrow {
            lifetime,
            mutable,
            inner,
        } => K::Borrow {
            lifetime: lifetime.clone(),
            mutable: *mutable,
            inner: Box::new(substitute_alias_type(resolution, inner, map)),
        },
        K::Function {
            lifetimes,
            parameters,
            result,
            effects,
            call_once,
            call_linear,
        } => K::Function {
            lifetimes: lifetimes.clone(),
            parameters: parameters
                .iter()
                .map(|parameter| ast::TypeParameter {
                    name: parameter.name.clone(),
                    ty: substitute_alias_type(resolution, &parameter.ty, map),
                    span: parameter.span,
                })
                .collect(),
            result: Box::new(substitute_alias_type(resolution, result, map)),
            effects: effects
                .iter()
                .map(|effect| substitute_alias_type(resolution, effect, map))
                .collect(),
            call_once: *call_once,
            call_linear: *call_linear,
        },
        K::Binary { op, left, right } => K::Binary {
            op: op.clone(),
            left: Box::new(substitute_alias_type(resolution, left, map)),
            right: Box::new(substitute_alias_type(resolution, right, map)),
        },
        K::Graded { inner, grade } => K::Graded {
            inner: Box::new(substitute_alias_type(resolution, inner, map)),
            grade: Box::new(substitute_alias_type(resolution, grade, map)),
        },
        K::Predicate(expr) => K::Predicate(expr.clone()),
        K::SelfType => K::SelfType,
    };
    ast::Type::new(kind, ty.span)
}

/// Whether a synthesized adapter body creates a capturing closure
/// environment. Such a body allocates when the adapter is called, so the
/// adapter's declared effect row must include `alloc` and `panic`.
fn block_allocates(block: &Block) -> bool {
    fn expr(node: &Expr) -> bool {
        match &node.kind {
            ExprKind::FnValue { captures, .. } => !captures.is_empty() || captures.iter().any(expr),
            ExprKind::Block(block) => block_allocates(block),
            ExprKind::Unary(_, value)
            | ExprKind::Try { value, .. }
            | ExprKind::Return(value)
            | ExprKind::BoxNew(value)
            | ExprKind::BoxTake(value)
            | ExprKind::BoxRead(value)
            | ExprKind::ArenaBoxRead(value)
            | ExprKind::ArenaBoxTake(value)
            | ExprKind::Drop(value)
            | ExprKind::Project(value, _)
            | ExprKind::Coerce { value, .. }
            | ExprKind::Break(Some(value), _)
            | ExprKind::Assign(_, value) => expr(value),
            ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. }
            | ExprKind::ArenaAlloc {
                arena: owner,
                value: payload,
            } => expr(owner) || expr(payload),
            ExprKind::ArenaNew
            | ExprKind::BoxTryNew { .. }
            | ExprKind::BytesTryWithCapacity { .. } => true,
            ExprKind::Loop(block) => block_allocates(block),
            ExprKind::While(condition, block) => expr(condition) || block_allocates(block),
            ExprKind::BytesAt(a, b) | ExprKind::Binary(_, a, b) => expr(a) || expr(b),
            ExprKind::RefAssign(reference, _, value) => expr(reference) || expr(value),
            ExprKind::Slice {
                base, start, end, ..
            } => {
                expr(base) || start.as_deref().is_some_and(expr) || end.as_deref().is_some_and(expr)
            }
            ExprKind::Call(_, arguments)
            | ExprKind::Construct {
                fields: arguments, ..
            } => arguments.iter().any(expr),
            ExprKind::CallIndirect { callee, arguments } => {
                expr(callee) || arguments.iter().any(expr)
            }
            ExprKind::TaskSpawn { .. } | ExprKind::TaskScope { .. } => true,
            ExprKind::TaskCancel(reference) => expr(reference),
            ExprKind::TaskJoin { task, .. } => expr(task),
            ExprKind::TaskYield | ExprKind::TaskCheckCancel => false,
            ExprKind::If(condition, yes, no) => {
                expr(condition) || block_allocates(yes) || block_allocates(no)
            }
            ExprKind::Match(value, arms) => {
                expr(value)
                    || arms
                        .iter()
                        .any(|arm| arm.guard.as_ref().is_some_and(expr) || expr(&arm.body))
            }
            _ => false,
        }
    }
    block.statements.iter().any(|statement| match statement {
        Statement::Let(_, value) | Statement::Expr(value) => expr(value),
    }) || block.tail.as_deref().is_some_and(expr)
}

/// Collect runtime binding references in a lambda body so captures can be
/// moved into the closure environment. Name resolution has already chosen the
/// exact binder, so a reference to an outer local remains distinguishable from
/// lambda parameters and lambda-local bindings.
fn collect_lambda_refs(resolution: &Resolution, block: &ast::Block, out: &mut BTreeSet<BindingId>) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } => collect_expr_refs(resolution, value, out),
            ast::Statement::Expr(expr) => collect_expr_refs(resolution, expr, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_expr_refs(resolution, tail, out);
    }
}

fn collect_expr_refs(resolution: &Resolution, expr: &ast::Expr, out: &mut BTreeSet<BindingId>) {
    if let Some(id) = resolution.reference(expr.span) {
        out.insert(id);
    }
    match &expr.kind {
        ast::ExprKind::Name(_)
        | ast::ExprKind::Integer(_)
        | ast::ExprKind::Float(_)
        | ast::ExprKind::String(_)
        | ast::ExprKind::Char(_)
        | ast::ExprKind::Bool(_)
        | ast::ExprKind::Continue => {}
        ast::ExprKind::Tuple(values) | ast::ExprKind::Array(values) => {
            for value in values {
                collect_expr_refs(resolution, value, out);
            }
        }
        ast::ExprKind::StructuralLiteral(fields) => {
            for (_, value) in fields {
                collect_expr_refs(resolution, value, out);
            }
        }
        ast::ExprKind::Block(block) => collect_lambda_refs(resolution, block, out),
        ast::ExprKind::Unary { operand, .. } | ast::ExprKind::Try(operand) => {
            collect_expr_refs(resolution, operand, out)
        }
        ast::ExprKind::Binary { left, right, .. } => {
            collect_expr_refs(resolution, left, out);
            collect_expr_refs(resolution, right, out);
        }
        ast::ExprKind::Call { callee, arguments } => {
            collect_expr_refs(resolution, callee, out);
            for argument in arguments {
                collect_expr_refs(resolution, argument, out);
            }
        }
        ast::ExprKind::Handle { handler, body, .. } => {
            collect_expr_refs(resolution, handler, out);
            collect_lambda_refs(resolution, body, out);
        }
        ast::ExprKind::Perform { value, .. } => collect_expr_refs(resolution, value, out),
        ast::ExprKind::Lambda(lambda) => collect_lambda_refs(resolution, &lambda.body, out),
        ast::ExprKind::Specialize { callee, .. } => collect_expr_refs(resolution, callee, out),
        ast::ExprKind::Field { value, .. } => collect_expr_refs(resolution, value, out),
        ast::ExprKind::Index { value, index } => {
            collect_expr_refs(resolution, value, out);
            collect_expr_refs(resolution, index, out);
        }
        ast::ExprKind::Slice { value, start, end } => {
            collect_expr_refs(resolution, value, out);
            if let Some(start) = start {
                collect_expr_refs(resolution, start, out);
            }
            if let Some(end) = end {
                collect_expr_refs(resolution, end, out);
            }
        }
        ast::ExprKind::Return(value) | ast::ExprKind::Break(value) => {
            if let Some(value) = value {
                collect_expr_refs(resolution, value, out);
            }
        }
        ast::ExprKind::If {
            condition,
            then,
            otherwise,
        } => {
            collect_expr_refs(resolution, condition, out);
            collect_lambda_refs(resolution, then, out);
            if let Some(otherwise) = otherwise {
                collect_expr_refs(resolution, otherwise, out);
            }
        }
        ast::ExprKind::Match { value, arms } => {
            collect_expr_refs(resolution, value, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(resolution, guard, out);
                }
                collect_expr_refs(resolution, &arm.body, out);
            }
        }
        ast::ExprKind::Record { ty, fields } => {
            collect_expr_refs(resolution, ty, out);
            for (_, value) in fields {
                collect_expr_refs(resolution, value, out);
            }
        }
        ast::ExprKind::While { condition, body } => {
            collect_expr_refs(resolution, condition, out);
            collect_lambda_refs(resolution, body, out);
        }
        ast::ExprKind::Loop(body) => collect_lambda_refs(resolution, body, out),
    }
}

/// Variants fully matched by an irrefutable-payload pattern.
fn covered_variants(pattern: &Pattern) -> u64 {
    fn irrefutable(p: &Pattern) -> bool {
        match p {
            Pattern::Any | Pattern::Bind(_) => true,
            Pattern::Or(ps) => ps.iter().any(irrefutable),
            _ => false,
        }
    }
    match pattern {
        Pattern::Any | Pattern::Bind(_) => u64::MAX,
        Pattern::Variant { tag, fields } if fields.iter().all(|(_, p)| irrefutable(p)) => 1 << tag,
        Pattern::Type { tag, .. } => 1 << tag,
        Pattern::Or(ps) => ps.iter().map(covered_variants).fold(0, |a, b| a | b),
        _ => 0,
    }
}
