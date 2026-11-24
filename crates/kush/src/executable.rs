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

pub(crate) mod anf;
mod blocks;
mod builtin_calls;
mod calls_records;
mod coercion;
mod collections;
mod concurrency;
mod construction_staging;
mod expressions;
mod handlers;
mod lambdas;
mod memory_calls;
mod methods;
mod performs;
mod places;
mod postconditions;
mod proof_scalars;
mod recursive_lifetimes;
mod slices;
mod unification;

type Result<T> = std::result::Result<T, Diagnostic>;
/// FND-ROWS-PANIC: `panic` is not an effect; any function may panic. The
/// constant is the empty set, so no row contains it and `require(PANIC)`
/// always holds. Code generation must not read "may not panic" from a row:
/// native tests the abort word after every call in unwinding programs.
/// (Bit 0 stays unused; declared operations start at `1 << 4`.)
pub(crate) const PANIC: u16 = 0;
/// CAP-CAPTURING-LEXICAL: operation ids above this name private frames of
/// capability-only capturing handlers; no declared operation reaches them.
pub(crate) const PRIVATE_OPERATION_BASE: usize = 1 << 20;
pub(crate) const IO: u16 = 2;
pub(crate) const ALLOC: u16 = 4;
pub(crate) const SUSPEND: u16 = 8;
pub(crate) const EFFECT_BITS: u16 = PANIC | IO | ALLOC | SUSPEND;
pub(crate) const MAX_EFFECT_ROW_VARIABLES: usize = 16;
/// Runtime host stubs whose answer is fixed for the process, so std may
/// declare them without the `io` effect (SIMD-CPU). Only std can import a
/// `kush_sys_*` symbol, so no program can add to this list.
const PURE_HOST_SYMBOLS: &[&str] = &["kush_sys_cpu_features"];
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
    /// An exclusive borrowed UTF-8 text view: `&'a mut str`. Same four-word
    /// descriptor as `Str`. It is a move-only capability with an exclusive
    /// loan on its `String` owner; the only writes are the checked
    /// `Str.make_ascii_*` and `Str.set_scalar` operations, which never change
    /// the byte length and keep the bytes valid UTF-8.
    StrMut,
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
    /// A multishot resumption token, `multi fn(R) -> R`
    /// (docs/multishot-capabilities.md). Two words: code address and an
    /// environment on the task's continuation stack (null when capture-free).
    /// Copyable and second-class: calls do not consume it, it owns nothing,
    /// and it is never stored, returned or captured, so the environment is
    /// released when the token call or `handle` that pushed it returns.
    Multi(usize),
    /// An opaque, affine structured-task handle. One word. Handles are created
    /// only inside a `Task.scope` and may not escape it through data or results.
    Task(usize),
    /// THREAD-CHANNELS: an owned bounded channel of plain-data messages
    /// (scalars and records of scalars). One word: the runtime channel.
    /// Shared between threads through a view `&[Channel<T>]`.
    Channel(usize),
    /// THREAD-ATOMICS: an atomic i64 cell. One word, affine (never copied,
    /// so it is never read with a plain load) and owning nothing. Shared
    /// between threads through a borrowed view `&[Atomic]` and used only by
    /// the `Atomic.*` operations.
    Atomic,
    /// THREAD-SCOPE: an opaque, affine handle of a parallel child thread
    /// (`Thread.spawn`). One word. Same structured rules as `Task`.
    Thread(usize),
    /// Owning bump-allocator region handle, one word. Values allocated through
    /// `Arena.alloc` retain the region, so the arena value may be dropped while
    /// its boxes remain live.
    Arena,
    /// An owning box allocated inside an `Arena`. One word: a payload pointer
    /// whose preceding header retains the region. Its payload is destroyed
    /// before the region reference is released.
    ArenaBox(usize),
    /// An open/generic trait object with checked dynamic dispatch. Two words:
    /// a member identifier and an owned heap payload. The identifier selects a
    /// compile-time-registered vtable entry for the concrete member; the value
    /// layout never enumerates the trait's members, so adding a generic or
    /// blanket impl instantiation does not change it. See `DynObjectType`.
    DynObj(usize),
    /// A checked user-defined allocator value: three words, the code pointers
    /// of a noncapturing `fn(i64) -> Bytes` allocation function, a
    /// noncapturing `fn(Bytes) -> Unit` release function, and an optional
    /// `fn(Bytes, i64) -> Bytes` growth hook (zero when absent). It owns
    /// nothing, so it is copyable; containers store their own copy and never
    /// borrow the allocator binding.
    Allocator,
    /// An owning, reference-counted allocator instance. One word: a handle to
    /// compiler-owned context storage that holds the concrete integer state
    /// value and checked allocate/release/grow thunks. Containers retain one
    /// reference, so they may outlive the binding that created the context;
    /// the last reference runs the state's drop glue exactly once.
    AllocatorContext,
    /// An owning box whose storage was supplied by a user allocator. Three
    /// words: the allocation code pointer, the release code pointer, and the
    /// `Bytes` block that owns the payload storage. Dropping the box destroys
    /// the payload and releases that block through the stored release
    /// function exactly once.
    AllocBox(usize),
    /// A growable vector whose element storage is supplied and released by a
    /// user allocator. One word: a handle to checked metadata that records the
    /// allocator pair, the element block, length, and capacity.
    AllocVec(usize),
    /// GPU-SUBSET: a device buffer of packed 4-byte `i32`/`u32`/`f32`
    /// elements (the pointee). Owned and affine; one word on the CPU side.
    /// `#[gpu]` entry functions receive it as `&GpuBuf<T>` (read-only
    /// storage) or `&mut GpuBuf<T>` (read-write storage); see docs/gpu.md.
    GpuBuf(usize),
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
        matches!(
            self,
            Type::Slice(_) | Type::SliceMut(_) | Type::Str | Type::StrMut
        )
    }
    /// Whether this is an exclusive view capability: `&mut [T]` or `&mut str`.
    pub(crate) fn is_mut_slice(self) -> bool {
        matches!(self, Type::SliceMut(_) | Type::StrMut)
    }
    /// Whether this is a shared or exclusive UTF-8 text view.
    pub(crate) fn is_text(self) -> bool {
        matches!(self, Type::Str | Type::StrMut)
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
/// One concrete `AllocatorProtocol` instance shape used by an allocator
/// context. `alloc`, `free`, and `grow` are checked method function indices
/// whose first receiver is `&mut State`; both backends call them with the
/// context's retained state address. The state type is recorded so native
/// code can synthesize its drop thunk.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct AllocatorContextSpec {
    pub(crate) state: Type,
    pub(crate) alloc: usize,
    pub(crate) free: usize,
    pub(crate) grow: usize,
}
#[derive(Debug, Clone)]
pub struct Executable {
    /// Function indices emitted by checked quotations. Opaque graph bytes
    /// may name only these templates, never arbitrary executable functions.
    pub(crate) stage_templates: BTreeSet<usize>,
    pub(crate) functions: Vec<Function>,
    /// Step budget of the reference evaluator (per task); see `set_eval_fuel`.
    pub(crate) eval_fuel: usize,
    /// Checked allocator-context shapes, referenced by `AllocatorContextNew`.
    pub(crate) allocator_contexts: Vec<AllocatorContextSpec>,
    pub(crate) entry: Option<usize>,
    pub(crate) enums: Vec<Enum>,
    pub(crate) pointees: Vec<Type>,
    pub(crate) unions: Vec<crate::runtime_types::UnionType>,
    pub(crate) function_types: Vec<FunctionType>,
    /// Checked spelling of each dynamically dispatched object specialization.
    pub(crate) dyn_object_names: Vec<String>,
    /// Registered concrete members of each dynamic object specialization.
    pub(crate) dyn_members: Vec<Vec<DynMember>>,
    /// Checked dynamic-object call sites.
    pub(crate) dyn_calls: Vec<DynCallSpec>,
    /// Checked borrowed calls on closed-world union objects.
    pub(crate) union_calls: Vec<UnionCallSpec>,
    /// Erased lifetime names for reference elements stored inside containers.
    /// Checker-only; the runtime representation is one word and carries no
    /// label. Ownership uses this table to recover a declared element lifetime
    /// from a container's pointee type.
    pub(crate) reference_labels: Vec<String>,
    /// Finite lifetime-only variance of declared lifetime parameters. Ownership
    /// uses the signed occurrence direction of each borrowed leaf; this table
    /// is never consulted by either runtime backend.
    pub(crate) variance: crate::variance::VarianceTable,
    pub(crate) owned_enums: Vec<bool>,
    pub(crate) linear_enums: Vec<bool>,
    /// Checked foreign imports aligned with `functions`; `Some` marks an
    /// imported host function whose body is inert and never executed.
    pub(crate) foreign_functions: Vec<Option<ForeignFunction>>,
    /// KUSH-RUST-EXPORT: `export "symbol" fn` instances, in declaration order.
    pub(crate) exports: Vec<ExportedFunction>,
    pub(crate) certificates: Vec<crate::facts::Certificate>,
    /// Total logical definitions checked by the kernel and erased from the IR.
    pub(crate) logical_definitions: Vec<String>,
    /// Checked nested in-place maps fused into one traversal. This is a
    /// tooling observation, not a source-language effect or proof fact.
    pub(crate) fusions: usize,
    /// Element accesses proved in bounds (inline, unchecked) and those left
    /// to a run-time check: the `KUSH_PROOF_REPORT` numbers.
    pub(crate) bounds_proved: usize,
    pub(crate) bounds_checked: usize,
    /// PROOF-FUZZ: every run-time check left in place, in source order.
    pub(crate) obligations: Vec<Obligation>,
    /// PROOF-FUZZ: every check the prover discharged (no run-time check).
    pub(crate) discharged: Vec<Obligation>,
    /// Whether any checked body contains a structured-task operation. Task
    /// programs use the cooperative reference scheduler and buffered host I/O.
    pub(crate) uses_tasks: bool,
    /// THREAD-SCOPE: the program runs OS threads (thread-safe runtime paths).
    pub(crate) uses_threads: bool,
    /// PANIC-UNWIND-NATIVE: the program has a panic catch boundary (it uses
    /// `Task.catch`), so native panics unwind: generated code tests the
    /// abort word after calls that may panic.
    pub(crate) uses_unwinding: bool,
    /// LANG-STACK-SIZE: `#[stack_size(N)]` on main, in bytes. The native
    /// runtime runs the program on a thread with a stack this large.
    pub(crate) main_stack: Option<u64>,
    /// GPU-SUBSET: per function instance, whether it is a `#[gpu]` function.
    /// Functions added after checking (continuations) are never GPU code.
    pub(crate) gpu_functions: Vec<bool>,
    /// SIMD-NATIVE: per function instance, `(vector type, function name)` when
    /// it is a function of a vector type in `std.simd` (or `("x86", name)`
    /// for an intrinsic of `std.x86`), which the native
    /// backend may replace with vector instructions. The Kush body stays the
    /// specification (and the evaluator's implementation).
    pub(crate) simd_functions: Vec<Option<(String, String)>>,
    /// PANIC-LINEAR-CLEANUP: record layout -> the function run on a live
    /// value of it while a panic unwinds (`#[linear(unwind = f)]`).
    pub(crate) unwind_functions: BTreeMap<usize, usize>,
    /// Effect-row bit of each declared operation, by operation id.
    pub(crate) effect_bits: Vec<u16>,
    /// Whether each declared operation is abortive (`-> Never`).
    pub(crate) abortive_operations: Vec<bool>,
    /// Own grade tables for every copyable identity above. Keep this last so
    /// tables remain available while all other program metadata is dropped.
    pub(crate) _grade_algebras: Vec<std::sync::Arc<crate::grades::Algebra>>,
}
/// PROOF-FUZZ: what a run-time check the prover could not discharge guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ObligationKind {
    /// An element access. `refined_length` is the `where len >= N` bound of a
    /// length-refined field, when the container has one.
    Bounds {
        container: Container,
        refined_length: Option<i64>,
    },
    /// Integer `+`, `-`, `*` or unary `-` whose result may leave its type.
    Overflow,
    /// Integer `/` or `%`: a zero divisor, or `MIN / -1`.
    Division,
    /// `<<` or `>>`: a shift amount outside the type's width.
    Shift,
}
/// The kind of container an access reads or writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Container {
    Vec,
    Slice,
    Array,
    Bytes,
}
/// PROOF-FUZZ: one run-time check the prover left in the program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Obligation {
    pub kind: ObligationKind,
    /// The span of the checked expression: the span the reference evaluator
    /// reports when this check panics.
    pub span: Span,
    /// The function instance the check is in (index into the executable's
    /// functions) and its name.
    pub function: usize,
    pub function_name: String,
    /// The condition the check tests, as the prover saw it.
    pub goal: String,
}
impl ObligationKind {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Bounds { .. } => "bounds",
            Self::Overflow => "overflow",
            Self::Division => "division",
            Self::Shift => "shift",
        }
    }
}
#[derive(Debug, Clone)]
pub(crate) struct Function {
    pub name: String,
    /// Number of initial locals that are runtime parameters. For a capturing
    /// closure this includes the captured values, which arrive from the owned
    /// environment pointer rather than from ordinary call arguments.
    pub parameters: usize,
    /// Number of leading locals captured from a closure environment. `None`
    /// for ordinary functions, noncapturing lambdas, and pure adapters.
    pub closure: Option<usize>,
    /// One flag per capture position: the environment stores a pointer to the
    /// captured caller location instead of a copy. Only call-scoped scalar
    /// captures use this representation; the ownership pass guarantees the
    /// closure cannot outlive the location.
    pub capture_refs: Vec<bool>,
    /// One flag per capture position: the lambda body may assign that captured
    /// location. A writing capture is an exclusive loan; a read-only capture is
    /// a shared loan.
    pub capture_writes: Vec<bool>,
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
    /// Lifetime binders declared by this function or method. They are rigid
    /// destinations for mutable container/record writes; labels that appear
    /// only in an expected instantiation are placeholders, not destinations.
    pub declared_lifetimes: BTreeSet<String>,
    /// Pairs `(low, high)` of index-place identities (`ExprKind::PlaceIndex`
    /// ids) whose index values the facts proved distinct where the later
    /// place was created. The ownership pass uses them to keep two element
    /// references into one array, vector, or view live together.
    pub index_relations: BTreeSet<(usize, usize)>,
    /// Local slot receiving each physical capture and parameter, in ABI order.
    /// `None` is the ordinary layout `0..parameters`. Continuation functions
    /// synthesized by `crate::suspend` keep the enclosing function's slot
    /// numbering and receive their captures at those slots.
    pub parameter_slots: Option<Vec<usize>>,
    /// Per local: its type holds a borrow (view, text, reference, borrowed
    /// record, or task handle). Empty when not computed; the suspension
    /// lowering then treats every local as borrowed.
    pub local_borrowed: Vec<bool>,
    /// Per local: the value is copyable (neither owning nor linear).
    pub local_copyable: Vec<bool>,
    /// Parameter slots of type `cap Op` (EFF-CAP-RESUME-CALLS).
    pub capability_parameters: Vec<usize>,
    /// A `multi fn` continuation: its captures are copied out of an
    /// environment on the continuation stack, which the call leaves in place
    /// for later resumptions (docs/multishot-capabilities.md).
    pub shared_environment: bool,
}
#[derive(Debug, Clone, Copy)]
pub(crate) struct Local {
    pub ty: Type,
    pub mutable: bool,
    /// `@[1]` on an owning/linear value: must be consumed exactly once.
    pub linear: bool,
    /// Whether this binding's address is taken by a checked borrow or a field
    /// reference. Only these locals need stable stack storage in the native
    /// backend; ordinary scalar locals stay in SSA variables.
    pub pinned: bool,
    /// Explicit usage grade, if the binding was annotated.
    pub grade: Option<Grade>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub(crate) struct Block {
    pub statements: Vec<Statement>,
    pub tail: Option<Box<Expr>>,
    pub ty: Type,
}
#[derive(Debug, Clone)]
pub(crate) enum Statement {
    Let(usize, Expr),
    /// Declare hidden backing storage for a temporary owner without
    /// evaluating it. The initializer runs at its source position through
    /// `ExprKind::InitOwner` or `ExprKind::BorrowInit`; the slot is cleaned up
    /// at the end of this lexical block only if it was actually initialized.
    Declare(usize),
    Expr(Expr),
}
#[derive(Debug, Clone)]
pub(crate) struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
    pub span: Span,
    pub resource: Option<usize>,
}
/// One registered concrete member of a dynamically dispatched trait object.
/// `methods` maps each object-safe trait method to the checked function
/// instance selected for this member, including generic/blanket impl
/// instantiations and inherited default bodies.
#[derive(Debug, Clone)]
pub(crate) struct DynMember {
    pub member: Type,
    pub methods: BTreeMap<DynMethodKey, usize>,
}
/// The monomorphized type, grade, natural, and effect arguments of one generic
/// method instance. A non-generic method uses an empty key.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct DynMethodKey {
    /// Position of the method's trait in the object's canonical component
    /// list; always zero for a one-trait object.
    pub component: usize,
    pub name: String,
    pub types: Vec<Type>,
    pub consts: Vec<usize>,
    pub grades: Vec<Grade>,
    pub effects: Vec<u16>,
}
impl DynMethodKey {
    /// The key of a non-generic method of the listed trait at `component`.
    pub(crate) fn in_component(component: usize, name: &str) -> Self {
        Self {
            component,
            name: name.to_owned(),
            ..Default::default()
        }
    }
}
/// A checked call site on a dynamically dispatched trait object. The native
/// and reference backends resolve the member identifier carried by the object
/// against `dyn_members[object]`, then call the selected checked function.
#[derive(Debug, Clone)]
pub(crate) struct DynCallSpec {
    pub object: usize,
    pub trait_name: String,
    pub method: String,
    /// Monomorphized generic-method arguments selecting the member-table entry.
    pub key: DynMethodKey,
    pub mode: ReceiverMode,
    /// Usage grade of each non-receiver argument, used by the grade checker.
    pub parameter_grades: Vec<Option<Grade>>,
    pub result: Type,
    pub result_grade: Option<Grade>,
}
/// A checked borrowed call on a closed-world union object. Dispatch reads the
/// union tag through the stored reference and passes the payload pointer to the
/// selected member method in place, so an owning or linear member is never
/// copied. `members` is the checked tag/member/function table.
#[derive(Debug, Clone)]
pub(crate) struct UnionCallSpec {
    pub mode: ReceiverMode,
    pub parameter_grades: Vec<Option<Grade>>,
    pub result: Type,
    pub result_grade: Option<Grade>,
    pub members: Vec<(usize, Type, usize)>,
}
/// The checked contract of one object-safe trait method, after `Self` and the
/// trait arguments are substituted and associated projections are normalized.
#[derive(Debug, Clone)]
struct DynMethodContract {
    mode: ReceiverMode,
    parameters: Vec<Type>,
    parameter_grades: Vec<Option<Grade>>,
    result: Type,
    result_grade: Option<Grade>,
    effects: u16,
    /// The expression type observed by the caller; a `@[0]` result is erased.
    value_type: Type,
}
/// Concrete method type/grade/natural/effect arguments selected at one dynamic
/// call site. Vectors are in declaration order among parameters of each
/// category, exactly like a function instance key.
#[derive(Debug, Clone, Default)]
struct MethodArguments {
    types: Vec<Type>,
    consts: Vec<usize>,
    grades: Vec<Grade>,
    effects: Vec<u16>,
}
#[derive(Debug, Clone, Copy)]
pub(crate) enum Target {
    /// Consumes an owned code graph and returns a fallible compiled owner.
    StageCompile(ResultShape),
    /// Private load of an owner-bound entry; emitted only inside Code.call.
    StageEntry(usize),
    Io(IoOp, Option<ResultShape>),
    /// Checked host operation (filesystem, environment, clock, process, or
    /// network). Every operation returns `Result<T, i64>`; error payloads are
    /// positive Linux errno values.
    Host(HostOp, ResultShape),
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
    /// User-allocator-backed vector operation with its element type.
    AllocVec(AllocVecOp, Type),
    Function(usize),
    /// A direct call to a checked `foreign "symbol" fn` import. The index is
    /// the imported function's instance; the native backend emits a C ABI call
    /// and the reference interpreter rejects it explicitly.
    Foreign(usize),
    /// A call on an open/generic trait object. `spec` indexes
    /// `Executable::dyn_calls`; the receiver is the owned fat object or a
    /// one-word reference to it.
    DynCall {
        spec: usize,
    },
    /// An in-place borrowed call on a closed-world union object.
    UnionBorrowCall {
        spec: usize,
    },
    Print,
    /// Print any fixed-width integer in decimal.
    PrintInt(crate::int::IntKind),
    /// Print an `f32`/`f64` as its shortest round-trip decimal.
    PrintFloat(crate::float::FloatKind),
    /// Explicit integer builtin: operation, source kind, target kind.
    Int(crate::int::IntOp, crate::int::IntKind, crate::int::IntKind),
    /// THREAD-CHANNELS: `Channel.new(capacity)`; the call's type
    /// `Channel<T>` gives the message width.
    ChannelNew,
    /// Explicit float builtin or conversion.
    Float(crate::float::FloatOp),
    Panic,
    /// GPU-SUBSET: `GpuBuf.len/get/set` inside a `#[gpu]` function, with the
    /// element type. The first argument is the `&GpuBuf<T>` or
    /// `&mut GpuBuf<T>` entry parameter; only the GPU backend lowers it.
    #[allow(dead_code)] // read by the GPU backend (GPU-WGSL-EMIT)
    Gpu(GpuOp, Type),
}
/// GPU-SUBSET: device-side buffer operations (docs/gpu.md).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum GpuOp {
    /// `GpuBuf.len(b) -> u32`.
    Len,
    /// `GpuBuf.get(b, i) -> T`; panics out of range.
    Get,
    /// `GpuBuf.set(b, i, v)` through `&mut GpuBuf<T>`; panics out of range.
    Set,
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
/// Successful payload of a checked host operation. `Bytes` operations
/// preserve the storage of the owned buffer they consume; `I64` operations
/// report a count, flag, clock value, or child exit status; `Unit` reports
/// plain success.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HostPayload {
    Bytes,
    Bool,
    I64,
    Unit,
}
/// Checked synchronous host operations. Every native entry point has the same
/// shape: `int64_t f(..., uint64_t *out)` returns zero on success or a positive
/// Linux errno on failure, and writes the success payload through `out`.
/// Borrowed `&Bytes` parameters arrive as pointers to the caller's buffer
/// handle; owned `Bytes` parameters arrive as the handle itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum HostOp {
    FsRead,
    FsWrite,
    FsWriteExclusive,
    FsAppend,
    FsRemove,
    FsRename,
    FsMkdir,
    FsRemoveDir,
    FsList,
    FsIsFile,
    FsIsDir,
    FsSize,
    FsExists,
    FsOpen,
    FsReadAt,
    FsWriteAt,
    FsSync,
    FsTruncate,
    FsFileSize,
    FsClose,
    FsSyncDir,
    EnvArgCount,
    EnvArg,
    EnvVarCount,
    EnvVar,
    TimeUnixSeconds,
    TimeMonotonicNs,
    TimeSleepMs,
    ProcRun,
    NetTcpExchange,
    OsStrerror,
}
impl HostOp {
    pub fn named(name: &str) -> Option<Self> {
        match name {
            "FS.read" => Some(Self::FsRead),
            "FS.write" => Some(Self::FsWrite),
            "FS.write_exclusive" => Some(Self::FsWriteExclusive),
            "FS.append" => Some(Self::FsAppend),
            "FS.remove" => Some(Self::FsRemove),
            "FS.rename" => Some(Self::FsRename),
            "FS.mkdir" => Some(Self::FsMkdir),
            "FS.remove_dir" => Some(Self::FsRemoveDir),
            "FS.list" => Some(Self::FsList),
            "FS.is_file" => Some(Self::FsIsFile),
            "FS.is_dir" => Some(Self::FsIsDir),
            "FS.size" => Some(Self::FsSize),
            "FS.exists" => Some(Self::FsExists),
            "FS.open" => Some(Self::FsOpen),
            "FS.read_at" => Some(Self::FsReadAt),
            "FS.write_at" => Some(Self::FsWriteAt),
            "FS.sync" => Some(Self::FsSync),
            "FS.truncate" => Some(Self::FsTruncate),
            "FS.file_size" => Some(Self::FsFileSize),
            "FS.close" => Some(Self::FsClose),
            "FS.sync_dir" => Some(Self::FsSyncDir),
            "ENV.arg_count" => Some(Self::EnvArgCount),
            "ENV.arg" => Some(Self::EnvArg),
            "ENV.var_count" => Some(Self::EnvVarCount),
            "ENV.var" => Some(Self::EnvVar),
            "TIME.unix_seconds" => Some(Self::TimeUnixSeconds),
            "TIME.monotonic_ns" => Some(Self::TimeMonotonicNs),
            "TIME.sleep_ms" => Some(Self::TimeSleepMs),
            "PROC.run" => Some(Self::ProcRun),
            "NET.tcp_exchange" => Some(Self::NetTcpExchange),
            "OS.strerror" => Some(Self::OsStrerror),
            _ => None,
        }
    }
    pub fn symbol(self) -> &'static str {
        match self {
            Self::FsRead => "kush_fs_read",
            Self::FsWrite => "kush_fs_write",
            Self::FsWriteExclusive => "kush_fs_write_exclusive",
            Self::FsAppend => "kush_fs_append",
            Self::FsRemove => "kush_fs_remove",
            Self::FsRename => "kush_fs_rename",
            Self::FsMkdir => "kush_fs_mkdir",
            Self::FsRemoveDir => "kush_fs_remove_dir",
            Self::FsList => "kush_fs_list",
            Self::FsIsFile => "kush_fs_is_file",
            Self::FsIsDir => "kush_fs_is_dir",
            Self::FsSize => "kush_fs_size",
            Self::FsExists => "kush_fs_exists",
            Self::FsOpen => "kush_fs_open",
            Self::FsReadAt => "kush_fs_read_at",
            Self::FsWriteAt => "kush_fs_write_at",
            Self::FsSync => "kush_fs_sync",
            Self::FsTruncate => "kush_fs_truncate",
            Self::FsFileSize => "kush_fs_file_size",
            Self::FsClose => "kush_fs_close",
            Self::FsSyncDir => "kush_fs_sync_dir",
            Self::EnvArgCount => "kush_env_arg_count",
            Self::EnvArg => "kush_env_arg",
            Self::EnvVarCount => "kush_env_var_count",
            Self::EnvVar => "kush_env_var",
            Self::TimeUnixSeconds => "kush_time_unix_seconds",
            Self::TimeMonotonicNs => "kush_time_monotonic_ns",
            Self::TimeSleepMs => "kush_time_sleep_ms",
            Self::ProcRun => "kush_proc_run",
            Self::NetTcpExchange => "kush_net_tcp_exchange",
            Self::OsStrerror => "kush_os_strerror",
        }
    }
    /// Number of source-level arguments, excluding the native out-pointer.
    pub fn arity(self) -> usize {
        match self {
            Self::FsRead | Self::FsList => 2,
            Self::FsWrite | Self::FsWriteExclusive | Self::FsAppend | Self::FsRename => 2,
            Self::EnvArg => 2,
            Self::EnvVar => 2,
            Self::OsStrerror => 2,
            Self::ProcRun => 4,
            Self::NetTcpExchange => 5,
            Self::FsOpen | Self::FsTruncate => 2,
            Self::FsReadAt => 4,
            Self::FsWriteAt => 3,
            Self::FsSync | Self::FsFileSize | Self::FsClose | Self::FsSyncDir => 1,
            Self::EnvArgCount
            | Self::EnvVarCount
            | Self::TimeUnixSeconds
            | Self::TimeMonotonicNs => 0,
            Self::TimeSleepMs => 1,
            Self::FsRemove
            | Self::FsMkdir
            | Self::FsRemoveDir
            | Self::FsIsFile
            | Self::FsIsDir
            | Self::FsSize
            | Self::FsExists => 1,
        }
    }
    /// Which source arguments are borrowed `&Bytes` handles. The native
    /// lowering loads the buffer handle from these pointer words.
    pub fn borrowed(self) -> &'static [bool] {
        match self {
            Self::FsRead | Self::FsList => &[true, false],
            Self::FsWrite | Self::FsWriteExclusive | Self::FsAppend | Self::FsRename => {
                &[true, true]
            }
            Self::FsRemove
            | Self::FsMkdir
            | Self::FsRemoveDir
            | Self::FsIsFile
            | Self::FsIsDir
            | Self::FsSize
            | Self::FsExists => &[true],
            Self::EnvArg => &[false, false],
            Self::EnvVar => &[true, false],
            Self::OsStrerror => &[false, false],
            Self::ProcRun => &[true, true, true, false],
            Self::NetTcpExchange => &[true, false, true, true, false],
            Self::FsOpen => &[true, false],
            Self::FsReadAt => &[false, false, false, false],
            Self::FsWriteAt => &[false, false, true],
            Self::FsTruncate => &[false, false],
            Self::FsSync | Self::FsFileSize | Self::FsClose => &[false],
            Self::FsSyncDir => &[true],
            Self::EnvArgCount
            | Self::EnvVarCount
            | Self::TimeUnixSeconds
            | Self::TimeMonotonicNs
            | Self::TimeSleepMs => &[],
        }
    }
    /// Builtins over raw descriptor numbers, callable only from std.
    pub fn raw_handle(self) -> bool {
        matches!(
            self,
            Self::FsOpen
                | Self::FsReadAt
                | Self::FsWriteAt
                | Self::FsSync
                | Self::FsTruncate
                | Self::FsFileSize
                | Self::FsClose
        )
    }
    pub fn payload(self) -> HostPayload {
        match self {
            Self::FsRead
            | Self::FsList
            | Self::FsReadAt
            | Self::EnvArg
            | Self::EnvVar
            | Self::OsStrerror => HostPayload::Bytes,
            Self::FsRemove
            | Self::FsRename
            | Self::FsMkdir
            | Self::FsRemoveDir
            | Self::FsSync
            | Self::FsTruncate
            | Self::FsClose
            | Self::FsSyncDir
            | Self::TimeSleepMs => HostPayload::Unit,
            Self::FsIsFile | Self::FsIsDir | Self::FsExists => HostPayload::Bool,
            _ => HostPayload::I64,
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
    /// ASCII letters of an exclusive view to upper case; other bytes
    /// (including every byte of a multi-byte scalar) are unchanged.
    AsciiUpper,
    /// ASCII letters of an exclusive view to lower case.
    AsciiLower,
    /// Replace the scalar at a byte offset with a same-width scalar; panics
    /// on a non-boundary offset or a width mismatch.
    SetScalar,
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
    /// The same mutations through an exclusive `&mut Vec<T>` receiver. The
    /// caller keeps ownership; a growth updates the handle in the caller's
    /// slot, and the call evaluates to Unit.
    PushBorrowed,
    SetBorrowed,
    ClearBorrowed,
    ReserveBorrowed,
    /// `Vec.replace(&mut place, new)`: store `new` in the place and return
    /// the vector it held, moving both handles (no element is copied).
    ReplaceBorrowed,
    /// `SetBorrowed` of a copyable element whose index was proved in bounds:
    /// an inline store with no check.
    SetProved,
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
    /// THREAD-ATOMICS: sequentially consistent operations on an element of a
    /// `&[Atomic]` view (shared or exclusive); each panics out of bounds.
    AtomicLoad,
    AtomicStore,
    AtomicFetchAdd,
    AtomicSwap,
    /// `(view, index, expected, new)`: true when the element was `expected`.
    AtomicCompareExchange,
    /// THREAD-CHANNELS on an element of a `&[Channel<T>]` view: send blocks
    /// while the channel is full (panics once closed); receive blocks while
    /// it is empty and open, and yields `Option<T>` (`None` once closed and
    /// drained); close wakes every waiter.
    ChannelSend,
    ChannelRecv {
        some_tag: usize,
        none_tag: usize,
        option: usize,
    },
    ChannelClose,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum AllocVecOp {
    /// Live element count.
    Len,
    /// Checked element read; copies a copyable element.
    Get,
    /// Append one element, growing the allocator-supplied block if needed.
    Push,
    /// Fallible append. Growth uses a fresh allocation and reports refusal
    /// instead of panicking; a refused call returns the unchanged vector and
    /// the untouched element.
    TryPush,
    /// Remove and return the last live element as `(vector, element)`.
    /// Copyable elements only, so the removed value cannot duplicate an owner.
    Pop,
    /// Overwrite one live slot, dropping the previous element exactly once.
    Set,
    /// Drop every element and retain the block and metadata.
    Clear,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum DynArrayOp {
    /// Runtime length stored in word zero.
    Len,
    /// Checked element read; bounds are checked against the runtime length.
    Get,
}

#[derive(Debug, Clone)]
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
    /// Borrow a temporary owner at its source evaluation point. The slot is
    /// declared by `Statement::Declare`; `value` initializes it exactly where
    /// the borrowed aggregate appears, then the expression yields the same
    /// reference `Borrow(slot)` would. This keeps argument, field, index,
    /// branch, and short-circuit order while the hidden storage keeps the
    /// referent alive until every checked use.
    BorrowInit {
        slot: usize,
        value: Box<Expr>,
    },
    /// A checked reference to an addressable place: a record field chain, an
    /// inline-array element, or a vector element. Unlike `Borrow`, which names
    /// one direct local binding, the operand is a place expression whose
    /// storage lives in its root owner. The reference is one word and owns
    /// nothing; the root binding stays loaned until the reference's checked
    /// last use.
    BorrowPlace(Box<Expr>),
    /// A place index: the address of one element of an inline array or of a
    /// checked `Vec<T>` local/field. It is only ever produced as the operand
    /// of `BorrowPlace`; evaluating it as a value would require a reference
    /// type. The index is checked once at reference creation and panics when
    /// out of bounds.
    PlaceIndex {
        base: Box<Expr>,
        index: Box<Expr>,
        /// Checker identity of this place (nonzero, unique per checked
        /// function body). `Function::index_relations` refers to it.
        id: usize,
    },
    BoxNew(Box<Expr>),
    BoxTake(Box<Expr>),
    BoxRead(Box<Expr>),
    /// Write a non-owning payload through an exclusive `&mut Box<T>` receiver.
    /// The allocation and its capacity are retained; the old payload is a
    /// reference or copyable scalar, so no owner is dropped.
    BoxWrite(Box<Expr>, Box<Expr>),
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
    /// Create a region whose chunk sizing is chosen by the supplied pure
    /// `fn(need, current_capacity) -> capacity` strategy. The strategy is a
    /// noncapturing function pointer, so the region never owns a dangling
    /// environment.
    ArenaNewWith {
        strategy: Box<Expr>,
    },
    /// Allocate `value` in the borrowed arena. The returned box retains the
    /// region until its payload has been dropped.
    ArenaAlloc {
        arena: Box<Expr>,
        value: Box<Expr>,
    },
    /// Fallible arena allocation. `Ok` carries an `ArenaBox<T>` and one region
    /// reference; `Err` returns the untouched payload. A refused chunk request
    /// leaves the region's references, chunks, and current bump position
    /// unchanged.
    ArenaTryAlloc {
        arena: Box<Expr>,
        value: Box<Expr>,
        shape: ResultShape,
    },
    /// Create a user-defined allocator value from noncapturing functions:
    /// `alloc(bytes) -> Bytes` supplies a block with at least that capacity, and
    /// `free(block)` releases it. The value is copyable and owns nothing.
    AllocatorNew {
        alloc: Box<Expr>,
        free: Box<Expr>,
        /// Optional `fn(Bytes, i64) -> Bytes` growth hook used by `AllocVec`
        /// when it must move an existing block. `None` falls back to the
        /// allocate-copy-release path.
        realloc: Option<Box<Expr>>,
    },
    /// Create an owning allocator context from one concrete
    /// `AllocatorProtocol` instance. The instance value is moved into
    /// compiler-owned reference-counted storage together with checked thunks
    /// for its three protocol methods. `spec` indexes
    /// `Executable::allocator_contexts`.
    AllocatorContextNew {
        value: Box<Expr>,
        spec: usize,
    },
    /// Add one reference to an allocator context. The context is affine, so
    /// sharing is an explicit checked operation rather than an implicit copy.
    AllocatorContextShare(Box<Expr>),
    /// Allocate `value` in a block supplied by the allocator. The box stores
    /// the allocator pair so release always uses the same allocator, even if
    /// the allocator binding is dropped or moved first.
    AllocBoxNew {
        allocator: Box<Expr>,
        value: Box<Expr>,
    },
    /// Fallible user-allocator box construction. A block smaller than the
    /// payload (including an empty block) is a refusal and returns the
    /// untouched payload in `Err`.
    AllocBoxTryNew {
        allocator: Box<Expr>,
        value: Box<Expr>,
        shape: ResultShape,
    },
    /// Read a copyable payload through `&AllocBox<T>`.
    AllocBoxRead(Box<Expr>),
    /// Move a payload out of an owning `AllocBox<T>` and release its block
    /// through the stored allocator.
    AllocBoxTake(Box<Expr>),
    /// Create an allocator-backed vector. `capacity` is absent for zero
    /// initial capacity and present for `AllocVec.with_capacity`.
    AllocVecNew {
        allocator: Box<Expr>,
        capacity: Option<Box<Expr>>,
        element: Type,
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
    /// Structural record equality. Both operands are evaluated exactly once
    /// and compared field by field; only copyable, non-owning, non-float leaf
    /// fields are admitted. `negated` implements `!=`.
    StructEq {
        left: Box<Expr>,
        right: Box<Expr>,
        negated: bool,
    },
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
    /// Replace the referent of a user-visible `*p = value`. The old affine
    /// (non-linear) payload is destroyed exactly once before the new value is
    /// stored. Owning handles use their dedicated operations instead.
    DerefWrite(Box<Expr>, Box<Expr>),
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
        /// THREAD-SCOPE: `Thread.spawn`, run on its own OS thread.
        parallel: bool,
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
        /// PANIC-UNWIND-USE: `Task.catch`. The scope is also a catch
        /// boundary: its value is `Ok(body)`, or `Err(Panic {})` when a panic
        /// unwound out of the body (`Result<T, Panic>`, this shape).
        catch: Option<crate::runtime_types::ResultShape>,
        /// THREAD-SCOPE: `Thread.scope`, whose epilogue joins child threads.
        parallel: bool,
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
        /// THREAD-SCOPE: `Thread.join`, whose value is the payload itself (a
        /// thread is never cancelled); `exit` still describes the payload.
        parallel: bool,
    },
    /// In-place vector transform. `callbacks` are applied left-to-right to
    /// every element; their signatures determine the intermediate layouts.
    /// The final `target` must be no wider than `source` unless `grow` is set,
    /// in which case the allocation may be grown/moved under `{alloc, panic}`.
    /// A checked fusion may contain two pure callback steps.
    VecMap {
        vector: Box<Expr>,
        callbacks: Vec<Expr>,
        source: Type,
        target: Type,
        grow: bool,
    },
    /// Construct an empty runtime-sized inline array with zeroed capacity.
    DynArrayNew {
        element: Type,
        capacity: usize,
    },
    /// Push a handler value on the dynamic one-shot handler stack for
    /// the duration of `body`. Direct lexical `perform` lowering is unchanged;
    /// the stack entry lets a called function resolve the same operation.
    HandlerPush {
        operation: usize,
        handler: Box<Expr>,
        body: Box<Block>,
        /// A capturing handler whose captures are all copyable: the frame
        /// keeps its environment and each perform calls a fresh copy, so it
        /// serves any number of performs (stateful front ends write through
        /// by-reference captures).
        reusable: bool,
    },
    /// `perform` resolved through the dynamic handler stack. The handler
    /// contract is pure; a copyable function is reusable, while a capturing
    /// once handler transfers its owned environment on the first lookup.
    DynamicPerform {
        operation: usize,
        payload: Box<Expr>,
        resume: Box<Expr>,
        handler: usize,
    },
    /// A handled body whose handler is not statically tail-resumptive and
    /// that performs its operation outside the body's tail. Produced by the
    /// checker and checked by ownership and grades in this structured form;
    /// `crate::suspend::lower` replaces it by a `Region` plus one continuation
    /// closure per suspension point (see `docs/effect-state-machines.md`).
    Suspendable(Box<Suspendable>),
    /// One suspension point of the innermost enclosing `Suspendable`. It has
    /// the operation result type and, after the checker's ANF step, is always
    /// the whole value of a `let`, an expression statement, or a block tail.
    /// `call` is the handler call `CallIndirect(handler, [payload,
    /// Erased(token)])`, so ownership and grades check a suspension exactly
    /// like a call of the handler; the lowering supplies the real token.
    ///
    /// `callee` is set for an await point: `call` is a direct call of a
    /// function that may perform the handled declared operation, and the
    /// lowering calls that function's resumable entry instead.
    Suspend {
        point: usize,
        call: Box<Expr>,
        callee: Option<usize>,
        /// For an await point that passes a capability: the callee's `cap`
        /// parameter index, which keys its resumable entry instead of the
        /// handled operation (EFF-CAP-RESUME-CALLS).
        capability: Option<usize>,
    },
    /// Lowered form only: a block that `RegionExit` can leave from any depth.
    /// A normal completion yields the body value, applied to `finish` when
    /// present. An exit pops the dynamic handler frames installed inside.
    Region {
        body: Block,
        finish: Option<Box<Expr>>,
    },
    /// Lowered form only: evaluate `value`, drop the active resources listed
    /// in `cleanup`, pop handler frames installed inside the region, and leave
    /// the innermost `Region` with the value (applied to its `finish` when
    /// `finish` is set).
    RegionExit {
        value: Box<Expr>,
        finish: bool,
        cleanup: Vec<usize>,
    },
    /// An abortive `handle` (E-ABORT-LEXICAL, docs/abortive-handlers.md):
    /// run `body`; an `AbortExit` with this `label` leaves it with a payload,
    /// and the scope's value is then `handler(payload)`. `handler` is a
    /// callable evaluated only on that path.
    AbortScope {
        label: usize,
        body: Block,
        handler: Box<Expr>,
        /// A declared operation: the scope also pushes a dynamic handler frame
        /// so called functions can abort to it (E-ABORT-PROPAGATE).
        operation: Option<usize>,
    },
    /// `perform F(value)` of a declared abortive operation with no enclosing
    /// abortive scope in this function: find the innermost dynamic frame for
    /// `F`, hand it the payload, and leave this function like `return` (every
    /// live value is dropped). A missing handler aborts the program. Type
    /// `Never`.
    AbortPerform {
        operation: usize,
        value: Box<Expr>,
    },
    /// A call that may abort (E-ABORT-PROPAGATE). After `call` returns, a set
    /// abort word names a handle activation: if it is one of the enclosing
    /// scopes in `exits` (label, cleanup filled by ownership), leave to it;
    /// otherwise, when `propagates`, leave this function like `return`.
    AbortCall {
        call: Box<Expr>,
        exits: Vec<(usize, Vec<usize>)>,
        propagates: bool,
    },
    /// `perform F(value)` of an abortive operation whose `AbortScope` `label`
    /// encloses it in the same function: evaluate `value`, drop `cleanup`
    /// (filled by the ownership pass, like `break`), pop dynamic handler
    /// frames installed inside the scope, and leave it. Type `Never`.
    AbortExit {
        label: usize,
        value: Box<Expr>,
        cleanup: Vec<usize>,
        /// The scope's declared operation. After lowering, an exit that a
        /// continuation function carries away from its scope becomes an
        /// `AbortPerform` of it (E-ABORT-INTERACT).
        operation: Option<usize>,
    },
    /// Lowered form only: the current depth of the dynamic handler stack.
    HandlerDepth,
    /// Lowered form only: run `body` (a multishot `handle` whose tokens are
    /// `multi fn`) and release whatever it pushed on the continuation stack
    /// (docs/multishot-capabilities.md section 6.2).
    ContinuationScope {
        body: Block,
    },
    /// Lowered form only: run `body` with dynamic handler lookups that skip
    /// the frames above `depth` that were pushed before entering it. A
    /// resumed continuation of a declared-operation handle uses it so that
    /// frames its handler pushed around `resume` stay invisible (deep
    /// semantics). A redirect frame is pushed only when such frames exist.
    HandlerRedirect {
        depth: Box<Expr>,
        body: Block,
    },
    /// Lowered form only: `?` inside a resumable function entry. The `Err`
    /// path leaves the innermost `Region` through its finish (the caller's
    /// continuation) instead of returning, dropping `cleanup` first.
    TryExit {
        value: Box<Expr>,
        input: ResultShape,
        output: ResultShape,
        cleanup: Vec<usize>,
    },
    /// Append one element, consuming and returning the same inline storage.
    /// The runtime length check panics before any out-of-capacity store.
    DynArrayPush {
        array: Box<Expr>,
        value: Box<Expr>,
        element: Type,
        capacity: usize,
    },
    /// Construct a runtime-length array `[T; n <= C]`: evaluate the length,
    /// then one copyable element, and store it in the first `length` slots.
    /// `check` requests the runtime `0 <= length <= capacity` guard; it is
    /// off when the bound was proved from facts.
    DynArrayFill {
        length: Box<Expr>,
        value: Box<Expr>,
        element: Type,
        capacity: usize,
        check: bool,
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
    /// Elementwise equality of two runtime-sized inline arrays. Both operands
    /// are read, never moved. Comparable one-word elements (integers, floats,
    /// `Bool`, and `Char`) are compared with their ordinary `==`; a length
    /// mismatch is unequal without reading any slot.
    DynArrayEqual {
        left: Box<Expr>,
        right: Box<Expr>,
        element: Type,
        capacity: usize,
        negate: bool,
    },
    /// Read a local without moving it (only to project copyable fields).
    Peek(usize),
    /// Initialize hidden backing storage for a temporary owner at the
    /// expression's source evaluation point, then behave as `Peek(slot)`.
    ///
    /// The slot itself is declared by `Statement::Declare` in the enclosing
    /// lexical block, so storage and cleanup outlive every checked borrow even
    /// though the initializer's effects stay in source order (inside a
    /// short-circuit operand, loop condition, or branch). Re-initializing the
    /// slot drops the previous owner first, which keeps repeated loop
    /// evaluation balanced.
    InitOwner {
        slot: usize,
        value: Box<Expr>,
    },
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
        /// A view directly over a `DynArray` field of a record place: the
        /// field index path from the record root. The descriptor aliases the
        /// live inline storage inside the pinned record, so writes through an
        /// exclusive view update the record field in place.
        field: Option<Vec<usize>>,
    },
    While(Box<Expr>, Block),
    Loop(Block),
    /// Leave the innermost loop. The list names resources owned by scopes
    /// inside the loop that must be cleaned up (filled by the ownership pass).
    Break(Option<Box<Expr>>, Vec<usize>),
    Continue(Vec<usize>),
}
/// The checked description of a suspendable handled body.
#[derive(Debug, Clone)]
pub(crate) struct Suspendable {
    /// The handler's function when it is a noncapturing lambda or function
    /// name; multishot resumption with captured values specializes it.
    pub handler_function: Option<usize>,
    /// The declared operation id when the handled operation is declared;
    /// calls of functions that may perform it are await points.
    pub operation: Option<usize>,
    /// Operation result type, which is also the body result type.
    pub result: Type,
    /// The resumption token type handed to the handler.
    pub token: Type,
    pub multishot: bool,
    /// Scalar locals the handler can write through a by-reference capture.
    pub handler_writes: Vec<usize>,
    /// Locals the handler captures by reference; continuation code must
    /// not write them, since the handler would read the original.
    pub handler_refs: Vec<usize>,
    /// Effect row available at the handle site.
    pub effects: u16,
    pub body: Block,
    pub span: Span,
}
#[derive(Debug, Clone)]
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
impl Expr {
    /// Visit every direct child expression, expanding blocks into their
    /// statements and tail. The match is exhaustive on purpose: a new
    /// expression kind must decide here which children it has, so analyses
    /// built on this walk cannot silently skip a position.
    pub(crate) fn for_each_child<'a>(&'a self, f: &mut dyn FnMut(&'a Expr)) {
        fn block<'a>(b: &'a Block, f: &mut dyn FnMut(&'a Expr)) {
            for statement in &b.statements {
                match statement {
                    Statement::Let(_, value) | Statement::Expr(value) => f(value),
                    Statement::Declare(_) => {}
                }
            }
            if let Some(tail) = &b.tail {
                f(tail);
            }
        }
        match &self.kind {
            ExprKind::Constant(_)
            | ExprKind::BytesLiteral(_)
            | ExprKind::Erased(_)
            | ExprKind::Local(_)
            | ExprKind::Move(_)
            | ExprKind::Borrow(_)
            | ExprKind::Peek(_)
            | ExprKind::ArenaNew
            | ExprKind::TaskYield
            | ExprKind::HandlerDepth
            | ExprKind::TaskCheckCancel
            | ExprKind::DynArrayNew { .. }
            | ExprKind::Break(None, _)
            | ExprKind::Continue(_) => {}
            ExprKind::Coerce { value, .. }
            | ExprKind::Try { value, .. }
            | ExprKind::BoxNew(value)
            | ExprKind::BoxTake(value)
            | ExprKind::BoxRead(value)
            | ExprKind::BoxTryNew { value, .. }
            | ExprKind::BytesTryWithCapacity {
                capacity: value, ..
            }
            | ExprKind::ArenaNewWith { strategy: value }
            | ExprKind::AllocBoxRead(value)
            | ExprKind::AllocBoxTake(value)
            | ExprKind::ArenaBoxRead(value)
            | ExprKind::ArenaBoxTake(value)
            | ExprKind::Drop(value)
            | ExprKind::Unary(_, value)
            | ExprKind::Assign(_, value)
            | ExprKind::RefRead(value)
            | ExprKind::Return(value)
            | ExprKind::TaskSpawn { body: value, .. }
            | ExprKind::TaskScope { body: value, .. }
            | ExprKind::TaskCancel(value)
            | ExprKind::TaskJoin { task: value, .. }
            | ExprKind::DynArrayPop { array: value, .. }
            | ExprKind::Project(value, _)
            | ExprKind::BorrowPlace(value)
            | ExprKind::InitOwner { value, .. }
            | ExprKind::BorrowInit { value, .. }
            | ExprKind::Break(Some(value), _) => f(value),
            ExprKind::PlaceIndex { base, index, .. } => {
                f(base);
                f(index);
            }
            ExprKind::BoxWrite(a, b)
            | ExprKind::DerefWrite(a, b)
            | ExprKind::BoxReuse {
                owner: a,
                payload: b,
            }
            | ExprKind::BoxReuseGrow {
                owner: a,
                payload: b,
            }
            | ExprKind::BoxTryReuse {
                owner: a,
                payload: b,
                ..
            }
            | ExprKind::ArenaAlloc { arena: a, value: b }
            | ExprKind::ArenaTryAlloc {
                arena: a, value: b, ..
            }
            | ExprKind::AllocBoxNew {
                allocator: a,
                value: b,
            }
            | ExprKind::AllocBoxTryNew {
                allocator: a,
                value: b,
                ..
            }
            | ExprKind::Binary(_, a, b)
            | ExprKind::StructEq {
                left: a, right: b, ..
            }
            | ExprKind::RefAssign(a, _, b)
            | ExprKind::DynamicPerform {
                payload: a,
                resume: b,
                ..
            }
            | ExprKind::DynArrayPush {
                array: a, value: b, ..
            }
            | ExprKind::DynArrayFill {
                length: a,
                value: b,
                ..
            }
            | ExprKind::DynArrayEqual {
                left: a, right: b, ..
            }
            | ExprKind::BytesAt(a, b) => {
                f(a);
                f(b);
            }
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                f(alloc);
                f(free);
                if let Some(realloc) = realloc {
                    f(realloc);
                }
            }
            ExprKind::AllocatorContextNew { value, .. }
            | ExprKind::AllocatorContextShare(value) => {
                f(value);
            }
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                ..
            } => {
                f(allocator);
                if let Some(capacity) = capacity {
                    f(capacity);
                }
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                f(array);
                f(index);
                f(value);
            }
            ExprKind::Construct { fields: items, .. }
            | ExprKind::Call(_, items)
            | ExprKind::FnValue {
                captures: items, ..
            } => {
                for item in items {
                    f(item);
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                f(callee);
                for argument in arguments {
                    f(argument);
                }
            }
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                f(vector);
                for callback in callbacks {
                    f(callback);
                }
            }
            ExprKind::Block(b) | ExprKind::Loop(b) => block(b, f),
            ExprKind::Suspendable(suspendable) => block(&suspendable.body, f),
            ExprKind::Suspend { call, .. } => f(call),
            ExprKind::Region { body, finish, .. } => {
                block(body, f);
                if let Some(finish) = finish {
                    f(finish);
                }
            }
            ExprKind::AbortScope { body, handler, .. } => {
                block(body, f);
                f(handler);
            }
            ExprKind::ContinuationScope { body } => block(body, f),
            ExprKind::RegionExit { value, .. }
            | ExprKind::TryExit { value, .. }
            | ExprKind::AbortExit { value, .. }
            | ExprKind::AbortPerform { value, .. }
            | ExprKind::AbortCall { call: value, .. } => f(value),
            ExprKind::HandlerRedirect { depth, body } => {
                f(depth);
                block(body, f);
            }
            ExprKind::If(condition, yes, no) => {
                f(condition);
                block(yes, f);
                block(no, f);
            }
            ExprKind::While(condition, body) => {
                f(condition);
                block(body, f);
            }
            ExprKind::Match(value, arms) => {
                f(value);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        f(guard);
                    }
                    f(&arm.body);
                }
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                f(handler);
                block(body, f);
            }
            ExprKind::Slice {
                base, start, end, ..
            } => {
                f(base);
                if let Some(start) = start {
                    f(start);
                }
                if let Some(end) = end {
                    f(end);
                }
            }
        }
    }
    /// Mutable twin of `for_each_child`; same children in the same order.
    pub(crate) fn for_each_child_mut(&mut self, f: &mut dyn FnMut(&mut Expr)) {
        fn block(b: &mut Block, f: &mut dyn FnMut(&mut Expr)) {
            for statement in &mut b.statements {
                match statement {
                    Statement::Let(_, value) | Statement::Expr(value) => f(value),
                    Statement::Declare(_) => {}
                }
            }
            if let Some(tail) = &mut b.tail {
                f(tail);
            }
        }
        match &mut self.kind {
            ExprKind::Constant(_)
            | ExprKind::BytesLiteral(_)
            | ExprKind::Erased(_)
            | ExprKind::Local(_)
            | ExprKind::Move(_)
            | ExprKind::Borrow(_)
            | ExprKind::Peek(_)
            | ExprKind::ArenaNew
            | ExprKind::TaskYield
            | ExprKind::HandlerDepth
            | ExprKind::TaskCheckCancel
            | ExprKind::DynArrayNew { .. }
            | ExprKind::Break(None, _)
            | ExprKind::Continue(_) => {}
            ExprKind::Coerce { value, .. }
            | ExprKind::Try { value, .. }
            | ExprKind::BoxNew(value)
            | ExprKind::BoxTake(value)
            | ExprKind::BoxRead(value)
            | ExprKind::BoxTryNew { value, .. }
            | ExprKind::BytesTryWithCapacity {
                capacity: value, ..
            }
            | ExprKind::ArenaNewWith { strategy: value }
            | ExprKind::AllocBoxRead(value)
            | ExprKind::AllocBoxTake(value)
            | ExprKind::ArenaBoxRead(value)
            | ExprKind::ArenaBoxTake(value)
            | ExprKind::Drop(value)
            | ExprKind::Unary(_, value)
            | ExprKind::Assign(_, value)
            | ExprKind::RefRead(value)
            | ExprKind::Return(value)
            | ExprKind::TaskSpawn { body: value, .. }
            | ExprKind::TaskScope { body: value, .. }
            | ExprKind::TaskCancel(value)
            | ExprKind::TaskJoin { task: value, .. }
            | ExprKind::DynArrayPop { array: value, .. }
            | ExprKind::Project(value, _)
            | ExprKind::BorrowPlace(value)
            | ExprKind::InitOwner { value, .. }
            | ExprKind::BorrowInit { value, .. }
            | ExprKind::Break(Some(value), _) => f(value),
            ExprKind::PlaceIndex { base, index, .. } => {
                f(base);
                f(index);
            }
            ExprKind::BoxWrite(a, b)
            | ExprKind::DerefWrite(a, b)
            | ExprKind::BoxReuse {
                owner: a,
                payload: b,
            }
            | ExprKind::BoxReuseGrow {
                owner: a,
                payload: b,
            }
            | ExprKind::BoxTryReuse {
                owner: a,
                payload: b,
                ..
            }
            | ExprKind::ArenaAlloc { arena: a, value: b }
            | ExprKind::ArenaTryAlloc {
                arena: a, value: b, ..
            }
            | ExprKind::AllocBoxNew {
                allocator: a,
                value: b,
            }
            | ExprKind::AllocBoxTryNew {
                allocator: a,
                value: b,
                ..
            }
            | ExprKind::Binary(_, a, b)
            | ExprKind::StructEq {
                left: a, right: b, ..
            }
            | ExprKind::RefAssign(a, _, b)
            | ExprKind::DynamicPerform {
                payload: a,
                resume: b,
                ..
            }
            | ExprKind::DynArrayPush {
                array: a, value: b, ..
            }
            | ExprKind::DynArrayFill {
                length: a,
                value: b,
                ..
            }
            | ExprKind::DynArrayEqual {
                left: a, right: b, ..
            }
            | ExprKind::BytesAt(a, b) => {
                f(a);
                f(b);
            }
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                f(alloc);
                f(free);
                if let Some(realloc) = realloc {
                    f(realloc);
                }
            }
            ExprKind::AllocatorContextNew { value, .. }
            | ExprKind::AllocatorContextShare(value) => {
                f(value);
            }
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                ..
            } => {
                f(allocator);
                if let Some(capacity) = capacity {
                    f(capacity);
                }
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                ..
            } => {
                f(array);
                f(index);
                f(value);
            }
            ExprKind::Construct { fields: items, .. }
            | ExprKind::Call(_, items)
            | ExprKind::FnValue {
                captures: items, ..
            } => {
                for item in items.iter_mut() {
                    f(item);
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                f(callee);
                for argument in arguments.iter_mut() {
                    f(argument);
                }
            }
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                f(vector);
                for callback in callbacks.iter_mut() {
                    f(callback);
                }
            }
            ExprKind::Block(b) | ExprKind::Loop(b) => block(b, f),
            ExprKind::Suspendable(suspendable) => block(&mut suspendable.body, f),
            ExprKind::Suspend { call, .. } => f(call),
            ExprKind::Region { body, finish, .. } => {
                block(body, f);
                if let Some(finish) = finish {
                    f(finish);
                }
            }
            ExprKind::AbortScope { body, handler, .. } => {
                block(body, f);
                f(handler);
            }
            ExprKind::ContinuationScope { body } => block(body, f),
            ExprKind::RegionExit { value, .. }
            | ExprKind::TryExit { value, .. }
            | ExprKind::AbortExit { value, .. }
            | ExprKind::AbortPerform { value, .. }
            | ExprKind::AbortCall { call: value, .. } => f(value),
            ExprKind::HandlerRedirect { depth, body } => {
                f(depth);
                block(body, f);
            }
            ExprKind::If(condition, yes, no) => {
                f(condition);
                block(yes, f);
                block(no, f);
            }
            ExprKind::While(condition, body) => {
                f(condition);
                block(body, f);
            }
            ExprKind::Match(value, arms) => {
                f(value);
                for arm in arms.iter_mut() {
                    if let Some(guard) = &mut arm.guard {
                        f(guard);
                    }
                    f(&mut arm.body);
                }
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                f(handler);
                block(body, f);
            }
            ExprKind::Slice {
                base, start, end, ..
            } => {
                f(base);
                if let Some(start) = start {
                    f(start);
                }
                if let Some(end) = end {
                    f(end);
                }
            }
        }
    }
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
    /// Store a concrete member in a dynamically dispatched trait-object
    /// payload. `member` is the registered runtime member identifier. The
    /// payload is allocated once and owned by the object value.
    DynBox { member: usize, member_type: Type },
    /// Upcast an owned multi-trait object to an object over a subset of its
    /// traits. The payload pointer is kept; the member identifier is mapped
    /// from `from`'s member table to `to`'s, where the checker registered
    /// every member of `from`.
    DynUpcast { from: usize, to: usize },
    /// Rebuild a callable field through a checked adapter function. Used by a
    /// structural conversion when a retained field's arrow changes
    /// representation. `capture` is the source callable type when the adapter
    /// needs its input in the closure environment; the source field is moved
    /// into that environment exactly once. `target` selects the output ABI
    /// (`Fn` or `Once`), so the runtime knows whether an environment word is
    /// part of the value.
    Callable {
        function: usize,
        capture: Option<Type>,
        target: Type,
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
        tagged: bool,
        niche: Option<crate::runtime_types::Niche>,
        fields: Vec<(usize, Pattern)>,
    },
    /// Match one normalized union alternative and apply `inner` to the
    /// narrowed payload. `member` is the runtime type of that payload.
    Type {
        tag: usize,
        member: Type,
        inner: Box<Pattern>,
    },
    /// A length-checked pattern over a runtime-sized inline array. `prefix`
    /// patterns match the leading live slots and `suffix` patterns the
    /// trailing ones; `rest` allows any length in between and `rest_binding`
    /// receives a copy of the middle as `DynArray<element, capacity>`. A
    /// suffix is only present with a rest. Elements must be copyable.
    DynArray {
        element: Type,
        capacity: usize,
        prefix: Vec<Pattern>,
        suffix: Vec<Pattern>,
        rest: bool,
        rest_binding: Option<usize>,
        /// A pattern over a shared `&DynArray` scrutinee. A top-level element
        /// `Bind` then binds `&T` to the element's slot and `rest_binding` a
        /// `&[T]` view of the middle; other element patterns test copies of
        /// copyable elements.
        borrowed: bool,
        /// For a `&mut DynArray` scrutinee: the first of one fresh split group
        /// per exclusive binding (element names then `..rest`, in order). Each
        /// binding takes the opposite side from every other binding, so the
        /// `&mut T` and `&mut [T]` bindings are pairwise disjoint loans.
        exclusive: Option<usize>,
    },
}
#[derive(Clone)]
struct Signature {
    /// Call-only types scope declared labels before caller rows are expanded.
    call_contract: Option<CallLifetimeContract>,
    binding: BindingId,
    name: String,
    /// Runtime parameter types, in order. Erased parameters are absent.
    parameters: Vec<Type>,
    result: Type,
    effects: u16,
    span: Span,
    /// Generic parameter binder -> concrete type, for specialized instances.
    substitution: BTreeMap<BindingId, Type>,
    /// Const natural binder -> compile-time value, for specialized instances.
    consts: BTreeMap<BindingId, usize>,
    /// Abstract grade binder -> concrete compile-time grade.
    grades: BTreeMap<BindingId, Grade>,
    /// Effect row binder -> concrete effect bitset for this instance.
    effect_arguments: BTreeMap<BindingId, u16>,
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
#[derive(Clone)]
struct CallLifetimeContract {
    parameters: Vec<Type>,
    result: Type,
    binders: BTreeSet<String>,
    names: BTreeMap<String, String>,
    bounds: BTreeSet<(String, String)>,
}
impl Signature {
    fn scope_call_lifetimes(&mut self) -> (BTreeSet<String>, BTreeMap<String, String>) {
        let Some(contract) = self.call_contract.take() else {
            return (BTreeSet::new(), BTreeMap::new());
        };
        self.parameters = contract.parameters;
        self.result = contract.result;
        self.lifetime_bounds = contract.bounds;
        (contract.binders, contract.names)
    }

    /// Whether logical runtime parameter `index` is physically erased by a
    /// grade-zero contract.
    fn parameter_erased(&self, index: usize) -> bool {
        crate::runtime_types::grade_erases(self.parameter_grades.get(index).copied().flatten())
    }
}
/// One checked `foreign "symbol" fn` import. The ABI classification is derived
/// from `parameters`/`result`; `fallible` is `Some` exactly when the declared
/// result is the conventional `Result<T, i64>`, in which case the C symbol
/// returns a status and writes `T` through a trailing out-pointer.
#[derive(Debug, Clone)]
pub(crate) struct ExportedFunction {
    pub symbol: String,
    pub index: usize,
    pub parameters: Vec<(String, Type)>,
    pub result: Type,
}
/// Public description of one `export "symbol" fn` (KUSH-RUST-EXPORT).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportInfo {
    pub symbol: String,
    pub name: String,
    /// Parameter names and Kush scalar type names (`i64`, `u8`, `Bool`, ...).
    pub parameters: Vec<(String, String)>,
    /// `Unit` or a scalar type name.
    pub result: String,
}
#[derive(Debug, Clone)]
pub(crate) struct ForeignFunction {
    pub symbol: String,
    pub parameters: Vec<Type>,
    pub result: Type,
    pub fallible: Option<ResultShape>,
}
/// Public, stable description of one checked foreign import, for build tooling
/// and generated adapters. It does not claim the foreign implementation is
/// verified: only the Kush-side signature, effects, and ownership are checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForeignFunctionInfo {
    pub name: String,
    pub symbol: String,
    pub parameters: Vec<String>,
    pub result: String,
    pub fallible: bool,
}
/// Allow only the stable C ABI bridge subset. Pointers, Rust enums with
/// payloads, owned text/buffers, and arbitrary aggregates are rejected here
/// rather than guessed at the backend.
fn foreign_value_supported(types: &Types<'_>, ty: Type) -> bool {
    match ty {
        Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_) | Type::Str => true,
        Type::Enum(id) => types.enums[id].foreign.is_some(),
        Type::Ref(pointer) => match types.pointees[pointer] {
            Type::Enum(id) => types.enums[id].foreign.is_some(),
            Type::Bytes | Type::String => true,
            _ => false,
        },
        _ => false,
    }
}
fn foreign_result_supported(types: &Types<'_>, ty: Type, error: bool) -> bool {
    if error {
        return ty == Type::I64;
    }
    match ty {
        Type::Unit | Type::Bytes | Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_) => true,
        Type::Enum(id) => types.enums[id].foreign.is_some(),
        _ => false,
    }
}
/// Validate the checked signature of a foreign declaration. The caller already
/// required a concrete, monomorphic, non-erased signature with `io` in its row.
///
/// `std_sys` marks a std-only `kush_sys_*` runtime stub, which may also take
/// an owned `Bytes` buffer (FOREIGN-BYTES-FILL): the stub appends into its
/// spare capacity and hands it back through a `Result<Bytes, i64>` out slot,
/// or frees it on failure, like the `FS.read_at` builtin.
#[allow(clippy::too_many_arguments)]
fn validate_foreign_function(
    types: &Types<'_>,
    std_sys: bool,
    parameters: &[Type],
    result: Type,
    result_shape: Option<ResultShape>,
    parameter_grades: &[Option<Grade>],
    result_grade: Option<Grade>,
    span: Span,
) -> Result<()> {
    if parameter_grades.iter().any(Option::is_some) || result_grade.is_some() {
        return Err(Diagnostic::new(
            span,
            "foreign functions cannot carry usage grades; use the owning result type for exactly-once transfer, or Result<T, i64> for checked failure",
        ));
    }
    for ty in parameters {
        if !foreign_value_supported(types, *ty) && !(std_sys && *ty == Type::Bytes) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "foreign parameter type {} is not part of the stable C bridge ABI; supported inputs are fixed-width integers, f32/f64, Bool, &str, &Bytes, &String, and declared foreign resources",
                    types.name(*ty)
                ),
            ));
        }
    }
    if let Some(shape) = result_shape {
        if !foreign_result_supported(types, shape.ok, false) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "foreign Result Ok type {} is not bridgeable; supported results are Unit, Bytes, fixed-width integers, f32/f64, Bool, and declared foreign resources",
                    types.name(shape.ok)
                ),
            ));
        }
        if !foreign_result_supported(types, shape.error, true) {
            return Err(Diagnostic::new(
                span,
                "a foreign Result must use i64 as its error type; the bridge returns a non-zero C status as Err(status)",
            ));
        }
    } else if !foreign_result_supported(types, result, false) {
        return Err(Diagnostic::new(
            span,
            format!(
                "foreign result type {} is not part of the stable C bridge ABI; return Unit, Bytes, a fixed-width integer, f32/f64, Bool, a declared foreign resource, or Result<T, i64>",
                types.name(result)
            ),
        ));
    }
    Ok(())
}
/// Split `T @[grade]` into the type and its grade expression.
pub(crate) fn split_grade(ty: &ast::Type) -> (&ast::Type, Option<&ast::Type>) {
    grades::split(ty)
}
/// Whether a name is a bare C symbol. Foreign declarations and resource release
/// hooks are passed to Cranelift and `cc` as arguments, never through a shell,
/// but restricting the spelling keeps diagnostics and generated C/Rust shims
/// predictable.
pub(crate) fn valid_c_symbol(name: &str) -> bool {
    let mut characters = name.chars();
    characters
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && characters.all(|character| character == '_' || character.is_ascii_alphanumeric())
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
        K::Structural { fields, .. } => fields
            .iter()
            .any(|field| type_mentions_binding(resolution, &field.ty, binder)),
        K::Dyn(bounds) => {
            ast::dyn_types(bounds).any(|inner| type_mentions_binding(resolution, inner, binder))
        }
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
        K::Capability { effects, .. } => effects
            .iter()
            .any(|effect| type_mentions_binding(resolution, effect, binder)),
        K::Integer(_) | K::Bool(_) | K::Lifetime(_) | K::SelfType | K::Infer | K::Predicate(_) => {
            false
        }
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
/// Reflexive-transitive closure of declared or inferred outlives edges.
fn close_lifetime_bounds(bounds: BTreeSet<(String, String)>) -> BTreeSet<(String, String)> {
    crate::lifetimes::LifetimeGraph::new(&bounds)
        .solve()
        .closure
}
fn borrow_lifetime(ty: &ast::Type) -> Option<String> {
    match &ty.kind {
        ast::TypeKind::Borrow { lifetime, .. } => lifetime.clone(),
        _ => None,
    }
}
/// Every lifetime name mentioned by a type, including nested borrows.
/// The first lifetime nested in a parameter's written type. A container such
/// as `&mut Vec<&'a T>` has an elided outer borrow lifetime but a concrete
/// element lifetime `'a`; the requirement mapper must use the element one.
fn nested_borrow_lifetime(ty: &ast::Type) -> Option<String> {
    match &ty.kind {
        ast::TypeKind::Borrow {
            lifetime, inner, ..
        } => lifetime.clone().or_else(|| nested_borrow_lifetime(inner)),
        ast::TypeKind::Lifetime(name) => Some(name.clone()),
        ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Slice(inner)
        | ast::TypeKind::Array(inner, _) => nested_borrow_lifetime(inner),
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
            arguments.iter().find_map(nested_borrow_lifetime)
        }
        _ => None,
    }
}
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
        ast::TypeKind::Structural { fields, .. } => {
            for field in fields {
                type_lifetimes(&field.ty, out);
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
        | ast::ExprKind::Cast { value: operand, .. }
        | ast::ExprKind::Is { value: operand, .. }
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
        ast::ExprKind::Record { ty, fields, base } => {
            collect_body_returns(ty, out);
            for (_, field) in fields {
                collect_body_returns(field, out);
            }
            if let Some(base) = base {
                collect_body_returns(base, out);
            }
        }
        ast::ExprKind::While {
            condition, body, ..
        } => {
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
/// A capability type `cap Op` is second-class: it is accepted only as the
/// whole type of a named function parameter. Anywhere else it is rejected.
fn reject_capability_type(ty: &ast::Type) -> Result<()> {
    let mut found = None;
    fn walk(ty: &ast::Type, found: &mut Option<Span>) {
        if found.is_some() {
            return;
        }
        match &ty.kind {
            ast::TypeKind::Capability { .. } => *found = Some(ty.span),
            ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
                arguments.iter().for_each(|argument| walk(argument, found));
            }
            ast::TypeKind::Slice(inner)
            | ast::TypeKind::Borrow { inner, .. }
            | ast::TypeKind::Graded { inner, .. } => walk(inner, found),
            ast::TypeKind::Array(inner, length) => {
                walk(inner, found);
                walk(length, found);
            }
            ast::TypeKind::Structural { fields, .. } => {
                fields.iter().for_each(|field| walk(&field.ty, found));
            }
            ast::TypeKind::Binary { left, right, .. } => {
                walk(left, found);
                walk(right, found);
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .for_each(|parameter| walk(&parameter.ty, found));
                walk(result, found);
            }
            ast::TypeKind::Dyn(bounds) => {
                crate::ast::dyn_types(bounds).for_each(|inner| walk(inner, found));
            }
            _ => {}
        }
    }
    walk(ty, &mut found);
    match found {
        Some(span) => Err(Diagnostic::new(
            span,
            "a capability type 'cap Op' is second-class: it is only allowed as the whole type of a named function parameter, never stored, returned, nested or used in a function value type",
        )),
        None => Ok(()),
    }
}
/// Reject capability types in declarations that store or name values.
/// FND-ROWS-INFER: only private free functions infer their row. A method's
/// row is part of its trait contract or of its type's interface.
fn reject_omitted_method_rows(module: &ast::Module) -> Result<()> {
    for declaration in &module.items {
        let (ast::ItemKind::Trait { methods, .. } | ast::ItemKind::Impl { methods, .. }) =
            &declaration.item.kind
        else {
            continue;
        };
        if let Some(method) = methods.iter().find(|method| method.function.row_omitted()) {
            return Err(Diagnostic::new(
                method.span,
                "a method declares its effect row; add '! {..}' after the result type",
            ));
        }
    }
    Ok(())
}
fn reject_stored_capabilities(module: &ast::Module) -> Result<()> {
    for declaration in &module.items {
        match &declaration.item.kind {
            ast::ItemKind::Struct { fields, .. } => {
                for field in fields {
                    reject_capability_type(&field.ty)?;
                }
            }
            ast::ItemKind::Enum { variants, .. } => {
                for variant in variants {
                    match &variant.payload {
                        ast::Payload::Unit => {}
                        ast::Payload::Tuple(types) => {
                            for ty in types {
                                reject_capability_type(ty)?;
                            }
                        }
                        ast::Payload::Fields(fields) | ast::Payload::Record(fields) => {
                            for field in fields {
                                reject_capability_type(&field.ty)?;
                            }
                        }
                    }
                }
            }
            ast::ItemKind::Alias { ty, .. } => reject_capability_type(ty)?,
            ast::ItemKind::Effect {
                parameter, result, ..
            } => {
                reject_capability_type(parameter)?;
                reject_capability_type(result)?;
            }
            ast::ItemKind::Function(function) => {
                reject_capability_type(&function.result)?;
                for effect in &function.effects {
                    reject_capability_type(effect)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}
/// Whether a lambda omits a parameter, result or effect annotation.
fn lambda_has_holes(lambda: &ast::Lambda) -> bool {
    matches!(lambda.result.kind, ast::TypeKind::Infer)
        || matches!(lambda.effects.as_slice(), [only] if matches!(only.kind, ast::TypeKind::Infer))
        || lambda
            .parameters
            .iter()
            .any(|parameter| matches!(parameter.ty.kind, ast::TypeKind::Infer))
}
/// Whether some expression of `block` (not inside a nested lambda) satisfies
/// `predicate`. Bounded by the AST size.
fn block_any(block: &ast::Block, predicate: &dyn Fn(&ast::ExprKind) -> bool) -> bool {
    let mut stack = Vec::new();
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } => stack.push(value),
            ast::Statement::Expr(expr) => stack.push(expr),
        }
    }
    stack.extend(block.tail.as_deref());
    while let Some(expr) = stack.pop() {
        if predicate(&expr.kind) {
            return true;
        }
        if !matches!(expr.kind, ast::ExprKind::Lambda(_)) {
            ast_children(expr, &mut |child| stack.push(child));
        }
    }
    false
}
/// Automatic fusion equivalence analysis.
///
/// A callback is eligible only when:
///
/// * it is a noncapturing `fn(...)` value;
/// * its declared effect row contains neither `io` nor `suspend`;
/// * its body has no operation that can panic (`fusion_may_panic`): since
///   FND-ROWS-PANIC a row no longer says so, and fusing two callbacks that
///   may panic would change which panic is reported;
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

/// FND-ROWS-PANIC: whether this node (not its children) may panic: checked
/// integer arithmetic and negation, range slicing, builtin operations (bounds,
/// capacity and infallible allocation), and fixed-capacity array writes.
/// Conservative: arithmetic the prover showed in range still counts, and
/// every builtin call is treated as able to panic.
fn fusion_may_panic(expr: &Expr) -> bool {
    use crate::lexer::Kind;
    let integer = expr.ty.float_kind().is_none();
    match &expr.kind {
        ExprKind::Binary(
            Kind::Plus
            | Kind::Minus
            | Kind::Star
            | Kind::Slash
            | Kind::Percent
            | Kind::Shl
            | Kind::Shr,
            _,
            _,
        ) => integer,
        ExprKind::Unary(Kind::Minus, _) => integer,
        ExprKind::Call(target, _) => !matches!(target, Target::Function(_)),
        ExprKind::Slice { .. }
        | ExprKind::BoxNew(_)
        | ExprKind::ArenaAlloc { .. }
        | ExprKind::DynArrayPush { .. }
        | ExprKind::DynArraySet { .. }
        | ExprKind::DynArrayPop { .. }
        | ExprKind::DynArrayFill { .. }
        | ExprKind::DynamicPerform { .. } => true,
        _ => false,
    }
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
        Statement::Declare(_) => true,
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
    if fusion_may_panic(expr) {
        return false;
    }
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
        ExprKind::RefRead(_)
        | ExprKind::DerefWrite(_, _)
        | ExprKind::BoxWrite(_, _)
        | ExprKind::BorrowPlace(_)
        | ExprKind::BorrowInit { .. }
        | ExprKind::InitOwner { .. }
        | ExprKind::PlaceIndex { .. } => false,
        // No loop has a checked termination argument here.
        ExprKind::While(..) | ExprKind::Loop(_) => false,
        ExprKind::Call(Target::Function(index), arguments) => {
            fusion_function_safe(*index, signatures, bodies, memo, visiting)
                && arguments
                    .iter()
                    .all(|argument| safe(argument, signatures, bodies, memo, visiting))
        }
        ExprKind::Call(
            Target::Io(..)
            | Target::Host(..)
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
        // Allocator construction only packages code pointers, so it is
        // inert; every container operation can invoke a user callback or
        // allocate, so it is never fusion-safe.
        ExprKind::AllocatorNew {
            alloc,
            free,
            realloc,
        } => {
            safe(alloc, signatures, bodies, memo, visiting)
                && safe(free, signatures, bodies, memo, visiting)
                && realloc
                    .as_deref()
                    .is_none_or(|realloc| safe(realloc, signatures, bodies, memo, visiting))
        }
        ExprKind::AllocBoxNew { .. }
        | ExprKind::AllocBoxTryNew { .. }
        | ExprKind::AllocBoxRead(_)
        | ExprKind::AllocBoxTake(_)
        | ExprKind::AllocVecNew { .. }
        // Building a context allocates compiler-owned storage and sharing
        // changes a reference count, so neither is an inert fusion stage.
        | ExprKind::AllocatorContextNew { .. }
        | ExprKind::AllocatorContextShare(_) => false,
        // A suspension runs arbitrary handler code.
        ExprKind::Suspendable(_)
        | ExprKind::Suspend { .. }
        | ExprKind::Region { .. }
        | ExprKind::RegionExit { .. }
        | ExprKind::HandlerDepth
        | ExprKind::HandlerRedirect { .. }
        | ExprKind::ContinuationScope { .. }
        | ExprKind::TryExit { .. }
        // An abort leaves code that a fused stage would have to resume.
        | ExprKind::AbortScope { .. }
        | ExprKind::AbortExit { .. }
        | ExprKind::AbortPerform { .. }
        | ExprKind::AbortCall { .. } => false,
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
        ExprKind::ArenaNewWith { strategy } => safe(strategy, signatures, bodies, memo, visiting),
        ExprKind::ArenaTryAlloc { arena, value, .. } => {
            safe(arena, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArrayPush { array, value, .. } => {
            safe(array, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArrayFill { length, value, .. } => {
            safe(length, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::HandlerPush { handler, body, .. } => {
            safe(handler, signatures, bodies, memo, visiting)
                && fusion_block_safe(body, signatures, bodies, memo, visiting)
        }
        ExprKind::DynamicPerform {
            payload, resume, ..
        } => {
            safe(payload, signatures, bodies, memo, visiting)
                && safe(resume, signatures, bodies, memo, visiting)
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
        ExprKind::Binary(_, left, right)
        | ExprKind::BytesAt(left, right)
        | ExprKind::StructEq { left, right, .. }
        | ExprKind::DynArrayEqual { left, right, .. } => {
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
            Statement::Declare(_) => {}
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
        | ExprKind::AllocBoxRead(value)
        | ExprKind::AllocBoxTake(value)
        | ExprKind::BytesTryWithCapacity {
            capacity: value, ..
        }
        | ExprKind::Drop(value)
        | ExprKind::Unary(_, value)
        | ExprKind::Assign(_, value)
        | ExprKind::Return(value)
        | ExprKind::Project(value, _)
        | ExprKind::BorrowPlace(value)
        | ExprKind::InitOwner { value, .. }
        | ExprKind::BorrowInit { value, .. }
        | ExprKind::RefRead(value) => fuse_expr(value, types, signatures, safety, fusions),
        ExprKind::PlaceIndex { base, index, .. } => {
            fuse_expr(base, types, signatures, safety, fusions);
            fuse_expr(index, types, signatures, safety, fusions);
        }
        ExprKind::DerefWrite(reference, value) | ExprKind::BoxWrite(reference, value) => {
            fuse_expr(reference, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::ArenaAlloc { arena, value } => {
            fuse_expr(arena, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::AllocatorNew {
            alloc,
            free,
            realloc,
        } => {
            fuse_expr(alloc, types, signatures, safety, fusions);
            fuse_expr(free, types, signatures, safety, fusions);
            if let Some(realloc) = realloc {
                fuse_expr(realloc, types, signatures, safety, fusions);
            }
        }
        ExprKind::AllocatorContextNew { value, .. } | ExprKind::AllocatorContextShare(value) => {
            fuse_expr(value, types, signatures, safety, fusions)
        }
        ExprKind::Suspendable(suspendable) => {
            fuse_block(&mut suspendable.body, types, signatures, safety, fusions)
        }
        ExprKind::Suspend { call, .. } => fuse_expr(call, types, signatures, safety, fusions),
        ExprKind::Region { body, finish, .. } => {
            fuse_block(body, types, signatures, safety, fusions);
            if let Some(finish) = finish {
                fuse_expr(finish, types, signatures, safety, fusions);
            }
        }
        ExprKind::RegionExit { value, .. }
        | ExprKind::TryExit { value, .. }
        | ExprKind::AbortExit { value, .. }
        | ExprKind::AbortPerform { value, .. }
        | ExprKind::AbortCall { call: value, .. } => {
            fuse_expr(value, types, signatures, safety, fusions)
        }
        ExprKind::AbortScope { body, handler, .. } => {
            fuse_block(body, types, signatures, safety, fusions);
            fuse_expr(handler, types, signatures, safety, fusions);
        }
        ExprKind::HandlerDepth => {}
        ExprKind::ContinuationScope { body } => {
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::HandlerRedirect { depth, body } => {
            fuse_expr(depth, types, signatures, safety, fusions);
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::AllocBoxNew { allocator, value }
        | ExprKind::AllocBoxTryNew {
            allocator, value, ..
        } => {
            fuse_expr(allocator, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::AllocVecNew {
            allocator,
            capacity,
            ..
        } => {
            fuse_expr(allocator, types, signatures, safety, fusions);
            if let Some(capacity) = capacity {
                fuse_expr(capacity, types, signatures, safety, fusions);
            }
        }
        ExprKind::ArenaNewWith { strategy } => {
            fuse_expr(strategy, types, signatures, safety, fusions);
        }
        ExprKind::ArenaTryAlloc { arena, value, .. } => {
            fuse_expr(arena, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArrayPush { array, value, .. } => {
            fuse_expr(array, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArrayFill { length, value, .. } => {
            fuse_expr(length, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::HandlerPush { handler, body, .. } => {
            fuse_expr(handler, types, signatures, safety, fusions);
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::DynamicPerform {
            payload, resume, ..
        } => {
            fuse_expr(payload, types, signatures, safety, fusions);
            fuse_expr(resume, types, signatures, safety, fusions);
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
        ExprKind::Binary(_, left, right)
        | ExprKind::BytesAt(left, right)
        | ExprKind::StructEq { left, right, .. }
        | ExprKind::DynArrayEqual { left, right, .. } => {
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
            grow,
        } => {
            fuse_expr(vector, types, signatures, safety, fusions);
            for callback in callbacks.iter_mut() {
                fuse_expr(callback, types, signatures, safety, fusions);
            }
            // A growth-capable transform may allocate/move the vector. Merging
            // it with another pass can change allocation and callback order, so
            // it is never an automatic fusion candidate.
            if *grow {
                return;
            }
            let mut merged = Vec::new();
            std::mem::swap(callbacks, &mut merged);
            let mut cursor = std::mem::replace(vector, placeholder_expr(expr.span));
            loop {
                let compatible = match &cursor.kind {
                    ExprKind::VecMap {
                        target: inner_target,
                        callbacks: inner_callbacks,
                        grow: inner_grow,
                        ..
                    } => {
                        !*inner_grow
                            && *inner_target == *source
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
                    grow: inner_grow,
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
                            grow: inner_grow,
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

fn callback_effects(types: &Types<'_>, callback: &Expr) -> u16 {
    match callback.ty {
        Type::Fn(id) => types.function_types[id].effects,
        _ => u16::MAX,
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
fn value_lifetime_candidates<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
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
                declared,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Unary { operand: value, .. } | ast::ExprKind::Try(value) => {
            value_lifetime_candidates(
                resolution,
                declared,
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
                declared,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
        }
        ast::ExprKind::Block(block) => {
            block_value_lifetime_candidates(
                resolution,
                declared,
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
                declared,
                then,
                parameter_lifetimes,
                parameter_field_lifetimes,
                out,
            );
            if let Some(otherwise) = otherwise {
                value_lifetime_candidates(
                    resolution,
                    declared,
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
                    declared,
                    &arm.body,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                    out,
                );
            }
        }
        ast::ExprKind::Call { callee, arguments } => {
            // Follow a helper's declared result source through the matching
            // argument. This keeps elided multi-input results inferable when
            // the body delegates to a checked helper (`fn alias(a, b) { tail(a) }`).
            for index in helper_result_parameters(resolution, declared, callee) {
                if let Some(argument) = arguments.get(index) {
                    value_lifetime_candidates(
                        resolution,
                        declared,
                        argument,
                        parameter_lifetimes,
                        parameter_field_lifetimes,
                        out,
                    );
                }
            }
        }
        _ => {}
    }
}
/// Record lifetimes introduced by local `let` bindings, so result inference can
/// follow a borrow through destructuring and simple aliases. This is a
/// conservative syntactic propagation: a binding receives a lifetime only when
/// its initializer has exactly one candidate lifetime. Anything ambiguous keeps
/// the existing explicit-annotation error.
fn collect_local_lifetimes<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    block: &ast::Block,
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { pattern, value, .. } => {
                bind_local_lifetime(
                    resolution,
                    declared,
                    pattern,
                    value,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
                collect_expr_local_lifetimes(
                    resolution,
                    declared,
                    value,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
            ast::Statement::Expr(expr) => collect_expr_local_lifetimes(
                resolution,
                declared,
                expr,
                parameter_lifetimes,
                parameter_field_lifetimes,
            ),
        }
    }
    if let Some(tail) = &block.tail {
        collect_expr_local_lifetimes(
            resolution,
            declared,
            tail,
            parameter_lifetimes,
            parameter_field_lifetimes,
        );
    }
}

fn collect_expr_local_lifetimes<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    expr: &ast::Expr,
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    match &expr.kind {
        ast::ExprKind::Block(block) => collect_local_lifetimes(
            resolution,
            declared,
            block,
            parameter_lifetimes,
            parameter_field_lifetimes,
        ),
        ast::ExprKind::If {
            then, otherwise, ..
        } => {
            collect_local_lifetimes(
                resolution,
                declared,
                then,
                parameter_lifetimes,
                parameter_field_lifetimes,
            );
            if let Some(otherwise) = otherwise {
                collect_expr_local_lifetimes(
                    resolution,
                    declared,
                    otherwise,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
        }
        ast::ExprKind::Match { arms, .. } => {
            for arm in arms {
                collect_expr_local_lifetimes(
                    resolution,
                    declared,
                    &arm.body,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
        }
        ast::ExprKind::While { body, .. } | ast::ExprKind::Loop(body) => {
            collect_local_lifetimes(
                resolution,
                declared,
                body,
                parameter_lifetimes,
                parameter_field_lifetimes,
            );
        }
        // A lambda body is a separate callable scope; its own inference runs
        // when that body is checked.
        ast::ExprKind::Lambda(_) => {}
        _ => {}
    }
}

fn bind_local_lifetime<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    pattern: &ast::Pattern,
    value: &ast::Expr,
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    let chain = field_chain(resolution, value);
    match &pattern.kind {
        ast::PatternKind::Name(_) => {
            let Some(id) = resolution.binder(pattern.span) else {
                return;
            };
            let mut candidates = BTreeSet::new();
            value_lifetime_candidates(
                resolution,
                declared,
                value,
                parameter_lifetimes,
                parameter_field_lifetimes,
                &mut candidates,
            );
            if candidates.len() == 1 {
                parameter_lifetimes.insert(id, candidates.into_iter().next().unwrap());
            }
            // A plain alias of a borrowed record keeps the same field paths.
            if let Some((root, path)) = chain
                && let Some(fields) = parameter_field_lifetimes.get(&root).cloned()
            {
                let prefix = path.join(".");
                let mut copied = BTreeMap::new();
                for (name, lifetime) in fields {
                    let stripped = if prefix.is_empty() {
                        Some(name.as_str())
                    } else {
                        name.strip_prefix(&format!("{prefix}."))
                    };
                    if let Some(stripped) = stripped {
                        copied.insert(stripped.to_owned(), lifetime);
                    }
                }
                if !copied.is_empty() {
                    parameter_field_lifetimes.insert(id, copied);
                }
            }
        }
        ast::PatternKind::Record { fields, .. } | ast::PatternKind::Structural { fields, .. } => {
            let Some((root, base)) = chain else {
                return;
            };
            for (name, subpattern) in fields {
                let mut path = base.clone();
                path.push(name.clone());
                let lifetime = parameter_field_lifetimes
                    .get(&root)
                    .and_then(|fields| fields.get(&path.join(".")).cloned());
                if let Some(lifetime) = lifetime
                    && let ast::PatternKind::Name(_) = subpattern.kind
                    && let Some(id) = resolution.binder(subpattern.span)
                {
                    parameter_lifetimes.insert(id, lifetime);
                }
                if let ast::PatternKind::Name(_) = subpattern.kind
                    && let Some(id) = resolution.binder(subpattern.span)
                    && let Some(fields) = parameter_field_lifetimes.get(&root).cloned()
                {
                    // The binding may itself be a nested borrowed record; keep
                    // its child field lifetimes for a later destructuring.
                    let prefix = format!("{}.", path.join("."));
                    let mut copied = BTreeMap::new();
                    for (name, lifetime) in fields {
                        if let Some(stripped) = name.strip_prefix(&prefix) {
                            copied.insert(stripped.to_owned(), lifetime);
                        }
                    }
                    if !copied.is_empty() {
                        parameter_field_lifetimes.insert(id, copied);
                    }
                }
                if matches!(
                    subpattern.kind,
                    ast::PatternKind::Record { .. } | ast::PatternKind::Structural { .. }
                ) {
                    // Nested destructuring needs a synthetic root for the
                    // sub-record. Reuse the original root and extend the path
                    // through each nested field below.
                    bind_nested_record_lifetime(
                        resolution,
                        subpattern,
                        &root,
                        &path,
                        parameter_lifetimes,
                        parameter_field_lifetimes,
                    );
                }
            }
        }
        ast::PatternKind::Type { inner, .. } => bind_local_lifetime(
            resolution,
            declared,
            inner,
            value,
            parameter_lifetimes,
            parameter_field_lifetimes,
        ),
        ast::PatternKind::Or(patterns) => {
            for pattern in patterns {
                bind_local_lifetime(
                    resolution,
                    declared,
                    pattern,
                    value,
                    parameter_lifetimes,
                    parameter_field_lifetimes,
                );
            }
        }
        _ => {}
    }
}

fn bind_nested_record_lifetime(
    resolution: &Resolution,
    pattern: &ast::Pattern,
    root: &BindingId,
    base: &[String],
    parameter_lifetimes: &mut BTreeMap<BindingId, String>,
    parameter_field_lifetimes: &mut BTreeMap<BindingId, BTreeMap<String, String>>,
) {
    let (ast::PatternKind::Record { fields, .. } | ast::PatternKind::Structural { fields, .. }) =
        &pattern.kind
    else {
        return;
    };
    for (name, subpattern) in fields {
        let mut path = base.to_vec();
        path.push(name.clone());
        let lifetime = parameter_field_lifetimes
            .get(root)
            .and_then(|fields| fields.get(&path.join(".")).cloned());
        if let Some(lifetime) = lifetime
            && let ast::PatternKind::Name(_) = subpattern.kind
            && let Some(id) = resolution.binder(subpattern.span)
        {
            parameter_lifetimes.insert(id, lifetime);
        }
        bind_nested_record_lifetime(
            resolution,
            subpattern,
            root,
            &path,
            parameter_lifetimes,
            parameter_field_lifetimes,
        );
    }
}

/// AST argument positions of `callee` whose written borrow lifetime supplies
/// its result. An explicit result lifetime selects every parameter that mentions
/// it; an elided borrowed result selects the single input lifetime, if any.
/// Positions are source positions because a call keeps erased proof arguments
/// in its AST argument list; they are not runtime parameter indices.
fn helper_result_parameters<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
    callee: &ast::Expr,
) -> Vec<usize> {
    let name = match &callee.kind {
        ast::ExprKind::Name(_) => callee,
        ast::ExprKind::Specialize { callee, .. } => callee,
        _ => return Vec::new(),
    };
    let Some(id) = resolution.reference(name.span) else {
        return Vec::new();
    };
    let Some(entry) = declared.get(&id) else {
        return Vec::new();
    };
    let function = entry.ast;
    let result = crate::grades::split(&function.result).0;
    if !matches!(
        result.kind,
        ast::TypeKind::Borrow { .. } | ast::TypeKind::Slice(_)
    ) {
        return Vec::new();
    }
    let explicit = borrow_lifetime(result);
    let mut inputs: Vec<(usize, Option<String>)> = Vec::new();
    for (position, parameter) in function.parameters.iter().enumerate() {
        if parameter.erased {
            continue;
        }
        let ty = crate::grades::split(&parameter.ty).0;
        if matches!(ty.kind, ast::TypeKind::Borrow { .. }) {
            inputs.push((position, borrow_lifetime(ty)));
        }
    }
    let Some(explicit) = explicit else {
        // Elided result: only an unambiguous single input borrow can tell us
        // which argument supplies it.
        let distinct = inputs
            .iter()
            .map(|(position, name)| name.clone().unwrap_or_else(|| format!("#{position}")))
            .collect::<BTreeSet<_>>();
        if distinct.len() == 1 {
            return inputs.iter().map(|(position, _)| *position).collect();
        }
        return Vec::new();
    };
    inputs
        .iter()
        .filter(|(_, name)| name.as_deref() == Some(explicit.as_str()))
        .map(|(position, _)| *position)
        .collect()
}

/// Map one solved stable origin onto this instance's declared lifetime. A
/// direct borrowed parameter owns every path through it. A by-value record
/// parameter uses its source field path. A missing mapping is an error, never a
/// silently dropped origin that would make the summary look smaller than it is.
fn summary_origin_lifetime(
    origin: &recursive_lifetimes::Origin,
    parameter_lifetimes: &[Option<String>],
    parameter_binders: &[Option<BindingId>],
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
) -> std::result::Result<String, String> {
    if let Some(lifetime) = parameter_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
    {
        return Ok(lifetime.clone());
    }
    if origin.path.is_empty() {
        return Err(format!(
            "runtime parameter #{} has no inferred borrow lifetime; no borrowed input lifetime was recorded for this position",
            origin.parameter
        ));
    }
    let binder = parameter_binders
        .get(origin.parameter)
        .copied()
        .flatten()
        .ok_or_else(|| {
            format!(
                "runtime parameter #{} has no source binder",
                origin.parameter
            )
        })?;
    let path = origin.path.join(".");
    parameter_field_lifetimes
        .get(&binder)
        .and_then(|fields| fields.get(&path).cloned())
        .ok_or_else(|| {
            format!(
                "cannot be returned: runtime parameter #{} field path '{path}' has no declared lifetime",
                origin.parameter
            )
        })
}
/// Map one required-precondition endpoint onto this instance's declared input
/// lifetime. Unlike a result origin, a root leaf may name a container element
/// lifetime, which `collect_parameter_field_lifetimes` records at the empty
/// path. A missing field path is an error, never a dropped requirement.
fn requirement_origin_lifetime(
    origin: &recursive_lifetimes::Origin,
    parameter_lifetimes: &[Option<String>],
    parameter_nested_lifetimes: &[Option<String>],
    parameter_binders: &[Option<BindingId>],
    parameter_field_lifetimes: &BTreeMap<BindingId, BTreeMap<String, String>>,
) -> std::result::Result<String, String> {
    if let Some(binder) = parameter_binders.get(origin.parameter).copied().flatten()
        && let Some(lifetime) = parameter_field_lifetimes
            .get(&binder)
            .and_then(|fields| fields.get(&origin.path.join(".")))
    {
        return Ok(lifetime.clone());
    }
    if let Some(lifetime) = parameter_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
        && !lifetime.starts_with('<')
    {
        return Ok(lifetime.clone());
    }
    if let Some(lifetime) = parameter_nested_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
    {
        return Ok(lifetime.clone());
    }
    if let Some(lifetime) = parameter_lifetimes
        .get(origin.parameter)
        .and_then(|lifetime| lifetime.as_ref())
    {
        return Ok(lifetime.clone());
    }
    summary_origin_lifetime(
        origin,
        parameter_lifetimes,
        parameter_binders,
        parameter_field_lifetimes,
    )
}
fn block_value_lifetime_candidates<'a>(
    resolution: &Resolution,
    declared: &BTreeMap<BindingId, Declared<'a>>,
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
            declared,
            returned,
            parameter_lifetimes,
            parameter_field_lifetimes,
            out,
        );
    }
    if let Some(tail) = &block.tail {
        value_lifetime_candidates(
            resolution,
            declared,
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
/// Resolve an elided borrowed field inside a structural record result from the
/// function's single input borrow lifetime. Explicit labels, including the
/// concrete label of a `..r` row specialization, are retained exactly. Only a
/// direct structural view field without a label is filled, and only when one
/// input borrow lifetime is available. Zero or several distinct inputs keep the
/// field unresolved so the result gate reports the missing relation; a row
/// hidden behind an owning container is likewise left for that gate.
fn resolve_elided_structural_result(
    types: &mut crate::runtime_types::Types<'_>,
    result: Type,
    input_lifetimes: &[(String, Span, Option<String>)],
    span: Span,
) -> Result<Type> {
    fn go(
        types: &mut crate::runtime_types::Types<'_>,
        ty: Type,
        label: Option<&str>,
        no_input: bool,
        span: Span,
        depth: usize,
    ) -> Result<Type> {
        if depth >= 64 {
            return Err(Diagnostic::new(
                span,
                "structural result nesting exceeded its finite lifetime-elision budget",
            ));
        }
        let Some(_id) = ty.layout().filter(|id| types.enums[*id].structural) else {
            return Ok(ty);
        };
        let fields = types
            .structural_row_fields(ty)
            .expect("structural layout has a canonical row");
        let mut rebuilt = Vec::with_capacity(fields.len());
        for field in &fields {
            let mut field_ty = field.ty;
            if field_ty
                .layout()
                .is_some_and(|id| types.enums[id].structural)
            {
                field_ty = go(types, field_ty, label, no_input, span, depth + 1)?;
            }
            let mut lifetime = field.lifetime.clone();
            if lifetime.is_none() && field_ty.is_view() {
                let Some(label) = label else {
                    return Err(Diagnostic::new(
                        span,
                        if no_input {
                            "a returned structural record field has an elided lifetime, but the function has no borrowed input to infer it from; write the field as '&'a [T]' with a declared lifetime or return a nominal record with declared field lifetimes"
                        } else {
                            "cannot recover the lifetime of an elided structural result field: the function has several distinct input borrow lifetimes; name the field's lifetime explicitly, as in 'struct { view: &'a [T] }'"
                        },
                    ));
                };
                lifetime = Some(label.to_owned());
            }
            rebuilt.push(crate::runtime_types::RowField::new(
                field.name.clone(),
                field_ty,
                lifetime,
            ));
        }
        if rebuilt == fields {
            return Ok(ty);
        }
        types.structural_fields(rebuilt, span)
    }
    let label = match input_lifetimes {
        [(only, _, _)] => Some(only.as_str()),
        _ => None,
    };
    go(types, result, label, input_lifetimes.is_empty(), span, 0)
}

/// Map each borrowed field path of a parameter type to its declared lifetime,
/// using source field names. Container element leaves use the container field's
/// name; a direct slice or reference field uses its own name.
fn collect_parameter_field_lifetimes(
    types: &crate::runtime_types::Types<'_>,
    ty: Type,
    out: &mut BTreeMap<String, String>,
) -> Result<()> {
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
    for leaf in crate::runtime_types::borrow_leaves(types, ty)? {
        let Some(lifetime) = leaf.lifetime else {
            continue;
        };
        if let Some(name) = names(types, ty, &leaf.path) {
            out.insert(name, lifetime);
        }
    }
    Ok(())
}
/// A lifetime label that names no caller identity at this occurrence: an
/// inferred record identity, a freshened argument placeholder, or an elided
/// label. These are resolved by the ownership provenance pass and must not be
/// compared as if they were declared caller lifetimes.
fn is_opaque_call_label(label: &str) -> bool {
    label.is_empty() || label == "_" || label.starts_with('<')
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
    let graph = crate::lifetimes::LifetimeGraph::new(&edges);
    let solution = graph.solve();
    let closure = solution.closure;
    debug_assert!(solution.components.iter().all(|c| !c.is_empty()));
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
        ).with_note(*span, format!("outlives cycle: {}", graph.path(short, long).unwrap().iter().map(|n| format!("'{n}")).chain(std::iter::once(format!("'{short}"))).collect::<Vec<_>>().join(" -> "))));
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
/// Render a concrete effect set for diagnostics, in canonical order with
/// declared operations after the built-in vocabulary.
fn effect_names(resolution: &Resolution, bits: u16) -> String {
    crate::runtime_types::effect_name_list(resolution, bits).join(", ")
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
    pub(crate) effects: Vec<u16>,
}
/// Concrete arguments for the generic parameters of one impl header. Stored by
/// index so `MethodDefinition` stays `Copy`.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
struct ImplArguments {
    types: Vec<Type>,
    consts: Vec<usize>,
    grades: Vec<Grade>,
    effects: Vec<u16>,
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
    Vec<u16>,
    Option<usize>,
);
/// One receiver type's trait-provided methods, each with the specialization
/// arguments that select it.
type TraitMethodTable = BTreeMap<String, Vec<(BindingId, TraitArguments, MethodDefinition)>>;
/// Type, grade, const, and effect arguments of one specialization.
type GenericArguments = (Vec<Type>, Vec<Grade>, Vec<usize>, Vec<u16>);
/// Generic arguments and checked values produced by inference.
type Inferred = (Vec<Type>, Vec<Grade>, Vec<usize>, Vec<u16>, Vec<Expr>);
/// Lifetime metadata copied from the first member method into a synthesized
/// closed-world dispatcher: parameter lifetimes, result lifetime, and bounds.
type WitnessLifetimes = (
    Vec<Option<String>>,
    Option<String>,
    BTreeSet<(String, String)>,
);
/// FND-ROWS-INFER: the rows of private functions that omit theirs. The check
/// runs in passes: each assumes the rows the previous one found, checks every
/// inferred body with all effects available and records what it requires.
/// Rows only grow, so the passes reach the least fixed point; callees are
/// checked before their callers, so one pass usually settles it.
#[derive(Debug, Default)]
struct RowInference {
    /// Rows assumed at the start of this pass.
    guesses: BTreeMap<BindingId, u16>,
    /// Rows found by this pass: the union over each function's instances.
    found: BTreeMap<BindingId, u16>,
    /// A body was checked against a row that later grew in this pass.
    stale: bool,
}
/// Function instances. A monomorphic function has one instance; a generic
/// function gets one per distinct list of type arguments that is used.
struct Functions<'a> {
    stage_templates: BTreeSet<usize>,
    declared: BTreeMap<BindingId, Declared<'a>>,
    /// `where len >= N` clauses of struct fields, by struct and field name.
    field_lengths: BTreeMap<BindingId, BTreeMap<String, &'a ast::Expr>>,
    /// Element accesses whose bound was proved, and those checked at run
    /// time (reported with KUSH_PROOF_REPORT=1).
    bounds_proved: usize,
    bounds_checked: usize,
    /// PROOF-FUZZ: run-time checks the prover could not discharge, keyed so a
    /// body checked twice records each check once.
    obligations: BTreeMap<(usize, usize, usize, ObligationKind), Obligation>,
    /// Checks the prover discharged, keyed the same way.
    discharged: BTreeMap<(usize, usize, usize, ObligationKind), Obligation>,
    /// The function instance whose body is being checked.
    checking: usize,
    /// Frozen recursive result-origin summaries, solved once before any body
    /// is checked. Provisional summaries never reach signature construction.
    summaries: recursive_lifetimes::Summaries,
    signatures: Vec<Signature>,
    /// Checked bodies aligned with `signatures`; `None` still needs checking,
    /// `Some` is a synthetic lambda/adapter body.
    bodies: Vec<Option<Function>>,
    instances: BTreeMap<InstanceKey, usize>,
    /// Instances created so far of each declaration; see [`MAX_INSTANCES`].
    instance_counts: BTreeMap<BindingId, usize>,
    /// Instances with type, grade, natural, effect or impl arguments; see
    /// [`MAX_GENERIC_INSTANCES`].
    generic_instances: usize,
    pending: Vec<usize>,
    /// Synthetic function adapter cache, keyed by optional static source
    /// function index and the source/target arrow types.
    adapter_cache: BTreeMap<(Option<usize>, Type, Type), usize>,
    certificates: Vec<crate::facts::Certificate>,
    /// Checked foreign imports, keyed by the function-instance index used by
    /// `Target::Foreign`. Only direct calls reach these entries.
    foreign_functions: BTreeMap<usize, ForeignFunction>,
    /// Checked nested map fusions produced while specializing bodies.
    fusions: usize,
    /// Deduplicated allocator-context shapes built while checking bodies.
    allocator_contexts: Vec<AllocatorContextSpec>,
    /// Set when any body uses a structured-task operation.
    uses_tasks: bool,
    uses_threads: bool,
    uses_unwinding: bool,
    /// GPU-SUBSET: declarations marked `#[gpu]`.
    gpu: BTreeSet<BindingId>,
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
    /// Associated functions of a non-generic inherent impl: no receiver,
    /// called as `Type.name(..)` and never by dot-call on a value. Keyed by
    /// the type declaration's binding.
    associated_fns: BTreeMap<BindingId, BTreeMap<String, MethodDefinition>>,
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
    /// EFF-CAP-RESUME-CAPTURING trampolines by (operation, handler arrow).
    capability_thunks: BTreeMap<(usize, usize), (usize, Type)>,
    /// CAP-CAPTURING-LEXICAL: private operation ids handed out so far.
    private_operations: usize,
    /// FND-ROWS-INFER: private functions that omit their row.
    inferred_rows: BTreeSet<BindingId>,
    /// FND-ROWS-INFER: the rows assumed and found by this pass.
    rows: &'a mut RowInference,
    /// FND-ROWS-INFER: functions with an instance body checked (or being
    /// checked) in this pass; one that names a function whose row then
    /// grows observed a stale row.
    checked_bodies: BTreeSet<BindingId>,
    /// FND-ROWS-INFER: the bindings each declared function's body names.
    body_refs: BTreeMap<BindingId, BTreeSet<BindingId>>,
    /// Registered members of each dynamically dispatched object specialization.
    /// Indexed by `Type::DynObj`. A member identifier is its position here.
    dyn_members: Vec<Vec<DynMember>>,
    /// Monomorphized generic-method contracts per dynamic object. A member
    /// registered after a call site instantiates every recorded contract.
    dyn_methods: BTreeMap<usize, BTreeMap<DynMethodKey, DynMethodContract>>,
    /// Checked upcast edges `(from, to)` between dynamic objects: every member
    /// registered in `from` is also registered in `to`, so the runtime upcast
    /// can map each identifier through the member tables.
    dyn_upcasts: BTreeSet<(usize, usize)>,
    /// Checked call sites on dynamically dispatched trait objects.
    dyn_calls: Vec<DynCallSpec>,
    /// Checked borrowed call sites on closed-world union objects.
    union_calls: Vec<UnionCallSpec>,
    logical: &'a crate::check::LogicalEnvironment,
}
/// Most instances of any one declaration. Specialization only multiplies
/// instances of a declaration through its type, grade, natural or effect
/// arguments, so this is what stops polymorphic recursion (each call
/// instantiating the next with a larger type) from specializing forever. The
/// number of functions in a program is otherwise unbounded: at most this many
/// per declaration, plus the lambdas and adapters those instances contain.
const MAX_INSTANCES: usize = 256;
/// Most instances of generic declarations in a program, all together. In a
/// polymorphic recursion through several declarations each step wraps the
/// type once more, so the per-declaration cap alone would allow types
/// 256 times the number of declarations deep, and checking time grows with
/// the cube of that (32 declarations took over a minute to reject). Ordinary
/// functions have one instance each and are not counted.
const MAX_GENERIC_INSTANCES: usize = 1024;
/// Total attempts for the bounded cross-parameter partition replay. This is a
/// deterministic work budget, not a completeness claim: exhausting it is an
/// explicit diagnostic asking for specialization.
const UNIFY_BACKTRACK_BUDGET: usize = 4096;

/// Traits that must use the dynamically dispatched object representation.
/// A generic or blanket impl leaves the member set open; a `dyn` mention in
/// any nominal field (including through an alias) would make the layout depend
/// on impl collection. Both are decided syntactically before layout.
fn dynamic_trait_set(module: &ast::Module, resolution: &Resolution) -> BTreeSet<BindingId> {
    fn scan(ty: &ast::Type, resolution: &Resolution, out: &mut BTreeSet<BindingId>) {
        match &ty.kind {
            ast::TypeKind::Dyn(bounds) => {
                for bound in bounds {
                    if let Some(id) = resolution.reference(bound.trait_ref.span)
                        && resolution.bindings[id].kind == BindingKind::Trait
                    {
                        out.insert(id);
                    }
                }
                for inner in ast::dyn_types(bounds) {
                    scan(inner, resolution, out);
                }
            }
            ast::TypeKind::Named { arguments, .. } => {
                for argument in arguments {
                    scan(argument, resolution, out);
                }
            }
            ast::TypeKind::Tuple(items) => {
                for item in items {
                    scan(item, resolution, out);
                }
            }
            ast::TypeKind::Array(element, _) | ast::TypeKind::Slice(element) => {
                scan(element, resolution, out)
            }
            ast::TypeKind::Borrow { inner, .. } => scan(inner, resolution, out),
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                for parameter in parameters {
                    scan(&parameter.ty, resolution, out);
                }
                scan(result, resolution, out);
            }
            ast::TypeKind::Binary { left, right, .. } => {
                scan(left, resolution, out);
                scan(right, resolution, out);
            }
            ast::TypeKind::Graded { inner, .. } => scan(inner, resolution, out),
            ast::TypeKind::Structural { fields, row, .. } => {
                for field in fields {
                    scan(&field.ty, resolution, out);
                }
                if let Some(row) = row {
                    scan(row, resolution, out);
                }
            }
            _ => {}
        }
    }
    // A trait named in a multi-trait object always uses the dynamic
    // representation, so an upcast never has to convert a closed union.
    let mut out = resolution.multi_object_traits.clone();
    for declaration in &module.items {
        match &declaration.item.kind {
            ast::ItemKind::Impl {
                generics,
                trait_path: Some(trait_path),
                ..
            } if !generics.is_empty() => {
                if let Some(id) = resolution.reference(trait_path.span)
                    && resolution.bindings[id].kind == BindingKind::Trait
                {
                    out.insert(id);
                }
            }
            ast::ItemKind::Struct { fields, .. } => {
                for field in fields {
                    scan(&field.ty, resolution, &mut out);
                }
            }
            ast::ItemKind::Trait { methods, .. }
                if methods
                    .iter()
                    .any(|method| !method.function.generics.is_empty()) =>
            {
                // A generic method needs per-call monomorphization, which the
                // fixed-layout dynamic representation provides; keep the trait
                // out of the closed-world union path.
                if let Some(id) = resolution.declarations.get(&declaration.item.span.start) {
                    out.insert(*id);
                }
            }
            ast::ItemKind::Enum { variants, .. } => {
                for variant in variants {
                    match &variant.payload {
                        ast::Payload::Unit | ast::Payload::Fields(_) => {}
                        ast::Payload::Tuple(types) => {
                            for ty in types {
                                scan(ty, resolution, &mut out);
                            }
                        }
                        ast::Payload::Record(fields) => {
                            for field in fields {
                                scan(&field.ty, resolution, &mut out);
                            }
                        }
                    }
                }
            }
            ast::ItemKind::Alias { ty, .. } => scan(ty, resolution, &mut out),
            _ => {}
        }
    }
    out
}

/// Check one in-memory file. Only standard-library modules can be imported.
pub fn check(source: &str) -> Result<Executable> {
    let program = crate::program::load_source("<input>", source).map_err(|(_, e)| e)?;
    check_program(&program)
}
/// The kernel-checked logical half of a program that may also contain
/// executable code, exactly as `check_program` admits it, without checking
/// executable bodies. Used by `kush core` to export the logical environment.
pub fn logical_module(source: &str) -> Result<crate::check::CheckedModule> {
    let program = crate::program::load_source("<input>", source).map_err(|(_, e)| e)?;
    let injected = inject_allocator_protocol(&program)?;
    let module = &injected.module;
    let mut resolution = resolve::resolve_program(&injected)?;
    collect_default_bindings(module, &mut resolution)?;
    crate::grades::validate_algebras(&mut resolution)?;
    let logical =
        crate::kernel::on_kernel_stack(|| crate::check::check_program(module, &resolution))?;
    Ok(crate::check::CheckedModule {
        resolution,
        kernel: logical.kernel,
        definitions: logical.definitions,
    })
}
/// The checked allocator-instance protocol. It is an ordinary trait declaration
/// injected ahead of user items, so impls are checked exactly like any other
/// trait: receiver modes, parameter/result layouts, grades, and effect rows must
/// match. The context adapter runs `free` during implicit drop, hence its empty
/// effect row.
const ALLOCATOR_PROTOCOL_SOURCE: &str = r#"
trait AllocatorProtocol {
    fn alloc(self: &mut Self, bytes: i64) -> Bytes ! {alloc};
    fn free(self: &mut Self, block: Bytes) -> Unit ! {};
    fn grow(self: &mut Self, block: Bytes, old_bytes: i64, bytes: i64) -> Bytes ! {alloc};
}
"#;
/// Synthetic spans sit far above any admitted source file (the loader rejects
/// programs over 16 MiB) so they cannot collide with a user declaration.
const ALLOCATOR_PROTOCOL_BASE: usize = 1 << 40;
/// Prepend the built-in allocator protocol trait to a loaded program.
fn inject_allocator_protocol(program: &crate::program::Program) -> Result<crate::program::Program> {
    let prelude = crate::parser::parse_at(ALLOCATOR_PROTOCOL_SOURCE, ALLOCATOR_PROTOCOL_BASE)?;
    let added = prelude.items.len();
    let mut injected = program.clone();
    // Give synthetic diagnostics a renderable source file rather than mapping
    // them onto the first user file.
    injected.sources.files.push(crate::program::SourceFile {
        name: "<allocator-protocol>".to_owned(),
        text: ALLOCATOR_PROTOCOL_SOURCE.to_owned(),
        base: ALLOCATOR_PROTOCOL_BASE,
    });
    for (index, unit) in injected.units.iter_mut().enumerate() {
        // The prelude belongs to the root unit, which is first. Later units
        // keep their own item ranges, shifted by the inserted item count.
        if index != 0 {
            unit.items.start += added;
        }
        unit.items.end += added;
    }
    // A root module header must remain item zero.
    let position = usize::from(
        injected
            .module
            .items
            .first()
            .is_some_and(|item| matches!(item.item.kind, ast::ItemKind::Module(_))),
    );
    let tail = injected.module.items.split_off(position);
    injected.module.items.extend(prelude.items);
    injected.module.items.extend(tail);
    Ok(injected)
}
/// Check a loaded multi-module program. Only the root module may define `main`.
/// KUSH-RUST-EXPORT: validate every `export "symbol" fn`. v1 crosses the
/// C ABI with scalars only: integers, floats and `Bool` parameters, a scalar
/// or `Unit` result, an effect row within `{panic}` (a panic aborts the
/// process), no generics, lifetimes, erased parameters or usage grades.
fn checked_exports(
    signatures: &[Signature],
    declared: &BTreeMap<BindingId, Declared<'_>>,
    resolution: &Resolution,
    types: &Types<'_>,
) -> Result<Vec<ExportedFunction>> {
    let primitive = |ty: Type| matches!(ty, Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_));
    // EXPORT-RECORDS: records of scalars (or such records) cross as C
    // structs; `&Bytes` parameters as a pointer and a length.
    fn scalar_record(types: &Types<'_>, ty: Type, depth: usize) -> bool {
        let Some(id) = ty.layout() else {
            return false;
        };
        let layout = &types.enums[id];
        depth < 8
            && layout.record
            && !layout.tuple
            && layout.array.is_none()
            && layout.dynamic_array.is_none()
            && layout.variants.len() == 1
            && !layout.variants[0].fields.is_empty()
            && layout.variants[0].fields.iter().all(|field| {
                matches!(
                    field,
                    Type::Bool | Type::I64 | Type::Int(_) | Type::Float(_)
                ) || scalar_record(types, *field, depth + 1)
            })
    }
    let scalar = |ty: Type| primitive(ty) || scalar_record(types, ty, 0);
    let bytes_ref = |ty: Type| matches!(ty, Type::Ref(p) if types.pointees[p] == Type::Bytes);
    let mut exports: Vec<ExportedFunction> = Vec::new();
    // Generic functions have no instance until called, so check them here.
    for info in declared.values() {
        let f = info.ast;
        if f.export.is_some()
            && (!f.generics.is_empty() || !f.lifetimes.is_empty() || info.impl_template.is_some())
        {
            return Err(Diagnostic::new(
                info.span,
                format!(
                    "exported function '{}' cannot be generic or take lifetime parameters",
                    f.name
                ),
            ));
        }
    }
    for (index, sig) in signatures.iter().enumerate() {
        let Some(info) = declared.get(&sig.binding) else {
            continue;
        };
        let f = info.ast;
        let Some(symbol) = &f.export else {
            continue;
        };
        let fail = |message: String| Err(Diagnostic::new(sig.span, message));
        let valid_symbol = !symbol.is_empty()
            && symbol.len() <= 128
            && symbol.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
            && symbol
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_');
        if !valid_symbol {
            return fail(format!(
                "export symbol '{symbol}' must be a C identifier of at most 128 characters"
            ));
        }
        if symbol.starts_with("kush_") || symbol == "main" {
            return fail(format!(
                "export symbol '{symbol}' is reserved for the Kush runtime"
            ));
        }
        if exports.iter().any(|e| e.symbol == *symbol) {
            return fail(format!("export symbol '{symbol}' is declared twice"));
        }
        if !f.generics.is_empty() || !f.lifetimes.is_empty() || info.impl_template.is_some() {
            return fail(format!(
                "exported function '{}' cannot be generic or take lifetime parameters",
                f.name
            ));
        }
        if f.parameters.iter().any(|p| p.erased)
            || sig.parameter_grades.iter().any(Option::is_some)
            || sig.result_grade.is_some()
        {
            return fail(format!(
                "exported function '{}' cannot take erased parameters or usage grades",
                f.name
            ));
        }
        // Every field of an exported record must be `pub`: a C or Rust
        // caller builds and reads the whole struct, which would bypass the
        // module's private fields.
        fn private_field(types: &Types<'_>, ty: Type, depth: usize) -> Option<String> {
            let id = ty.layout()?;
            let layout = &types.enums[id];
            if !layout.record || depth > 8 {
                return None;
            }
            let variant = layout.variants.first()?;
            for (name, field) in variant.names.iter().zip(&variant.fields) {
                if !types.field_public(layout.definition, name) {
                    return Some(name.clone());
                }
                if let Some(inner) = private_field(types, *field, depth + 1) {
                    return Some(inner);
                }
            }
            None
        }
        for ty in sig.parameters.iter().chain([&sig.result]) {
            if scalar_record(types, *ty, 0)
                && let Some(field) = private_field(types, *ty, 0)
            {
                return fail(format!(
                    "exported function '{}' passes a record whose field '{field}' is private; a C or Rust caller sees the whole struct, so mark every field 'pub'",
                    f.name
                ));
            }
        }
        if sig
            .parameters
            .iter()
            .any(|ty| !scalar(*ty) && !bytes_ref(*ty))
        {
            return fail(format!(
                "exported function '{}' takes only integers, floats, Bool, records of those, and &Bytes across the C ABI",
                f.name
            ));
        }
        if !(scalar(sig.result) || sig.result == Type::Unit) {
            return fail(format!(
                "exported function '{}' returns an integer, float, Bool, a record of those, or Unit across the C ABI",
                f.name
            ));
        }
        if sig.effects & !PANIC != 0 || !sig.effect_arguments.is_empty() {
            return fail(format!(
                "exported function '{}' must have the empty effect row {{}}; a panic aborts the process",
                f.name
            ));
        }
        let names = f
            .parameters
            .iter()
            .map(|p| {
                resolution
                    .binder(p.span)
                    .map(|id| resolution.bindings[id].name.clone())
                    .unwrap_or_else(|| "arg".to_owned())
            })
            .collect::<Vec<_>>();
        exports.push(ExportedFunction {
            symbol: symbol.clone(),
            index,
            parameters: names
                .into_iter()
                .zip(sig.parameters.iter().copied())
                .collect(),
            result: sig.result,
        });
    }
    Ok(exports)
}

pub fn check_program(program: &crate::program::Program) -> Result<Executable> {
    if let Some(prepared) = crate::staging::prepare(program)? {
        let (executable, initializers) =
            check_program_unstaged(&prepared.program, &prepared.entries, false, false)?;
        let mut executable =
            crate::staging::materialize(executable, initializers, &prepared.entries)?;
        crate::suspend::lower(&mut executable)?;
        return Ok(executable);
    }
    check_program_unstaged(program, &[], true, false).map(|(executable, _)| executable)
}

fn check_program_unstaged(
    source_program: &crate::program::Program,
    stage_entries: &[crate::staging::Entry],
    lower_suspensions: bool,
    validate_generic_staging: bool,
) -> Result<(Executable, BTreeMap<usize, usize>)> {
    // FND-ROWS-INFER: rerun the check while an inferred row grew after a
    // body had observed it. A pass that fails after a row grew is rerun too:
    // the failure may come from the smaller row it assumed.
    let mut guesses = BTreeMap::new();
    loop {
        let mut rows = RowInference {
            guesses: guesses.clone(),
            ..RowInference::default()
        };
        let result = check_program_pass(
            source_program,
            stage_entries,
            lower_suspensions,
            validate_generic_staging,
            &mut rows,
        );
        let grown = rows
            .found
            .iter()
            .any(|(binding, row)| row & !guesses.get(binding).copied().unwrap_or(0) != 0);
        if !grown || (result.is_ok() && !rows.stale) {
            return result;
        }
        for (binding, row) in rows.found {
            *guesses.entry(binding).or_insert(0) |= row;
        }
    }
}
fn check_program_pass(
    source_program: &crate::program::Program,
    stage_entries: &[crate::staging::Entry],
    lower_suspensions: bool,
    validate_generic_staging: bool,
    rows: &mut RowInference,
) -> Result<(Executable, BTreeMap<usize, usize>)> {
    let injected = inject_allocator_protocol(source_program)?;
    let program = &injected;
    let module = &program.module;
    reject_stored_capabilities(module)?;
    reject_omitted_method_rows(module)?;
    let mut resolution = resolve::resolve_staged_program(program)?;
    // Default trait methods inherited by an impl need one synthetic function
    // binding per (impl, method) pair. Allocate them before `Types` borrows the
    // resolver table: the table cannot be mutated once type lowering holds it.
    let default_bindings = collect_default_bindings(module, &mut resolution)?;
    crate::grades::validate_algebras(&mut resolution)?;
    let resolution = &resolution;
    let mut initializer_bindings = BTreeMap::new();
    for stage in stage_entries {
        let target = resolution.declarations[&stage.target.start];
        let initializer = resolution.declarations[&stage.initializer.start];
        initializer_bindings.insert(target, initializer);
    }
    // Total functions and aliases are erased and checked by the trusted kernel
    // before any executable body can cite them as proof evidence.
    let logical =
        crate::kernel::on_kernel_stack(|| crate::check::check_program(module, resolution))?;
    // A trait object whose member set is open (a generic or blanket impl) or
    // that appears inside a laid-out nominal field cannot use the inline
    // closed-world union: its width would depend on impl collection, which in
    // turn may depend on the layout. Those traits use the dynamically
    // dispatched fat-object representation instead. The decision must be made
    // before `Types::new` instantiates monomorphic layouts.
    let dynamic_traits = dynamic_trait_set(module, resolution);
    let mut types = Types::new(module, resolution, &logical, dynamic_traits)?;
    let mut field_lengths: BTreeMap<BindingId, BTreeMap<String, &ast::Expr>> = BTreeMap::new();
    for declaration in &module.items {
        if let ast::ItemKind::Struct { fields, .. } = &declaration.item.kind
            && fields.iter().any(|field| field.min_length.is_some())
        {
            let id = resolution.declarations[&declaration.item.span.start];
            let entry = field_lengths.entry(id).or_default();
            for field in fields {
                if let Some(length) = &field.min_length {
                    entry.insert(field.name.clone(), &**length);
                }
            }
        }
    }
    let mut functions = Functions {
        stage_templates: BTreeSet::new(),
        declared: BTreeMap::new(),
        field_lengths,
        bounds_proved: 0,
        bounds_checked: 0,
        obligations: BTreeMap::new(),
        discharged: BTreeMap::new(),
        checking: 0,
        summaries: recursive_lifetimes::Summaries::default(),
        signatures: Vec::new(),
        bodies: Vec::new(),
        instances: BTreeMap::new(),
        instance_counts: BTreeMap::new(),
        generic_instances: 0,
        pending: Vec::new(),
        adapter_cache: BTreeMap::new(),
        certificates: Vec::new(),
        foreign_functions: BTreeMap::new(),
        fusions: 0,
        allocator_contexts: Vec::new(),
        uses_tasks: false,
        uses_threads: false,
        uses_unwinding: false,
        gpu: BTreeSet::new(),
        elided_lifetimes: 0,
        traits: BTreeMap::new(),
        inherent: BTreeMap::new(),
        associated_fns: BTreeMap::new(),
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
        capability_thunks: BTreeMap::new(),
        private_operations: 0,
        inferred_rows: BTreeSet::new(),
        rows,
        checked_bodies: BTreeSet::new(),
        body_refs: BTreeMap::new(),
        dyn_members: Vec::new(),
        dyn_methods: BTreeMap::new(),
        dyn_upcasts: BTreeSet::new(),
        dyn_calls: Vec::new(),
        union_calls: Vec::new(),
        logical: &logical,
    };
    let mut effect_operations = BTreeMap::new();
    for declaration in &module.items {
        let ast::ItemKind::Effect {
            name,
            parameter,
            result,
            effects,
        } = &declaration.item.kind
        else {
            continue;
        };
        if effect_operations.contains_key(name) {
            return Err(Diagnostic::new(
                declaration.item.span,
                format!("duplicate effect operation '{name}'"),
            ));
        }
        let subst = crate::runtime_types::Subst::default();
        let parameter_ty = types.ty_in(parameter, &subst)?;
        let parameter_ty = types.full(parameter_ty, parameter.span)?;
        let result_ty = if types.names_never(result) {
            Type::Never
        } else {
            let result_ty = types.ty_in(result, &subst)?;
            types.full(result_ty, result.span)?
        };
        let parameter = parameter_ty;
        let result = result_ty;
        if matches!(parameter, Type::Never) {
            return Err(Diagnostic::new(
                declaration.item.span,
                "an effect operation cannot use Never as its payload type",
            ));
        }
        if parameter.is_view()
            || result.is_view()
            || matches!(parameter, Type::Ref(_) | Type::RefMut(_))
            || matches!(result, Type::Ref(_) | Type::RefMut(_))
        {
            return Err(Diagnostic::new(
                declaration.item.span,
                "dynamic effect operations cannot carry borrowed payloads or results; a handler stack entry has no caller lifetime to borrow from",
            ));
        }
        let (latent, variables) = crate::runtime_types::effect_bits_partial(resolution, effects)?;
        if !variables.is_empty() || latent & !EFFECT_BITS != 0 {
            return Err(Diagnostic::new(
                declaration.item.span,
                "an effect operation's handler effects are built-in effects (io, alloc, panic, suspend)",
            ));
        }
        let id = effect_operations.len();
        effect_operations.insert(
            name.clone(),
            EffectOperation {
                id,
                parameter,
                result,
                latent,
            },
        );
        types
            .capability_operations
            .insert(name.clone(), (parameter, result));
    }
    let mut abortive_operations = vec![false; effect_operations.len()];
    for operation in effect_operations.values() {
        abortive_operations[operation.id] = operation.result == Type::Never;
    }
    let mut effect_bits = vec![0; effect_operations.len()];
    for (name, operation) in &effect_operations {
        effect_bits[operation.id] = resolution.effect_bits.get(name).copied().unwrap_or(0);
    }
    let effect_operations = &effect_operations;
    let mut monomorphic = Vec::new();
    let mut main_stack = None;
    for declaration in &module.items {
        let span = declaration.item.span;
        // `#[kernel_steps(N)]` raises the kernel budget of a logical
        // declaration; the logical checker has already validated and used it.
        let logical_declaration = match &declaration.item.kind {
            ast::ItemKind::Function(f) => f.total,
            ast::ItemKind::Enum { total, .. } => *total,
            ast::ItemKind::Prop { .. } | ast::ItemKind::Alias { .. } => true,
            _ => false,
        };
        if let Some(attribute) = declaration
            .attributes
            .iter()
            .find(|attribute| attribute.kind == "kernel_steps" && !logical_declaration)
        {
            return Err(Diagnostic::new(
                attribute.span,
                "#[kernel_steps(N)] applies to logical declarations only: total fn, total enum, prop and type aliases",
            ));
        }
        if declaration
            .attributes
            .iter()
            .any(|attribute| attribute.kind != "kernel_steps")
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
        let data = matches!(
            declaration.item.kind,
            ast::ItemKind::Struct { .. } | ast::ItemKind::Enum { .. }
        );
        for attribute in &declaration.attributes {
            if attribute.kind == "kernel_steps" {
                continue;
            }
            if attribute.kind == "stack_size" {
                // LANG-STACK-SIZE: only the program's own main, in MiB.
                let is_main = matches!(&declaration.item.kind, ast::ItemKind::Function(f) if f.name == "main")
                    && resolution
                        .declarations
                        .get(&span.start)
                        .is_some_and(|binding| resolution.unit_of.get(binding) == Some(&0));
                if !is_main {
                    return Err(Diagnostic::new(
                        attribute.span,
                        "#[stack_size(N)] applies to the program's main function only",
                    ));
                }
                let mebibytes = attribute
                    .argument
                    .as_deref()
                    .and_then(|text| text.parse::<u64>().ok())
                    .filter(|value| (1..=65536).contains(value))
                    .ok_or_else(|| {
                        Diagnostic::new(
                            attribute.span,
                            "#[stack_size(N)] takes the main stack size in MiB, from 1 to 65536",
                        )
                    })?;
                if main_stack.replace(mebibytes << 20).is_some() {
                    return Err(Diagnostic::new(
                        attribute.span,
                        "#[stack_size(N)] may appear once",
                    ));
                }
                continue;
            }
            // FND-ROWS-ATTRS: the effect row is the contract. A row without
            // `alloc`/`suspend` (and whose row variables exclude it, as in
            // `e: Effects - alloc`) already says everything the attributes did.
            if function && matches!(attribute.kind.as_str(), "noalloc" | "nosuspend") {
                let effect = if attribute.kind == "noalloc" {
                    "alloc"
                } else {
                    "suspend"
                };
                return Err(Diagnostic::new(
                    attribute.span,
                    format!(
                        "#[{}] was removed: the effect row is the contract. Leave '{effect}' out of the row; for an effect-polymorphic row, exclude it from the row variable, as in 'e: Effects - {effect}'",
                        attribute.kind
                    ),
                ));
            }
            let valid = if function {
                matches!(attribute.kind.as_str(), "test" | "fuzz" | "gpu")
                    && attribute.argument.is_none()
            } else if data {
                (attribute.kind == "linear"
                    && attribute
                        .argument
                        .as_deref()
                        .is_none_or(|argument| argument.starts_with("unwind=")))
                    || attribute.kind == "foreign"
            } else {
                false
            };
            if !valid {
                return Err(Diagnostic::new(
                    attribute.span,
                    if function {
                        "functions support the #[test], #[fuzz], and #[gpu] attributes"
                    } else if data {
                        "data declarations support #[linear], #[linear(unwind = cleanup)] or #[foreign(\"release_symbol\")]"
                    } else {
                        "attributes apply to functions, enums, and structs only"
                    },
                ));
            }
            if attribute.kind == "foreign"
                && !matches!(declaration.item.kind, ast::ItemKind::Struct { .. })
            {
                return Err(Diagnostic::new(
                    attribute.span,
                    "#[foreign(\"release_symbol\")] declares an opaque resource and may only annotate a struct",
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
            | ast::ItemKind::Effect { .. }
            | ast::ItemKind::EffectRow { .. }
            | ast::ItemKind::Use(_) => continue,
            ast::ItemKind::Alias { .. } => continue,
            ast::ItemKind::Function(f) => f,
        };
        if f.total {
            // Checked by the logical kernel above and erased from runtime IR.
            continue;
        }
        // FND-ROWS-INFER: only a private function may omit its row; every
        // other row is a contract its callers outside the module rely on.
        if f.row_omitted() {
            let reason = if declaration.public {
                Some(
                    "a public function declares its effect row: it is the contract other modules check against",
                )
            } else if f.foreign.is_some() {
                Some("a foreign function declares its effect row")
            } else if f.export.is_some() {
                Some("an exported function declares its effect row")
            } else if declaration.attributes.iter().any(|a| a.kind == "gpu") {
                Some("a #[gpu] kernel declares its effect row")
            } else if f
                .generics
                .iter()
                .any(|generic| generic_category(resolution, generic) == GenericCategory::Effect)
            {
                Some("a function with effect parameters declares its effect row")
            } else {
                None
            };
            if let Some(reason) = reason {
                return Err(Diagnostic::new(
                    span,
                    format!("{reason}; add '! {{..}}' after the result type"),
                ));
            }
            functions
                .inferred_rows
                .insert(resolution.declarations[&span.start]);
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
        validate_runtime_length_signature(resolution, f, false)?;
        if f.body.is_none() {
            let Some(symbol) = &f.foreign else {
                return Err(Diagnostic::new(
                    span,
                    "executable functions require a body; declare an imported C function as 'foreign \"symbol\" fn name(...) -> T ! { io };'",
                ));
            };
            if !valid_c_symbol(symbol) {
                return Err(Diagnostic::new(
                    span,
                    "a foreign symbol must be a C identifier ([A-Za-z_][A-Za-z0-9_]*)",
                ));
            }
            // STD-SYS-FOREIGN: `kush_sys_*` symbols are the runtime's own host
            // stubs, which trust their arguments (a descriptor number, a
            // buffer's spare capacity). Only std may import them; the root
            // unit (0) may call itself `std.x`, so it never counts as std.
            if symbol.starts_with("kush_sys_") {
                let unit = resolution.item_units.get(&span.start).copied().unwrap_or(0);
                let std = unit != 0
                    && resolution
                        .units
                        .get(unit)
                        .is_some_and(|path| path.first().is_some_and(|p| p == "std"));
                if !std {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "foreign symbol '{symbol}' is reserved for the Kush standard library"
                        ),
                    ));
                }
            }
            if !f.generics.is_empty() || !f.lifetimes.is_empty() {
                return Err(Diagnostic::new(
                    span,
                    "a foreign function cannot be generic or lifetime-parameterized; declare one concrete C ABI signature",
                ));
            }
            if f.parameters.iter().any(|parameter| parameter.erased) {
                return Err(Diagnostic::new(
                    span,
                    "foreign functions cannot have erased proof parameters; FFI is runtime-only",
                ));
            }
            let (effects, _) = crate::runtime_types::effect_bits_partial(resolution, &f.effects)?;
            if effects & IO == 0 && !PURE_HOST_SYMBOLS.contains(&symbol.as_str()) {
                return Err(Diagnostic::new(
                    span,
                    "a foreign call has unchecked host side effects and requires the 'io' effect in its declared row",
                ));
            }
        } else if f.foreign.is_some() {
            return Err(Diagnostic::new(
                span,
                "a foreign declaration has no body; remove the implementation block",
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
        let (fixed_effects, effect_variables) = if f.row_omitted() {
            (0, Default::default())
        } else {
            crate::runtime_types::effect_bits_partial(resolution, &f.effects)?
        };
        let binding = resolution.declarations[&span.start];
        if declaration.attributes.iter().any(|a| a.kind == "gpu") {
            crate::gpu::check_declaration(
                f,
                span,
                &declaration.attributes,
                fixed_effects,
                &effect_variables,
            )?;
            functions.gpu.insert(binding);
        }
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
    // Recursive borrow summaries are solved before any body is checked, so a
    // signature, callable arrow, or ownership judgment observes only the frozen
    // least fixed point. The solver rejects unseeded cycles and unsupported
    // boundaries instead of publishing a provisional contract.
    functions.summaries = recursive_lifetimes::solve(resolution, &functions.declared, &types)?;
    // Generic methods are monomorphized on demand at each call site. Only
    // monomorphic methods get an eagerly checked instance here.
    monomorphic.extend(method_bindings.into_iter().filter(|binding| {
        let declared = functions.declared[binding];
        // A generic impl method is instantiated only after dispatch
        // selects concrete impl arguments; it has no `Self` otherwise.
        declared.ast.generics.is_empty() && declared.impl_template.is_none()
    }));
    // FND-ROWS-INFER: check callees before their callers, so a body sees the
    // final rows of the inferred functions it names. Pending bodies are
    // checked last-in first-out, so callers are queued first.
    if !functions.inferred_rows.is_empty() {
        for (&binding, declared) in &functions.declared {
            let mut refs = BTreeSet::new();
            if let Some(body) = &declared.ast.body {
                collect_lambda_refs(resolution, body, &mut refs);
            }
            functions.body_refs.insert(binding, refs);
        }
        let mut order = Vec::new();
        let mut visited = BTreeSet::new();
        for &root in &monomorphic {
            // Iterative post-order: callees end up before callers.
            let mut stack = vec![(root, false)];
            while let Some((binding, expanded)) = stack.pop() {
                if expanded {
                    order.push(binding);
                    continue;
                }
                if !visited.insert(binding) {
                    continue;
                }
                stack.push((binding, true));
                if let Some(refs) = functions.body_refs.get(&binding) {
                    stack.extend(refs.iter().rev().map(|&callee| (callee, false)));
                }
            }
        }
        let wanted: BTreeSet<_> = monomorphic.iter().copied().collect();
        monomorphic = order
            .into_iter()
            .rev()
            .filter(|binding| wanted.contains(binding))
            .collect();
    }
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
    for declared in functions.declared.values() {
        crate::staging::check_generic_quotes(declared.ast, resolution)?;
    }
    let mut staged_generics = Vec::new();
    for (&binding, declared) in &functions.declared {
        let function = declared.ast;
        if declared.impl_template.is_none()
            && !function.generics.is_empty()
            && function.body.as_ref().is_some_and(block_contains_quote)
            && let Some(cases) =
                crate::staging::generic_quotation_cases(function, resolution, MAX_INSTANCES)?
        {
            staged_generics.push((binding, cases));
        }
    }
    if validate_generic_staging {
        for (binding, cases) in staged_generics {
            let arguments: Vec<_> = cases
                .types
                .iter()
                .map(|&id| types.staging_type_parameter(id))
                .collect();
            for effects in cases.effects {
                functions.instance(
                    &mut types,
                    resolution,
                    binding,
                    arguments.clone(),
                    vec![],
                    vec![],
                    effects,
                    None,
                    None,
                )?;
            }
        }
    } else if !staged_generics.is_empty() {
        // Use distinct type identities even when every actual specialization
        // chooses the same type for two parameters. The validation program
        // is discarded before materialization or backend lowering.
        check_program_unstaged(source_program, stage_entries, false, true)?;
    }
    let mut initializers = BTreeMap::new();
    loop {
        let Some(index) = functions.pending.pop() else {
            if initializer_bindings.is_empty() {
                break;
            }
            // An initializer can itself request another staged specialization.
            // Check every newly requested instance before evaluating any of them.
            let pending = functions
                .instances
                .iter()
                .filter_map(|(key, &target)| {
                    let &initializer = initializer_bindings.get(&key.0)?;
                    (!initializers.contains_key(&target))
                        .then(|| (target, initializer, key.clone()))
                })
                .collect::<Vec<_>>();
            if pending.is_empty() {
                break;
            }
            for (target, initializer, (_, type_args, grade_args, const_args, effect_args, _)) in
                pending
            {
                let instance = functions.instance(
                    &mut types,
                    resolution,
                    initializer,
                    type_args,
                    grade_args,
                    const_args,
                    effect_args,
                    None,
                    Some(functions.signatures[target].span),
                )?;
                initializers.insert(target, instance);
            }
            continue;
        };
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
        functions.checking = index;
        // FND-ROWS-INFER: an inferred body is checked with every effect
        // available; what it requires becomes its row.
        let inferring_row = functions.inferred_rows.contains(&sig.binding);
        if !functions.inferred_rows.is_empty() {
            functions.checked_bodies.insert(sig.binding);
        }
        let all_effects = EFFECT_BITS
            | resolution
                .effect_bits
                .values()
                .fold(0u16, |bits, bit| bits | bit);
        let mut checker = Checker {
            inferring_row,
            quote_holes: BTreeMap::new(),
            quote_splices: BTreeMap::new(),
            lambda_holes: BTreeMap::new(),
            lambda_hint: None,
            required_effects: std::cell::Cell::new(0),
            pending_capability: None,
            expanding_constants: Vec::new(),
            writing_bounded_field: false,
            replace_min_length: None,
            body_invariant: None,
            parameter_lengths: BTreeMap::new(),
            refined_use_ok: false,
            lending_spans: BTreeSet::new(),
            abort_labels: 0,
            capability_slots: BTreeSet::new(),
            capability_passable: BTreeSet::new(),
            capability_resumable: BTreeSet::new(),
            capability_framed: BTreeMap::new(),
            capability_parameter_slots: BTreeSet::new(),
            capability_argument: false,
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
            declared_lifetimes: f
                .lifetimes
                .iter()
                .map(|lifetime| lifetime.name.clone())
                .collect(),
            result_lifetime: sig.result_lifetime.clone(),
            lifetime_bounds: sig.lifetime_bounds.clone(),
            call_boundary: 0,
            result_grade: sig.result_grade,
            effects: if inferring_row {
                all_effects
            } else {
                sig.effects
            },
            depth: 0,
            loops: Vec::new(),
            facts: crate::facts::Facts::default(),
            written_slots: BTreeSet::new(),
            closure_writes: BTreeMap::new(),
            closure_captures: BTreeMap::new(),
            proofs: BTreeMap::new(),
            logical: &logical,
            kernel_locals: Vec::new(),
            kernel_types: BTreeMap::new(),
            kernel_proofs: BTreeMap::new(),
            scope_depth: 0,
            scope_parallel: false,
            next_scope_parallel: false,
            next_split: 0,
            self_type: sig.self_type,
            default_trait: sig.default_trait.clone(),
            associated_consts: sig.associated_consts.clone(),
            unit: resolution.unit_of.get(&sig.binding).copied().unwrap_or(0),
            field_place: false,
            binding: sig.binding,
            scalar_epochs: BTreeMap::new(),
            kernel_aliases: BTreeMap::new(),
            scalar_values: BTreeMap::new(),
            proof_values: BTreeMap::new(),
            effect_operations,
            handlers: Vec::new(),
            effect_constraints: Vec::new(),
            unify_plan: Vec::new(),
            unify_decisions: Vec::new(),
            unify_plan_active: false,
            unify_open_choice: false,
            partition_bound: BTreeSet::new(),
            row_bound: BTreeSet::new(),
            hoisted: Vec::new(),
            next_index_place: 0,
            index_relations: BTreeSet::new(),
            pending_lengths: BTreeMap::new(),
            ensures_context: None,
            ensures_tail: false,
            ensures_depth: std::cell::Cell::new(0),
            branch_tail: false,
        };
        let body = (|| {
            let mut runtime = sig.parameters.iter().zip(&sig.parameter_grades);
            let mut ensures_params = Vec::new();
            for p in &f.parameters {
                if p.erased {
                    checker.assume_parameter(p)?;
                } else {
                    let (ty, grade) = runtime.next().unwrap();
                    let slot = checker.bind(p.span, *ty, false)?;
                    ensures_params.push((resolution.binder(p.span).unwrap(), slot));
                    if let Some(length) = &p.min_length {
                        let refined = ty.ref_pointee().is_some_and(|pointer| {
                            matches!(checker.types.pointees[pointer], Type::Vec(_))
                        });
                        let Some(length) = checker.ast_integer(length, 0).filter(|_| refined)
                        else {
                            return Err(Diagnostic::new(
                                p.ty.span,
                                "'where len >= N' on a parameter needs a '&Vec<T>' or '&mut Vec<T>' type and a compile-time N",
                            ));
                        };
                        checker.parameter_lengths.insert(slot, length);
                    }
                    if matches!(split_grade(&p.ty).0.kind, ast::TypeKind::Capability { .. }) {
                        checker.capability_slots.insert(slot);
                        checker.capability_passable.insert(slot);
                        checker.capability_parameter_slots.insert(slot);
                    }
                    checker.locals[slot].grade = *grade;
                    checker.locals[slot].linear =
                        grade.is_some_and(Grade::is_one) && checker.owned_type(*ty);
                    checker.validate_grade(*grade, *ty, p.ty.span, false)?;
                    let id = resolution.binder(p.span).unwrap();
                    checker.admit_scalar_index(id, *ty, p.span)?;
                }
            }
            if !f.ensures.is_empty() {
                for clause in &f.ensures {
                    checker.validate_ensures_calls(&clause.body)?;
                }
                checker.ensures_context = Some(EnsuresContext {
                    clauses: f.ensures.clone(),
                    params: ensures_params,
                    result: sig.result,
                });
                checker.ensures_tail = true;
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
        let (local_borrowed, local_copyable) = checker.local_classes(&checker.locals);
        let capability_parameters = (0..sig.parameters.len())
            .filter(|slot| checker.capability_slots.contains(slot))
            .collect();
        let required = checker.required_effects.get() & all_effects;
        let locals = checker.locals;
        functions.bodies[index] = Some(Function {
            name: sig.name.clone(),
            parameters: sig.parameters.len(),
            closure: None,
            capture_refs: vec![],
            capture_writes: vec![],
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
            declared_lifetimes: f
                .lifetimes
                .iter()
                .map(|lifetime| lifetime.name.clone())
                .collect(),
            index_relations: checker.index_relations.clone(),
            parameter_slots: None,
            local_borrowed,
            local_copyable,
            capability_parameters,
            shared_environment: false,
        });
        if inferring_row {
            functions.settle_inferred_row(sig.binding, required);
        }
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
    if !validate_generic_staging && std::env::var_os("KUSH_PROOF_REPORT").is_some() {
        eprintln!(
            "proof report: {} element accesses proved in bounds (no runtime check), {} checked at run time",
            functions.bounds_proved, functions.bounds_checked
        );
        if std::env::var("KUSH_PROOF_REPORT").as_deref() == Ok("verbose") {
            for line in obligation_report(&program.sources, functions.obligations.values()) {
                eprintln!("  {line}");
            }
        }
    }
    let mut foreign_functions = vec![None; functions.bodies.len()];
    for (index, foreign) in functions.foreign_functions {
        foreign_functions[index] = Some(foreign);
    }
    let exports = checked_exports(
        &functions.signatures,
        &functions.declared,
        resolution,
        &types,
    )?;
    let gpu_functions = functions
        .signatures
        .iter()
        .map(|signature| functions.gpu.contains(&signature.binding))
        .collect();
    // PANIC-LINEAR-CLEANUP: `#[linear(unwind = f)]`, by record layout: the
    // function in the type's module run on a live value while a panic
    // unwinds past it. It takes the value by move and returns Unit.
    let mut unwind_functions = BTreeMap::new();
    for (layout, record) in types.enums.iter().enumerate() {
        let Some((name, span)) = types.unwind_names.get(&record.definition) else {
            continue;
        };
        let unit = resolution.unit_of.get(&record.definition).copied();
        let found = functions.signatures.iter().position(|signature| {
            signature.name == *name
                && resolution.unit_of.get(&signature.binding).copied() == unit
                && functions
                    .declared
                    .get(&signature.binding)
                    .is_some_and(|declared| declared.self_ty.is_none())
        });
        let Some(index) = found else {
            return Err(Diagnostic::new(
                *span,
                format!("#[linear(unwind = {name})] names no function '{name}' in this module"),
            ));
        };
        let signature = &functions.signatures[index];
        if signature.parameters != [Type::Enum(layout)] || signature.result != Type::Unit {
            return Err(Diagnostic::new(
                *span,
                format!(
                    "the unwind cleanup '{name}' must take the {} by value and return Unit",
                    resolution.bindings[record.definition].name
                ),
            ));
        }
        unwind_functions.insert(layout, index);
    }
    let simd_functions = functions
        .signatures
        .iter()
        .map(|signature| {
            let binding = signature.binding;
            let unit = *resolution.unit_of.get(&binding)?;
            let path = resolution.units.get(unit)?;
            // The root unit is never std (the loader also rejects a root
            // under `std`).
            if unit == 0 || path.len() != 2 || path[0] != "std" {
                return None;
            }
            let declared = functions.declared.get(&binding)?;
            // SIMD-X86-SHA: the intrinsics of std.x86, by function name.
            if path[1] == "x86" && declared.self_ty.is_none() {
                return Some(("x86".to_owned(), declared.ast.name.clone()));
            }
            if path[1] != "simd" {
                return None;
            }
            let layout = declared.self_ty?.layout()?;
            let ty = resolution.bindings[types.enums[layout].definition]
                .name
                .clone();
            Some((ty, declared.ast.name.clone()))
        })
        .collect();
    let mut executable = Executable {
        stage_templates: functions.stage_templates,
        gpu_functions,
        simd_functions,
        unwind_functions,
        eval_fuel: crate::eval::DEFAULT_EVAL_FUEL,
        _grade_algebras: resolution.lowered_algebras.values().cloned().collect(),
        fusions: functions.fusions,
        bounds_proved: functions.bounds_proved,
        bounds_checked: functions.bounds_checked,
        obligations: sorted_obligations(&functions.obligations),
        discharged: sorted_obligations(&functions.discharged),
        uses_tasks: functions.uses_tasks,
        uses_unwinding: functions.uses_unwinding,
        main_stack,
        // A channel type anywhere needs the threaded runtime (its drop glue).
        uses_threads: functions.uses_threads
            || types
                .pointees
                .iter()
                .any(|ty| matches!(ty, Type::Channel(_)))
            || types.enums.iter().any(|layout| {
                layout
                    .variants
                    .iter()
                    .any(|variant| variant.fields.iter().any(|f| matches!(f, Type::Channel(_))))
            }),
        effect_bits,
        abortive_operations,
        certificates: functions.certificates,
        allocator_contexts: functions.allocator_contexts,
        functions: functions.bodies.into_iter().map(Option::unwrap).collect(),
        entry,
        enums: types.enums,
        pointees: types.pointees,
        unions: types.unions,
        function_types: types.function_types,
        dyn_object_names: types
            .objects
            .iter()
            .map(|object| object.name.clone())
            .collect(),
        // An object type that never had a member coerced into it still has
        // an (empty) member table, so every backend can index it.
        dyn_members: {
            let mut members = functions.dyn_members;
            members.resize_with(types.objects.len().max(members.len()), Vec::new);
            members
        },
        dyn_calls: functions.dyn_calls,
        union_calls: functions.union_calls,
        reference_labels: types.reference_labels,
        variance: types.variance,
        owned_enums: vec![],
        linear_enums: vec![],
        foreign_functions,
        exports,
        logical_definitions: logical.definitions.clone(),
    };
    crate::gpu::check(&executable)?;
    crate::multishot::check(&executable)?;
    crate::suspend::mark_abort_calls(&mut executable)?;
    crate::ownership::check(&mut executable)?;
    crate::grades::check(&executable)?;
    if lower_suspensions {
        crate::suspend::lower(&mut executable)?;
    }
    Ok((executable, initializers))
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
        E::Cast { value, ty } => format!("({} as {})", expr_key(value), type_key(ty)),
        E::Is { value, variant } => format!("({} is {variant})", expr_key(value)),
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
/// A field place of a record held directly in a local (not behind a
/// reference): the local and the field's word offset.
fn split_local_projection(expr: &Expr) -> Option<(usize, usize)> {
    let ExprKind::Project(base, offset) = &expr.kind else {
        return None;
    };
    match &base.kind {
        ExprKind::Peek(slot) | ExprKind::Local(slot) if !base.ty.is_ref() => Some((*slot, *offset)),
        ExprKind::Project(..) => {
            let (slot, inner) = split_local_projection(base)?;
            Some((slot, inner + offset))
        }
        _ => None,
    }
}
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
/// Outcome of a speculative unification; see `Checker::unify_trial`.
struct UnifyTrial<R> {
    result: Result<R>,
    /// A nested partition or indexed assignment took the first of several
    /// choices, so a failure does not rule the trial out.
    nested_choice: bool,
    effects: Vec<(crate::runtime_types::EffectRowTerm, u16)>,
}
/// Identity of a verified indexed-union assignment: its substitution, effect
/// evidence, and the members of bare variables a trial left unbound.
type IndexedSolutionKey = (
    crate::runtime_types::Subst,
    Vec<(crate::runtime_types::EffectRowTerm, u16)>,
    Vec<Vec<Type>>,
);
/// One surviving plan of the cross-parameter search.
struct ReplaySolution {
    subst: crate::runtime_types::Subst,
    /// The effect-row evidence this plan produced.
    effects: Vec<EffectConstraint>,
    /// Whether the plan passes the call's subtype checks, not only matching.
    valid: bool,
}
/// Whether two inference solutions bind every type and natural variable the
/// same way.
fn same_solution(
    left: &crate::runtime_types::Subst,
    right: &crate::runtime_types::Subst,
    type_vars: &[BindingId],
    const_vars: &[BindingId],
) -> bool {
    type_vars
        .iter()
        .all(|var| left.types.get(var) == right.types.get(var))
        && const_vars
            .iter()
            .all(|var| left.consts.get(var) == right.consts.get(var))
}
/// Layout budget exhaustion is a resource limit, never evidence against one
/// inference choice.
fn is_layout_budget_error(error: &Diagnostic) -> bool {
    error.message.contains("layout budget exhausted")
}
/// Spell a declared type for diagnostics, writing unions with `|`.
fn union_pattern_spelling(ty: &ast::Type) -> String {
    match &ty.kind {
        ast::TypeKind::Binary {
            op: crate::lexer::Kind::Pipe,
            left,
            right,
        } => format!(
            "{} | {}",
            union_pattern_spelling(left),
            union_pattern_spelling(right)
        ),
        ast::TypeKind::Named { path, arguments } if !arguments.is_empty() => format!(
            "{}<{}>",
            path.join("."),
            arguments
                .iter()
                .map(union_pattern_spelling)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ast::TypeKind::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(union_pattern_spelling)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ast::TypeKind::Array(inner, length) => format!(
            "[{}; {}]",
            union_pattern_spelling(inner),
            union_pattern_spelling(length)
        ),
        _ => type_key(ty),
    }
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
        ast::TypeKind::Dyn(bounds) => format!(
            "dyn {}",
            bounds
                .iter()
                .map(|bound| {
                    let mut text = type_key(&bound.trait_ref);
                    for (name, value) in &bound.bindings {
                        text.push_str(&format!("[{name}={}]", type_key(value)));
                    }
                    text
                })
                .collect::<Vec<_>>()
                .join(" + ")
        ),
        ast::TypeKind::Structural { fields, row, .. } => {
            let mut fields = fields
                .iter()
                .map(|field| (field.name.clone(), field.ty.clone()))
                .collect::<Vec<_>>();
            fields.sort_by(|left, right| left.0.cmp(&right.0));
            let tail = row
                .as_ref()
                .map(|row| format!(", ..{}", type_key(row)))
                .unwrap_or_default();
            format!(
                "struct{{{}{tail}}}",
                fields
                    .iter()
                    .map(|(name, ty)| format!("{name}:{}", type_key(ty)))
                    .collect::<Vec<_>>()
                    .join(","),
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
        ast::TypeKind::Infer => "_".to_owned(),
        ast::TypeKind::Capability {
            operation,
            effects,
            multi,
        } => format!(
            "cap {}{operation} ! {{{}}}",
            if *multi { "multi " } else { "" },
            effects.iter().map(type_key).collect::<Vec<_>>().join(", ")
        ),
        ast::TypeKind::Function {
            lifetimes,
            parameters,
            result,
            effects,
            call_once,
            call_linear,
            call_multi,
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
                } else if *call_multi {
                    "multi "
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
            ast::TypeKind::Infer => ast::TypeKind::Infer,
            ast::TypeKind::Capability {
                operation,
                effects,
                multi,
            } => ast::TypeKind::Capability {
                operation: operation.clone(),
                effects: effects.iter().map(|effect| self.ty(effect)).collect(),
                multi: *multi,
            },
            ast::TypeKind::SelfType => {
                if let Some(self_ty) = &self.self_ty {
                    return self_ty.clone();
                }
                ast::TypeKind::SelfType
            }
            ast::TypeKind::Dyn(bounds) => ast::TypeKind::Dyn(
                bounds
                    .iter()
                    .map(|bound| ast::DynBound {
                        trait_ref: self.ty(&bound.trait_ref),
                        bindings: bound
                            .bindings
                            .iter()
                            .map(|(name, value)| (name.clone(), self.ty(value)))
                            .collect(),
                    })
                    .collect(),
            ),
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
            ast::TypeKind::Structural { fields, open, row } => ast::TypeKind::Structural {
                fields: fields
                    .iter()
                    .map(|field| ast::Field {
                        name: field.name.clone(),
                        source: field.source.clone(),
                        ty: self.ty(&field.ty),
                        span: field.span,
                        public: field.public,
                        min_length: None,
                    })
                    .collect(),
                open: *open,
                row: row.as_ref().map(|row| Box::new(self.ty(row))),
            },
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
                call_multi,
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
                call_multi: *call_multi,
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
pub(crate) fn evaluate_trait_arguments(
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
    effects: &mut BTreeMap<BindingId, u16>,
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
pub(crate) fn trait_specialization_name(
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
                let names = crate::runtime_types::effect_name_list(resolution, row);
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
/// One destructured level of a consumed projected field: the hidden binding
/// (or root local) matched, its aggregate type, and the binding pattern.
type ConsumedLevel = (usize, Type, Pattern);
/// Put the destructuring levels built by `consume_object_field` around a
/// consuming call, outermost aggregate first.
fn wrap_consumed_field(levels: Vec<ConsumedLevel>, call: Expr) -> Expr {
    let span = call.span;
    levels
        .into_iter()
        .rev()
        .fold(call, |body, (scrutinee, ty, pattern)| {
            let result = body.ty;
            Expr {
                kind: ExprKind::Match(
                    Box::new(Expr {
                        kind: ExprKind::Local(scrutinee),
                        ty,
                        span,
                        resource: None,
                    }),
                    vec![Arm {
                        pattern,
                        guard: None,
                        body,
                    }],
                ),
                ty: result,
                span,
                resource: None,
            }
        })
}
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
/// Whether a reference parameter reaches `target` either directly or through
/// inline nominal-record fields. A returned `&Field` may borrow caller-owned
/// storage named by a `&Record` parameter; the ownership pass still proves the
/// exact origin is that parameter. Exclusive results require an exclusive
/// reference parameter.
fn reference_reaches_type(types: &Types<'_>, ty: Type, target: Type, mutable: bool) -> bool {
    fn contains(types: &Types<'_>, ty: Type, target: Type, depth: usize) -> bool {
        if ty.full() == target.full() {
            return true;
        }
        if depth >= 16 {
            return false;
        }
        let Some(id) = ty.layout().filter(|id| types.enums[*id].record) else {
            return false;
        };
        types.enums[id].variants[0]
            .fields
            .iter()
            .any(|field| contains(types, *field, target, depth + 1))
    }
    // A slice view parameter backs a reference to one of its elements (or a
    // field inside one): `&s[i]` borrows the caller's storage behind `s`.
    let (Type::Ref(pointer)
    | Type::RefMut(pointer)
    | Type::Slice(pointer)
    | Type::SliceMut(pointer)) = ty
    else {
        return false;
    };
    if mutable && !matches!(ty, Type::RefMut(_) | Type::SliceMut(_)) {
        return false;
    }
    contains(types, types.pointees[pointer], target, 0)
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
        ast::TypeKind::Structural { fields, row, .. } => {
            for field in fields {
                type_self_associations(&field.ty, out);
            }
            if let Some(row) = row {
                type_self_associations(row, out);
            }
        }
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Borrow { inner, .. } => type_self_associations(inner, out),
        ast::TypeKind::Dyn(bounds) => {
            for inner in ast::dyn_types(bounds) {
                type_self_associations(inner, out);
            }
        }
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
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. }
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
        ast::TypeKind::Infer | ast::TypeKind::Capability { .. } => false,
        ast::TypeKind::Named { path, arguments } => {
            path.first().is_some_and(|name| name == "Self")
                || arguments.iter().any(type_mentions_self)
        }
        ast::TypeKind::Tuple(arguments) => arguments.iter().any(type_mentions_self),
        ast::TypeKind::Structural { fields, row, .. } => {
            fields.iter().any(|field| type_mentions_self(&field.ty))
                || row.as_ref().is_some_and(|row| type_mentions_self(row))
        }
        ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(type_mentions_self),
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
        ast::TypeKind::Dyn(bounds) => {
            ast::dyn_types(bounds).any(|inner| type_mentions_self_outside_assoc(inner, allowed))
        }
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
                if let Some(length) = &parameter.min_length {
                    return Err(Diagnostic::new(
                        length.span,
                        "'where len >= N' parameters are supported on functions, not on methods yet",
                    ));
                }
                if parameter.erased && type_mentions_self(&parameter.ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "erased method parameters may not mention 'Self' in this subset",
                    ));
                }
            }
            validate_erased_parameters(resolution, logical, f)?;
            validate_length_templates(resolution, f)?;
            validate_runtime_length_signature(resolution, f, true)?;
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
        if type_has_open_row(self_ty) {
            return Err(Diagnostic::new(
                self_ty.span,
                "an impl self type cannot use an open row ('..'); impl headers match one exact canonical structural row",
            ));
        }
        let self_key = types.ty_in(self_ty, &crate::runtime_types::Subst::default())?;
        if matches!(
            self_key,
            Type::Ref(_)
                | Type::RefMut(_)
                | Type::Slice(_)
                | Type::SliceMut(_)
                | Type::Str
                | Type::StrMut
                | Type::Task(_)
                | Type::Thread(_)
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
            // A function of an inherent impl without a `self` receiver is an
            // associated function, called as `Type.name(..)`.
            let associated_fn = trait_id.is_none()
                && f.parameters
                    .first()
                    .is_none_or(|first| first.erased || first.name != "self");
            if !associated_fn {
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
            }
            // Builtin and field names only shadow dot-calls, which never
            // reach an associated function.
            if !associated_fn && Checker::builtin_method(&f.name) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' uses a reserved builtin method name; builtin receiver methods take precedence, so choose another name",
                        f.name
                    ),
                ));
            }
            if !associated_fn && record_fields.contains(&f.name) {
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
                if let Some(length) = &parameter.min_length {
                    return Err(Diagnostic::new(
                        length.span,
                        "'where len >= N' parameters are supported on functions, not on methods yet",
                    ));
                }
                if parameter.erased && type_mentions_self(&parameter.ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "erased method parameters may not mention 'Self' in this subset",
                    ));
                }
            }
            validate_erased_parameters(resolution, logical, f)?;
            validate_length_templates(resolution, f)?;
            validate_runtime_length_signature(resolution, f, true)?;
            let binding = resolution.method(method.span).ok_or_else(|| {
                Diagnostic::new(method.span, "internal error: impl method has no binding")
            })?;
            let definition = MethodDefinition {
                binding,
                public: method.public,
                unit: resolution.unit_of.get(&binding).copied().unwrap_or(0),
                impl_arguments: None,
            };
            if associated_fn {
                let owner = self_key
                    .layout()
                    .map(|layout| types.enums[layout].definition)
                    .ok_or_else(|| {
                        Diagnostic::new(
                            method.span,
                            "associated functions need a nominal record or enum type",
                        )
                    })?;
                let table = functions.associated_fns.entry(owner).or_default();
                if definitions.contains_key(&f.name)
                    || table.insert(f.name.clone(), definition).is_some()
                {
                    return Err(Diagnostic::new(
                        method.span,
                        format!("duplicate method or associated function '{}'", f.name),
                    ));
                }
            } else if definitions.insert(f.name.clone(), definition).is_some()
                || self_key
                    .layout()
                    .and_then(|layout| {
                        functions
                            .associated_fns
                            .get(&types.enums[layout].definition)
                    })
                    .is_some_and(|table| table.contains_key(&f.name))
            {
                return Err(Diagnostic::new(
                    method.span,
                    format!("duplicate method or associated function '{}'", f.name),
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
        let dynamic = types.dynamic_traits.contains(&trait_id);
        let mut reason: Option<String> = None;
        // Trait parameters may be type, natural, grade, or effect arguments.
        // The dynamic representation stores the checked specialization, so a
        // non-type argument is identity like a type argument; it never changes
        // the two-word object layout.
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
                if !f.generics.is_empty() && !dynamic {
                    reason = Some(format!(
                        "method '{name}' is generic; a generic method cannot be dispatched through a closed-world union object"
                    ));
                    break;
                }
                // A borrowed result is checked against the selected member's
                // lifetime contract at each call site. An owned receiver has no
                // receiver lifetime, so a result can only borrow caller-owned
                // storage (another argument) and remains valid after dispatch.
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
                // A dynamic call has no static callee whose length binders the
                // call site could replace with the caller's.
                if f.parameters
                    .iter()
                    .map(|parameter| &parameter.ty)
                    .chain(std::iter::once(&f.result))
                    .any(type_mentions_runtime_length)
                {
                    reason = Some(format!(
                        "method '{name}' mentions a runtime-length array [T; n <= C]; call it through a concrete receiver"
                    ));
                    break;
                }
            }
        }
        if reason.is_none()
            && !dynamic
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
                    // An open dynamic object may have no concrete impl at
                    // declaration time: every member can come from a generic
                    // or blanket impl and is registered at its coercion site.
                    if !dynamic {
                        reason = Some(format!("trait '{trait_name}' has no concrete impls"));
                    }
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
            if dynamic {
                // Open objects do not enumerate members in the value layout.
                // Concrete impls still contribute agreed associated values for
                // method signatures; generic impls are checked when a concrete
                // member is registered at a coercion site.
                if let Some(values) = object_associated.get(&arguments) {
                    types.agree_object_projections(trait_id, &arguments, values)?;
                }
                continue;
            }
            members.sort();
            members.dedup();
            let object = match types.object_union(members, resolution.bindings[trait_id].span) {
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
                types.agree_object_projections(trait_id, &arguments, values)?;
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
            // A trait object used in an already-laid-out nominal field cannot
            // defer this to the first `dyn` lowering: the layout is committed.
            if types
                .objects
                .iter()
                .any(|object| object.components.iter().any(|(id, _)| *id == trait_id))
            {
                return Err(Diagnostic::new(
                    resolution.bindings[trait_id].span,
                    format!("trait '{trait_name}' is not object-safe: {reason}"),
                ));
            }
            types.dyn_errors.insert(trait_id, reason);
        }
    }
    for entries in functions.object_traits.values_mut() {
        entries.sort();
        entries.dedup();
    }
    Ok(())
}
/// Whether a declared type syntax contains an open structural row. Impl
/// headers require an exact canonical row, so they reject `..`.
fn type_has_open_row(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::Structural { fields, open, row } => {
            *open || row.is_some() || fields.iter().any(|field| type_has_open_row(&field.ty))
        }
        ast::TypeKind::Named { arguments, .. } | ast::TypeKind::Tuple(arguments) => {
            arguments.iter().any(type_has_open_row)
        }
        ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(type_has_open_row),
        ast::TypeKind::Slice(inner)
        | ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Borrow { inner, .. } => type_has_open_row(inner),
        ast::TypeKind::Array(element, length) => {
            type_has_open_row(element) || type_has_open_row(length)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_has_open_row(left) || type_has_open_row(right)
        }
        ast::TypeKind::Function {
            parameters, result, ..
        } => parameters.iter().any(|p| type_has_open_row(&p.ty)) || type_has_open_row(result),
        _ => false,
    }
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
        ast::TypeKind::Structural { fields, open, row } => {
            if let Some(row) = row {
                // An open-row impl header is monomorphized per concrete
                // residual row. It must name a declared impl parameter, and
                // the tail participates in coherence exactly like a nominal
                // pattern variable.
                let Some(binder) = resolution.reference(row.span) else {
                    return Err(Diagnostic::new(
                        row.span,
                        format!(
                            "an impl {what} row tail must name a declared impl parameter, as in 'impl<r> Trait for struct {{ x: i64, ..r }}'"
                        ),
                    ));
                };
                if !generics.contains(&binder) {
                    return Err(Diagnostic::new(
                        row.span,
                        format!(
                            "row tail '{}' is not an impl parameter of this header",
                            resolution.bindings[binder].name
                        ),
                    ));
                }
            } else if *open {
                return Err(Diagnostic::new(
                    pattern.span,
                    format!(
                        "an impl {what} cannot use an unnamed open row ('..'); name a row parameter, as in 'impl<r> Trait for struct {{ x: i64, ..r }}'"
                    ),
                ));
            }
            for field in fields {
                validate_impl_pattern(resolution, types, &field.ty, generics, const_binders, what)?;
            }
            Ok(())
        }
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
        | ast::TypeKind::SelfType
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. } => Err(Diagnostic::new(
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
    effects: BTreeMap<BindingId, u16>,
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
        ast::TypeKind::Structural { fields, row, .. } => {
            fields
                .iter()
                .any(|field| pattern_has_unbound(resolution, &field.ty, bindings))
                || row
                    .as_ref()
                    .is_some_and(|row| pattern_has_unbound(resolution, row, bindings))
        }
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
        ast::TypeKind::Structural { fields, row, .. } => {
            // Structural impl headers match an anonymous structural row.
            // Nominal records are deliberately not matched here: they keep
            // their own identity, so a structural impl cannot silently overlap
            // a nominal impl. A `..r` tail binds the residual canonical row,
            // complete with each field's erased borrow label.
            let Some(row_fields) = types.structural_row_fields(actual) else {
                return Ok(false);
            };
            if row.is_none() && row_fields.len() != fields.len() {
                return Ok(false);
            }
            for field in fields {
                let Some(actual_field) = row_fields.iter().find(|actual| actual.name == field.name)
                else {
                    return Ok(false);
                };
                if !match_type_pattern(
                    resolution,
                    types,
                    &field.ty,
                    actual_field.ty,
                    bindings,
                    depth + 1,
                )? {
                    return Ok(false);
                }
            }
            if let Some(row) = row {
                let Some(binder) = resolution.reference(row.span) else {
                    return Ok(false);
                };
                let declared = fields
                    .iter()
                    .map(|field| field.name.as_str())
                    .collect::<BTreeSet<_>>();
                let residual = row_fields
                    .into_iter()
                    .filter(|field| !declared.contains(field.name.as_str()))
                    .collect::<Vec<_>>();
                let residual = types.structural_fields(residual, row.span)?;
                if let Some(bound) = bindings.types.get(&binder).copied() {
                    if types.structural_row_fields(bound) != types.structural_row_fields(residual) {
                        return Ok(false);
                    }
                } else {
                    bindings.types.insert(binder, residual);
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
            ast::TypeKind::Structural {
                fields: left,
                row: left_row,
                ..
            },
            ast::TypeKind::Structural {
                fields: right,
                row: right_row,
                ..
            },
        ) => {
            // Structural rows are canonical by field name. Common fields must
            // unify; a row tail can absorb every field the other header names.
            // With two named rows their tails are left flexible, which is
            // exactly the overlap relation needed for coherence.
            // A row tail absorbs fields only when its variable is flexible: the
            // general header's tail may stand for fields of the specific one,
            // but a rigid (specific) tail cannot invent fields the general
            // header names. Without this, `{x, y}` would "subsume" `{x, ..r}`
            // and genuine specializations were reported as duplicates.
            let absorbable = |holder: &Option<Box<ast::Type>>| {
                holder.as_deref().is_some_and(|row| {
                    pattern_binder(resolution, row).is_some_and(|id| flexible.contains(&id))
                })
            };
            for left_field in left {
                match right
                    .iter()
                    .find(|right_field| right_field.name == left_field.name)
                {
                    Some(right_field) => {
                        if !unify_ast_patterns(
                            resolution,
                            &left_field.ty,
                            &right_field.ty,
                            flexible,
                            map,
                            depth + 1,
                        ) {
                            return false;
                        }
                    }
                    None if absorbable(right_row) => {}
                    None => return false,
                }
            }
            for right_field in right {
                if left
                    .iter()
                    .any(|left_field| left_field.name == right_field.name)
                {
                    continue;
                }
                if !absorbable(left_row) {
                    return false;
                }
            }
            true
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
        && !matches!(
            &self_ty.kind,
            ast::TypeKind::Structural { row: Some(_), .. }
        )
    {
        return Err(Diagnostic::new(
            self_ty.span,
            "an inherent generic impl must target a nominal record/enum pattern or an open structural row with a row parameter",
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
            if let Some(length) = &parameter.min_length {
                return Err(Diagnostic::new(
                    length.span,
                    "'where len >= N' parameters are supported on functions, not on methods yet",
                ));
            }
            if parameter.erased && type_mentions_self(&parameter.ty) {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "erased method parameters may not mention 'Self' in this subset",
                ));
            }
        }
        validate_erased_parameters(resolution, logical, f)?;
        validate_length_templates(resolution, f)?;
        validate_runtime_length_signature(resolution, f, true)?;
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
        ast::TypeKind::Structural { fields, row, .. } => {
            fields.iter().any(|field| mentions(&field.ty))
                || row.as_ref().is_some_and(|row| mentions(row))
        }
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
pub(crate) enum ReceiverMode {
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
        effect_arguments: Vec<u16>,
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
        let count = self.instance_counts.entry(binding).or_default();
        if *count >= MAX_INSTANCES {
            return Err(Diagnostic::new(
                origin.unwrap_or(declared.span),
                "executable limit exceeded (256 instances of one function); polymorphic recursion cannot be specialized",
            ));
        }
        *count += 1;
        let (_, key_types, key_grades, key_naturals, key_effects, key_impl) = &key;
        if !(key_types.is_empty()
            && key_grades.is_empty()
            && key_naturals.is_empty()
            && key_effects.is_empty()
            && key_impl.is_none())
        {
            if self.generic_instances >= MAX_GENERIC_INSTANCES {
                return Err(Diagnostic::new(
                    origin.unwrap_or(declared.span),
                    "executable limit exceeded (1024 instances of generic functions in all; polymorphic recursion, or very many distinct specializations)",
                ));
            }
            self.generic_instances += 1;
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
                        effect_names(resolution, *effects),
                        generic.name,
                        effect_names(resolution, illegal),
                        generic.name,
                        effect_names(resolution, excluded)
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
                        effect_names(resolution, *effects),
                        generic.name,
                        effect_names(resolution, missing),
                        generic.name,
                        effect_names(resolution, included)
                    ),
                ));
            }
        }
        // A structural row type argument is a monomorphized canonical row, not
        // an erased lifetime-bearing nominal identity: its borrowed fields keep
        // their provenance through the ordinary structural conversion rules.
        // This is what lets a row variable preserve a borrowed field. Nominal
        // borrowed records still cannot cross an ordinary generic parameter.
        if key
            .1
            .iter()
            .any(|ty| crate::runtime_types::has_borrow(types, *ty) && !types.is_structural(*ty))
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
        // A type argument may not name a runtime-length binder of the function
        // being instantiated. Only a recursive call can write one, and in the
        // new activation that binder holds a different value, so a value of
        // the old length would get the new length's type.
        // An inherited trait default runs under a synthesized per-impl
        // binding, but its parameters and locals are owned by the trait
        // method's own binding; both count as the function's own.
        let body_owner = f
            .parameters
            .iter()
            .find_map(|parameter| resolution.binder(parameter.span))
            .and_then(|parameter| resolution.bindings[parameter].owner);
        for ty in substitution.types.values().chain(&substitution.self_type) {
            let captured = crate::runtime_types::runtime_length_binders(types, *ty)
                .into_iter()
                .find(|binder| {
                    let owner = resolution.bindings[*binder].owner;
                    owner == Some(binding) || (owner.is_some() && owner == body_owner)
                });
            if let Some(binder) = captured {
                return Err(Diagnostic::new(
                    origin.unwrap_or(declared.span),
                    format!(
                        "a type argument of '{}' mentions its own length binder '{}'; each call gets a new '{}', so pass the array as an ordinary runtime-length parameter instead",
                        f.name, resolution.bindings[binder].name, resolution.bindings[binder].name
                    ),
                ));
            }
        }
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
        let mut parameter_binders = Vec::new();
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
        let mut lifetime_bounds = build_lifetime_bounds(&f.lifetimes)?;
        for p in f.parameters.iter().filter(|p| !p.erased) {
            let (ty, grade) = split_grade(&p.ty);
            if !matches!(ty.kind, ast::TypeKind::Capability { .. }) {
                reject_capability_type(ty)?;
            }
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
            parameter_binders.push(binder);
            if let (Some(binder), Some(name)) = (binder, &lifetime) {
                parameter_binder_lifetimes.insert(binder, name.clone());
            }
            if let Some(binder) = binder {
                let mut fields = BTreeMap::new();
                collect_parameter_field_lifetimes(
                    types,
                    parameters.last().copied().unwrap(),
                    &mut fields,
                )?;
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
                    crate::runtime_types::borrow_leaves(types, parameters.last().copied().unwrap())?
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
        if let Some(body) = &f.body {
            // Local destructuring and simple aliases can carry a parameter
            // lifetime into the return position. Propagate them before the
            // result lifetime seed is chosen.
            collect_local_lifetimes(
                resolution,
                &self.declared,
                body,
                &mut parameter_binder_lifetimes,
                &mut parameter_field_lifetimes,
            );
        }
        let parameter_nested_lifetimes = f
            .parameters
            .iter()
            .filter(|parameter| !parameter.erased)
            .map(|parameter| nested_borrow_lifetime(&parameter.ty))
            .collect::<Vec<_>>();
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
        let result_was_explicit = explicit_result_lifetime.is_some();
        // Resolve an elided borrowed structural result field from the
        // function's single input borrow lifetime before result metadata is
        // collected. This mirrors ordinary slice-result elision; every other
        // case stays unresolved and is rejected below.
        let result =
            resolve_elided_structural_result(types, result, &input_lifetimes, f.result.span)?;
        // Stable parameter-leaf origins solved over the concrete call graph.
        // Map each origin back to this instance's declared or elided lifetime
        // labels. Every origin must map to a real lifetime: rejecting an
        // unmapped path keeps a partial summary from masquerading as complete.
        let mut summary_sources = BTreeSet::new();
        // Per-result-leaf outlives edges inferred from the frozen summaries.
        // They are added to `lifetime_bounds` after the result lifetime is
        // chosen, so ownership sees every reachable owner.
        let mut summary_bounds: BTreeSet<(String, String)> = BTreeSet::new();
        let mut result_field_lifetimes = BTreeMap::new();
        collect_parameter_field_lifetimes(types, result, &mut result_field_lifetimes)?;
        if let Some(summary) = self.summaries.get(binding) {
            let map_origin = |origin: &recursive_lifetimes::Origin| {
                summary_origin_lifetime(
                    origin,
                    &parameter_lifetimes,
                    &parameter_binders,
                    &parameter_field_lifetimes,
                )
                .map_err(|what| {
                    Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot map a recursive lifetime summary origin to a declared lifetime: {what}. Annotate the result lifetime explicitly or name the borrowed field's lifetime"
                        ),
                    )
                })
            };
            let mut root_origins = BTreeSet::new();
            for (path, origins) in &summary.leaves {
                if path.is_empty() {
                    root_origins.extend(origins.iter().cloned());
                    if result.is_view() || result.is_ref() {
                        for origin in origins {
                            summary_sources.insert(map_origin(origin)?);
                        }
                    }
                    continue;
                }
                let target = result_field_lifetimes
                    .get(&path.join("."))
                    .cloned()
                    .ok_or_else(|| {
                        Diagnostic::new(
                            f.result.span,
                            format!(
                                "cannot map a recursive lifetime summary result path '{}' to a declared result field lifetime. Annotate the result type explicitly or name the borrowed field's lifetime",
                                path.join(".")
                            ),
                        )
                    })?;
                if summary.inferred_contract {
                    for origin in origins {
                        let source = map_origin(origin)?;
                        if source != target {
                            summary_bounds.insert((source, target.clone()));
                        }
                    }
                }
            }
            // A whole-value origin on a record result contributes to every
            // declared borrowed field. Try the leaf-specific input path first
            // (an identity/forwarding function keeps each field's own owner),
            // then conservatively fall back to the parameter root.
            if summary.inferred_contract
                && !root_origins.is_empty()
                && !(result.is_view() || result.is_ref())
            {
                for (field_path, target) in &result_field_lifetimes {
                    let components = field_path
                        .split('.')
                        .filter(|part| !part.is_empty())
                        .collect::<Vec<_>>();
                    for origin in &root_origins {
                        let mut specific = origin.clone();
                        specific
                            .path
                            .extend(components.iter().map(|part| (*part).to_owned()));
                        let source = match map_origin(&specific) {
                            Ok(source) => source,
                            Err(_) => map_origin(origin)?,
                        };
                        if source != *target {
                            summary_bounds.insert((source, target.clone()));
                        }
                    }
                }
            }
        }
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
                                &self.declared,
                                value,
                                &parameter_binder_lifetimes,
                                &parameter_field_lifetimes,
                                &mut body_lifetimes,
                            );
                        }
                        // The finite fixed point over direct call edges adds
                        // origins that no single syntactic return exposes,
                        // including mutually recursive forwarding. It is a
                        // union with the local seed, never a replacement: every
                        // owner seen either way stays in the summary.
                        body_lifetimes.extend(summary_sources.iter().cloned());
                        let inferred = body_lifetimes.into_iter().collect::<Vec<_>>();
                        if let [only] = inferred.as_slice() {
                            Some(only.clone())
                        } else if inferred.len() > 1 {
                            // The body can return a borrow from several input
                            // lifetimes. The result is an anonymous internal
                            // lifetime: it is outlived by every contributing
                            // source, so both backends still retain all owners
                            // through the result's last use. At a call site the
                            // shortest provable caller lifetime is selected, or
                            // the result stays anonymous when no order can be
                            // proved (see instantiate_result_lifetime).
                            Some(self.fresh_elided_lifetime())
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
        // Per-field result summaries add the outlives relation needed for
        // every declared result leaf. This is a guarantee, not a caller
        // precondition: it is derived from a possible returned origin.
        for (source, target) in &summary_bounds {
            if source == target || outlives(&lifetime_bounds, source, target) {
                continue;
            }
            if outlives(&lifetime_bounds, target, source) {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "cannot infer an outlives bound for result lifetime '{target}': the returned value can have both the longer lifetime '{source}' and the shorter one; use one shared lifetime or return the record fields with distinct lifetimes"
                    ),
                ));
            }
            lifetime_bounds.insert((source.clone(), target.clone()));
        }
        // Independent required preconditions. These are exported only for an
        // inferable declaration: an explicit outlives bound, trait/impl
        // contract, or function-value arrow is never silently strengthened.
        // Inherent methods own their contract like free functions; a trait
        // impl or generic impl method must match its trait/template exactly.
        let trait_bound_method = declared.impl_template.is_some()
            || self
                .trait_impls
                .values()
                .any(|methods| methods.values().any(|method| method.binding == binding));
        if !trait_bound_method
            && declared.default_specialization.is_none()
            && f.lifetimes
                .iter()
                .all(|lifetime| lifetime.bounds.is_empty())
            && self
                .summaries
                .get(binding)
                .is_some_and(|summary| summary.inferred_contract)
            && let Some(summary) = self.summaries.get(binding)
        {
            for requirement in &summary.requirements {
                let long = requirement_origin_lifetime(
                    &requirement.long,
                    &parameter_lifetimes,
                    &parameter_nested_lifetimes,
                    &parameter_binders,
                    &parameter_field_lifetimes,
                )
                .map_err(|what| {
                    Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot map a recursive lifetime requirement to a declared input lifetime: {what}. Annotate the outlives bound explicitly"
                        ),
                    )
                })?;
                let short = requirement_origin_lifetime(
                    &requirement.short,
                    &parameter_lifetimes,
                    &parameter_nested_lifetimes,
                    &parameter_binders,
                    &parameter_field_lifetimes,
                )
                .map_err(|what| {
                    Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot map a recursive lifetime requirement to a declared input lifetime: {what}. Annotate the outlives bound explicitly"
                        ),
                    )
                })?;
                if long == short || outlives(&lifetime_bounds, &long, &short) {
                    continue;
                }
                if outlives(&lifetime_bounds, &short, &long) {
                    return Err(Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot infer the recursive precondition '{long}: {short}': the opposite relation already holds; use one shared lifetime or bind the values to matching parameters"
                        ),
                    ));
                }
                lifetime_bounds.insert((long, short));
            }
        }
        lifetime_bounds = close_lifetime_bounds(lifetime_bounds);
        // An optional reference may be a parameter: it lives for the call,
        // like any reference argument. A result still needs provenance.
        crate::runtime_types::reject_optional_reference_boundary(types, result, f.result.span)?;
        // An explicit result lifetime need not repeat the caller's declared
        // outlives bounds: when the body returns a parameter borrow that does
        // not already outlive the result, infer that relation. Every returned
        // source contributes, which is conservative when a function can return
        // more than one parameter borrow. The inferred edges are closed
        // transitively and used by the same call-site validation as explicit
        // bounds.
        let inferred_internal_result = result_lifetime
            .as_deref()
            .is_some_and(|name| name.starts_with('<'));
        if (result_was_explicit || inferred_internal_result)
            && (result.is_view() || result.is_ref())
            && let Some(result_lifetime) = &result_lifetime
            && let Some(body) = &f.body
        {
            let mut returned = Vec::new();
            collect_block_returns(body, &mut returned);
            if let Some(tail) = &body.tail {
                returned.push(tail);
            }
            let mut sources = BTreeSet::new();
            for value in returned {
                value_lifetime_candidates(
                    resolution,
                    &self.declared,
                    value,
                    &parameter_binder_lifetimes,
                    &parameter_field_lifetimes,
                    &mut sources,
                );
            }
            // Recursive forwarding contributes its frozen fixed-point origins
            // in addition to the local syntactic seed.
            sources.extend(summary_sources.iter().cloned());
            // An explicit result may only receive bounds from a parameter's
            // own declared lifetime: selecting a different field lifetime of a
            // multi-lifetime record stays an explicit error. An inferred
            // anonymous result may also be bounded by record-field lifetimes,
            // which is exactly the multi-source intersection case.
            let parameter_bound_lifetimes = if inferred_internal_result {
                input_lifetimes
                    .iter()
                    .map(|(name, _, _)| name.clone())
                    .collect::<BTreeSet<_>>()
            } else {
                parameter_lifetimes
                    .iter()
                    .flatten()
                    .cloned()
                    .collect::<BTreeSet<_>>()
            };
            sources.retain(|source| parameter_bound_lifetimes.contains(source));
            for source in sources {
                if source == *result_lifetime
                    || outlives(&lifetime_bounds, &source, result_lifetime)
                {
                    continue;
                }
                if outlives(&lifetime_bounds, result_lifetime, &source) {
                    return Err(Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot infer an outlives bound for result lifetime '{result_lifetime}': the returned value has the longer lifetime '{source}'; use one shared lifetime instead"
                        ),
                    ));
                }
                lifetime_bounds.insert((source, result_lifetime.clone()));
            }
            lifetime_bounds = close_lifetime_bounds(lifetime_bounds);
        }
        // A structural row may now carry resolved borrow labels from its
        // annotation or a `..r` specialization. Each borrowed leaf is checked
        // below against the parameters that carry it; an unlabelled leaf stays
        // an explicit rejection because no caller lifetime relation can be
        // recovered for it.
        if result.is_view() {
            let Some(lifetime) = &result_lifetime else {
                return Err(Diagnostic::new(
                    f.result.span,
                    if result.is_mut_slice() {
                        "a borrowed '&mut [T]' result cannot be returned without an explicit lifetime, as in '-> &'a mut [T]'"
                    } else if result.is_text() {
                        "a borrowed '&str' result cannot be returned without an explicit lifetime, as in '-> &'a str'"
                    } else {
                        "a borrowed slice result cannot be returned without an explicit lifetime, as in '-> &'a [T]'"
                    },
                ));
            };
            let parameter_leaf_sets = parameters
                .iter()
                .map(|ty| crate::runtime_types::borrow_leaves(types, *ty))
                .collect::<Result<Vec<_>>>()?;
            let matching = parameter_lifetimes
                .iter()
                .zip(parameters.iter())
                .zip(&parameter_leaf_sets)
                .filter(|((parameter, _), leaves)| {
                    parameter
                        .as_ref()
                        .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                        || leaves.iter().any(|leaf| {
                            leaf.lifetime
                                .as_ref()
                                .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                        })
                })
                .map(|((parameter, ty), leaves)| (parameter, ty, leaves))
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
                && !matching.iter().any(|(_, ty, leaves)| {
                    ty.is_mut_slice()
                        || leaves.iter().any(|leaf| {
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
            let mutable_result = matches!(result, Type::RefMut(_));
            let matching = parameter_lifetimes
                .iter()
                .zip(parameters.iter())
                .filter(|(parameter, ty)| {
                    reference_reaches_type(types, **ty, result_pointee, mutable_result)
                        && parameter
                            .as_ref()
                            .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                })
                .collect::<Vec<_>>();
            let parameter_leaf_sets = parameters
                .iter()
                .map(|ty| crate::runtime_types::borrow_leaves(types, *ty))
                .collect::<Result<Vec<_>>>()?;
            let referent_leaf_sets = parameters
                .iter()
                .map(|ty| match ty.ref_pointee() {
                    Some(pointer) => {
                        crate::runtime_types::borrow_leaves(types, types.pointees[pointer])
                    }
                    None => Ok(Vec::new()),
                })
                .collect::<Result<Vec<_>>>()?;
            // A reference element stored in a by-value container parameter is
            // backed by caller-owned storage too; its declared element
            // lifetime supplies the same outlives relation.
            let container_leaf = parameter_leaf_sets.iter().any(|leaves| {
                leaves.iter().any(|leaf| {
                    leaf.lifetime
                        .as_ref()
                        .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                })
            });
            // A shared reference field stored inside the referent of a
            // reference parameter is caller-owned storage too. Its declared
            // field lifetime was instantiated in the parameter's record type,
            // so projecting it through the reference keeps that relation.
            let referent_field_leaf = |wanted_mutable: bool| {
                parameters
                    .iter()
                    .zip(&referent_leaf_sets)
                    .any(|(ty, leaves)| {
                        ty.is_ref()
                            && leaves.iter().any(|leaf| {
                                leaf.mutable == wanted_mutable
                                    && leaf.lifetime.as_ref().is_some_and(|name| {
                                        outlives(&lifetime_bounds, name, lifetime)
                                    })
                            })
                    })
            };
            if matching.is_empty() && !container_leaf && !referent_field_leaf(mutable_result) {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "reference result lifetime '{lifetime}' does not appear on any reference parameter to the same '{}' pointee that outlives it; a returned reference must borrow caller-owned storage",
                        types.name(result_pointee)
                    ),
                ));
            }
            if mutable_result
                && !matching
                    .iter()
                    .any(|(_, ty)| matches!(ty, Type::RefMut(_) | Type::SliceMut(_)))
                && !referent_field_leaf(true)
                && !parameter_leaf_sets.iter().any(|leaves| {
                    leaves.iter().any(|leaf| {
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
            // Every borrowed leaf of a returned record, including a structural
            // row, must name a signature label that a parameter carries. A
            // label from a `..r` specialization or an elided input is a rigid
            // occurrence identity, not a callee declaration, so it is validated
            // by the parameter relation rather than the declared-name set. The
            // field annotation is an obligation only: the ownership pass checks
            // each actual value origin against the same paths below.
            let parameter_leaf_sets = parameters
                .iter()
                .map(|ty| crate::runtime_types::borrow_leaves(types, *ty))
                .collect::<Result<Vec<_>>>()?;
            for leaf in crate::runtime_types::borrow_leaves(types, result)? {
                let Some(lifetime) = &leaf.lifetime else {
                    return Err(Diagnostic::new(
                        f.result.span,
                        "a returned record cannot carry a borrowed field without a declared lifetime; name the field's lifetime from a parameter, as in 'struct { view: &'a [T] }', or preserve it through a '..r' row variable",
                    ));
                };
                let declared_here = declared_lifetimes.contains(lifetime);
                let carried =
                    parameter_lifetimes
                        .iter()
                        .zip(parameters.iter())
                        .zip(&parameter_leaf_sets)
                        .any(|((parameter, ty), leaves)| {
                            (parameter
                                .as_ref()
                                .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                                && (!leaf.mutable
                                    || ty.is_mut_slice()
                                    || matches!(ty, Type::RefMut(_))))
                                || leaves.iter().any(|parameter_leaf| {
                                    parameter_leaf.lifetime.as_ref().is_some_and(|name| {
                                        outlives(&lifetime_bounds, name, lifetime)
                                    }) && (!leaf.mutable || parameter_leaf.mutable)
                                })
                        });
                if !carried {
                    let detail = if declared_here {
                        String::new()
                    } else {
                        format!(
                            " (lifetime '{lifetime}' is neither declared by this function nor supplied by a parameter's borrowed field)"
                        )
                    };
                    return Err(Diagnostic::new(
                        f.result.span,
                        if leaf.mutable {
                            format!(
                                "exclusive borrowed record result lifetime '{lifetime}' does not appear on an exclusive '&mut [T]' parameter or mutable record-field parameter that outlives it; a returned mutable field must borrow caller-owned exclusive storage{detail}"
                            )
                        } else {
                            format!(
                                "borrowed record result lifetime '{lifetime}' does not appear on any parameter that outlives it; a returned record must borrow caller-owned storage{detail}"
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
                            let names =
                                crate::runtime_types::effect_name_list(resolution, *effects);
                            format!("{{{}}}", names.join(", "))
                        })
                    } else {
                        type_values.next().map(|ty| types.name(*ty))
                    }
                })
                .collect::<Vec<_>>();
            format!("{}::<{}>", f.name, arguments.join(", "))
        };
        let effects = if f.row_omitted() {
            if !self.inferred_rows.contains(&binding) {
                return Err(Diagnostic::new(
                    declared.span,
                    "only a private function may omit its effect row; add '! {..}' after the result type",
                ));
            }
            // FND-ROWS-INFER: the row this pass assumes, grown by any
            // instance already checked.
            self.rows.guesses.get(&binding).copied().unwrap_or(0)
                | self.rows.found.get(&binding).copied().unwrap_or(0)
        } else {
            crate::runtime_types::effect_bits_with(resolution, &f.effects, &effect_substitution)?
        };
        let foreign = if let Some(symbol) = &f.foreign {
            if effects & IO == 0 && !PURE_HOST_SYMBOLS.contains(&symbol.as_str()) {
                return Err(Diagnostic::new(
                    declared.span,
                    "a foreign call has unchecked host side effects and requires the 'io' effect in its declared row",
                ));
            }
            let shape = result
                .layout()
                .and_then(|layout| types.enums[layout].result);
            validate_foreign_function(
                types,
                symbol.starts_with("kush_sys_"),
                &parameters,
                result,
                shape,
                &parameter_grades,
                result_grade,
                declared.span,
            )?;
            Some(ForeignFunction {
                symbol: symbol.clone(),
                parameters: parameters.clone(),
                result,
                fallible: shape,
            })
        } else {
            None
        };
        let default_trait = declared
            .default_specialization
            .map(|index| self.default_specializations[index].clone());
        // Rename only labels written in the callee declaration. Substituted
        // type arguments (including residual rows) already belong to the caller
        // and must never be captured by a same-spelled callee binder.
        let call_contract = if f.lifetimes.is_empty() {
            None
        } else {
            let mut scoped = substitution.clone();
            let mut binders = BTreeSet::new();
            let mut names = BTreeMap::new();
            for lifetime in &f.lifetimes {
                let identity = types.fresh_lifetime(&format!("callee '{}", lifetime.name));
                scoped
                    .lifetimes
                    .insert(lifetime.name.clone(), identity.clone());
                binders.insert(identity.clone());
                names.insert(identity, lifetime.name.clone());
            }
            let rename = |name: &String| {
                scoped
                    .lifetimes
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| name.clone())
            };
            Some(CallLifetimeContract {
                parameters: f
                    .parameters
                    .iter()
                    .filter(|p| !p.erased)
                    .map(|p| types.ty_in(split_grade(&p.ty).0, &scoped))
                    .collect::<Result<Vec<_>>>()?,
                result: types.ty_in(&result_ty, &scoped)?,
                binders,
                names,
                bounds: lifetime_bounds
                    .iter()
                    .map(|(a, b)| (rename(a), rename(b)))
                    .collect(),
            })
        };
        let index = self.signatures.len();
        self.signatures.push(Signature {
            call_contract,
            binding,
            origin: origin
                .filter(|_| specialized)
                .map(|span| (span, format!("'{name}'"))),
            name: name.clone(),
            parameters: parameters.clone(),
            result,
            effects,
            span: declared.span,
            substitution: substitution.types,
            consts: const_substitution,
            grades: grade_substitution,
            effect_arguments: effect_substitution,
            parameter_grades: parameter_grades.clone(),
            result_grade,
            parameter_lifetimes: parameter_lifetimes.clone(),
            result_lifetime: result_lifetime.clone(),
            lifetime_bounds: lifetime_bounds.clone(),
            self_type: substitution.self_type,
            default_trait,
            associated_consts,
        });
        self.instances.insert(key, index);
        if let Some(foreign) = foreign {
            self.foreign_functions.insert(index, foreign);
            // A foreign declaration has no source body. Store an inert,
            // already-checked body so the pending-body loop and the ownership
            // pass see the ordinary parameter/result shape, while the native
            // backend declares an import instead of defining this instance.
            let locals = parameters
                .iter()
                .map(|ty| Local {
                    ty: *ty,
                    mutable: false,
                    linear: false,
                    pinned: false,
                    grade: None,
                    span: declared.span,
                })
                .collect();
            self.bodies.push(Some(Function {
                name: name.clone(),
                parameters: parameters.len(),
                closure: None,
                capture_refs: vec![],
                capture_writes: vec![],
                locals,
                result,
                body: Block {
                    statements: Vec::new(),
                    tail: Some(Box::new(Expr {
                        kind: ExprKind::Constant(0),
                        ty: result,
                        span: declared.span,
                        resource: None,
                    })),
                    ty: result,
                },
                span: declared.span,
                resources: Vec::new(),
                local_resources: Vec::new(),
                parameter_grades: parameter_grades.clone(),
                result_grade,
                parameter_lifetimes: parameter_lifetimes.clone(),
                result_lifetime: result_lifetime.clone(),
                lifetime_bounds: lifetime_bounds.clone(),
                declared_lifetimes: declared
                    .ast
                    .lifetimes
                    .iter()
                    .map(|lifetime| lifetime.name.clone())
                    .collect(),
                index_relations: BTreeSet::new(),
                parameter_slots: None,
                local_borrowed: vec![],
                local_copyable: vec![],
                capability_parameters: vec![],
                shared_environment: false,
            }));
        } else {
            self.bodies.push(None);
            self.pending.push(index);
        }
        Ok(index)
    }
    /// Register a synthetic, already-checked function body (lambda or adapter).
    /// Synthetic entries share the same index space as declared instances, so
    /// an `FnValue` code pointer stays stable.
    /// Not counted against [`MAX_INSTANCES`]: each one belongs to an instance
    /// that is.
    fn add_synthetic(&mut self, signature: Signature, function: Function) -> Result<usize> {
        let index = self.signatures.len();
        self.signatures.push(signature);
        self.bodies.push(Some(function));
        Ok(index)
    }
    /// FND-ROWS-INFER: record the row a checked instance of an inferred
    /// function requires. Signatures made later see it at once; a body
    /// already checked that names the function saw a smaller row, so the pass
    /// is stale and runs again.
    fn settle_inferred_row(&mut self, binding: BindingId, required: u16) {
        let found = self.rows.found.entry(binding).or_insert(0);
        *found |= required;
        let row = *found | self.rows.guesses.get(&binding).copied().unwrap_or(0);
        let mut grew = false;
        for signature in &mut self.signatures {
            if signature.binding == binding && signature.effects != row {
                signature.effects = row;
                grew = true;
            }
        }
        if grew
            && self.checked_bodies.iter().any(|body| {
                self.body_refs
                    .get(body)
                    .is_some_and(|refs| refs.contains(&binding))
            })
        {
            self.rows.stale = true;
        }
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
            "propositions support linear integer comparisons over earlier integer and Bool parameters, constants, 'x + c', 'c * x', Bytes.len/Vec.len/Slice.len, and Bool atoms 'b' / '!b', joined by '&&'",
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
            ast::ExprKind::Unary {
                op: Kind::Bang,
                operand,
                ..
            } => format!("!({})", text(operand)),
            ast::ExprKind::Unary { operand, .. } => format!("-{}", text(operand)),
            ast::ExprKind::Bool(value) => value.to_string(),
            ast::ExprKind::Binary { op, left, right } => {
                let op = match op {
                    Kind::Lt => "<",
                    Kind::Le => "<=",
                    Kind::Gt => ">",
                    Kind::Ge => ">=",
                    Kind::EqEq => "==",
                    Kind::Plus => "+",
                    Kind::Minus => "-",
                    Kind::Star => "*",
                    Kind::AmpAmp => "&&",
                    Kind::PipePipe => "||",
                    Kind::Ne => "!=",
                    _ => "?",
                };
                format!("{} {op} {}", text(left), text(right))
            }
            _ => "?".into(),
        }
    }
    let linear = |e: &ast::Expr| -> Result<crate::facts::ParamLinear> {
        use crate::facts::ParamLinear;
        fn go(
            e: &ast::Expr,
            resolution: &Resolution,
            params: &BTreeMap<BindingId, usize>,
            unsupported: &dyn Fn(Span) -> Diagnostic,
        ) -> Result<ParamLinear> {
            match &e.kind {
                ast::ExprKind::Integer(n) => Ok(ParamLinear::constant(
                    n.parse().map_err(|_| unsupported(e.span))?,
                )),
                ast::ExprKind::Bool(value) => Ok(ParamLinear::constant(i128::from(*value))),
                ast::ExprKind::Unary {
                    op: Kind::Minus,
                    operand,
                    ..
                } => go(operand, resolution, params, unsupported)?
                    .negate()
                    .ok_or_else(|| unsupported(e.span)),
                ast::ExprKind::Name(_) => resolution
                    .reference(e.span)
                    .and_then(|id| params.get(&id))
                    .map(|i| ParamLinear::variable(ParamTerm::Param(*i), 1))
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
                    if *op == Kind::Plus {
                        l.add(&r)
                    } else {
                        l.sub(&r)
                    }
                    .ok_or_else(|| unsupported(e.span))
                }
                ast::ExprKind::Binary {
                    op: Kind::Star,
                    left,
                    right,
                } => {
                    let l = go(left, resolution, params, unsupported)?;
                    let r = go(right, resolution, params, unsupported)?;
                    if l.coefficients.is_empty() {
                        r.scale(l.constant)
                    } else if r.coefficients.is_empty() {
                        l.scale(r.constant)
                    } else {
                        None
                    }
                    .ok_or_else(|| unsupported(e.span))
                }
                ast::ExprKind::Call { callee, arguments } if arguments.len() == 1 => {
                    let builtin = resolution.reference(callee.span).is_some_and(|id| {
                        let b = &resolution.bindings[id];
                        b.kind == BindingKind::Builtin
                            && matches!(b.name.as_str(), "Bytes.len" | "Vec.len" | "Slice.len")
                    });
                    match (builtin, go(&arguments[0], resolution, params, unsupported)?) {
                        (true, argument)
                            if argument.coefficients.len() == 1
                                && argument.constant == 0
                                && argument.coefficients.values().all(|c| *c == 1) =>
                        {
                            let ParamTerm::Param(index) =
                                *argument.coefficients.keys().next().unwrap()
                            else {
                                return Err(unsupported(e.span));
                            };
                            Ok(ParamLinear::variable(ParamTerm::Len(index), 1))
                        }
                        _ => Err(unsupported(e.span)),
                    }
                }
                _ => Err(unsupported(e.span)),
            }
        }
        go(e, resolution, &runtime_before, &unsupported)
    };
    type Atom = (crate::facts::ParamLinear, Kind, crate::facts::ParamLinear);
    type Formula = Vec<Vec<Atom>>;
    const MAX_DISJUNCTS: usize = 32;
    let too_large = |span| {
        Diagnostic::new(
            span,
            "this proposition expands to more than 32 cases; split it into several erased parameters",
        )
    };
    let and = |a: Formula, b: Formula, span| -> Result<Formula> {
        if a.len() * b.len() > MAX_DISJUNCTS {
            return Err(too_large(span));
        }
        let mut out = Vec::new();
        for left in &a {
            for right in &b {
                let mut both = left.clone();
                both.extend(right.iter().cloned());
                out.push(both);
            }
        }
        Ok(out)
    };
    let or = |mut a: Formula, b: Formula, span| -> Result<Formula> {
        a.extend(b);
        if a.len() > MAX_DISJUNCTS {
            return Err(too_large(span));
        }
        Ok(a)
    };
    let negated = |op: &Kind| match op {
        Kind::Lt => Kind::Ge,
        Kind::Le => Kind::Gt,
        Kind::Gt => Kind::Le,
        Kind::Ge => Kind::Lt,
        Kind::EqEq => Kind::Ne,
        _ => Kind::EqEq,
    };
    let mut booleans = Vec::new();
    // Negation is pushed to the atoms (PROVE-DISJ).
    #[allow(clippy::too_many_arguments)]
    fn formula(
        e: &ast::Expr,
        positive: bool,
        linear: &dyn Fn(&ast::Expr) -> Result<crate::facts::ParamLinear>,
        and: &dyn Fn(Formula, Formula, Span) -> Result<Formula>,
        or: &dyn Fn(Formula, Formula, Span) -> Result<Formula>,
        negated: &dyn Fn(&Kind) -> Kind,
        booleans: &mut Vec<usize>,
        unsupported: &dyn Fn(Span) -> Diagnostic,
    ) -> Result<Formula> {
        use crate::facts::{ParamLinear, ParamTerm};
        match &e.kind {
            ast::ExprKind::Binary {
                op: op @ (Kind::AmpAmp | Kind::PipePipe),
                left,
                right,
            } => {
                let l = formula(
                    left,
                    positive,
                    linear,
                    and,
                    or,
                    negated,
                    booleans,
                    unsupported,
                )?;
                let r = formula(
                    right,
                    positive,
                    linear,
                    and,
                    or,
                    negated,
                    booleans,
                    unsupported,
                )?;
                if (*op == Kind::AmpAmp) == positive {
                    and(l, r, e.span)
                } else {
                    or(l, r, e.span)
                }
            }
            ast::ExprKind::Unary {
                op: Kind::Bang,
                operand,
                ..
            } => formula(
                operand,
                !positive,
                linear,
                and,
                or,
                negated,
                booleans,
                unsupported,
            ),
            ast::ExprKind::Binary {
                op: op @ (Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne),
                left,
                right,
            } => {
                let op = if positive { op.clone() } else { negated(op) };
                Ok(vec![vec![(linear(left)?, op, linear(right)?)]])
            }
            ast::ExprKind::Bool(value) => Ok(if *value == positive {
                vec![Vec::new()]
            } else {
                Vec::new()
            }),
            // A bare `Bool` parameter `b` is `b == 1`.
            ast::ExprKind::Name(_) => {
                let term = linear(e)?;
                let Some(ParamTerm::Param(index)) = term.coefficients.keys().next().copied() else {
                    return Err(unsupported(e.span));
                };
                booleans.push(index);
                Ok(vec![vec![(
                    term,
                    Kind::EqEq,
                    ParamLinear::constant(i128::from(positive)),
                )]])
            }
            _ => Err(unsupported(e.span)),
        }
    }
    let disjuncts = formula(
        body,
        true,
        &linear,
        &and,
        &or,
        &negated,
        &mut booleans,
        &unsupported,
    )?;
    let _ = indices;
    Ok(crate::facts::Proposition {
        disjuncts,
        booleans,
        text: text(body),
    })
}
/// The local whose storage a checked place lives in.
fn place_root_slot(expr: &Expr) -> Option<usize> {
    match &expr.kind {
        ExprKind::Local(slot)
        | ExprKind::Peek(slot)
        | ExprKind::Move(slot)
        | ExprKind::Borrow(slot) => Some(*slot),
        ExprKind::Project(base, _) | ExprKind::PlaceIndex { base, .. } => place_root_slot(base),
        ExprKind::BorrowPlace(base) | ExprKind::Coerce { value: base, .. } => place_root_slot(base),
        ExprKind::Slice { base, .. } => place_root_slot(base),
        _ => None,
    }
}
/// Source-like text of a postcondition clause, for diagnostics.
fn ensures_text(clause: &ast::Ensures) -> String {
    fn text(e: &ast::Expr) -> String {
        match &e.kind {
            ast::ExprKind::Name(n) | ast::ExprKind::Integer(n) => n.clone(),
            ast::ExprKind::Bool(value) => value.to_string(),
            ast::ExprKind::Field { value, name } => format!("{}.{name}", text(value)),
            ast::ExprKind::Is { value, variant } => format!("{} is {variant}", text(value)),
            ast::ExprKind::Unary {
                op: Kind::Bang,
                operand,
                ..
            } => format!("!({})", text(operand)),
            ast::ExprKind::Unary { operand, .. } => format!("-{}", text(operand)),
            ast::ExprKind::Binary { op, left, right } => {
                let op = match op {
                    Kind::Lt => "<",
                    Kind::Le => "<=",
                    Kind::Gt => ">",
                    Kind::Ge => ">=",
                    Kind::EqEq => "==",
                    Kind::Ne => "!=",
                    Kind::Plus => "+",
                    Kind::Minus => "-",
                    Kind::Star => "*",
                    Kind::AmpAmp => "&&",
                    Kind::PipePipe => "||",
                    _ => "?",
                };
                // Parenthesise operands that bind looser than `op`.
                let level = |e: &ast::Expr| match &e.kind {
                    ast::ExprKind::Binary { op, .. } => match op {
                        Kind::PipePipe => 1,
                        Kind::AmpAmp => 2,
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne => 3,
                        Kind::Plus | Kind::Minus => 4,
                        _ => 5,
                    },
                    _ => 6,
                };
                let own = level(e);
                let side = |operand: &ast::Expr, right: bool| {
                    let inner = level(operand);
                    if inner < own || (right && inner == own && op != "&&" && op != "||") {
                        format!("({})", text(operand))
                    } else {
                        text(operand)
                    }
                };
                format!("{} {op} {}", side(left, false), side(right, true))
            }
            _ => "?".into(),
        }
    }
    let guard = match &clause.guard {
        ast::EnsuresGuard::Always => String::new(),
        ast::EnsuresGuard::Result(true) => "result => ".into(),
        ast::EnsuresGuard::Result(false) => "!result => ".into(),
        ast::EnsuresGuard::Variant { name, binders, .. } if binders.is_empty() => {
            format!("{name} => ")
        }
        ast::EnsuresGuard::Variant { name, binders, .. } => format!(
            "{name}({}) => ",
            binders
                .iter()
                .map(|(binder, _)| binder.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    };
    format!("{guard}{{ {} }}", text(&clause.body))
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
/// Runtime-length arrays in a signature. A parameter or result type may
/// mention `[T; n <= C]` anywhere the call site rewrites binders (references,
/// containers, tuples, arrays, records, rows, unions), where `n` is an
/// earlier `i64` parameter (any `i64` parameter for the result; never a
/// method receiver). Foreign signatures, `fn` types, and trait object types
/// may not mention them: nothing substitutes the caller's binder there.
fn validate_runtime_length_signature(
    resolution: &Resolution,
    f: &ast::Function,
    method: bool,
) -> Result<()> {
    fn is_i64(ty: &ast::Type) -> bool {
        matches!(&split_grade(ty).0.kind, ast::TypeKind::Named { path, arguments } if path.len() == 1 && path[0] == "i64" && arguments.is_empty())
    }
    fn walk(
        resolution: &Resolution,
        ty: &ast::Type,
        allowed: &BTreeSet<BindingId>,
        restricted: Option<&'static str>,
    ) -> Result<()> {
        match &ty.kind {
            ast::TypeKind::Array(element, length) => {
                if let Some((binder, capacity)) = runtime_length_parts(length) {
                    if let Some(reason) = restricted {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!("{reason} cannot mention a runtime-length array [T; n <= C]"),
                        ));
                    }
                    let id = runtime_length_binder(resolution, binder)?;
                    if !allowed.contains(&id) {
                        return Err(Diagnostic::new(
                            binder.span,
                            "the length of a runtime-length array in a signature must be an earlier i64 parameter of the same function",
                        ));
                    }
                    walk(resolution, capacity, allowed, restricted)?;
                }
                walk(resolution, element, allowed, restricted)
            }
            ast::TypeKind::Borrow { inner, .. } => walk(resolution, inner, allowed, restricted),
            ast::TypeKind::Graded { inner, .. } => walk(resolution, inner, allowed, restricted),
            ast::TypeKind::Named { arguments, .. } => {
                for argument in arguments {
                    walk(resolution, argument, allowed, restricted)?;
                }
                Ok(())
            }
            ast::TypeKind::Tuple(items) => {
                for item in items {
                    walk(resolution, item, allowed, restricted)?;
                }
                Ok(())
            }
            ast::TypeKind::Slice(inner) => walk(resolution, inner, allowed, restricted),
            ast::TypeKind::Dyn(bounds) => {
                for inner in ast::dyn_types(bounds) {
                    walk(resolution, inner, allowed, Some("a trait object type"))?;
                }
                Ok(())
            }
            ast::TypeKind::Structural { fields, .. } => {
                for field in fields {
                    walk(resolution, &field.ty, allowed, restricted)?;
                }
                Ok(())
            }
            ast::TypeKind::Binary { left, right, .. } => {
                walk(resolution, left, allowed, restricted)?;
                walk(resolution, right, allowed, restricted)
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                let reason = Some("a fn/once fn type");
                for parameter in parameters {
                    walk(resolution, &parameter.ty, allowed, reason)?;
                }
                walk(resolution, result, allowed, reason)
            }
            _ => Ok(()),
        }
    }
    let restricted = if f.foreign.is_some() {
        Some("a foreign function signature")
    } else {
        None
    };
    // A method receiver is never a length binder: the call site substitutes
    // binders from the explicit argument list only.
    let binders = if method {
        &f.parameters[1.min(f.parameters.len())..]
    } else {
        &f.parameters[..]
    };
    let all = binders
        .iter()
        .filter(|parameter| !parameter.erased && is_i64(&parameter.ty))
        .filter_map(|parameter| resolution.binder(parameter.span))
        .collect::<BTreeSet<_>>();
    let mut earlier = BTreeSet::new();
    for (index, parameter) in f.parameters.iter().enumerate() {
        if parameter.erased {
            continue;
        }
        walk(resolution, &parameter.ty, &earlier, restricted)?;
        if is_i64(&parameter.ty)
            && (!method || index > 0)
            && let Some(id) = resolution.binder(parameter.span)
        {
            earlier.insert(id);
        }
    }
    walk(resolution, &f.result, &all, restricted)
}

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
            if let Some((binder, capacity)) = runtime_length_parts(length) {
                runtime_length_binder(resolution, binder)?;
                return validate_length_template(resolution, capacity, consts);
            }
            validate_length_template(resolution, length, consts)
        }
        ast::TypeKind::Dyn(bounds) => {
            for inner in ast::dyn_types(bounds) {
                validate_type_template(resolution, inner, consts, false, true)?;
            }
            Ok(())
        }
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
                        "array length depends on a runtime value; give a runtime-length array an inline capacity as [T; n <= C], or use Vec<T> or a &[T] view",
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
        ast::TypeKind::Structural { fields, row, .. } => {
            for field in fields {
                validate_type_template(resolution, &field.ty, consts, false, false)?;
            }
            if let Some(row) = row {
                validate_type_template(resolution, row, consts, false, false)?;
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
        ast::TypeKind::Lifetime(_)
        | ast::TypeKind::SelfType
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. } => Ok(()),
        ast::TypeKind::Integer(_) | ast::TypeKind::Bool(_) => Ok(()),
    }
}

/// Whether a written type mentions a runtime-length array `[T; n <= C]`
/// anywhere.
pub(crate) fn type_mentions_runtime_length(ty: &ast::Type) -> bool {
    match &ty.kind {
        ast::TypeKind::Array(element, length) => {
            runtime_length_parts(length).is_some() || type_mentions_runtime_length(element)
        }
        ast::TypeKind::Borrow { inner, .. }
        | ast::TypeKind::Graded { inner, .. }
        | ast::TypeKind::Slice(inner) => type_mentions_runtime_length(inner),
        ast::TypeKind::Dyn(bounds) => ast::dyn_types(bounds).any(type_mentions_runtime_length),
        ast::TypeKind::Named { arguments, .. } => {
            arguments.iter().any(type_mentions_runtime_length)
        }
        ast::TypeKind::Tuple(items) => items.iter().any(type_mentions_runtime_length),
        ast::TypeKind::Structural { fields, row, .. } => {
            fields
                .iter()
                .any(|field| type_mentions_runtime_length(&field.ty))
                || row.as_deref().is_some_and(type_mentions_runtime_length)
        }
        ast::TypeKind::Binary { left, right, .. } => {
            type_mentions_runtime_length(left) || type_mentions_runtime_length(right)
        }
        ast::TypeKind::Function {
            parameters, result, ..
        } => {
            parameters
                .iter()
                .any(|parameter| type_mentions_runtime_length(&parameter.ty))
                || type_mentions_runtime_length(result)
        }
        _ => false,
    }
}

/// Split the length of a runtime-length array `[T; n <= C]` into the binder
/// expression `n` and the compile-time capacity `C`.
pub(crate) fn runtime_length_parts(length: &ast::Type) -> Option<(&ast::Type, &ast::Type)> {
    match &length.kind {
        ast::TypeKind::Binary {
            op: Kind::Le,
            left,
            right,
        } => Some((left, right)),
        _ => None,
    }
}

/// Resolve the length binder of `[T; n <= C]`. It must be a plain name of a
/// runtime parameter or local; whether it is an immutable `i64` is checked
/// where the binding's type is known.
pub(crate) fn runtime_length_binder(
    resolution: &Resolution,
    binder: &ast::Type,
) -> Result<BindingId> {
    let error = || {
        Diagnostic::new(
            binder.span,
            "the length of [T; n <= C] must be the name of an immutable i64 parameter or local",
        )
    };
    let ast::TypeKind::Named { path, arguments } = &binder.kind else {
        return Err(error());
    };
    if path.len() != 1 || !arguments.is_empty() {
        return Err(error());
    }
    let id = resolution.reference(binder.span).ok_or_else(error)?;
    if !matches!(
        resolution.bindings[id].kind,
        BindingKind::Parameter | BindingKind::Local
    ) {
        return Err(error());
    }
    Ok(id)
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
        ast::TypeKind::Structural { fields, row, .. } => {
            fields
                .iter()
                .any(|field| type_references_binding(resolution, &field.ty, id))
                || row
                    .as_ref()
                    .is_some_and(|row| type_references_binding(resolution, row, id))
        }
        ast::TypeKind::Dyn(bounds) => {
            ast::dyn_types(bounds).any(|inner| type_references_binding(resolution, inner, id))
        }
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
        | ast::TypeKind::Infer
        | ast::TypeKind::Capability { .. }
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
    /// Whether a `break` leaves this loop (then exit values need not be
    /// the loop-head values).
    broke: bool,
    /// The checked `invariant { P }` of a `while`, proved at each `continue`.
    invariant: Option<Expr>,
}
/// One inclusion constraint on an effect row during a call: the declared row
/// `fixed | e1 | e2 ...` must cover the actual callable row. Constraints are
/// accumulated across every higher-order argument before a finite solver picks
/// a unique minimal specialization.
/// How an unannotated lambda's row is decided.
#[derive(Clone, Copy, Debug)]
enum LambdaRow {
    Declared,
    /// From the expected arrow (bodies that handle or perform).
    Fixed(u16),
    /// The union of the effects the body requires.
    FromBody,
}
#[derive(Clone, Copy, Debug)]
struct LambdaInference {
    result_from_body: bool,
    row: LambdaRow,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum LambdaContext {
    Ordinary,
    TaskScope,
    Quotation,
}
/// Types a call or a binding's first use supplies for an unannotated
/// lambda's parameters and result (I-LAMBDA-INFER).
#[derive(Clone, Debug, Default)]
struct LambdaHint {
    parameters: Vec<Option<Type>>,
    result: Option<Type>,
}

#[derive(Debug, Clone)]
struct EffectConstraint {
    row: crate::runtime_types::EffectRowTerm,
    actual: u16,
    span: Span,
}

/// One declared effect operation. Dynamic `perform` calls use this signature;
/// lexical handlers still drive direct performs, while the declaration lets a
/// called function find the handler on the runtime stack.
#[derive(Clone, Copy)]
struct EffectOperation {
    id: usize,
    parameter: Type,
    result: Type,
    /// Built-in effects a handler may have (`effect Op: P -> R ! {..}`);
    /// every dynamic perform requires them.
    latent: u16,
}
/// The canonical kernel index of an admitted runtime scalar binding.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ScalarValue {
    /// A symbolic binder at this absolute position in `kernel_locals`.
    Position(usize),
    /// A machine literal known on every path reaching the current point.
    Literal(Term),
    /// A value changed on only some path or across a loop iteration. It has no
    /// stable index until [`Checker::fresh_scalar_value`] appends a binder.
    Unknown,
}
/// One lexical effect-handler binding. The handler is materialized in a hidden
/// local so `perform` can call it and the ownership pass can enforce the
/// callable's one-shot/linear contract.
/// What `checked_effect_body` needs to build a `Suspendable` node.
struct SuspendableSite {
    name: String,
    /// Types of the values the handler closure captures.
    handler_captures: Vec<Type>,
    /// The handler is a `once` callable, consumed by its first perform.
    handler_once: bool,
    handler_parameter: Type,
    /// Locals the handler captures by reference (it reads or writes them).
    handler_refs: Vec<usize>,
    handler_function: Option<usize>,
    /// The body performs the operation lexically outside its tail.
    lexical: bool,
    operation: Option<usize>,
    multishot: bool,
    /// The handler takes a `multi fn` token (docs/multishot-capabilities.md).
    multi: bool,
    handler_writes: Vec<usize>,
    effects: u16,
    token_effects: u16,
    /// The handler local of a capability whose calls become await points.
    capability_slot: Option<usize>,
}
struct HandlerScope {
    operation: String,
    parameter: Type,
    result: Type,
    slot: usize,
    handler_parameter: Type,
    handler_result: Type,
    effects: u16,
    /// The handler accepts the copyable multishot resumption token. Only a
    /// capture-free continuation has that representation.
    multishot: bool,
    /// The multishot token is a `multi fn` with a continuation-stack
    /// environment instead of a code pointer.
    multi: bool,
    /// Performs of this operation become `Suspend` points of a suspendable
    /// body instead of identity-token handler calls.
    region: bool,
    /// Suspension points issued so far for this handle.
    points: usize,
    /// The handle pushes a dynamic handler frame (declared operation).
    declared: bool,
    /// Abortive operation (`-> Never`): the label of the `AbortScope` its
    /// performs leave (E-ABORT-LEXICAL).
    abort: Option<usize>,
    /// Abortive operations that may leave the body through the resumption
    /// token (its row; E-ABORT-INTERACT).
    token_effects: u16,
    /// The handler was moved into its dynamic frame: a capturing one-shot
    /// handler of a declared operation, reusable or consumed by its first
    /// perform. Its performs, lexical ones included, go through the frame.
    in_frame: bool,
}

struct Checker<'a, 't> {
    /// FND-ROWS-INFER: this body's row is being inferred; `effects` holds
    /// every effect and `required_effects` collects the row.
    inferring_row: bool,
    /// Explicit quotation holes, keyed by original source occurrence. During
    /// template checking their slots are remapped to captured parameters.
    quote_holes: BTreeMap<(usize, usize), usize>,
    quote_splices: BTreeMap<(usize, usize), (usize, usize)>,
    types: &'t mut Types<'a>,
    resolution: &'a Resolution,
    functions: &'t mut Functions<'a>,
    substitution: BTreeMap<BindingId, Type>,
    /// Concrete values of this instance's compile-time natural parameters.
    consts: BTreeMap<BindingId, usize>,
    /// Concrete values of this instance's abstract grade parameters.
    grades: BTreeMap<BindingId, Grade>,
    /// Concrete effect rows of this instance's `e: Effects` parameters.
    effect_arguments: BTreeMap<BindingId, u16>,
    locals: Vec<Local>,
    slots: BTreeMap<BindingId, usize>,
    result: Type,
    /// Declared or freshly elided lifetime of each runtime parameter of the
    /// function currently being checked. Lambda captures inherit a declared
    /// parameter lifetime so a captured slice keeps the caller's identity.
    parameter_lifetimes: Vec<Option<String>>,
    /// Every lifetime declared by the function currently being checked. Nested
    /// record instantiations may mention these labels even when no runtime
    /// parameter is itself a reference, so the contextual witness classifies
    /// them as free occurrence labels instead of dropping the whole check.
    declared_lifetimes: BTreeSet<String>,
    /// Static result-transfer contract of the function/lambda currently being
    /// checked. Distinguishes owning `@[1]` transfers from must-use copyable
    /// transfers when a returned value is observed.
    result_grade: Option<Grade>,
    /// Declared result lifetime and outlives bounds of the function currently
    /// being checked. They are the evidence source for same-scope lifetime
    /// witnesses; the witness never invents an edge.
    result_lifetime: Option<String>,
    lifetime_bounds: BTreeSet<(String, String)>,
    /// Nonzero while checking an expression that is being coerced into a
    /// callee parameter. Callee-declared labels are instantiated by the call
    /// and are governed by the callee contract plus the ownership provenance
    /// mapping, so the same-scope contextual witness does not reinterpret them
    /// as the caller's declared lifetimes.
    call_boundary: usize,
    effects: u16,
    depth: usize,
    loops: Vec<Loop>,
    facts: crate::facts::Facts,
    /// Slots assigned by the function or lambda currently being checked.
    /// A lambda turns this set into `Function::capture_writes`, which decides
    /// whether a by-reference capture is a shared or exclusive loan.
    written_slots: BTreeSet<usize>,
    /// Captured outer slots that a call to a closure binding may write.
    /// Populated when a local is bound to a capturing lambda and consulted by
    /// indirect calls so proof facts never survive a writing call.
    closure_writes: BTreeMap<usize, Vec<usize>>,
    /// Types captured by the closure value a local holds, when known.
    closure_captures: BTreeMap<usize, Vec<Type>>,
    /// Types filled into omitted lambda annotations (`fn(x) { ... }`), keyed
    /// by the hole's span (I-LAMBDA-INFER).
    lambda_holes: BTreeMap<(usize, usize), Type>,
    /// Parameter/result types a generic call or a binding's first use
    /// supplies for the next unannotated lambda.
    lambda_hint: Option<LambdaHint>,
    /// Union of every effect `require`d in the current lambda body; an
    /// omitted lambda row is inferred as exactly these bits.
    required_effects: std::cell::Cell<u16>,
    /// The binder span of `handle Op as op`, consumed by `handle_effect`.
    pending_capability: Option<(String, Span)>,
    /// Constants whose value is being checked, to reject a cycle.
    expanding_constants: Vec<BindingId>,
    /// Set while an element write borrows a `where len >= N` field: the only
    /// exclusive borrow of such a field that cannot shorten it.
    writing_bounded_field: bool,
    /// Set while checking `place.replace(v)` on a length-refined field: the
    /// length `v` must be checked to have.
    replace_min_length: Option<i64>,
    /// The invariant the next checked block (a `while` body) must prove at
    /// its end.
    body_invariant: Option<Expr>,
    /// Reference parameters declared `where len >= N`, by slot.
    parameter_lengths: BTreeMap<usize, i64>,
    /// Set just before checking a refined parameter in a use that keeps its
    /// bound (a non-shortening method receiver).
    refined_use_ok: bool,
    /// Spans of call arguments passed to a length-refined parameter: such a
    /// parameter keeps the bound, so a refined place may be lent there.
    lending_spans: BTreeSet<(usize, usize)>,
    /// Next `AbortScope` label of this checker (unique per function body).
    abort_labels: usize,
    /// Locals holding a second-class capability (EFF-CAP-LEXICAL).
    capability_slots: BTreeSet<usize>,
    /// Capabilities that may be passed to functions: `cap` parameters and
    /// noncapturing, one-shot, tail-resumptive handlers. Others can only be
    /// performed in their own handle body (EFF-CAP-RESUME).
    capability_passable: BTreeSet<usize>,
    /// Capability locals of non-tail, noncapturing, one-shot handlers: they
    /// may be passed to `cap` parameters, and such calls become await
    /// points of the handled body (EFF-CAP-RESUME-CALLS).
    capability_resumable: BTreeSet<usize>,
    /// EFF-CAP-RESUME-CAPTURING: capability slots of capturing handlers kept
    /// in their dynamic frame: declared operation id and handler arrow type.
    capability_framed: BTreeMap<usize, (usize, usize, u16)>,
    /// `cap` parameters of this function: they may be bound to a handler
    /// with code after `resume`, so a lambda cannot capture them.
    capability_parameter_slots: BTreeSet<usize>,
    /// Set while checking an argument passed to a `cap` parameter.
    capability_argument: bool,
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
    /// THREAD-SCOPE: the immediate scope lambda is a `Thread.scope`.
    scope_parallel: bool,
    /// Kind of the scope lambda about to be checked by `task_callable`.
    next_scope_parallel: bool,
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
    /// Canonical index value of an admitted scalar binding. `Position` names a
    /// symbolic binder; `Literal` is a machine literal known for every branch
    /// reaching this point; `Unknown` has no stable index until a fresh binder
    /// is appended at a branch or loop join.
    scalar_values: BTreeMap<BindingId, ScalarValue>,
    /// Erased proof-valued locals bound by `let p = <proof>`. Each entry stores
    /// the checked kernel term together with the context length at which it was
    /// elaborated, so later context growth can shift its free variables.
    proof_values: BTreeMap<BindingId, (Term, usize)>,
    /// Declared effect operations used by dynamic performs in called bodies.
    effect_operations: &'t BTreeMap<String, EffectOperation>,
    /// Lexically active effect handlers, innermost last. A handler is visible
    /// only to direct `perform` expressions in the same function body.
    handlers: Vec<HandlerScope>,
    /// Pending effect-row inclusion constraints for the current inference
    /// group. `infer` takes a mark and solves them after every argument has
    /// contributed its evidence.
    effect_constraints: Vec<EffectConstraint>,
    /// Cross-parameter backtracking state. `unify_plan` is the current choice
    /// sequence for multi-variable union partitions, `unify_decisions`
    /// records each decision's cardinality in the current replay, and
    /// `unify_plan_active` distinguishes a planned replay from ordinary
    /// left-to-right inference (which deterministically takes choice zero).
    unify_plan: Vec<usize>,
    unify_decisions: Vec<usize>,
    unify_plan_active: bool,
    /// Set when the ordinary inference pass took the first of several choices
    /// at a partition or indexed-union decision. Such a call is then searched
    /// exhaustively and accepted only when one substitution survives.
    unify_open_choice: bool,
    /// Type variables bound by a multi-variable union partition during the
    /// current `infer` call. Parameters that mention one of them are checked
    /// without a tentative expected type so the replay can reconsider the
    /// partition instead of failing during contextual checking.
    partition_bound: BTreeSet<BindingId>,
    /// Type variables bound as structural row tails in the current `infer`
    /// call. Parameters mentioning them are checked without a tentative
    /// expected row so a residual-row mismatch is reported by unification.
    row_bound: BTreeSet<BindingId>,
    /// Hidden owner bindings hoisted out of an expression so a checked
    /// reference to a temporary has real storage. Each enclosing statement
    /// list drains the entries created while checking it; the local's resource
    /// drops at that block's end, after every checked reference's last use.
    hoisted: Vec<Statement>,
    /// Last index-place identity handed out (see `index_place_id`).
    next_index_place: usize,
    /// Proved-distinct index-place pairs of the bodies checked so far.
    index_relations: BTreeSet<(usize, usize)>,
    /// Runtime-length binder renaming for the call whose `infer` is about to
    /// run: callee `i64` parameter -> caller binding passed for it.
    pending_lengths: BTreeMap<BindingId, BindingId>,
    /// ENSURES: the current function's postconditions, if any.
    ensures_context: Option<EnsuresContext>,
    /// The expression being checked is a value the function returns.
    ensures_tail: bool,
    /// ENSURES-PREDICATES: nesting of predicate expansions in a proposition.
    ensures_depth: std::cell::Cell<usize>,
    /// The `if`/`match`/block being checked is in return position, so its
    /// branch tails are too.
    branch_tail: bool,
}
/// The postconditions of the function being checked (ENSURES).
#[derive(Clone)]
struct EnsuresContext {
    clauses: Vec<ast::Ensures>,
    /// Runtime parameters: binder and slot.
    params: Vec<(BindingId, usize)>,
    result: Type,
}
/// A symbolic value in a postcondition: a path from a root, or a checked
/// expression (a construction or a scalar expression).
#[derive(Clone)]
enum Sym {
    Path(crate::facts::Root, Vec<crate::facts::Step>),
    Value(Box<Expr>),
    Unknown,
}
/// One actual lifetime supplied for a callee-declared binder at a parameter
/// occurrence. The polarity decides whether the actual identity must equal the
/// binder (invariant), outlive it (covariant), or be outlived by it
/// (contravariant).
#[derive(Clone, Debug)]
struct CallLifetimeOccurrence {
    actual: String,
    polarity: crate::variance::LabelPolarity,
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
    /// Every concrete effect bit in this program: the four built-ins plus each
    /// declared `effect` operation's row bit.
    fn all_effects(&self) -> u16 {
        EFFECT_BITS
            | self
                .resolution
                .effect_bits
                .values()
                .copied()
                .fold(0u16, |bits, bit| bits | bit)
    }
    /// Row bit of a declared effect operation, or zero for an undeclared
    /// lexically handled operation name.
    fn operation_effect(&self, operation: &str) -> u16 {
        self.resolution
            .effect_bits
            .get(operation)
            .copied()
            .unwrap_or(0)
    }
    fn require(&self, effects: u16, span: Span) -> Result<()> {
        self.required_effects
            .set(self.required_effects.get() | effects);
        let missing = effects & !self.effects;
        if missing == 0 {
            return Ok(());
        }
        let mut names = [(IO, "io"), (ALLOC, "alloc"), (SUSPEND, "suspend")]
            .into_iter()
            .filter_map(|(bit, name)| (missing & bit != 0).then_some(name.to_owned()))
            .collect::<Vec<_>>();
        names.extend(crate::runtime_types::user_effect_names(
            self.resolution,
            missing,
        ));
        Err(Diagnostic::new(
            span,
            format!(
                "operation requires effects {{{}}}; add them to the function signature",
                names.join(", ")
            ),
        ))
    }
    fn ty(&mut self, ty: &ast::Type) -> Result<Type> {
        reject_capability_type(ty)?;
        if matches!(ty.kind, ast::TypeKind::Infer) {
            return self
                .lambda_holes
                .get(&(ty.span.start, ty.span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(
                        ty.span,
                        "cannot infer this lambda type: no expected function type, generic call, or first use fixes it; add the annotation",
                    )
                });
        }
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
            lengths: BTreeMap::new(),
        };
        let lowered = self.types.ty_in(ty, &subst)?;
        self.check_runtime_lengths(ty)?;
        Ok(lowered)
    }
    /// The local slot of a runtime-length binder. The binder must be an
    /// immutable `i64` parameter or local in scope, so the value the type
    /// describes can never change.
    fn runtime_length_slot(&self, binder: BindingId, span: Span) -> Result<usize> {
        let error = || {
            Diagnostic::new(
                span,
                format!(
                    "the length '{}' of a runtime-length array must be an immutable i64 parameter or local in scope",
                    self.resolution.bindings[binder].name
                ),
            )
        };
        let slot = *self.slots.get(&binder).ok_or_else(error)?;
        let local = &self.locals[slot];
        if local.ty != Type::I64 || local.mutable {
            return Err(error());
        }
        Ok(slot)
    }
    /// Validate every runtime-length binder written in an annotation in this
    /// body. Binders that arrive through a generic substitution were checked
    /// where the caller wrote them. A written callable type cannot carry one:
    /// an indirect call cannot substitute the caller's binder.
    fn check_runtime_lengths(&self, ty: &ast::Type) -> Result<()> {
        fn walk(checker: &Checker<'_, '_>, ty: &ast::Type, in_callable: bool) -> Result<()> {
            match &ty.kind {
                ast::TypeKind::Array(element, length) => {
                    if let Some((binder, _)) = runtime_length_parts(length) {
                        if in_callable {
                            return Err(Diagnostic::new(
                                ty.span,
                                "fn/once fn types and lambdas cannot mention a runtime-length array [T; n <= C]; call a named function instead",
                            ));
                        }
                        let id = runtime_length_binder(checker.resolution, binder)?;
                        checker.runtime_length_slot(id, binder.span)?;
                    }
                    walk(checker, element, in_callable)
                }
                ast::TypeKind::Named { arguments, .. } => {
                    for argument in arguments {
                        walk(checker, argument, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Tuple(items) => {
                    for item in items {
                        walk(checker, item, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Dyn(bounds) => {
                    for inner in ast::dyn_types(bounds) {
                        walk(checker, inner, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Slice(inner)
                | ast::TypeKind::Borrow { inner, .. }
                | ast::TypeKind::Graded { inner, .. } => walk(checker, inner, in_callable),
                ast::TypeKind::Structural { fields, .. } => {
                    for field in fields {
                        walk(checker, &field.ty, in_callable)?;
                    }
                    Ok(())
                }
                ast::TypeKind::Binary { left, right, .. } => {
                    walk(checker, left, in_callable)?;
                    walk(checker, right, in_callable)
                }
                ast::TypeKind::Function {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        walk(checker, &parameter.ty, true)?;
                    }
                    walk(checker, result, true)
                }
                _ => Ok(()),
            }
        }
        walk(self, ty, false)
    }
    /// A slice pattern over a shared `&DynArray<T, C>` (or `&[T; n <= C]`)
    /// scrutinee. Element names bind `&T` into the array's slots, so owning
    /// elements are matched without moving or copying them; `..rest` binds a
    /// `&[T]` view of the middle. Copyable elements may also use ordinary
    /// by-value sub-patterns, which test copies.
    ///
    /// Over an exclusive `&mut` scrutinee, element names bind `&mut T` and
    /// `..rest` binds `&mut [T]`. Each such binding gets its own split group,
    /// so the bindings are pairwise disjoint loans of the array. Like
    /// `&mut s[i]`, this requires non-owning, non-linear, non-view elements.
    fn borrowed_dyn_pattern(
        &mut self,
        parts: &[ast::Pattern],
        element: Type,
        capacity: usize,
        exclusive: bool,
        span: Span,
        bindings: &mut BTreeMap<String, (usize, Type)>,
    ) -> Result<Pattern> {
        let copyable =
            !(self.owned_type(element) || self.linear_type(element) || element.is_view());
        if exclusive && (!copyable || element.is_ref()) {
            return Err(Diagnostic::new(
                span,
                "a '&mut DynArray' pattern binds '&mut T' element references, which would alias an owning, linear, or view element; match a shared borrow instead, or move elements out with DynArray.pop",
            ));
        }
        let element_pointer = self.types.pointer(element);
        let (reference, view) = if exclusive {
            (
                Type::RefMut(element_pointer),
                Type::SliceMut(element_pointer),
            )
        } else {
            (Type::Ref(element_pointer), Type::Slice(element_pointer))
        };
        let mut prefix = Vec::new();
        let mut suffix = Vec::new();
        let mut rest = false;
        let mut rest_binding = None;
        let mut exclusive_slots = BTreeSet::new();
        let bind = |checker: &mut Self,
                    name: &str,
                    ty: Type,
                    part: &ast::Pattern,
                    bindings: &mut BTreeMap<String, (usize, Type)>,
                    exclusive_slots: &mut BTreeSet<usize>|
         -> Result<usize> {
            if let Some((slot, previous)) = bindings.get(name) {
                // Two exclusive references to different elements cannot share
                // one name.
                if exclusive && exclusive_slots.contains(slot) {
                    return Err(Diagnostic::new(
                        part.span,
                        format!("'{name}' is bound twice in one '&mut DynArray' pattern"),
                    ));
                }
                checker.expect(ty, *previous, part.span)?;
                return Ok(*slot);
            }
            let slot = checker.bind(part.span, ty, false)?;
            bindings.insert(name.to_owned(), (slot, ty));
            exclusive_slots.insert(slot);
            Ok(slot)
        };
        for part in parts {
            let checked = match &part.kind {
                ast::PatternKind::Rest(name) => {
                    if rest {
                        return Err(Diagnostic::new(
                            part.span,
                            "a DynArray pattern may contain at most one '..'",
                        ));
                    }
                    rest = true;
                    if let Some(name) = name {
                        if !copyable {
                            return Err(Diagnostic::new(
                                part.span,
                                "a borrowed DynArray pattern cannot bind '..name' over owning, linear, or view elements: a '&[T]' view of them has no checked operations; use '..' and bind the elements you need",
                            ));
                        }
                        rest_binding = Some(bind(
                            self,
                            name,
                            view,
                            part,
                            bindings,
                            &mut exclusive_slots,
                        )?);
                    }
                    continue;
                }
                ast::PatternKind::Wildcard => Pattern::Any,
                ast::PatternKind::Name(path)
                    if path.len() == 1 && !self.is_constructor_pattern(part) =>
                {
                    Pattern::Bind(bind(
                        self,
                        &path[0],
                        reference,
                        part,
                        bindings,
                        &mut exclusive_slots,
                    )?)
                }
                _ if copyable => self.pattern(part, element, bindings)?,
                _ => {
                    return Err(Diagnostic::new(
                        part.span,
                        "a borrowed DynArray pattern over owning, linear, or view elements supports only element names (bound as '&T'), '_', and '..'",
                    ));
                }
            };
            if rest {
                suffix.push(checked);
            } else {
                prefix.push(checked);
            }
        }
        if prefix.len() + suffix.len() > capacity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "DynArray pattern has {} element(s) but the capacity is {capacity}",
                    prefix.len() + suffix.len()
                ),
            ));
        }
        // One split group per exclusive binding; see `Pattern::DynArray`.
        let exclusive = exclusive.then(|| {
            let base = self.next_split;
            self.next_split += prefix
                .iter()
                .chain(&suffix)
                .filter(|pattern| matches!(pattern, Pattern::Bind(_)))
                .count()
                + usize::from(rest_binding.is_some());
            base
        });
        Ok(Pattern::DynArray {
            element,
            capacity,
            prefix,
            suffix,
            rest,
            rest_binding,
            borrowed: true,
            exclusive,
        })
    }
    /// `let v = &a[..]` over a runtime-length array `[T; n <= C]` records
    /// `Slice.len(v) == n`, so `Slice.at(v, i, _)` can be proved from facts
    /// about `n`.
    fn define_view_length(&mut self, slot: usize, value: &Expr) {
        let ExprKind::Slice {
            base,
            start: None,
            end: None,
            text: false,
            ..
        } = &value.kind
        else {
            return;
        };
        let owner = match base.ty {
            Type::Ref(pointer) | Type::RefMut(pointer) => self.types.pointees[pointer],
            ty => ty,
        };
        let Some(binder) = owner
            .layout()
            .and_then(|id| self.types.enums[id].runtime_length)
        else {
            return;
        };
        let Ok(length) = self.runtime_length_term(binder, value.span) else {
            return;
        };
        let view =
            crate::facts::Linear::variable(crate::facts::Term::Len(slot, self.facts.version(slot)));
        let mut facts = Vec::new();
        crate::facts::compare(view, &Kind::EqEq, length, &mut facts);
        self.facts.add(facts);
    }
    /// `a[i]` on a runtime-length array `[T; n <= C]` (a local or a shared
    /// reference to one). When the facts prove `0 <= i && i < n` the read is
    /// proof-based and needs no `panic` effect; otherwise it is a checked read.
    /// Both lower to the checked `DynArray` read, whose bound check cannot
    /// fire on the proved path.
    fn runtime_array_index(
        &mut self,
        base: &Expr,
        index: &ast::Expr,
        span: Span,
    ) -> Result<Option<Expr>> {
        let array_ty = match base.ty {
            Type::Ref(pointer) | Type::RefMut(pointer) => self.types.pointees[pointer],
            ty => ty,
        };
        let Some(binder) = array_ty
            .layout()
            .and_then(|id| self.types.enums[id].runtime_length)
        else {
            return Ok(None);
        };
        let (element, _) = self.types.enums[array_ty.layout().unwrap()]
            .dynamic_array
            .expect("runtime arrays use the DynArray layout");
        let array = match (&base.kind, base.ty) {
            (ExprKind::Peek(slot), Type::Ref(_)) => Expr {
                kind: ExprKind::Local(*slot),
                ty: base.ty,
                span: base.span,
                resource: None,
            },
            // An exclusive reference is read without being moved: the read
            // reborrows it as shared for this one element copy.
            (ExprKind::Peek(slot), Type::RefMut(pointer)) => Expr {
                kind: ExprKind::Peek(*slot),
                ty: Type::Ref(pointer),
                span: base.span,
                resource: None,
            },
            (ExprKind::Peek(slot), ty) if ty == array_ty => Expr {
                kind: ExprKind::Borrow(*slot),
                ty: Type::Ref(self.types.pointer(array_ty)),
                span: base.span,
                resource: None,
            },
            _ => {
                return Err(Diagnostic::new(
                    base.span,
                    "index a runtime-length array through a local binding or a reference parameter; bind the array to a local first",
                ));
            }
        };
        if self.owned_type(element) || self.linear_type(element) || element.is_view() {
            return Err(Diagnostic::new(
                span,
                "indexing a runtime-length array copies the element, but it owns resources, is linear, or is a view",
            ));
        }
        let index = self.expr_expected(index, Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        let length = self.runtime_length_term(binder, span).ok();
        let proved = match (self.facts.linear(&index), length) {
            (Some(position), Some(length)) => self.try_prove(
                vec![
                    (
                        crate::facts::Linear::constant(0),
                        Kind::Le,
                        position.clone(),
                    ),
                    (position, Kind::Lt, length),
                ],
                "0 <= index && index < n",
                span,
            ),
            _ => false,
        };
        if !proved {
            self.require(PANIC, span)?;
        }
        let ty = if index.ty == Type::Never {
            Type::Never
        } else {
            element
        };
        Ok(Some(Expr {
            kind: ExprKind::Call(
                Target::DynArray(DynArrayOp::Get, element),
                vec![array, index],
            ),
            ty,
            span,
            resource: None,
        }))
    }
    /// `DynArray.push`/`pop` change the runtime length, which a runtime-length
    /// array's type fixes to its binder.
    fn reject_length_change(&self, ty: Type, name: &str, span: Span) -> Result<()> {
        let Some(binder) = ty
            .layout()
            .and_then(|id| self.types.enums[id].runtime_length)
        else {
            return Ok(());
        };
        Err(Diagnostic::new(
            span,
            format!(
                "{name} would change the length of a [T; {} <= C], which always equals '{}'; use a DynArray<T, C> for a growable length",
                self.resolution.bindings[binder].name, self.resolution.bindings[binder].name
            ),
        ))
    }
    /// A lambda is called indirectly, so its signature cannot carry a
    /// runtime-length binder the call would have to substitute.
    fn reject_lambda_runtime_length(&self, ty: Type, span: Span) -> Result<()> {
        if crate::runtime_types::runtime_length_binders(self.types, ty).is_empty() {
            return Ok(());
        }
        Err(Diagnostic::new(
            span,
            "fn/once fn types and lambdas cannot mention a runtime-length array [T; n <= C]; call a named function instead",
        ))
    }
    /// The solver term for the current value of a runtime-length binder.
    fn runtime_length_term(&self, binder: BindingId, span: Span) -> Result<crate::facts::Linear> {
        let slot = self.runtime_length_slot(binder, span)?;
        Ok(crate::facts::Linear::variable(crate::facts::Term::Var(
            slot,
            self.facts.version(slot),
        )))
    }
    /// Try to prove `l op r` for every atom from the facts in scope without
    /// reporting a failure. Proved goals record checked certificates.
    /// Prove a checked `Bool` proposition (linear comparisons with `&&`,
    /// `||` and `!`) from the facts here, recording its certificate.
    fn prove_condition(&mut self, condition: &Expr, what: &str) -> Result<()> {
        let Some(goal) = self.facts.formula_exact(condition, true) else {
            return Err(Diagnostic::new(
                condition.span,
                format!("{what} must be linear comparisons of integers joined by &&, || and !"),
            ));
        };
        match self.facts.certify(&goal, condition.span, what) {
            Some(certificates) => {
                self.functions.certificates.extend(certificates);
                Ok(())
            }
            None => Err(Diagnostic::new(
                condition.span,
                format!("cannot prove {what} from what is known here"),
            )),
        }
    }
    /// PROOF-FUZZ: remember a run-time check the prover left in place.
    fn record_obligation(&mut self, kind: ObligationKind, span: Span, goal: String) {
        self.record_check(kind, span, goal, false);
    }
    /// PROOF-FUZZ: remember a check, discharged (`proved`) or left in place.
    fn record_check(&mut self, kind: ObligationKind, span: Span, goal: String, proved: bool) {
        let function = self.functions.checking;
        let function_name = self.functions.signatures[function].name.clone();
        let table = if proved {
            &mut self.functions.discharged
        } else {
            &mut self.functions.obligations
        };
        table
            .entry((function, span.start, span.end, kind))
            .or_insert(Obligation {
                kind,
                span,
                function,
                function_name,
                goal,
            });
    }
    fn record_bounds(&mut self, container: Container, length: Option<i64>, span: Span) {
        let goal = match length {
            Some(length) => format!("0 <= index && index < {length}"),
            None => "0 <= index && index < len".to_owned(),
        };
        let kind = ObligationKind::Bounds {
            container,
            refined_length: length,
        };
        self.record_obligation(kind, span, goal);
    }
    fn try_prove(
        &mut self,
        atoms: Vec<(crate::facts::Linear, Kind, crate::facts::Linear)>,
        text: &str,
        span: Span,
    ) -> bool {
        let mut goals = Vec::new();
        let mut wanted = 0;
        for (left, op, right) in atoms {
            wanted += if op == Kind::EqEq { 2 } else { 1 };
            crate::facts::compare(left, &op, right, &mut goals);
        }
        // An overflowing translation drops a goal; never treat that as proved.
        if goals.len() != wanted {
            return false;
        }
        let Some(certificates) = self.facts.certify(&vec![goals], span, text) else {
            return false;
        };
        self.functions.certificates.extend(certificates);
        true
    }
    /// The caller binding for each callee `i64` parameter that sizes a
    /// runtime-length array in the callee's signature. The actual must name an
    /// immutable `i64` binding in scope.
    fn call_runtime_lengths(
        &self,
        f: &ast::Function,
        skip: usize,
        arguments: &[ast::Expr],
    ) -> Result<BTreeMap<BindingId, BindingId>> {
        fn collect(resolution: &Resolution, ty: &ast::Type, out: &mut BTreeSet<BindingId>) {
            match &ty.kind {
                ast::TypeKind::Array(element, length) => {
                    if let Some((binder, _)) = runtime_length_parts(length)
                        && let Ok(id) = runtime_length_binder(resolution, binder)
                    {
                        out.insert(id);
                    }
                    collect(resolution, element, out);
                }
                ast::TypeKind::Borrow { inner, .. }
                | ast::TypeKind::Graded { inner, .. }
                | ast::TypeKind::Slice(inner) => collect(resolution, inner, out),
                ast::TypeKind::Named { arguments, .. } => {
                    for argument in arguments {
                        collect(resolution, argument, out);
                    }
                }
                ast::TypeKind::Tuple(items) => {
                    for item in items {
                        collect(resolution, item, out);
                    }
                }
                ast::TypeKind::Structural { fields, .. } => {
                    for field in fields {
                        collect(resolution, &field.ty, out);
                    }
                }
                ast::TypeKind::Binary { left, right, .. } => {
                    collect(resolution, left, out);
                    collect(resolution, right, out);
                }
                _ => {}
            }
        }
        let parameters = &f.parameters[skip.min(f.parameters.len())..];
        let mut binders = BTreeSet::new();
        for parameter in parameters.iter().filter(|parameter| !parameter.erased) {
            collect(self.resolution, &parameter.ty, &mut binders);
        }
        collect(self.resolution, &f.result, &mut binders);
        let mut map = BTreeMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let Some(binder) = self.resolution.binder(parameter.span) else {
                continue;
            };
            if !binders.contains(&binder) {
                continue;
            }
            let error = || {
                Diagnostic::new(
                    argument.span,
                    format!(
                        "'{}' sizes a runtime-length array in the signature of '{}'; pass the name of an immutable i64 local",
                        parameter.name, f.name
                    ),
                )
            };
            let ast::ExprKind::Name(_) = &argument.kind else {
                return Err(error());
            };
            let actual = self.resolution.reference(argument.span).ok_or_else(error)?;
            self.runtime_length_slot(actual, argument.span)?;
            map.insert(binder, actual);
        }
        Ok(map)
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
                let mut offset = c.types.enums[layout].tag_words();
                for (index, field_ty) in variant.fields.iter().enumerate() {
                    let sub = fields.iter().find(|(n, _)| *n == variant.names[index]);
                    if let Some((name, p)) = sub {
                        c.check_layout_field_visible(layout, name, p.span)?;
                    }
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
                    tag: 0, tagged: c.types.enums[layout].tag_words() != 0, niche: c.types.enums[layout].niche(),
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
                let mut offset = c.types.enums[index].tag_words();
                let mut checked = Vec::new();
                for (field, ty) in fields.iter().zip(variant.fields) {
                    checked.push((offset, c.pattern(field, ty, bindings)?));
                    offset += c.types.width(ty);
                }
                return Ok(Pattern::Variant {
                    tag,
                    tagged: c.types.enums[index].tag_words() != 0,
                    niche: c.types.enums[index].niche(),
                    fields: checked,
                });
            }
            if let ast::PatternKind::Slice(parts) = &pattern.kind
                && let Type::Ref(pointer) | Type::RefMut(pointer) = ty
                && let Some((element, capacity)) = c.types.pointees[pointer]
                    .layout()
                    .and_then(|id| c.types.enums[id].dynamic_array)
            {
                let exclusive = matches!(ty, Type::RefMut(_));
                return c.borrowed_dyn_pattern(
                    parts,
                    element,
                    capacity,
                    exclusive,
                    pattern.span,
                    bindings,
                );
            }
            if let ast::PatternKind::Slice(parts) = &pattern.kind {
                if let Some((element, capacity)) = ty
                    .layout()
                    .and_then(|id| c.types.enums[id].dynamic_array)
                {
                    if c.owned_type(element) || c.linear_type(element) || element.is_view() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            "DynArray patterns copy element bindings; owning, linear, and view elements cannot be matched by value",
                        ));
                    }
                    let mut prefix = Vec::new();
                    let mut suffix = Vec::new();
                    let mut rest = false;
                    let mut rest_binding = None;
                    // A runtime-length array's tail has a different length, so
                    // `..rest` is a plain DynArray with the same capacity.
                    let rest_ty = if ty
                        .layout()
                        .is_some_and(|id| c.types.enums[id].runtime_length.is_some())
                    {
                        c.types.dynamic_array(element, capacity, pattern.span)?
                    } else {
                        ty
                    };
                    for part in parts {
                        if let ast::PatternKind::Rest(name) = &part.kind {
                            if rest {
                                return Err(Diagnostic::new(
                                    part.span,
                                    "a DynArray pattern may contain at most one '..'",
                                ));
                            }
                            rest = true;
                            rest_binding = match name {
                                Some(name) => {
                                    if let Some((slot, previous)) = bindings.get(name) {
                                        c.expect(rest_ty, *previous, part.span)?;
                                        Some(*slot)
                                    } else {
                                        let slot = c.bind(part.span, rest_ty, false)?;
                                        bindings.insert(name.clone(), (slot, rest_ty));
                                        Some(slot)
                                    }
                                }
                                None => None,
                            };
                            continue;
                        }
                        // Elements after the rest match the trailing slots,
                        // counted back from the runtime length.
                        if rest {
                            suffix.push(c.pattern(part, element, bindings)?);
                        } else {
                            prefix.push(c.pattern(part, element, bindings)?);
                        }
                    }
                    if prefix.len() + suffix.len() > capacity {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "DynArray pattern has {} element(s) but the capacity is {capacity}",
                                prefix.len() + suffix.len()
                            ),
                        ));
                    }
                    return Ok(Pattern::DynArray {
                        element,
                        capacity,
                        prefix,
                        suffix,
                        rest,
                        rest_binding,
                        borrowed: false,
                        exclusive: None,
                    });
                }
                let Some((element, length)) = ty.layout().and_then(|id| c.types.enums[id].array)
                else {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "array pattern requires an inline array",
                    ));
                };
                if parts
                    .iter()
                    .any(|part| matches!(part.kind, ast::PatternKind::Rest(_)))
                {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "inline array patterns require an exact element count; use a DynArray for a '..' rest pattern",
                    ));
                }
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
                return Ok(Pattern::Variant { tag: 0, tagged: true, niche: None, fields });
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
                    Ok(Pattern::Variant { tag: 0, tagged: true, niche: None, fields })
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
    /// `(proved, checked)`: element accesses proved in bounds, compiled as
    /// plain loads and stores, and those that keep a run-time check.
    pub fn bounds_report(&self) -> (usize, usize) {
        (self.bounds_proved, self.bounds_checked)
    }
    /// PROOF-FUZZ: every run-time check the prover could not discharge, in
    /// source order.
    pub fn obligations(&self) -> &[Obligation] {
        &self.obligations
    }
    /// PROOF-FUZZ: checks the prover discharged (bounds and overflow), one
    /// per function instance, in source order.
    pub fn discharged(&self) -> &[Obligation] {
        &self.discharged
    }
    /// PROOF-FUZZ: obligation sites, one per source location and kind (the
    /// instances of a generic function share a site), in source order. A
    /// site's position in this list is its id in fuzz builds.
    pub fn obligation_sites(&self) -> Vec<&Obligation> {
        let mut seen = BTreeSet::new();
        self.obligations
            .iter()
            .filter(|o| seen.insert((o.span.start, o.span.end, o.kind.label())))
            .collect()
    }
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
    /// The source spelling of a checked type.
    pub(crate) fn type_name(&self, ty: Type) -> String {
        crate::runtime_types::type_name_in(
            ty,
            &self.pointees,
            &self.enums,
            &self.unions,
            &self.function_types,
        )
    }
    /// `export "symbol" fn` declarations (KUSH-RUST-EXPORT).
    pub fn exports(&self) -> Vec<ExportInfo> {
        let name = |ty: Type| {
            crate::runtime_types::type_name_in(
                ty,
                &self.pointees,
                &self.enums,
                &self.unions,
                &self.function_types,
            )
        };
        self.exports
            .iter()
            .map(|export| ExportInfo {
                symbol: export.symbol.clone(),
                name: self.functions[export.index].name.clone(),
                parameters: export
                    .parameters
                    .iter()
                    .map(|(n, ty)| (n.clone(), name(*ty)))
                    .collect(),
                result: name(export.result),
            })
            .collect()
    }
    /// Checked foreign declarations in instance order. This reports the
    /// Kush-side contract only; the foreign library remains trusted code that
    /// Kush cannot verify for memory safety.
    pub fn foreign_functions(&self) -> Vec<ForeignFunctionInfo> {
        self.foreign_functions
            .iter()
            .enumerate()
            .filter_map(|(index, foreign)| {
                foreign.as_ref().map(|foreign| ForeignFunctionInfo {
                    name: self.functions[index].name.clone(),
                    symbol: foreign.symbol.clone(),
                    parameters: foreign
                        .parameters
                        .iter()
                        .map(|ty| {
                            crate::runtime_types::type_name_in(
                                *ty,
                                &self.pointees,
                                &self.enums,
                                &self.unions,
                                &self.function_types,
                            )
                        })
                        .collect(),
                    result: crate::runtime_types::type_name_in(
                        foreign.result,
                        &self.pointees,
                        &self.enums,
                        &self.unions,
                        &self.function_types,
                    ),
                    fallible: foreign.fallible.is_some(),
                })
            })
            .collect()
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
        crate::runtime_types::width(
            &self.pointees,
            &self.enums,
            &self.unions,
            &self.function_types,
            ty,
        )
    }
    pub(crate) fn owns(&self, ty: Type) -> bool {
        match ty {
            Type::Box(_)
            | Type::Arena
            | Type::ArenaBox(_)
            | Type::AllocatorContext
            | Type::AllocBox(_)
            | Type::AllocVec(_)
            | Type::Bytes
            | Type::String
            | Type::Vec(_)
            | Type::Once(_)
            | Type::Task(_)
            | Type::Thread(_)
            | Type::Channel(_)
            | Type::GpuBuf(_)
            | Type::DynObj(_) => true,
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
        K::Dyn(bounds) => K::Dyn(
            bounds
                .iter()
                .map(|bound| ast::DynBound {
                    trait_ref: substitute_alias_type(resolution, &bound.trait_ref, map),
                    bindings: bound
                        .bindings
                        .iter()
                        .map(|(name, value)| {
                            (name.clone(), substitute_alias_type(resolution, value, map))
                        })
                        .collect(),
                })
                .collect(),
        ),
        K::Integer(value) => K::Integer(value.clone()),
        K::Bool(value) => K::Bool(*value),
        K::Lifetime(name) => K::Lifetime(name.clone()),
        K::Tuple(items) => K::Tuple(
            items
                .iter()
                .map(|item| substitute_alias_type(resolution, item, map))
                .collect(),
        ),
        K::Structural { fields, open, row } => K::Structural {
            fields: fields
                .iter()
                .map(|field| ast::Field {
                    name: field.name.clone(),
                    source: field.source.clone(),
                    ty: substitute_alias_type(resolution, &field.ty, map),
                    span: field.span,
                    public: field.public,
                    min_length: None,
                })
                .collect(),
            open: *open,
            row: row
                .as_ref()
                .map(|row| Box::new(substitute_alias_type(resolution, row, map))),
        },
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
            call_multi,
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
            call_multi: *call_multi,
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
        K::Infer => K::Infer,
        K::Capability {
            operation,
            effects,
            multi,
        } => K::Capability {
            operation: operation.clone(),
            effects: effects.clone(),
            multi: *multi,
        },
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
            | ExprKind::AllocBoxRead(value)
            | ExprKind::AllocBoxTake(value)
            | ExprKind::Drop(value)
            | ExprKind::Project(value, _)
            | ExprKind::InitOwner { value, .. }
            | ExprKind::BorrowInit { value, .. }
            | ExprKind::Coerce { value, .. }
            | ExprKind::Break(Some(value), _)
            | ExprKind::Assign(_, value) => expr(value),
            ExprKind::BoxWrite(reference, value) => expr(reference) || expr(value),
            ExprKind::BoxReuseGrow { owner, payload }
            | ExprKind::BoxTryReuse { owner, payload, .. }
            | ExprKind::ArenaAlloc {
                arena: owner,
                value: payload,
            }
            | ExprKind::AllocBoxNew {
                allocator: owner,
                value: payload,
            }
            | ExprKind::AllocBoxTryNew {
                allocator: owner,
                value: payload,
                ..
            } => expr(owner) || expr(payload),
            ExprKind::ArenaNew
            | ExprKind::ArenaNewWith { .. }
            | ExprKind::ArenaTryAlloc { .. }
            | ExprKind::BoxTryNew { .. }
            | ExprKind::BytesTryWithCapacity { .. } => true,
            ExprKind::Loop(block) => block_allocates(block),
            ExprKind::While(condition, block) => expr(condition) || block_allocates(block),
            ExprKind::BytesAt(a, b)
            | ExprKind::Binary(_, a, b)
            | ExprKind::StructEq {
                left: a, right: b, ..
            }
            | ExprKind::DynArrayEqual {
                left: a, right: b, ..
            } => expr(a) || expr(b),
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
        Statement::Declare(_) => false,
    }) || block.tail.as_deref().is_some_and(expr)
}

/// Whether an expression contains a direct `perform operation` that targets
/// the currently enclosing lexical handler. Nested handles for the same
/// operation shadow the outer one, and lambdas are separate callables that do
/// not inherit a lexical handler. Used only to classify the handled body before
/// choosing the tail-resumptive or continuation lowering.
/// Whether a handler is a lambda whose resumption token is used only as
/// `resume(e)` in tail position, with `e` and every statement independent of
/// the token. Such a handler computes `h(p, k) = k(e)`, so resuming with the
/// identity token and continuing in place is the same computation.
fn tail_resumptive_handler(resolution: &Resolution, handler: &ast::Expr) -> bool {
    let ast::ExprKind::Lambda(lambda) = &handler.kind else {
        return false;
    };
    let Some(token) = lambda
        .parameters
        .get(1)
        .and_then(|parameter| resolution.binder(parameter.span))
    else {
        return false;
    };
    // An early `return` or `?` in the handler would skip the resumption,
    // which the identity token cannot express; count it as a mention.
    let mentions = |expr: &ast::Expr| {
        let mut refs = BTreeSet::new();
        collect_expr_refs(resolution, expr, &mut refs);
        refs.contains(&token) || exits_early(expr)
    };
    fn statement_value(statement: &ast::Statement) -> &ast::Expr {
        match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => value,
        }
    }
    fn tail(
        resolution: &Resolution,
        token: BindingId,
        mentions: &dyn Fn(&ast::Expr) -> bool,
        expr: &ast::Expr,
    ) -> bool {
        match &expr.kind {
            ast::ExprKind::Call { callee, arguments } => {
                resolution.reference(callee.span) == Some(token)
                    && matches!(callee.kind, ast::ExprKind::Name(_))
                    && arguments.len() == 1
                    && !mentions(&arguments[0])
            }
            ast::ExprKind::Block(block) => block_tail(resolution, token, mentions, block),
            ast::ExprKind::If {
                condition,
                then,
                otherwise,
            } => {
                !mentions(condition)
                    && block_tail(resolution, token, mentions, then)
                    && otherwise
                        .as_deref()
                        .is_some_and(|otherwise| tail(resolution, token, mentions, otherwise))
            }
            ast::ExprKind::Match { value, arms } => {
                !mentions(value)
                    && arms.iter().all(|arm| {
                        arm.guard.as_ref().is_none_or(|guard| !mentions(guard))
                            && tail(resolution, token, mentions, &arm.body)
                    })
            }
            ast::ExprKind::Return(Some(value)) => tail(resolution, token, mentions, value),
            _ => false,
        }
    }
    fn block_tail(
        resolution: &Resolution,
        token: BindingId,
        mentions: &dyn Fn(&ast::Expr) -> bool,
        block: &ast::Block,
    ) -> bool {
        block
            .statements
            .iter()
            .all(|statement| !mentions(statement_value(statement)))
            && block
                .tail
                .as_deref()
                .is_some_and(|value| tail(resolution, token, mentions, value))
    }
    block_tail(resolution, token, &mentions, &lambda.body)
}
/// Visit the direct child expressions of an AST expression; blocks are
/// expanded into their statement values and tail. Lambda bodies are
/// children too; callers that must not enter them check for lambdas first.
/// Whether a call in `block` passes the binding by name as an argument
/// (CAP-CAPTURING-LEXICAL: a capability given to a callee).
fn block_passes_binding(resolution: &Resolution, block: &ast::Block, id: BindingId) -> bool {
    fn expr(resolution: &Resolution, e: &ast::Expr, id: BindingId) -> bool {
        if let ast::ExprKind::Call { arguments, .. } = &e.kind
            && arguments.iter().any(|argument| {
                matches!(argument.kind, ast::ExprKind::Name(_))
                    && resolution.reference(argument.span) == Some(id)
            })
        {
            return true;
        }
        let mut found = false;
        ast_children(e, &mut |child| found = found || expr(resolution, child, id));
        found
    }
    block.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
            expr(resolution, value, id)
        }
    }) || block
        .tail
        .as_deref()
        .is_some_and(|tail| expr(resolution, tail, id))
}

fn block_contains_quote(block: &ast::Block) -> bool {
    fn contains_quote(expr: &ast::Expr) -> bool {
        if matches!(expr.staging(), Some((ast::StagingForm::Quote, _))) {
            return true;
        }
        let mut found = false;
        ast_children(expr, &mut |child| found |= contains_quote(child));
        found
    }
    block.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => contains_quote(value),
    }) || block.tail.as_deref().is_some_and(contains_quote)
}

pub(crate) fn ast_children<'a>(expr: &'a ast::Expr, f: &mut dyn FnMut(&'a ast::Expr)) {
    fn block<'a>(block: &'a ast::Block, f: &mut dyn FnMut(&'a ast::Expr)) {
        for statement in &block.statements {
            match statement {
                ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => f(value),
            }
        }
        if let Some(tail) = &block.tail {
            f(tail);
        }
    }
    use ast::ExprKind as E;
    match &expr.kind {
        E::Name(_)
        | E::Integer(_)
        | E::Float(_)
        | E::String(_)
        | E::Char(_)
        | E::Bool(_)
        | E::Continue
        | E::Return(None)
        | E::Break(None) => {}
        E::Tuple(values) | E::Array(values) => values.iter().for_each(f),
        E::StructuralLiteral(fields) => fields.iter().for_each(|(_, value)| f(value)),
        E::Record { ty, fields, base } => {
            f(ty);
            fields.iter().for_each(|(_, value)| f(value));
            if let Some(base) = base {
                f(base);
            }
        }
        E::Block(inner) | E::Loop(inner) => block(inner, f),
        E::Unary { operand, .. }
        | E::Cast { value: operand, .. }
        | E::Is { value: operand, .. }
        | E::Try(operand) => f(operand),
        E::Return(Some(value)) | E::Break(Some(value)) => f(value),
        E::Binary { left, right, .. } => {
            f(left);
            f(right);
        }
        E::Call { callee, arguments } => {
            f(callee);
            arguments.iter().for_each(f);
        }
        E::Handle { handler, body, .. } => {
            f(handler);
            block(body, f);
        }
        E::Perform { value, .. } => f(value),
        E::Lambda(lambda) => block(&lambda.body, f),
        E::Specialize { callee, .. } => f(callee),
        E::Field { value, .. } => f(value),
        E::Index { value, index } => {
            f(value);
            f(index);
        }
        E::Slice { value, start, end } => {
            f(value);
            if let Some(start) = start {
                f(start);
            }
            if let Some(end) = end {
                f(end);
            }
        }
        E::If {
            condition,
            then,
            otherwise,
        } => {
            f(condition);
            block(then, f);
            if let Some(otherwise) = otherwise {
                f(otherwise);
            }
        }
        E::Match { value, arms } => {
            f(value);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    f(guard);
                }
                f(&arm.body);
            }
        }
        E::While {
            condition, body, ..
        } => {
            f(condition);
            block(body, f);
        }
    }
}
/// Whether a block contains (outside lambdas) a `handle` for a declared
/// operation whose effect bit is in `effects`.
fn body_handles_any(body: &ast::Block, effects: u16, resolution: &Resolution) -> bool {
    fn handles(expr: &ast::Expr, effects: u16, resolution: &Resolution) -> bool {
        match &expr.kind {
            ast::ExprKind::Handle {
                operation, body, ..
            } => {
                resolution
                    .effect_bits
                    .get(operation)
                    .is_some_and(|bit| effects & bit != 0)
                    || block(body, effects, resolution)
            }
            ast::ExprKind::Lambda(_) => false,
            _ => {
                let mut found = false;
                ast_children(expr, &mut |child| {
                    found |= handles(child, effects, resolution)
                });
                found
            }
        }
    }
    fn block(body: &ast::Block, effects: u16, resolution: &Resolution) -> bool {
        body.statements.iter().any(|statement| match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                handles(value, effects, resolution)
            }
        }) || body
            .tail
            .as_deref()
            .is_some_and(|tail| handles(tail, effects, resolution))
    }
    effects & !(IO | ALLOC | PANIC | SUSPEND) != 0 && block(body, effects, resolution)
}
/// Whether an expression contains `return` or `?` outside nested lambdas.
fn exits_early(expr: &ast::Expr) -> bool {
    fn block(block: &ast::Block) -> bool {
        block.statements.iter().any(|statement| match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => exits_early(value),
        }) || block.tail.as_deref().is_some_and(exits_early)
    }
    use ast::ExprKind as E;
    match &expr.kind {
        E::Return(_) | E::Try(_) => true,
        E::Lambda(_) => false,
        E::Name(_)
        | E::Integer(_)
        | E::Float(_)
        | E::String(_)
        | E::Char(_)
        | E::Bool(_)
        | E::Continue => false,
        E::Tuple(values) | E::Array(values) => values.iter().any(exits_early),
        E::StructuralLiteral(fields) | E::Record { fields, .. } => {
            fields.iter().any(|(_, value)| exits_early(value))
                || matches!(&expr.kind, E::Record { ty, base, .. }
                    if exits_early(ty) || base.as_deref().is_some_and(exits_early))
        }
        E::Block(inner) | E::Loop(inner) => block(inner),
        E::Unary { operand, .. }
        | E::Cast { value: operand, .. }
        | E::Is { value: operand, .. } => exits_early(operand),
        E::Binary { left, right, .. } => exits_early(left) || exits_early(right),
        E::Call { callee, arguments } => exits_early(callee) || arguments.iter().any(exits_early),
        E::Handle { handler, body, .. } => exits_early(handler) || block(body),
        E::Perform { value, .. } => exits_early(value),
        E::Specialize { callee, .. } => exits_early(callee),
        E::Field { value, .. } => exits_early(value),
        E::Index { value, index } => exits_early(value) || exits_early(index),
        E::Slice { value, start, end } => {
            exits_early(value)
                || start.as_deref().is_some_and(exits_early)
                || end.as_deref().is_some_and(exits_early)
        }
        E::If {
            condition,
            then,
            otherwise,
        } => exits_early(condition) || block(then) || otherwise.as_deref().is_some_and(exits_early),
        E::Match { value, arms } => {
            exits_early(value)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(exits_early) || exits_early(&arm.body)
                })
        }
        E::While {
            condition, body, ..
        } => exits_early(condition) || block(body),
        E::Break(value) => value.as_deref().is_some_and(exits_early),
    }
}
/// Whether a handled body performs `operation` lexically anywhere other than
/// as the body's whole tail expression (which keeps the identity token).
fn body_has_non_tail_perform(body: &ast::Block, operation: &str) -> bool {
    body.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
            contains_lexical_perform(value, operation)
        }
    }) || body.tail.as_deref().is_some_and(|tail| match &tail.kind {
        ast::ExprKind::Perform {
            operation: name,
            value,
        } if name == operation => contains_lexical_perform(value, operation),
        _ => contains_lexical_perform(tail, operation),
    })
}
fn contains_lexical_perform(expr: &ast::Expr, operation: &str) -> bool {
    match &expr.kind {
        ast::ExprKind::Perform {
            operation: name, ..
        } => name == operation,
        ast::ExprKind::Handle {
            operation: inner,
            handler,
            body,
            ..
        } => {
            contains_lexical_perform(handler, operation)
                || (inner != operation && block_contains_lexical_perform(body, operation))
        }
        ast::ExprKind::Lambda(_) => false,
        ast::ExprKind::Name(_)
        | ast::ExprKind::Integer(_)
        | ast::ExprKind::Float(_)
        | ast::ExprKind::String(_)
        | ast::ExprKind::Char(_)
        | ast::ExprKind::Bool(_)
        | ast::ExprKind::Continue => false,
        ast::ExprKind::Tuple(values) | ast::ExprKind::Array(values) => values
            .iter()
            .any(|value| contains_lexical_perform(value, operation)),
        ast::ExprKind::StructuralLiteral(fields) => fields
            .iter()
            .any(|(_, value)| contains_lexical_perform(value, operation)),
        ast::ExprKind::Block(block) => block_contains_lexical_perform(block, operation),
        ast::ExprKind::Unary { operand, .. }
        | ast::ExprKind::Try(operand)
        | ast::ExprKind::Cast { value: operand, .. }
        | ast::ExprKind::Is { value: operand, .. } => contains_lexical_perform(operand, operation),
        ast::ExprKind::Binary { left, right, .. } => {
            contains_lexical_perform(left, operation) || contains_lexical_perform(right, operation)
        }
        ast::ExprKind::Call { callee, arguments } => {
            contains_lexical_perform(callee, operation)
                || arguments
                    .iter()
                    .any(|argument| contains_lexical_perform(argument, operation))
        }
        ast::ExprKind::Specialize { callee, .. } | ast::ExprKind::Field { value: callee, .. } => {
            contains_lexical_perform(callee, operation)
        }
        ast::ExprKind::Index { value, index } => {
            contains_lexical_perform(value, operation) || contains_lexical_perform(index, operation)
        }
        ast::ExprKind::Slice { value, start, end } => {
            contains_lexical_perform(value, operation)
                || start
                    .as_deref()
                    .is_some_and(|start| contains_lexical_perform(start, operation))
                || end
                    .as_deref()
                    .is_some_and(|end| contains_lexical_perform(end, operation))
        }
        ast::ExprKind::Return(value) | ast::ExprKind::Break(value) => value
            .as_deref()
            .is_some_and(|value| contains_lexical_perform(value, operation)),
        ast::ExprKind::If {
            condition,
            then,
            otherwise,
        } => {
            contains_lexical_perform(condition, operation)
                || block_contains_lexical_perform(then, operation)
                || otherwise
                    .as_deref()
                    .is_some_and(|otherwise| contains_lexical_perform(otherwise, operation))
        }
        ast::ExprKind::Match { value, arms } => {
            contains_lexical_perform(value, operation)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| contains_lexical_perform(guard, operation))
                        || contains_lexical_perform(&arm.body, operation)
                })
        }
        ast::ExprKind::Record { fields, base, .. } => {
            fields
                .iter()
                .any(|(_, value)| contains_lexical_perform(value, operation))
                || base
                    .as_deref()
                    .is_some_and(|base| contains_lexical_perform(base, operation))
        }
        ast::ExprKind::While {
            condition, body, ..
        } => {
            contains_lexical_perform(condition, operation)
                || block_contains_lexical_perform(body, operation)
        }
        ast::ExprKind::Loop(body) => block_contains_lexical_perform(body, operation),
    }
}

fn block_contains_lexical_perform(block: &ast::Block, operation: &str) -> bool {
    block.statements.iter().any(|statement| match statement {
        ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
            contains_lexical_perform(value, operation)
        }
    }) || block
        .tail
        .as_deref()
        .is_some_and(|tail| contains_lexical_perform(tail, operation))
}

/// A one-word scalar value that can be captured by reference without owning
/// or borrowing storage. Mutable bindings of these types become live views.
pub(crate) fn is_live_scalar(ty: Type) -> bool {
    matches!(
        ty,
        Type::I64 | Type::Int(_) | Type::Float(_) | Type::Char | Type::Bool | Type::Unit
    )
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
        ast::ExprKind::Unary { operand, .. }
        | ast::ExprKind::Try(operand)
        | ast::ExprKind::Cast { value: operand, .. }
        | ast::ExprKind::Is { value: operand, .. } => collect_expr_refs(resolution, operand, out),
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
        ast::ExprKind::Record { ty, fields, base } => {
            collect_expr_refs(resolution, ty, out);
            for (_, value) in fields {
                collect_expr_refs(resolution, value, out);
            }
            if let Some(base) = base {
                collect_expr_refs(resolution, base, out);
            }
        }
        ast::ExprKind::While {
            condition, body, ..
        } => {
            collect_expr_refs(resolution, condition, out);
            collect_lambda_refs(resolution, body, out);
        }
        ast::ExprKind::Loop(body) => collect_lambda_refs(resolution, body, out),
    }
}

/// Two branch arms that produce the same borrowed record type must agree on
/// every invariant lifetime binder. For covariant or contravariant binders a
/// different label composes by polarity; for an invariant one the labels are
/// identity, and joining both would let one arm's provenance be laundered into
/// the other's by the label-erased normalization of the joined value.
fn check_branch_record_labels(
    types: &crate::runtime_types::Types<'_>,
    left: Type,
    right: Type,
    span: Span,
) -> Result<()> {
    if branch_record_label_mismatch(types, left, right, 0, &mut BTreeSet::new()) {
        return Err(Diagnostic::new(
            span,
            format!(
                "lifetime mismatch: {} is not a lifetime-compatible {}",
                types.name(left),
                types.name(right)
            ),
        )
        .with_note(
            span,
            "one branch reinterprets the other's provenance over an invariant record lifetime",
        ));
    }
    Ok(())
}

fn branch_record_label_mismatch(
    types: &crate::runtime_types::Types<'_>,
    left: Type,
    right: Type,
    depth: usize,
    seen: &mut BTreeSet<(Type, Type)>,
) -> bool {
    if left == right {
        return false;
    }
    if depth >= 32 || !seen.insert((left, right)) {
        return false;
    }
    // A wrapper whose coercions do not reinterpret a record's provenance
    // label unwraps into the pointee comparison.
    let pointee = |types: &crate::runtime_types::Types<'_>, value: Type| -> Option<Type> {
        match value {
            Type::Box(index)
            | Type::Vec(index)
            | Type::ArenaBox(index)
            | Type::AllocBox(index)
            | Type::AllocVec(index)
            | Type::Slice(index)
            | Type::SliceMut(index)
            | Type::Ref(index)
            | Type::RefMut(index) => Some(types.pointees[index]),
            Type::Annotated(index, _) => Some(types.pointees[index]),
            _ => None,
        }
    };
    if let (Some(left_pointee), Some(right_pointee)) = (pointee(types, left), pointee(types, right))
    {
        return branch_record_label_mismatch(types, left_pointee, right_pointee, depth + 1, seen);
    }
    match (left, right) {
        (Type::Enum(a), Type::Enum(b)) if a != b => {
            let left_def = &types.enums[a];
            let right_def = &types.enums[b];
            // Any same-declaration instantiation — record or a non-record
            // enum carrying borrowed payloads — compares its erased labels:
            // the arms' provenance identities must agree, or the truncating
            // union merges one arm into the other.
            if !left_def.structural
                && !right_def.structural
                && left_def.definition == right_def.definition
            {
                // Compare slot by slot. Only a slot whose own label is
                // compiler-internal (`<...>`) is excused; one internal label
                // must not exempt every other invariant binder on the arms.
                if left_def.lifetimes.len() != right_def.lifetimes.len()
                    || left_def
                        .lifetimes
                        .iter()
                        .zip(right_def.lifetimes.iter())
                        .any(|(left_label, right_label)| {
                            left_label != right_label
                                && !left_label.starts_with('<')
                                && !right_label.starts_with('<')
                        })
                {
                    return true;
                }
                for (left_variant, right_variant) in
                    left_def.variants.iter().zip(right_def.variants.iter())
                {
                    for (left_field, right_field) in
                        left_variant.fields.iter().zip(right_variant.fields.iter())
                    {
                        if branch_record_label_mismatch(
                            types,
                            *left_field,
                            *right_field,
                            depth + 1,
                            seen,
                        ) {
                            return true;
                        }
                    }
                }
            }
            false
        }
        (Type::Union(a), Type::Union(b)) => {
            // Composing arms keep their consumed labels as a laundering
            // channel when any misaligned pair exists.
            types.unions[a].members.len() != types.unions[b].members.len()
                || types.unions[a]
                    .members
                    .iter()
                    .zip(types.unions[b].members.iter())
                    .any(|(left, right)| {
                        branch_record_label_mismatch(types, *left, *right, depth + 1, seen)
                    })
        }
        (Type::Union(a), other) | (other, Type::Union(a)) => {
            // A same-definition union member against a single arm's value:
            // every member must agree on the labels.
            types.unions[a].members.iter().any(|member| {
                let same_definition = match (member, &other) {
                    (Type::Enum(m), Type::Enum(o)) => {
                        !types.enums[*m].structural
                            && !types.enums[*o].structural
                            && types.enums[*m].definition == types.enums[*o].definition
                    }
                    _ => false,
                };
                same_definition
                    && branch_record_label_mismatch(types, *member, other, depth + 1, seen)
            })
        }
        _ => false,
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
        Pattern::Variant { tag, fields, .. } if fields.iter().all(|(_, p)| irrefutable(p)) => {
            1 << tag
        }
        Pattern::Type { tag, .. } => 1 << tag,
        Pattern::Or(ps) => ps.iter().map(covered_variants).fold(0, |a, b| a | b),
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// Redundant-drop lint
//
// Explicit `drop(x)` is optional for affine values: the checker emits cleanup
// at the end of the declaring block anyway. The lint reports the drops whose
// removal cannot be observed:
//
// * a copyable local has no storage to release, so `drop` of one is a no-op
//   wherever it appears;
// * an owning local is reported when nothing that could allocate, perform
//   I/O, or run user code executes between the drop and the cleanup point
//   (the end of its declaring block, a `return`, or the function end), and
//   the type contains no user release hook (`AllocBox`, `AllocVec`, allocator
//   contexts, closures, task handles, dynamic objects), whose destruction can
//   run user or generated code and whose ordering an explicit drop can choose.
//
// Code that runs after the declaring block is irrelevant: the value is freed
// either way before it. That makes `drop(x); return ..;` and a drop as the last
// statement of a function or match-tail arm redundant, while an early release
// followed by more work stays.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RedundantDropKind {
    /// A copyable local: dropping it releases nothing.
    Copyable,
    /// An affine owning local dropped at its cleanup point.
    AtCleanupPoint,
}

/// How the path after a position ends, for cleanup-point analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LintRest {
    /// Inert code up to the end of this block.
    Inert,
    /// A `return` with an inert value: every scope unwinds here.
    Return,
    /// Anything else can allocate, run user code, or observe the free time.
    Blocked,
}

#[derive(Default)]
struct LintScopes {
    /// One set per open block, outermost first.
    scopes: Vec<std::collections::BTreeSet<usize>>,
    /// Per open block: whether the work after it inside every enclosing block,
    /// up to any declaring block, is inert or ends in a return.
    readiness: Vec<bool>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RedundantDrop {
    /// Span of the `drop(...)` expression in the loaded program's source map.
    pub span: Span,
    pub kind: RedundantDropKind,
}

impl Executable {
    /// Every explicit `drop(x)` this pass can remove without changing what the
    /// program observes. See the section comment for the exact conditions.
    pub fn redundant_drops(&self) -> Vec<RedundantDrop> {
        let mut out = Vec::new();
        for (index, function) in self.functions.iter().enumerate() {
            if self
                .foreign_functions
                .get(index)
                .is_some_and(Option::is_some)
            {
                continue;
            }
            let mut state = LintScopes::default();
            state.scopes.push(std::collections::BTreeSet::new());
            state.readiness.push(true);
            // Parameters belong to the function body's scope.
            state.scopes[0].extend(0..function.parameters);
            for statement in &function.body.statements {
                if let Statement::Let(id, _) = statement {
                    state.scopes[0].insert(*id);
                }
            }
            self.walk_lint_block(function, &function.body, true, &mut state, &mut out);
        }
        out
    }

    /// `ready` is true when the work after this block inside every enclosing
    /// block, up to the declaring block of any owner, is inert (or ends in a
    /// return); it says nothing about the block's own contents.
    fn walk_lint_block(
        &self,
        function: &Function,
        block: &Block,
        ready: bool,
        state: &mut LintScopes,
        out: &mut Vec<RedundantDrop>,
    ) {
        let mut declared = std::collections::BTreeSet::new();
        for statement in &block.statements {
            if let Statement::Let(id, _) = statement {
                declared.insert(*id);
            }
        }
        state.scopes.push(declared);
        state.readiness.push(ready);
        let mut rest = match block.tail.as_deref() {
            None => LintRest::Inert,
            Some(tail) => match &tail.kind {
                ExprKind::Return(value) => {
                    if self.inert_lint_expr(function, value) {
                        LintRest::Return
                    } else {
                        LintRest::Blocked
                    }
                }
                _ => {
                    if self.inert_lint_expr(function, tail) {
                        LintRest::Inert
                    } else {
                        LintRest::Blocked
                    }
                }
            },
        };
        for statement in block.statements.iter().rev() {
            // Whatever follows this position inside the block must be inert to
            // hand the cleanup point to a nested construct.
            let position_ready = matches!(rest, LintRest::Inert | LintRest::Return);
            if let Statement::Expr(expr) = statement {
                if let ExprKind::Drop(inner) = &expr.kind
                    && let Some(kind) = self.lint_drop_kind(function, inner, rest, state)
                {
                    out.push(RedundantDrop {
                        span: expr.span,
                        kind,
                    });
                }
                self.walk_lint_statement_expr(function, expr, position_ready, state, out);
            } else if let Statement::Let(_, expr) = statement {
                self.walk_lint_statement_expr(function, expr, position_ready, state, out);
            }
            // This statement now precedes the rest.
            if rest != LintRest::Return {
                rest = match &statement {
                    Statement::Expr(expr) => match &expr.kind {
                        ExprKind::Return(value) => {
                            if self.inert_lint_expr(function, value) {
                                LintRest::Return
                            } else {
                                LintRest::Blocked
                            }
                        }
                        ExprKind::Break(..) | ExprKind::Continue(..) => LintRest::Blocked,
                        _ if self.inert_lint_statement_with_drop(function, statement) => rest,
                        _ => LintRest::Blocked,
                    },
                    _ if self.inert_lint_statement_with_drop(function, statement) => rest,
                    _ => LintRest::Blocked,
                };
            }
        }
        if let Some(tail) = &block.tail {
            // Nothing runs after the tail inside this block, so a nested
            // construct in it sits at the block's cleanup point.
            self.walk_lint_value_expr(function, tail, true, state, out);
        }
        state.scopes.pop();
        state.readiness.pop();
    }

    /// Descend into a statement expression. `ready` describes the position of
    /// any nested block within this block.
    fn walk_lint_statement_expr(
        &self,
        function: &Function,
        expr: &Expr,
        ready: bool,
        state: &mut LintScopes,
        out: &mut Vec<RedundantDrop>,
    ) {
        match &expr.kind {
            ExprKind::Block(block) => self.walk_lint_block(function, block, ready, state, out),
            ExprKind::Match(scrutinee, arms) => {
                self.walk_lint_value_expr(function, scrutinee, false, state, out);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.walk_lint_value_expr(function, guard, false, state, out);
                    }
                    self.walk_lint_value_expr(function, &arm.body, ready, state, out);
                }
            }
            ExprKind::If(condition, then, otherwise) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, then, ready, state, out);
                self.walk_lint_block(function, otherwise, ready, state, out);
            }
            // A loop body may run again; only a return inside it ends the
            // enclosing work.
            ExprKind::While(condition, body) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Loop(body) => {
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Return(value) => {
                let ready = self.inert_lint_expr(function, value);
                self.walk_lint_value_expr(function, value, ready, state, out);
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::AbortScope { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            _ => self.walk_lint_value_expr(function, expr, false, state, out),
        }
    }

    /// Descend into a value expression; a block that is not the whole value
    /// has other evaluation around it.
    fn walk_lint_value_expr(
        &self,
        function: &Function,
        expr: &Expr,
        ready: bool,
        state: &mut LintScopes,
        out: &mut Vec<RedundantDrop>,
    ) {
        match &expr.kind {
            ExprKind::Block(block) => self.walk_lint_block(function, block, ready, state, out),
            ExprKind::Match(scrutinee, arms) => {
                self.walk_lint_value_expr(function, scrutinee, false, state, out);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.walk_lint_value_expr(function, guard, false, state, out);
                    }
                    self.walk_lint_value_expr(function, &arm.body, ready, state, out);
                }
            }
            ExprKind::If(condition, then, otherwise) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, then, ready, state, out);
                self.walk_lint_block(function, otherwise, ready, state, out);
            }
            ExprKind::While(condition, body) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Loop(body) => {
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Return(value) => {
                let ready = self.inert_lint_expr(function, value);
                self.walk_lint_value_expr(function, value, ready, state, out);
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::AbortScope { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            _ => expr.for_each_child(&mut |child| {
                self.walk_lint_value_expr(function, child, false, state, out)
            }),
        }
    }

    fn lint_drop_kind(
        &self,
        function: &Function,
        inner: &Expr,
        rest: LintRest,
        state: &LintScopes,
    ) -> Option<RedundantDropKind> {
        let id = match &inner.kind {
            ExprKind::Local(id) | ExprKind::Move(id) => *id,
            // Dropping an arbitrary expression: its evaluation is an effect.
            _ => return None,
        };
        let local = function.locals.get(id)?;
        if local.linear || local.grade.is_some_and(|grade| !grade.is_zero()) {
            return None;
        }
        if self.drop_has_release_hook(local.ty) {
            return None;
        }
        if !self.lint_owned_type(local.ty) {
            return Some(RedundantDropKind::Copyable);
        }
        // The deepest block that declares this binding.
        let declaring = state.scopes.iter().rposition(|scope| scope.contains(&id))?;
        let current = state.scopes.len() - 1;
        let at_cleanup_point = match rest {
            // A return unwinds every scope, so nothing after it runs.
            LintRest::Return => true,
            // The rest of this block is inert. Then every position between
            // this block and its declaring block must also be at the end of
            // its own block's work; the declaring block's own continuation is
            // irrelevant because cleanup happens there.
            LintRest::Inert => state.readiness[declaring + 1..=current]
                .iter()
                .all(|ready| *ready),
            LintRest::Blocked => false,
        };
        at_cleanup_point.then_some(RedundantDropKind::AtCleanupPoint)
    }

    fn inert_lint_statement_with_drop(&self, function: &Function, statement: &Statement) -> bool {
        match statement {
            Statement::Let(_, expr) => self.inert_lint_expr(function, expr),
            Statement::Expr(expr) => {
                if let ExprKind::Drop(inner) = &expr.kind
                    && let ExprKind::Local(id) | ExprKind::Move(id) = &inner.kind
                    && let Some(local) = function.locals.get(*id)
                {
                    // Dropping a hook-free local only frees storage; nothing
                    // else observes it.
                    return !self.drop_has_release_hook(local.ty);
                }
                self.inert_lint_expr(function, expr)
            }
            Statement::Declare(_) => true,
        }
    }

    /// Whether evaluating this expression could allocate, run user code, or
    /// otherwise observe that an owner was freed earlier. Conservative by
    /// construction: only scalars, copies, moves, and pure value construction
    /// pass.
    fn inert_lint_expr(&self, function: &Function, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Constant(_) | ExprKind::Erased(_) | ExprKind::Move(_) => true,
            // `Local` reads a copyable value.
            ExprKind::Local(_) => self.lint_copyable_type(expr.ty),
            ExprKind::Construct { fields, .. } => fields
                .iter()
                .all(|field| self.inert_lint_expr(function, field)),
            ExprKind::Coerce { value, .. } => self.inert_lint_expr(function, value),
            ExprKind::Unary(_, value) => self.inert_lint_expr(function, value),
            ExprKind::Binary(_, left, right) => {
                self.inert_lint_expr(function, left) && self.inert_lint_expr(function, right)
            }
            // Overwriting a copyable local destroys nothing; an owning local
            // would run its old value's cleanup here.
            ExprKind::Assign(id, value) => {
                function.locals.get(*id).is_some_and(|local| {
                    !self.lint_owned_type(local.ty) && !self.drop_has_release_hook(local.ty)
                }) && self.inert_lint_expr(function, value)
            }
            _ => false,
        }
    }

    /// Types whose destruction can run user or generated code: an explicit
    /// drop can order those callbacks relative to other drops, so they are not
    /// reported as redundant.
    fn drop_has_release_hook(&self, ty: Type) -> bool {
        fn go(executable: &Executable, ty: Type, depth: usize, seen: &mut Vec<Type>) -> bool {
            if depth > 64 || seen.contains(&ty) {
                return false;
            }
            seen.push(ty);
            match ty {
                Type::AllocBox(_)
                | Type::AllocVec(_)
                | Type::AllocatorContext
                | Type::Arena
                | Type::Once(_)
                | Type::Task(_)
                | Type::Thread(_)
                | Type::DynObj(_) => true,
                Type::Box(pointee) | Type::Vec(pointee) => {
                    go(executable, executable.pointees[pointee], depth + 1, seen)
                }
                Type::Enum(id) | Type::Variants(id, _) => {
                    executable.enums[id].variants.iter().any(|variant| {
                        variant
                            .fields
                            .iter()
                            .any(|field| go(executable, *field, depth + 1, seen))
                    })
                }
                Type::Union(id) => executable.unions[id]
                    .members
                    .iter()
                    .any(|member| go(executable, *member, depth + 1, seen)),
                _ => false,
            }
        }
        go(self, ty, 0, &mut Vec::new())
    }

    /// Copyable means no owned storage anywhere, mirroring the ownership pass.
    fn lint_copyable_type(&self, ty: Type) -> bool {
        !self.lint_owned_type(ty)
    }

    fn lint_owned_type(&self, ty: Type) -> bool {
        fn go(executable: &Executable, ty: Type, depth: usize, seen: &mut Vec<Type>) -> bool {
            if depth > 64 || seen.contains(&ty) {
                return false;
            }
            seen.push(ty);
            match ty {
                Type::Box(_)
                | Type::Arena
                | Type::ArenaBox(_)
                | Type::AllocBox(_)
                | Type::AllocVec(_)
                | Type::AllocatorContext
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::Once(_)
                | Type::Task(_)
                | Type::Thread(_)
                | Type::DynObj(_) => true,
                Type::Enum(id) | Type::Variants(id, _) => {
                    executable.enums[id].linear
                        || executable.enums[id].variants.iter().any(|variant| {
                            variant
                                .fields
                                .iter()
                                .any(|field| go(executable, *field, depth + 1, seen))
                        })
                }
                Type::Union(id) => executable.unions[id]
                    .members
                    .iter()
                    .any(|member| go(executable, *member, depth + 1, seen)),
                _ => false,
            }
        }
        go(self, ty, 0, &mut Vec::new())
    }
}

/// PROOF-FUZZ: obligations in source order (then by function instance).
fn sorted_obligations(
    obligations: &BTreeMap<(usize, usize, usize, ObligationKind), Obligation>,
) -> Vec<Obligation> {
    let mut out: Vec<Obligation> = obligations.values().cloned().collect();
    out.sort_by_key(|o| (o.span.start, o.span.end, o.kind, o.function));
    out
}
fn op_text(op: &Kind) -> &'static str {
    match op {
        Kind::Plus => "+",
        Kind::Minus => "-",
        Kind::Star => "*",
        Kind::Slash => "/",
        Kind::Percent => "%",
        _ => "an operator",
    }
}
/// PROOF-FUZZ: one line per obligation, `file:line:column  kind  function:
/// goal`, in source order. A check in a generic function is listed once per
/// location, however many instances it has.
pub(crate) fn obligation_report<'o>(
    sources: &crate::program::SourceMap,
    obligations: impl Iterator<Item = &'o Obligation>,
) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut sorted: Vec<&Obligation> = obligations.collect();
    sorted.sort_by_key(|o| (o.span.start, o.span.end, o.kind));
    let mut lines = Vec::new();
    for obligation in sorted {
        if !seen.insert((obligation.span.start, obligation.span.end, obligation.kind)) {
            continue;
        }
        let Some(file) = sources.file(obligation.span) else {
            continue;
        };
        let offset = obligation.span.start - file.base;
        let before = &file.text[..offset.min(file.text.len())];
        let line = before.matches('\n').count() + 1;
        let column = before.len() - before.rfind('\n').map_or(0, |at| at + 1) + 1;
        let refined = match obligation.kind {
            ObligationKind::Bounds {
                refined_length: Some(_),
                ..
            } => " (length-refined field)",
            _ => "",
        };
        lines.push(format!(
            "not proved: {}:{line}:{column} {} in {}: {}{refined}",
            file.name,
            obligation.kind.label(),
            obligation.function_name,
            obligation.goal,
        ));
    }
    lines
}

#[cfg(test)]
mod recursive_summary_mapping_tests {
    use super::*;

    fn origin(parameter: usize, path: &[&str]) -> recursive_lifetimes::Origin {
        recursive_lifetimes::Origin {
            parameter,
            path: path.iter().map(|part| (*part).to_owned()).collect(),
        }
    }

    #[test]
    fn a_direct_parameter_origin_maps_even_when_a_field_path_is_present() {
        let lifetime = summary_origin_lifetime(
            &origin(0, &["view"]),
            &[Some("'a".to_owned())],
            &[],
            &BTreeMap::new(),
        )
        .unwrap();
        assert_eq!(lifetime, "'a");
    }

    #[test]
    fn a_missing_field_path_is_rejected_instead_of_dropped() {
        let error =
            summary_origin_lifetime(&origin(0, &["missing"]), &[None], &[], &BTreeMap::new())
                .unwrap_err();
        assert!(error.contains("no source binder"), "{error}");
    }

    #[test]
    fn an_unborrowed_empty_path_origin_is_rejected() {
        let error =
            summary_origin_lifetime(&origin(0, &[]), &[None], &[], &BTreeMap::new()).unwrap_err();
        assert!(error.contains("no inferred borrow lifetime"), "{error}");
    }
}
