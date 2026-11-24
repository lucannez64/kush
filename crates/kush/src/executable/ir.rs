//! The checked program: types, expressions, functions, obligations and
//! the operation enums the backends lower.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

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
pub(super) fn normalized_scalar(term: &Term) -> Option<Scalar> {
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
pub(super) struct DynMethodContract {
    pub(super) mode: ReceiverMode,
    pub(super) parameters: Vec<Type>,
    pub(super) parameter_grades: Vec<Option<Grade>>,
    pub(super) result: Type,
    pub(super) result_grade: Option<Grade>,
    pub(super) effects: u16,
    /// The expression type observed by the caller; a `@[0]` result is erased.
    pub(super) value_type: Type,
}
/// Concrete method type/grade/natural/effect arguments selected at one dynamic
/// call site. Vectors are in declaration order among parameters of each
/// category, exactly like a function instance key.
#[derive(Debug, Clone, Default)]
pub(super) struct MethodArguments {
    pub(super) types: Vec<Type>,
    pub(super) consts: Vec<usize>,
    pub(super) grades: Vec<Grade>,
    pub(super) effects: Vec<u16>,
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
    pub(super) fn named(name: &str) -> Option<Self> {
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
    pub(super) fn named(name: &str) -> Option<Self> {
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
pub(super) struct Signature {
    /// Call-only types scope declared labels before caller rows are expanded.
    pub(super) call_contract: Option<CallLifetimeContract>,
    pub(super) binding: BindingId,
    pub(super) name: String,
    /// Runtime parameter types, in order. Erased parameters are absent.
    pub(super) parameters: Vec<Type>,
    pub(super) result: Type,
    pub(super) effects: u16,
    pub(super) span: Span,
    /// Generic parameter binder -> concrete type, for specialized instances.
    pub(super) substitution: BTreeMap<BindingId, Type>,
    /// Const natural binder -> compile-time value, for specialized instances.
    pub(super) consts: BTreeMap<BindingId, usize>,
    /// Abstract grade binder -> concrete compile-time grade.
    pub(super) grades: BTreeMap<BindingId, Grade>,
    /// Effect row binder -> concrete effect bitset for this instance.
    pub(super) effect_arguments: BTreeMap<BindingId, u16>,
    /// Where a generic instance was first requested, for diagnostics.
    pub(super) origin: Option<(Span, String)>,
    /// Usage grade of each runtime parameter (`None` is unannotated).
    pub(super) parameter_grades: Vec<Option<Grade>>,
    /// Static result-transfer contract; `Some(Finite(1))` means the caller
    /// acquires a linear obligation for the returned owning value.
    pub(super) result_grade: Option<Grade>,
    pub(super) parameter_lifetimes: Vec<Option<String>>,
    pub(super) result_lifetime: Option<String>,
    pub(super) lifetime_bounds: BTreeSet<(String, String)>,
    /// Concrete `Self` target for an impl method instance.
    pub(super) self_type: Option<Type>,
    /// Trait specialization that this instance's default body belongs to.
    /// Unqualified method calls on `Self` inside the body prefer it.
    pub(super) default_trait: Option<(BindingId, TraitArguments)>,
    /// Associated constants of the owning impl, already evaluated for this
    /// instance's specialization. `Self::NAME` resolves here.
    pub(super) associated_consts: BTreeMap<String, ConstValue>,
}
#[derive(Clone)]
pub(super) struct CallLifetimeContract {
    pub(super) parameters: Vec<Type>,
    pub(super) result: Type,
    pub(super) binders: BTreeSet<String>,
    pub(super) names: BTreeMap<String, String>,
    pub(super) bounds: BTreeSet<(String, String)>,
}
impl Signature {
    pub(super) fn scope_call_lifetimes(&mut self) -> (BTreeSet<String>, BTreeMap<String, String>) {
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
    pub(super) fn parameter_erased(&self, index: usize) -> bool {
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
