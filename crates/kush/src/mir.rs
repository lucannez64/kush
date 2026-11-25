//! The control-flow-graph IR between checking and code generation
//! (docs/mir-design.md, plan node FND-MIR).
//!
//! A [`Body`] is built from one checked function by [`build`]. Its locals
//! keep the checked function's slot numbers, followed by temporaries; its
//! blocks end in explicit terminators. Native code generation lowers a body
//! instead of the tree when `KUSH_MIR=1` is set, and falls back to the tree
//! for any function [`build`] does not cover yet.
//!
//! [`text`] gives the stable text form printed by `kush mir FILE`; its
//! parser reads the same form back, and the tests check that the two agree.

mod build;
mod drop_flags;
mod text;
mod verify;

use crate::Span;
use crate::executable::{Executable, Type};
use crate::int::{ArithOp, IntKind, IntOp, Shift};
use crate::lexer::Kind;

pub(crate) use build::build;
pub(crate) use verify::verify;

pub(crate) type BlockId = usize;
pub(crate) type LocalId = usize;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Body {
    pub name: String,
    /// Number of leading locals that are parameters.
    pub parameters: usize,
    /// The checked function's locals, in slot order, then temporaries.
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BasicBlock>,
    pub result: Type,
    /// The builtin operations the body calls, by `Callee::Builtin` index.
    pub builtins: Builtins,
    /// The coercions the body applies, by `Rvalue::Coerce` index: the
    /// target type and the representation change.
    pub coercions: Coercions,
}

/// The coercions of a body, by index; the text form declares each one.
#[derive(Debug, Clone, Default)]
pub(crate) struct Coercions(pub Vec<(Type, crate::executable::Coercion)>);

impl PartialEq for Coercions {
    fn eq(&self, other: &Self) -> bool {
        format!("{self:?}") == format!("{other:?}")
    }
}

/// The builtin call targets of a body, by index. The text form declares
/// each one as `builtin N = "<json>";` and reads it back.
#[derive(Debug, Clone, Default)]
pub(crate) struct Builtins(pub Vec<crate::executable::Target>);

impl PartialEq for Builtins {
    fn eq(&self, other: &Self) -> bool {
        format!("{self:?}") == format!("{other:?}")
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct LocalDecl {
    pub ty: Type,
    pub mutable: bool,
    /// Introduced by the builder, not a source binding.
    pub temporary: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
    /// Where a panic raised by one of the statements unwinds to. `None`
    /// continues unwinding: nothing is live that needs cleanup.
    pub unwind: Option<BlockId>,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum StatementKind {
    Assign(Place, Rvalue),
}

/// A local, or a run of its words; or, with `deref`, a run of the words
/// the reference in the local points to. Records and enums are flat words,
/// so a nested field is one offset from the start. A deref place always
/// names its field.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Place {
    pub local: LocalId,
    pub deref: bool,
    pub field: Option<Field>,
}

/// The words `offset..offset + width(ty)` of a local.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Field {
    pub offset: usize,
    pub ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Operand {
    Copy(Place),
    Move(Place),
    Constant(i64, Type),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Rvalue {
    Use(Operand),
    /// Checked arithmetic: overflow, division by zero and out-of-range
    /// shifts panic, as in the tree.
    Unary(UnOp, Operand),
    Binary(BinOp, Operand, Operand),
    /// An integer builtin with a one-word result, from `source` to
    /// `target`: conversions, wrapping and saturating arithmetic, and
    /// arithmetic the checker proved in range (no run-time check).
    Int(IntOp, IntKind, IntKind, Vec<Operand>),
    /// The variant `tag` of a record or enum of type `ty`, from its fields.
    Aggregate(Type, usize, Vec<Operand>),
    /// Allocate a box and move the operand into it.
    BoxNew(Operand),
    /// Move the payload out of a box and free the allocation.
    BoxTake(Operand),
    /// A new `Bytes` holding a copy of a literal.
    Bytes(Vec<u8>),
    /// A task operation on its operands; it may suspend or run other tasks.
    Task(TaskOp, Vec<Operand>),
    /// The byte at an index of a `Bytes` handle, proved in bounds (no
    /// run-time check).
    ByteAt(Operand, Operand),
    /// The address of a place: a reference to it.
    Ref(Place),
    /// The address of an element after its bound check: of a slice view
    /// (the operand), or of the vector or inline array at a place.
    ElementAddress(ElementBase, Operand),
    /// Change the representation of a value: inject it into a union, box it
    /// as a `dyn` object, and so on (the body's coercion at this index).
    Coerce(Operand, usize),
    /// A function value: the code of `function`, with an environment
    /// holding `captures` when there are any.
    FnValue {
        function: usize,
        captures: Vec<Capture>,
    },
    /// A view of the elements `start..end` (default: all) of `source`, or
    /// with `text`, a text view of its bytes. `check` tests the range (and
    /// for text, that both ends are scalar boundaries) at run time.
    View {
        source: ViewSource,
        start: Option<Operand>,
        end: Option<Operand>,
        element: Type,
        check: bool,
        text: bool,
    },
}

/// A structured-concurrency operation (the tree path's task expressions).
#[derive(Debug, Clone, Copy, PartialEq, serde::Serialize, serde::Deserialize)]
pub(crate) enum TaskOp {
    /// Spawn a task or thread running the owned `once` body (operand 0).
    Spawn {
        result: Type,
        obligation: bool,
        parallel: bool,
    },
    /// Run the owned `once` body (operand 0) in a task or thread scope, or
    /// in a `Task.catch` (a scope that is also a catch boundary).
    Scope {
        failure: Option<crate::runtime_types::ResultShape>,
        catch: Option<crate::runtime_types::ResultShape>,
        parallel: bool,
    },
    Yield,
    CheckCancel,
    /// Cancel the task behind a reference (operand 0).
    Cancel,
    /// Join a task or thread handle (operand 0).
    Join {
        exit: crate::executable::TaskExitShape,
        parallel: bool,
    },
}

/// One captured value of a closure.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Capture {
    /// Moved or copied into the environment.
    Value(Operand),
    /// The environment holds the local's address (a call-scoped scalar
    /// capture the closure may read or write in place).
    Address(LocalId),
}

/// What an element address indexes into.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum ElementBase {
    Slice(Operand),
    /// A vector or inline array, by the place holding it.
    Stored(Place),
}

/// What a view looks into.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum ViewSource {
    /// An inline array local: the view aliases its storage when it has a
    /// stable address, and a copy of it otherwise (as on the tree path).
    Array(LocalId),
    /// A `&Bytes`, `&Vec`, `&String`, array value or another view.
    Value(Operand),
}

impl ViewSource {
    pub(crate) fn ty(self, body: &Body) -> Type {
        match self {
            ViewSource::Array(local) => body.locals[local].ty,
            ViewSource::Value(operand) => body.operand_ty(operand),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TerminatorKind {
    Goto(BlockId),
    /// Jump to the target whose value equals the operand, else `otherwise`.
    Switch {
        value: Operand,
        targets: Vec<(i64, BlockId)>,
        otherwise: BlockId,
    },
    Call {
        callee: Callee,
        args: Vec<Operand>,
        destination: LocalId,
        next: BlockId,
        /// `None` continues unwinding.
        unwind: Option<BlockId>,
    },
    Return(Operand),
    /// A `panic(..)`: unwinds to `unwind`, or continues unwinding.
    Panic {
        unwind: Option<BlockId>,
    },
    /// Run the drop glue of the value at `place`.
    Drop {
        place: Place,
        next: BlockId,
        unwind: Option<BlockId>,
    },
    /// End of a cleanup block: continue unwinding into the caller.
    Resume,
    Unreachable,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Callee {
    Function(usize),
    PrintInt(IntKind),
    /// A builtin operation, by its index in the body's [`Builtins`].
    Builtin(usize),
    /// A `fn` or `once fn` value.
    Indirect(Operand),
}

impl Body {
    pub(crate) fn operand_ty(&self, operand: Operand) -> Type {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place_ty(place),
            Operand::Constant(_, ty) => ty,
        }
    }
    pub(crate) fn place_ty(&self, place: Place) -> Type {
        place
            .field
            .map_or(self.locals[place.local].ty, |field| field.ty)
    }
}

impl Place {
    pub(crate) fn local(local: LocalId) -> Self {
        Place {
            local,
            deref: false,
            field: None,
        }
    }
    pub(crate) fn field(local: LocalId, offset: usize, ty: Type) -> Self {
        Place {
            local,
            deref: false,
            field: Some(Field { offset, ty }),
        }
    }
    /// The words of type `ty` at `offset` behind the reference in `local`.
    pub(crate) fn deref(local: LocalId, offset: usize, ty: Type) -> Self {
        Place {
            local,
            deref: true,
            field: Some(Field { offset, ty }),
        }
    }
}

impl Operand {
    pub(crate) fn place(self) -> Option<Place> {
        match self {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(..) => None,
        }
    }
}

impl UnOp {
    pub(crate) fn kind(self) -> Kind {
        match self {
            UnOp::Neg => Kind::Minus,
            UnOp::Not => Kind::Bang,
        }
    }
    fn from_kind(kind: &Kind) -> Option<Self> {
        Some(match kind {
            Kind::Minus => UnOp::Neg,
            Kind::Bang => UnOp::Not,
            _ => return None,
        })
    }
    const ALL: [UnOp; 2] = [UnOp::Neg, UnOp::Not];
    fn name(self) -> &'static str {
        match self {
            UnOp::Neg => "Neg",
            UnOp::Not => "Not",
        }
    }
}

impl BinOp {
    pub(crate) fn kind(self) -> Kind {
        match self {
            BinOp::Add => Kind::Plus,
            BinOp::Sub => Kind::Minus,
            BinOp::Mul => Kind::Star,
            BinOp::Div => Kind::Slash,
            BinOp::Rem => Kind::Percent,
            BinOp::BitAnd => Kind::Amp,
            BinOp::BitOr => Kind::Pipe,
            BinOp::BitXor => Kind::Caret,
            BinOp::Shl => Kind::Shl,
            BinOp::Shr => Kind::Shr,
            BinOp::Lt => Kind::Lt,
            BinOp::Le => Kind::Le,
            BinOp::Gt => Kind::Gt,
            BinOp::Ge => Kind::Ge,
            BinOp::Eq => Kind::EqEq,
            BinOp::Ne => Kind::Ne,
        }
    }
    fn from_kind(kind: &Kind) -> Option<Self> {
        BinOp::ALL.into_iter().find(|op| op.kind() == *kind)
    }
    const ALL: [BinOp; 16] = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::Div,
        BinOp::Rem,
        BinOp::BitAnd,
        BinOp::BitOr,
        BinOp::BitXor,
        BinOp::Shl,
        BinOp::Shr,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
        BinOp::Eq,
        BinOp::Ne,
    ];
    fn name(self) -> &'static str {
        match self {
            BinOp::Add => "Add",
            BinOp::Sub => "Sub",
            BinOp::Mul => "Mul",
            BinOp::Div => "Div",
            BinOp::Rem => "Rem",
            BinOp::BitAnd => "BitAnd",
            BinOp::BitOr => "BitOr",
            BinOp::BitXor => "BitXor",
            BinOp::Shl => "Shl",
            BinOp::Shr => "Shr",
            BinOp::Lt => "Lt",
            BinOp::Le => "Le",
            BinOp::Gt => "Gt",
            BinOp::Ge => "Ge",
            BinOp::Eq => "Eq",
            BinOp::Ne => "Ne",
        }
    }
}

/// The text name of an integer builtin the IR carries, or `None` for one it
/// does not (those produce an `Option`).
pub(crate) fn int_op_name(op: IntOp) -> Option<String> {
    let arith = |op: ArithOp| match op {
        ArithOp::Add => "add",
        ArithOp::Sub => "sub",
        ArithOp::Mul => "mul",
    };
    Some(match op {
        IntOp::Convert => "convert".into(),
        IntOp::Truncate => "truncate".into(),
        IntOp::Wrapping(op) => format!("wrapping_{}", arith(op)),
        IntOp::Saturating(op) => format!("saturating_{}", arith(op)),
        IntOp::Unchecked(op) => format!("unchecked_{}", arith(op)),
        IntOp::UncheckedShift(Shift::Left) => "unchecked_shl".into(),
        IntOp::UncheckedShift(Shift::Right) => "unchecked_shr".into(),
        IntOp::TryConvert { .. } | IntOp::Checked(..) | IntOp::CharFromCode { .. } => {
            return None;
        }
    })
}

/// The integer builtins the IR carries, for reading the text form.
pub(crate) fn int_op_named(name: &str) -> Option<IntOp> {
    let ariths = [ArithOp::Add, ArithOp::Sub, ArithOp::Mul];
    let mut all = vec![
        IntOp::Convert,
        IntOp::Truncate,
        IntOp::UncheckedShift(Shift::Left),
        IntOp::UncheckedShift(Shift::Right),
    ];
    for op in ariths {
        all.extend([
            IntOp::Wrapping(op),
            IntOp::Saturating(op),
            IntOp::Unchecked(op),
        ]);
    }
    all.into_iter()
        .find(|op| int_op_name(*op).is_some_and(|candidate| candidate == name))
}

/// Every function of the program, as built or with the reason it is not.
pub(crate) fn bodies(program: &Executable) -> Vec<Result<Body, String>> {
    (0..program.functions.len())
        .map(|index| build(program, index))
        .collect()
}

/// `kush mir FILE`: the text form of every body, and a comment naming the
/// first construct of each function the builder does not cover yet.
pub fn dump(program: &Executable) -> String {
    let mut out = String::new();
    for (index, body) in bodies(program).into_iter().enumerate() {
        if index > 0 {
            out.push('\n');
        }
        out.push_str(&format!("// function {index}\n"));
        match body {
            Ok(body) => out.push_str(&text::print(&body)),
            Err(reason) => {
                let name = &program.functions[index].name;
                out.push_str(&format!("// fn {name}: not lowered: {reason}\n"));
            }
        }
    }
    out
}

/// How many functions [`build`] covers, as `(built, total)`.
pub fn coverage(program: &Executable) -> (usize, usize) {
    let bodies = bodies(program);
    (
        bodies.iter().filter(|body| body.is_ok()).count(),
        bodies.len(),
    )
}

/// Build every covered body, check it, print it, parse the text back and
/// compare. Returns the number of bodies checked, or the first failure.
pub fn self_check(program: &Executable) -> Result<usize, String> {
    let mut checked = 0;
    for body in bodies(program).into_iter().flatten() {
        verify(program, &body).map_err(|e| format!("fn {}: {e}", body.name))?;
        let printed = text::print(&body);
        let parsed =
            text::parse(&printed).map_err(|e| format!("fn {}: {e}\n{printed}", body.name))?;
        if parsed != body {
            return Err(format!(
                "fn {}: the text form does not read back\n{printed}",
                body.name
            ));
        }
        checked += 1;
    }
    Ok(checked)
}
