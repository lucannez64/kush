//! Usage grades: natural multiplicities, unbounded usage, and exact-use checking.
//!
//! ## Algebra
//!
//! A grade is an element of the ordered semiring of natural usage bounds
//! extended with infinity:
//!
//! ```text
//! Grade = 0 | 1 | 2 | ... | many
//! 0 + g = g           g + many = many        (checked finite addition)
//! 0 * g = 0           n * many = many (n > 0) (checked finite multiplication)
//! 1 * g = g           many * many = many
//! ```
//!
//! `0 * many = 0` is the annihilation law: an expression whose result is used
//! zero times cannot duplicate anything, even when the enclosing operation
//! permits arbitrary duplication. Finite arithmetic is overflow-checked; a
//! grade annotation that overflows 64 bits is rejected rather than silently
//! becoming `many`.
//!
//! ## Surface forms
//!
//! * `T @[0]` — ghost/non-observable binding. The value must not be read,
//!   moved, borrowed, or passed at runtime. Owning/linear values are rejected:
//!   a grade must never silently discard storage.
//! * `T @[1]` — exactly one use. For owning/linear storage this remains the
//!   original linear obligation (the ownership pass also enforces it). For a
//!   copyable value the grade checker enforces exactly one observation.
//! * `T @[n]`, `n >= 2` — exactly `n` uses. Only copyable, non-linear values.
//! * `T @[many]` — unrestricted use. Only copyable, non-linear values.
//! * `T @[G]`, `T @[G + 1]`, `T @[G * 2]` — an abstract grade parameter,
//!   declared as `<G: Grade>`. Instances are created only by explicit
//!   compile-time specialization (`f::<..., 4>(...)`). No runtime grade value
//!   exists.
//!
//! Grade expressions support `+`, `*`, parentheses, natural literals, `many`,
//! and grade variables. They are evaluated entirely at compile time.
//!
//! ## Checking rules
//!
//! * Each use of a copyable binding contributes its surrounding duplication
//!   demand to the binding's use count. A call argument is evaluated under the
//!   callee parameter's demand: passing a variable to a `@[2]` parameter counts
//!   as two uses, to a `@[many]` parameter as unbounded use, and to a `@[0]`
//!   parameter as one evaluation (strict evaluation still reads the argument;
//!   the callee simply cannot observe the parameter).
//! * Consuming an owning/linear value (`Move`, `Box.take`, a move into a call)
//!   counts once regardless of demand. Owning/linear parameters cannot be
//!   graded above one, so a callee can only duplicate a *copyable result*, not
//!   the owner that produced it.
//! * Sequential uses add. Branches (`if`, `match`, short-circuit right
//!   operands) must produce the same count on every normally surviving path.
//! * A `return` and the error path of `?` check every in-scope exact grade
//!   before transferring control.
//! * Loop back-edges, `break`, and `continue` require outer exact-grade counts
//!   to be restored to their loop-entry values. A loop may therefore use and
//!   reassign a graded binding each iteration, but may not consume a fixed
//!   outer budget an unknown number of times. Locals bound inside the loop must
//!   satisfy their exact grade on every iteration.
//! * A match guard cannot observe a finite exact-grade binding: a guard is
//!   evaluated a path-dependent number of times. `@[many]` bindings remain
//!   usable in guards; owning borrows are not consumptions and stay legal.
//! * Assignment to a graded mutable binding requires the old value to have met
//!   its exact grade, then starts a new obligation for the replacement value.
//!
//! These rules are deliberately conservative at a few boundaries (notably
//! side-effecting blocks passed to a high-demand parameter, and loops). They
//! reject programs they cannot decide; they do not infer an exact grade from
//! runtime values.
use crate::{
    Diagnostic, Span, ast,
    executable::{
        Block, BytesOp, Executable, Expr, ExprKind, Function, Statement, Target, Type, VecOp,
    },
    resolve::{BindingId, Resolution},
};
use std::collections::BTreeMap;

type Result<T> = std::result::Result<T, Diagnostic>;

/// The usage semiring: finite natural bounds plus infinity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Grade {
    Finite(u64),
    Many,
}
impl Grade {
    pub(crate) const ZERO: Self = Self::Finite(0);
    pub(crate) const ONE: Self = Self::Finite(1);

    pub(crate) fn is_zero(self) -> bool {
        self == Self::ZERO
    }
    /// Addition with checked finite overflow. `None` means the mathematical
    /// finite result does not fit in `u64`; callers that are checking a source
    /// annotation report an error instead of approximating it.
    pub(crate) fn checked_add(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Many, _) | (_, Self::Many) => Some(Self::Many),
            (Self::Finite(a), Self::Finite(b)) => a.checked_add(b).map(Self::Finite),
        }
    }
    /// Multiplication with the extended-natural annihilation law
    /// `0 * many = 0`.
    pub(crate) fn checked_mul(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Finite(0), _) | (_, Self::Finite(0)) => Some(Self::ZERO),
            (Self::Many, Self::Many) => Some(Self::Many),
            (Self::Many, Self::Finite(_)) | (Self::Finite(_), Self::Many) => Some(Self::Many),
            (Self::Finite(a), Self::Finite(b)) => a.checked_mul(b).map(Self::Finite),
        }
    }
    /// Saturating addition for observed usage counts. A count that overflows
    /// becomes unbounded; a finite exact grade can then never match it.
    fn saturating_add(self, other: Self) -> Self {
        self.checked_add(other).unwrap_or(Self::Many)
    }
    fn saturating_mul(self, other: Self) -> Self {
        self.checked_mul(other).unwrap_or(Self::Many)
    }
}
impl std::fmt::Display for Grade {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Finite(0) => f.write_str("0"),
            Self::Finite(n) => write!(f, "{n}"),
            Self::Many => f.write_str("many"),
        }
    }
}

/// Split `T @[grade]` into the underlying type and the grade expression.
pub(crate) fn split(ty: &ast::Type) -> (&ast::Type, Option<&ast::Type>) {
    match &ty.kind {
        ast::TypeKind::Graded { inner, grade } => (inner, Some(grade)),
        _ => (ty, None),
    }
}

/// Evaluate a grade annotation at compile time. No runtime grade values exist.
pub(crate) fn evaluate(
    resolution: &Resolution,
    variables: &BTreeMap<BindingId, Grade>,
    expr: &ast::Type,
) -> Result<Grade> {
    fn go(
        resolution: &Resolution,
        variables: &BTreeMap<BindingId, Grade>,
        expr: &ast::Type,
        budget: &mut usize,
    ) -> Result<Grade> {
        if *budget == 0 {
            return Err(Diagnostic::new(
                expr.span,
                "usage grade expression exceeds the 128-node evaluation budget",
            ));
        }
        *budget -= 1;
        match &expr.kind {
            ast::TypeKind::Integer(text) => text.parse::<u64>().map(Grade::Finite).map_err(|_| {
                Diagnostic::new(
                    expr.span,
                    "usage grades are nonnegative naturals that fit in 64 bits",
                )
            }),
            ast::TypeKind::Named { path, arguments } if arguments.is_empty() && path.len() == 1 => {
                let id = resolution.reference(expr.span).ok_or_else(|| {
                    Diagnostic::new(expr.span, "internal error: unresolved grade name")
                })?;
                let binding = &resolution.bindings[id];
                if binding.kind == crate::resolve::BindingKind::Builtin && binding.name == "many" {
                    return Ok(Grade::Many);
                }
                variables.get(&id).copied().ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        format!(
                            "'{}' is not an abstract grade parameter in this specialization; declare it as <{}: Grade> or use 0, 1, many",
                            binding.name, binding.name
                        ),
                    )
                })
            }
            ast::TypeKind::Binary { op, left, right } => {
                use crate::lexer::Kind;
                let left = go(resolution, variables, left, budget)?;
                let right = go(resolution, variables, right, budget)?;
                let result = match op {
                    Kind::Plus => left.checked_add(right),
                    Kind::Star => left.checked_mul(right),
                    _ => None,
                };
                result.ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "usage grade arithmetic overflows the 64-bit finite bound (or uses an unsupported operator); use 'many' explicitly if an unbounded grade is intended",
                    )
                })
            }
            _ => Err(Diagnostic::new(
                expr.span,
                "usage grades are natural literals, 'many', grade variables, and '+'/'*' expressions",
            )),
        }
    }
    let mut budget = 128;
    go(resolution, variables, expr, &mut budget)
}

/// Check exact-use obligations for every function after ownership elaboration.
pub(crate) fn check(program: &Executable) -> Result<()> {
    for function in &program.functions {
        Checker::new(program, function).run()?;
    }
    Ok(())
}

#[derive(Clone)]
struct Frame {
    /// Counts at the loop head for every tracked outer binding.
    entry: BTreeMap<usize, Grade>,
    /// Number of active bindings at the loop head; later bindings are local
    /// to this loop body.
    active_start: usize,
    /// Counts observed at each `break`, for outer bindings. `while` must also
    /// join these with the zero-iteration head; `loop` continues with them.
    breaks: Option<BTreeMap<usize, Grade>>,
}

#[derive(Clone)]
struct Checker<'a> {
    program: &'a Executable,
    function: &'a Function,
    /// Bindings currently in scope, in declaration order.
    active: Vec<usize>,
    /// Use counts for finite exact grades. Unbounded/default bindings are not
    /// tracked because they have no exact obligation.
    counts: BTreeMap<usize, Grade>,
    loops: Vec<Frame>,
    /// A match guard is evaluated a path-dependent number of times.
    guard: bool,
    steps: usize,
}
/// A conservative per-function traversal budget. It bounds compiler work on
/// adversarial expression graphs; it is not a program-runtime budget.
const MAX_STEPS: usize = 1_000_000;

impl<'a> Checker<'a> {
    fn new(program: &'a Executable, function: &'a Function) -> Self {
        Self {
            program,
            function,
            active: Vec::new(),
            counts: BTreeMap::new(),
            loops: Vec::new(),
            guard: false,
            steps: 0,
        }
    }
    fn run(mut self) -> Result<()> {
        for slot in 0..self.function.parameters {
            self.activate(slot);
        }
        let function = self.function;
        let survives = self.block(&function.body, false, Grade::ONE)?;
        if survives {
            self.check_exact(&self.active.clone(), function.span, "the function returns")?;
        }
        Ok(())
    }
    fn tick(&mut self, span: Span) -> Result<()> {
        self.steps += 1;
        if self.steps > MAX_STEPS {
            return Err(Diagnostic::new(
                span,
                "usage-grade checking exceeds the per-function 1,000,000-step budget",
            ));
        }
        Ok(())
    }
    fn moves(&self, ty: Type) -> bool {
        match ty {
            Type::Box(_)
            | Type::Bytes
            | Type::String
            | Type::Vec(_)
            | Type::Once(_)
            | Type::Task(_) => true,
            Type::Enum(id) | Type::Variants(id, _) => {
                self.program.owned_enums.get(id).copied().unwrap_or(false)
                    || self.program.linear_enums.get(id).copied().unwrap_or(false)
            }
            Type::Union(id) => self.program.unions[id]
                .members
                .iter()
                .any(|member| self.moves(*member)),
            _ => false,
        }
    }
    /// A type-level `#[linear]` obligation (distinct from a `@[1]` binding grade).
    fn is_linear_type(&self, ty: Type) -> bool {
        match ty {
            Type::Box(pointee) | Type::Vec(pointee) => {
                self.is_linear_type(self.program.pointees[pointee])
            }
            Type::Enum(id) | Type::Variants(id, _) => {
                self.program.linear_enums.get(id).copied().unwrap_or(false)
            }
            Type::Union(id) => self.program.unions[id]
                .members
                .iter()
                .any(|member| self.is_linear_type(*member)),
            Type::Once(id) => self
                .program
                .function_types
                .get(id)
                .is_some_and(|signature| signature.linear),
            _ => false,
        }
    }
    /// Whether the value of `expr` is a move of a binding carrying a linear
    /// obligation, including through value-position blocks, `if`, `match`,
    /// constructors, and `Box.new`. A copyable `@[1]` result is a must-use
    /// obligation, not an owning move, so its result type must own storage.
    fn value_moves_linear(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => self.function.locals[*slot].linear,
            ExprKind::Call(Target::Function(index), _) => {
                self.program.functions.get(*index).is_some_and(|function| {
                    function.result_grade == Some(Grade::Finite(1)) && self.moves(function.result)
                })
            }
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) => {
                    self.program
                        .function_types
                        .get(id)
                        .is_some_and(|signature| {
                            signature.result_grade == Some(Grade::Finite(1))
                                && self.moves(signature.result)
                        })
                }
                _ => false,
            },
            ExprKind::Block(block) => self.block_value_moves_linear(block),
            ExprKind::If(_, yes, no) => {
                (yes.ty != Type::Never && self.block_value_moves_linear(yes))
                    || (no.ty != Type::Never && self.block_value_moves_linear(no))
            }
            ExprKind::Match(_, arms) => arms
                .iter()
                .any(|arm| arm.body.ty != Type::Never && self.value_moves_linear(&arm.body)),
            ExprKind::Construct { fields, .. } => {
                fields.iter().any(|field| self.value_moves_linear(field))
            }
            ExprKind::FnValue { captures, .. } => captures
                .iter()
                .any(|capture| self.value_moves_linear(capture)),
            ExprKind::Loop(body) => crate::ownership::loop_break_values(body)
                .into_iter()
                .any(|v| self.value_moves_linear(v)),
            ExprKind::Try { value, .. } => self.value_moves_linear(value),
            ExprKind::BoxTake(value) if self.program.owns(expr.ty) => {
                self.value_moves_linear(value)
            }
            ExprKind::BoxNew(value) => self.value_moves_linear(value),
            ExprKind::BoxReuse { owner, payload } => {
                self.value_moves_linear(owner) || self.value_moves_linear(payload)
            }
            ExprKind::VecMap { vector, .. } => self.value_moves_linear(vector),
            ExprKind::Coerce { value, .. } => self.value_moves_linear(value),
            _ => false,
        }
    }
    fn block_value_moves_linear(&self, block: &Block) -> bool {
        block
            .tail
            .as_ref()
            .is_some_and(|tail| self.value_moves_linear(tail))
    }
    /// Whether the value is bound by `@[1]` (or a propagated linear binding),
    /// used to preserve the original "linear values cannot be dropped" rule.
    fn value_has_grade_one(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Move(slot) => {
                self.function.locals[*slot].linear || self.grade(*slot) == Some(Grade::Finite(1))
            }
            ExprKind::Call(Target::Function(index), _) => self
                .program
                .functions
                .get(*index)
                .is_some_and(|function| function.result_grade == Some(Grade::Finite(1))),
            ExprKind::CallIndirect { callee, .. } => match callee.ty {
                Type::Fn(id) | Type::Once(id) => self
                    .program
                    .function_types
                    .get(id)
                    .is_some_and(|signature| signature.result_grade == Some(Grade::Finite(1))),
                _ => false,
            },
            ExprKind::Block(block) => self.block_value_has_grade_one(block),
            ExprKind::If(_, yes, no) => {
                (yes.ty != Type::Never && self.block_value_has_grade_one(yes))
                    || (no.ty != Type::Never && self.block_value_has_grade_one(no))
            }
            ExprKind::Match(_, arms) => arms
                .iter()
                .any(|arm| arm.body.ty != Type::Never && self.value_has_grade_one(&arm.body)),
            ExprKind::Loop(body) => crate::ownership::loop_break_values(body)
                .into_iter()
                .any(|v| self.value_has_grade_one(v)),
            ExprKind::Try { value, .. } => self.value_has_grade_one(value),
            ExprKind::BoxReuse { owner, payload } => {
                self.value_has_grade_one(owner) || self.value_has_grade_one(payload)
            }
            ExprKind::VecMap { vector, .. } => self.value_has_grade_one(vector),
            ExprKind::Coerce { value, .. } => self.value_has_grade_one(value),
            // A constructor or Box.new consumes its inputs and produces a new
            // value; dropping that new value is a separate affine action.
            _ => false,
        }
    }
    fn block_value_has_grade_one(&self, block: &Block) -> bool {
        block
            .tail
            .as_ref()
            .is_some_and(|tail| self.value_has_grade_one(tail))
    }
    /// A linear value may only be handed to a parameter that will consume it
    /// (an explicit `@[1]` parameter or a `#[linear]` type), or to a terminal
    /// builtin such as `Box.take`. Value-carrying builtins are rejected because
    /// their ungraded result could be dropped.
    fn check_linear_parameter(
        &self,
        grade: Option<Grade>,
        ty: Option<Type>,
        span: Span,
    ) -> Result<()> {
        if matches!(grade, Some(Grade::Finite(1))) || ty.is_some_and(|ty| self.is_linear_type(ty)) {
            return Ok(());
        }
        Err(Diagnostic::new(
            span,
            "a value with a linear @[1] obligation is passed to an ungraded parameter that may drop it; mark the parameter @[1] or consume the value at the call site",
        ))
    }
    fn check_linear_argument(&self, target: Target, index: usize, span: Span) -> Result<()> {
        match target {
            Target::String(
                crate::executable::StringOp::IntoBytes
                | crate::executable::StringOp::FromUtf8 { .. },
            ) => Err(Diagnostic::new(
                span,
                "this string conversion would return a linear @[1] owner through an ungraded result; consume it through an explicitly graded parameter instead",
            )),
            Target::Function(function) => {
                let Some(function) = self.program.functions.get(function) else {
                    return Ok(());
                };
                self.check_linear_parameter(
                    function.parameter_grades.get(index).copied().flatten(),
                    function.locals.get(index).map(|local| local.ty),
                    span,
                )
            }
            Target::Vec(VecOp::Push | VecOp::Set, _) => Err(Diagnostic::new(
                span,
                "this vector operation would store a linear @[1] value in an ungraded vector that could be dropped; consume it first",
            )),
            Target::Bytes(BytesOp::Push | BytesOp::PushReserved | BytesOp::Clear) => {
                Err(Diagnostic::new(
                    span,
                    "this byte-buffer operation would store or return a linear @[1] value in an ungraded buffer; consume it first",
                ))
            }
            _ => Ok(()),
        }
    }
    fn grade(&self, slot: usize) -> Option<Grade> {
        self.function.locals[slot].grade
    }
    fn is_tracked(&self, slot: usize) -> bool {
        matches!(self.grade(slot), Some(Grade::Finite(_)))
    }
    fn activate(&mut self, slot: usize) {
        self.active.push(slot);
        if self.is_tracked(slot) {
            self.counts.insert(slot, Grade::ZERO);
        }
    }
    fn deactivate(&mut self, slot: usize) {
        if let Some(index) = self.active.iter().position(|s| *s == slot) {
            self.active.remove(index);
        }
        self.counts.remove(&slot);
    }
    /// Record `amount` uses of `slot`. `amount` is already the full multiplicity
    /// for this occurrence. Consuming uses pass `Grade::ONE`.
    fn record(&mut self, slot: usize, amount: Grade, span: Span) -> Result<()> {
        if amount.is_zero() || !self.is_tracked(slot) {
            return Ok(());
        }
        if self.guard {
            return Err(self.grade_error(
                slot,
                span,
                "cannot be observed in a match guard",
                "a guard may be evaluated a path-dependent number of times, so exact usage cannot be established",
            ));
        }
        let current = self.counts.get(&slot).copied().unwrap_or(Grade::ZERO);
        self.counts.insert(slot, current.saturating_add(amount));
        Ok(())
    }
    fn grade_error(&self, slot: usize, span: Span, action: &str, detail: &str) -> Diagnostic {
        let grade = self.grade(slot).unwrap_or(Grade::ZERO);
        Diagnostic::new(
            span,
            format!("a value graded @[{grade}] {action}; {detail}"),
        )
        .with_note(
            self.function.locals[slot].span,
            format!("value graded @[{grade}] bound here"),
        )
    }
    fn check_exact(&self, slots: &[usize], span: Span, reason: &str) -> Result<()> {
        for slot in slots {
            let Some(Grade::Finite(wanted)) = self.grade(*slot) else {
                continue;
            };
            let seen = self.counts.get(slot).copied().unwrap_or(Grade::ZERO);
            if seen != Grade::Finite(wanted) {
                let seen = seen.to_string();
                let detail = if wanted == 0 {
                    format!(
                        "the value is used {seen} time(s) on this path; grade @[0] forbids runtime observation"
                    )
                } else {
                    format!(
                        "the value is used {seen} time(s) on this path; the annotation requires exactly {wanted}"
                    )
                };
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is not used consistently before {reason}"),
                    &detail,
                ));
            }
        }
        Ok(())
    }
    /// A back-edge or `continue`: the next iteration starts from the loop head.
    /// Outer exact grades must be restored; loop-local bindings must finish
    /// their per-iteration obligation.
    fn check_iteration(&self, span: Span, what: &str) -> Result<()> {
        let Some(frame) = self.loops.last() else {
            return Ok(());
        };
        for (slot, entry) in &frame.entry {
            let seen = self.counts.get(slot).copied().unwrap_or(Grade::ZERO);
            if seen != *entry {
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is used an unknown number of times by the loop before {what}"),
                    "the loop may run zero, one, or many iterations; use @[many], use the value outside the loop, or reassign it to restore the loop-head use count on every path",
                ));
            }
        }
        self.check_loop_locals(span, what)
    }
    /// Bindings declared inside the loop body must satisfy their exact grade on
    /// every exit path, including `break` and `continue`.
    fn check_loop_locals(&self, span: Span, what: &str) -> Result<()> {
        let Some(frame) = self.loops.last() else {
            return Ok(());
        };
        for slot in &self.active[frame.active_start..] {
            self.check_exact(
                &[*slot],
                span,
                &format!("the end of this loop iteration ({what})"),
            )?;
        }
        Ok(())
    }
    /// Record the outer counts of a `break`. Different break paths must agree.
    fn note_break(&mut self, span: Span) -> Result<()> {
        let Some(frame) = self.loops.last() else {
            return Ok(());
        };
        let slots: Vec<usize> = frame.entry.keys().copied().collect();
        let current: BTreeMap<usize, Grade> = slots
            .iter()
            .map(|slot| (*slot, self.counts.get(slot).copied().unwrap_or(Grade::ZERO)))
            .collect();
        let frame = self.loops.last_mut().unwrap();
        let mut mismatch = None;
        match &mut frame.breaks {
            Some(previous) => {
                for (slot, count) in current {
                    if previous.get(&slot).copied().unwrap_or(Grade::ZERO) != count {
                        mismatch = Some(slot);
                        break;
                    }
                }
            }
            None => frame.breaks = Some(current),
        }
        if let Some(slot) = mismatch {
            let grade = self.grade(slot).unwrap_or(Grade::ZERO);
            return Err(self.grade_error(
                slot,
                span,
                "is used a different number of times on different break paths",
                &format!("exact grade @[{grade}] must match on every path that leaves the loop"),
            ));
        }
        Ok(())
    }
    /// Merge break records from a branch clone. Break paths diverge, but their
    /// counts still determine the surrounding loop's post-state.
    fn merge_breaks(&mut self, other: &Self, span: Span) -> Result<()> {
        let depth = self.loops.len().min(other.loops.len());
        let mut mismatch = None;
        for index in 0..depth {
            let Some(other_breaks) = other.loops[index].breaks.as_ref() else {
                continue;
            };
            let frame = &mut self.loops[index];
            match &mut frame.breaks {
                Some(previous) => {
                    for (slot, count) in other_breaks {
                        if previous.get(slot).copied().unwrap_or(Grade::ZERO) != *count {
                            mismatch = Some(*slot);
                            break;
                        }
                    }
                }
                None => frame.breaks = Some(other_breaks.clone()),
            }
            if mismatch.is_some() {
                break;
            }
        }
        if let Some(slot) = mismatch {
            let grade = self.grade(slot).unwrap_or(Grade::ZERO);
            return Err(self.grade_error(
                slot,
                span,
                "is used a different number of times on different break paths",
                &format!("exact grade @[{grade}] must match on every path that leaves the loop"),
            ));
        }
        Ok(())
    }
    fn join(&mut self, other: &Self, span: Span, what: &str) -> Result<()> {
        for (slot, left) in &self.counts {
            let right = other.counts.get(slot).copied().unwrap_or(Grade::ZERO);
            if *left != right {
                let grade = self.grade(*slot).unwrap_or(Grade::ZERO);
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is used a different number of times on different paths in {what}"),
                    &format!(
                        "one path uses it {} time(s) and the other {} time(s); exact grade @[{grade}] must match on every normally surviving path",
                        left, right
                    ),
                ));
            }
        }
        for slot in other.counts.keys() {
            if !self.counts.contains_key(slot) {
                let grade = self.grade(*slot).unwrap_or(Grade::ZERO);
                return Err(self.grade_error(
                    *slot,
                    span,
                    &format!("is used on only one path in {what}"),
                    &format!(
                        "exact grade @[{grade}] must be satisfied on every normally surviving path"
                    ),
                ));
            }
        }
        Ok(())
    }
    fn block(&mut self, block: &Block, loop_body: bool, multiplier: Grade) -> Result<bool> {
        self.tick(block_span(block))?;
        let active_start = self.active.len();
        let mut survives = true;
        for statement in &block.statements {
            match statement {
                Statement::Let(slot, value) => {
                    survives = self.expr(value, multiplier)?;
                    if !survives {
                        break;
                    }
                    self.activate(*slot);
                }
                Statement::Expr(expr) => {
                    survives = self.expr(expr, multiplier)?;
                    if !survives {
                        break;
                    }
                }
            }
        }
        if survives && let Some(tail) = &block.tail {
            survives = self.expr(tail, multiplier)?;
        }
        if survives && loop_body {
            self.check_iteration(block_span(block), "the loop falls through")?;
        }
        let bound = self.active[active_start..].to_vec();
        if survives {
            self.check_exact(&bound, block_span(block), "the end of its lexical scope")?;
        }
        for slot in bound {
            self.deactivate(slot);
        }
        Ok(survives)
    }
    fn expr(&mut self, expr: &Expr, multiplier: Grade) -> Result<bool> {
        self.tick(expr.span)?;
        match &expr.kind {
            ExprKind::Constant(_) | ExprKind::BytesLiteral(_) => {}
            ExprKind::Local(slot) => {
                let amount = if self.moves(self.function.locals[*slot].ty) {
                    Grade::ONE
                } else {
                    multiplier
                };
                self.record(*slot, amount, expr.span)?;
            }
            ExprKind::Move(slot) => self.record(*slot, Grade::ONE, expr.span)?,
            ExprKind::Peek(slot) | ExprKind::Borrow(slot) => {
                let amount = if self.moves(self.function.locals[*slot].ty) {
                    Grade::ZERO
                } else {
                    multiplier
                };
                self.record(*slot, amount, expr.span)?;
            }
            ExprKind::Block(block) => {
                return self.block(block, false, multiplier);
            }
            ExprKind::Project(base, _)
            | ExprKind::Unary(_, base)
            | ExprKind::BoxRead(base)
            | ExprKind::Coerce { value: base, .. } => {
                if !self.expr(base, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::BoxNew(base) | ExprKind::BoxTake(base) => {
                // The argument is consumed/evaluated once; duplicating the
                // resulting copyable value does not duplicate the consumption.
                if !self.expr(base, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::BoxReuse { owner, payload } => {
                // Both arguments are evaluated exactly once. The returned
                // owner inherits any binding-based obligation from either.
                if !self.expr(owner, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(payload, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                // The vector owner is consumed once and the copyable callable
                // values are observed once. The number of element calls is not
                // a usage count of the callback binding.
                if !self.expr(vector, Grade::ONE)? {
                    return Ok(false);
                }
                for callback in callbacks {
                    if !self.expr(callback, Grade::ONE)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::Drop(base) => {
                if self.value_has_grade_one(base) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "linear values cannot be dropped; consume them by matching or passing them on",
                    ));
                }
                if !self.expr(base, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::Try { value, .. } => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
                // The error path returns before the rest of the expression.
                self.check_exact(
                    &self.active.clone(),
                    expr.span,
                    "'?' takes its early error return",
                )?;
            }
            ExprKind::Return(value) => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
                self.check_exact(&self.active.clone(), expr.span, "this return")?;
                return Ok(false);
            }
            ExprKind::Assign(slot, value) => {
                if self.guard && self.is_tracked(*slot) {
                    return Err(self.grade_error(
                        *slot,
                        expr.span,
                        "cannot be replaced inside a match guard",
                        "a guard may fail after the replacement, so a later arm would observe a path-dependent value",
                    ));
                }
                // The replacement expression is evaluated once; only its
                // resulting value is subject to the surrounding demand.
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
                if self.is_tracked(*slot) {
                    self.check_exact(&[*slot], expr.span, "it is replaced by an assignment")?;
                    self.counts.insert(*slot, Grade::ZERO);
                }
            }
            ExprKind::Binary(
                crate::lexer::Kind::AmpAmp | crate::lexer::Kind::PipePipe,
                left,
                right,
            ) => {
                if !self.expr(left, multiplier)? {
                    return Ok(false);
                }
                let mut skipped = self.clone();
                let right_survives = self.expr(right, multiplier)?;
                if right_survives {
                    self.join(&skipped, expr.span, "a short-circuit expression")?;
                    self.merge_breaks(&skipped, expr.span)?;
                } else {
                    // Only the left-value path that skips the right operand
                    // continues; the right path diverges. Its break records
                    // still matter to an enclosing loop.
                    skipped.merge_breaks(self, expr.span)?;
                    skipped.guard = self.guard;
                    *self = skipped;
                }
            }
            ExprKind::Binary(_, left, right) => {
                if !self.expr(left, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(right, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::Call(target, arguments) => {
                for (index, argument) in arguments.iter().enumerate() {
                    if self.value_moves_linear(argument) {
                        self.check_linear_argument(*target, index, argument.span)?;
                    }
                    let demand = self.demand(*target, index);
                    let nested = multiplier.saturating_mul(demand);
                    if !self.expr(argument, nested)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                if !self.expr(callee, multiplier)? {
                    return Ok(false);
                }
                let id = match callee.ty {
                    Type::Fn(id) | Type::Once(id) => Some(id),
                    _ => None,
                };
                for (index, argument) in arguments.iter().enumerate() {
                    let grade = id
                        .and_then(|id| self.program.function_types.get(id))
                        .and_then(|signature| {
                            signature.parameter_grades.get(index).copied().flatten()
                        });
                    if self.value_moves_linear(argument) {
                        let ty = id
                            .and_then(|id| self.program.function_types.get(id))
                            .and_then(|signature| signature.parameters.get(index).copied());
                        self.check_linear_parameter(grade, ty, argument.span)?;
                    }
                    let demand = match grade {
                        Some(Grade::Finite(0)) | None => Grade::ONE,
                        Some(grade) => grade,
                    };
                    let nested = multiplier.saturating_mul(demand);
                    if !self.expr(argument, nested)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
                if !self.expr(body, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::TaskYield | ExprKind::TaskCheckCancel => {}
            ExprKind::TaskCancel(task) => {
                if !self.expr(task, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::TaskJoin { task, .. } => {
                if !self.expr(task, Grade::ONE)? {
                    return Ok(false);
                }
            }
            ExprKind::FnValue { captures, .. } => {
                for capture in captures {
                    if !self.expr(capture, Grade::ONE)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::Construct { fields, .. } => {
                for field in fields {
                    if !self.expr(field, multiplier)? {
                        return Ok(false);
                    }
                }
            }
            ExprKind::If(condition, yes, no) => {
                if !self.expr(condition, multiplier)? {
                    return Ok(false);
                }
                let mut baseline = self.clone();
                let yes_survives = baseline.block(yes, false, multiplier)?;
                let mut other = self.clone();
                let no_survives = other.block(no, false, multiplier)?;
                return match (yes_survives, no_survives) {
                    (true, true) => {
                        baseline.join(&other, expr.span, "an if/else")?;
                        baseline.merge_breaks(&other, expr.span)?;
                        *self = baseline;
                        Ok(true)
                    }
                    (true, false) => {
                        baseline.merge_breaks(&other, expr.span)?;
                        *self = baseline;
                        Ok(true)
                    }
                    (false, true) => {
                        other.merge_breaks(&baseline, expr.span)?;
                        *self = other;
                        Ok(true)
                    }
                    (false, false) => {
                        baseline.merge_breaks(&other, expr.span)?;
                        *self = baseline;
                        Ok(false)
                    }
                };
            }
            ExprKind::Match(value, arms) => {
                if !self.expr(value, multiplier)? {
                    return Ok(false);
                }
                let baseline = self.clone();
                let mut joined: Option<Self> = None;
                let mut break_records = baseline.clone();
                for arm in arms {
                    let mut arm_state = baseline.clone();
                    let mut binding_set = std::collections::BTreeSet::new();
                    crate::ownership::pattern_bindings(&arm.pattern, &mut binding_set);
                    let bindings: Vec<usize> = binding_set.into_iter().collect();
                    for slot in &bindings {
                        arm_state.activate(*slot);
                    }
                    if let Some(guard) = &arm.guard {
                        let old = arm_state.guard;
                        arm_state.guard = true;
                        let survives = arm_state.expr(guard, multiplier)?;
                        arm_state.guard = old;
                        if !survives {
                            break_records.merge_breaks(&arm_state, arm.body.span)?;
                            continue;
                        }
                    }
                    let survives = arm_state.expr(&arm.body, multiplier)?;
                    let local: Vec<usize> = arm_state.active[baseline.active.len()..].to_vec();
                    if survives {
                        arm_state.check_exact(
                            &local,
                            arm.body.span,
                            "the end of this match arm",
                        )?;
                    }
                    for slot in local {
                        arm_state.deactivate(slot);
                    }
                    break_records.merge_breaks(&arm_state, arm.body.span)?;
                    if survives {
                        match &mut joined {
                            Some(state) => state.join(&arm_state, arm.body.span, "a match")?,
                            None => joined = Some(arm_state),
                        }
                    }
                }
                return match joined {
                    Some(mut state) => {
                        state.merge_breaks(&break_records, expr.span)?;
                        *self = state;
                        Ok(true)
                    }
                    None => {
                        let mut state = baseline;
                        state.merge_breaks(&break_records, expr.span)?;
                        *self = state;
                        Ok(false)
                    }
                };
            }
            ExprKind::While(condition, body) => {
                self.enter_loop();
                let entry = self.clone();
                let alive = self.expr(condition, multiplier)?;
                if !alive {
                    self.loops.pop();
                    return Ok(false);
                }
                // The condition runs before every iteration and once on the
                // zero-iteration path; exact outer grades must be restored.
                self.check_iteration(condition.span, "the while condition")?;
                self.block(body, true, multiplier)?;
                let frame = self.loops.pop().unwrap();
                // A `while` may execute zero times: the head counts and every
                // break path must agree.
                if let Some(breaks) = frame.breaks {
                    self.counts = entry.counts.clone();
                    self.active = entry.active.clone();
                    for (slot, count) in &entry.counts {
                        if breaks.get(slot).copied().unwrap_or(Grade::ZERO) != *count {
                            return Err(self.grade_error(
                                *slot,
                                expr.span,
                                "is used differently on the zero-iteration and break paths of a while loop",
                                "the loop may not run at all, so an exact grade cannot rely on a break-path use",
                            ));
                        }
                    }
                } else {
                    self.counts = entry.counts;
                    self.active = entry.active;
                }
            }
            ExprKind::Loop(body) => {
                self.enter_loop();
                let entry = self.clone();
                let body_alive = self.block(body, true, multiplier)?;
                let frame = self.loops.pop().unwrap();
                self.active = entry.active;
                if let Some(breaks) = frame.breaks {
                    self.counts = breaks;
                } else {
                    self.counts = entry.counts;
                    if !body_alive || expr.ty == Type::Never {
                        return Ok(false);
                    }
                }
            }
            ExprKind::Break(value, _) => {
                if let Some(value) = value
                    && !self.expr(value, multiplier)?
                {
                    return Ok(false);
                }
                self.check_loop_locals(expr.span, "'break'")?;
                self.note_break(expr.span)?;
                return Ok(false);
            }
            ExprKind::Continue(_) => {
                self.check_iteration(expr.span, "'continue'")?;
                return Ok(false);
            }
            ExprKind::BytesAt(bytes, index) => {
                if !self.expr(bytes, multiplier)? {
                    return Ok(false);
                }
                if !self.expr(index, multiplier)? {
                    return Ok(false);
                }
            }
            ExprKind::Slice {
                base, start, end, ..
            } => {
                if !self.expr(base, multiplier)? {
                    return Ok(false);
                }
                if let Some(start) = start
                    && !self.expr(start, multiplier)?
                {
                    return Ok(false);
                }
                if let Some(end) = end
                    && !self.expr(end, multiplier)?
                {
                    return Ok(false);
                }
            }
            ExprKind::RefAssign(reference, _, value) => {
                if !self.expr(reference, Grade::ONE)? {
                    return Ok(false);
                }
                if !self.expr(value, Grade::ONE)? {
                    return Ok(false);
                }
            }
        }
        Ok(expr.ty != Type::Never)
    }
    fn enter_loop(&mut self) {
        self.loops.push(Frame {
            entry: self.counts.clone(),
            active_start: self.active.len(),
            breaks: None,
        });
    }
    /// The multiplicity a callee places on runtime argument `index`.
    ///
    /// An unannotated parameter uses its argument once. A `@[0]` parameter
    /// still evaluates its argument (the language is strict), so it counts as
    /// one evaluation; only `@[n]` and `@[many]` duplicate the resulting value.
    fn demand(&self, target: Target, index: usize) -> Grade {
        match target {
            Target::Function(function) => self
                .program
                .functions
                .get(function)
                .and_then(|f| f.parameter_grades.get(index))
                .map_or(Grade::ONE, |grade| match grade {
                    Some(Grade::Finite(0)) | None => Grade::ONE,
                    Some(grade) => *grade,
                }),
            _ => Grade::ONE,
        }
    }
}
fn block_span(block: &Block) -> Span {
    block
        .tail
        .as_ref()
        .map(|tail| tail.span)
        .or_else(|| {
            block.statements.last().map(|statement| match statement {
                Statement::Let(_, expr) | Statement::Expr(expr) => expr.span,
            })
        })
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::Grade;

    fn n(value: u64) -> Grade {
        Grade::Finite(value)
    }

    #[test]
    fn grade_semiring_has_expected_laws() {
        assert_eq!(n(0).checked_add(n(3)), Some(n(3)));
        assert_eq!(n(2).checked_add(n(3)), Some(n(5)));
        assert_eq!(Grade::Many.checked_add(n(2)), Some(Grade::Many));
        assert_eq!(n(0).checked_mul(Grade::Many), Some(n(0)));
        assert_eq!(n(1).checked_mul(n(7)), Some(n(7)));
        assert_eq!(n(2).checked_mul(n(3)), Some(n(6)));
        assert_eq!(n(2).checked_mul(Grade::Many), Some(Grade::Many));
        assert_eq!(Grade::Many.checked_mul(Grade::Many), Some(Grade::Many));
        assert_eq!(n(u64::MAX).checked_add(n(1)), None);
        assert_eq!(n(u64::MAX).checked_mul(n(2)), None);
        assert_eq!(Grade::Many.saturating_add(n(u64::MAX)), Grade::Many);
        assert_eq!(n(0).saturating_mul(Grade::Many), n(0));
    }

    #[test]
    fn grade_display_is_stable() {
        assert_eq!(n(0).to_string(), "0");
        assert_eq!(n(42).to_string(), "42");
        assert_eq!(Grade::Many.to_string(), "many");
    }
}
