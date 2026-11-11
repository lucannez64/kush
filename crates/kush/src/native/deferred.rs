//! Deferred overflow checks for counted loops.
//!
//! Kush integer arithmetic panics on overflow. A panic branch after every
//! operation is cheap for scalar code, but it stops LLVM from vectorizing a
//! loop: each iteration has an early exit with a side effect. Rust release
//! builds avoid the problem by not checking; Kush keeps the check and moves
//! it.
//!
//! For an innermost counted loop without observable effects, the panic is
//! deferred to the loop exit, in one of two ways.
//!
//! **Exact.** The operation wraps and ORs its exact overflow bit into a
//! sticky word tested once after the loop. Until the first overflow every
//! value equals the checked execution's value, so the sticky word is set
//! exactly when the checked loop would have panicked. This needs no replay,
//! so it also applies to loops that update a slice in place.
//!
//! **Certified.** Signed 64-bit `+`, `-` and `*` simply wrap, with no
//! per-operation test at all (an exact test would keep multiplications
//! scalar, and the test of a reduction `acc = acc + e` depends on the running
//! sum, which serializes the loop). Instead the loop ORs a magnitude word for
//! every *leaf* operand, i.e. every operand that is not itself a certified
//! operation, and counts reduction steps. After the loop those give, for each
//! leaf, a `u` with `|leaf| <= 2^u` over all iterations, and bounds follow
//! structurally:
//!
//! ```text
//! u(a + b) = u(a - b) = max(u(a), u(b)) + 1      u(a * b) = u(a) + u(b)
//! u(prefix sums of acc) = max(u(acc at entry), u(operands)) + bits(count)
//! ```
//!
//! If every certified result has `u <= 62`, none overflowed: take the first
//! operation that would overflow in the checked execution; all its inputs
//! are still exact and were observed by the magnitude words, so its result
//! is bounded by `2^62`, a contradiction. If a bound is too large nothing is
//! concluded; the loop state is restored and the loop is replayed with
//! ordinary checks. Replay requires that the loop reads no memory it writes:
//! it may only store through exclusive slices it never reads.
//!
//! Both are unobservable: a panic aborts the process, and the loop performs
//! no I/O, calls, allocation or ownership transfer. What keeps the
//! speculative execution well behaved after an overflow that has not been
//! reported yet:
//!
//! * **Bounded delay.** The loop runs in chunks of `CHUNK` iterations, each
//!   with its own sticky word, certificate and replay state. Whatever wrapped
//!   values do to the loop, it stops and reports within one chunk.
//! * **No proof-dependent access.** The checker's proofs may use "this
//!   operation did not overflow" as a hypothesis, so a loop with a proved,
//!   unchecked read (`Slice.at`, `Vec.at`) is not deferred. Every memory
//!   access in a deferred loop is bounds-checked at run time.
//! * **Canonical values.** A deferred narrow operation yields its wrapped
//!   result, and proved-in-range narrow arithmetic is wrapped too, so every
//!   narrow value stays in the form the rest of the lowering assumes.
//! * **Everything else that can panic still panics immediately**, which is
//!   the outcome the checked loop would have had.
//!
//! In addition the loop must be counted over an integer with a bound made of
//! constants, locals and lengths, and every value feeding a loop or branch
//! condition or an index keeps its immediate check. That keeps the
//! speculative run on the checked run's path in the common case; safety does
//! not rest on it.
use crate::executable::{self as ex, BytesOp, Expr, ExprKind, SliceOp, Statement, Target, VecOp};
use crate::executable::{Function, Type};
use crate::lexer::Kind;
use std::collections::{BTreeMap, BTreeSet};

/// Identity of one expression node during a single lowering.
pub(super) fn key(expr: &Expr) -> usize {
    std::ptr::from_ref(expr) as usize
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Mode {
    /// Wrap and record the exact overflow bit.
    Exact,
    /// Wrap; the result is validated by the loop's certificate.
    Certified,
    /// A certified reduction step `acc = acc +/- e`.
    Accumulate,
}

/// `u` with `|value| <= 2^u`, as a function of the loop's magnitude words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Bound {
    Constant(u32),
    /// A tracked operand, by [`key`].
    Leaf(usize),
    Sum(Box<Bound>, Box<Bound>),
    Product(Box<Bound>, Box<Bound>),
    /// Every prefix sum of a reduction local with these step operands.
    Accumulated {
        local: usize,
        operands: Vec<Bound>,
    },
}

#[derive(Debug, Default)]
pub(super) struct Plan {
    /// Deferred checked operations, by [`key`].
    pub modes: BTreeMap<usize, Mode>,
    /// Operands whose magnitude the loop tracks, by [`key`].
    pub leaves: BTreeSet<usize>,
    /// Bounds that must all be at most [`LIMIT`] for the certificate to hold.
    pub obligations: Vec<Bound>,
    /// Reduction locals; their entry values are part of the certificate.
    pub accumulators: Vec<usize>,
    /// Locals restored before an exact replay.
    pub replay: Vec<usize>,
    /// Pairs of a written view and a read view that a replay needs to be
    /// disjoint. The types say they are; the lowering checks the addresses
    /// anyway, so a replay never depends on that.
    pub disjoint: Vec<(usize, usize)>,
    /// The counter of a loop that counts upward, when it has one.
    pub ascending: Option<usize>,
    /// Whether a certified operation multiplies two non-constant operands.
    multiplies: bool,
}

/// A certified result may be at most `2^LIMIT` in absolute value.
pub(super) const LIMIT: i64 = 62;

/// A deferred loop reports after at most this many iterations.
pub(super) const CHUNK: i64 = 1 << 16;

fn scalar(ty: Type) -> bool {
    matches!(
        ty,
        Type::I64 | Type::Int(_) | Type::Float(_) | Type::Char | Type::Bool | Type::Unit
    )
}
fn integer(ty: Type) -> bool {
    matches!(ty, Type::I64 | Type::Int(_))
}
fn local_read(expr: &Expr) -> Option<usize> {
    match expr.kind {
        ExprKind::Local(slot) | ExprKind::Peek(slot) => Some(slot),
        _ => None,
    }
}

struct Analysis<'a> {
    function: &'a Function,
    /// Right-hand sides of every assignment or `let` of a local in the loop.
    assignments: BTreeMap<usize, Vec<&'a Expr>>,
    declared: BTreeSet<usize>,
    reads: BTreeMap<usize, usize>,
    candidates: Vec<&'a Expr>,
    /// Expressions whose value must equal the checked execution's value.
    exact: Vec<&'a Expr>,
    /// Element indices of the loop's reads and writes.
    indices: Vec<&'a Expr>,
    /// `local = <checked + or ->` statements.
    updates: Vec<(usize, &'a Expr)>,
    /// Slice locals the loop stores through, and container locals it reads.
    stored: BTreeSet<usize>,
    loaded: BTreeSet<usize>,
    /// Plain reads of locals, by [`key`]; filtered to loop-invariant ones.
    invariant: BTreeSet<usize>,
    local_reads: BTreeMap<usize, usize>,
}

impl<'a> Analysis<'a> {
    fn block(&mut self, block: &'a ex::Block) -> Result<(), &'static str> {
        for statement in &block.statements {
            match statement {
                Statement::Let(slot, value) => {
                    if !scalar(self.function.locals[*slot].ty) {
                        return Err("a non-scalar binding");
                    }
                    self.declared.insert(*slot);
                    self.assignments.entry(*slot).or_default().push(value);
                    self.expr(value)?;
                }
                Statement::Expr(value) => self.expr(value)?,
                Statement::Declare(_) => return Err("a temporary owner"),
            }
        }
        match &block.tail {
            Some(tail) => self.expr(tail),
            None => Ok(()),
        }
    }
    /// A borrowed container operand: a plain local that the loop never assigns.
    fn receiver(&mut self, expr: &'a Expr) -> Result<usize, &'static str> {
        let slot = match expr.kind {
            ExprKind::Borrow(slot) => Some(slot),
            _ => local_read(expr),
        };
        match slot {
            Some(slot) => {
                *self.reads.entry(slot).or_default() += 1;
                Ok(slot)
            }
            None => Err("a container operand that is not a local"),
        }
    }
    fn expr(&mut self, expr: &'a Expr) -> Result<(), &'static str> {
        if expr.resource.is_some() {
            return Err("an owned temporary");
        }
        if !(scalar(expr.ty) || expr.ty == Type::Never) {
            return Err("a non-scalar value");
        }
        match &expr.kind {
            ExprKind::Constant(_) => Ok(()),
            ExprKind::Local(slot) | ExprKind::Peek(slot) => {
                *self.reads.entry(*slot).or_default() += 1;
                self.invariant.insert(key(expr));
                self.local_reads.insert(key(expr), *slot);
                Ok(())
            }
            ExprKind::Block(block) => self.block(block),
            ExprKind::Unary(op, operand) => {
                if *op == Kind::Minus && integer(expr.ty) {
                    self.candidates.push(expr);
                }
                self.expr(operand)
            }
            ExprKind::Binary(op, left, right) => {
                match op {
                    Kind::Plus | Kind::Minus | Kind::Star if integer(expr.ty) => {
                        self.candidates.push(expr);
                    }
                    // The right operand runs conditionally.
                    Kind::AmpAmp | Kind::PipePipe => self.exact.push(left),
                    _ => {}
                }
                self.expr(left)?;
                self.expr(right)
            }
            ExprKind::Assign(slot, value) => {
                if !scalar(self.function.locals[*slot].ty) {
                    return Err("assignment to a non-scalar local");
                }
                self.assignments.entry(*slot).or_default().push(value);
                if matches!(value.kind, ExprKind::Binary(Kind::Plus | Kind::Minus, _, _)) {
                    self.updates.push((*slot, value));
                }
                self.expr(value)
            }
            ExprKind::If(condition, then_block, else_block) => {
                self.exact.push(condition);
                self.expr(condition)?;
                self.block(then_block)?;
                self.block(else_block)
            }
            ExprKind::Break(None, cleanup) if cleanup.is_empty() => Ok(()),
            ExprKind::Call(target, arguments) => self.call(target, arguments),
            ExprKind::While(..) | ExprKind::Loop(_) => Err("a nested loop"),
            ExprKind::Continue(_) => Err("continue"),
            _ => Err("an operation with effects or ownership"),
        }
    }
    fn call(&mut self, target: &Target, arguments: &'a [Expr]) -> Result<(), &'static str> {
        #[derive(PartialEq)]
        enum Access {
            Length,
            Load,
            Store,
        }
        let (access, value) = match target {
            Target::Slice(SliceOp::Len, _)
            | Target::Vec(VecOp::Len, _)
            | Target::Bytes(BytesOp::Len) => (Some(Access::Length), None),
            // Only checked reads. A proved, unchecked read (`at`) may owe its
            // proof to a deferred operation not having overflowed.
            Target::Slice(SliceOp::Get, element) | Target::Vec(VecOp::Get, element)
                if scalar(*element) =>
            {
                (Some(Access::Load), None)
            }
            Target::Bytes(BytesOp::Get) => (Some(Access::Load), None),
            Target::Slice(SliceOp::Set, element) if scalar(*element) => {
                (Some(Access::Store), arguments.len().checked_sub(1))
            }
            Target::Int(..) | Target::Float(_) => (None, None),
            _ => return Err("a call"),
        };
        let receiver = access.is_some();
        for (index, argument) in arguments.iter().enumerate() {
            if receiver && index == 0 {
                let slot = self.receiver(argument)?;
                match access {
                    Some(Access::Store) => {
                        // Only an exclusive view is known not to alias the
                        // loop's other operands.
                        if !matches!(self.function.locals[slot].ty, Type::SliceMut(_)) {
                            return Err("a store through a shared view");
                        }
                        self.stored.insert(slot);
                    }
                    Some(Access::Load) => {
                        self.loaded.insert(slot);
                    }
                    _ => {}
                }
                continue;
            }
            self.expr(argument)?;
            // Indices keep their immediate checks; a stored value may be
            // speculative because a panic discards it.
            if receiver && Some(index) != value {
                self.exact.push(argument);
                self.indices.push(argument);
            }
        }
        Ok(())
    }
}

fn reads_local(expr: &Expr, slot: usize) -> bool {
    if local_read(expr) == Some(slot) {
        return true;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| found |= reads_local(child, slot));
    found
}

/// The loop's induction local when it has the counted shape
/// `while i <op> bound { ...; i = i +/- c; ... }` with `c > 0`, one
/// unconditional update per iteration and a loop-invariant bound.
fn induction(condition: &Expr, body: &ex::Block) -> Option<usize> {
    let ExprKind::Binary(comparison, left, bound) = &condition.kind else {
        return None;
    };
    let slot = local_read(left)?;
    if !integer(left.ty) || !plain_bound(bound) {
        return None;
    }
    let step = match comparison {
        Kind::Lt | Kind::Le => Kind::Plus,
        Kind::Gt | Kind::Ge => Kind::Minus,
        _ => return None,
    };
    // The step is written `i + c`, but when the checker proves it cannot
    // overflow (as it does under `i < bound`) it arrives as an unchecked
    // operation instead.
    let unchecked = match step {
        Kind::Plus => crate::int::ArithOp::Add,
        _ => crate::int::ArithOp::Sub,
    };
    let is_step = |expr: &Expr| {
        let ExprKind::Assign(target, value) = &expr.kind else {
            return false;
        };
        let (base, amount) = match &value.kind {
            ExprKind::Binary(op, base, amount) if *op == step => (&**base, &**amount),
            ExprKind::Call(Target::Int(crate::int::IntOp::Unchecked(op), _, _), arguments)
                if *op == unchecked && arguments.len() == 2 =>
            {
                (&arguments[0], &arguments[1])
            }
            _ => return false,
        };
        *target == slot
            && local_read(base) == Some(slot)
            && matches!(amount.kind, ExprKind::Constant(c) if c > 0)
    };
    let top_level = body
        .statements
        .iter()
        .filter(|statement| matches!(statement, Statement::Expr(expr) if is_step(expr)))
        .count()
        + usize::from(body.tail.as_deref().is_some_and(is_step));
    (top_level == 1).then_some(slot)
}

/// `counter`, or `counter` plus or minus a constant.
fn follows_counter(index: &Expr, counter: usize) -> bool {
    if local_read(index) == Some(counter) {
        return true;
    }
    let (base, offset) = match &index.kind {
        ExprKind::Binary(Kind::Plus | Kind::Minus, base, offset) => (&**base, &**offset),
        ExprKind::Call(
            Target::Int(
                crate::int::IntOp::Unchecked(crate::int::ArithOp::Add | crate::int::ArithOp::Sub),
                _,
                _,
            ),
            arguments,
        ) if arguments.len() == 2 => (&arguments[0], &arguments[1]),
        _ => return false,
    };
    local_read(base) == Some(counter) && matches!(offset.kind, ExprKind::Constant(_))
}

/// A loop bound made of constants, locals, container lengths and arithmetic
/// on those: nothing the loop body could change by storing.
fn plain_bound(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Constant(_) | ExprKind::Local(_) | ExprKind::Peek(_) => integer(expr.ty),
        ExprKind::Binary(Kind::Plus | Kind::Minus | Kind::Star, left, right) => {
            integer(expr.ty) && plain_bound(left) && plain_bound(right)
        }
        ExprKind::Call(
            Target::Slice(SliceOp::Len, _)
            | Target::Vec(VecOp::Len, _)
            | Target::Bytes(BytesOp::Len),
            arguments,
        ) => arguments.len() == 1,
        _ => false,
    }
}

/// Plan deferred overflow checks for one innermost `while` loop, or `None`
/// when the loop must keep ordinary checks.
///
/// `wide_multiply` says the target multiplies 64-bit vectors natively. Without
/// it a multiplication is vectorized through three 32-bit multiplies, and a
/// loop that must also track two or more operands per iteration is faster
/// with ordinary checks.
pub(super) fn plan(
    function: &Function,
    condition: &Expr,
    body: &ex::Block,
    wide_multiply: bool,
) -> Option<Plan> {
    let trace = |reason: &str| {
        if std::env::var_os("KUSH_TRACE_DEFERRED").is_some() {
            eprintln!(
                "deferred overflow: loop in {} keeps immediate checks: {reason}",
                function.name
            );
        }
    };
    let mut analysis = Analysis {
        function,
        assignments: BTreeMap::new(),
        declared: BTreeSet::new(),
        reads: BTreeMap::new(),
        candidates: Vec::new(),
        exact: Vec::new(),
        indices: Vec::new(),
        updates: Vec::new(),
        stored: BTreeSet::new(),
        loaded: BTreeSet::new(),
        invariant: BTreeSet::new(),
        local_reads: BTreeMap::new(),
    };
    if let Err(reason) = analysis.expr(condition).and_then(|()| analysis.block(body)) {
        trace(reason);
        return None;
    }
    let Some(counter) = induction(condition, body) else {
        trace("it is not a counted loop");
        return None;
    };
    // One update of the counter, and a bound the loop cannot change.
    let ExprKind::Binary(_, _, bound) = &condition.kind else {
        return None;
    };
    if analysis.assignments.get(&counter).map_or(0, Vec::len) != 1
        || analysis
            .assignments
            .keys()
            .any(|slot| reads_local(bound, *slot))
    {
        trace("its bound or counter changes inside the loop");
        return None;
    }
    // Deferring pays only where the loop then vectorizes; in a scalar loop
    // a sticky flag costs more than the branch it replaces. An element
    // reached by anything but the counter (plus or minus a constant) is a
    // gather, a scatter or a dependence between iterations.
    if !analysis
        .indices
        .iter()
        .all(|index| follows_counter(index, counter))
    {
        trace("an index that does not follow the counter");
        return None;
    }
    analysis.exact.push(condition);
    let assigned: BTreeSet<usize> = analysis.assignments.keys().copied().collect();
    let local_reads = std::mem::take(&mut analysis.local_reads);
    analysis
        .invariant
        .retain(|read| !assigned.contains(&local_reads[read]));

    // Pin every operation an exact value depends on, through local data flow.
    let mut deferred: BTreeSet<usize> = analysis.candidates.iter().map(|e| key(e)).collect();
    let mut pinned_locals = BTreeSet::new();
    let mut work: Vec<&Expr> = analysis.exact.clone();
    while let Some(expr) = work.pop() {
        deferred.remove(&key(expr));
        if let Some(slot) = local_read(expr)
            && pinned_locals.insert(slot)
            && let Some(values) = analysis.assignments.get(&slot)
        {
            work.extend(values.iter().copied());
        }
        expr.for_each_child(&mut |child| work.push(child));
    }
    if deferred.is_empty() {
        trace("no checked arithmetic can be deferred");
        return None;
    }

    let mut plan = Plan::default();
    if matches!(&condition.kind, ExprKind::Binary(Kind::Lt | Kind::Le, _, _)) {
        plan.ascending = Some(counter);
    }
    for id in &deferred {
        plan.modes.insert(*id, Mode::Exact);
    }
    // A replay must observe the memory the first attempt observed: nothing
    // the loop reads may be something it wrote. Different locals are
    // different views, and the lowering confirms at run time that their
    // address ranges do not overlap, which it can do for slices.
    let view = |slot: &usize| {
        matches!(
            function.locals[*slot].ty,
            Type::Slice(_) | Type::SliceMut(_)
        )
    };
    let checkable = analysis.stored.is_empty() || analysis.loaded.iter().all(view);
    if analysis.stored.is_disjoint(&analysis.loaded) && checkable {
        certify(&analysis, &deferred, &mut plan);
        let varying = plan
            .leaves
            .iter()
            .filter(|leaf| !analysis.invariant.contains(leaf))
            .count();
        if plan.multiplies && varying >= 2 && !wide_multiply {
            trace("tracking its operands would cost more than the checks");
            return None;
        }
    }
    if !plan.obligations.is_empty() {
        for stored in &analysis.stored {
            for loaded in &analysis.loaded {
                plan.disjoint.push((*stored, *loaded));
            }
        }
        plan.replay = analysis
            .assignments
            .keys()
            .copied()
            .filter(|slot| !analysis.declared.contains(slot))
            .collect();
    }
    Some(plan)
}

/// Whether a deferred operation is plain signed 64-bit arithmetic.
fn certifiable(expr: &Expr) -> bool {
    expr.ty == Type::I64
        && match &expr.kind {
            ExprKind::Binary(Kind::Plus | Kind::Minus | Kind::Star, left, right) => {
                left.ty == Type::I64 && right.ty == Type::I64
            }
            ExprKind::Unary(Kind::Minus, operand) => operand.ty == Type::I64,
            _ => false,
        }
}

/// Replace exact tests of signed 64-bit operations by a loop certificate.
fn certify(analysis: &Analysis<'_>, deferred: &BTreeSet<usize>, plan: &mut Plan) {
    let function = analysis.function;
    // Reductions: every assignment of the local is `acc = acc +/- e`, and the
    // local is read nowhere else in the loop.
    let mut steps: BTreeMap<usize, Vec<&Expr>> = BTreeMap::new();
    for (slot, value) in &analysis.updates {
        let ExprKind::Binary(op, left, right) = &value.kind else {
            continue;
        };
        if !certifiable(value)
            || function.locals[*slot].ty != Type::I64
            || function.locals[*slot].pinned
            || !deferred.contains(&key(value))
        {
            continue;
        }
        let on_left = local_read(left) == Some(*slot) && !reads_local(right, *slot);
        let on_right =
            *op == Kind::Plus && local_read(right) == Some(*slot) && !reads_local(left, *slot);
        if on_left {
            steps.entry(*slot).or_default().push(right);
        } else if on_right {
            steps.entry(*slot).or_default().push(left);
        }
    }
    steps.retain(|slot, operands| {
        analysis.assignments.get(slot).map_or(0, Vec::len) == operands.len()
            && analysis.reads.get(slot).copied().unwrap_or(0) == operands.len()
    });
    let mut reduction_steps = BTreeSet::new();
    for (slot, value) in &analysis.updates {
        if steps.contains_key(slot) {
            reduction_steps.insert(key(value));
        }
    }
    let certified = |expr: &Expr| {
        deferred.contains(&key(expr)) && certifiable(expr) && !reduction_steps.contains(&key(expr))
    };
    fn bound(
        expr: &Expr,
        certified: &dyn Fn(&Expr) -> bool,
        leaves: &mut BTreeSet<usize>,
        nested: &mut BTreeSet<usize>,
        multiplies: &mut bool,
    ) -> Bound {
        if let ExprKind::Constant(value) = expr.kind {
            // The least `u` with `|value| <= 2^u`.
            let magnitude = value.unsigned_abs();
            return Bound::Constant(match magnitude {
                0 => 0,
                _ => u64::BITS - (magnitude - 1).leading_zeros(),
            });
        }
        if !certified(expr) {
            leaves.insert(key(expr));
            return Bound::Leaf(key(expr));
        }
        nested.insert(key(expr));
        match &expr.kind {
            ExprKind::Binary(op, left, right) => {
                let left = Box::new(bound(left, certified, leaves, nested, multiplies));
                let right = Box::new(bound(right, certified, leaves, nested, multiplies));
                if *op == Kind::Star {
                    if !matches!(*left, Bound::Constant(_)) && !matches!(*right, Bound::Constant(_))
                    {
                        *multiplies = true;
                    }
                    Bound::Product(left, right)
                } else {
                    Bound::Sum(left, right)
                }
            }
            ExprKind::Unary(_, operand) => bound(operand, certified, leaves, nested, multiplies),
            _ => unreachable!("certified operations are unary or binary"),
        }
    }
    // Operations that are operands of another certified operation are covered
    // by their parent: bounds only grow towards the root.
    let mut nested = BTreeSet::new();
    let mut roots = Vec::new();
    for candidate in &analysis.candidates {
        if certified(candidate) {
            let mut inner = BTreeSet::new();
            let result = bound(
                candidate,
                &certified,
                &mut plan.leaves,
                &mut inner,
                &mut plan.multiplies,
            );
            inner.remove(&key(candidate));
            nested.extend(inner);
            roots.push((key(candidate), result));
            plan.modes.insert(key(candidate), Mode::Certified);
        }
    }
    for (id, result) in roots {
        if !nested.contains(&id) {
            plan.obligations.push(result);
        }
    }
    for (slot, operands) in steps {
        let operands = operands
            .into_iter()
            .map(|operand| {
                bound(
                    operand,
                    &certified,
                    &mut plan.leaves,
                    &mut BTreeSet::new(),
                    &mut plan.multiplies,
                )
            })
            .collect();
        plan.obligations.push(Bound::Accumulated {
            local: slot,
            operands,
        });
        plan.accumulators.push(slot);
    }
    for id in reduction_steps {
        plan.modes.insert(id, Mode::Accumulate);
    }
}
