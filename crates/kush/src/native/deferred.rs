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

/// What an element access reads or writes.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) enum Container {
    /// A slice view, of this element type.
    Slice(Type),
    /// A vector, of this element type.
    Vec(Type),
    /// A byte buffer.
    Bytes,
}

/// An element read or write in the loop, at the counter plus a constant.
/// The lowering proves all of a chunk's accesses in range before the chunk
/// runs and then emits them without per-element checks; see
/// `docs/deferred-overflow.md`.
#[derive(Debug, Clone, Copy)]
pub(super) struct Access<'a> {
    /// The call, by [`key`].
    pub call: usize,
    /// The container operand of the call, a local or a borrow of one.
    pub receiver: &'a Expr,
    pub container: Container,
    /// The index is the counter plus this.
    pub offset: i64,
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
    /// The loop counter, and the constant it moves by each iteration (up
    /// for `<` and `<=`, down for `>` and `>=`).
    pub counter: usize,
    pub step: i64,
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

struct Analysis<'f, 'a> {
    function: &'f Function,
    /// Right-hand sides of every assignment or `let` of a local in the loop.
    assignments: BTreeMap<usize, Vec<&'a Expr>>,
    declared: BTreeSet<usize>,
    reads: BTreeMap<usize, usize>,
    candidates: Vec<&'a Expr>,
    /// Expressions whose value must equal the checked execution's value.
    exact: Vec<&'a Expr>,
    /// The loop's element reads and writes: call, receiver, container,
    /// index.
    accesses: Vec<(&'a Expr, &'a Expr, Container, &'a Expr)>,
    /// `local = <checked + or ->` statements.
    updates: Vec<(usize, &'a Expr)>,
    /// Slice locals the loop stores through, and container locals it reads.
    stored: BTreeSet<usize>,
    loaded: BTreeSet<usize>,
    /// What keeps a loop from vectorizing, so that deferring it would only
    /// cost: an early exit, a division, a store that runs conditionally.
    breaks: bool,
    divides: bool,
    conditional_store: bool,
    /// Checked arithmetic that runs conditionally, and byte-buffer reads:
    /// both vectorize, but on baseline x86-64 (SSE2) the blends and the
    /// widening of bytes to words cost more than the checks they replace.
    conditional_arithmetic: bool,
    byte_reads: bool,
    /// How deep the walk is inside code that runs conditionally.
    conditional: usize,
    /// Plain reads of locals, by [`key`]; filtered to loop-invariant ones.
    invariant: BTreeSet<usize>,
    local_reads: BTreeMap<usize, usize>,
}

impl<'a> Analysis<'_, 'a> {
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
                    self.conditional_arithmetic |= self.conditional > 0;
                }
                self.expr(operand)
            }
            ExprKind::Binary(op, left, right) => {
                match op {
                    Kind::Plus | Kind::Minus | Kind::Star if integer(expr.ty) => {
                        self.candidates.push(expr);
                        self.conditional_arithmetic |= self.conditional > 0;
                    }
                    // The right operand runs conditionally.
                    Kind::AmpAmp | Kind::PipePipe => {
                        self.exact.push(left);
                        self.expr(left)?;
                        self.conditional += 1;
                        let result = self.expr(right);
                        self.conditional -= 1;
                        return result;
                    }
                    Kind::Slash | Kind::Percent => self.divides = true,
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
                self.conditional += 1;
                let result = self.block(then_block).and_then(|()| self.block(else_block));
                self.conditional -= 1;
                result
            }
            ExprKind::Break(None, cleanup) if cleanup.is_empty() => {
                self.breaks = true;
                Ok(())
            }
            ExprKind::Call(target, arguments) => self.call(expr, target, arguments),
            ExprKind::While(..) | ExprKind::Loop(_) => Err("a nested loop"),
            ExprKind::Continue(_) => Err("continue"),
            _ => Err("an operation with effects or ownership"),
        }
    }
    fn call(
        &mut self,
        call: &'a Expr,
        target: &Target,
        arguments: &'a [Expr],
    ) -> Result<(), &'static str> {
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
            Target::Bytes(BytesOp::Get) => {
                self.byte_reads = true;
                (Some(Access::Load), None)
            }
            Target::Slice(SliceOp::Set, element) if scalar(*element) => {
                (Some(Access::Store), arguments.len().checked_sub(1))
            }
            Target::Int(..) | Target::Float(_) => (None, None),
            _ => return Err("a call"),
        };
        let container = match target {
            Target::Slice(_, element) => Some(Container::Slice(*element)),
            Target::Vec(_, element) => Some(Container::Vec(*element)),
            Target::Bytes(_) => Some(Container::Bytes),
            _ => None,
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
                        self.conditional_store |= self.conditional > 0;
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
                if access != Some(Access::Length)
                    && let Some(container) = container
                {
                    self.accesses
                        .push((call, &arguments[0], container, argument));
                }
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
/// Also returns where the update is: the index of its top-level statement,
/// or the number of statements when it is the block's tail.
fn induction(condition: &Expr, body: &ex::Block) -> Option<(usize, i64, usize)> {
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
    let step_of = |expr: &Expr| -> Option<i64> {
        let ExprKind::Assign(target, value) = &expr.kind else {
            return None;
        };
        let (base, amount) = match &value.kind {
            ExprKind::Binary(op, base, amount) if *op == step => (&**base, &**amount),
            ExprKind::Call(Target::Int(crate::int::IntOp::Unchecked(op), _, _), arguments)
                if *op == unchecked && arguments.len() == 2 =>
            {
                (&arguments[0], &arguments[1])
            }
            _ => return None,
        };
        match amount.kind {
            ExprKind::Constant(c) if c > 0 && *target == slot && local_read(base) == Some(slot) => {
                Some(c)
            }
            _ => None,
        }
    };
    let steps: Vec<(i64, usize)> = body
        .statements
        .iter()
        .enumerate()
        .filter_map(|(at, statement)| match statement {
            Statement::Expr(expr) => step_of(expr).map(|step| (step, at)),
            _ => None,
        })
        .chain(
            body.tail
                .as_deref()
                .and_then(step_of)
                .map(|step| (step, body.statements.len())),
        )
        .collect();
    match steps.as_slice() {
        [(step, at)] => Some((slot, *step, *at)),
        _ => None,
    }
}

/// Keys of every call in an expression.
fn calls(expr: &Expr, found: &mut BTreeSet<usize>) {
    if matches!(expr.kind, ExprKind::Call(..)) {
        found.insert(key(expr));
    }
    expr.for_each_child(&mut |child| calls(child, found));
}

/// `Some(c)` when `index` is `counter + c`: the counter itself, or the
/// counter plus or minus a constant.
fn counter_offset(index: &Expr, counter: usize) -> Option<i64> {
    if local_read(index) == Some(counter) {
        return Some(0);
    }
    use crate::int::{ArithOp, IntOp};
    let (subtract, base, offset) = match &index.kind {
        ExprKind::Binary(op @ (Kind::Plus | Kind::Minus), base, offset) => {
            (*op == Kind::Minus, &**base, &**offset)
        }
        ExprKind::Call(
            Target::Int(IntOp::Unchecked(op @ (ArithOp::Add | ArithOp::Sub)), _, _),
            arguments,
        ) if arguments.len() == 2 => (*op == ArithOp::Sub, &arguments[0], &arguments[1]),
        _ => return None,
    };
    let ExprKind::Constant(constant) = offset.kind else {
        return None;
    };
    if local_read(base) != Some(counter) {
        return None;
    }
    if subtract {
        constant.checked_neg()
    } else {
        Some(constant)
    }
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
pub(super) fn plan<'a>(
    function: &Function,
    condition: &'a Expr,
    body: &'a ex::Block,
    wide_multiply: bool,
    wide_vectors: bool,
) -> Option<(Plan, Vec<Access<'a>>)> {
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
        accesses: Vec::new(),
        updates: Vec::new(),
        stored: BTreeSet::new(),
        loaded: BTreeSet::new(),
        invariant: BTreeSet::new(),
        local_reads: BTreeMap::new(),
        breaks: false,
        divides: false,
        conditional_store: false,
        conditional_arithmetic: false,
        byte_reads: false,
        conditional: 0,
    };
    if let Err(reason) = analysis.expr(condition).and_then(|()| analysis.block(body)) {
        trace(reason);
        return None;
    }
    // Deferring pays only where LLVM then vectorizes the loop profitably: a
    // scalar loop with sticky overflow words is slower than one with
    // branches, and it still costs compile time. LLVM 18 does not vectorize
    // a loop with an early exit, x86 has no 64-bit vector division, and a
    // store that runs conditionally needs masked stores (AVX). On baseline
    // x86-64 (SSE2), conditional arithmetic and byte reads vectorize but
    // measured slower than the checked loop; with `--target-cpu native`
    // (here AVX-512) the same loops ran 2.8 to 2.9 times faster.
    if analysis.breaks {
        trace("an early exit (`break`), which keeps it from vectorizing");
        return None;
    }
    if analysis.divides {
        trace("a division, which does not vectorize");
        return None;
    }
    if !wide_vectors {
        let reason = if analysis.conditional_store {
            Some("a store under a condition")
        } else if analysis.conditional_arithmetic {
            Some("arithmetic under a condition")
        } else if analysis.byte_reads {
            Some("byte-buffer reads")
        } else {
            None
        };
        if let Some(reason) = reason {
            trace(&format!(
                "{reason}, which only pays with `--target-cpu native`"
            ));
            return None;
        }
    }
    let Some((counter, step, update)) = induction(condition, body) else {
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
    // An access after the counter's update in the body sees the counter
    // one step on: within an iteration, its index is the updated counter
    // plus its offset. The update is a top-level statement, so every access
    // is either before it or after it in every iteration.
    let mut after = BTreeSet::new();
    for statement in body.statements.iter().skip(update + 1) {
        match statement {
            Statement::Let(_, expr) | Statement::Expr(expr) => calls(expr, &mut after),
            Statement::Declare(_) => {}
        }
    }
    if update < body.statements.len()
        && let Some(tail) = &body.tail
    {
        calls(tail, &mut after);
    }
    let moved = match &condition.kind {
        ExprKind::Binary(Kind::Lt | Kind::Le, _, _) => step,
        _ => -step,
    };
    let mut accesses = Vec::new();
    for (call, receiver, container, index) in &analysis.accesses {
        let Some(offset) = counter_offset(index, counter) else {
            trace("an index that does not follow the counter");
            return None;
        };
        let offset = if after.contains(&key(call)) {
            match offset.checked_add(moved) {
                Some(offset) => offset,
                None => {
                    trace("an index too far from the counter");
                    return None;
                }
            }
        } else {
            offset
        };
        accesses.push(Access {
            call: key(call),
            receiver,
            container: *container,
            offset,
        });
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

    let mut plan = Plan {
        counter,
        step,
        ..Plan::default()
    };
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
    Some((plan, accesses))
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
fn certify(analysis: &Analysis<'_, '_>, deferred: &BTreeSet<usize>, plan: &mut Plan) {
    let function = analysis.function;
    // Reductions: every assignment of the local is `acc = acc +/- e`, or a
    // chain `acc = acc + a - b + c` with the local leftmost, and the local is
    // read nowhere else in the loop. Each operation of a chain adds one term,
    // and every intermediate value is itself a prefix sum of the terms, so
    // one bound covers them all; this is what lets `acc = acc + x[i] + y[i]`
    // vectorize instead of tracking the running sum as an operand.
    let reducing = |expr: &Expr| {
        matches!(expr.kind, ExprKind::Binary(Kind::Plus | Kind::Minus, _, _))
            && certifiable(expr)
            && deferred.contains(&key(expr))
    };
    // The operations and terms of a chain whose leftmost operand is `slot`.
    fn chain<'e>(
        expr: &'e Expr,
        slot: usize,
        reducing: &dyn Fn(&Expr) -> bool,
        operations: &mut Vec<&'e Expr>,
        terms: &mut Vec<&'e Expr>,
    ) -> bool {
        let ExprKind::Binary(_, left, right) = &expr.kind else {
            return false;
        };
        if !reducing(expr) || reads_local(right, slot) {
            return false;
        }
        if local_read(left) != Some(slot) && !chain(left, slot, reducing, operations, terms) {
            return false;
        }
        operations.push(expr);
        terms.push(right);
        true
    }
    #[derive(Default)]
    struct Reduction<'e> {
        updates: usize,
        operations: Vec<&'e Expr>,
        terms: Vec<&'e Expr>,
    }
    let mut steps: BTreeMap<usize, Reduction<'_>> = BTreeMap::new();
    for (slot, value) in &analysis.updates {
        if function.locals[*slot].ty != Type::I64 || function.locals[*slot].pinned {
            continue;
        }
        let mut operations = Vec::new();
        let mut terms = Vec::new();
        let found = chain(value, *slot, &reducing, &mut operations, &mut terms)
            || matches!(&value.kind, ExprKind::Binary(Kind::Plus, left, right)
            if reducing(value)
                && local_read(right) == Some(*slot)
                && !reads_local(left, *slot)
                && {
                    operations.push(value);
                    terms.push(left);
                    true
                });
        if found {
            let reduction = steps.entry(*slot).or_default();
            reduction.updates += 1;
            reduction.operations.extend(operations);
            reduction.terms.extend(terms);
        }
    }
    steps.retain(|slot, reduction| {
        analysis.assignments.get(slot).map_or(0, Vec::len) == reduction.updates
            && analysis.reads.get(slot).copied().unwrap_or(0) == reduction.updates
    });
    let reduction_steps: BTreeSet<usize> = steps
        .values()
        .flat_map(|reduction| reduction.operations.iter().map(|operation| key(operation)))
        .collect();
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
        // A value whose range its type already bounds needs no tracking:
        // a byte read, or a widened narrow integer (narrow values stay
        // canonical in deferred loops too).
        match &expr.kind {
            ExprKind::Call(Target::Bytes(BytesOp::Get), _) => return Bound::Constant(8),
            ExprKind::Call(Target::Int(crate::int::IntOp::Convert, source, _), _)
                if source.bits() < 64 =>
            {
                let bits = source.bits();
                return Bound::Constant(if source.signed() { bits - 1 } else { bits });
            }
            _ => {}
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
    for (slot, reduction) in steps {
        let operands = reduction
            .terms
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
