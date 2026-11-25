//! Deferred overflow checks on the MIR (FND-MIR-DEFERRED,
//! docs/mir-design.md section 8).
//!
//! The analysis is `native/deferred.rs` on a CFG: the module documentation
//! there explains why deferring is unobservable. Here an expression tree is
//! a chain of single-assignment temporaries, so:
//! - an operation is *exact*, keeping its check, when its value reaches a
//!   switch, an element index or the counter, through the definitions of
//!   temporaries and the assignments of locals in the loop;
//! - a certified bound follows the definitions of its operands, and a leaf
//!   is an operand (a statement and a position) whose magnitude the chunk
//!   tracks.
//!
//! The transform keeps the loop as the checked loop and adds, before it, a
//! chunk frame and a copy of the loop that runs one chunk:
//!
//! ```text
//! preheader: unsuitable views? -> checked loop
//! chunk:     sticky = 0, trackers = 0, start = i, bound, lengths
//!            accesses outside? -> checked loop
//!            limit, entry magnitudes, replay snapshot
//! copy:      while i <cmp> limit { body with deferred arithmetic }
//! after:     certificate fails? -> restore snapshot -> checked loop
//!            sticky < 0? -> panic
//!            i <cmp> bound? -> chunk : exit
//! ```

use super::loops::{self, Counted, Loop, Term};
use super::*;
use crate::executable::{BytesOp, SliceOp, Target, VecOp};
use crate::int::{ArithOp, IntOp};
use std::collections::{BTreeMap, BTreeSet};

/// The start of the trace line for a loop that keeps its checks, as the
/// tree path prints it (`KUSH_TRACE_DEFERRED`).
const CHUNK_TRACE: &str = "deferred overflow: loop in";

/// The code generator's choices that decide whether deferring pays.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Options {
    /// The target multiplies 64-bit vectors natively.
    pub wide_multiply: bool,
    /// The build targets this machine's wide vectors.
    pub wide_vectors: bool,
    /// `Speed`: specialize the chunk to whole-element slices.
    pub speed: bool,
    pub trace: bool,
}

fn scalar(ty: Type) -> bool {
    matches!(
        ty,
        Type::I64 | Type::Int(_) | Type::Float(_) | Type::Char | Type::Bool | Type::Unit
    )
}
fn integer(ty: Type) -> bool {
    matches!(ty, Type::I64 | Type::Int(_))
}

/// A statement, by block and index.
type At = (BlockId, usize);

#[derive(Debug, Clone, Copy, PartialEq)]
enum Container {
    Slice(Type),
    Vec(Type),
    Bytes,
}

/// An element read or write of the loop.
#[derive(Debug, Clone, Copy)]
struct Access {
    /// The block whose terminator is the call.
    block: BlockId,
    /// The container's local (a view, or a reference to a vector or bytes,
    /// or the container itself when the call borrows it).
    receiver: LocalId,
    /// Whether the call's receiver operand borrows `receiver` (`&v`).
    borrowed: bool,
    container: Container,
    /// The builtin of the call, to derive the length call from.
    target: Target,
    /// The index is the counter plus this.
    offset: i64,
}

/// An operand occurrence: the statement using it and its position.
type Leaf = (At, usize);

/// A reduction's chain operations, and the operands that are its terms.
type Chain = (Vec<At>, Vec<Leaf>);

struct Scan {
    candidates: Vec<At>,
    exact: Vec<Operand>,
    /// (call block, receiver operand, container, index operand)
    accesses: Vec<(BlockId, Operand, Container, Target, Operand)>,
    stored: BTreeSet<LocalId>,
    loaded: BTreeSet<LocalId>,
    divides: bool,
    conditional_store: bool,
    conditional_arithmetic: bool,
    byte_reads: bool,
}

struct Analysis<'b> {
    body: &'b Body,
    lp: &'b Loop,
    idom: Vec<Option<BlockId>>,
}

impl Analysis<'_> {
    /// Whether every iteration runs the block.
    fn unconditional(&self, block: BlockId) -> bool {
        self.lp
            .latches
            .iter()
            .all(|latch| loops::dominates(&self.idom, block, *latch))
    }
    /// The definition of a temporary in the loop: a statement, or the call
    /// whose destination it is.
    fn definition(&self, local: LocalId) -> Option<Result<At, BlockId>> {
        let mut found = None;
        for block in &self.lp.blocks {
            let data = &self.body.blocks[*block];
            for (at, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(place, _) = &statement.kind;
                if place.local == local && !place.deref {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(Ok((*block, at)));
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator.kind
                && *destination == local
            {
                if found.is_some() {
                    return None;
                }
                found = Some(Err(*block));
            }
        }
        found
    }
    fn rvalue(&self, (block, at): At) -> &Rvalue {
        let StatementKind::Assign(_, rvalue) = &self.body.blocks[block].statements[at].kind;
        rvalue
    }
    fn scan(&self) -> Result<Scan, &'static str> {
        let body = self.body;
        let mut scan = Scan {
            candidates: Vec::new(),
            exact: Vec::new(),
            accesses: Vec::new(),
            stored: BTreeSet::new(),
            loaded: BTreeSet::new(),
            divides: false,
            conditional_store: false,
            conditional_arithmetic: false,
            byte_reads: false,
        };
        for block in &self.lp.blocks {
            let conditional = !self.unconditional(*block);
            let data = &body.blocks[*block];
            for (at, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(place, rvalue) = &statement.kind;
                let ty = body.locals[place.local].ty;
                if let Rvalue::Ref(source) = rvalue {
                    // A borrow of a container for a call's receiver.
                    if !body.locals[place.local].temporary || source.deref || source.field.is_some()
                    {
                        return Err("an operation with effects or ownership");
                    }
                    continue;
                }
                if let Rvalue::Use(Operand::Copy(source)) = rvalue
                    && !scalar(ty)
                    && body.locals[place.local].temporary
                    && !body.locals[source.local].temporary
                    && !source.deref
                    && source.field.is_none()
                {
                    // A copy of a view (or a reference to a container) for
                    // a call's receiver.
                    continue;
                }
                if place.deref || place.field.is_some() || !scalar(ty) {
                    return Err(if body.locals[place.local].temporary {
                        "a non-scalar value"
                    } else {
                        "assignment to a non-scalar local"
                    });
                }
                match rvalue {
                    Rvalue::Use(_) | Rvalue::Int(..) => {}
                    Rvalue::Unary(UnOp::Neg, operand) if integer(body.operand_ty(*operand)) => {
                        scan.candidates.push((*block, at));
                        scan.conditional_arithmetic |= conditional;
                    }
                    Rvalue::Unary(..) => {}
                    Rvalue::Binary(BinOp::Add | BinOp::Sub | BinOp::Mul, left, _)
                        if integer(body.operand_ty(*left)) =>
                    {
                        scan.candidates.push((*block, at));
                        scan.conditional_arithmetic |= conditional;
                    }
                    Rvalue::Binary(BinOp::Div | BinOp::Rem, ..) => scan.divides = true,
                    Rvalue::Binary(..) => {}
                    _ => return Err("an operation with effects or ownership"),
                }
            }
            match &data.terminator.kind {
                TerminatorKind::Goto(_) => {}
                TerminatorKind::Switch { value, .. } => scan.exact.push(*value),
                TerminatorKind::Call {
                    callee: Callee::Builtin { index, .. },
                    args,
                    destination,
                    ..
                } => {
                    if !scalar(body.locals[*destination].ty) {
                        return Err("a non-scalar value");
                    }
                    let target = body.builtins.0[*index];
                    #[derive(PartialEq)]
                    enum Kind {
                        Length,
                        Load,
                        Store,
                    }
                    let (kind, container) = match target {
                        Target::Slice(SliceOp::Len, element) => {
                            (Some(Kind::Length), Some(Container::Slice(element)))
                        }
                        Target::Vec(VecOp::Len, element) => {
                            (Some(Kind::Length), Some(Container::Vec(element)))
                        }
                        Target::Bytes(BytesOp::Len) => (Some(Kind::Length), Some(Container::Bytes)),
                        // Only checked reads: a proved, unchecked read
                        // (`at`) may owe its proof to a deferred operation
                        // not having overflowed.
                        Target::Slice(SliceOp::Get, element) if scalar(element) => {
                            (Some(Kind::Load), Some(Container::Slice(element)))
                        }
                        Target::Vec(VecOp::Get, element) if scalar(element) => {
                            (Some(Kind::Load), Some(Container::Vec(element)))
                        }
                        Target::Bytes(BytesOp::Get) => {
                            scan.byte_reads = true;
                            (Some(Kind::Load), Some(Container::Bytes))
                        }
                        Target::Slice(SliceOp::Set, element) if scalar(element) => {
                            (Some(Kind::Store), Some(Container::Slice(element)))
                        }
                        Target::Int(..) | Target::Float(_) => (None, None),
                        _ => return Err("a call"),
                    };
                    let Some(kind) = kind else {
                        scan.exact.extend(args.iter().copied());
                        continue;
                    };
                    let [receiver, rest @ ..] = args.as_slice() else {
                        return Err("a call");
                    };
                    let Some(local) = self.receiver(*receiver) else {
                        return Err("a container operand that is not a local");
                    };
                    match kind {
                        Kind::Store => {
                            // Only an exclusive view is known not to alias
                            // the loop's other operands.
                            if !matches!(body.locals[local].ty, Type::SliceMut(_)) {
                                return Err("a store through a shared view");
                            }
                            scan.stored.insert(local);
                            scan.conditional_store |= conditional;
                        }
                        Kind::Load => {
                            scan.loaded.insert(local);
                        }
                        Kind::Length => {}
                    }
                    // Indices keep their immediate checks; a stored value
                    // may be speculative because a panic discards it.
                    if let Some(index) = rest.first() {
                        scan.exact.push(*index);
                        if kind != Kind::Length {
                            scan.accesses.push((
                                *block,
                                *receiver,
                                container.expect("an element access has a container"),
                                target,
                                *index,
                            ));
                        }
                    }
                }
                TerminatorKind::Call { .. } => return Err("a call"),
                TerminatorKind::Drop { .. } => {
                    return Err("an operation with effects or ownership");
                }
                TerminatorKind::Return(_) | TerminatorKind::Abort => {
                    return Err("an operation with effects or ownership");
                }
                TerminatorKind::Panic { .. }
                | TerminatorKind::Resume
                | TerminatorKind::Unreachable => {}
            }
        }
        Ok(scan)
    }
    /// The local a container operand names: a local, or a borrow of one
    /// made in the loop. The loop assigns no non-scalar local, so it is the
    /// same container throughout.
    fn receiver(&self, operand: Operand) -> Option<LocalId> {
        let place = operand.place()?;
        if place.deref || place.field.is_some() {
            return None;
        }
        if !self.body.locals[place.local].temporary {
            return Some(place.local);
        }
        match self.definition(place.local)? {
            Ok(at) => match self.rvalue(at) {
                Rvalue::Ref(source) | Rvalue::Use(Operand::Copy(source))
                    if !self.body.locals[source.local].temporary =>
                {
                    Some(source.local)
                }
                _ => None,
            },
            Err(_) => None,
        }
    }
    /// `Some(c)` when the index operand of the call in `block` is the
    /// counter plus `c`, and where its value was taken: the statement, or
    /// `None` for the call itself.
    fn counter_offset(
        &self,
        block: BlockId,
        index: Operand,
        counter: LocalId,
    ) -> Option<(i64, Option<usize>)> {
        let statements = &self.body.blocks[block].statements;
        // A temporary defined in the call's block, before the call, from
        // the counter's value at that point.
        let local_value = |operand: Operand, before: usize| -> Option<usize> {
            let place = operand.place()?;
            if place.deref || place.field.is_some() {
                return None;
            }
            if place.local == counter {
                return Some(before);
            }
            if !self.body.locals[place.local].temporary {
                return None;
            }
            let (at, rvalue) =
                statements[..before]
                    .iter()
                    .enumerate()
                    .rev()
                    .find_map(|(at, statement)| {
                        let StatementKind::Assign(target, rvalue) = &statement.kind;
                        (target.local == place.local).then_some((at, rvalue))
                    })?;
            match rvalue {
                Rvalue::Use(Operand::Copy(source) | Operand::Move(source))
                    if source.local == counter && source.field.is_none() && !source.deref =>
                {
                    Some(at)
                }
                _ => None,
            }
        };
        let assigns_counter = |from: usize, to: usize| {
            statements[from..to].iter().any(|statement| {
                let StatementKind::Assign(target, _) = &statement.kind;
                target.local == counter
            })
        };
        let end = statements.len();
        // The counter itself, or a copy of it.
        if let Some(at) = local_value(index, end) {
            if assigns_counter(at, end) && at != end {
                return None;
            }
            return Some((0, (at != end).then_some(at)));
        }
        let place = index.place()?;
        if !self.body.locals[place.local].temporary || place.field.is_some() || place.deref {
            return None;
        }
        let (at, rvalue) = statements
            .iter()
            .enumerate()
            .rev()
            .find_map(|(at, statement)| {
                let StatementKind::Assign(target, rvalue) = &statement.kind;
                (target.local == place.local).then_some((at, rvalue))
            })?;
        let (subtract, base, amount) = match rvalue {
            Rvalue::Binary(op @ (BinOp::Add | BinOp::Sub), base, amount) => {
                (*op == BinOp::Sub, *base, *amount)
            }
            Rvalue::Int(IntOp::Unchecked(op @ (ArithOp::Add | ArithOp::Sub)), _, _, operands)
                if operands.len() == 2 =>
            {
                (*op == ArithOp::Sub, operands[0], operands[1])
            }
            _ => return None,
        };
        let Operand::Constant(constant, _) = amount else {
            return None;
        };
        let read = local_value(base, at)?;
        if assigns_counter(read, at) || assigns_counter(at, end) {
            return None;
        }
        let offset = if subtract {
            constant.checked_neg()?
        } else {
            constant
        };
        Some((offset, Some(read)))
    }
    /// Every statement an exact value depends on, through the definitions
    /// of temporaries and the assignments of locals in the loop.
    fn pinned(&self, roots: &[Operand]) -> BTreeSet<At> {
        let mut pinned = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut work = roots.to_vec();
        while let Some(operand) = work.pop() {
            let Some(place) = operand.place() else {
                continue;
            };
            if !seen.insert(place.local) {
                continue;
            }
            for block in &self.lp.blocks {
                let data = &self.body.blocks[*block];
                for (at, statement) in data.statements.iter().enumerate() {
                    let StatementKind::Assign(target, rvalue) = &statement.kind;
                    if target.local == place.local {
                        pinned.insert((*block, at));
                        work.extend(super::drop_flags::rvalue_operands(rvalue));
                    }
                }
                if let TerminatorKind::Call {
                    destination, args, ..
                } = &data.terminator.kind
                    && *destination == place.local
                {
                    work.extend(args.iter().copied());
                }
            }
        }
        pinned
    }
}

/// A certified operation: plain signed 64-bit `+`, `-`, `*` or negation.
fn certifiable(body: &Body, rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Binary(BinOp::Add | BinOp::Sub | BinOp::Mul, left, right) => {
            body.operand_ty(*left) == Type::I64 && body.operand_ty(*right) == Type::I64
        }
        Rvalue::Unary(UnOp::Neg, operand) => body.operand_ty(*operand) == Type::I64,
        _ => false,
    }
}

/// What the chunk certifies.
#[derive(Default)]
struct Certificate {
    modes: BTreeMap<At, DeferMode>,
    leaves: Vec<Leaf>,
    /// Whether each leaf reads a value the loop does not change.
    invariant: Vec<bool>,
    obligations: Vec<Bound>,
    /// Reduction locals, in order; their entry magnitudes follow the
    /// leaves among the certificate's words.
    accumulators: Vec<LocalId>,
    multiplies: bool,
}

struct Certify<'a, 'b> {
    analysis: &'a Analysis<'b>,
    deferred: &'a BTreeSet<At>,
    reduction_steps: BTreeSet<At>,
    assigned: BTreeSet<LocalId>,
    out: Certificate,
}

impl Certify<'_, '_> {
    fn certified(&self, at: At) -> bool {
        self.deferred.contains(&at)
            && certifiable(self.analysis.body, self.analysis.rvalue(at))
            && !self.reduction_steps.contains(&at)
    }
    fn leaf(&mut self, leaf: Leaf, operand: Operand) -> Bound {
        // An operation's bound is taken again as a reduction's term; its
        // leaves are the same words.
        if let Some(index) = self.out.leaves.iter().position(|known| *known == leaf) {
            return Bound::Word(index);
        }
        let body = self.analysis.body;
        let invariant = operand.place().is_some_and(|place| {
            let mut local = place.local;
            if body.locals[local].temporary
                && let Some(Ok(at)) = self.analysis.definition(local)
                && let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) =
                    self.analysis.rvalue(at)
            {
                local = source.local;
            }
            !body.locals[local].temporary && !self.assigned.contains(&local)
        });
        let index = self.out.leaves.len();
        self.out.leaves.push(leaf);
        self.out.invariant.push(invariant);
        Bound::Word(index)
    }
    /// The bound of the operand at position `position` of the statement
    /// at `at`.
    fn bound(&mut self, at: At, position: usize, nested: &mut BTreeSet<At>) -> Bound {
        let body = self.analysis.body;
        let operand = super::drop_flags::rvalue_operands(self.analysis.rvalue(at))[position];
        if let Operand::Constant(value, _) = operand {
            // The least `u` with `|value| <= 2^u`.
            let magnitude = value.unsigned_abs();
            return Bound::Constant(match magnitude {
                0 => 0,
                _ => u64::BITS - (magnitude - 1).leading_zeros(),
            });
        }
        let place = operand.place().expect("a non-constant operand");
        if body.locals[place.local].temporary && place.field.is_none() && !place.deref {
            match self.analysis.definition(place.local) {
                // A value whose range its type already bounds.
                Some(Err(call)) => {
                    if let TerminatorKind::Call {
                        callee: Callee::Builtin { index, .. },
                        ..
                    } = &body.blocks[call].terminator.kind
                        && matches!(body.builtins.0[*index], Target::Bytes(BytesOp::Get))
                    {
                        return Bound::Constant(8);
                    }
                    if let TerminatorKind::Call {
                        callee: Callee::Builtin { index, .. },
                        ..
                    } = &body.blocks[call].terminator.kind
                        && let Target::Int(IntOp::Convert, source, _) = body.builtins.0[*index]
                        && source.bits() < 64
                    {
                        let bits = source.bits();
                        return Bound::Constant(if source.signed() { bits - 1 } else { bits });
                    }
                }
                Some(Ok(definition)) => {
                    if let Rvalue::Int(IntOp::Convert, source, _, _) =
                        self.analysis.rvalue(definition)
                        && source.bits() < 64
                    {
                        let bits = source.bits();
                        return Bound::Constant(if source.signed() { bits - 1 } else { bits });
                    }
                    if self.certified(definition) {
                        nested.insert(definition);
                        return self.operation(definition, nested);
                    }
                }
                None => {}
            }
        }
        self.leaf((at, position), operand)
    }
    /// The bound of a certified operation.
    fn operation(&mut self, at: At, nested: &mut BTreeSet<At>) -> Bound {
        match self.analysis.rvalue(at).clone() {
            Rvalue::Binary(op, _, _) => {
                let left = Box::new(self.bound(at, 0, nested));
                let right = Box::new(self.bound(at, 1, nested));
                if op == BinOp::Mul {
                    if !matches!(*left, Bound::Constant(_)) && !matches!(*right, Bound::Constant(_))
                    {
                        self.out.multiplies = true;
                    }
                    Bound::Product(left, right)
                } else {
                    Bound::Sum(left, right)
                }
            }
            Rvalue::Unary(..) => self.bound(at, 0, nested),
            _ => unreachable!("certified operations are unary or binary"),
        }
    }
}

/// Reductions: every assignment of the local is `acc = acc +/- e` (or a
/// chain `acc = acc + a - b + c`, or `acc = e + acc`), and the local is read
/// nowhere else in the loop. Returns, per local, the chain operations and
/// the statements and positions of their terms.
fn reductions(analysis: &Analysis<'_>, deferred: &BTreeSet<At>) -> BTreeMap<LocalId, Chain> {
    let body = analysis.body;
    let reducing = |at: At| {
        matches!(
            analysis.rvalue(at),
            Rvalue::Binary(BinOp::Add | BinOp::Sub, ..)
        ) && certifiable(body, analysis.rvalue(at))
            && deferred.contains(&at)
    };
    // Whether an operand is the local's value (directly or through a copy).
    let reads = |operand: Operand, local: LocalId| -> bool {
        let Some(place) = operand.place() else {
            return false;
        };
        if place.local == local {
            return true;
        }
        body.locals[place.local].temporary
            && matches!(analysis.definition(place.local), Some(Ok(at))
                if matches!(analysis.rvalue(at),
                    Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) if source.local == local))
    };
    // Whether an operand's value depends on the local, in the loop.
    let depends = |operand: Operand, local: LocalId| -> bool {
        let mut work = vec![operand];
        let mut seen = BTreeSet::new();
        while let Some(operand) = work.pop() {
            let Some(place) = operand.place() else {
                continue;
            };
            if place.local == local {
                return true;
            }
            if !body.locals[place.local].temporary || !seen.insert(place.local) {
                continue;
            }
            match analysis.definition(place.local) {
                Some(Ok(at)) => {
                    work.extend(super::drop_flags::rvalue_operands(analysis.rvalue(at)))
                }
                Some(Err(call)) => {
                    if let TerminatorKind::Call { args, .. } = &body.blocks[call].terminator.kind {
                        work.extend(args.iter().copied());
                    }
                }
                None => return true,
            }
        }
        false
    };
    // The chain whose leftmost operand is the local, ending at `at`.
    #[allow(clippy::too_many_arguments)]
    fn chain(
        analysis: &Analysis<'_>,
        at: At,
        local: LocalId,
        reducing: &dyn Fn(At) -> bool,
        reads: &dyn Fn(Operand, LocalId) -> bool,
        depends: &dyn Fn(Operand, LocalId) -> bool,
        operations: &mut Vec<At>,
        terms: &mut Vec<(At, usize)>,
    ) -> bool {
        let Rvalue::Binary(_, left, right) = analysis.rvalue(at) else {
            return false;
        };
        if !reducing(at) || depends(*right, local) {
            return false;
        }
        if !reads(*left, local) {
            let Some(place) = left.place() else {
                return false;
            };
            let Some(Ok(inner)) = analysis.definition(place.local) else {
                return false;
            };
            if !analysis.body.locals[place.local].temporary
                || !chain(
                    analysis, inner, local, reducing, reads, depends, operations, terms,
                )
            {
                return false;
            }
        }
        operations.push(at);
        terms.push((at, 1));
        true
    }
    // Per local: how many updates are reductions, and their chains.
    let mut steps: BTreeMap<LocalId, (usize, Chain)> = BTreeMap::new();
    let mut updates: BTreeMap<LocalId, usize> = BTreeMap::new();
    let mut reads_of: BTreeMap<LocalId, usize> = BTreeMap::new();
    for block in &analysis.lp.blocks {
        let data = &body.blocks[*block];
        for statement in &data.statements {
            let StatementKind::Assign(place, rvalue) = &statement.kind;
            if !body.locals[place.local].temporary {
                *updates.entry(place.local).or_default() += 1;
            }
            for operand in super::drop_flags::rvalue_operands(rvalue) {
                if let Some(read) = operand.place() {
                    *reads_of.entry(read.local).or_default() += 1;
                }
            }
        }
        if let TerminatorKind::Call { args, .. } = &data.terminator.kind {
            for operand in args {
                if let Some(read) = operand.place() {
                    *reads_of.entry(read.local).or_default() += 1;
                }
            }
        }
        if let TerminatorKind::Switch { value, .. } = &data.terminator.kind
            && let Some(read) = value.place()
        {
            *reads_of.entry(read.local).or_default() += 1;
        }
    }
    let taken = loops::address_taken(body);
    for block in &analysis.lp.blocks {
        for statement in &body.blocks[*block].statements {
            let StatementKind::Assign(place, rvalue) = &statement.kind;
            let local = place.local;
            if body.locals[local].temporary
                || body.locals[local].ty != Type::I64
                || taken.contains(&local)
                || place.field.is_some()
                || place.deref
            {
                continue;
            }
            let Rvalue::Use(Operand::Move(value) | Operand::Copy(value)) = rvalue else {
                continue;
            };
            let Some(Ok(definition)) = analysis.definition(value.local) else {
                continue;
            };
            let mut operations = Vec::new();
            let mut terms = Vec::new();
            let found = chain(
                analysis,
                definition,
                local,
                &reducing,
                &reads,
                &depends,
                &mut operations,
                &mut terms,
            ) || matches!(analysis.rvalue(definition), Rvalue::Binary(BinOp::Add, left, right)
            if reducing(definition)
                && reads(*right, local)
                && !depends(*left, local)
                && {
                    operations.push(definition);
                    terms.push((definition, 0));
                    true
                });
            if found {
                let entry = steps.entry(local).or_default();
                entry.0 += 1;
                entry.1.0.extend(operations);
                entry.1.1.extend(terms);
            }
        }
    }
    // Each update reads the local once, through a copy into a temporary.
    steps
        .into_iter()
        .filter(|(local, (count, ..))| {
            updates.get(local).copied().unwrap_or(0) == *count
                && reads_of.get(local).copied().unwrap_or(0) == *count
        })
        .map(|(local, (_, chain))| (local, chain))
        .collect()
}

/// Everything the transform needs for one loop.
struct Plan {
    counted: Counted,
    modes: BTreeMap<At, DeferMode>,
    leaves: Vec<Leaf>,
    obligations: Vec<Bound>,
    accumulators: Vec<LocalId>,
    replay: Vec<LocalId>,
    disjoint: Vec<(LocalId, LocalId)>,
    layouts: Vec<(LocalId, i64)>,
    accesses: Vec<Access>,
}

fn plan(
    program: &Executable,
    body: &Body,
    lp: &Loop,
    all: &[Loop],
    options: Options,
) -> Result<Plan, String> {
    if !loops::innermost(lp, all) {
        return Err("a nested loop".into());
    }
    let analysis = Analysis {
        body,
        lp,
        idom: loops::dominators(body),
    };
    let scan = analysis.scan()?;
    // Deferring pays only where LLVM then vectorizes the loop profitably
    // (see `native/deferred.rs`).
    let test = loops::test(body, lp);
    let breaks = lp.exits(body).into_iter().any(|(from, to)| {
        test.as_ref()
            .is_none_or(|test| from != *test.condition.last().unwrap() || to != test.exit)
    });
    if breaks {
        return Err("an early exit (`break`), which keeps it from vectorizing".into());
    }
    if scan.divides {
        return Err("a division, which does not vectorize".into());
    }
    if !options.wide_vectors {
        let reason = if scan.conditional_store {
            Some("a store under a condition")
        } else if scan.conditional_arithmetic {
            Some("arithmetic under a condition")
        } else if scan.byte_reads {
            Some("byte-buffer reads")
        } else {
            None
        };
        if let Some(reason) = reason {
            return Err(format!(
                "{reason}, which only pays with `--target-cpu native`"
            ));
        }
    }
    let Some(counted) = loops::counted(body, lp) else {
        let changes = test.is_some_and(|test| matches!(test.left, Term::Local(_)));
        return Err(if changes {
            "its bound or counter changes inside the loop"
        } else {
            "it is not a counted loop"
        }
        .into());
    };
    // Every access follows the counter; one after the update sees it a
    // step on.
    let moved = match counted.comparison {
        BinOp::Lt | BinOp::Le => counted.step,
        _ => -counted.step,
    };
    let (update_block, update_at) = counted.update;
    let mut accesses = Vec::new();
    for (block, receiver, container, target, index) in &scan.accesses {
        let Some((offset, read)) = analysis.counter_offset(*block, *index, counted.counter) else {
            return Err("an index that does not follow the counter".into());
        };
        let after = if *block == update_block {
            read.is_none_or(|read| read > update_at)
        } else {
            loops::dominates(&analysis.idom, update_block, *block)
        };
        let offset = if after {
            offset
                .checked_add(moved)
                .ok_or("an index too far from the counter")?
        } else {
            offset
        };
        let local = analysis
            .receiver(*receiver)
            .expect("checked receiver operand");
        accesses.push(Access {
            block: *block,
            receiver: local,
            borrowed: receiver.place().is_some_and(|place| {
                place.local != local
                    && matches!(analysis.definition(place.local),
                        Some(Ok(at)) if matches!(analysis.rvalue(at), Rvalue::Ref(_)))
            }),
            container: *container,
            target: *target,
            offset,
        });
    }
    let mut exact = scan.exact.clone();
    exact.push(Operand::Copy(Place::local(counted.counter)));
    let pinned = analysis.pinned(&exact);
    let deferred = scan
        .candidates
        .iter()
        .copied()
        .filter(|at| !pinned.contains(at))
        .collect::<BTreeSet<_>>();
    if deferred.is_empty() {
        return Err("no checked arithmetic can be deferred".into());
    }
    let mut modes = deferred
        .iter()
        .map(|at| (*at, DeferMode::Exact))
        .collect::<BTreeMap<_, _>>();
    // A replay must observe the memory the first attempt observed: nothing
    // the loop reads may be something it wrote.
    let view =
        |local: &LocalId| matches!(body.locals[*local].ty, Type::Slice(_) | Type::SliceMut(_));
    let checkable = scan.stored.is_empty() || scan.loaded.iter().all(view);
    let assigned = loops::assigned(body, &lp.blocks);
    let mut certificate = Certificate::default();
    if scan.stored.is_disjoint(&scan.loaded) && checkable {
        let steps = reductions(&analysis, &deferred);
        let mut certify = Certify {
            analysis: &analysis,
            deferred: &deferred,
            reduction_steps: steps
                .values()
                .flat_map(|(operations, _)| operations.iter().copied())
                .collect(),
            assigned: assigned.clone(),
            out: Certificate::default(),
        };
        // Operations that are operands of another certified operation are
        // covered by their parent: bounds only grow towards the root.
        let mut nested = BTreeSet::new();
        let mut roots = Vec::new();
        for at in &scan.candidates {
            if certify.certified(*at) {
                let mut inner = BTreeSet::new();
                let result = certify.operation(*at, &mut inner);
                inner.remove(at);
                nested.extend(inner);
                roots.push((*at, result));
                certify.out.modes.insert(*at, DeferMode::Certified);
            }
        }
        for (at, result) in roots {
            if !nested.contains(&at) {
                certify.out.obligations.push(result);
            }
        }
        let mut reductions = Vec::new();
        for (local, (operations, terms)) in &steps {
            let operands = terms
                .iter()
                .map(|(at, position)| certify.bound(*at, *position, &mut BTreeSet::new()))
                .collect::<Vec<_>>();
            reductions.push((*local, operands));
            for at in operations {
                certify.out.modes.insert(*at, DeferMode::Accumulate);
            }
        }
        // Entry magnitudes come after every leaf among the words.
        let leaves = certify.out.leaves.len();
        for (index, (local, operands)) in reductions.into_iter().enumerate() {
            certify.out.obligations.push(Bound::Accumulated {
                entry: leaves + index,
                operands,
            });
            certify.out.accumulators.push(local);
        }
        certificate = certify.out;
        let varying = certificate
            .invariant
            .iter()
            .filter(|invariant| !**invariant)
            .count();
        if certificate.multiplies && varying >= 2 && !options.wide_multiply {
            return Err("tracking its operands would cost more than the checks".into());
        }
        modes.extend(certificate.modes.iter().map(|(at, mode)| (*at, *mode)));
    }
    let mut disjoint = Vec::new();
    let mut replay = Vec::new();
    if !certificate.obligations.is_empty() {
        for stored in &scan.stored {
            for loaded in &scan.loaded {
                disjoint.push((*stored, *loaded));
            }
        }
        replay = assigned
            .iter()
            .copied()
            .filter(|local| !body.locals[*local].temporary)
            .collect();
    }
    // The chunk is specialized to every slice it touches holding whole
    // consecutive elements; nothing else would vectorize.
    let mut layouts = BTreeMap::new();
    if options.speed {
        if let Term::Length(Target::Slice(SliceOp::Len, element), view) = &counted.bound {
            layouts.insert(*view, (program.width(*element) * 8) as i64);
        }
        for access in &accesses {
            if let Container::Slice(element) = access.container
                && !access.borrowed
                && view(&access.receiver)
            {
                layouts.insert(access.receiver, (program.width(element) * 8) as i64);
            }
        }
    }
    Ok(Plan {
        counted,
        modes,
        leaves: certificate.leaves,
        obligations: certificate.obligations,
        accumulators: certificate.accumulators,
        replay,
        disjoint,
        layouts: layouts.into_iter().collect(),
        accesses,
    })
}

/// Emits straight-line MIR into new blocks.
struct Emitter<'b> {
    body: &'b mut Body,
    current: BlockId,
    span: Span,
    /// Where calls and panics unwind.
    unwind: Option<BlockId>,
}

impl Emitter<'_> {
    fn new_block(&mut self) -> BlockId {
        self.body.blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator {
                kind: TerminatorKind::Unreachable,
                span: self.span,
            },
            unwind: self.unwind,
        });
        self.body.blocks.len() - 1
    }
    fn temp(&mut self, ty: Type) -> LocalId {
        self.body.locals.push(LocalDecl {
            ty,
            mutable: true,
            temporary: true,
        });
        self.body.locals.len() - 1
    }
    fn assign(&mut self, place: Place, rvalue: Rvalue) {
        let span = self.span;
        self.body.blocks[self.current].statements.push(Statement {
            kind: StatementKind::Assign(place, rvalue),
            span,
        });
    }
    fn value(&mut self, ty: Type, rvalue: Rvalue) -> Operand {
        let local = self.temp(ty);
        self.assign(Place::local(local), rvalue);
        Operand::Copy(Place::local(local))
    }
    fn terminate(&mut self, kind: TerminatorKind) {
        self.body.blocks[self.current].terminator.kind = kind;
    }
    /// A call to a builtin; the emitter continues after it.
    fn call(&mut self, target: Target, args: Vec<Operand>, ty: Type) -> Operand {
        let index = self.body.builtins.0.len();
        self.body.builtins.0.push(target);
        let destination = self.temp(ty);
        let next = self.new_block();
        self.terminate(TerminatorKind::Call {
            callee: Callee::Builtin {
                index,
                hint: CallHint::None,
            },
            args,
            destination,
            next,
            unwind: self.unwind,
        });
        self.current = next;
        Operand::Copy(Place::local(destination))
    }
    /// The value of a loop bound's term, checked as the condition checks it.
    fn term(&mut self, term: &Term, ty: Type) -> Operand {
        match term {
            Term::Constant(value) => Operand::Constant(*value, ty),
            Term::Local(local) => Operand::Copy(Place::local(*local)),
            Term::Length(target, local) => {
                let receiver = Operand::Copy(Place::local(*local));
                self.call(*target, vec![receiver], Type::I64)
            }
            Term::Binary(op, left, right) => {
                let left = self.term(left, ty);
                let right = self.term(right, ty);
                self.value(ty, Rvalue::Binary(*op, left, right))
            }
        }
    }
    /// A container's length, as a call on its receiver.
    fn length(&mut self, access: &Access) -> Operand {
        let receiver = if access.borrowed {
            // Borrow the container again, as the loop's call does.
            let borrow_ty = self.borrow_type(access);
            self.value(borrow_ty, Rvalue::Ref(Place::local(access.receiver)))
        } else {
            Operand::Copy(Place::local(access.receiver))
        };
        let target = match access.target {
            Target::Slice(_, element) => Target::Slice(SliceOp::Len, element),
            Target::Vec(_, element) => Target::Vec(VecOp::Len, element),
            _ => Target::Bytes(BytesOp::Len),
        };
        self.call(target, vec![receiver], Type::I64)
    }
    /// The type of the loop's borrow of an access's container.
    fn borrow_type(&self, access: &Access) -> Type {
        let TerminatorKind::Call { args, .. } = &self.body.blocks[access.block].terminator.kind
        else {
            unreachable!("an access is a call");
        };
        self.body.operand_ty(args[0])
    }
}

/// Defer the overflow checks of every loop of `body` the analysis accepts.
/// Returns the headers of the deferred loops (now the checked loops).
pub(crate) fn defer(program: &Executable, body: &mut Body, options: Options) -> BTreeSet<BlockId> {
    let all = loops::loops(body);
    let mut deferred = BTreeSet::new();
    let mut plans = Vec::new();
    for lp in &all {
        match plan(program, body, lp, &all, options) {
            Ok(plan) => plans.push((lp.clone(), plan)),
            Err(reason) => {
                if options.trace {
                    eprintln!(
                        "{CHUNK_TRACE} {} keeps immediate checks: {reason}",
                        body.name
                    );
                }
            }
        }
    }
    for (lp, plan) in plans {
        transform(body, &lp, plan);
        deferred.insert(lp.header);
    }
    deferred
}

fn transform(body: &mut Body, lp: &Loop, plan: Plan) {
    let counted = &plan.counted;
    let counter = counted.counter;
    let counter_ty = body.locals[counter].ty;
    let unsigned = counter_ty.int_kind().is_some_and(|kind| !kind.signed());
    let entry = loops::preheader(body, lp);
    let span = body.blocks[lp.header].terminator.span;
    // Calls in the frame unwind where the loop's calls do.
    let unwind = lp
        .blocks
        .iter()
        .find_map(|block| match &body.blocks[*block].terminator.kind {
            TerminatorKind::Call { unwind, .. } => Some(*unwind),
            _ => None,
        })
        .unwrap_or(body.blocks[lp.header].unwind);
    let copies = loops::clone_loop(body, lp);
    let mut emit = Emitter {
        body,
        current: entry,
        span,
        unwind,
    };
    let chunk = emit.new_block();
    // Views that overlap or have another layout rule the chunk out.
    let mut views = Vec::new();
    let index_of = |local: LocalId, views: &mut Vec<LocalId>| match views
        .iter()
        .position(|view| *view == local)
    {
        Some(at) => at,
        None => {
            views.push(local);
            views.len() - 1
        }
    };
    let overlaps = plan
        .disjoint
        .iter()
        .map(|(stored, loaded)| (index_of(*stored, &mut views), index_of(*loaded, &mut views)))
        .collect::<Vec<_>>();
    let layouts = plan
        .layouts
        .iter()
        .map(|(view, stride)| (index_of(*view, &mut views), *stride))
        .collect::<Vec<_>>();
    if views.is_empty() {
        emit.terminate(TerminatorKind::Goto(chunk));
    } else {
        let operands = views
            .iter()
            .map(|view| Operand::Copy(Place::local(*view)))
            .collect();
        let unsuitable = emit.value(
            Type::Bool,
            Rvalue::Loop(LoopOp::Unsuitable { overlaps, layouts }, operands),
        );
        emit.terminate(TerminatorKind::Switch {
            value: unsuitable,
            targets: vec![(0, chunk)],
            otherwise: lp.header,
        });
    }
    // The chunk's frame.
    emit.current = chunk;
    let sticky = emit.temp(Type::I64);
    emit.assign(
        Place::local(sticky),
        Rvalue::Use(Operand::Constant(0, Type::I64)),
    );
    let trackers = plan
        .leaves
        .iter()
        .map(|_| {
            let tracker = emit.temp(Type::I64);
            emit.assign(
                Place::local(tracker),
                Rvalue::Use(Operand::Constant(0, Type::I64)),
            );
            tracker
        })
        .collect::<Vec<_>>();
    let start = emit.value(
        counter_ty,
        Rvalue::Use(Operand::Copy(Place::local(counter))),
    );
    let bound = emit.term(&counted.bound, counter_ty);
    let bound = emit.value(counter_ty, Rvalue::Use(bound));
    if !plan.accesses.is_empty() {
        let mut ranges: Vec<(LocalId, &Access, i64, i64)> = Vec::new();
        for access in &plan.accesses {
            match ranges
                .iter_mut()
                .find(|(receiver, ..)| *receiver == access.receiver)
            {
                Some((_, _, least, most)) => {
                    *least = (*least).min(access.offset);
                    *most = (*most).max(access.offset);
                }
                None => ranges.push((access.receiver, access, access.offset, access.offset)),
            }
        }
        let mut operands = vec![start, bound];
        let mut extents = Vec::new();
        for (_, access, least, most) in &ranges {
            operands.push(emit.length(access));
            extents.push((*least, *most));
        }
        let outside = emit.value(
            Type::Bool,
            Rvalue::Loop(
                LoopOp::Outside {
                    comparison: counted.comparison,
                    ranges: extents,
                },
                operands,
            ),
        );
        let proved = emit.new_block();
        emit.terminate(TerminatorKind::Switch {
            value: outside,
            targets: vec![(0, proved)],
            otherwise: lp.header,
        });
        emit.current = proved;
    }
    let limit = emit.value(
        counter_ty,
        Rvalue::Loop(
            LoopOp::ChunkLimit {
                comparison: counted.comparison,
                unsigned,
                step: counted.step,
            },
            vec![start, bound],
        ),
    );
    let entries = plan
        .accumulators
        .iter()
        .map(|local| {
            emit.value(
                Type::I64,
                Rvalue::Loop(LoopOp::Magnitude, vec![Operand::Copy(Place::local(*local))]),
            )
        })
        .collect::<Vec<_>>();
    let snapshot = plan
        .replay
        .iter()
        .map(|local| {
            let ty = emit.body.locals[*local].ty;
            (
                *local,
                emit.value(ty, Rvalue::Use(Operand::Copy(Place::local(*local)))),
            )
        })
        .collect::<Vec<_>>();
    for (view, stride) in &plan.layouts {
        for (offset, value) in [(2, *stride), (3, 0)] {
            emit.assign(
                Place::field(*view, offset, Type::I64),
                Rvalue::Use(Operand::Constant(value, Type::I64)),
            );
        }
    }
    emit.terminate(TerminatorKind::Goto(copies[&lp.header]));
    // After the chunk.
    let after = emit.new_block();
    emit.current = after;
    let end = emit.value(
        counter_ty,
        Rvalue::Use(Operand::Copy(Place::local(counter))),
    );
    if !plan.obligations.is_empty() {
        let accumulating = plan
            .modes
            .values()
            .filter(|mode| **mode == DeferMode::Accumulate)
            .count() as i64;
        let mut operands = vec![start, end];
        operands.extend(
            trackers
                .iter()
                .map(|tracker| Operand::Copy(Place::local(*tracker))),
        );
        operands.extend(entries.iter().copied());
        let certified = emit.value(
            Type::Bool,
            Rvalue::Loop(
                LoopOp::Certificate {
                    obligations: plan.obligations.clone(),
                    comparison: counted.comparison,
                    step: counted.step,
                    accumulating,
                },
                operands,
            ),
        );
        // Without it nothing is known: go back to this chunk's entry state
        // and run the rest of the loop with ordinary checks.
        let replay = emit.new_block();
        let holds = emit.new_block();
        emit.terminate(TerminatorKind::Switch {
            value: certified,
            targets: vec![(0, replay)],
            otherwise: holds,
        });
        emit.current = replay;
        for (local, value) in &snapshot {
            emit.assign(Place::local(*local), Rvalue::Use(*value));
        }
        emit.terminate(TerminatorKind::Goto(lp.header));
        emit.current = holds;
    }
    let overflowed = emit.value(
        Type::Bool,
        Rvalue::Binary(
            BinOp::Lt,
            Operand::Copy(Place::local(sticky)),
            Operand::Constant(0, Type::I64),
        ),
    );
    let panic = emit.new_block();
    let report = emit.new_block();
    emit.terminate(TerminatorKind::Switch {
        value: overflowed,
        targets: vec![(0, report)],
        otherwise: panic,
    });
    emit.body.blocks[panic].terminator.kind = TerminatorKind::Panic { unwind };
    emit.current = report;
    // The chunk stopped at its limit or at the loop's own end.
    let more = emit.value(Type::Bool, Rvalue::Binary(counted.comparison, end, bound));
    emit.terminate(TerminatorKind::Switch {
        value: more,
        targets: vec![(0, counted.exit)],
        otherwise: chunk,
    });
    // The copy runs one chunk: its header tests the limit directly.
    let body = emit.body;
    let header = copies[&lp.header];
    let tested = body.locals.len();
    body.locals.push(LocalDecl {
        ty: Type::Bool,
        mutable: false,
        temporary: true,
    });
    let test = Rvalue::Binary(
        counted.comparison,
        Operand::Copy(Place::local(counter)),
        Operand::Copy(Place::local(limit.place().expect("a temporary").local)),
    );
    body.blocks[header].statements = vec![Statement {
        kind: StatementKind::Assign(Place::local(tested), test),
        span,
    }];
    body.blocks[header].terminator.kind = TerminatorKind::Switch {
        value: Operand::Move(Place::local(tested)),
        targets: vec![(0, after)],
        otherwise: copies[&counted.body],
    };
    // Deferred arithmetic and leaf tracking in the copy.
    let mut tracked: BTreeMap<At, Vec<(usize, LocalId)>> = BTreeMap::new();
    for ((at, position), tracker) in plan.leaves.iter().zip(&trackers) {
        tracked.entry(*at).or_default().push((*position, *tracker));
    }
    let blocks = plan
        .modes
        .keys()
        .map(|(block, _)| *block)
        .chain(tracked.keys().map(|(block, _)| *block))
        .collect::<BTreeSet<_>>();
    for block in blocks {
        let copy = copies[&block];
        let statements = std::mem::take(&mut body.blocks[copy].statements);
        let mut rewritten = Vec::with_capacity(statements.len());
        for (at, mut statement) in statements.into_iter().enumerate() {
            if let Some(leaves) = tracked.get(&(block, at)) {
                let StatementKind::Assign(_, rvalue) = &statement.kind;
                let operands = super::drop_flags::rvalue_operands(rvalue);
                for (position, tracker) in leaves {
                    let read = match operands[*position] {
                        Operand::Move(place) => Operand::Copy(place),
                        other => other,
                    };
                    let word = body.locals.len();
                    body.locals.push(LocalDecl {
                        ty: Type::I64,
                        mutable: false,
                        temporary: true,
                    });
                    rewritten.push(Statement {
                        kind: StatementKind::Assign(
                            Place::local(word),
                            Rvalue::Loop(LoopOp::Magnitude, vec![read]),
                        ),
                        span: statement.span,
                    });
                    rewritten.push(Statement {
                        kind: StatementKind::Assign(
                            Place::local(*tracker),
                            Rvalue::Binary(
                                BinOp::BitOr,
                                Operand::Copy(Place::local(*tracker)),
                                Operand::Copy(Place::local(word)),
                            ),
                        ),
                        span: statement.span,
                    });
                }
            }
            if let Some(mode) = plan.modes.get(&(block, at)) {
                let StatementKind::Assign(_, rvalue) = &mut statement.kind;
                let deferral = |op| Deferral {
                    mode: *mode,
                    sticky,
                    op,
                };
                *rvalue = match rvalue.clone() {
                    Rvalue::Binary(op, left, right) => {
                        Rvalue::Deferred(deferral(Some(op)), vec![left, right])
                    }
                    Rvalue::Unary(_, operand) => Rvalue::Deferred(deferral(None), vec![operand]),
                    other => other,
                };
            }
            rewritten.push(statement);
        }
        body.blocks[copy].statements = rewritten;
    }
    // The chunk proved every access in range.
    for access in &plan.accesses {
        if let TerminatorKind::Call {
            callee: Callee::Builtin { hint, .. },
            ..
        } = &mut body.blocks[copies[&access.block]].terminator.kind
        {
            *hint = CallHint::Proved;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const OPTIONS: Options = Options {
        wide_multiply: true,
        wide_vectors: false,
        speed: true,
        trace: false,
    };

    fn deferred(source: &str, name: &str, options: Options) -> (Body, usize) {
        let program = crate::executable::check(source).expect("the test program checks");
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some(name))
            .expect("the function");
        let mut body = build(&program, index).expect("the function builds");
        let count = defer(&program, &mut body, options).len();
        verify(&program, &body).expect("the deferred body verifies");
        let printed = text::print(&body);
        assert_eq!(text::parse(&printed).unwrap(), body, "{printed}");
        (body, count)
    }

    #[test]
    fn a_reduction_over_a_view_gets_a_certified_chunk() {
        let (body, count) = deferred(
            "fn sum(xs: &[i64]) -> i64 {
                let mut i = 0;
                let mut total = 0;
                while i < xs.len() { total = total + xs[i] * 3; i = i + 1; }
                total
            }
            fn main() -> Unit ! {io} { print_i64(0); }",
            "sum",
            OPTIONS,
        );
        assert_eq!(count, 1);
        let printed = text::print(&body);
        for expected in [
            "Accumulate",
            "Certificate",
            "ChunkLimit",
            "Outside",
            " proved(",
        ] {
            assert!(printed.contains(expected), "{expected}\n{printed}");
        }
    }

    #[test]
    fn loops_that_do_not_pay_keep_their_checks() {
        for shape in [
            // A division.
            "while i < xs.len() { total = total + xs[i] / 3; i = i + 1; }",
            // An early exit.
            "while i < xs.len() { if xs[i] < 0 { break; } total = total + xs[i]; i = i + 1; }",
            // A gather.
            "while i < xs.len() { total = total + xs[xs[i] % 4]; i = i + 1; }",
            // Nothing to defer: the value steers the loop.
            "while i < xs.len() { i = i + 1; }",
        ] {
            let source = format!(
                "fn sum(xs: &[i64]) -> i64 {{
                    let mut i = 0;
                    let mut total = 0;
                    {shape}
                    total
                }}
                fn main() -> Unit ! {{io}} {{ print_i64(0); }}"
            );
            let (_, count) = deferred(&source, "sum", OPTIONS);
            assert_eq!(count, 0, "{shape}");
        }
    }
}
