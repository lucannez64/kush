//! Loop structure of a body (FND-MIR-LOOPS, docs/mir-design.md section 8).
//!
//! The loop passes share this: dominators over the normal edges, the
//! natural loops of the back edges, preheaders, the recognition of counted
//! loops, and loop versioning. Unwind edges are not part of a loop: a
//! cleanup block ends in `resume` and never returns to the header.

use super::*;
use crate::executable::Target;
use std::collections::{BTreeMap, BTreeSet};

/// The targets of a terminator's normal edges.
pub(crate) fn successors(kind: &TerminatorKind) -> Vec<BlockId> {
    match kind {
        TerminatorKind::Goto(target) => vec![*target],
        TerminatorKind::Switch {
            targets, otherwise, ..
        } => targets
            .iter()
            .map(|(_, target)| *target)
            .chain([*otherwise])
            .collect(),
        TerminatorKind::Call { next, .. } | TerminatorKind::Drop { next, .. } => vec![*next],
        TerminatorKind::Return(_)
        | TerminatorKind::Panic { .. }
        | TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => Vec::new(),
    }
}

/// Redirect the terminator's normal edges to `from` towards `to`.
fn retarget(kind: &mut TerminatorKind, from: BlockId, to: BlockId) {
    let edit = |target: &mut BlockId| {
        if *target == from {
            *target = to;
        }
    };
    match kind {
        TerminatorKind::Goto(target) => edit(target),
        TerminatorKind::Switch {
            targets, otherwise, ..
        } => {
            for (_, target) in targets {
                edit(target);
            }
            edit(otherwise);
        }
        TerminatorKind::Call { next, .. } | TerminatorKind::Drop { next, .. } => edit(next),
        TerminatorKind::Return(_)
        | TerminatorKind::Panic { .. }
        | TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => {}
    }
}

/// Each block's predecessors along normal edges.
pub(crate) fn predecessors(body: &Body) -> Vec<Vec<BlockId>> {
    let mut predecessors = vec![Vec::new(); body.blocks.len()];
    for (block, data) in body.blocks.iter().enumerate() {
        for target in successors(&data.terminator.kind) {
            if !predecessors[target].contains(&block) {
                predecessors[target].push(block);
            }
        }
    }
    predecessors
}

/// The blocks reachable from the entry along normal edges, in reverse
/// postorder.
pub(crate) fn reverse_postorder(body: &Body) -> Vec<BlockId> {
    let mut visited = vec![false; body.blocks.len()];
    let mut order = Vec::new();
    // An explicit stack of (block, next successor to visit).
    let mut stack = vec![(0, 0)];
    visited[0] = true;
    while let Some((block, next)) = stack.pop() {
        let targets = successors(&body.blocks[block].terminator.kind);
        if let Some(&target) = targets.get(next) {
            stack.push((block, next + 1));
            if !visited[target] {
                visited[target] = true;
                stack.push((target, 0));
            }
        } else {
            order.push(block);
        }
    }
    order.reverse();
    order
}

/// Immediate dominators along normal edges (Cooper, Harvey and Kennedy):
/// the entry is its own, and a block the entry does not reach has none.
pub(crate) fn dominators(body: &Body) -> Vec<Option<BlockId>> {
    let order = reverse_postorder(body);
    let mut position = vec![usize::MAX; body.blocks.len()];
    for (index, block) in order.iter().enumerate() {
        position[*block] = index;
    }
    let predecessors = predecessors(body);
    let mut idom = vec![None; body.blocks.len()];
    idom[0] = Some(0);
    let intersect = |idom: &[Option<BlockId>], mut a: BlockId, mut b: BlockId| {
        while a != b {
            while position[a] > position[b] {
                a = idom[a].expect("a processed block");
            }
            while position[b] > position[a] {
                b = idom[b].expect("a processed block");
            }
        }
        a
    };
    let mut changed = true;
    while changed {
        changed = false;
        for &block in order.iter().skip(1) {
            let mut new = None;
            for &predecessor in &predecessors[block] {
                if idom[predecessor].is_none() {
                    continue;
                }
                new = Some(match new {
                    None => predecessor,
                    Some(current) => intersect(&idom, predecessor, current),
                });
            }
            if new.is_some() && idom[block] != new {
                idom[block] = new;
                changed = true;
            }
        }
    }
    idom
}

/// Whether `a` dominates `b`.
pub(crate) fn dominates(idom: &[Option<BlockId>], a: BlockId, mut b: BlockId) -> bool {
    loop {
        if a == b {
            return true;
        }
        match idom[b] {
            Some(parent) if parent != b => b = parent,
            _ => return false,
        }
    }
}

/// A natural loop: the header and every block that reaches a back edge to
/// it without passing through it.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Loop {
    pub header: BlockId,
    pub blocks: BTreeSet<BlockId>,
    /// The sources of the back edges.
    pub latches: Vec<BlockId>,
}

impl Loop {
    /// The edges from a block of the loop to a block outside it.
    pub(crate) fn exits(&self, body: &Body) -> Vec<(BlockId, BlockId)> {
        self.blocks
            .iter()
            .flat_map(|block| {
                successors(&body.blocks[*block].terminator.kind)
                    .into_iter()
                    .filter(|target| !self.blocks.contains(target))
                    .map(move |target| (*block, target))
            })
            .collect()
    }
}

/// The body's natural loops, one per header, outermost first.
pub(crate) fn loops(body: &Body) -> Vec<Loop> {
    let idom = dominators(body);
    let predecessors = predecessors(body);
    let mut found: BTreeMap<BlockId, Loop> = BTreeMap::new();
    for (block, data) in body.blocks.iter().enumerate() {
        if idom[block].is_none() {
            continue;
        }
        for header in successors(&data.terminator.kind) {
            if !dominates(&idom, header, block) {
                continue;
            }
            let entry = found.entry(header).or_insert_with(|| Loop {
                header,
                blocks: BTreeSet::from([header]),
                latches: Vec::new(),
            });
            entry.latches.push(block);
            // Blocks the entry does not reach (a drop whose flag test was
            // folded away, say) may jump into the loop; they are not in it.
            let mut work = vec![block];
            while let Some(member) = work.pop() {
                if entry.blocks.insert(member) {
                    let reached = predecessors[member]
                        .iter()
                        .filter(|predecessor| idom[**predecessor].is_some());
                    work.extend(reached);
                }
            }
        }
    }
    let mut loops = found.into_values().collect::<Vec<_>>();
    loops.sort_by_key(|lp| std::cmp::Reverse(lp.blocks.len()));
    loops
}

/// Whether no other loop of `loops` lies inside `lp`.
pub(crate) fn innermost(lp: &Loop, loops: &[Loop]) -> bool {
    loops
        .iter()
        .all(|other| other.header == lp.header || !lp.blocks.contains(&other.header))
}

/// The loop's preheader: the one block outside the loop that enters the
/// header, ending in a `goto` to it. One is inserted when the header has
/// several entries, or an entry that also goes elsewhere.
pub(crate) fn preheader(body: &mut Body, lp: &Loop) -> BlockId {
    let entries = predecessors(body)[lp.header]
        .iter()
        .copied()
        .filter(|block| !lp.blocks.contains(block))
        .collect::<Vec<_>>();
    if let [entry] = entries.as_slice()
        && body.blocks[*entry].terminator.kind == TerminatorKind::Goto(lp.header)
    {
        return *entry;
    }
    let span = body.blocks[lp.header].terminator.span;
    let block = body.blocks.len();
    body.blocks.push(BasicBlock {
        statements: Vec::new(),
        terminator: Terminator {
            kind: TerminatorKind::Goto(lp.header),
            span,
        },
        unwind: None,
    });
    for entry in entries {
        retarget(&mut body.blocks[entry].terminator.kind, lp.header, block);
    }
    block
}

/// Copy the loop's blocks. Edges between blocks of the loop go to the
/// copies; exits and unwind edges stay as they are. Returns each block's
/// copy.
pub(crate) fn clone_loop(body: &mut Body, lp: &Loop) -> BTreeMap<BlockId, BlockId> {
    let mut copies = BTreeMap::new();
    for block in &lp.blocks {
        copies.insert(*block, body.blocks.len());
        body.blocks.push(body.blocks[*block].clone());
    }
    for copy in copies.values() {
        for (original, replacement) in &copies {
            retarget(&mut body.blocks[*copy].terminator.kind, *original, *replacement);
        }
    }
    copies
}

/// Version a loop: its preheader (from [`preheader`]) runs `statements`,
/// then enters the copy when `condition` is nonzero and the original loop
/// otherwise. Returns each block's copy.
pub(crate) fn version(
    body: &mut Body,
    lp: &Loop,
    preheader: BlockId,
    statements: Vec<Statement>,
    condition: Operand,
) -> BTreeMap<BlockId, BlockId> {
    let copies = clone_loop(body, lp);
    let block = &mut body.blocks[preheader];
    debug_assert_eq!(block.terminator.kind, TerminatorKind::Goto(lp.header));
    block.statements.extend(statements);
    block.terminator.kind = TerminatorKind::Switch {
        value: condition,
        targets: vec![(0, lp.header)],
        otherwise: copies[&lp.header],
    };
    copies
}

/// A value of the loop's condition, in terms of what it reads.
#[derive(Debug, Clone)]
pub(crate) enum Term {
    Constant(i64),
    /// A local's value (not a temporary of the condition).
    Local(LocalId),
    /// The length of the container in a local: a builtin `Len` call.
    Length(Target, LocalId),
    Binary(BinOp, Box<Term>, Box<Term>),
}

impl Term {
    fn locals(&self, out: &mut BTreeSet<LocalId>) {
        match self {
            Term::Constant(_) => {}
            Term::Local(local) | Term::Length(_, local) => {
                out.insert(*local);
            }
            Term::Binary(_, left, right) => {
                left.locals(out);
                right.locals(out);
            }
        }
    }
}

/// A counted loop: `while i <op> bound { ...; i = i +/- step; ... }`, with
/// one unconditional update of `i` per iteration and a bound the loop does
/// not change.
#[derive(Debug, Clone)]
pub(crate) struct Counted {
    pub counter: LocalId,
    /// `Lt` or `Le` with an increasing counter, `Gt` or `Ge` with a
    /// decreasing one.
    pub comparison: BinOp,
    pub bound: Term,
    pub step: i64,
    /// The blocks from the header to the test, in order; the last one
    /// switches on the condition.
    pub condition: Vec<BlockId>,
    /// Where the condition goes when it holds, and when it does not.
    pub body: BlockId,
    pub exit: BlockId,
    /// The update: its block and the statement assigning the counter.
    pub update: (BlockId, usize),
}

/// The locals whose address the body takes; an assignment through a
/// reference may change them.
pub(crate) fn address_taken(body: &Body) -> BTreeSet<LocalId> {
    let mut taken = BTreeSet::new();
    for block in &body.blocks {
        for statement in &block.statements {
            let StatementKind::Assign(_, rvalue) = &statement.kind;
            match rvalue {
                Rvalue::Ref(place) if !place.deref => {
                    taken.insert(place.local);
                }
                Rvalue::FnValue { captures, .. } => {
                    for capture in captures {
                        if let Capture::Address(local) = capture {
                            taken.insert(*local);
                        }
                    }
                }
                Rvalue::ElementAddress(ElementBase::Stored(place), _) if !place.deref => {
                    taken.insert(place.local);
                }
                Rvalue::View { source, .. } => match source {
                    ViewSource::Array(local) => {
                        taken.insert(*local);
                    }
                    ViewSource::DynArray(place) if !place.deref => {
                        taken.insert(place.local);
                    }
                    _ => {}
                },
                _ => {}
            }
        }
    }
    taken
}

/// The locals a set of blocks assigns: by statement or as a call's
/// destination.
pub(crate) fn assigned(body: &Body, blocks: &BTreeSet<BlockId>) -> BTreeSet<LocalId> {
    let mut out = BTreeSet::new();
    for block in blocks {
        let data = &body.blocks[*block];
        for statement in &data.statements {
            let StatementKind::Assign(place, _) = &statement.kind;
            if !place.deref {
                out.insert(place.local);
            }
        }
        if let TerminatorKind::Call {
            destination,
            callee,
            ..
        } = &data.terminator.kind
        {
            out.insert(*destination);
            if let Callee::Builtin {
                hint: CallHint::Shadow(length, capacity),
                ..
            } = callee
            {
                out.extend([*length, *capacity]);
            }
        }
    }
    out
}

/// The definition of a temporary assigned once in `blocks`, by statement
/// (its block and index) or as a call's destination (its block).
enum Definition<'b> {
    Statement(&'b Rvalue),
    Call(&'b TerminatorKind),
}

fn definition<'b>(
    body: &'b Body,
    blocks: &[BlockId],
    local: LocalId,
) -> Option<Definition<'b>> {
    let mut found = None;
    for block in blocks {
        let data = &body.blocks[*block];
        for statement in &data.statements {
            let StatementKind::Assign(place, rvalue) = &statement.kind;
            if place.local == local {
                if found.is_some() || place.deref || place.field.is_some() {
                    return None;
                }
                found = Some(Definition::Statement(rvalue));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator.kind
            && *destination == local
        {
            if found.is_some() {
                return None;
            }
            found = Some(Definition::Call(&data.terminator.kind));
        }
    }
    found
}

/// The term an operand of the condition denotes: temporaries are followed
/// to their one definition in the condition blocks.
fn term(body: &Body, blocks: &[BlockId], operand: Operand) -> Option<Term> {
    let place = match operand {
        Operand::Constant(value, _) => return Some(Term::Constant(value)),
        Operand::Copy(place) | Operand::Move(place) => place,
    };
    if place.deref || place.field.is_some() {
        return None;
    }
    if !body.locals[place.local].temporary {
        return Some(Term::Local(place.local));
    }
    match definition(body, blocks, place.local)? {
        Definition::Statement(Rvalue::Use(operand)) => term(body, blocks, *operand),
        Definition::Statement(Rvalue::Binary(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), l, r)) => {
            Some(Term::Binary(
                *op,
                Box::new(term(body, blocks, *l)?),
                Box::new(term(body, blocks, *r)?),
            ))
        }
        Definition::Call(TerminatorKind::Call {
            callee: Callee::Builtin { index, .. },
            args,
            ..
        }) => {
            use crate::executable::{BytesOp, SliceOp, VecOp};
            let target = body.builtins.0[*index];
            let length = matches!(
                target,
                Target::Slice(SliceOp::Len, _)
                    | Target::Vec(VecOp::Len, _)
                    | Target::Bytes(BytesOp::Len)
            );
            match (length, args.as_slice()) {
                (true, [container]) => match term(body, blocks, *container)? {
                    Term::Local(local) => Some(Term::Length(target, local)),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// The counter update `i = i +/- k`, as `(sign, k)`, when `rvalue` is the
/// value assigned to `i`: an addition or subtraction of a positive
/// constant, checked or unchecked, possibly through a temporary defined in
/// the same block before `at`.
fn update_step(body: &Body, block: BlockId, at: usize, counter: LocalId) -> Option<(BinOp, i64)> {
    let statements = &body.blocks[block].statements;
    let StatementKind::Assign(_, rvalue) = &statements[at].kind;
    let rvalue = match rvalue {
        Rvalue::Use(Operand::Move(place) | Operand::Copy(place))
            if body.locals[place.local].temporary && place.field.is_none() && !place.deref =>
        {
            statements[..at].iter().rev().find_map(|statement| {
                let StatementKind::Assign(target, rvalue) = &statement.kind;
                (target.local == place.local).then_some(rvalue)
            })?
        }
        rvalue => rvalue,
    };
    let reads_counter = |operand: &Operand| {
        matches!(operand, Operand::Copy(place) | Operand::Move(place)
            if place.local == counter && place.field.is_none() && !place.deref)
    };
    let (op, base, amount) = match rvalue {
        Rvalue::Binary(op @ (BinOp::Add | BinOp::Sub), base, amount) => (*op, base, amount),
        Rvalue::Int(crate::int::IntOp::Unchecked(op), _, _, operands) if operands.len() == 2 => {
            let op = match op {
                crate::int::ArithOp::Add => BinOp::Add,
                crate::int::ArithOp::Sub => BinOp::Sub,
                _ => return None,
            };
            (op, &operands[0], &operands[1])
        }
        _ => return None,
    };
    match amount {
        Operand::Constant(step, _) if *step > 0 && reads_counter(base) => Some((op, *step)),
        _ => None,
    }
}

/// A loop's test: `left <comparison> right` at the end of a chain of
/// blocks from the header, staying in the loop when it holds. The locals
/// the two terms read are not address-taken and not assigned by the
/// chain, so the terms are their values at the switch.
#[derive(Debug, Clone)]
pub(crate) struct Test {
    pub condition: Vec<BlockId>,
    pub comparison: BinOp,
    pub left: Term,
    pub right: Term,
    pub body: BlockId,
    pub exit: BlockId,
}

/// The loop's test, if its header starts one.
pub(crate) fn test(body: &Body, lp: &Loop) -> Option<Test> {
    // The condition: a chain of blocks from the header, each with one
    // successor, up to the one that switches.
    let mut condition = vec![lp.header];
    loop {
        let block = *condition.last().expect("the header");
        match &body.blocks[block].terminator.kind {
            TerminatorKind::Goto(next) | TerminatorKind::Call { next, .. }
                if lp.blocks.contains(next) && !condition.contains(next) =>
            {
                condition.push(*next);
            }
            TerminatorKind::Switch { .. } => break,
            _ => return None,
        }
    }
    let test = *condition.last().expect("the test");
    let TerminatorKind::Switch {
        value,
        targets,
        otherwise,
    } = &body.blocks[test].terminator.kind
    else {
        return None;
    };
    let [(0, exit)] = targets.as_slice() else {
        return None;
    };
    if lp.blocks.contains(exit) || !lp.blocks.contains(otherwise) {
        return None;
    }
    let tested = match value {
        Operand::Copy(place) | Operand::Move(place)
            if body.locals[place.local].temporary && place.field.is_none() && !place.deref =>
        {
            place.local
        }
        _ => return None,
    };
    let Some(Definition::Statement(Rvalue::Binary(
        comparison @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
        left,
        right,
    ))) = definition(body, &condition, tested)
    else {
        return None;
    };
    let left = term(body, &condition, *left)?;
    let right = term(body, &condition, *right)?;
    // The terms' locals change only where seen: not through a reference,
    // and not in the condition itself.
    let taken = address_taken(body);
    let mut read = BTreeSet::new();
    left.locals(&mut read);
    right.locals(&mut read);
    let in_condition = assigned(body, &condition.iter().copied().collect());
    if read.iter().any(|local| taken.contains(local) || in_condition.contains(local)) {
        return None;
    }
    Some(Test {
        condition,
        comparison: *comparison,
        left,
        right,
        body: *otherwise,
        exit: *exit,
    })
}

/// The loop's counted shape, if it has one.
pub(crate) fn counted(body: &Body, lp: &Loop) -> Option<Counted> {
    let Test {
        condition,
        comparison,
        left,
        right: bound,
        body: inside,
        exit,
    } = test(body, lp)?;
    if !matches!(comparison, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) {
        return None;
    }
    let Term::Local(counter) = left else {
        return None;
    };
    if !matches!(body.locals[counter].ty, Type::I64 | Type::Int(_)) {
        return None;
    }
    // The bound does not change in the loop.
    let in_loop = assigned(body, &lp.blocks);
    let mut bound_locals = BTreeSet::new();
    bound.locals(&mut bound_locals);
    if bound_locals.iter().any(|local| in_loop.contains(local)) {
        return None;
    }
    // One update of the counter, in a block every iteration runs.
    let mut updates = Vec::new();
    for block in &lp.blocks {
        for (at, statement) in body.blocks[*block].statements.iter().enumerate() {
            let StatementKind::Assign(place, _) = &statement.kind;
            if place.local == counter {
                updates.push((*block, at));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &body.blocks[*block].terminator.kind
            && *destination == counter
        {
            return None;
        }
    }
    let [(block, at)] = updates.as_slice() else {
        return None;
    };
    let idom = dominators(body);
    if !lp.latches.iter().all(|latch| dominates(&idom, *block, *latch)) {
        return None;
    }
    let (direction, step) = update_step(body, *block, *at, counter)?;
    let increasing = matches!(comparison, BinOp::Lt | BinOp::Le);
    if increasing != (direction == BinOp::Add) {
        return None;
    }
    Some(Counted {
        counter,
        comparison,
        bound,
        step,
        condition,
        body: inside,
        exit,
        update: (*block, *at),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn body(source: &str, name: &str) -> Body {
        let program = crate::executable::check(source).expect("the test program checks");
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some(name))
            .expect("the function");
        build(&program, index).expect("the function builds")
    }

    const SUM: &str = "
        fn sum(xs: &[i64]) -> i64 {
            let mut i = 0;
            let mut total = 0;
            while i < xs.len() {
                total = total + xs[i];
                i = i + 1;
            }
            total
        }
        fn main() -> Unit ! {io} { print_i64(0); }";

    #[test]
    fn a_while_loop_is_a_counted_natural_loop() {
        let body = body(SUM, "sum");
        let loops = loops(&body);
        let [lp] = loops.as_slice() else {
            panic!("one loop: {loops:?}");
        };
        assert!(innermost(lp, &loops));
        assert_eq!(lp.latches.len(), 1);
        let counted = counted(&body, lp).expect("a counted loop");
        assert_eq!(counted.comparison, BinOp::Lt);
        assert_eq!(counted.step, 1);
        assert_eq!(counted.condition.first(), Some(&lp.header));
        assert!(!lp.blocks.contains(&counted.exit));
        assert!(matches!(
            counted.bound,
            Term::Length(Target::Slice(crate::executable::SliceOp::Len, _), 0)
        ));
        assert_eq!(body.locals[counted.counter].ty, Type::I64);
    }

    #[test]
    fn counted_loops_need_one_constant_step_towards_the_bound() {
        let shapes = [
            ("while i > 0 { i = i - 2; }", true),
            ("while i < n { i = i * 2; }", false),
            ("while i < n { i = i - 1; }", false),
            ("while i < n { if i > 3 { i = i + 1; } else { i = i + 2; } }", false),
            ("while i < n { n = n - 1; i = i + 1; }", false),
            ("while i <= n { i = i + 3; }", true),
        ];
        for (shape, expected) in shapes {
            let source = format!(
                "fn f(start: i64, limit: i64) -> i64 {{
                    let mut i = start + 1;
                    let mut n = limit;
                    {shape}
                    i + n
                }}
                fn main() -> Unit ! {{io}} {{ print_i64(f(1, 2)); }}"
            );
            let body = body(&source, "f");
            let loops = loops(&body);
            assert_eq!(loops.len(), 1, "{shape}");
            assert_eq!(counted(&body, &loops[0]).is_some(), expected, "{shape}");
        }
    }

    #[test]
    fn nested_loops_nest_and_only_the_inner_one_is_innermost() {
        let body = body(
            "fn f(n: i64) -> i64 {
                let mut total = 0;
                let mut i = 0;
                while i < n {
                    let mut j = 0;
                    while j < i { total = total + j; j = j + 1; }
                    i = i + 1;
                }
                total
            }
            fn main() -> Unit ! {io} { print_i64(f(3)); }",
            "f",
        );
        let loops = loops(&body);
        assert_eq!(loops.len(), 2);
        let (outer, inner) = (&loops[0], &loops[1]);
        assert!(outer.blocks.is_superset(&inner.blocks));
        assert!(!innermost(outer, &loops));
        assert!(innermost(inner, &loops));
        assert!(counted(&body, outer).is_some());
        assert!(counted(&body, inner).is_some());
    }

    #[test]
    fn versioning_copies_the_loop_behind_its_preheader() {
        let program = crate::executable::check(SUM).unwrap();
        let mut body = body(SUM, "sum");
        let lp = loops(&body).remove(0);
        let before = body.blocks.len();
        let entry = preheader(&mut body, &lp);
        assert_eq!(body.blocks.len(), before, "the entry block is a preheader");
        let flag = body.locals.len();
        body.locals.push(LocalDecl {
            ty: Type::Bool,
            mutable: false,
            temporary: true,
        });
        let span = body.blocks[entry].terminator.span;
        let guard = Statement {
            kind: StatementKind::Assign(
                Place::local(flag),
                Rvalue::Use(Operand::Constant(1, Type::Bool)),
            ),
            span,
        };
        let copies = version(
            &mut body,
            &lp,
            entry,
            vec![guard],
            Operand::Copy(Place::local(flag)),
        );
        assert_eq!(body.blocks.len(), before + lp.blocks.len());
        assert_eq!(copies.len(), lp.blocks.len());
        verify(&program, &body).expect("the versioned body verifies");
        // Two loops now, each counted, with the same exit.
        let loops = loops(&body);
        assert_eq!(loops.len(), 2);
        let exits = loops
            .iter()
            .map(|lp| counted(&body, lp).expect("counted").exit)
            .collect::<Vec<_>>();
        assert_eq!(exits[0], exits[1]);
        // The text form reads back.
        let printed = text::print(&body);
        assert_eq!(text::parse(&printed).unwrap(), body);
    }

    #[test]
    fn a_header_with_two_entries_gets_a_preheader() {
        let mut body = body(SUM, "sum");
        let lp = loops(&body).remove(0);
        // Add a second entry: a block that jumps to the header.
        let span = body.blocks[lp.header].terminator.span;
        let extra = body.blocks.len();
        body.blocks.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator {
                kind: TerminatorKind::Goto(lp.header),
                span,
            },
            unwind: None,
        });
        body.blocks[0].terminator.kind = TerminatorKind::Switch {
            value: Operand::Constant(0, Type::Bool),
            targets: vec![(0, lp.header)],
            otherwise: extra,
        };
        let entry = preheader(&mut body, &lp);
        assert_eq!(entry, extra + 1);
        assert_eq!(predecessors(&body)[lp.header].len(), 1 + lp.latches.len());
        assert_eq!(
            body.blocks[entry].terminator.kind,
            TerminatorKind::Goto(lp.header)
        );
    }
}
