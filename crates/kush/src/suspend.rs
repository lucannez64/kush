//! Lowering of suspendable handled bodies into resumable state machines.
//!
//! See `docs/effect-state-machines.md`. The checker produces
//! `ExprKind::Suspendable` for a handled body whose handler is not statically
//! tail-resumptive, with one `ExprKind::Suspend` per perform; ownership and
//! grades check that structured form. This pass then, for every suspendable
//! body `S` in a function `F`:
//!
//! 1. computes the locals live after each suspension point `i` (`L(i)`) with
//!    a backward liveness over the checked IR, including loop fixed points;
//! 2. checks the suspension rules of the design (no borrow across a point,
//!    no handler-written local across a point, outer locals moved into the
//!    machine are not used again by `F`, no `return`/`?`/outer `break` after a
//!    point, `alloc` for a capturing resumption);
//! 3. builds one continuation function per point: the code that runs from
//!    the point to the end of the body, reconstructed structurally through
//!    the enclosing blocks, branches and loops. It keeps `F`'s slot numbering
//!    and receives `L(i)` as closure captures at those slots plus the
//!    operation result as its parameter;
//! 4. replaces each point by `RegionExit(handler(payload, token))` where the
//!    token is a closure of that continuation capturing `L(i)` by move, and
//!    `S` by a `Region`. Code before the first point therefore still runs in
//!    place in `F`.
//!
//! The per-point closure environment is the frame of the design: it holds
//! exactly the values live at that point, it is consumed by resuming, and the
//! existing closure drop glue releases it. Every owned value therefore leaves
//! `F` (or the previous continuation) exactly once through a capture move and
//! enters the next continuation exactly once through its prologue.
use crate::{
    Diagnostic, Span,
    executable::{
        Block, Executable, Expr, ExprKind, Function, Local, Statement, Suspendable, Type,
    },
    grades::Grade,
};
use std::collections::{BTreeMap, BTreeSet};
type Result<T> = std::result::Result<T, Diagnostic>;
type Slots = BTreeSet<usize>;

/// One step of a path from a handled body to a suspension point.
#[derive(Debug, Clone, Copy)]
enum Step {
    /// Statement `k` of a block; `k == statements.len()` is the tail.
    Stmt(usize),
    /// The block of a `Block`, `Loop` or `While` expression.
    Body,
    Then,
    Else,
    /// The body of match arm `k`.
    Arm(usize),
}

pub(crate) fn lower(program: &mut Executable) -> Result<()> {
    let mut index = 0;
    while index < program.functions.len() {
        while let Some(target) = innermost_in_block(&program.functions[index].body) {
            lower_one(program, index, target)?;
        }
        index += 1;
    }
    Ok(())
}

fn innermost(expr: &Expr) -> Option<*const Suspendable> {
    if let ExprKind::Suspendable(suspendable) = &expr.kind {
        return innermost_in_block(&suspendable.body)
            .or(Some(&**suspendable as *const Suspendable));
    }
    let mut found = None;
    expr.for_each_child(&mut |child| {
        if found.is_none() {
            found = innermost(child);
        }
    });
    found
}

fn innermost_in_block(block: &Block) -> Option<*const Suspendable> {
    block
        .statements
        .iter()
        .find_map(|statement| match statement {
            Statement::Let(_, value) | Statement::Expr(value) => innermost(value),
            Statement::Declare(_) => None,
        })
        .or_else(|| block.tail.as_deref().and_then(innermost))
}

/// Take the target suspendable out of a function body, leaving a placeholder,
/// run `f` on it, and store the expression kind `f` returns in its place.
fn replace_target(
    expr: &mut Expr,
    target: *const Suspendable,
    f: &mut Option<&mut dyn FnMut(Box<Suspendable>) -> Result<ExprKind>>,
) -> Result<()> {
    if let ExprKind::Suspendable(suspendable) = &expr.kind
        && std::ptr::eq(&**suspendable, target)
    {
        let ExprKind::Suspendable(suspendable) =
            std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
        else {
            unreachable!("matched above")
        };
        let lower = f.take().expect("the target occurs once");
        expr.kind = lower(suspendable)?;
        return Ok(());
    }
    let mut result = Ok(());
    expr.for_each_child_mut(&mut |child| {
        if result.is_ok() && f.is_some() {
            result = replace_target(child, target, f);
        }
    });
    result
}

fn replace_target_in_block(
    block: &mut Block,
    target: *const Suspendable,
    f: &mut Option<&mut dyn FnMut(Box<Suspendable>) -> Result<ExprKind>>,
) -> Result<()> {
    for statement in &mut block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            replace_target(value, target, f)?;
        }
    }
    if let Some(tail) = block.tail.as_deref_mut() {
        replace_target(tail, target, f)?;
    }
    Ok(())
}

fn find_in_block(block: &Block, target: *const Suspendable) -> Option<&Suspendable> {
    block
        .statements
        .iter()
        .find_map(|statement| match statement {
            Statement::Let(_, value) | Statement::Expr(value) => find(value, target),
            Statement::Declare(_) => None,
        })
        .or_else(|| block.tail.as_deref().and_then(|tail| find(tail, target)))
}

fn find(expr: &Expr, target: *const Suspendable) -> Option<&Suspendable> {
    if let ExprKind::Suspendable(suspendable) = &expr.kind
        && std::ptr::eq(&**suspendable, target)
    {
        return Some(suspendable);
    }
    let mut found = None;
    expr.for_each_child(&mut |child| {
        if found.is_none() {
            found = find(child, target);
        }
    });
    found
}

/// Backward liveness of local slots over checked IR. Every read, move,
/// borrow, or capture of a slot is a use; `let`, assignment, temporary-owner
/// initialization and pattern binding are definitions. Loops are solved to a
/// fixed point. While walking, it records the live set after the target
/// suspendable and after every suspension point.
#[derive(Default)]
struct Live {
    /// (live at the loop head, live after the loop) of enclosing loops.
    loops: Vec<(Slots, Slots)>,
    /// Live after each enclosing lowered region.
    regions: Vec<Slots>,
    target: Option<*const Suspendable>,
    target_after: Slots,
    points: BTreeMap<usize, Slots>,
}

impl Live {
    fn block(&mut self, block: &Block, after: &Slots) -> Slots {
        let mut live = after.clone();
        if let Some(tail) = &block.tail {
            live = self.expr(tail, &live);
        }
        for statement in block.statements.iter().rev() {
            match statement {
                Statement::Let(slot, value) => {
                    live.remove(slot);
                    live = self.expr(value, &live);
                }
                Statement::Expr(value) => live = self.expr(value, &live),
                Statement::Declare(slot) => {
                    live.remove(slot);
                }
            }
        }
        live
    }

    fn expr(&mut self, expr: &Expr, after: &Slots) -> Slots {
        match &expr.kind {
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Borrow(slot) => {
                let mut live = after.clone();
                live.insert(*slot);
                live
            }
            ExprKind::Assign(slot, value) => {
                let mut live = after.clone();
                live.remove(slot);
                self.expr(value, &live)
            }
            ExprKind::InitOwner { slot, value } | ExprKind::BorrowInit { slot, value } => {
                let mut live = after.clone();
                live.remove(slot);
                self.expr(value, &live)
            }
            ExprKind::Block(block) => self.block(block, after),
            ExprKind::If(condition, yes, no) => {
                let mut branches = self.block(yes, after);
                branches.extend(self.block(no, after));
                self.expr(condition, &branches)
            }
            ExprKind::Match(scrutinee, arms) => {
                let mut arms_live = Slots::new();
                for arm in arms {
                    let mut live = self.expr(&arm.body, after);
                    if let Some(guard) = &arm.guard {
                        live = self.expr(guard, &live);
                    }
                    let mut bound = Slots::new();
                    crate::ownership::pattern_bindings(&arm.pattern, &mut bound);
                    live.retain(|slot| !bound.contains(slot));
                    arms_live.extend(live);
                }
                self.expr(scrutinee, &arms_live)
            }
            ExprKind::Loop(body) => {
                let mut head = Slots::new();
                loop {
                    self.loops.push((head.clone(), after.clone()));
                    let mut next = self.block(body, &head);
                    self.loops.pop();
                    next.extend(head.iter().copied());
                    if next == head {
                        break head;
                    }
                    head = next;
                }
            }
            ExprKind::While(condition, body) => {
                let mut head = Slots::new();
                loop {
                    self.loops.push((head.clone(), after.clone()));
                    let mut test = self.block(body, &head);
                    self.loops.pop();
                    test.extend(after.iter().copied());
                    let mut next = self.expr(condition, &test);
                    next.extend(head.iter().copied());
                    if next == head {
                        break head;
                    }
                    head = next;
                }
            }
            ExprKind::Break(value, _) => {
                let exit = self
                    .loops
                    .last()
                    .map(|(_, exit)| exit.clone())
                    .unwrap_or_default();
                match value {
                    Some(value) => self.expr(value, &exit),
                    None => exit,
                }
            }
            ExprKind::Continue(_) => self
                .loops
                .last()
                .map(|(head, _)| head.clone())
                .unwrap_or_default(),
            ExprKind::Return(value) => self.expr(value, &Slots::new()),
            ExprKind::Binary(
                crate::lexer::Kind::AmpAmp | crate::lexer::Kind::PipePipe,
                left,
                right,
            ) => {
                let mut live = self.expr(right, after);
                live.extend(after.iter().copied());
                self.expr(left, &live)
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                let live = self.block(body, after);
                self.expr(handler, &live)
            }
            ExprKind::Region { body, finish, .. } => {
                let exit = match finish {
                    Some(finish) => self.expr(finish, after),
                    None => after.clone(),
                };
                self.regions.push(exit.clone());
                let live = self.block(body, &exit);
                self.regions.pop();
                live
            }
            ExprKind::RegionExit { value, .. } => {
                let exit = self.regions.last().cloned().unwrap_or_default();
                self.expr(value, &exit)
            }
            ExprKind::Suspendable(suspendable) => {
                if self
                    .target
                    .is_some_and(|target| std::ptr::eq(&**suspendable, target))
                {
                    self.target_after.extend(after.iter().copied());
                }
                self.block(&suspendable.body, after)
            }
            ExprKind::Suspend { point, call } => {
                self.points
                    .entry(*point)
                    .or_default()
                    .extend(after.iter().copied());
                self.expr(call, after)
            }
            _ => {
                let mut children = Vec::new();
                expr.for_each_child(&mut |child| children.push(child));
                let mut live = after.clone();
                for child in children.into_iter().rev() {
                    live = self.expr(child, &live);
                }
                live
            }
        }
    }
}

/// Slots bound anywhere inside a block (not inside separately compiled
/// lambda bodies, which are other functions).
fn bound_in_block(block: &Block, out: &mut Slots) {
    for statement in &block.statements {
        match statement {
            Statement::Let(slot, value) => {
                out.insert(*slot);
                bound_in(value, out);
            }
            Statement::Declare(slot) => {
                out.insert(*slot);
            }
            Statement::Expr(value) => bound_in(value, out),
        }
    }
    if let Some(tail) = &block.tail {
        bound_in(tail, out);
    }
}

fn bound_in(expr: &Expr, out: &mut Slots) {
    match &expr.kind {
        ExprKind::Match(scrutinee, arms) => {
            bound_in(scrutinee, out);
            for arm in arms {
                crate::ownership::pattern_bindings(&arm.pattern, out);
                if let Some(guard) = &arm.guard {
                    bound_in(guard, out);
                }
                bound_in(&arm.body, out);
            }
        }
        ExprKind::InitOwner { slot, value } | ExprKind::BorrowInit { slot, value } => {
            out.insert(*slot);
            bound_in(value, out);
        }
        _ => {
            let mut blocks = Vec::new();
            let mut children = Vec::new();
            block_children(expr, &mut |block| blocks.push(block), &mut |child| {
                children.push(child)
            });
            for block in blocks {
                bound_in_block(block, out);
            }
            for child in children {
                bound_in(child, out);
            }
        }
    }
}

/// Visit the direct blocks of a block-carrying expression with `on_block`
/// and every other direct child with `on_expr`.
fn block_children<'a>(
    expr: &'a Expr,
    on_block: &mut dyn FnMut(&'a Block),
    on_expr: &mut dyn FnMut(&'a Expr),
) {
    match &expr.kind {
        ExprKind::Block(block) | ExprKind::Loop(block) => on_block(block),
        ExprKind::If(condition, yes, no) => {
            on_expr(condition);
            on_block(yes);
            on_block(no);
        }
        ExprKind::While(condition, body) => {
            on_expr(condition);
            on_block(body);
        }
        ExprKind::HandlerPush { handler, body, .. } => {
            on_expr(handler);
            on_block(body);
        }
        ExprKind::Suspendable(suspendable) => on_block(&suspendable.body),
        ExprKind::Region { body, finish, .. } => {
            on_block(body);
            if let Some(finish) = finish {
                on_expr(finish);
            }
        }
        _ => expr.for_each_child(on_expr),
    }
}

/// Resource ids that can be active inside a body: every temporary and every
/// local bound in it. A region exit drops the active ones.
fn resources_in(block: &Block, local_resources: &[Option<usize>]) -> Vec<usize> {
    fn walk(expr: &Expr, out: &mut BTreeSet<usize>) {
        if let Some(id) = expr.resource {
            out.insert(id);
        }
        expr.for_each_child(&mut |child| walk(child, out));
    }
    let mut ids = BTreeSet::new();
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, &mut ids);
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, &mut ids);
    }
    let mut bound = Slots::new();
    bound_in_block(block, &mut bound);
    ids.extend(bound.iter().filter_map(|slot| local_resources[*slot]));
    let mut ids = ids.into_iter().collect::<Vec<_>>();
    ids.reverse();
    ids
}

/// Find the path to every suspension point of the body.
fn point_paths(block: &Block) -> Result<BTreeMap<usize, Vec<Step>>> {
    fn in_block(
        block: &Block,
        path: &mut Vec<Step>,
        out: &mut BTreeMap<usize, Vec<Step>>,
    ) -> Result<()> {
        for (index, statement) in block.statements.iter().enumerate() {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                path.push(Step::Stmt(index));
                in_expr(value, path, out)?;
                path.pop();
            }
        }
        if let Some(tail) = &block.tail {
            path.push(Step::Stmt(block.statements.len()));
            in_expr(tail, path, out)?;
            path.pop();
        }
        Ok(())
    }
    fn in_expr(
        expr: &Expr,
        path: &mut Vec<Step>,
        out: &mut BTreeMap<usize, Vec<Step>>,
    ) -> Result<()> {
        match &expr.kind {
            ExprKind::Suspend { point, call } => {
                if contains_point(call) {
                    return Err(misplaced(call.span));
                }
                if out.insert(*point, path.clone()).is_some() {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: a suspension point occurs twice",
                    ));
                }
                Ok(())
            }
            ExprKind::Block(block) | ExprKind::Loop(block) => {
                path.push(Step::Body);
                in_block(block, path, out)?;
                path.pop();
                Ok(())
            }
            ExprKind::While(condition, body) => {
                if contains_point(condition) {
                    return Err(misplaced(condition.span));
                }
                path.push(Step::Body);
                in_block(body, path, out)?;
                path.pop();
                Ok(())
            }
            ExprKind::If(condition, yes, no) => {
                if contains_point(condition) {
                    return Err(misplaced(condition.span));
                }
                path.push(Step::Then);
                in_block(yes, path, out)?;
                path.pop();
                path.push(Step::Else);
                in_block(no, path, out)?;
                path.pop();
                Ok(())
            }
            ExprKind::Match(scrutinee, arms) => {
                if contains_point(scrutinee) {
                    return Err(misplaced(scrutinee.span));
                }
                for (index, arm) in arms.iter().enumerate() {
                    if let Some(guard) = &arm.guard
                        && contains_point(guard)
                    {
                        return Err(misplaced(guard.span));
                    }
                    path.push(Step::Arm(index));
                    in_expr(&arm.body, path, out)?;
                    path.pop();
                }
                Ok(())
            }
            _ if contains_point(expr) => Err(misplaced(expr.span)),
            _ => Ok(()),
        }
    }
    let mut out = BTreeMap::new();
    in_block(block, &mut Vec::new(), &mut out)?;
    Ok(out)
}

fn misplaced(span: Span) -> Diagnostic {
    Diagnostic::new(
        span,
        "a non-tail 'perform' is not supported in this position; bind it with 'let' in the handled body",
    )
}

fn contains_point(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Suspend { .. } => true,
        ExprKind::Suspendable(_) => false,
        _ => {
            let mut found = false;
            expr.for_each_child(&mut |child| found |= contains_point(child));
            found
        }
    }
}

fn statement_value_mut(statement: &mut Statement) -> &mut Expr {
    match statement {
        Statement::Let(_, value) | Statement::Expr(value) => value,
        Statement::Declare(_) => unreachable!("paths never enter a declaration"),
    }
}

/// The expression at `path` inside `block`.
fn at_path_mut<'a>(block: &'a mut Block, path: &[Step]) -> &'a mut Expr {
    let Step::Stmt(index) = path[0] else {
        unreachable!("a block path starts with a statement")
    };
    let expr = if index == block.statements.len() {
        block.tail.as_deref_mut().expect("path to the tail")
    } else {
        statement_value_mut(&mut block.statements[index])
    };
    expr_at_path_mut(expr, &path[1..])
}

fn expr_at_path_mut<'a>(expr: &'a mut Expr, path: &[Step]) -> &'a mut Expr {
    let Some(step) = path.first() else {
        return expr;
    };
    match (step, &mut expr.kind) {
        (
            Step::Body,
            ExprKind::Block(block) | ExprKind::Loop(block) | ExprKind::While(_, block),
        )
        | (Step::Then, ExprKind::If(_, block, _))
        | (Step::Else, ExprKind::If(_, _, block)) => at_path_mut(block, &path[1..]),
        (Step::Arm(index), ExprKind::Match(_, arms)) => {
            expr_at_path_mut(&mut arms[*index].body, &path[1..])
        }
        _ => unreachable!("paths follow the checked structure"),
    }
}

/// Builds continuation code for one suspension point.
struct Zipper {
    /// First free local slot of the continuation function.
    next_local: usize,
    /// Flag locals added for re-entered loops.
    flags: Vec<Local>,
    span: Span,
}

impl Zipper {
    /// Code that runs the remainder of `block` from the point at `path`,
    /// where `input` replaces the point.
    fn block(&mut self, block: &Block, path: &[Step], input: Expr) -> Block {
        let Step::Stmt(index) = path[0] else {
            unreachable!("a block path starts with a statement")
        };
        let mut statements = Vec::new();
        // Locals bound earlier in this block are in scope at the point; they
        // arrive through captures (or were not live). Declaring them keeps
        // their lexical cleanup at this block's end.
        for statement in &block.statements[..index] {
            match statement {
                Statement::Let(slot, _) | Statement::Declare(slot) => {
                    statements.push(Statement::Declare(*slot))
                }
                Statement::Expr(_) => {}
            }
        }
        let tail = if index == block.statements.len() {
            let tail = block.tail.as_deref().expect("path to the tail");
            Some(Box::new(self.expr(tail, &path[1..], input)))
        } else {
            let resumed = match &block.statements[index] {
                Statement::Let(slot, value) => {
                    Statement::Let(*slot, self.expr(value, &path[1..], input))
                }
                Statement::Expr(value) => Statement::Expr(self.expr(value, &path[1..], input)),
                Statement::Declare(_) => unreachable!("paths never enter a declaration"),
            };
            statements.push(resumed);
            statements.extend(block.statements[index + 1..].iter().cloned());
            block.tail.clone()
        };
        Block {
            statements,
            tail,
            ty: block.ty,
        }
    }

    fn expr(&mut self, expr: &Expr, path: &[Step], input: Expr) -> Expr {
        let Some(step) = path.first() else {
            return input;
        };
        let span = expr.span;
        let wrap = |kind: ExprKind, ty: Type| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        match (step, &expr.kind) {
            (Step::Body, ExprKind::Block(block)) => wrap(
                ExprKind::Block(self.block(block, &path[1..], input)),
                expr.ty,
            ),
            (Step::Then, ExprKind::If(_, block, _)) | (Step::Else, ExprKind::If(_, _, block)) => {
                wrap(
                    ExprKind::Block(self.block(block, &path[1..], input)),
                    expr.ty,
                )
            }
            (Step::Arm(index), ExprKind::Match(_, arms)) => {
                let arm = &arms[*index];
                let mut bound = Slots::new();
                crate::ownership::pattern_bindings(&arm.pattern, &mut bound);
                let rest = self.expr(&arm.body, &path[1..], input);
                wrap(
                    ExprKind::Block(Block {
                        statements: bound.into_iter().map(Statement::Declare).collect(),
                        ty: rest.ty,
                        tail: Some(Box::new(rest)),
                    }),
                    expr.ty,
                )
            }
            (Step::Body, ExprKind::Loop(body)) => {
                let rest = self.block(body, &path[1..], input);
                self.reentered_loop(expr, rest, body.clone(), None)
            }
            (Step::Body, ExprKind::While(condition, body)) => {
                let rest = self.block(body, &path[1..], input);
                self.reentered_loop(expr, rest, body.clone(), Some((**condition).clone()))
            }
            _ => unreachable!("paths follow the checked structure"),
        }
    }

    /// `{ let mut first = true; loop { if first { first = false; rest }
    /// else { [if !cond { break }] body } } }`: finish the interrupted
    /// iteration, then iterate normally. `break` and `continue` in both arms
    /// target the rebuilt loop, as they targeted the original one.
    fn reentered_loop(
        &mut self,
        original: &Expr,
        rest: Block,
        body: Block,
        condition: Option<Expr>,
    ) -> Expr {
        let span = self.span;
        let first = self.next_local;
        self.next_local += 1;
        self.flags.push(Local {
            ty: Type::Bool,
            mutable: true,
            linear: false,
            pinned: false,
            grade: None,
            span,
        });
        let e = |kind: ExprKind, ty: Type| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let block_expr = |block: Block| {
            let ty = block.ty;
            e(ExprKind::Block(block), ty)
        };
        let mut normal = Vec::new();
        if let Some(condition) = condition {
            let not = e(
                ExprKind::Unary(crate::lexer::Kind::Bang, Box::new(condition)),
                Type::Bool,
            );
            normal.push(Statement::Expr(e(
                ExprKind::If(
                    Box::new(not),
                    Block {
                        statements: vec![],
                        tail: Some(Box::new(e(ExprKind::Break(None, vec![]), Type::Never))),
                        ty: Type::Never,
                    },
                    Block {
                        statements: vec![],
                        tail: None,
                        ty: Type::Unit,
                    },
                ),
                Type::Unit,
            )));
        }
        let body_ty = body.ty;
        normal.push(Statement::Expr(block_expr(body)));
        let _ = body_ty;
        let iteration_ty = Type::Unit;
        let resumed = Block {
            statements: vec![
                Statement::Expr(e(
                    ExprKind::Assign(first, Box::new(e(ExprKind::Constant(0), Type::Bool))),
                    Type::Unit,
                )),
                Statement::Expr(block_expr(rest)),
            ],
            tail: None,
            ty: Type::Unit,
        };
        let normal = Block {
            statements: normal,
            tail: None,
            ty: Type::Unit,
        };
        let iteration = e(
            ExprKind::If(
                Box::new(e(ExprKind::Local(first), Type::Bool)),
                resumed,
                normal,
            ),
            iteration_ty,
        );
        let looped = e(
            ExprKind::Loop(Block {
                statements: vec![Statement::Expr(iteration)],
                tail: None,
                ty: Type::Unit,
            }),
            original.ty,
        );
        block_expr(Block {
            statements: vec![Statement::Let(first, e(ExprKind::Constant(1), Type::Bool))],
            tail: Some(Box::new(looped)),
            ty: original.ty,
        })
    }
}

/// Reject control transfers that would leave a continuation function:
/// `return`, `?`, and `break`/`continue` that target a loop outside it.
fn check_escapes(block: &Block) -> Result<()> {
    fn walk(expr: &Expr, depth: usize) -> Result<()> {
        match &expr.kind {
            ExprKind::Return(_) => Err(Diagnostic::new(
                expr.span,
                "a non-tail resumption continuation cannot 'return' out of the handled body: the handler is still running around the resumption. Return a value from the body and let the handler or the code after 'handle' decide, or use a tail-resumptive handler",
            )),
            ExprKind::Try { .. } => Err(Diagnostic::new(
                expr.span,
                "a non-tail resumption continuation cannot use '?': it would return across the resumption; match on the result instead",
            )),
            ExprKind::Break(..) | ExprKind::Continue(_) if depth == 0 => Err(Diagnostic::new(
                expr.span,
                "a non-tail resumption continuation cannot 'break' or 'continue' to a loop outside the handled body",
            )),
            ExprKind::Loop(_) | ExprKind::While(..) => {
                let mut result = Ok(());
                expr.for_each_child(&mut |child| {
                    if result.is_ok() {
                        result = walk(child, depth + 1);
                    }
                });
                result
            }
            _ => {
                let mut result = Ok(());
                expr.for_each_child(&mut |child| {
                    if result.is_ok() {
                        result = walk(child, depth);
                    }
                });
                result
            }
        }
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, 0)?;
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, 0)?;
    }
    Ok(())
}

/// The root local of a place expression, if any.
fn place_root(expr: &Expr) -> Option<usize> {
    match &expr.kind {
        ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => Some(*slot),
        ExprKind::Project(base, _) | ExprKind::PlaceIndex { base, .. } => place_root(base),
        _ => None,
    }
}

/// Reject writes in a continuation to locals of the enclosing function that
/// the function reads after the handle: the continuation works on its own
/// copy, so the write would be lost.
fn check_outer_writes(
    block: &Block,
    outer_live: &dyn Fn(usize) -> bool,
    locals: &[Local],
) -> Result<()> {
    fn walk(expr: &Expr, outer_live: &dyn Fn(usize) -> bool, locals: &[Local]) -> Result<()> {
        let written = match &expr.kind {
            ExprKind::Assign(slot, _)
            | ExprKind::InitOwner { slot, .. }
            | ExprKind::BorrowInit { slot, .. } => Some(*slot),
            ExprKind::Borrow(slot)
                if expr.ty.is_mut_slice() || matches!(expr.ty, Type::RefMut(_) | Type::StrMut) =>
            {
                Some(*slot)
            }
            ExprKind::BorrowPlace(place) if matches!(expr.ty, Type::RefMut(_)) => place_root(place),
            _ => None,
        };
        if let Some(slot) = written
            && outer_live(slot)
        {
            return Err(Diagnostic::new(
                expr.span,
                "a resumed continuation cannot write a local of the enclosing function that is used after the 'handle': the continuation runs on its own copy of the value",
            )
            .with_note(locals[slot].span, "local declared here"));
        }
        let mut result = Ok(());
        expr.for_each_child(&mut |child| {
            if result.is_ok() {
                result = walk(child, outer_live, locals);
            }
        });
        result
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, outer_live, locals)?;
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, outer_live, locals)?;
    }
    Ok(())
}

/// Replace the `Erased` token argument of a suspension's handler call.
fn install_token(call: &mut Expr, token: Expr) {
    match &mut call.kind {
        ExprKind::Coerce { value, .. } => install_token(value, token),
        ExprKind::CallIndirect { arguments, .. } => arguments[1] = token,
        _ => unreachable!("a suspension wraps the handler call"),
    }
}

fn lower_one(program: &mut Executable, index: usize, target: *const Suspendable) -> Result<()> {
    let function = &program.functions[index];
    let after_handle = {
        let mut live = Live {
            target: Some(target),
            ..Live::default()
        };
        live.block(&function.body, &Slots::new());
        live.target_after
    };
    let locals = function.locals.clone();
    let resources = function.resources.clone();
    let local_resources = function.local_resources.clone();
    let index_relations = function.index_relations.clone();
    let name = function.name.clone();
    let suspendable = find_in_block(&function.body, target).expect("target suspendable exists");
    let result_owned = program.owns(suspendable.result);
    let first_function = program.functions.len();
    let mut continuations = Vec::new();
    let mut lower = |suspendable: Box<Suspendable>| -> Result<ExprKind> {
        let Suspendable {
            result,
            token,
            multishot,
            handler_writes,
            effects,
            borrowed,
            copyable,
            mut body,
            span,
            ..
        } = *suspendable;
        let paths = point_paths(&body)?;
        if paths.is_empty() {
            return Ok(ExprKind::Block(body));
        }
        let mut liveness = Live::default();
        liveness.block(&body, &Slots::new());
        let mut bound = Slots::new();
        bound_in_block(&body, &mut bound);
        let erased = |slot: usize| locals[slot].grade.is_some_and(Grade::is_zero);
        // Live values at each point, in a stable order: they become the
        // continuation's captures.
        let mut captures = BTreeMap::new();
        for point in paths.keys() {
            let live = liveness.points.get(point).cloned().unwrap_or_default();
            captures.insert(
                *point,
                live.into_iter()
                    .filter(|slot| !erased(*slot))
                    .collect::<Vec<_>>(),
            );
        }
        // Suspension rules (design section 6).
        let mut point_spans = BTreeMap::new();
        for (point, path) in &paths {
            point_spans.insert(*point, at_path_mut(&mut body, path).span);
        }
        for (point, slots) in &captures {
            let at = point_spans[point];
            for slot in slots {
                let local = &locals[*slot];
                if borrowed.get(*slot).copied().unwrap_or(false) {
                    return Err(Diagnostic::new(
                        at,
                        "a borrowed value (slice view, text view, reference, borrowed record, or task handle) cannot stay live across a non-tail 'perform'; end the borrow before the perform or pass an owned value",
                    )
                    .with_note(local.span, "borrowed value declared here"));
                }
                if handler_writes.contains(slot) {
                    return Err(Diagnostic::new(
                        at,
                        "a local the handler writes through its capture cannot stay live across a non-tail 'perform': the resumption would hold a stale copy",
                    )
                    .with_note(local.span, "local declared here"));
                }
                if !bound.contains(slot)
                    && !copyable.get(*slot).copied().unwrap_or(false)
                    && after_handle.contains(slot)
                {
                    return Err(Diagnostic::new(
                        at,
                        "this value is used after the 'handle', but the non-tail 'perform' moves it into the resumption; use it only inside the handled body or after it is no longer needed there",
                    )
                    .with_note(local.span, "value declared here"));
                }
            }
            if multishot && !slots.is_empty() {
                return Err(Diagnostic::new(
                    at,
                    "multishot resumption requires a continuation with no captured values; the copyable resumption token cannot own an environment. Copy the needed values into the operation payload or use a one-shot 'linear once fn' handler",
                )
                .with_note(locals[slots[0]].span, "captured value declared here"));
            }
            if !slots.is_empty() {
                let missing = (crate::executable::ALLOC | crate::executable::PANIC) & !effects;
                if missing != 0 {
                    let names = [
                        (crate::executable::ALLOC, "alloc"),
                        (crate::executable::PANIC, "panic"),
                    ]
                    .into_iter()
                    .filter(|(bit, _)| missing & bit != 0)
                    .map(|(_, name)| name)
                    .collect::<Vec<_>>();
                    return Err(Diagnostic::new(
                        at,
                        format!(
                            "operation requires effects {{{}}}; add them to the function signature (a non-tail 'perform' with live values allocates its resumption)",
                            names.join(", ")
                        ),
                    ));
                }
            }
        }
        // Function index of each point's continuation.
        let order = paths.keys().copied().collect::<Vec<_>>();
        let function_of = |point: usize| {
            first_function + order.iter().position(|p| *p == point).expect("known point")
        };
        let cleanup = resources_in(&body, &local_resources);
        // Replace every point by an exit that calls the handler with the
        // payload and the point's resumption token.
        let mut inputs = BTreeMap::new();
        for (point, path) in &paths {
            let site = at_path_mut(&mut body, path);
            let span = site.span;
            inputs.insert(*point, site.resource);
            let ExprKind::Suspend { mut call, .. } =
                std::mem::replace(&mut site.kind, ExprKind::Constant(0))
            else {
                unreachable!("paths lead to suspension points")
            };
            let token = Expr {
                kind: ExprKind::FnValue {
                    function: function_of(*point),
                    captures: captures[point]
                        .iter()
                        .map(|slot| Expr {
                            kind: ExprKind::Move(*slot),
                            ty: locals[*slot].ty,
                            span,
                            resource: None,
                        })
                        .collect(),
                },
                ty: token,
                span,
                resource: None,
            };
            install_token(&mut call, token);
            site.kind = ExprKind::RegionExit {
                value: call,
                finish: false,
                cleanup: cleanup.clone(),
            };
            site.ty = Type::Never;
            site.resource = None;
        }
        // One continuation function per point.
        let outer_live = |slot: usize| !bound.contains(&slot) && after_handle.contains(&slot);
        for point in &order {
            let slots = &captures[point];
            let input_slot = locals.len();
            let mut zipper = Zipper {
                next_local: input_slot + 1,
                flags: Vec::new(),
                span,
            };
            let input = Expr {
                kind: ExprKind::Move(input_slot),
                ty: result,
                span,
                resource: inputs[point],
            };
            let rest = zipper.block(&body, &paths[point], input);
            check_escapes(&rest)?;
            check_outer_writes(&rest, &outer_live, &locals)?;
            let mut cont_locals = locals.clone();
            cont_locals.push(Local {
                ty: result,
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span,
            });
            cont_locals.extend(zipper.flags);
            let mut cont_resources = resources.clone();
            let mut cont_local_resources = local_resources.clone();
            if result_owned {
                cont_resources.push(result);
                cont_local_resources.push(Some(cont_resources.len() - 1));
            } else {
                cont_local_resources.push(None);
            }
            cont_local_resources.resize(cont_locals.len(), None);
            let mut parameter_slots = slots.clone();
            parameter_slots.push(input_slot);
            let parameters = parameter_slots.len();
            let once = matches!(token, Type::Once(_));
            continuations.push(Function {
                name: format!("{name}::resume#{point}"),
                parameters,
                closure: once.then_some(slots.len()),
                capture_refs: vec![false; slots.len()],
                capture_writes: vec![false; slots.len()],
                locals: cont_locals,
                result,
                body: Block {
                    statements: vec![],
                    tail: Some(Box::new(Expr {
                        kind: ExprKind::Region {
                            body: rest,
                            finish: None,
                        },
                        ty: result,
                        span,
                        resource: None,
                    })),
                    ty: result,
                },
                span,
                resources: cont_resources,
                local_resources: cont_local_resources,
                parameter_grades: vec![None; parameters],
                result_grade: None,
                parameter_lifetimes: vec![None; parameters],
                result_lifetime: None,
                lifetime_bounds: BTreeSet::new(),
                declared_lifetimes: BTreeSet::new(),
                index_relations: index_relations.clone(),
                parameter_slots: Some(parameter_slots),
            });
        }
        Ok(ExprKind::Region { body, finish: None })
    };
    let mut lower: Option<&mut dyn FnMut(Box<Suspendable>) -> Result<ExprKind>> = Some(&mut lower);
    replace_target_in_block(&mut program.functions[index].body, target, &mut lower)?;
    for continuation in continuations {
        program.functions.push(continuation);
        program.foreign_functions.push(None);
    }
    Ok(())
}
