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
    let mut context = Context {
        performs: performs(program),
        entries: BTreeMap::new(),
        lowering: BTreeSet::new(),
    };
    let mut index = 0;
    while index < program.functions.len() {
        lower_function(program, &mut context, index)?;
        index += 1;
    }
    Ok(())
}

/// State shared by every lowering step of one program.
struct Context {
    /// Declared operations each original function may perform dynamically
    /// (not handled inside it), by operation id.
    performs: Vec<BTreeSet<usize>>,
    /// Resumable entry of (function, operation): its index and whether it or
    /// anything it awaits allocates a resumption environment.
    entries: BTreeMap<(usize, usize), (usize, bool)>,
    /// Functions whose suspendable bodies are being lowered.
    lowering: BTreeSet<usize>,
}

fn lower_function(program: &mut Executable, context: &mut Context, index: usize) -> Result<()> {
    context.lowering.insert(index);
    while let Some(target) = innermost_in_block(&program.functions[index].body) {
        lower_one(program, context, index, target)?;
    }
    context.lowering.remove(&index);
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
    /// Live when an exit applies the outermost region's finish (the
    /// continuation parameter of a resumable entry).
    finish_live: Slots,
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
            ExprKind::RegionExit { value, finish, .. } => {
                let exit = match self.regions.last() {
                    Some(exit) => exit.clone(),
                    None if *finish => self.finish_live.clone(),
                    None => Slots::new(),
                };
                self.expr(value, &exit)
            }
            ExprKind::TryExit { value, .. } => {
                let mut live = after.clone();
                match self.regions.last() {
                    Some(exit) => live.extend(exit.iter().copied()),
                    None => live.extend(self.finish_live.iter().copied()),
                }
                self.expr(value, &live)
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
            ExprKind::Suspend { point, call, .. } => {
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
            ExprKind::Suspend { point, call, .. } => {
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
    capture_writes: &BTreeMap<usize, Vec<bool>>,
) -> Result<()> {
    fn walk(
        expr: &Expr,
        outer_live: &dyn Fn(usize) -> bool,
        locals: &[Local],
        capture_writes: &BTreeMap<usize, Vec<bool>>,
    ) -> Result<()> {
        // A closure that writes a captured local through a reference writes
        // the continuation's copy too.
        if let ExprKind::FnValue { function, captures } = &expr.kind
            && let Some(writes) = capture_writes.get(function)
        {
            for (capture, writes) in captures.iter().zip(writes) {
                if *writes
                    && let Some(slot) = place_root(capture)
                    && outer_live(slot)
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a resumed continuation cannot write a local of the enclosing function that is used after the 'handle': the continuation runs on its own copy of the value",
                    )
                    .with_note(locals[slot].span, "local declared here"));
                }
            }
        }
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
                result = walk(child, outer_live, locals, capture_writes);
            }
        });
        result
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, outer_live, locals, capture_writes)?;
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, outer_live, locals, capture_writes)?;
    }
    Ok(())
}

/// Locals that hold a closure capturing locals by reference (directly or
/// through moves between locals): the closure's type does not show the
/// borrow, but holding it across a suspension is holding a borrow.
fn by_reference_closures(program: &Executable, body: &Block) -> Slots {
    fn holds(program: &Executable, out: &Slots, value: &Expr) -> bool {
        let mut value = value;
        while let ExprKind::Coerce { value: inner, .. } = &value.kind {
            value = inner;
        }
        match &value.kind {
            ExprKind::FnValue { function, .. } => {
                program.functions[*function].capture_refs.iter().any(|r| *r)
            }
            ExprKind::Local(source) | ExprKind::Move(source) => out.contains(source),
            _ => false,
        }
    }
    fn in_block(block: &Block, program: &Executable, out: &mut Slots, changed: &mut bool) {
        for statement in &block.statements {
            match statement {
                Statement::Let(slot, value) => {
                    if holds(program, out, value) && out.insert(*slot) {
                        *changed = true;
                    }
                    in_expr(value, program, out, changed);
                }
                Statement::Expr(value) => in_expr(value, program, out, changed),
                Statement::Declare(_) => {}
            }
        }
        if let Some(tail) = &block.tail {
            in_expr(tail, program, out, changed);
        }
    }
    fn in_expr(expr: &Expr, program: &Executable, out: &mut Slots, changed: &mut bool) {
        if let ExprKind::Assign(slot, value) = &expr.kind
            && holds(program, out, value)
            && out.insert(*slot)
        {
            *changed = true;
        }
        let mut blocks = Vec::new();
        let mut children = Vec::new();
        block_children(expr, &mut |block| blocks.push(block), &mut |child| {
            children.push(child)
        });
        for block in blocks {
            in_block(block, program, out, changed);
        }
        for child in children {
            in_expr(child, program, out, changed);
        }
    }
    let mut out = Slots::new();
    loop {
        let mut changed = false;
        in_block(body, program, &mut out, &mut changed);
        if !changed {
            break out;
        }
    }
}

/// Closures that write captured locals: function index to per-capture flags.
fn writing_closures(program: &Executable) -> BTreeMap<usize, Vec<bool>> {
    program
        .functions
        .iter()
        .enumerate()
        .filter(|(_, function)| function.capture_writes.iter().any(|w| *w))
        .map(|(index, function)| (index, function.capture_writes.clone()))
        .collect()
}

/// Locals a suspension point's own call borrows: directly (`&v`, `&mut v`,
/// a place reference), plus whether it passes an opaque borrowed value (a
/// view local or a by-reference closure) whose source is unknown.
fn point_borrows(call: &Expr, host: &Host) -> (Slots, bool) {
    fn operand(expr: &Expr, host: &Host, direct: &mut Slots, opaque: &mut bool) {
        match &expr.kind {
            ExprKind::Borrow(slot) | ExprKind::BorrowInit { slot, .. } => {
                direct.insert(*slot);
            }
            ExprKind::BorrowPlace(place) | ExprKind::BorrowField(place) => {
                if let Some(slot) = place_root(place) {
                    direct.insert(slot);
                } else {
                    *opaque = true;
                }
            }
            ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot)
                if host.borrowed.get(*slot).copied().unwrap_or(true)
                    || host.by_reference.contains(slot) =>
            {
                *opaque = true;
            }
            _ => {}
        }
        if expr.ty.is_view() || expr.ty.is_ref() || expr.ty.is_text() {
            *opaque |= !matches!(
                expr.kind,
                ExprKind::Borrow(_) | ExprKind::BorrowInit { .. } | ExprKind::BorrowPlace(_)
            );
        }
        expr.for_each_child(&mut |child| operand(child, host, direct, opaque));
    }
    let mut direct = Slots::new();
    let mut opaque = false;
    let operands: Vec<&Expr> = match &call.kind {
        ExprKind::Coerce { value, .. } => return point_borrows(value, host),
        ExprKind::Call(_, arguments) => arguments.iter().collect(),
        ExprKind::CallIndirect { arguments, .. } => arguments.iter().take(1).collect(),
        ExprKind::DynamicPerform { payload, .. } => vec![payload],
        _ => vec![],
    };
    for argument in operands {
        operand(argument, host, &mut direct, &mut opaque);
    }
    (direct, opaque)
}

/// Replace the `Erased` token argument of a suspension's handler call.
/// Replace the placeholder token of a suspension's handler call: the
/// `Erased` argument of a lexical handler call, or the identity `resume` of
/// a dynamic perform.
fn install_token(call: &mut Expr, token: Expr) {
    match &mut call.kind {
        ExprKind::Coerce { value, .. } => install_token(value, token),
        ExprKind::CallIndirect { arguments, .. } => arguments[1] = token,
        ExprKind::DynamicPerform { resume, .. } => **resume = token,
        _ => unreachable!("a suspension wraps the handler call"),
    }
}

/// The token type a perform point hands to its handler.
fn token_type(call: &Expr, lexical: Type) -> Type {
    match &call.kind {
        ExprKind::Coerce { value, .. } => token_type(value, lexical),
        ExprKind::DynamicPerform { resume, .. } => resume.ty,
        _ => lexical,
    }
}

/// What the machine builder needs from the function that owns a body.
struct Host {
    name: String,
    locals: Vec<Local>,
    resources: Vec<Type>,
    local_resources: Vec<Option<usize>>,
    index_relations: BTreeSet<(usize, usize)>,
    /// Per local: holds a borrow. Missing entries count as borrowed.
    borrowed: Vec<bool>,
    /// Per local: copyable. Missing entries count as not copyable.
    copyable: Vec<bool>,
    /// Locals the owning function reads after the body.
    after: Slots,
    /// Locals holding a closure that captures by reference.
    by_reference: Slots,
    /// Closures that write captured locals, by function index.
    capture_writes: BTreeMap<usize, Vec<bool>>,
}

/// What the machine builder needs about one suspendable body.
struct Spec {
    /// The final answer type: the operation result.
    result: Type,
    /// Token type of a lexical perform point.
    token: Type,
    multishot: bool,
    handler_writes: Vec<usize>,
    /// Effect row at the handle; `None` for a resumable entry, whose
    /// allocation is checked at the handle that awaits it.
    effects: Option<u16>,
    /// An awaited resumable entry allocates resumption environments.
    awaited_allocates: bool,
    /// Continuation parameter of a resumable entry; exits that finish apply
    /// it.
    finish: Option<usize>,
    /// Resumable entry index and continuation token type per awaited callee.
    entries: BTreeMap<usize, (usize, Type)>,
    /// The handler, when it is a known noncapturing function that only calls
    /// its resumption directly: multishot points with captured values call a
    /// specialization of it.
    multishot_handler: Option<MultishotHandler>,
    span: Span,
}

struct Built {
    /// The body had suspension points (otherwise it is returned unchanged).
    points: bool,
    body: Block,
    continuations: Vec<Function>,
    allocates: bool,
}

/// Turn a suspendable body into a region whose points leave it with the
/// handler's (or the awaited entry's) result, plus one continuation function
/// per point, numbered from `first_function`.
fn build(
    host: &Host,
    spec: &Spec,
    mut body: Block,
    first_function: usize,
    owns: &dyn Fn(Type) -> bool,
) -> Result<Built> {
    let paths = point_paths(&body)?;
    if paths.is_empty() {
        return Ok(Built {
            points: false,
            body,
            continuations: Vec::new(),
            allocates: false,
        });
    }
    let locals = &host.locals;
    let finish_live = spec.finish.into_iter().collect::<Slots>();
    let mut liveness = Live {
        finish_live: finish_live.clone(),
        ..Live::default()
    };
    liveness.block(&body, &finish_live);
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
    // Suspension rules (design section 6, as built in section 14).
    let mut point_spans = BTreeMap::new();
    for (point, path) in &paths {
        point_spans.insert(*point, at_path_mut(&mut body, path).span);
    }
    // The point's own call may borrow a local that its continuation also
    // captures: the callee (or handler) would then use the original while
    // the continuation works on its moved copy.
    for (point, path) in &paths {
        let site = at_path_mut(&mut body, path);
        let ExprKind::Suspend { call, .. } = &site.kind else {
            unreachable!("paths lead to suspension points")
        };
        let (direct, opaque) = point_borrows(call, host);
        let relevant = captures[point]
            .iter()
            .copied()
            .filter(|slot| Some(*slot) != spec.finish && !matches!(locals[*slot].ty, Type::Fn(_)))
            .collect::<Vec<_>>();
        let conflict = relevant
            .iter()
            .find(|slot| direct.contains(slot))
            .or_else(|| relevant.first().filter(|_| opaque));
        if let Some(slot) = conflict {
            return Err(Diagnostic::new(
                point_spans[point],
                "this call can suspend while it borrows a value that is still used after it; the resumed code would work on a moved copy. Finish using the borrowed value before the call, or pass an owned value",
            )
            .with_note(locals[*slot].span, "value used after the call declared here"));
        }
    }
    for (point, slots) in &captures {
        let at = point_spans[point];
        for slot in slots {
            let local = &locals[*slot];
            if host.borrowed.get(*slot).copied().unwrap_or(true) || host.by_reference.contains(slot)
            {
                return Err(Diagnostic::new(
                    at,
                    "a borrowed value (slice view, text view, reference, borrowed record, or task handle) cannot stay live across a non-tail 'perform'; end the borrow before the perform or pass an owned value",
                )
                .with_note(local.span, "borrowed value declared here"));
            }
            if spec.handler_writes.contains(slot) {
                return Err(Diagnostic::new(
                    at,
                    "a local the handler writes through its capture cannot stay live across a non-tail 'perform': the resumption would hold a stale copy",
                )
                .with_note(local.span, "local declared here"));
            }
            if !bound.contains(slot)
                && !host.copyable.get(*slot).copied().unwrap_or(false)
                && host.after.contains(slot)
            {
                return Err(Diagnostic::new(
                    at,
                    "this value is used after the 'handle', but the non-tail 'perform' moves it into the resumption; use it only inside the handled body or after it is no longer needed there",
                )
                .with_note(local.span, "value declared here"));
            }
        }
        if spec.multishot && !slots.is_empty() {
            if spec.multishot_handler.is_none() {
                return Err(Diagnostic::new(
                    at,
                    "multishot resumption requires a continuation with no captured values unless the handler is a lambda (or function name) without captures that only calls its resumption directly; the copyable resumption token cannot own an environment",
                )
                .with_note(locals[slots[0]].span, "captured value declared here"));
            }
            if let Some(slot) = slots.iter().find(|slot| {
                !host.copyable.get(**slot).copied().unwrap_or(false)
                    || locals[**slot].grade.is_some()
            }) {
                return Err(Diagnostic::new(
                    at,
                    "multishot resumption copies the continuation's live values for each resume, but this value is owned, linear, or graded and cannot be copied; keep it out of the multishot continuation or use a one-shot 'linear once fn' handler",
                )
                .with_note(locals[*slot].span, "captured value declared here"));
            }
        }
    }
    let effects_check = |allocates: bool| -> Result<()> {
        let Some(effects) = spec.effects else {
            return Ok(());
        };
        if !(allocates || spec.awaited_allocates) {
            return Ok(());
        }
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
                spec.span,
                format!(
                    "operation requires effects {{{}}}; add them to the function signature (a non-tail 'perform' with live values allocates its resumption)",
                    names.join(", ")
                ),
            ));
        }
        Ok(())
    };
    // A point whose continuation only passes its value to the entry's
    // continuation parameter `k` (it is in tail position and nothing else is
    // live) resumes through `k` itself: no environment, no function.
    let tails = paths
        .iter()
        .filter(|(_, path)| tail_path(&body, path))
        .map(|(point, _)| *point)
        .collect::<BTreeSet<_>>();
    let direct = |point: usize, token: Type| {
        spec.finish.is_some_and(|k| {
            captures[&point] == [k] && locals[k].ty == token && tails.contains(&point)
        })
    };
    // Function index of each point's continuation.
    let mut order = Vec::new();
    let mut tokens = BTreeMap::new();
    for (point, path) in &paths {
        let site = at_path_mut(&mut body, path);
        let ExprKind::Suspend { call, callee, .. } = &site.kind else {
            unreachable!("paths lead to suspension points")
        };
        let token = match callee {
            Some(callee) => spec.entries[callee].1,
            None => token_type(call, spec.token),
        };
        tokens.insert(*point, token);
    }
    for point in paths.keys() {
        if !direct(*point, tokens[point]) {
            order.push(*point);
        }
    }
    // A multishot point with live values passes them by value to a
    // specialization of the handler instead of building an environment.
    let specialized = order
        .iter()
        .copied()
        .filter(|point| spec.multishot && !captures[point].is_empty())
        .collect::<Vec<_>>();
    let allocates = order
        .iter()
        .any(|point| !captures[point].is_empty() && !specialized.contains(point));
    effects_check(allocates)?;
    let function_of = |point: usize| {
        first_function + order.iter().position(|p| *p == point).expect("known point")
    };
    let specialization_of = |point: usize| {
        first_function
            + order.len()
            + specialized
                .iter()
                .position(|p| *p == point)
                .expect("known point")
    };
    let cleanup = resources_in(&body, &host.local_resources);
    // Replace every point by an exit whose value is the handler call (or the
    // awaited entry call) with the point's resumption token.
    let mut inputs = BTreeMap::new();
    for (point, path) in &paths {
        let site = at_path_mut(&mut body, path);
        let span = site.span;
        inputs.insert(*point, (site.resource, site.ty));
        let ExprKind::Suspend {
            mut call, callee, ..
        } = std::mem::replace(&mut site.kind, ExprKind::Constant(0))
        else {
            unreachable!("paths lead to suspension points")
        };
        let token_ty = tokens[point];
        if specialized.contains(point) {
            let environment = captures[point]
                .iter()
                .map(|slot| Expr {
                    kind: ExprKind::Local(*slot),
                    ty: locals[*slot].ty,
                    span,
                    resource: None,
                })
                .collect();
            call_specialization(&mut call, specialization_of(*point), environment);
            site.kind = ExprKind::RegionExit {
                value: call,
                finish: false,
                cleanup: cleanup.clone(),
            };
            site.ty = Type::Never;
            site.resource = None;
            continue;
        }
        let token = if direct(*point, token_ty) {
            Expr {
                kind: ExprKind::Move(spec.finish.expect("direct points need k")),
                ty: token_ty,
                span,
                resource: None,
            }
        } else {
            Expr {
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
                ty: token_ty,
                span,
                resource: None,
            }
        };
        match callee {
            Some(callee) => {
                let ExprKind::Call(target, arguments) = &mut call.kind else {
                    unreachable!("an await point wraps a direct call")
                };
                *target = crate::executable::Target::Function(spec.entries[&callee].0);
                arguments.push(token);
                call.ty = spec.result;
            }
            None => install_token(&mut call, token),
        }
        site.kind = ExprKind::RegionExit {
            value: call,
            finish: false,
            cleanup: cleanup.clone(),
        };
        site.ty = Type::Never;
        site.resource = None;
    }
    // One continuation function per point.
    let outer_live = |slot: usize| !bound.contains(&slot) && host.after.contains(&slot);
    let finish = |span: Span| {
        spec.finish.map(|slot| {
            Box::new(Expr {
                kind: ExprKind::Move(slot),
                ty: locals[slot].ty,
                span,
                resource: None,
            })
        })
    };
    let mut continuations = Vec::new();
    for point in &order {
        let slots = &captures[point];
        let (input_resource, input_ty) = inputs[point];
        let input_slot = locals.len();
        let mut zipper = Zipper {
            next_local: input_slot + 1,
            flags: Vec::new(),
            span: spec.span,
        };
        let input = Expr {
            kind: ExprKind::Move(input_slot),
            ty: input_ty,
            span: spec.span,
            resource: input_resource,
        };
        let rest = zipper.block(&body, &paths[point], input);
        check_escapes(&rest)?;
        check_outer_writes(&rest, &outer_live, locals, &host.capture_writes)?;
        let mut cont_locals = locals.clone();
        cont_locals.push(Local {
            ty: input_ty,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span: spec.span,
        });
        cont_locals.extend(zipper.flags);
        let mut cont_resources = host.resources.clone();
        let mut cont_local_resources = host.local_resources.clone();
        if owns(input_ty) {
            cont_resources.push(input_ty);
            cont_local_resources.push(Some(cont_resources.len() - 1));
        } else {
            cont_local_resources.push(None);
        }
        cont_local_resources.resize(cont_locals.len(), None);
        let mut parameter_slots = slots.clone();
        parameter_slots.push(input_slot);
        let parameters = parameter_slots.len();
        continuations.push(Function {
            name: format!("{}::resume#{point}", host.name),
            parameters,
            // Once tokens carry an environment word even without captures;
            // a capture-free multishot token is a plain code pointer.
            closure: matches!(tokens[point], Type::Once(_)).then_some(slots.len()),
            capture_refs: vec![false; slots.len()],
            capture_writes: vec![false; slots.len()],
            locals: cont_locals,
            result: spec.result,
            body: Block {
                statements: vec![],
                tail: Some(Box::new(Expr {
                    kind: ExprKind::Region {
                        body: rest,
                        finish: finish(spec.span),
                    },
                    ty: spec.result,
                    span: spec.span,
                    resource: None,
                })),
                ty: spec.result,
            },
            span: spec.span,
            resources: cont_resources,
            local_resources: cont_local_resources,
            parameter_grades: vec![None; parameters],
            result_grade: None,
            parameter_lifetimes: vec![None; parameters],
            result_lifetime: None,
            lifetime_bounds: BTreeSet::new(),
            declared_lifetimes: BTreeSet::new(),
            index_relations: host.index_relations.clone(),
            parameter_slots: Some(parameter_slots),
            local_borrowed: vec![],
            local_copyable: vec![],
        });
    }
    // Handler specializations: `resume(y)` calls the point's continuation
    // directly with copies of the captured values.
    for point in &specialized {
        let handler = spec
            .multishot_handler
            .as_ref()
            .expect("checked above for captured multishot points");
        let mut function = handler.function.clone();
        let mut environment = Vec::new();
        for slot in &captures[point] {
            environment.push(function.locals.len());
            function.locals.push(Local {
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                ..locals[*slot]
            });
            function.local_resources.push(None);
        }
        let continuation = function_of(*point);
        rewrite_resume_calls(&mut function.body, handler.token, &|span, argument| {
            let mut arguments = environment
                .iter()
                .zip(&captures[point])
                .map(|(slot, outer)| Expr {
                    kind: ExprKind::Local(*slot),
                    ty: locals[*outer].ty,
                    span,
                    resource: None,
                })
                .collect::<Vec<_>>();
            arguments.push(argument);
            ExprKind::Call(crate::executable::Target::Function(continuation), arguments)
        });
        let mut parameter_slots = vec![handler.payload];
        parameter_slots.extend(environment.iter().copied());
        let mut parameter_grades = vec![function.parameter_grades.first().copied().flatten()];
        parameter_grades.resize(parameter_slots.len(), None);
        function.name = format!("{}::multishot#{point}", function.name);
        function.parameters = parameter_slots.len();
        function.parameter_grades = parameter_grades;
        function.parameter_lifetimes = vec![None; parameter_slots.len()];
        function.parameter_slots = Some(parameter_slots);
        function.local_borrowed = vec![];
        function.local_copyable = vec![];
        continuations.push(function);
    }
    Ok(Built {
        points: true,
        body,
        continuations,
        allocates,
    })
}

fn empty_block() -> Block {
    Block {
        statements: vec![],
        tail: None,
        ty: Type::Unit,
    }
}

/// Await points in a suspendable body: callees whose resumable entries it
/// needs.
fn awaited_callees(block: &Block, out: &mut BTreeSet<usize>) {
    fn walk(expr: &Expr, out: &mut BTreeSet<usize>) {
        if let ExprKind::Suspend {
            callee: Some(callee),
            ..
        } = &expr.kind
        {
            out.insert(*callee);
        }
        if !matches!(expr.kind, ExprKind::Suspendable(_)) {
            expr.for_each_child(&mut |child| walk(child, out));
        }
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, out);
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, out);
    }
}

fn lower_one(
    program: &mut Executable,
    context: &mut Context,
    index: usize,
    target: *const Suspendable,
) -> Result<()> {
    let (operation, result, awaited, multishot) = {
        let suspendable = find_in_block(&program.functions[index].body, target)
            .expect("target suspendable exists");
        let mut awaited = BTreeSet::new();
        awaited_callees(&suspendable.body, &mut awaited);
        (
            suspendable.operation,
            suspendable.result,
            awaited,
            suspendable
                .multishot
                .then_some(suspendable.handler_function)
                .flatten(),
        )
    };
    // A multishot handler is specialized from its lowered body.
    let multishot_handler = match multishot {
        Some(handler) if !context.lowering.contains(&handler) => {
            lower_function(program, context, handler)?;
            multishot_handler(program, handler)
        }
        _ => None,
    };
    // Resumable entries first: building one may lower other functions and
    // append functions, but never moves this function's body.
    let mut entries = BTreeMap::new();
    let mut awaited_allocates = false;
    for callee in awaited {
        let operation = operation.expect("await points only exist for declared operations");
        let (entry, allocates) = resumable_entry(program, context, callee, operation, result)?;
        let input = program.functions[callee].result;
        let token = Type::Once(function_type(program, input, result));
        entries.insert(callee, (entry, token));
        awaited_allocates |= allocates;
    }
    if let Some(operation) = operation {
        let suspendable = find_in_block(&program.functions[index].body, target)
            .expect("target suspendable exists");
        check_unresumable_paths(program, context, &suspendable.body, operation)?;
    }
    let function = &program.functions[index];
    let after = {
        let mut live = Live {
            target: Some(target),
            ..Live::default()
        };
        live.block(&function.body, &Slots::new());
        live.target_after
    };
    let host = Host {
        name: function.name.clone(),
        locals: function.locals.clone(),
        resources: function.resources.clone(),
        local_resources: function.local_resources.clone(),
        index_relations: function.index_relations.clone(),
        borrowed: function.local_borrowed.clone(),
        copyable: function.local_copyable.clone(),
        after,
        by_reference: by_reference_closures(program, &function.body),
        capture_writes: writing_closures(program),
    };
    let mut body = std::mem::replace(&mut program.functions[index].body, empty_block());
    let first_function = program.functions.len();
    let mut continuations = Vec::new();
    let owns = |ty: Type| program.owns(ty);
    let mut lower = |suspendable: Box<Suspendable>| -> Result<ExprKind> {
        let Suspendable {
            result,
            token,
            multishot,
            handler_writes,
            effects,
            body,
            span,
            ..
        } = *suspendable;
        let spec = Spec {
            result,
            token,
            multishot,
            handler_writes,
            effects: Some(effects),
            awaited_allocates,
            finish: None,
            entries: entries.clone(),
            multishot_handler: multishot_handler.clone(),
            span,
        };
        let built = build(&host, &spec, body, first_function, &owns)?;
        continuations = built.continuations;
        if !built.points {
            return Ok(ExprKind::Block(built.body));
        }
        Ok(ExprKind::Region {
            body: built.body,
            finish: None,
        })
    };
    let mut lower: Option<&mut dyn FnMut(Box<Suspendable>) -> Result<ExprKind>> = Some(&mut lower);
    let lowered = replace_target_in_block(&mut body, target, &mut lower);
    program.functions[index].body = body;
    lowered?;
    for continuation in continuations {
        program.functions.push(continuation);
        program.foreign_functions.push(None);
    }
    Ok(())
}

/// Intern the linear one-shot callable type `linear once fn(input) -> result`.
fn function_type(program: &mut Executable, input: Type, result: Type) -> usize {
    let wanted = crate::runtime_types::FunctionType {
        parameters: vec![input],
        result,
        effects: 0,
        parameter_grades: vec![None],
        result_grade: None,
        once: true,
        linear: true,
        borrows: crate::runtime_types::BorrowSig::default(),
    };
    if let Some(index) = program
        .function_types
        .iter()
        .position(|existing| *existing == wanted)
    {
        return index;
    }
    program.function_types.push(wanted);
    program.function_types.len() - 1
}

/// Operations each function may perform dynamically without handling them
/// itself: a least fixed point over the call graph of the checked IR.
fn performs(program: &Executable) -> Vec<BTreeSet<usize>> {
    let bits = &program.effect_bits;
    let row_operations = |effects: u16| {
        bits.iter()
            .enumerate()
            .filter(|(_, bit)| **bit != 0 && effects & **bit != 0)
            .map(|(operation, _)| operation)
            .collect::<BTreeSet<_>>()
    };
    let callable_effects = |ty: Type| match ty {
        Type::Fn(id) | Type::Once(id) => program.function_types[id].effects,
        _ => 0,
    };
    let mut result = vec![BTreeSet::new(); program.functions.len()];
    loop {
        let mut changed = false;
        for (index, function) in program.functions.iter().enumerate() {
            let mut found = BTreeSet::new();
            fn walk(
                expr: &Expr,
                masked: &BTreeSet<usize>,
                current: &[BTreeSet<usize>],
                program: &Executable,
                row_operations: &dyn Fn(u16) -> BTreeSet<usize>,
                callable_effects: &dyn Fn(Type) -> u16,
                found: &mut BTreeSet<usize>,
            ) {
                let mut add = |operations: &BTreeSet<usize>| {
                    found.extend(operations.difference(masked).copied());
                };
                match &expr.kind {
                    ExprKind::DynamicPerform { operation, .. } => {
                        add(&BTreeSet::from([*operation]));
                    }
                    ExprKind::Call(
                        crate::executable::Target::Function(callee)
                        | crate::executable::Target::ObjectFunction {
                            function: callee, ..
                        },
                        _,
                    ) => add(&current[*callee]),
                    ExprKind::Call(crate::executable::Target::DynCall { spec }, _) => {
                        let spec = &program.dyn_calls[*spec];
                        for member in &program.dyn_members[spec.object] {
                            if let Some(function) = member.methods.get(&spec.key) {
                                add(&current[*function]);
                            }
                        }
                    }
                    ExprKind::Call(crate::executable::Target::UnionBorrowCall { spec }, _) => {
                        for (_, _, function) in &program.union_calls[*spec].members {
                            add(&current[*function]);
                        }
                    }
                    ExprKind::CallIndirect { callee, .. } => {
                        add(&row_operations(callable_effects(callee.ty)))
                    }
                    ExprKind::TaskScope { body, .. } => {
                        add(&row_operations(callable_effects(body.ty)))
                    }
                    ExprKind::VecMap { callbacks, .. } => {
                        for callback in callbacks {
                            add(&row_operations(callable_effects(callback.ty)));
                        }
                    }
                    _ => {}
                }
                let masked = match &expr.kind {
                    ExprKind::HandlerPush { operation, .. } => {
                        let mut masked = masked.clone();
                        masked.insert(*operation);
                        std::borrow::Cow::Owned(masked)
                    }
                    _ => std::borrow::Cow::Borrowed(masked),
                };
                expr.for_each_child(&mut |child| {
                    walk(
                        child,
                        &masked,
                        current,
                        program,
                        row_operations,
                        callable_effects,
                        found,
                    )
                });
            }
            let masked = BTreeSet::new();
            let block = &function.body;
            for statement in &block.statements {
                if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                    walk(
                        value,
                        &masked,
                        &result,
                        program,
                        &row_operations,
                        &callable_effects,
                        &mut found,
                    );
                }
            }
            if let Some(tail) = &block.tail {
                walk(
                    tail,
                    &masked,
                    &result,
                    program,
                    &row_operations,
                    &callable_effects,
                    &mut found,
                );
            }
            if found != result[index] {
                result[index] = found;
                changed = true;
            }
        }
        if !changed {
            break result;
        }
    }
}

/// Reject, in code resumed by a non-tail handler for `operation`, every way
/// to perform it that cannot be resumed: calls through function values,
/// trait objects, task scopes, and vector callbacks. Code under a nested
/// handler for the same operation belongs to that handler.
fn check_unresumable_paths(
    program: &Executable,
    context: &Context,
    block: &Block,
    operation: usize,
) -> Result<()> {
    fn walk(expr: &Expr, program: &Executable, context: &Context, operation: usize) -> Result<()> {
        let bit = program.effect_bits[operation];
        let callable = |ty: Type| match ty {
            Type::Fn(id) | Type::Once(id) => program.function_types[id].effects & bit != 0,
            _ => false,
        };
        let performs = |function: usize| {
            context
                .performs
                .get(function)
                .is_some_and(|set| set.contains(&operation))
        };
        let unresumable = match &expr.kind {
            ExprKind::HandlerPush {
                operation: inner, ..
            } if *inner == operation => {
                return Ok(());
            }
            ExprKind::Suspend { .. } => false,
            ExprKind::CallIndirect { callee, .. } => callable(callee.ty),
            ExprKind::TaskScope { body, .. } => callable(body.ty),
            ExprKind::VecMap { callbacks, .. } => callbacks.iter().any(|c| callable(c.ty)),
            ExprKind::Call(crate::executable::Target::ObjectFunction { function, .. }, _) => {
                performs(*function)
            }
            ExprKind::Call(crate::executable::Target::DynCall { spec }, _) => {
                let spec = &program.dyn_calls[*spec];
                program.dyn_members[spec.object].iter().any(|member| {
                    member
                        .methods
                        .get(&spec.key)
                        .is_some_and(|function| performs(*function))
                })
            }
            ExprKind::Call(crate::executable::Target::UnionBorrowCall { spec }, _) => program
                .union_calls[*spec]
                .members
                .iter()
                .any(|(_, _, function)| performs(*function)),
            _ => false,
        };
        if unresumable {
            return Err(Diagnostic::new(
                expr.span,
                "this call may perform an operation handled by a handler with code after 'resume', but it goes through a function value, trait object, task scope, or vector callback, which cannot be resumed; call a named function instead",
            ));
        }
        if let ExprKind::Suspend { call, .. } = &expr.kind {
            // The point itself is resumable; its operands still need checking.
            let mut result = Ok(());
            call.for_each_child(&mut |child| {
                if result.is_ok() {
                    result = walk(child, program, context, operation);
                }
            });
            return result;
        }
        let mut result = Ok(());
        expr.for_each_child(&mut |child| {
            if result.is_ok() {
                result = walk(child, program, context, operation);
            }
        });
        result
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, program, context, operation)?;
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, program, context, operation)?;
    }
    Ok(())
}

/// Temporaries for normalizing a resumable entry body after ownership: an
/// owned temporary gets its own drop resource.
struct EntryTemporaries<'a> {
    locals: &'a mut Vec<Local>,
    resources: &'a mut Vec<Type>,
    local_resources: &'a mut Vec<Option<usize>>,
    borrowed: &'a mut Vec<bool>,
    copyable: &'a mut Vec<bool>,
    owns: &'a dyn Fn(Type) -> bool,
}

impl crate::executable::anf::Temporaries for EntryTemporaries<'_> {
    fn bind(&mut self, value: Expr, out: &mut Vec<Statement>) -> Result<Expr> {
        let ty = value.ty;
        let span = value.span;
        let owned = (self.owns)(ty);
        // An owned operand that is neither moved nor a fresh temporary is a
        // place read of storage another binding owns; binding it would
        // create a second owner.
        if owned && !matches!(value.kind, ExprKind::Move(_)) && value.resource.is_none() {
            return Err(Diagnostic::new(
                span,
                "this operand reads owned storage in place and cannot be evaluated before a resumable call; bind it with 'let' first",
            ));
        }
        let slot = self.locals.len();
        self.locals.push(Local {
            ty,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span,
        });
        if owned {
            self.resources.push(ty);
            self.local_resources.push(Some(self.resources.len() - 1));
        } else {
            self.local_resources.push(None);
        }
        // Without the checker's type tables a temporary is assumed to hold
        // a borrow unless it is a scalar or an owning handle, so the
        // suspension rules stay conservative.
        self.borrowed.push(!(owned || is_plain_scalar(ty)));
        self.copyable.push(!owned && is_plain_scalar(ty));
        out.push(Statement::Let(slot, value));
        Ok(Expr {
            kind: if owned {
                ExprKind::Move(slot)
            } else {
                ExprKind::Local(slot)
            },
            ty,
            span,
            resource: None,
        })
    }
    fn flag(&mut self, span: Span) -> Result<usize> {
        let slot = self.locals.len();
        self.locals.push(Local {
            ty: Type::Bool,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span,
        });
        self.local_resources.push(None);
        self.borrowed.push(false);
        self.copyable.push(true);
        Ok(slot)
    }
}

fn is_plain_scalar(ty: Type) -> bool {
    ty.scalar_carrier().is_some()
        || matches!(
            ty,
            Type::Bool | Type::Unit | Type::Char | Type::I64 | Type::Fn(_)
        )
}

/// Mark the suspension points of a resumable entry for `operation`: dynamic
/// performs of it and direct calls of functions that may perform it, outside
/// any nested handler for the same operation.
fn mark_entry_points(
    expr: &mut Expr,
    operation: usize,
    performs: &[BTreeSet<usize>],
    points: &mut usize,
    awaited: &mut BTreeSet<usize>,
    nested: bool,
) -> Result<()> {
    let nested = match &expr.kind {
        ExprKind::HandlerPush {
            operation: inner, ..
        } if *inner == operation => return Ok(()),
        ExprKind::HandlerPush { .. } | ExprKind::Region { .. } | ExprKind::Suspendable(_) => true,
        _ => nested,
    };
    let mut result = Ok(());
    expr.for_each_child_mut(&mut |child| {
        if result.is_ok() {
            result = mark_entry_points(child, operation, performs, points, awaited, nested);
        }
    });
    result?;
    let callee = match &expr.kind {
        ExprKind::DynamicPerform {
            operation: performed,
            ..
        } if *performed == operation => None,
        ExprKind::Call(crate::executable::Target::Function(callee), _)
            if performs
                .get(*callee)
                .is_some_and(|set| set.contains(&operation)) =>
        {
            Some(*callee)
        }
        _ => return Ok(()),
    };
    if nested {
        return Err(Diagnostic::new(
            expr.span,
            "a perform inside a nested handler or handled body cannot be resumed by an outer handler with code after 'resume'; perform it outside the nested 'handle'",
        ));
    }
    *points += 1;
    let span = expr.span;
    let ty = expr.ty;
    let mut call = std::mem::replace(
        expr,
        Expr {
            kind: ExprKind::Constant(0),
            ty,
            span,
            resource: None,
        },
    );
    // The point's value is the call's value: move its drop resource to the
    // point so the continuation input inherits it.
    expr.resource = call.resource.take();
    if let Some(callee) = callee {
        awaited.insert(callee);
    }
    expr.kind = ExprKind::Suspend {
        point: *points,
        call: Box::new(call),
        callee,
    };
    Ok(())
}

/// In a resumable entry, `return e` continues the caller with `e`, and the
/// error path of `?` does the same with the converted error.
fn rewrite_entry_exits(expr: &mut Expr, cleanup: &[usize], nested: bool) -> Result<()> {
    let nested = nested || matches!(expr.kind, ExprKind::Region { .. });
    let mut result = Ok(());
    expr.for_each_child_mut(&mut |child| {
        if result.is_ok() {
            result = rewrite_entry_exits(child, cleanup, nested);
        }
    });
    result?;
    let span = expr.span;
    match std::mem::replace(&mut expr.kind, ExprKind::Constant(0)) {
        ExprKind::Return(_) | ExprKind::Try { .. } if nested => Err(Diagnostic::new(
            span,
            "'return' or '?' inside a handled body of a function that is resumed by an outer handler is not supported",
        )),
        ExprKind::Return(value) => {
            expr.kind = ExprKind::RegionExit {
                value,
                finish: true,
                cleanup: cleanup.to_vec(),
            };
            Ok(())
        }
        ExprKind::Try {
            value,
            input,
            output,
        } => {
            expr.kind = ExprKind::TryExit {
                value,
                input,
                output,
                cleanup: cleanup.to_vec(),
            };
            Ok(())
        }
        kind => {
            expr.kind = kind;
            Ok(())
        }
    }
}

fn for_each_value_mut(block: &mut Block, f: &mut dyn FnMut(&mut Expr) -> Result<()>) -> Result<()> {
    for statement in &mut block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            f(value)?;
        }
    }
    if let Some(tail) = block.tail.as_deref_mut() {
        f(tail)?;
    }
    Ok(())
}

/// The resumable entry of `function` for `operation`: the same body taking
/// one more parameter, the caller's continuation `k`. Performs of the
/// operation and calls of functions that may perform it become suspension
/// points; returning `v` (normally, by `return`, or by `?`) calls `k(v)`;
/// the entry's result is the handled body's final answer.
fn resumable_entry(
    program: &mut Executable,
    context: &mut Context,
    function: usize,
    operation: usize,
    result: Type,
) -> Result<(usize, bool)> {
    if let Some(entry) = context.entries.get(&(function, operation)) {
        return Ok(*entry);
    }
    {
        let source = &program.functions[function];
        if context.lowering.contains(&function) {
            return Err(Diagnostic::new(
                source.span,
                "a function that installs a handler with code after 'resume' cannot be called back through that handler's resumption; split the recursive call out of the handled body",
            ));
        }
        if source.closure.is_some()
            || source.parameter_slots.is_some()
            || program.foreign_functions[function].is_some()
            || source.result_grade.is_some_and(Grade::is_zero)
            || source
                .parameter_grades
                .iter()
                .any(|grade| grade.is_some_and(Grade::is_zero))
        {
            return Err(Diagnostic::new(
                source.span,
                "this function performs an operation handled with code after 'resume', but it has erased (@[0]) parameters or result, so it has no resumable form",
            ));
        }
    }
    lower_function(program, context, function)?;
    let index = program.functions.len();
    let source = program.functions[function].clone();
    program.functions.push(source.clone());
    program.foreign_functions.push(None);
    context.entries.insert((function, operation), (index, true));
    let continuation = Type::Once(function_type(program, source.result, result));
    let mut locals = source.locals.clone();
    let mut resources = source.resources.clone();
    let mut local_resources = source.local_resources.clone();
    let mut borrowed = source.local_borrowed.clone();
    let mut copyable = source.local_copyable.clone();
    borrowed.resize(locals.len(), true);
    copyable.resize(locals.len(), false);
    let k = locals.len();
    locals.push(Local {
        ty: continuation,
        mutable: false,
        linear: true,
        pinned: false,
        grade: None,
        span: source.span,
    });
    resources.push(continuation);
    local_resources.push(Some(resources.len() - 1));
    borrowed.push(false);
    copyable.push(false);
    let mut body = source.body.clone();
    let mut points = 0;
    let mut awaited = BTreeSet::new();
    for_each_value_mut(&mut body, &mut |value| {
        mark_entry_points(
            value,
            operation,
            &context.performs,
            &mut points,
            &mut awaited,
            false,
        )
    })?;
    check_unresumable_paths(program, context, &body, operation)?;
    let mut entries = BTreeMap::new();
    let mut awaited_allocates = false;
    for callee in awaited {
        let (entry, allocates) = resumable_entry(program, context, callee, operation, result)?;
        let input = program.functions[callee].result;
        let token = Type::Once(function_type(program, input, result));
        entries.insert(callee, (entry, token));
        awaited_allocates |= allocates;
    }
    {
        let owns = |ty: Type| program.owns(ty);
        let mut temps = EntryTemporaries {
            locals: &mut locals,
            resources: &mut resources,
            local_resources: &mut local_resources,
            borrowed: &mut borrowed,
            copyable: &mut copyable,
            owns: &owns,
        };
        crate::executable::anf::Anf { temps: &mut temps }.block(&mut body)?;
    }
    let cleanup = resources_in(&body, &local_resources);
    for_each_value_mut(&mut body, &mut |value| {
        rewrite_entry_exits(value, &cleanup, false)
    })?;
    let host = Host {
        name: format!("{}::resumable", source.name),
        locals,
        resources,
        local_resources,
        index_relations: source.index_relations.clone(),
        borrowed,
        copyable,
        after: Slots::new(),
        by_reference: by_reference_closures(program, &body),
        capture_writes: writing_closures(program),
    };
    let spec = Spec {
        result,
        token: Type::Unit,
        multishot: false,
        handler_writes: vec![],
        effects: None,
        awaited_allocates,
        finish: Some(k),
        entries,
        multishot_handler: None,
        span: source.span,
    };
    let first_function = program.functions.len();
    let built = {
        let owns = |ty: Type| program.owns(ty);
        build(&host, &spec, body, first_function, &owns)?
    };
    let allocates = built.allocates || awaited_allocates;
    let mut parameter_slots = (0..source.parameters).collect::<Vec<_>>();
    parameter_slots.push(k);
    let mut parameter_grades = source.parameter_grades.clone();
    parameter_grades.resize(source.parameters, None);
    parameter_grades.push(None);
    let mut parameter_lifetimes = source.parameter_lifetimes.clone();
    parameter_lifetimes.resize(source.parameters, None);
    parameter_lifetimes.push(None);
    let finish = Expr {
        kind: ExprKind::Move(k),
        ty: continuation,
        span: source.span,
        resource: None,
    };
    program.functions[index] = Function {
        name: host.name.clone(),
        parameters: source.parameters + 1,
        closure: None,
        capture_refs: vec![],
        capture_writes: vec![],
        locals: host.locals,
        result,
        body: Block {
            statements: vec![],
            tail: Some(Box::new(Expr {
                kind: ExprKind::Region {
                    body: built.body,
                    finish: Some(Box::new(finish)),
                },
                ty: result,
                span: source.span,
                resource: None,
            })),
            ty: result,
        },
        span: source.span,
        resources: host.resources,
        local_resources: host.local_resources,
        parameter_grades,
        result_grade: None,
        parameter_lifetimes,
        result_lifetime: None,
        lifetime_bounds: source.lifetime_bounds.clone(),
        declared_lifetimes: source.declared_lifetimes.clone(),
        index_relations: source.index_relations.clone(),
        parameter_slots: Some(parameter_slots),
        local_borrowed: host.borrowed,
        local_copyable: host.copyable,
    };
    for continuation in built.continuations {
        program.functions.push(continuation);
        program.foreign_functions.push(None);
    }
    context
        .entries
        .insert((function, operation), (index, allocates));
    Ok((index, allocates))
}

/// Whether the point at `path` is in tail position of the body: each step
/// leaves through a block tail or a branch, never through a loop.
fn tail_path(body: &Block, path: &[Step]) -> bool {
    fn block(block: &Block, path: &[Step]) -> bool {
        match path.first() {
            Some(Step::Stmt(index)) if *index == block.statements.len() => {
                tail(block.tail.as_deref().expect("path to the tail"), &path[1..])
            }
            _ => false,
        }
    }
    fn tail(expr: &Expr, path: &[Step]) -> bool {
        match (path.first(), &expr.kind) {
            (None, _) => true,
            (Some(Step::Body), ExprKind::Block(inner))
            | (Some(Step::Then), ExprKind::If(_, inner, _))
            | (Some(Step::Else), ExprKind::If(_, _, inner)) => block(inner, &path[1..]),
            (Some(Step::Arm(index)), ExprKind::Match(_, arms)) => {
                tail(&arms[*index].body, &path[1..])
            }
            _ => false,
        }
    }
    block(body, path)
}

/// A known multishot handler: a noncapturing function `fn(P, fn(R) -> R)`
/// whose token parameter is used only as the callee of direct calls.
#[derive(Clone)]
struct MultishotHandler {
    function: Function,
    payload: usize,
    token: usize,
}

/// The handler as a multishot specialization source, if it qualifies.
fn multishot_handler(program: &Executable, function: usize) -> Option<MultishotHandler> {
    let handler = &program.functions[function];
    if handler.closure.is_some()
        || handler.parameters != 2
        || handler.parameter_slots.is_some()
        || program.foreign_functions[function].is_some()
        || handler
            .parameter_grades
            .iter()
            .any(|grade| grade.is_some_and(Grade::is_zero))
    {
        return None;
    }
    let token = 1;
    fn only_called(expr: &Expr, token: usize) -> bool {
        match &expr.kind {
            ExprKind::CallIndirect { callee, arguments }
                if matches!(
                    callee.kind,
                    ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot)
                        if slot == token
                ) =>
            {
                arguments
                    .iter()
                    .all(|argument| only_called(argument, token))
            }
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Peek(slot)
            | ExprKind::Borrow(slot)
                if *slot == token =>
            {
                false
            }
            ExprKind::Assign(slot, _)
            | ExprKind::InitOwner { slot, .. }
            | ExprKind::BorrowInit { slot, .. }
                if *slot == token =>
            {
                false
            }
            _ => {
                let mut ok = true;
                expr.for_each_child(&mut |child| ok &= only_called(child, token));
                ok
            }
        }
    }
    let body = &handler.body;
    let ok = body.statements.iter().all(|statement| match statement {
        Statement::Let(slot, value) => *slot != token && only_called(value, token),
        Statement::Expr(value) => only_called(value, token),
        Statement::Declare(slot) => *slot != token,
    }) && body
        .tail
        .as_deref()
        .is_none_or(|tail| only_called(tail, token));
    ok.then(|| MultishotHandler {
        function: handler.clone(),
        payload: 0,
        token,
    })
}

/// Replace every direct call of the token parameter by `make(span, argument)`.
fn rewrite_resume_calls(block: &mut Block, token: usize, make: &dyn Fn(Span, Expr) -> ExprKind) {
    fn walk(expr: &mut Expr, token: usize, make: &dyn Fn(Span, Expr) -> ExprKind) {
        expr.for_each_child_mut(&mut |child| walk(child, token, make));
        let is_resume = matches!(
            &expr.kind,
            ExprKind::CallIndirect { callee, .. }
                if matches!(
                    callee.kind,
                    ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot)
                        if slot == token
                )
        );
        if is_resume {
            let ExprKind::CallIndirect { mut arguments, .. } =
                std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
            else {
                unreachable!("matched above")
            };
            let argument = arguments.pop().expect("a resumption takes one argument");
            expr.kind = make(expr.span, argument);
        }
    }
    for statement in &mut block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, token, make);
        }
    }
    if let Some(tail) = block.tail.as_deref_mut() {
        walk(tail, token, make);
    }
}

/// Turn a multishot point's handler call into a direct call of the handler
/// specialization with the payload and the captured values.
fn call_specialization(call: &mut Expr, function: usize, environment: Vec<Expr>) {
    match &mut call.kind {
        ExprKind::Coerce { value, .. } => call_specialization(value, function, environment),
        ExprKind::CallIndirect { arguments, .. } => {
            let payload = arguments.remove(0);
            let mut values = vec![payload];
            values.extend(environment);
            call.kind = ExprKind::Call(crate::executable::Target::Function(function), values);
        }
        _ => unreachable!("a multishot point wraps the handler call"),
    }
}
