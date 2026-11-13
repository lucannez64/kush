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
//! 2. checks the suspension rules of the design (no borrow across a point
//!    except a view of outer storage the continuation does not capture,
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
    check_task_tokens(program)?;
    let mut context = Context {
        performs: performs(program),
        capability_performs: capability_performs(program),
        entries: BTreeMap::new(),
        lowering: BTreeSet::new(),
    };
    let mut index = 0;
    while index < program.functions.len() {
        lower_function(program, &mut context, index)?;
        index += 1;
    }
    for function in &mut program.functions {
        retarget_aborts_in_block(&mut function.body, &mut Vec::new())?;
    }
    Ok(())
}

/// After lowering, a continuation function holds code moved out of its
/// handled body, but not the abortive scopes around that body
/// (E-ABORT-INTERACT). An exit to such a scope becomes a dynamic abort of
/// its declared operation, which leaves the continuation like `return` and
/// travels back through the handler's resumption call; a call that may
/// abort to it propagates instead.
fn retarget_aborts_in_block(block: &mut Block, labels: &mut Vec<usize>) -> Result<()> {
    for statement in &mut block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            retarget_aborts(value, labels)?;
        }
    }
    if let Some(tail) = block.tail.as_deref_mut() {
        retarget_aborts(tail, labels)?;
    }
    Ok(())
}

fn retarget_aborts(expr: &mut Expr, labels: &mut Vec<usize>) -> Result<()> {
    let mut result = Ok(());
    match &mut expr.kind {
        ExprKind::AbortScope {
            label,
            body,
            handler,
            ..
        } => {
            retarget_aborts(handler, labels)?;
            labels.push(*label);
            result = retarget_aborts_in_block(body, labels);
            labels.pop();
        }
        _ => expr.for_each_child_mut(&mut |child| {
            if result.is_ok() {
                result = retarget_aborts(child, labels);
            }
        }),
    }
    result?;
    match &mut expr.kind {
        ExprKind::AbortExit {
            label, operation, ..
        } if !labels.contains(label) => {
            let Some(operation) = *operation else {
                return Err(Diagnostic::new(
                    expr.span,
                    "internal error: an abort of a lexical operation was separated from its handle",
                ));
            };
            let ExprKind::AbortExit { value, .. } =
                std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
            else {
                unreachable!()
            };
            expr.kind = ExprKind::AbortPerform { operation, value };
        }
        ExprKind::AbortCall {
            exits, propagates, ..
        } => {
            let before = exits.len();
            exits.retain(|(label, _)| labels.contains(label));
            if exits.len() != before {
                *propagates = true;
            }
        }
        _ => {}
    }
    Ok(())
}

/// What a resumable entry is resumable for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EntryKey {
    /// Performs of a declared operation found on the dynamic stack.
    Operation(usize),
    /// Performs through the `cap` parameter with this index.
    Capability(usize),
}

/// Whether `expr` passes parameter slot `slot` as is (a capability).
fn passes_slot(expr: &Expr, slot: usize) -> bool {
    match &expr.kind {
        ExprKind::Local(local) | ExprKind::Move(local) | ExprKind::Peek(local) => *local == slot,
        ExprKind::Coerce { value, .. } => passes_slot(value, slot),
        _ => false,
    }
}

/// Whether `expr` is a perform through the capability in `slot`: an
/// indirect call of that local with the payload and a token.
fn performs_through(expr: &Expr, slot: usize) -> bool {
    matches!(
        &expr.kind,
        ExprKind::CallIndirect { callee, arguments }
            if arguments.len() == 2 && passes_slot(callee, slot)
    )
}

/// Capability parameters each function may perform through: directly, or by
/// passing them to a `cap` parameter that its callee performs through. A
/// least fixed point over the call graph.
fn capability_performs(program: &Executable) -> Vec<BTreeSet<usize>> {
    let mut result = vec![BTreeSet::new(); program.functions.len()];
    loop {
        let mut changed = false;
        for (index, function) in program.functions.iter().enumerate() {
            let mut found = result[index].clone();
            for &slot in &function.capability_parameters {
                if found.contains(&slot) {
                    continue;
                }
                let mut uses = false;
                fn walk(expr: &Expr, slot: usize, result: &[BTreeSet<usize>], uses: &mut bool) {
                    if performs_through(expr, slot) {
                        *uses = true;
                    }
                    if let ExprKind::Call(crate::executable::Target::Function(callee), arguments) =
                        &expr.kind
                    {
                        for (index, argument) in arguments.iter().enumerate() {
                            if passes_slot(argument, slot) && result[*callee].contains(&index) {
                                *uses = true;
                            }
                        }
                    }
                    expr.for_each_child(&mut |child| walk(child, slot, result, uses));
                }
                for statement in &function.body.statements {
                    if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                        walk(value, slot, &result, &mut uses);
                    }
                }
                if let Some(tail) = &function.body.tail {
                    walk(tail, slot, &result, &mut uses);
                }
                if uses {
                    found.insert(slot);
                }
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

/// Replace capability await points of `target` whose callee never performs
/// through that parameter by their plain call.
fn unmark_capability_awaits(
    program: &mut Executable,
    context: &Context,
    index: usize,
    target: *const Suspendable,
) {
    fn walk(expr: &mut Expr, performs: &[BTreeSet<usize>]) {
        if let ExprKind::Suspend {
            callee: Some(callee),
            capability: Some(parameter),
            ..
        } = &expr.kind
            && !performs
                .get(*callee)
                .is_some_and(|set| set.contains(parameter))
        {
            let ExprKind::Suspend { call, .. } =
                std::mem::replace(&mut expr.kind, ExprKind::Constant(0))
            else {
                unreachable!()
            };
            *expr = *call;
            return;
        }
        if matches!(expr.kind, ExprKind::Suspendable(_)) {
            return;
        }
        expr.for_each_child_mut(&mut |child| walk(child, performs));
    }
    let performs = &context.capability_performs;
    let mut lower = |mut suspendable: Box<Suspendable>| -> Result<ExprKind> {
        for statement in &mut suspendable.body.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                walk(value, performs);
            }
        }
        if let Some(tail) = suspendable.body.tail.as_deref_mut() {
            walk(tail, performs);
        }
        Ok(ExprKind::Suspendable(suspendable))
    };
    let mut lower: Option<&mut dyn FnMut(Box<Suspendable>) -> Result<ExprKind>> = Some(&mut lower);
    let _ = replace_target_in_block(&mut program.functions[index].body, target, &mut lower);
}

/// State shared by every lowering step of one program.
struct Context {
    /// Declared operations each original function may perform dynamically
    /// (not handled inside it), by operation id.
    performs: Vec<BTreeSet<usize>>,
    /// Capability parameters each function may perform through, directly
    /// or by passing them on (EFF-CAP-RESUME-CALLS).
    capability_performs: Vec<BTreeSet<usize>>,
    /// Resumable entry of (function, operation or capability parameter): its
    /// index and whether it or anything it awaits allocates a resumption
    /// environment.
    entries: BTreeMap<(usize, EntryKey), (usize, bool)>,
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
    /// Live when an abort reaches each enclosing `AbortScope`, by label.
    aborts: Vec<(usize, Slots)>,
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
            ExprKind::AbortScope {
                label,
                body,
                handler,
                ..
            } => {
                let aborted = self.expr(handler, after);
                self.aborts.push((*label, aborted));
                let live = self.block(body, after);
                self.aborts.pop();
                live
            }
            ExprKind::AbortPerform { value, .. } => self.expr(value, &Slots::new()),
            ExprKind::AbortCall { call, exits, .. } => {
                let mut live = after.clone();
                for (label, _) in exits {
                    if let Some((_, exit)) =
                        self.aborts.iter().rev().find(|(target, _)| target == label)
                    {
                        live.extend(exit.iter().copied());
                    }
                }
                self.expr(call, &live)
            }
            ExprKind::AbortExit { label, value, .. } => {
                let exit = self
                    .aborts
                    .iter()
                    .rev()
                    .find(|(target, _)| target == label)
                    .map(|(_, live)| live.clone())
                    .unwrap_or_default();
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
        ExprKind::HandlerRedirect { depth, body } => {
            on_expr(depth);
            on_block(body);
        }
        ExprKind::ContinuationScope { body } => on_block(body),
        ExprKind::Suspendable(suspendable) => on_block(&suspendable.body),
        ExprKind::Region { body, finish, .. } => {
            on_block(body);
            if let Some(finish) = finish {
                on_expr(finish);
            }
        }
        ExprKind::AbortScope { body, handler, .. } => {
            on_block(body);
            on_expr(handler);
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
                // The loop is rebuilt around the condition when resuming
                // inside its body, which would retarget a jump in it.
                if crate::executable::anf::exits_enclosing_loop(condition)
                    && contains_point_block(body)
                {
                    return Err(Diagnostic::new(
                        condition.span,
                        "a 'break' or 'continue' inside the condition of a while loop whose body performs a non-tail operation is not supported; compute the condition in the loop body",
                    ));
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
            ExprKind::AbortScope { .. } if contains_point(expr) => Err(Diagnostic::new(
                expr.span,
                "a non-tail resumption point inside an abortive 'handle' is not supported; perform the operation or call the function outside that handle",
            )),
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

fn contains_point_block(block: &Block) -> bool {
    block.statements.iter().any(|statement| match statement {
        Statement::Let(_, value) | Statement::Expr(value) => contains_point(value),
        Statement::Declare(_) => false,
    }) || block.tail.as_deref().is_some_and(contains_point)
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
            ExprKind::While(condition, body) => {
                // A jump in the condition targets an enclosing loop.
                walk(condition, depth)?;
                let wrapper = Expr {
                    kind: ExprKind::Block(body.clone()),
                    ty: body.ty,
                    span: expr.span,
                    resource: None,
                };
                walk(&wrapper, depth + 1)
            }
            ExprKind::Loop(_) => {
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
        ExprKind::Local(slot)
        | ExprKind::Peek(slot)
        | ExprKind::Move(slot)
        | ExprKind::Borrow(slot)
        | ExprKind::BorrowInit { slot, .. } => Some(*slot),
        ExprKind::Slice { base, .. } => place_root(base),
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
            ExprKind::Slice { base, .. } if expr.ty.is_mut_slice() || expr.ty == Type::StrMut => {
                place_root(base)
            }
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
    let layouts = carrying_layouts(program);
    let holds = |out: &Slots, value: &Expr| -> bool {
        let mut value = value;
        while let ExprKind::Coerce { value: inner, .. } = &value.kind {
            value = inner;
        }
        match &value.kind {
            // A closure holds a borrow if it captures by reference or
            // captures a value that holds one (a view, a reference, ...).
            ExprKind::FnValue { function, captures } => {
                program.functions[*function].capture_refs.iter().any(|r| *r)
                    // A captured capability borrows its handle activation.
                    || (program.functions[*function].closure.is_some()
                        && !program.functions[*function].capability_parameters.is_empty())
                    || captures
                        .iter()
                        .any(|capture| carries_in(capture.ty, &layouts, &program.pointees, 0))
            }
            ExprKind::Local(source) | ExprKind::Move(source) => out.contains(source),
            _ => false,
        }
    };
    fn in_block(
        block: &Block,
        holds: &dyn Fn(&Slots, &Expr) -> bool,
        out: &mut Slots,
        changed: &mut bool,
    ) {
        for statement in &block.statements {
            match statement {
                Statement::Let(slot, value) => {
                    if holds(out, value) && out.insert(*slot) {
                        *changed = true;
                    }
                    in_expr(value, holds, out, changed);
                }
                Statement::Expr(value) => in_expr(value, holds, out, changed),
                Statement::Declare(_) => {}
            }
        }
        if let Some(tail) = &block.tail {
            in_expr(tail, holds, out, changed);
        }
    }
    fn in_expr(
        expr: &Expr,
        holds: &dyn Fn(&Slots, &Expr) -> bool,
        out: &mut Slots,
        changed: &mut bool,
    ) {
        if let ExprKind::Assign(slot, value) = &expr.kind
            && holds(out, value)
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
            in_block(block, holds, out, changed);
        }
        for child in children {
            in_expr(child, holds, out, changed);
        }
    }
    let mut out = Slots::new();
    loop {
        let mut changed = false;
        in_block(body, &holds, &mut out, &mut changed);
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

/// A local that is a plain view or reference: its value is a pointer into
/// storage owned by some other local (or by the caller).
fn is_view_local(ty: Type) -> bool {
    ty.is_view() || ty.is_ref()
}

/// Conservative loan provenance for the view and reference locals of a
/// function body (E-CPS-BORROW): for each such local, the owner locals whose
/// storage its value may point into. A parameter contributes no owner (its
/// storage belongs to the caller, whose frame outlives this activation). A
/// local is `None` (unknown) when any of its definitions is not one of the
/// forms below, so the suspension rule falls back to rejecting it.
///
/// Understood value forms: `&x`, `&place`, `x[a..b]` / `&x[..]` (a slice of
/// an owner, or of a view, which shares that view's owners), copies of
/// another view local, coercions, and direct calls (the result may borrow
/// from any borrow-carrying argument).
fn borrow_origins(
    body: &Block,
    locals: &[Local],
    parameters: usize,
    carries: &dyn Fn(Type) -> bool,
) -> BTreeMap<usize, Option<Slots>> {
    fn collect<'a>(block: &'a Block, definitions: &mut Vec<(usize, &'a Expr)>, opaque: &mut Slots) {
        for statement in &block.statements {
            match statement {
                Statement::Let(slot, value) => {
                    definitions.push((*slot, value));
                    walk(value, definitions, opaque);
                }
                Statement::Expr(value) => walk(value, definitions, opaque),
                Statement::Declare(_) => {}
            }
        }
        if let Some(tail) = &block.tail {
            walk(tail, definitions, opaque);
        }
    }
    fn walk<'a>(expr: &'a Expr, definitions: &mut Vec<(usize, &'a Expr)>, opaque: &mut Slots) {
        match &expr.kind {
            ExprKind::Assign(slot, value) | ExprKind::InitOwner { slot, value } => {
                definitions.push((*slot, value));
            }
            ExprKind::BorrowInit { slot, .. } => {
                opaque.insert(*slot);
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    crate::ownership::pattern_bindings(&arm.pattern, opaque);
                }
            }
            _ => {}
        }
        let mut blocks = Vec::new();
        let mut children = Vec::new();
        block_children(expr, &mut |block| blocks.push(block), &mut |child| {
            children.push(child)
        });
        for block in blocks {
            collect(block, definitions, opaque);
        }
        for child in children {
            walk(child, definitions, opaque);
        }
    }
    let mut definitions = Vec::new();
    let mut opaque = Slots::new();
    collect(body, &mut definitions, &mut opaque);
    let defined = definitions.iter().map(|(slot, _)| *slot).collect::<Slots>();
    let mut origins = BTreeMap::new();
    for (slot, local) in locals.iter().enumerate() {
        if !is_view_local(local.ty) {
            continue;
        }
        let known = !opaque.contains(&slot) && (slot < parameters || defined.contains(&slot));
        origins.insert(slot, known.then(Slots::new));
    }
    loop {
        let mut changed = false;
        for (slot, value) in &definitions {
            let Some(Some(current)) = origins.get(slot) else {
                continue;
            };
            let next = roots(value, locals, &origins, carries).map(|found| {
                let mut next = current.clone();
                next.extend(found);
                next
            });
            if next.as_ref() != Some(current) {
                origins.insert(*slot, next);
                changed = true;
            }
        }
        if !changed {
            break origins;
        }
    }
}

/// Owner locals a place expression's storage belongs to.
fn place_roots(
    place: &Expr,
    locals: &[Local],
    origins: &BTreeMap<usize, Option<Slots>>,
    carries: &dyn Fn(Type) -> bool,
) -> Option<Slots> {
    let root = place_root(place)?;
    if is_view_local(locals[root].ty) {
        // A slice of a view, or a field of a referenced record: the
        // storage is the view's (or reference's) own referent.
        origins.get(&root).cloned().flatten()
    } else if carries(locals[root].ty) {
        // A place inside a value that itself holds a borrow (a borrowed
        // record field `r.p.x`) may be storage owned elsewhere: unknown.
        None
    } else {
        Some(Slots::from([root]))
    }
}
/// Owner locals a borrow-carrying value may point into, or `None` when its
/// source is not one of the forms `borrow_origins` understands.
fn roots(
    expr: &Expr,
    locals: &[Local],
    origins: &BTreeMap<usize, Option<Slots>>,
    carries: &dyn Fn(Type) -> bool,
) -> Option<Slots> {
    match &expr.kind {
        ExprKind::Coerce { value, .. } => roots(value, locals, origins, carries),
        ExprKind::Borrow(slot) if !is_view_local(locals[*slot].ty) && carries(locals[*slot].ty) => {
            // A reference to a value that holds a borrow reaches storage
            // owned elsewhere.
            None
        }
        ExprKind::Borrow(slot) => {
            let mut out = Slots::from([*slot]);
            if is_view_local(locals[*slot].ty) {
                out.extend(origins.get(slot).cloned().flatten()?);
            }
            Some(out)
        }
        ExprKind::BorrowPlace(place) => place_roots(place, locals, origins, carries),
        ExprKind::Slice { base, .. } => place_roots(base, locals, origins, carries),
        ExprKind::Local(slot) | ExprKind::Move(slot) | ExprKind::Peek(slot)
            if is_view_local(locals[*slot].ty) =>
        {
            origins.get(slot).cloned().flatten()
        }
        ExprKind::Call(_, arguments) => {
            let mut out = Slots::new();
            for argument in arguments.iter().filter(|argument| carries(argument.ty)) {
                out.extend(roots(argument, locals, origins, carries)?);
            }
            Some(out)
        }
        _ => None,
    }
}

/// Locals a suspension point's own call borrows: directly (`&v`, `&mut v`,
/// a place reference), plus whether it passes an opaque borrowed value (a
/// view local or a by-reference closure) whose source is unknown.
fn point_borrows(call: &Expr, host: &Host) -> (Slots, bool) {
    fn operand(expr: &Expr, host: &Host, direct: &mut Slots, opaque: &mut bool) {
        // A value whose type cannot hold a borrow ends every borrow made
        // while computing it (`Vec.len(&v)`).
        if !host.carries_borrow(expr.ty) {
            return;
        }
        // A view or reference with known owners borrows exactly those.
        if (expr.ty.is_view() || expr.ty.is_ref())
            && let Some(owners) = roots(expr, &host.locals, &host.origins, &|ty| {
                host.carries_borrow(ty)
            })
        {
            direct.extend(owners);
            return;
        }
        match &expr.kind {
            ExprKind::Borrow(slot) | ExprKind::BorrowInit { slot, .. } => {
                direct.insert(*slot);
            }
            ExprKind::BorrowPlace(place) => {
                match place_root(place) {
                    // A place inside a borrow-holding value may be storage
                    // owned by another local.
                    Some(slot) if !host.carries_borrow(host.locals[slot].ty) => {
                        direct.insert(slot);
                    }
                    _ => *opaque = true,
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
    /// Per record/enum layout: a value can hold a borrow or a closure.
    carrying_layouts: Vec<bool>,
    pointees: Vec<Type>,
    /// Per view or reference local: the owner locals it may borrow from,
    /// or `None` when its source is not understood (see `borrow_origins`).
    origins: BTreeMap<usize, Option<Slots>>,
}

impl Host {
    /// Whether a value of `ty` can hold a borrow (conservatively: views,
    /// references, closures, trait objects, unions, tasks, and data
    /// containing them).
    fn carries_borrow(&self, ty: Type) -> bool {
        match ty {
            Type::Slice(_)
            | Type::SliceMut(_)
            | Type::Str
            | Type::StrMut
            | Type::Ref(_)
            | Type::RefMut(_)
            | Type::Fn(_)
            | Type::Once(_)
            | Type::DynObj(_)
            | Type::Union(_)
            | Type::Task(_)
            | Type::Thread(_) => true,
            Type::Enum(id) | Type::Variants(id, _) => self.carrying_layouts[id],
            Type::Box(p) | Type::Vec(p) | Type::Annotated(p, _) => {
                carries_in(self.pointees[p], &self.carrying_layouts, &self.pointees, 0)
            }
            _ => false,
        }
    }
}

fn carries_in(ty: Type, layouts: &[bool], pointees: &[Type], depth: usize) -> bool {
    if depth > 16 {
        return true;
    }
    match ty {
        Type::Enum(id) | Type::Variants(id, _) => layouts[id],
        Type::Box(p) | Type::Vec(p) | Type::Annotated(p, _) => {
            carries_in(pointees[p], layouts, pointees, depth + 1)
        }
        Type::Slice(_)
        | Type::SliceMut(_)
        | Type::Str
        | Type::StrMut
        | Type::Ref(_)
        | Type::RefMut(_)
        | Type::Fn(_)
        | Type::Once(_)
        | Type::DynObj(_)
        | Type::Union(_)
        | Type::Task(_)
        | Type::Thread(_) => true,
        _ => false,
    }
}

/// Per layout: whether a value can hold a borrow or a closure, as a least
/// fixed point over field types.
fn carrying_layouts(program: &Executable) -> Vec<bool> {
    let mut layouts = vec![false; program.enums.len()];
    loop {
        let mut changed = false;
        for (index, layout) in program.enums.iter().enumerate() {
            if layouts[index] {
                continue;
            }
            let carries = layout.variants.iter().any(|variant| {
                variant
                    .fields
                    .iter()
                    .any(|field| carries_in(*field, &layouts, &program.pointees, 0))
            });
            if carries {
                layouts[index] = true;
                changed = true;
            }
        }
        if !changed {
            break layouts;
        }
    }
}

/// What the machine builder needs about one suspendable body.
struct Spec {
    /// The final answer type: the operation result.
    result: Type,
    /// Token type of a lexical perform point.
    token: Type,
    multishot: bool,
    handler_writes: Vec<usize>,
    /// Locals the handler captures by reference: continuation code must not
    /// write them.
    handler_refs: Vec<usize>,
    /// Effect row at the handle; `None` for a resumable entry, whose
    /// allocation is checked at the handle that awaits it.
    effects: Option<u16>,
    /// An awaited resumable entry allocates resumption environments.
    awaited_allocates: bool,
    /// Continuation parameter of a resumable entry; exits that finish apply
    /// it.
    finish: Option<usize>,
    /// Resumable entry index and continuation token type per awaited callee.
    entries: BTreeMap<(usize, Option<usize>), (usize, Type)>,
    /// The handle is for a declared operation: resumed continuations hide
    /// frames the handler pushes (see `ExprKind::HandlerRedirect`).
    redirect: bool,
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

/// Whether a borrow-holding local live across a suspension point may stay
/// live (E-CPS-BORROW). It must be a plain view or reference whose every
/// possible owner is
///
/// - declared outside the handled body: suspension never pops a native or
///   evaluator frame (the handler, the token and every continuation run
///   nested inside the activation that reached the point, and the token
///   cannot escape the handler), so such storage outlives every
///   continuation and is never moved by the lowering;
/// - not captured at this point: a captured owner is moved or copied into
///   the continuation's environment, so the view would point at the stale
///   original while the continuation used the copy;
/// - not written by the handler through a capture, and not read by it at all
///   when the view is exclusive.
///
/// Everything else the view can observe is ordinary code in the structured
/// body, which ownership has already checked with the perform as a call.
fn outer_borrow(host: &Host, spec: &Spec, bound: &Slots, captured: &[usize], slot: usize) -> bool {
    let ty = host.locals[slot].ty;
    if host.by_reference.contains(&slot) || !is_view_local(ty) {
        return false;
    }
    let exclusive = ty.is_mut_slice() || matches!(ty, Type::RefMut(_));
    // A multishot token runs the continuation several times; each run
    // would hold the same exclusive loan.
    if exclusive && spec.multishot {
        return false;
    }
    let Some(Some(owners)) = host.origins.get(&slot) else {
        return false;
    };
    owners.iter().all(|owner| {
        !bound.contains(owner)
            && !captured.contains(owner)
            && !spec.handler_writes.contains(owner)
            && !(exclusive && spec.handler_refs.contains(owner))
    })
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
    // Multishot points hand out `multi fn` tokens whose environments live on
    // the continuation stack (docs/multishot-capabilities.md): no handler
    // specialization is needed.
    let multi_tokens = matches!(spec.token, Type::Multi(_))
        || spec
            .entries
            .values()
            .any(|(_, token)| matches!(token, Type::Multi(_)));
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
            if (host.borrowed.get(*slot).copied().unwrap_or(true)
                || host.by_reference.contains(slot))
                && !outer_borrow(host, spec, &bound, slots, *slot)
            {
                return Err(Diagnostic::new(
                    at,
                    "a borrowed value (slice view, text view, reference, borrowed record, or task handle) cannot stay live across a non-tail 'perform' unless it is a view or reference of storage declared outside the handled body that the resumption neither captures nor lets the handler write; end the borrow before the perform or pass an owned value",
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
        if let Some(slot) = slots
            .iter()
            .find(|slot| Some(**slot) != spec.finish && matches!(locals[**slot].ty, Type::Multi(_)))
        {
            return Err(Diagnostic::new(
                at,
                "a multishot resumption token ('multi fn') cannot stay live across a 'perform': the continuation would keep it after the call that made it returns. Use it before the perform",
            )
            .with_note(locals[*slot].span, "token declared here"));
        }
        if spec.multishot && !slots.is_empty() {
            if spec.multishot_handler.is_none() && !multi_tokens {
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
        let ExprKind::Suspend {
            call,
            callee,
            capability,
            ..
        } = &site.kind
        else {
            unreachable!("paths lead to suspension points")
        };
        let token = match callee {
            Some(callee) => spec.entries[&(*callee, *capability)].1,
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
        .filter(|point| spec.multishot && !multi_tokens && !captures[point].is_empty())
        .collect::<Vec<_>>();
    // A one-shot continuation records the
    // handler-stack depth at its point and resumes under a redirect, so
    // frames the handler pushes around `resume` stay invisible to it.
    let redirects = |point: usize| spec.redirect && matches!(tokens[&point], Type::Once(_));
    let allocates = order.iter().any(|point| {
        (!captures[point].is_empty() || redirects(*point)) && !specialized.contains(point)
    });
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
            mut call,
            callee,
            capability,
            ..
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
                        .chain(redirects(*point).then_some(Expr {
                            kind: ExprKind::HandlerDepth,
                            ty: Type::I64,
                            span,
                            resource: None,
                        }))
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
                *target =
                    crate::executable::Target::Function(spec.entries[&(callee, capability)].0);
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
    let outer_live = |slot: usize| {
        (!bound.contains(&slot) && host.after.contains(&slot)) || spec.handler_refs.contains(&slot)
    };
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
        let redirect = redirects(*point);
        let depth_slot = input_slot + 1;
        let mut zipper = Zipper {
            next_local: input_slot + 1 + usize::from(redirect),
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
        if redirect {
            cont_locals.push(Local {
                ty: Type::I64,
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span: spec.span,
            });
        }
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
        if redirect {
            parameter_slots.push(depth_slot);
        }
        let environment = parameter_slots.len();
        parameter_slots.push(input_slot);
        let parameters = parameter_slots.len();
        let region = Expr {
            kind: ExprKind::Region {
                body: rest,
                finish: finish(spec.span),
            },
            ty: spec.result,
            span: spec.span,
            resource: None,
        };
        let body = if redirect {
            Expr {
                kind: ExprKind::HandlerRedirect {
                    depth: Box::new(Expr {
                        kind: ExprKind::Local(depth_slot),
                        ty: Type::I64,
                        span: spec.span,
                        resource: None,
                    }),
                    body: Block {
                        statements: vec![],
                        tail: Some(Box::new(region)),
                        ty: spec.result,
                    },
                },
                ty: spec.result,
                span: spec.span,
                resource: None,
            }
        } else {
            region
        };
        continuations.push(Function {
            name: format!("{}::resume#{point}", host.name),
            parameters,
            // Once and multi tokens carry an environment word even without
            // captures; a capture-free `fn` multishot token is a plain code
            // pointer.
            closure: matches!(tokens[point], Type::Once(_) | Type::Multi(_)).then_some(environment),
            capture_refs: vec![false; environment],
            capture_writes: vec![false; environment],
            locals: cont_locals,
            result: spec.result,
            body: Block {
                statements: vec![],
                tail: Some(Box::new(body)),
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
            capability_parameters: vec![],
            shared_environment: matches!(tokens[point], Type::Multi(_)),
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
fn awaited_callees(block: &Block, out: &mut BTreeSet<(usize, Option<usize>)>) {
    fn walk(expr: &Expr, out: &mut BTreeSet<(usize, Option<usize>)>) {
        if let ExprKind::Suspend {
            callee: Some(callee),
            capability,
            ..
        } = &expr.kind
        {
            out.insert((*callee, *capability));
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
    // A capability await whose callee never performs through that
    // parameter is an ordinary call.
    unmark_capability_awaits(program, context, index, target);
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
    // A known handler that installs no dynamic handler and only calls its
    // token directly cannot hide frames from the resumed code, so its
    // continuations need no redirect (and stay capture-free when possible).
    let handler_is_transparent = {
        let handler = find_in_block(&program.functions[index].body, target)
            .and_then(|suspendable| suspendable.handler_function);
        handler.is_some_and(|handler| {
            !context.lowering.contains(&handler) && {
                let function = &program.functions[handler];
                let pushes = {
                    fn pushes(expr: &Expr) -> bool {
                        if matches!(
                            expr.kind,
                            ExprKind::HandlerPush { .. }
                                | ExprKind::HandlerRedirect { .. }
                                | ExprKind::AbortScope {
                                    operation: Some(_),
                                    ..
                                }
                        ) {
                            return true;
                        }
                        let mut found = false;
                        expr.for_each_child(&mut |child| found |= pushes(child));
                        found
                    }
                    function
                        .body
                        .statements
                        .iter()
                        .any(|statement| match statement {
                            Statement::Let(_, value) | Statement::Expr(value) => pushes(value),
                            Statement::Declare(_) => false,
                        })
                        || function.body.tail.as_deref().is_some_and(pushes)
                };
                !pushes && multishot_handler(program, handler).is_some()
            }
        })
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
    for (callee, capability) in awaited {
        let key = match capability {
            Some(parameter) => EntryKey::Capability(parameter),
            None => EntryKey::Operation(
                operation.expect("await points only exist for declared operations"),
            ),
        };
        let (entry, allocates) = resumable_entry(program, context, callee, key, result)?;
        let token = entry_token(program, callee, capability, result);
        entries.insert((callee, capability), (entry, token));
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
    let layouts = carrying_layouts(program);
    let origins = borrow_origins(
        &function.body,
        &function.locals,
        function.parameters,
        &|ty| carries_in(ty, &layouts, &program.pointees, 0),
    );
    let host = Host {
        origins,
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
        carrying_layouts: carrying_layouts(program),
        pointees: program.pointees.clone(),
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
            handler_refs,
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
            handler_refs,
            effects: Some(effects),
            awaited_allocates,
            finish: None,
            entries: entries.clone(),
            redirect: !handler_is_transparent,
            multishot_handler: multishot_handler.clone(),
            span,
        };
        let multi = matches!(spec.token, Type::Multi(_));
        let built = build(&host, &spec, body, first_function, &owns)?;
        continuations = built.continuations;
        if !built.points {
            return Ok(ExprKind::Block(built.body));
        }
        let region = ExprKind::Region {
            body: built.body,
            finish: None,
        };
        if !multi {
            return Ok(region);
        }
        // Release the continuation environments of this `handle` when it
        // ends (docs/multishot-capabilities.md section 6.2).
        Ok(ExprKind::ContinuationScope {
            body: Block {
                statements: vec![],
                tail: Some(Box::new(Expr {
                    kind: region,
                    ty: result,
                    span,
                    resource: None,
                })),
                ty: result,
            },
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
/// The arrow of a `multi fn(input) -> result` token, interned like the
/// checker's (`Types::multi_token`): not once, not linear.
fn multi_function_type(program: &mut Executable, input: Type, result: Type) -> usize {
    let wanted = crate::runtime_types::FunctionType {
        parameters: vec![input],
        result,
        effects: 0,
        parameter_grades: vec![None],
        result_grade: None,
        once: false,
        linear: false,
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

/// Whether parameter `slot` of `function` is a `cap multi` capability: its
/// handler arrow takes a `multi fn` token (docs/multishot-capabilities.md).
fn capability_multi(program: &Executable, function: usize, slot: usize) -> bool {
    match program.functions[function]
        .locals
        .get(slot)
        .map(|local| local.ty)
    {
        Some(Type::Fn(arrow)) => matches!(
            program.function_types[arrow].parameters.get(1),
            Some(Type::Multi(_))
        ),
        _ => false,
    }
}

/// The token a resumable entry of `callee` receives as its continuation:
/// `multi fn` for a `cap multi` parameter, otherwise `linear once fn`.
fn entry_token(
    program: &mut Executable,
    callee: usize,
    capability: Option<usize>,
    result: Type,
) -> Type {
    let input = program.functions[callee].result;
    if capability.is_some_and(|slot| capability_multi(program, callee, slot)) {
        Type::Multi(multi_function_type(program, input, result))
    } else {
        Type::Once(function_type(program, input, result))
    }
}

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
        Type::Fn(id) | Type::Once(id) | Type::Multi(id) => program.function_types[id].effects,
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
                    ExprKind::DynamicPerform { operation, .. }
                    | ExprKind::AbortPerform { operation, .. } => {
                        add(&BTreeSet::from([*operation]));
                    }
                    ExprKind::Call(crate::executable::Target::Function(callee), _) => {
                        add(&current[*callee])
                    }
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
                    ExprKind::HandlerPush { operation, .. }
                    | ExprKind::AbortScope {
                        operation: Some(operation),
                        ..
                    } => {
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

/// E-ABORT-PROPAGATE (docs/abortive-handlers.md 3.3): wrap every call that
/// may abort with a declared abortive operation in an `AbortCall` naming the
/// enclosing abortive scopes it can leave to, and whether the abort can also
/// leave this function. Runs before ownership, which checks and fills the
/// cleanup of each exit. Rejects aborts across task boundaries, through
/// vector callbacks, and out of non-tail handler bodies.
pub(crate) fn mark_abort_calls(program: &mut Executable) -> Result<()> {
    let abortive: BTreeSet<usize> = program
        .abortive_operations
        .iter()
        .enumerate()
        .filter(|(_, abortive)| **abortive)
        .map(|(operation, _)| operation)
        .collect();
    if abortive.is_empty() {
        return Ok(());
    }
    let may = performs(program);
    let row_operations = |effects: u16| -> BTreeSet<usize> {
        program
            .effect_bits
            .iter()
            .enumerate()
            .filter(|(operation, bit)| {
                **bit != 0 && effects & **bit != 0 && abortive.contains(operation)
            })
            .map(|(operation, _)| operation)
            .collect()
    };
    let callable_effects = |ty: Type| match ty {
        Type::Fn(id) | Type::Once(id) | Type::Multi(id) => program.function_types[id].effects,
        _ => 0,
    };
    // Abortive operations each call may leave with, computed on the
    // unmodified program.
    struct Marker<'a> {
        program: &'a Executable,
        may: &'a [BTreeSet<usize>],
        abortive: &'a BTreeSet<usize>,
        row_operations: &'a dyn Fn(u16) -> BTreeSet<usize>,
        callable_effects: &'a dyn Fn(Type) -> u16,
    }
    impl Marker<'_> {
        fn aborts_of(&self, expr: &Expr) -> BTreeSet<usize> {
            let mut operations = BTreeSet::new();
            match &expr.kind {
                ExprKind::Call(crate::executable::Target::Function(callee), _) => {
                    operations.extend(self.may[*callee].iter().copied());
                }
                ExprKind::Call(crate::executable::Target::DynCall { spec }, _) => {
                    let spec = &self.program.dyn_calls[*spec];
                    for member in &self.program.dyn_members[spec.object] {
                        if let Some(function) = member.methods.get(&spec.key) {
                            operations.extend(self.may[*function].iter().copied());
                        }
                    }
                }
                ExprKind::Call(crate::executable::Target::UnionBorrowCall { spec }, _) => {
                    for (_, _, function) in &self.program.union_calls[*spec].members {
                        operations.extend(self.may[*function].iter().copied());
                    }
                }
                ExprKind::CallIndirect { callee, .. } => {
                    operations.extend((self.row_operations)((self.callable_effects)(callee.ty)));
                }
                _ => {}
            }
            operations.retain(|operation| self.abortive.contains(operation));
            operations
        }
        /// The shape of a resumption token whose row names abortive
        /// operations: `linear once fn(R) -> R ! {F, ..}`.
        fn token_like(&self, ty: Type) -> bool {
            let Type::Once(id) = ty else {
                return false;
            };
            let signature = &self.program.function_types[id];
            signature.parameters.len() == 1
                && signature.parameters[0] == signature.result
                && signature.effects != 0
                && (self.row_operations)(signature.effects).len()
                    == self
                        .program
                        .effect_bits
                        .iter()
                        .filter(|bit| **bit != 0 && signature.effects & **bit != 0)
                        .count()
                && signature.effects & crate::executable::EFFECT_BITS == 0
        }
        fn walk(
            &self,
            expr: &mut Expr,
            scopes: &mut Vec<(usize, Option<usize>)>,
            regions: &mut Vec<Region>,
        ) -> Result<()> {
            let barrier = match &expr.kind {
                ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
                    (!(self.row_operations)((self.callable_effects)(body.ty)).is_empty())
                        .then_some("an abortive operation cannot leave a task: handle it inside the task body")
                }
                ExprKind::VecMap { callbacks, .. } => callbacks
                    .iter()
                    .any(|callback| {
                        !(self.row_operations)((self.callable_effects)(callback.ty)).is_empty()
                    })
                    .then_some("a vector callback cannot abort with an abortive operation; handle it inside the callback"),
                _ => None,
            };
            if let Some(message) = barrier {
                return Err(Diagnostic::new(expr.span, message));
            }
            let mut result = Ok(());
            let operations = match &mut expr.kind {
                ExprKind::AbortScope {
                    label,
                    body,
                    handler,
                    operation,
                } => {
                    result = self.walk(handler, scopes, regions);
                    scopes.push((*label, *operation));
                    if result.is_ok() {
                        result = self.walk_block(body, scopes, regions);
                    }
                    scopes.pop();
                    BTreeSet::new()
                }
                ExprKind::Suspendable(suspendable) => {
                    // A handler passes an abort through its token when the
                    // token's row names it (E-ABORT-INTERACT, E-ABORT-ENTRIES:
                    // also declared-operation and multishot tokens).
                    let row = (self.row_operations)((self.callable_effects)(suspendable.token));
                    regions.push(Region {
                        scopes: scopes.len(),
                        row: row.clone(),
                    });
                    result = self.walk_block(&mut suspendable.body, scopes, regions);
                    regions.pop();
                    // The lowered body is left with a placeholder when an
                    // abort comes back through a handler call.
                    row
                }
                ExprKind::Suspend { call, callee, .. } => {
                    let awaited = callee.is_some();
                    call.for_each_child_mut(&mut |child| {
                        if result.is_ok() {
                            result = self.walk(child, scopes, regions);
                        }
                    });
                    result?;
                    // The handler call itself aborts out of the region; the
                    // check after the region takes it.
                    let operations = self.aborts_of(call);
                    let row = regions.last().map(|region| &region.row);
                    if operations
                        .iter()
                        .any(|operation| row.is_none_or(|row| !row.contains(operation)))
                    {
                        return Err(Diagnostic::new(
                            expr.span,
                            if awaited {
                                "a call that may abort cannot run in the body of a handler with code after 'resume' unless its one-shot resumption token names the abortive operation; call it outside that handle"
                            } else {
                                "this handler may abort, so the resumption token of its one-shot handler must name the abortive operation in its row"
                            },
                        ));
                    }
                    return Ok(());
                }
                _ => {
                    expr.for_each_child_mut(&mut |child| {
                        if result.is_ok() {
                            result = self.walk(child, scopes, regions);
                        }
                    });
                    self.aborts_of(expr)
                }
            };
            result?;
            if operations.is_empty() {
                return Ok(());
            }
            let mut exits = Vec::new();
            let mut propagates = false;
            // A resumption token runs its continuation under a redirect that
            // hides frames pushed after the suspension, so an abort coming
            // back through it may address a handle outside this function even
            // when one for the same operation encloses the call here.
            let token_call = match &expr.kind {
                ExprKind::CallIndirect { callee, .. } => self.token_like(callee.ty),
                _ => false,
            };
            for operation in operations {
                let target = scopes
                    .iter()
                    .rposition(|(_, scope)| *scope == Some(operation));
                if token_call && target.is_some() {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a resumption token that may abort cannot be called inside a 'handle' for the same abortive operation; call it outside that handle",
                    ));
                }
                // Every non-tail body the abort leaves must let it through.
                let crossed = regions
                    .iter()
                    .filter(|region| target.is_none_or(|target| region.scopes > target));
                if crossed
                    .clone()
                    .any(|region| !region.row.contains(&operation))
                {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a call that may abort cannot run in the body of a handler with code after 'resume' unless its one-shot resumption token names the abortive operation; call it outside that handle",
                    ));
                }
                match target {
                    Some(target) => {
                        let label = scopes[target].0;
                        if !exits.iter().any(|(existing, _)| *existing == label) {
                            exits.push((label, Vec::new()));
                        }
                    }
                    None => propagates = true,
                }
            }
            // Innermost scope first: the native dispatch tests them in order.
            exits.sort_by_key(|(label, _)| {
                std::cmp::Reverse(scopes.iter().position(|(scope, _)| scope == label))
            });
            let (ty, span) = (expr.ty, expr.span);
            let call = std::mem::replace(
                expr,
                Expr {
                    kind: ExprKind::Constant(0),
                    ty,
                    span,
                    resource: None,
                },
            );
            expr.kind = ExprKind::AbortCall {
                call: Box::new(call),
                exits,
                propagates,
            };
            Ok(())
        }
        fn walk_block(
            &self,
            block: &mut Block,
            scopes: &mut Vec<(usize, Option<usize>)>,
            regions: &mut Vec<Region>,
        ) -> Result<()> {
            for statement in &mut block.statements {
                if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                    self.walk(value, scopes, regions)?;
                }
            }
            if let Some(tail) = block.tail.as_deref_mut() {
                self.walk(tail, scopes, regions)?;
            }
            Ok(())
        }
    }
    /// An enclosing non-tail handled body: the number of abortive scopes
    /// outside it and the abortive operations its token lets through.
    struct Region {
        scopes: usize,
        row: BTreeSet<usize>,
    }
    let mut bodies: Vec<Block> = program
        .functions
        .iter_mut()
        .map(|function| {
            std::mem::replace(
                &mut function.body,
                Block {
                    statements: vec![],
                    tail: None,
                    ty: Type::Unit,
                },
            )
        })
        .collect();
    let result = {
        let marker = Marker {
            program,
            may: &may,
            abortive: &abortive,
            row_operations: &row_operations,
            callable_effects: &callable_effects,
        };
        bodies
            .iter_mut()
            .try_for_each(|body| marker.walk_block(body, &mut Vec::new(), &mut Vec::new()))
    };
    for (function, body) in program.functions.iter_mut().zip(bodies) {
        function.body = body;
    }
    result
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
            Type::Fn(id) | Type::Once(id) | Type::Multi(id) => {
                program.function_types[id].effects & bit != 0
            }
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
/// Whether `expr` is a suspension point of an entry for `operation`.
fn is_entry_point(expr: &Expr, operation: usize, performs: &[BTreeSet<usize>]) -> bool {
    match &expr.kind {
        ExprKind::DynamicPerform {
            operation: performed,
            ..
        } => *performed == operation,
        ExprKind::Call(crate::executable::Target::Function(callee), _) => performs
            .get(*callee)
            .is_some_and(|set| set.contains(&operation)),
        _ => false,
    }
}

fn mark_entry_points(
    expr: &mut Expr,
    operation: usize,
    performs: &[BTreeSet<usize>],
    points: &mut usize,
    awaited: &mut BTreeSet<(usize, Option<usize>)>,
    nested: bool,
) -> Result<()> {
    let nested = match &expr.kind {
        ExprKind::HandlerPush {
            operation: inner, ..
        } if *inner == operation => return Ok(()),
        ExprKind::HandlerPush { .. }
        | ExprKind::Region { .. }
        | ExprKind::Suspendable(_)
        | ExprKind::AbortScope { .. } => true,
        _ => nested,
    };
    // E-ABORT-ENTRIES: a point that may abort was wrapped in an abort check
    // before lowering. The check moves to the caller: the point leaves this
    // region, and the region is the tail of the entry or continuation, so
    // its placeholder value returns to the awaiting caller, which tests the
    // abort word. Local exits cannot occur (a point inside a nested scope
    // is rejected).
    if let ExprKind::AbortCall { call, exits, .. } = &mut expr.kind
        && exits.is_empty()
        && !nested
        && is_entry_point(call, operation, performs)
    {
        let call = std::mem::replace(
            call.as_mut(),
            Expr {
                kind: ExprKind::Constant(0),
                ty: Type::Unit,
                span: expr.span,
                resource: None,
            },
        );
        let resource = expr.resource;
        *expr = call;
        if expr.resource.is_none() {
            expr.resource = resource;
        }
    }
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
        awaited.insert((callee, None));
    }
    expr.kind = ExprKind::Suspend {
        point: *points,
        call: Box::new(call),
        callee,
        capability: None,
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
        // E-ABORT-ENTRIES: an abort leaves the entry like `return` without
        // calling `k`; `k` is a resource of the entry (or was moved into the
        // continuation of the last point), so the abort path drops the
        // caller's pending continuation exactly once.
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
    key: EntryKey,
    result: Type,
) -> Result<(usize, bool)> {
    if let Some(entry) = context.entries.get(&(function, key)) {
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
    context.entries.insert((function, key), (index, true));
    // A `cap multi` entry is resumed several times: its continuation and its
    // tokens are `multi fn` values on the continuation stack.
    let multi =
        matches!(key, EntryKey::Capability(slot) if capability_multi(program, function, slot));
    let continuation = if multi {
        Type::Multi(multi_function_type(program, source.result, result))
    } else {
        Type::Once(function_type(program, source.result, result))
    };
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
        linear: !multi,
        pinned: false,
        grade: None,
        span: source.span,
    });
    if multi {
        local_resources.push(None);
    } else {
        resources.push(continuation);
        local_resources.push(Some(resources.len() - 1));
    }
    borrowed.push(false);
    copyable.push(multi);
    let mut body = source.body.clone();
    let mut points = 0;
    let mut awaited = BTreeSet::new();
    // The token a perform through the capability hands its handler.
    let mut capability_token = Type::Unit;
    match key {
        EntryKey::Operation(operation) => {
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
        }
        EntryKey::Capability(slot) => {
            let Type::Fn(arrow) = source.locals[slot].ty else {
                unreachable!("a capability parameter is a handler arrow")
            };
            let answer = program.function_types[arrow].result;
            capability_token = if multi {
                Type::Multi(multi_function_type(program, answer, result))
            } else {
                Type::Once(function_type(program, answer, result))
            };
            for_each_value_mut(&mut body, &mut |value| {
                mark_capability_points(
                    value,
                    slot,
                    &context.capability_performs,
                    &mut points,
                    &mut awaited,
                    false,
                )
            })?;
        }
    }
    let mut entries = BTreeMap::new();
    let mut awaited_allocates = false;
    for (callee, capability) in awaited {
        let callee_key = match (capability, key) {
            (Some(parameter), _) => EntryKey::Capability(parameter),
            (None, key) => key,
        };
        let (entry, allocates) = resumable_entry(program, context, callee, callee_key, result)?;
        let token = entry_token(program, callee, capability, result);
        entries.insert((callee, capability), (entry, token));
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
    let layouts = carrying_layouts(program);
    let origins = borrow_origins(&body, &locals, source.parameters, &|ty| {
        carries_in(ty, &layouts, &program.pointees, 0)
    });
    let host = Host {
        origins,
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
        carrying_layouts: carrying_layouts(program),
        pointees: program.pointees.clone(),
    };
    let spec = Spec {
        result,
        token: capability_token,
        multishot: multi,
        handler_writes: vec![],
        handler_refs: vec![],
        effects: None,
        awaited_allocates,
        finish: Some(k),
        entries,
        redirect: true,
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
        capability_parameters: source.capability_parameters.clone(),
        shared_environment: false,
    };
    for continuation in built.continuations {
        program.functions.push(continuation);
        program.foreign_functions.push(None);
    }
    context.entries.insert((function, key), (index, allocates));
    Ok((index, allocates))
}

/// Mark the suspension points of a resumable entry for the capability
/// parameter `slot`: performs through it and calls passing it to a `cap`
/// parameter its callee performs through, outside nested handlers.
fn mark_capability_points(
    expr: &mut Expr,
    slot: usize,
    performs: &[BTreeSet<usize>],
    points: &mut usize,
    awaited: &mut BTreeSet<(usize, Option<usize>)>,
    nested: bool,
) -> Result<()> {
    let nested = nested
        || matches!(
            expr.kind,
            ExprKind::HandlerPush { .. }
                | ExprKind::Region { .. }
                | ExprKind::Suspendable(_)
                | ExprKind::AbortScope { .. }
        );
    let mut result = Ok(());
    expr.for_each_child_mut(&mut |child| {
        if result.is_ok() {
            result = mark_capability_points(child, slot, performs, points, awaited, nested);
        }
    });
    result?;
    let await_parameter = match &expr.kind {
        _ if performs_through(expr, slot) => None,
        ExprKind::Call(crate::executable::Target::Function(callee), arguments) => {
            if arguments
                .iter()
                .filter(|argument| passes_slot(argument, slot))
                .count()
                > 1
            {
                return Err(Diagnostic::new(
                    expr.span,
                    "a capability that may be bound to a handler with code after 'resume' cannot be passed to two parameters of one call",
                ));
            }
            match arguments
                .iter()
                .position(|argument| passes_slot(argument, slot))
            {
                Some(parameter)
                    if performs
                        .get(*callee)
                        .is_some_and(|set| set.contains(&parameter)) =>
                {
                    Some((*callee, parameter))
                }
                _ => return Ok(()),
            }
        }
        _ => return Ok(()),
    };
    if nested {
        return Err(Diagnostic::new(
            expr.span,
            "a perform through a capability inside a nested handler or handled body cannot be resumed by its handler with code after 'resume'; perform it outside the nested 'handle'",
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
    expr.resource = call.resource.take();
    if let Some((callee, parameter)) = await_parameter {
        awaited.insert((callee, Some(parameter)));
    }
    expr.kind = ExprKind::Suspend {
        point: *points,
        call: Box::new(call),
        callee: await_parameter.map(|(callee, _)| callee),
        capability: await_parameter.map(|(_, parameter)| parameter),
    };
    Ok(())
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

/// A resumption token moved into a spawned task would run the rest of the
/// handled body in another task, which does not see the handle's dynamic
/// frames. Reject spawning a closure that captures a value of a resumption
/// token type of some suspendable body (directly, or through a local bound
/// to such a closure).
fn check_task_tokens(program: &Executable) -> Result<()> {
    fn tokens_in(expr: &Expr, out: &mut BTreeSet<Type>) {
        if let ExprKind::Suspendable(suspendable) = &expr.kind {
            out.insert(suspendable.token);
        }
        expr.for_each_child(&mut |child| tokens_in(child, out));
    }
    let mut tokens = BTreeSet::new();
    for function in &program.functions {
        let wrapper = Expr {
            kind: ExprKind::Block(function.body.clone()),
            ty: function.body.ty,
            span: function.span,
            resource: None,
        };
        tokens_in(&wrapper, &mut tokens);
    }
    if tokens.is_empty() {
        return Ok(());
    }
    // Whether a value of `ty` can hold a token (in a box, field, element...).
    let holds_token = |ty: Type| {
        let mut pending = vec![ty];
        let mut seen = BTreeSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            if tokens.contains(&ty) {
                return true;
            }
            match ty {
                Type::DynObj(_) | Type::Task(_) | Type::Thread(_) | Type::AllocatorContext => {
                    return true;
                }
                Type::Box(p)
                | Type::Vec(p)
                | Type::ArenaBox(p)
                | Type::AllocBox(p)
                | Type::AllocVec(p)
                | Type::Ref(p)
                | Type::RefMut(p)
                | Type::Slice(p)
                | Type::SliceMut(p)
                | Type::Annotated(p, _) => pending.push(program.pointees[p]),
                Type::Enum(id) | Type::Variants(id, _) => {
                    for variant in &program.enums[id].variants {
                        pending.extend(variant.fields.iter().copied());
                    }
                }
                Type::Union(id) => pending.extend(program.unions[id].members.iter().copied()),
                // A closure value may itself have captured a token.
                Type::Once(_) => return true,
                _ => {}
            }
        }
        false
    };
    let captures_token = |expr: &Expr, holders: &Slots| {
        let mut expr = expr;
        while let ExprKind::Coerce { value, .. } = &expr.kind {
            expr = value;
        }
        match &expr.kind {
            ExprKind::FnValue { captures, .. } => captures.iter().any(|capture| {
                holds_token(capture.ty)
                    || matches!(capture.kind, ExprKind::Local(s) | ExprKind::Move(s) if holders.contains(&s))
            }),
            ExprKind::Local(slot) | ExprKind::Move(slot) => holders.contains(slot),
            _ => false,
        }
    };
    for function in &program.functions {
        // Locals holding a closure that captures a token, to a fixed point.
        let mut holders = Slots::new();
        loop {
            let before = holders.len();
            fn bindings<'a>(block: &'a Block, out: &mut Vec<(usize, &'a Expr)>) {
                for statement in &block.statements {
                    if let Statement::Let(slot, value) = statement {
                        out.push((*slot, value));
                    }
                    if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                        collect(value, out);
                    }
                }
                if let Some(tail) = &block.tail {
                    collect(tail, out);
                }
            }
            fn collect<'a>(expr: &'a Expr, out: &mut Vec<(usize, &'a Expr)>) {
                if let ExprKind::Assign(slot, value) = &expr.kind {
                    out.push((*slot, value));
                }
                let mut blocks = Vec::new();
                let mut children = Vec::new();
                block_children(expr, &mut |block| blocks.push(block), &mut |child| {
                    children.push(child)
                });
                for block in blocks {
                    bindings(block, out);
                }
                for child in children {
                    collect(child, out);
                }
            }
            let mut pairs = Vec::new();
            bindings(&function.body, &mut pairs);
            for (slot, value) in pairs {
                if captures_token(value, &holders) {
                    holders.insert(slot);
                }
            }
            if holders.len() == before {
                break;
            }
        }
        fn spawns<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
            if let ExprKind::TaskSpawn { body, .. } = &expr.kind {
                out.push(expr);
                let _ = body;
            }
            expr.for_each_child(&mut |child| spawns(child, out));
        }
        let mut found = Vec::new();
        let wrapper = Expr {
            kind: ExprKind::Block(function.body.clone()),
            ty: function.body.ty,
            span: function.span,
            resource: None,
        };
        spawns(&wrapper, &mut found);
        for spawn in found {
            let ExprKind::TaskSpawn { body, .. } = &spawn.kind else {
                continue;
            };
            if captures_token(body, &holders) {
                return Err(Diagnostic::new(
                    spawn.span,
                    "a resumption token cannot be moved into a spawned task: the rest of the handled body would run in another task, without the handle's dynamic handlers; resume it in the handler's own task",
                ));
            }
        }
    }
    Ok(())
}
