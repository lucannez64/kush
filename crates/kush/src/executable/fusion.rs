//! Automatic map fusion: which calls may fuse, and the rewrite.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

/// Automatic fusion equivalence analysis.
///
/// A callback is eligible only when:
///
/// * it is a noncapturing `fn(...)` value;
/// * its declared effect row contains neither `io` nor `suspend`;
/// * its body has no operation that can panic (`fusion_may_panic`): since
///   FND-ROWS-PANIC a row no longer says so, and fusing two callbacks that
///   may panic would change which panic is reported;
/// * its body is structurally total: no loops, no direct or indirect recursion,
///   no indirect calls, and no task operations;
/// * every direct callee is itself eligible.
///
/// This establishes structural totality, not allocation commutativity:
/// refused allocations produce observable values. The merge separately checks
/// that only one allocation stage is active and the other stages cannot change
/// heap ownership, so allocator operations retain their original order.
/// The pass is deliberately conservative: it does not try to prove termination
/// for loops, and it rejects indirect calls and recursion outright.
pub(super) fn fusion_function_safe(
    index: usize,
    signatures: &[Signature],
    bodies: &[Option<Function>],
    memo: &mut Vec<Option<bool>>,
    visiting: &mut Vec<bool>,
) -> bool {
    if let Some(result) = memo.get(index).copied().flatten() {
        return result;
    }
    if visiting.get(index).copied().unwrap_or(false) {
        // Recursion (direct or mutual) has no checked termination argument.
        return false;
    }
    let Some(signature) = signatures.get(index) else {
        return false;
    };
    if signature.effects & !ALLOC != 0 {
        return false;
    }
    let Some(Some(body)) = bodies.get(index) else {
        return false;
    };
    if visiting.len() <= index {
        visiting.resize(index + 1, false);
    }
    visiting[index] = true;
    let safe = fusion_block_safe(&body.body, signatures, bodies, memo, visiting);
    visiting[index] = false;
    if memo.len() <= index {
        memo.resize(index + 1, None);
    }
    memo[index] = Some(safe);
    safe
}

/// FND-ROWS-PANIC: whether this node (not its children) may panic: checked
/// integer arithmetic and negation, range slicing, builtin operations (bounds,
/// capacity and infallible allocation), and fixed-capacity array writes.
/// Conservative: arithmetic the prover showed in range still counts, and
/// every builtin call is treated as able to panic.
pub(super) fn fusion_may_panic(expr: &Expr) -> bool {
    use crate::lexer::Kind;
    let integer = expr.ty.float_kind().is_none();
    match &expr.kind {
        ExprKind::Binary(
            Kind::Plus
            | Kind::Minus
            | Kind::Star
            | Kind::Slash
            | Kind::Percent
            | Kind::Shl
            | Kind::Shr,
            _,
            _,
        ) => integer,
        ExprKind::Unary(Kind::Minus, _) => integer,
        ExprKind::Call(target, _) => !matches!(target, Target::Function(_)),
        ExprKind::Slice { .. }
        | ExprKind::BoxNew(_)
        | ExprKind::ArenaAlloc { .. }
        | ExprKind::DynArrayPush { .. }
        | ExprKind::DynArraySet { .. }
        | ExprKind::DynArrayPop { .. }
        | ExprKind::DynArrayFill { .. }
        | ExprKind::DynamicPerform { .. } => true,
        _ => false,
    }
}

pub(super) fn fusion_block_safe(
    block: &Block,
    signatures: &[Signature],
    bodies: &[Option<Function>],
    memo: &mut Vec<Option<bool>>,
    visiting: &mut Vec<bool>,
) -> bool {
    block.statements.iter().all(|statement| match statement {
        Statement::Let(_, value) | Statement::Expr(value) => {
            fusion_expr_safe(value, signatures, bodies, memo, visiting)
        }
        Statement::Declare(_) => true,
    }) && block
        .tail
        .as_ref()
        .is_none_or(|tail| fusion_expr_safe(tail, signatures, bodies, memo, visiting))
}

pub(super) fn fusion_expr_safe(
    expr: &Expr,
    signatures: &[Signature],
    bodies: &[Option<Function>],
    memo: &mut Vec<Option<bool>>,
    visiting: &mut Vec<bool>,
) -> bool {
    let safe = |value: &Expr,
                signatures: &[Signature],
                bodies: &[Option<Function>],
                memo: &mut Vec<Option<bool>>,
                visiting: &mut Vec<bool>| {
        fusion_expr_safe(value, signatures, bodies, memo, visiting)
    };
    if fusion_may_panic(expr) {
        return false;
    }
    match &expr.kind {
        ExprKind::Constant(_)
        | ExprKind::Erased(_)
        | ExprKind::BytesLiteral(_)
        | ExprKind::Local(_)
        | ExprKind::Move(_)
        | ExprKind::Borrow(_)
        | ExprKind::Peek(_)
        | ExprKind::ArenaNew
        | ExprKind::DynArrayNew { .. } => true,
        // A whole-value reference read/write is never fused: it depends on
        // aliasing storage and has no total, capture-free callback shape.
        ExprKind::RefRead(_)
        | ExprKind::DerefWrite(_, _)
        | ExprKind::BoxWrite(_, _)
        | ExprKind::BorrowPlace(_)
        | ExprKind::BorrowInit { .. }
        | ExprKind::InitOwner { .. }
        | ExprKind::PlaceIndex { .. } => false,
        // No loop has a checked termination argument here.
        ExprKind::While(..) | ExprKind::Loop(_) => false,
        ExprKind::Call(Target::Function(index), arguments) => {
            fusion_function_safe(*index, signatures, bodies, memo, visiting)
                && arguments
                    .iter()
                    .all(|argument| safe(argument, signatures, bodies, memo, visiting))
        }
        ExprKind::Call(
            Target::Io(..)
            | Target::Host(..)
            | Target::Print
            | Target::PrintInt(_)
            | Target::PrintFloat(_)
            | Target::Panic,
            _,
        ) => false,
        ExprKind::Call(_, arguments) => arguments
            .iter()
            .all(|argument| safe(argument, signatures, bodies, memo, visiting)),
        // An opaque callable can select an effectful or divergent body.
        ExprKind::CallIndirect { .. } => false,
        ExprKind::TaskSpawn { .. }
        | ExprKind::TaskScope { .. }
        | ExprKind::TaskYield
        | ExprKind::TaskCheckCancel
        | ExprKind::TaskCancel(_)
        | ExprKind::TaskJoin { .. } => false,
        // Allocator construction only packages code pointers, so it is
        // inert; every container operation can invoke a user callback or
        // allocate, so it is never fusion-safe.
        ExprKind::AllocatorNew {
            alloc,
            free,
            realloc,
        } => {
            safe(alloc, signatures, bodies, memo, visiting)
                && safe(free, signatures, bodies, memo, visiting)
                && realloc
                    .as_deref()
                    .is_none_or(|realloc| safe(realloc, signatures, bodies, memo, visiting))
        }
        ExprKind::AllocBoxNew { .. }
        | ExprKind::AllocBoxTryNew { .. }
        | ExprKind::AllocBoxRead(_)
        | ExprKind::AllocBoxTake(_)
        | ExprKind::AllocVecNew { .. }
        // Building a context allocates compiler-owned storage and sharing
        // changes a reference count, so neither is an inert fusion stage.
        | ExprKind::AllocatorContextNew { .. }
        | ExprKind::AllocatorContextShare(_) => false,
        // A suspension runs arbitrary handler code.
        ExprKind::Suspendable(_)
        | ExprKind::Suspend { .. }
        | ExprKind::Region { .. }
        | ExprKind::RegionExit { .. }
        | ExprKind::HandlerDepth
        | ExprKind::HandlerRedirect { .. }
        | ExprKind::ContinuationScope { .. }
        | ExprKind::TryExit { .. }
        // An abort leaves code that a fused stage would have to resume.
        | ExprKind::AbortScope { .. }
        | ExprKind::AbortExit { .. }
        | ExprKind::AbortPerform { .. }
        | ExprKind::AbortCall { .. } => false,
        ExprKind::FnValue { function, captures } => {
            captures
                .iter()
                .all(|capture| safe(capture, signatures, bodies, memo, visiting))
                && fusion_function_safe(*function, signatures, bodies, memo, visiting)
        }
        ExprKind::Coerce { value, .. }
        | ExprKind::Try { value, .. }
        | ExprKind::BoxNew(value)
        | ExprKind::BoxTake(value)
        | ExprKind::BoxRead(value)
        | ExprKind::BoxTryNew { value, .. }
        | ExprKind::ArenaBoxRead(value)
        | ExprKind::ArenaBoxTake(value)
        | ExprKind::BytesTryWithCapacity {
            capacity: value, ..
        }
        | ExprKind::Drop(value)
        | ExprKind::Unary(_, value)
        | ExprKind::Assign(_, value)
        | ExprKind::Return(value)
        | ExprKind::Project(value, _) => safe(value, signatures, bodies, memo, visiting),
        ExprKind::ArenaAlloc { arena, value } => {
            safe(arena, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::ArenaNewWith { strategy } => safe(strategy, signatures, bodies, memo, visiting),
        ExprKind::ArenaTryAlloc { arena, value, .. } => {
            safe(arena, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArrayPush { array, value, .. } => {
            safe(array, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArrayFill { length, value, .. } => {
            safe(length, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::HandlerPush { handler, body, .. } => {
            safe(handler, signatures, bodies, memo, visiting)
                && fusion_block_safe(body, signatures, bodies, memo, visiting)
        }
        ExprKind::DynamicPerform {
            payload, resume, ..
        } => {
            safe(payload, signatures, bodies, memo, visiting)
                && safe(resume, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArraySet {
            array,
            index,
            value,
            ..
        } => {
            safe(array, signatures, bodies, memo, visiting)
                && safe(index, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::DynArrayPop { array, .. } => safe(array, signatures, bodies, memo, visiting),
        ExprKind::BoxReuse { owner, payload }
        | ExprKind::BoxReuseGrow { owner, payload }
        | ExprKind::BoxTryReuse { owner, payload, .. } => {
            safe(owner, signatures, bodies, memo, visiting)
                && safe(payload, signatures, bodies, memo, visiting)
        }
        ExprKind::RefAssign(reference, _, value) => {
            safe(reference, signatures, bodies, memo, visiting)
                && safe(value, signatures, bodies, memo, visiting)
        }
        ExprKind::Binary(_, left, right)
        | ExprKind::BytesAt(left, right)
        | ExprKind::StructEq { left, right, .. }
        | ExprKind::DynArrayEqual { left, right, .. } => {
            safe(left, signatures, bodies, memo, visiting)
                && safe(right, signatures, bodies, memo, visiting)
        }
        ExprKind::Construct { fields, .. } => fields
            .iter()
            .all(|field| safe(field, signatures, bodies, memo, visiting)),
        ExprKind::Block(block) => fusion_block_safe(block, signatures, bodies, memo, visiting),
        ExprKind::If(condition, yes, no) => {
            safe(condition, signatures, bodies, memo, visiting)
                && fusion_block_safe(yes, signatures, bodies, memo, visiting)
                && fusion_block_safe(no, signatures, bodies, memo, visiting)
        }
        ExprKind::Match(value, arms) => {
            safe(value, signatures, bodies, memo, visiting)
                && arms.iter().all(|arm| {
                    arm.guard
                        .as_ref()
                        .is_none_or(|guard| safe(guard, signatures, bodies, memo, visiting))
                        && safe(&arm.body, signatures, bodies, memo, visiting)
                })
        }
        ExprKind::VecMap {
            vector, callbacks, ..
        } => {
            safe(vector, signatures, bodies, memo, visiting)
                && callbacks
                    .iter()
                    .all(|callback| safe(callback, signatures, bodies, memo, visiting))
        }
        ExprKind::Slice {
            base, start, end, ..
        } => {
            safe(base, signatures, bodies, memo, visiting)
                && start
                    .as_ref()
                    .is_none_or(|start| safe(start, signatures, bodies, memo, visiting))
                && end
                    .as_ref()
                    .is_none_or(|end| safe(end, signatures, bodies, memo, visiting))
        }
        ExprKind::Break(value, _) => value
            .as_ref()
            .is_none_or(|value| safe(value, signatures, bodies, memo, visiting)),
        // `Continue` carries no expression children.
        ExprKind::Continue(_) => true,
    }
}

/// Select automatic nested in-place map fusion after every body has been
/// checked. A merge is allowed only when every callback in both steps is
/// fusion-safe and the intermediate layout agrees. For a step with a non-empty
/// (alloc-only) effect row, the intermediate must also be non-owning: the
/// fused traversal keeps one intermediate live at a time instead of all of
/// them, and this restriction keeps every drop-order observation identical.
pub(super) fn automatic_fusion(types: &Types<'_>, functions: &mut Functions<'_>) -> usize {
    let mut memo: Vec<Option<bool>> = vec![None; functions.bodies.len()];
    let mut visiting = vec![false; functions.bodies.len()];
    let mut safety = vec![false; functions.bodies.len()];
    for (index, entry) in safety.iter_mut().enumerate() {
        *entry = fusion_function_safe(
            index,
            &functions.signatures,
            &functions.bodies,
            &mut memo,
            &mut visiting,
        );
    }
    let signatures = &functions.signatures;
    let mut fusions = 0;
    for body in functions.bodies.iter_mut().flatten() {
        fuse_block(&mut body.body, types, signatures, &safety, &mut fusions);
    }
    fusions
}

pub(super) fn fuse_block(
    block: &mut Block,
    types: &Types<'_>,
    signatures: &[Signature],
    safety: &[bool],
    fusions: &mut usize,
) {
    for statement in &mut block.statements {
        match statement {
            Statement::Let(_, value) | Statement::Expr(value) => {
                fuse_expr(value, types, signatures, safety, fusions)
            }
            Statement::Declare(_) => {}
        }
    }
    if let Some(tail) = &mut block.tail {
        fuse_expr(tail, types, signatures, safety, fusions);
    }
}

pub(super) fn fuse_expr(
    expr: &mut Expr,
    types: &Types<'_>,
    signatures: &[Signature],
    safety: &[bool],
    fusions: &mut usize,
) {
    let safe_callback = |callback: &Expr| -> bool {
        matches!(
            &callback.kind,
            ExprKind::FnValue { function, captures }
                if captures.is_empty() && safety.get(*function).copied().unwrap_or(false)
        )
    };
    match &mut expr.kind {
        ExprKind::Coerce { value, .. }
        | ExprKind::Try { value, .. }
        | ExprKind::BoxNew(value)
        | ExprKind::BoxTake(value)
        | ExprKind::BoxRead(value)
        | ExprKind::BoxTryNew { value, .. }
        | ExprKind::ArenaBoxRead(value)
        | ExprKind::ArenaBoxTake(value)
        | ExprKind::AllocBoxRead(value)
        | ExprKind::AllocBoxTake(value)
        | ExprKind::BytesTryWithCapacity {
            capacity: value, ..
        }
        | ExprKind::Drop(value)
        | ExprKind::Unary(_, value)
        | ExprKind::Assign(_, value)
        | ExprKind::Return(value)
        | ExprKind::Project(value, _)
        | ExprKind::BorrowPlace(value)
        | ExprKind::InitOwner { value, .. }
        | ExprKind::BorrowInit { value, .. }
        | ExprKind::RefRead(value) => fuse_expr(value, types, signatures, safety, fusions),
        ExprKind::PlaceIndex { base, index, .. } => {
            fuse_expr(base, types, signatures, safety, fusions);
            fuse_expr(index, types, signatures, safety, fusions);
        }
        ExprKind::DerefWrite(reference, value) | ExprKind::BoxWrite(reference, value) => {
            fuse_expr(reference, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::ArenaAlloc { arena, value } => {
            fuse_expr(arena, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::AllocatorNew {
            alloc,
            free,
            realloc,
        } => {
            fuse_expr(alloc, types, signatures, safety, fusions);
            fuse_expr(free, types, signatures, safety, fusions);
            if let Some(realloc) = realloc {
                fuse_expr(realloc, types, signatures, safety, fusions);
            }
        }
        ExprKind::AllocatorContextNew { value, .. } | ExprKind::AllocatorContextShare(value) => {
            fuse_expr(value, types, signatures, safety, fusions)
        }
        ExprKind::Suspendable(suspendable) => {
            fuse_block(&mut suspendable.body, types, signatures, safety, fusions)
        }
        ExprKind::Suspend { call, .. } => fuse_expr(call, types, signatures, safety, fusions),
        ExprKind::Region { body, finish, .. } => {
            fuse_block(body, types, signatures, safety, fusions);
            if let Some(finish) = finish {
                fuse_expr(finish, types, signatures, safety, fusions);
            }
        }
        ExprKind::RegionExit { value, .. }
        | ExprKind::TryExit { value, .. }
        | ExprKind::AbortExit { value, .. }
        | ExprKind::AbortPerform { value, .. }
        | ExprKind::AbortCall { call: value, .. } => {
            fuse_expr(value, types, signatures, safety, fusions)
        }
        ExprKind::AbortScope { body, handler, .. } => {
            fuse_block(body, types, signatures, safety, fusions);
            fuse_expr(handler, types, signatures, safety, fusions);
        }
        ExprKind::HandlerDepth => {}
        ExprKind::ContinuationScope { body } => {
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::HandlerRedirect { depth, body } => {
            fuse_expr(depth, types, signatures, safety, fusions);
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::AllocBoxNew { allocator, value }
        | ExprKind::AllocBoxTryNew {
            allocator, value, ..
        } => {
            fuse_expr(allocator, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::AllocVecNew {
            allocator,
            capacity,
            ..
        } => {
            fuse_expr(allocator, types, signatures, safety, fusions);
            if let Some(capacity) = capacity {
                fuse_expr(capacity, types, signatures, safety, fusions);
            }
        }
        ExprKind::ArenaNewWith { strategy } => {
            fuse_expr(strategy, types, signatures, safety, fusions);
        }
        ExprKind::ArenaTryAlloc { arena, value, .. } => {
            fuse_expr(arena, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArrayPush { array, value, .. } => {
            fuse_expr(array, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArrayFill { length, value, .. } => {
            fuse_expr(length, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::HandlerPush { handler, body, .. } => {
            fuse_expr(handler, types, signatures, safety, fusions);
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::DynamicPerform {
            payload, resume, ..
        } => {
            fuse_expr(payload, types, signatures, safety, fusions);
            fuse_expr(resume, types, signatures, safety, fusions);
        }
        ExprKind::DynArraySet {
            array,
            index,
            value,
            ..
        } => {
            fuse_expr(array, types, signatures, safety, fusions);
            fuse_expr(index, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::DynArrayPop { array, .. } => {
            fuse_expr(array, types, signatures, safety, fusions);
        }
        ExprKind::BoxReuse { owner, payload }
        | ExprKind::BoxReuseGrow { owner, payload }
        | ExprKind::BoxTryReuse { owner, payload, .. } => {
            fuse_expr(owner, types, signatures, safety, fusions);
            fuse_expr(payload, types, signatures, safety, fusions);
        }
        ExprKind::RefAssign(reference, _, value) => {
            fuse_expr(reference, types, signatures, safety, fusions);
            fuse_expr(value, types, signatures, safety, fusions);
        }
        ExprKind::Binary(_, left, right)
        | ExprKind::BytesAt(left, right)
        | ExprKind::StructEq { left, right, .. }
        | ExprKind::DynArrayEqual { left, right, .. } => {
            fuse_expr(left, types, signatures, safety, fusions);
            fuse_expr(right, types, signatures, safety, fusions);
        }
        ExprKind::Construct { fields, .. } => {
            for field in fields {
                fuse_expr(field, types, signatures, safety, fusions);
            }
        }
        ExprKind::Call(_, arguments) => {
            for argument in arguments {
                fuse_expr(argument, types, signatures, safety, fusions);
            }
        }
        ExprKind::Block(block) => fuse_block(block, types, signatures, safety, fusions),
        ExprKind::If(condition, yes, no) => {
            fuse_expr(condition, types, signatures, safety, fusions);
            fuse_block(yes, types, signatures, safety, fusions);
            fuse_block(no, types, signatures, safety, fusions);
        }
        ExprKind::Match(value, arms) => {
            fuse_expr(value, types, signatures, safety, fusions);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    fuse_expr(guard, types, signatures, safety, fusions);
                }
                fuse_expr(&mut arm.body, types, signatures, safety, fusions);
            }
        }
        ExprKind::FnValue { captures, .. } => {
            for capture in captures {
                fuse_expr(capture, types, signatures, safety, fusions);
            }
        }
        ExprKind::CallIndirect { callee, arguments } => {
            fuse_expr(callee, types, signatures, safety, fusions);
            for argument in arguments {
                fuse_expr(argument, types, signatures, safety, fusions);
            }
        }
        ExprKind::TaskSpawn { body, .. } | ExprKind::TaskScope { body, .. } => {
            fuse_expr(body, types, signatures, safety, fusions)
        }
        ExprKind::TaskCancel(value) => fuse_expr(value, types, signatures, safety, fusions),
        ExprKind::TaskJoin { task, .. } => fuse_expr(task, types, signatures, safety, fusions),
        ExprKind::Slice {
            base, start, end, ..
        } => {
            fuse_expr(base, types, signatures, safety, fusions);
            if let Some(start) = start {
                fuse_expr(start, types, signatures, safety, fusions);
            }
            if let Some(end) = end {
                fuse_expr(end, types, signatures, safety, fusions);
            }
        }
        ExprKind::Break(value, _) => {
            if let Some(value) = value {
                fuse_expr(value, types, signatures, safety, fusions);
            }
        }
        ExprKind::VecMap {
            vector,
            callbacks,
            source,
            target: _,
            grow,
        } => {
            fuse_expr(vector, types, signatures, safety, fusions);
            for callback in callbacks.iter_mut() {
                fuse_expr(callback, types, signatures, safety, fusions);
            }
            // A growth-capable transform may allocate/move the vector. Merging
            // it with another pass can change allocation and callback order, so
            // it is never an automatic fusion candidate.
            if *grow {
                return;
            }
            let mut merged = Vec::new();
            std::mem::swap(callbacks, &mut merged);
            let mut cursor = std::mem::replace(vector, placeholder_expr(expr.span));
            loop {
                let compatible = match &cursor.kind {
                    ExprKind::VecMap {
                        target: inner_target,
                        callbacks: inner_callbacks,
                        grow: inner_grow,
                        ..
                    } => {
                        !*inner_grow
                            && *inner_target == *source
                            && inner_callbacks
                                .iter()
                                .chain(merged.iter())
                                .all(safe_callback)
                            && fusion_preserves_allocation_order(
                                types,
                                inner_callbacks.iter().chain(merged.iter()),
                            )
                    }
                    _ => false,
                };
                if !compatible {
                    break;
                }
                let old = std::mem::replace(
                    &mut *cursor,
                    Expr {
                        kind: ExprKind::Constant(0),
                        ty: Type::Unit,
                        span: expr.span,
                        resource: None,
                    },
                );
                let old_ty = old.ty;
                let old_span = old.span;
                let old_resource = old.resource;
                let ExprKind::VecMap {
                    vector: inner_vector,
                    callbacks: mut inner_callbacks,
                    source: inner_source,
                    target: inner_target,
                    grow: inner_grow,
                } = old.kind
                else {
                    unreachable!("checked compatible map")
                };
                let nonempty = inner_callbacks
                    .iter()
                    .chain(merged.iter())
                    .any(|callback| callback_effects(types, callback) != 0);
                if nonempty
                    && crate::runtime_types::type_owns(&types.enums, &types.unions, inner_target, 0)
                {
                    // Restore the untouched layer and stop: an effectful step
                    // must not change when an owning intermediate is dropped.
                    cursor = Box::new(Expr {
                        kind: ExprKind::VecMap {
                            vector: inner_vector,
                            callbacks: inner_callbacks,
                            source: inner_source,
                            target: inner_target,
                            grow: inner_grow,
                        },
                        ty: old_ty,
                        span: old_span,
                        resource: old_resource,
                    });
                    break;
                }
                inner_callbacks.append(&mut merged);
                merged = inner_callbacks;
                *source = inner_source;
                cursor = inner_vector;
                *fusions += 1;
            }
            *callbacks = merged;
            *vector = cursor;
        }
        ExprKind::Constant(_)
        | ExprKind::Erased(_)
        | ExprKind::BytesLiteral(_)
        | ExprKind::Local(_)
        | ExprKind::Move(_)
        | ExprKind::Borrow(_)
        | ExprKind::Peek(_)
        | ExprKind::ArenaNew
        | ExprKind::DynArrayNew { .. }
        | ExprKind::TaskYield
        | ExprKind::TaskCheckCancel
        | ExprKind::Continue(_) => {}
        ExprKind::While(condition, body) => {
            fuse_expr(condition, types, signatures, safety, fusions);
            fuse_block(body, types, signatures, safety, fusions);
        }
        ExprKind::Loop(body) => fuse_block(body, types, signatures, safety, fusions),
    }
}

pub(super) fn callback_effects(types: &Types<'_>, callback: &Expr) -> u16 {
    match callback.ty {
        Type::Fn(id) => types.function_types[id].effects,
        _ => u16::MAX,
    }
}

pub(super) fn fusion_preserves_allocation_order<'a>(
    types: &Types<'_>,
    callbacks: impl Iterator<Item = &'a Expr>,
) -> bool {
    let callbacks = callbacks.collect::<Vec<_>>();
    let allocating = callbacks
        .iter()
        .filter(|callback| callback_effects(types, callback) != 0)
        .count();
    if allocating == 0 {
        return true;
    }
    if allocating > 1 {
        // Two fallible stages can consume the allocator budget in a different
        // order even when they are total and produce non-owning values.
        return false;
    }
    callbacks.into_iter().all(|callback| {
        if callback_effects(types, callback) != 0 {
            return true;
        }
        let Type::Fn(id) = callback.ty else {
            return false;
        };
        let signature = &types.function_types[id];
        signature
            .parameters
            .iter()
            .copied()
            .chain(std::iter::once(signature.result))
            .all(|ty| !crate::runtime_types::type_owns(&types.enums, &types.unions, ty, 0))
    })
}
