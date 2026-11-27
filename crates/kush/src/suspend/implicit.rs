//! Declared operations as hidden capability parameters
//! (FND-HANDLERS-ONE-PARAMS to -CELLS, docs/one-handler-model.md section 2).
//!
//! A capability is an `i64`: the cell of a `handle` activation (its frame),
//! or the payload buffer of an abortive one. A function that may perform
//! declared operations it does not handle gets a copy taking one more
//! capability per such operation, after its written parameters and in
//! operation-id order. A perform by name names the innermost enclosing
//! `handle`'s cell or the hidden parameter, and the frame is used without a
//! search; a direct call passes, per operation of the callee, the same.
//! Code that has neither (entry points, arrows kept on the dynamic stack)
//! keeps the original function, whose performs still search. An await point
//! under a handler with code after `resume` resumes the copy through its
//! capability parameter.
//!
//! A function value takes the capabilities its arrow's row names the same
//! way (decision D1: bound at each call): its function is a copy for those
//! operations, the arrow gains the parameters, and every indirect call passes
//! them. Task bodies capture them where the builtin is called (rule 8).
//! Arrows whose values reach code that calls them without capabilities
//! (handlers, callback builtins, foreign functions) keep the dynamic stack
//! until HANDLERS-ONE-CALLBACKS.
use super::{Result, performs_with};
use crate::executable::{Block, Executable, Expr, ExprKind, Local, Statement, Target, Type};
use std::collections::{BTreeMap, BTreeSet};

/// The `i64` local holding an operation's capability in some scope: the
/// cell of an enclosing `handle` (FND-HANDLERS-ONE-CELLS), the payload
/// buffer of an enclosing abortive `handle`, or a hidden parameter.
type Capability = usize;

/// A function the pass adds.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Request {
    /// A copy of `function` taking the capabilities of `operations` as
    /// parameters after its written ones, or as closure captures after its
    /// own when `captured`.
    Copy {
        function: usize,
        operations: Vec<usize>,
        captured: bool,
    },
}

struct Pass<'a> {
    /// Operations each original function needs a capability for, in id
    /// order; empty for functions that are not copied.
    needs: &'a [Vec<usize>],
    /// Operations that get capabilities: those performed by name.
    caps: &'a BTreeSet<usize>,
    /// Operations whose capabilities a function value of each arrow type
    /// takes; empty for arrows that keep the dynamic stack.
    values: &'a [Vec<usize>],
    /// Operations whose capabilities each trait-object call and each
    /// closed-world union call passes to its members.
    dyn_calls: &'a [Vec<usize>],
    union_calls: &'a [Vec<usize>],
    originals: usize,
    /// Index of each added function, in request order.
    copies: BTreeMap<Request, usize>,
    order: Vec<Request>,
    /// For an arrow whose values a task builtin calls: its form without
    /// capability parameters, the type of the body the builtin receives.
    split: &'a BTreeMap<usize, usize>,
    /// Operations of each arrow's row, also for arrows that keep the
    /// dynamic stack.
    rows: &'a [Vec<usize>],
}

impl Pass<'_> {
    fn copy_of(&mut self, function: usize, operations: &[usize]) -> usize {
        self.copy_with(function, operations, false)
    }

    fn copy_with(&mut self, function: usize, operations: &[usize], captured: bool) -> usize {
        self.request(Request::Copy {
            function,
            operations: operations.to_vec(),
            captured,
        })
    }

    fn request(&mut self, key: Request) -> usize {
        if let Some(copy) = self.copies.get(&key) {
            return *copy;
        }
        let copy = self.originals + self.order.len();
        self.order.push(key.clone());
        self.copies.insert(key, copy);
        copy
    }

    /// The operations whose capabilities a value of callable type `ty`
    /// takes.
    fn value_operations(&self, ty: Type) -> &[usize] {
        match ty {
            Type::Fn(id) | Type::Once(id) | Type::Multi(id) => {
                self.values.get(id).map_or(&[], Vec::as_slice)
            }
            _ => &[],
        }
    }

    /// The capability of `operation` at this point.
    fn capability(scope: &Scope, operation: usize) -> Option<Capability> {
        scope
            .capabilities
            .get(&operation)
            .or_else(|| scope.hidden.get(&operation))
            .copied()
    }

    /// The capability arguments for `operations` at this point. Without
    /// one, zero: the perform searches the dynamic stack.
    fn supply(&self, operations: &[usize], scope: &Scope, span: crate::Span) -> Vec<Expr> {
        operations
            .iter()
            .map(|&operation| Expr {
                kind: match Self::capability(scope, operation) {
                    Some(slot) => ExprKind::Local(slot),
                    None => ExprKind::Constant(0),
                },
                ty: Type::I64,
                span,
                resource: None,
            })
            .collect()
    }

    fn block(&mut self, block: &mut Block, scope: &Scope) {
        for statement in &mut block.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                self.expr(value, scope);
            }
        }
        if let Some(tail) = block.tail.as_deref_mut() {
            self.expr(tail, scope);
        }
    }

    fn expr(&mut self, expr: &mut Expr, scope: &Scope) {
        // Rule 8: the runtime calls a task body without capabilities. The
        // checker requires a written lambda there, which captures them where
        // the builtin is called. A spawned task thereby keeps each
        // noncapturing handler (decision D3); the runtime treats the cell of
        // another task's capturing handler as missing. The builtin receives
        // the lambda at its arrow without capability parameters.
        if let ExprKind::TaskScope { body, .. } | ExprKind::TaskSpawn { body, .. } = &mut expr.kind
            && let Type::Once(arrow) = body.ty
            && let Some(&bare) = self.split.get(&arrow)
            && let ExprKind::FnValue { function, captures } = &mut body.kind
            && *function < self.originals
        {
            let operations = self.rows[arrow].clone();
            let supplied = self.supply(&operations, scope, body.span);
            for capture in captures.iter_mut() {
                self.expr(capture, scope);
            }
            *function = self.copy_with(*function, &operations, true);
            captures.extend(supplied);
            body.ty = Type::Once(bare);
            return;
        }
        if let ExprKind::HandlerPush {
            operation,
            handler,
            body,
            cell,
            ..
        } = &mut expr.kind
        {
            self.expr(handler, scope);
            let mut inner = scope.clone();
            if self.caps.contains(operation) {
                match cell {
                    Some(cell) => inner.capabilities.insert(*operation, *cell),
                    None => inner.capabilities.remove(operation),
                };
            }
            self.block(body, &inner);
            return;
        }
        // FND-HANDLERS-ONE-ABORT: an abortive scope's payload buffer is the
        // capability of its operation in the body.
        if let ExprKind::AbortScope {
            body,
            handler,
            operation: Some(operation),
            capability: Some(slot),
            ..
        } = &mut expr.kind
        {
            self.expr(handler, scope);
            let mut inner = scope.clone();
            if self.caps.contains(operation) {
                inner.capabilities.insert(*operation, *slot);
            }
            self.block(body, &inner);
            return;
        }
        expr.for_each_child_mut(&mut |child| self.expr(child, scope));
        match &mut expr.kind {
            // A perform by name uses its operation's capability: the
            // innermost enclosing `handle`'s cell or the hidden parameter.
            ExprKind::DynamicPerform {
                operation,
                cell: cell @ None,
                ..
            } => {
                if let Some(slot) = Self::capability(scope, *operation) {
                    *cell = Some(Box::new(Expr {
                        kind: ExprKind::Local(slot),
                        ty: Type::I64,
                        span: expr.span,
                        resource: None,
                    }));
                }
            }
            ExprKind::AbortPerform {
                operation,
                capability: capability @ None,
                ..
            } => {
                if let Some(slot) = Self::capability(scope, *operation) {
                    *capability = Some(Box::new(Expr {
                        kind: ExprKind::Local(slot),
                        ty: Type::I64,
                        span: expr.span,
                        resource: None,
                    }));
                }
            }
            ExprKind::Call(Target::Function(callee), arguments)
                if *callee < self.originals && !self.needs[*callee].is_empty() =>
            {
                // Code with no capability for any of them keeps the
                // original, which performs through the dynamic stack.
                let supplied = self.needs[*callee].iter().any(|operation| {
                    scope.capabilities.contains_key(operation)
                        || scope.hidden.contains_key(operation)
                });
                if !supplied {
                    return;
                }
                let operations = self.needs[*callee].clone();
                arguments.extend(self.supply(&operations, scope, expr.span));
                *callee = self.copy_of(*callee, &operations);
            }
            // Call-time binding (decision D1): a function value receives the
            // capabilities its arrow's row names from each caller.
            ExprKind::CallIndirect { callee, arguments }
                if !self.value_operations(callee.ty).is_empty() =>
            {
                let operations = self.value_operations(callee.ty).to_vec();
                arguments.extend(self.supply(&operations, scope, expr.span));
            }
            ExprKind::Call(Target::DynCall { spec }, arguments)
                if !self.dyn_calls[*spec].is_empty() =>
            {
                let operations = self.dyn_calls[*spec].clone();
                arguments.extend(self.supply(&operations, scope, expr.span));
            }
            ExprKind::Call(Target::UnionBorrowCall { spec }, arguments)
                if !self.union_calls[*spec].is_empty() =>
            {
                let operations = self.union_calls[*spec].clone();
                arguments.extend(self.supply(&operations, scope, expr.span));
            }
            ExprKind::FnValue { function, .. }
                if *function < self.originals && !self.value_operations(expr.ty).is_empty() =>
            {
                let operations = self.value_operations(expr.ty).to_vec();
                *function = self.copy_of(*function, &operations);
            }
            ExprKind::Suspend {
                call,
                callee: Some(callee),
                ..
            } => {
                // The call was redirected to the copy. An await of the
                // region's operation is keyed by the copy's capability
                // parameter when the lowering finds it performs through it.
                if let ExprKind::Call(Target::Function(target), _) = &call.kind {
                    *callee = *target;
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Default)]
struct Scope {
    /// Hidden capability parameter slot by operation (copies only).
    hidden: BTreeMap<usize, usize>,
    /// Innermost enclosing `handle` of each operation in this function.
    capabilities: BTreeMap<usize, Capability>,
}

/// Hidden capability parameter slot of each copy, by operation.
pub(super) type Hidden = BTreeMap<usize, BTreeMap<usize, usize>>;

/// Handler arrow of each resumptive declared operation performed by name.
pub(super) type Arrows = BTreeMap<usize, usize>;

/// Add the copies and redirect direct calls and function values to them.
/// Returns the copies' capability slots and the operations' handler arrows.
pub(super) fn add(program: &mut Executable) -> Result<(Hidden, Arrows)> {
    let mut arrows = BTreeMap::new();
    let mut caps = BTreeSet::new();
    for function in &program.functions {
        collect_arrows(&function.body, &mut arrows, &mut caps);
    }
    if caps.is_empty() {
        return Ok((Hidden::new(), arrows));
    }
    let performs = performs_with(program, true);
    let mut needs = (0..program.functions.len())
        .map(|index| {
            let function = &program.functions[index];
            if function.closure.is_some()
                || function.parameter_slots.is_some()
                || program.foreign_functions[index].is_some()
            {
                return vec![];
            }
            performs[index]
                .iter()
                .copied()
                .filter(|operation| caps.contains(operation))
                .collect()
        })
        .collect::<Vec<Vec<usize>>>();
    let values = value_operations(program, &caps);
    // Dispatch calls every member directly, so the members of one key take
    // the union of their operations. A member that performs operations but
    // cannot be copied keeps the whole dispatch on the dynamic stack.
    let members = |functions: &mut dyn Iterator<Item = usize>| -> Vec<usize> {
        let mut operations = BTreeSet::new();
        for function in functions {
            if needs[function].is_empty()
                && performs[function]
                    .iter()
                    .any(|operation| caps.contains(operation))
            {
                return vec![];
            }
            operations.extend(needs[function].iter().copied());
        }
        operations.into_iter().collect()
    };
    let dyn_calls = program
        .dyn_calls
        .iter()
        .map(|spec| {
            members(
                &mut program.dyn_members[spec.object]
                    .iter()
                    .filter_map(|member| member.methods.get(&spec.key).copied()),
            )
        })
        .collect::<Vec<_>>();
    let union_calls = program
        .union_calls
        .iter()
        .map(|spec| members(&mut spec.members.iter().map(|member| member.2)))
        .collect::<Vec<_>>();
    if needs.iter().all(Vec::is_empty) && values.iter().all(Vec::is_empty) {
        return Ok((Hidden::new(), arrows));
    }
    let originals = program.functions.len();
    needs.resize(originals, vec![]);
    let rows = (0..program.function_types.len())
        .map(|id| row_operations(program, &caps, id))
        .collect::<Vec<_>>();
    // A task builtin receives its body at the arrow without capability
    // parameters: a clone made before the arrows change.
    let mut split = BTreeMap::new();
    for function in &program.functions {
        collect_task_bodies(&function.body, &rows, &mut split);
    }
    split.retain(|arrow, _| !values[*arrow].is_empty());
    for (arrow, bare) in split.iter_mut() {
        program
            .function_types
            .push(program.function_types[*arrow].clone());
        *bare = program.function_types.len() - 1;
    }
    // Copies start from the bodies as checked: the originals' calls get the
    // dynamic trampoline where a copy passes its own parameter.
    let sources = program.functions.clone();
    let mut pass = Pass {
        needs: &needs,
        caps: &caps,
        values: &values,
        rows: &rows,
        split: &split,
        dyn_calls: &dyn_calls,
        union_calls: &union_calls,
        originals,
        copies: BTreeMap::new(),
        order: Vec::new(),
    };
    for function in &mut program.functions[..originals] {
        pass.block(&mut function.body, &Scope::default());
    }
    for (spec, operations) in program.dyn_calls.iter().zip(&dyn_calls) {
        if operations.is_empty() {
            continue;
        }
        for member in &mut program.dyn_members[spec.object] {
            if let Some(method) = member.methods.get_mut(&spec.key)
                && *method < originals
            {
                *method = pass.copy_of(*method, operations);
            }
        }
    }
    for (spec, operations) in program.union_calls.iter_mut().zip(&union_calls) {
        if operations.is_empty() {
            continue;
        }
        for member in &mut spec.members {
            member.2 = pass.copy_of(member.2, operations);
        }
    }
    let mut copies = Hidden::new();
    let mut next = 0;
    while next < pass.order.len() {
        let (original, operations, captured) = match pass.order[next].clone() {
            Request::Copy {
                function,
                operations,
                captured,
            } => (function, operations, captured),
        };
        let mut copy = sources[original].clone();
        let mut slots = (0..copy.parameters).collect::<Vec<_>>();
        let mut hidden = BTreeMap::new();
        copy.parameter_grades.resize(copy.parameters, None);
        copy.parameter_lifetimes.resize(copy.parameters, None);
        // Captured capabilities follow the closure's own captures.
        let first = if captured {
            copy.closure.unwrap_or(0)
        } else {
            copy.parameters
        };
        for (offset, &operation) in operations.iter().enumerate() {
            let position = first + offset;
            let slot = copy.locals.len();
            copy.locals.push(Local {
                ty: Type::I64,
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span: copy.span,
            });
            if copy.local_resources.len() == slot {
                copy.local_resources.push(None);
            }
            if !copy.local_borrowed.is_empty() {
                copy.local_borrowed.push(false);
            }
            if !copy.local_copyable.is_empty() {
                copy.local_copyable.push(true);
            }
            copy.parameter_grades.insert(position, None);
            copy.parameter_lifetimes.insert(position, None);
            copy.capability_parameters.push(slot);
            slots.insert(position, slot);
            copy.parameters += 1;
            if captured {
                copy.closure = Some(copy.closure.unwrap_or(0) + 1);
                copy.capture_refs.push(false);
                copy.capture_writes.push(false);
            }
            hidden.insert(operation, slot);
        }
        copy.parameter_slots = Some(slots);
        copies.insert(originals + next, hidden.clone());
        copy.name = format!("{}::capabilities", copy.name);
        pass.block(
            &mut copy.body,
            &Scope {
                hidden,
                ..Scope::default()
            },
        );
        program.functions.push(copy);
        program.foreign_functions.push(None);
        next += 1;
    }
    // The arrows of function values take the capabilities last.
    for (id, operations) in values.iter().enumerate() {
        let arrow = &mut program.function_types[id];
        let written = arrow.parameters.len();
        arrow
            .parameters
            .extend(operations.iter().map(|_| Type::I64));
        if arrow.parameter_grades.len() == written {
            arrow.parameter_grades.resize(arrow.parameters.len(), None);
        }
        if arrow.borrows.parameters.len() == written {
            arrow
                .borrows
                .parameters
                .resize(arrow.parameters.len(), None);
        }
        if arrow.borrows.parameter_leaves.len() == written {
            arrow
                .borrows
                .parameter_leaves
                .resize(arrow.parameters.len(), vec![]);
        }
    }
    Ok((copies, arrows))
}

/// The resumptive declared operations performed by name somewhere that the
/// row of arrow `id` names, in id order.
fn row_operations(program: &Executable, caps: &BTreeSet<usize>, id: usize) -> Vec<usize> {
    let effects = program.function_types[id].effects;
    caps.iter()
        .copied()
        .filter(|&operation| {
            program
                .effect_bits
                .get(operation)
                .is_some_and(|bit| *bit != 0 && effects & bit != 0)
        })
        .collect()
}

/// The resumptive declared operations whose capabilities a value of each
/// arrow type takes after its written parameters (rule 4). An arrow keeps the
/// dynamic stack when a value with its set of operations reaches code that
/// calls it without capabilities: a handler, a task or callback builtin, a
/// foreign function, or a function whose layout cannot take more parameters.
/// Coercions between arrows with different sets go through checked adapters,
/// so arrows with one set agree.
fn value_operations(program: &Executable, caps: &BTreeSet<usize>) -> Vec<Vec<usize>> {
    let operations = |ty: Type| -> Option<Vec<usize>> {
        let (Type::Fn(id) | Type::Once(id) | Type::Multi(id)) = ty else {
            return None;
        };
        let found = row_operations(program, caps, id);
        (!found.is_empty()).then_some(found)
    };
    let mut pinned = BTreeSet::new();
    let mut pin = |ty: Type| {
        if let Some(found) = operations(ty) {
            pinned.insert(found);
        }
    };
    fn walk(expr: &Expr, program: &Executable, pin: &mut dyn FnMut(Type)) {
        match &expr.kind {
            ExprKind::HandlerPush { handler, .. } | ExprKind::AbortScope { handler, .. } => {
                pin(handler.ty)
            }
            ExprKind::Suspend { call, .. } => {
                if let ExprKind::CallIndirect { callee, .. } = &call.kind {
                    pin(callee.ty);
                }
            }
            ExprKind::VecMap { callbacks, .. } => {
                for callback in callbacks {
                    pin(callback.ty);
                }
            }
            // A task body takes its capabilities as captures, which needs a
            // closure with an ordinary layout (the checker requires a
            // written lambda).
            ExprKind::TaskScope { body, .. } | ExprKind::TaskSpawn { body, .. }
                if !matches!(&body.kind, ExprKind::FnValue { function, .. }
                    if program.functions[*function].closure.is_some()
                        && program.functions[*function].parameter_slots.is_none()) =>
            {
                pin(body.ty)
            }
            ExprKind::Call(Target::Function(callee), arguments)
                if program.foreign_functions[*callee].is_some() =>
            {
                for argument in arguments {
                    pin(argument.ty);
                }
            }
            ExprKind::Call(
                Target::Function(_) | Target::DynCall { .. } | Target::UnionBorrowCall { .. },
                _,
            ) => {}
            ExprKind::Call(_, arguments) => {
                for argument in arguments {
                    pin(argument.ty);
                }
            }
            ExprKind::FnValue { function, .. } => {
                let source = &program.functions[*function];
                if source.parameter_slots.is_some()
                    || program.foreign_functions[*function].is_some()
                {
                    pin(expr.ty);
                }
            }
            _ => {}
        }
        expr.for_each_child(&mut |child| walk(child, program, pin));
    }
    for function in &program.functions {
        for statement in &function.body.statements {
            if let Statement::Let(_, value) | Statement::Expr(value) = statement {
                walk(value, program, &mut pin);
            }
        }
        if let Some(tail) = &function.body.tail {
            walk(tail, program, &mut pin);
        }
    }
    (0..program.function_types.len())
        .map(|id| {
            operations(Type::Fn(id))
                .filter(|found| !pinned.contains(found))
                .unwrap_or_default()
        })
        .collect()
}

/// Arrows of task bodies whose rows name operations with capabilities.
fn collect_task_bodies(block: &Block, rows: &[Vec<usize>], split: &mut BTreeMap<usize, usize>) {
    fn walk(expr: &Expr, rows: &[Vec<usize>], split: &mut BTreeMap<usize, usize>) {
        if let ExprKind::TaskScope { body, .. } | ExprKind::TaskSpawn { body, .. } = &expr.kind
            && let Type::Once(arrow) = body.ty
            && !rows[arrow].is_empty()
        {
            split.insert(arrow, 0);
        }
        expr.for_each_child(&mut |child| walk(child, rows, split));
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, rows, split);
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, rows, split);
    }
}

/// The handler arrow of each resumptive operation performed by name, and
/// the capability type of every operation performed by name.
fn collect_arrows(block: &Block, arrows: &mut BTreeMap<usize, usize>, caps: &mut BTreeSet<usize>) {
    fn walk(expr: &Expr, arrows: &mut BTreeMap<usize, usize>, caps: &mut BTreeSet<usize>) {
        match &expr.kind {
            ExprKind::DynamicPerform {
                operation, handler, ..
            } => {
                arrows.entry(*operation).or_insert(*handler);
                caps.insert(*operation);
            }
            ExprKind::AbortPerform { operation, .. } => {
                caps.insert(*operation);
            }
            _ => {}
        }
        expr.for_each_child(&mut |child| walk(child, arrows, caps));
    }
    for statement in &block.statements {
        if let Statement::Let(_, value) | Statement::Expr(value) = statement {
            walk(value, arrows, caps);
        }
    }
    if let Some(tail) = &block.tail {
        walk(tail, arrows, caps);
    }
}
