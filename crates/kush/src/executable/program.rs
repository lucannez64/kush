//! Queries and passes over a checked program (reports, redundant drops).
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Executable {
    /// `(proved, checked)`: element accesses proved in bounds, compiled as
    /// plain loads and stores, and those that keep a run-time check.
    pub fn bounds_report(&self) -> (usize, usize) {
        (self.bounds_proved, self.bounds_checked)
    }
    /// PROOF-FUZZ: every run-time check the prover could not discharge, in
    /// source order.
    pub fn obligations(&self) -> &[Obligation] {
        &self.obligations
    }
    /// PROOF-FUZZ: checks the prover discharged (bounds and overflow), one
    /// per function instance, in source order.
    pub fn discharged(&self) -> &[Obligation] {
        &self.discharged
    }
    /// PROOF-FUZZ: obligation sites, one per source location and kind (the
    /// instances of a generic function share a site), in source order. A
    /// site's position in this list is its id in fuzz builds.
    pub fn obligation_sites(&self) -> Vec<&Obligation> {
        let mut seen = BTreeSet::new();
        self.obligations
            .iter()
            .filter(|o| seen.insert((o.span.start, o.span.end, o.kind.label())))
            .collect()
    }
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }
    /// Erased proof obligations discharged at compile time, each with a
    /// certificate that was re-checked independently of the search.
    pub fn certificates(&self) -> &[crate::facts::Certificate] {
        &self.certificates
    }
    /// Total logical definitions that were kernel-checked and erased.
    pub fn logical_definitions(&self) -> &[String] {
        &self.logical_definitions
    }
    /// Checked nested in-place map fusions. Diagnostics-only observation.
    pub fn fusion_count(&self) -> usize {
        self.fusions
    }
    /// The source spelling of a checked type.
    pub(crate) fn type_name(&self, ty: Type) -> String {
        crate::runtime_types::type_name_in(
            ty,
            &self.pointees,
            &self.enums,
            &self.unions,
            &self.function_types,
        )
    }
    /// `export "symbol" fn` declarations (KUSH-RUST-EXPORT).
    pub fn exports(&self) -> Vec<ExportInfo> {
        let name = |ty: Type| {
            crate::runtime_types::type_name_in(
                ty,
                &self.pointees,
                &self.enums,
                &self.unions,
                &self.function_types,
            )
        };
        self.exports
            .iter()
            .map(|export| ExportInfo {
                symbol: export.symbol.clone(),
                name: self.functions[export.index].name.clone(),
                parameters: export
                    .parameters
                    .iter()
                    .map(|(n, ty)| (n.clone(), name(*ty)))
                    .collect(),
                result: name(export.result),
            })
            .collect()
    }
    /// Checked foreign declarations in instance order. This reports the
    /// Kush-side contract only; the foreign library remains trusted code that
    /// Kush cannot verify for memory safety.
    pub fn foreign_functions(&self) -> Vec<ForeignFunctionInfo> {
        self.foreign_functions
            .iter()
            .enumerate()
            .filter_map(|(index, foreign)| {
                foreign.as_ref().map(|foreign| ForeignFunctionInfo {
                    name: self.functions[index].name.clone(),
                    symbol: foreign.symbol.clone(),
                    parameters: foreign
                        .parameters
                        .iter()
                        .map(|ty| {
                            crate::runtime_types::type_name_in(
                                *ty,
                                &self.pointees,
                                &self.enums,
                                &self.unions,
                                &self.function_types,
                            )
                        })
                        .collect(),
                    result: crate::runtime_types::type_name_in(
                        foreign.result,
                        &self.pointees,
                        &self.enums,
                        &self.unions,
                        &self.function_types,
                    ),
                    fallible: foreign.fallible.is_some(),
                })
            })
            .collect()
    }
    pub(crate) fn entry(&self) -> Result<usize> {
        self.entry.ok_or_else(|| {
            Diagnostic::new(
                Span::default(),
                "a runnable executable needs fn main() -> Unit or i64",
            )
        })
    }
    pub(crate) fn width(&self, ty: Type) -> usize {
        crate::runtime_types::width(
            &self.pointees,
            &self.enums,
            &self.unions,
            &self.function_types,
            ty,
        )
    }
    pub(crate) fn owns(&self, ty: Type) -> bool {
        match ty {
            Type::Box(_)
            | Type::Arena
            | Type::ArenaBox(_)
            | Type::AllocatorContext
            | Type::AllocBox(_)
            | Type::AllocVec(_)
            | Type::Bytes
            | Type::String
            | Type::Vec(_)
            | Type::Once(_)
            | Type::Task(_)
            | Type::Thread(_)
            | Type::Channel(_)
            | Type::GpuBuf(_)
            | Type::DynObj(_) => true,
            Type::Enum(id) | Type::Variants(id, _) => self.owned_enums[id],
            Type::Union(id) => self.unions[id]
                .members
                .iter()
                .any(|member| self.owns(*member)),
            _ => false,
        }
    }
}

impl Executable {
    /// Every explicit `drop(x)` this pass can remove without changing what the
    /// program observes. See the section comment for the exact conditions.
    pub fn redundant_drops(&self) -> Vec<RedundantDrop> {
        let mut out = Vec::new();
        for (index, function) in self.functions.iter().enumerate() {
            if self
                .foreign_functions
                .get(index)
                .is_some_and(Option::is_some)
            {
                continue;
            }
            let mut state = LintScopes::default();
            state.scopes.push(std::collections::BTreeSet::new());
            state.readiness.push(true);
            // Parameters belong to the function body's scope.
            state.scopes[0].extend(0..function.parameters);
            for statement in &function.body.statements {
                if let Statement::Let(id, _) = statement {
                    state.scopes[0].insert(*id);
                }
            }
            self.walk_lint_block(function, &function.body, true, &mut state, &mut out);
        }
        out
    }

    /// `ready` is true when the work after this block inside every enclosing
    /// block, up to the declaring block of any owner, is inert (or ends in a
    /// return); it says nothing about the block's own contents.
    pub(super) fn walk_lint_block(
        &self,
        function: &Function,
        block: &Block,
        ready: bool,
        state: &mut LintScopes,
        out: &mut Vec<RedundantDrop>,
    ) {
        let mut declared = std::collections::BTreeSet::new();
        for statement in &block.statements {
            if let Statement::Let(id, _) = statement {
                declared.insert(*id);
            }
        }
        state.scopes.push(declared);
        state.readiness.push(ready);
        let mut rest = match block.tail.as_deref() {
            None => LintRest::Inert,
            Some(tail) => match &tail.kind {
                ExprKind::Return(value) => {
                    if self.inert_lint_expr(function, value) {
                        LintRest::Return
                    } else {
                        LintRest::Blocked
                    }
                }
                _ => {
                    if self.inert_lint_expr(function, tail) {
                        LintRest::Inert
                    } else {
                        LintRest::Blocked
                    }
                }
            },
        };
        for statement in block.statements.iter().rev() {
            // Whatever follows this position inside the block must be inert to
            // hand the cleanup point to a nested construct.
            let position_ready = matches!(rest, LintRest::Inert | LintRest::Return);
            if let Statement::Expr(expr) = statement {
                if let ExprKind::Drop(inner) = &expr.kind
                    && let Some(kind) = self.lint_drop_kind(function, inner, rest, state)
                {
                    out.push(RedundantDrop {
                        span: expr.span,
                        kind,
                    });
                }
                self.walk_lint_statement_expr(function, expr, position_ready, state, out);
            } else if let Statement::Let(_, expr) = statement {
                self.walk_lint_statement_expr(function, expr, position_ready, state, out);
            }
            // This statement now precedes the rest.
            if rest != LintRest::Return {
                rest = match &statement {
                    Statement::Expr(expr) => match &expr.kind {
                        ExprKind::Return(value) => {
                            if self.inert_lint_expr(function, value) {
                                LintRest::Return
                            } else {
                                LintRest::Blocked
                            }
                        }
                        ExprKind::Break(..) | ExprKind::Continue(..) => LintRest::Blocked,
                        _ if self.inert_lint_statement_with_drop(function, statement) => rest,
                        _ => LintRest::Blocked,
                    },
                    _ if self.inert_lint_statement_with_drop(function, statement) => rest,
                    _ => LintRest::Blocked,
                };
            }
        }
        if let Some(tail) = &block.tail {
            // Nothing runs after the tail inside this block, so a nested
            // construct in it sits at the block's cleanup point.
            self.walk_lint_value_expr(function, tail, true, state, out);
        }
        state.scopes.pop();
        state.readiness.pop();
    }

    /// Descend into a statement expression. `ready` describes the position of
    /// any nested block within this block.
    pub(super) fn walk_lint_statement_expr(
        &self,
        function: &Function,
        expr: &Expr,
        ready: bool,
        state: &mut LintScopes,
        out: &mut Vec<RedundantDrop>,
    ) {
        match &expr.kind {
            ExprKind::Block(block) => self.walk_lint_block(function, block, ready, state, out),
            ExprKind::Match(scrutinee, arms) => {
                self.walk_lint_value_expr(function, scrutinee, false, state, out);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.walk_lint_value_expr(function, guard, false, state, out);
                    }
                    self.walk_lint_value_expr(function, &arm.body, ready, state, out);
                }
            }
            ExprKind::If(condition, then, otherwise) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, then, ready, state, out);
                self.walk_lint_block(function, otherwise, ready, state, out);
            }
            // A loop body may run again; only a return inside it ends the
            // enclosing work.
            ExprKind::While(condition, body) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Loop(body) => {
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Return(value) => {
                let ready = self.inert_lint_expr(function, value);
                self.walk_lint_value_expr(function, value, ready, state, out);
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::AbortScope { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            _ => self.walk_lint_value_expr(function, expr, false, state, out),
        }
    }

    /// Descend into a value expression; a block that is not the whole value
    /// has other evaluation around it.
    pub(super) fn walk_lint_value_expr(
        &self,
        function: &Function,
        expr: &Expr,
        ready: bool,
        state: &mut LintScopes,
        out: &mut Vec<RedundantDrop>,
    ) {
        match &expr.kind {
            ExprKind::Block(block) => self.walk_lint_block(function, block, ready, state, out),
            ExprKind::Match(scrutinee, arms) => {
                self.walk_lint_value_expr(function, scrutinee, false, state, out);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.walk_lint_value_expr(function, guard, false, state, out);
                    }
                    self.walk_lint_value_expr(function, &arm.body, ready, state, out);
                }
            }
            ExprKind::If(condition, then, otherwise) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, then, ready, state, out);
                self.walk_lint_block(function, otherwise, ready, state, out);
            }
            ExprKind::While(condition, body) => {
                self.walk_lint_value_expr(function, condition, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Loop(body) => {
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::Return(value) => {
                let ready = self.inert_lint_expr(function, value);
                self.walk_lint_value_expr(function, value, ready, state, out);
            }
            ExprKind::HandlerPush { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            ExprKind::AbortScope { handler, body, .. } => {
                self.walk_lint_value_expr(function, handler, false, state, out);
                self.walk_lint_block(function, body, false, state, out);
            }
            _ => expr.for_each_child(&mut |child| {
                self.walk_lint_value_expr(function, child, false, state, out)
            }),
        }
    }

    pub(super) fn lint_drop_kind(
        &self,
        function: &Function,
        inner: &Expr,
        rest: LintRest,
        state: &LintScopes,
    ) -> Option<RedundantDropKind> {
        let id = match &inner.kind {
            ExprKind::Local(id) | ExprKind::Move(id) => *id,
            // Dropping an arbitrary expression: its evaluation is an effect.
            _ => return None,
        };
        let local = function.locals.get(id)?;
        if local.linear || local.grade.is_some_and(|grade| !grade.is_zero()) {
            return None;
        }
        if self.drop_has_release_hook(local.ty) {
            return None;
        }
        if !self.lint_owned_type(local.ty) {
            return Some(RedundantDropKind::Copyable);
        }
        // The deepest block that declares this binding.
        let declaring = state.scopes.iter().rposition(|scope| scope.contains(&id))?;
        let current = state.scopes.len() - 1;
        let at_cleanup_point = match rest {
            // A return unwinds every scope, so nothing after it runs.
            LintRest::Return => true,
            // The rest of this block is inert. Then every position between
            // this block and its declaring block must also be at the end of
            // its own block's work; the declaring block's own continuation is
            // irrelevant because cleanup happens there.
            LintRest::Inert => state.readiness[declaring + 1..=current]
                .iter()
                .all(|ready| *ready),
            LintRest::Blocked => false,
        };
        at_cleanup_point.then_some(RedundantDropKind::AtCleanupPoint)
    }

    pub(super) fn inert_lint_statement_with_drop(
        &self,
        function: &Function,
        statement: &Statement,
    ) -> bool {
        match statement {
            Statement::Let(_, expr) => self.inert_lint_expr(function, expr),
            Statement::Expr(expr) => {
                if let ExprKind::Drop(inner) = &expr.kind
                    && let ExprKind::Local(id) | ExprKind::Move(id) = &inner.kind
                    && let Some(local) = function.locals.get(*id)
                {
                    // Dropping a hook-free local only frees storage; nothing
                    // else observes it.
                    return !self.drop_has_release_hook(local.ty);
                }
                self.inert_lint_expr(function, expr)
            }
            Statement::Declare(_) => true,
        }
    }

    /// Whether evaluating this expression could allocate, run user code, or
    /// otherwise observe that an owner was freed earlier. Conservative by
    /// construction: only scalars, copies, moves, and pure value construction
    /// pass.
    pub(super) fn inert_lint_expr(&self, function: &Function, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Constant(_) | ExprKind::Erased(_) | ExprKind::Move(_) => true,
            // `Local` reads a copyable value.
            ExprKind::Local(_) => self.lint_copyable_type(expr.ty),
            ExprKind::Construct { fields, .. } => fields
                .iter()
                .all(|field| self.inert_lint_expr(function, field)),
            ExprKind::Coerce { value, .. } => self.inert_lint_expr(function, value),
            ExprKind::Unary(_, value) => self.inert_lint_expr(function, value),
            ExprKind::Binary(_, left, right) => {
                self.inert_lint_expr(function, left) && self.inert_lint_expr(function, right)
            }
            // Overwriting a copyable local destroys nothing; an owning local
            // would run its old value's cleanup here.
            ExprKind::Assign(id, value) => {
                function.locals.get(*id).is_some_and(|local| {
                    !self.lint_owned_type(local.ty) && !self.drop_has_release_hook(local.ty)
                }) && self.inert_lint_expr(function, value)
            }
            _ => false,
        }
    }

    /// Types whose destruction can run user or generated code: an explicit
    /// drop can order those callbacks relative to other drops, so they are not
    /// reported as redundant.
    pub(super) fn drop_has_release_hook(&self, ty: Type) -> bool {
        fn go(executable: &Executable, ty: Type, depth: usize, seen: &mut Vec<Type>) -> bool {
            if depth > 64 || seen.contains(&ty) {
                return false;
            }
            seen.push(ty);
            match ty {
                Type::AllocBox(_)
                | Type::AllocVec(_)
                | Type::AllocatorContext
                | Type::Arena
                | Type::Once(_)
                | Type::Task(_)
                | Type::Thread(_)
                | Type::DynObj(_) => true,
                Type::Box(pointee) | Type::Vec(pointee) => {
                    go(executable, executable.pointees[pointee], depth + 1, seen)
                }
                Type::Enum(id) | Type::Variants(id, _) => {
                    executable.enums[id].variants.iter().any(|variant| {
                        variant
                            .fields
                            .iter()
                            .any(|field| go(executable, *field, depth + 1, seen))
                    })
                }
                Type::Union(id) => executable.unions[id]
                    .members
                    .iter()
                    .any(|member| go(executable, *member, depth + 1, seen)),
                _ => false,
            }
        }
        go(self, ty, 0, &mut Vec::new())
    }

    /// Copyable means no owned storage anywhere, mirroring the ownership pass.
    pub(super) fn lint_copyable_type(&self, ty: Type) -> bool {
        !self.lint_owned_type(ty)
    }

    pub(super) fn lint_owned_type(&self, ty: Type) -> bool {
        fn go(executable: &Executable, ty: Type, depth: usize, seen: &mut Vec<Type>) -> bool {
            if depth > 64 || seen.contains(&ty) {
                return false;
            }
            seen.push(ty);
            match ty {
                Type::Box(_)
                | Type::Arena
                | Type::ArenaBox(_)
                | Type::AllocBox(_)
                | Type::AllocVec(_)
                | Type::AllocatorContext
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::Once(_)
                | Type::Task(_)
                | Type::Thread(_)
                | Type::DynObj(_) => true,
                Type::Enum(id) | Type::Variants(id, _) => {
                    executable.enums[id].linear
                        || executable.enums[id].variants.iter().any(|variant| {
                            variant
                                .fields
                                .iter()
                                .any(|field| go(executable, *field, depth + 1, seen))
                        })
                }
                Type::Union(id) => executable.unions[id]
                    .members
                    .iter()
                    .any(|member| go(executable, *member, depth + 1, seen)),
                _ => false,
            }
        }
        go(self, ty, 0, &mut Vec::new())
    }
}
