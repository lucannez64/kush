//! Parameters, erased evidence and the kernel facts that track scalar values.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Least upper bound for branch results: a normalized algebraic union.
    pub(super) fn join(&mut self, left: Type, right: Type, span: Span) -> Result<Type> {
        if left == Type::Never {
            return Ok(right);
        }
        if right == Type::Never {
            return Ok(left);
        }
        self.types.union(vec![left, right], span)
    }
    pub(super) fn local_name(&self, slot: usize) -> String {
        self.slots.iter().find(|(_, s)| **s == slot).map_or_else(
            || format!("_{slot}"),
            |(id, _)| self.resolution.bindings[*id].name.clone(),
        )
    }
    /// An erased proof parameter. Arithmetic `{ ... }` parameters become
    /// difference-constraint facts; other parameters elaborate to an open
    /// logical type relative to earlier erased kernel binders and are checked
    /// by the trusted kernel.
    pub(super) fn assume_parameter(&mut self, parameter: &ast::Parameter) -> Result<()> {
        let id = self.resolution.binder(parameter.span).unwrap();
        if !matches!(parameter.ty.kind, ast::TypeKind::Predicate(_)) {
            let bindings = self.kernel_bindings();
            let ty = crate::check::elaborate_type(
                self.resolution,
                self.logical,
                &bindings,
                &parameter.ty,
            )
            .map_err(|e| {
                Diagnostic::new(
                    e.span,
                    format!(
                        "erased parameters must be arithmetic '{{ ... }}' propositions or logical types with checked dependencies: {}",
                        e.message
                    ),
                )
            })?;
            let context = self.kernel_context();
            self.logical.kernel.sort_open(&ty, &context).map_err(|e| {
                Diagnostic::new(
                    parameter.ty.span,
                    format!("invalid erased logical parameter: {e}"),
                )
            })?;
            // A hypothesis type is interpreted in the prefix of binders before
            // its own position, so appending a later binder does not change its
            // de Bruijn indices. The elaborated type is stored as-is.
            self.kernel_proofs.insert(id, ty.clone());
            self.kernel_types.insert(id, ty);
            self.kernel_locals.push(id);
            return Ok(());
        }
        let proposition = self.functions.proposition(self.resolution, parameter)?;
        let params = self.parameter_slots();
        for index in &proposition.booleans {
            if self.locals[params[*index]].ty != Type::Bool {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "a bare name in a proposition must be a Bool parameter; compare integers explicitly",
                ));
            }
        }
        for slot in &params {
            self.facts.note_type(*slot, self.locals[*slot].ty);
        }
        let term = |linear: &crate::facts::ParamLinear| -> Option<crate::facts::Linear> {
            use crate::facts::{Linear, ParamTerm, Term};
            let mut expression = Linear::constant(linear.constant);
            for (base, coefficient) in &linear.coefficients {
                let part = match base {
                    ParamTerm::Zero => Linear::constant(1),
                    ParamTerm::Param(i) => Linear::variable(Term::Var(params[*i], 0)),
                    ParamTerm::Len(i) => Linear::variable(Term::Len(params[*i], 0)),
                };
                expression = expression.add_scaled(&part, *coefficient)?;
            }
            Some(expression)
        };
        // The precondition as a hypothesis. An untranslatable atom is
        // dropped from its conjunction, which only weakens it.
        let mut hypothesis: crate::facts::Dnf = Vec::new();
        for disjunct in &proposition.disjuncts {
            let mut part: crate::facts::Dnf = vec![Vec::new()];
            for (l, op, r) in disjunct {
                let atom = match (term(l), term(r)) {
                    (Some(left), Some(right)) => crate::facts::compare_dnf(left, op, right),
                    _ => None,
                };
                if let Some(atom) = atom {
                    match crate::facts::dnf_and(&part, &atom) {
                        Some(next) => part = next,
                        None => continue,
                    }
                }
            }
            hypothesis.extend(part);
        }
        if hypothesis.len() <= 32 {
            self.facts.add_formula(hypothesis);
        }
        self.proofs.insert(id, proposition);
        Ok(())
    }
    /// Slots of runtime parameters, in order (they are the first locals).
    pub(super) fn parameter_slots(&self) -> Vec<usize> {
        (0..self.locals.len()).collect()
    }
    /// Prove a callee's erased precondition for the given runtime arguments.
    pub(super) fn discharge(
        &mut self,
        proposition: &crate::facts::Proposition,
        arguments: &[Expr],
        evidence: &ast::Expr,
        span: Span,
    ) -> Result<()> {
        use crate::facts::{Linear, ParamLinear, ParamTerm, Term};
        match &evidence.kind {
            ast::ExprKind::Name(name) if name == "_" => {}
            ast::ExprKind::Name(_)
                if self
                    .resolution
                    .reference(evidence.span)
                    .is_some_and(|id| self.proofs.contains_key(&id)) => {}
            _ => {
                return Err(Diagnostic::new(
                    evidence.span,
                    "an erased argument must be '_' (prove from context) or the name of an erased proof parameter",
                ));
            }
        }
        for index in &proposition.booleans {
            if arguments[*index].ty != Type::Bool {
                return Err(Diagnostic::new(
                    arguments[*index].span,
                    "a bare name in a proposition must be a Bool parameter; compare integers explicitly",
                ));
            }
        }
        let overflow = || {
            Diagnostic::new(
                span,
                "proof obligation coefficients overflow the bounded linear solver",
            )
        };
        let mut goal: crate::facts::Dnf = Vec::new();
        for disjunct in &proposition.disjuncts {
            let mut part: crate::facts::Dnf = vec![Vec::new()];
            for (l, op, r) in disjunct {
                let term = |linear: &ParamLinear| -> Result<Linear> {
                    let mut expression = Linear::constant(linear.constant);
                    for (base, coefficient) in &linear.coefficients {
                        let part = match base {
                        ParamTerm::Zero => Linear::constant(1),
                        ParamTerm::Param(i) => {
                            self.facts.linear(&arguments[*i]).ok_or_else(|| {
                                Diagnostic::new(
                                    arguments[*i].span,
                                    "this argument appears in a proof obligation; use a linear expression such as a local, a constant, 'local + constant', or 'constant * local'",
                                )
                            })?
                        }
                        ParamTerm::Len(i) => {
                            let slot =
                                crate::facts::owner_slot(&arguments[*i]).ok_or_else(|| {
                                    Diagnostic::new(
                                        arguments[*i].span,
                                        "pass a named buffer here so its length can appear in a proof obligation",
                                    )
                                })?;
                            Linear::variable(Term::Len(slot, self.facts.version(slot)))
                        }
                    };
                        expression = expression.add_scaled(&part, *coefficient).ok_or_else(|| {
                        Diagnostic::new(
                            span,
                            "proof obligation coefficients overflow the bounded linear solver",
                        )
                    })?;
                    }
                    Ok(expression)
                };
                let atom =
                    crate::facts::compare_dnf(term(l)?, op, term(r)?).ok_or_else(overflow)?;
                part = crate::facts::dnf_and(&part, &atom).ok_or_else(overflow)?;
            }
            goal = crate::facts::dnf_or(goal, part).ok_or_else(overflow)?;
        }
        let Some(certificates) = self.facts.certify(&goal, span, &proposition.text) else {
            let known = self.facts.snapshot_formula(&goal);
            let names = (0..self.locals.len())
                .map(|s| self.local_name(s))
                .collect::<Vec<_>>();
            return Err(crate::facts::failure(
                span,
                &proposition.text,
                &known,
                &|slot| names[slot].clone(),
            ));
        };
        self.functions.certificates.extend(certificates);
        Ok(())
    }
    /// All kernel binders in scope order, each paired with its hypothesis type.
    pub(super) fn kernel_bindings(&self) -> Vec<(BindingId, Term)> {
        self.kernel_locals
            .iter()
            .map(|id| (*id, self.kernel_types[id].clone()))
            .collect()
    }
    pub(super) fn kernel_context(&self) -> Vec<Term> {
        self.kernel_locals
            .iter()
            .map(|id| self.kernel_types[id].clone())
            .collect()
    }
    /// Alias bindings in the form the evidence elaborator uses: an alias name
    /// resolves to the binder that was copied at its binding site.
    pub(super) fn kernel_alias_sources(&self) -> BTreeMap<BindingId, usize> {
        self.kernel_aliases
            .iter()
            .filter(|(_, position)| **position < self.kernel_locals.len())
            .map(|(alias, position)| (*alias, *position))
            .collect()
    }
    /// Canonical literal values of scalar locals at the current program point.
    /// These make `refl::<i64>(n)` elaborate to the same literal the checker
    /// substituted for a symbolic argument after a branch/loop join.
    pub(super) fn kernel_literals(&self) -> BTreeMap<BindingId, Term> {
        self.scalar_values
            .iter()
            .filter_map(|(id, value)| match value {
                ScalarValue::Literal(term) => Some((*id, term.clone())),
                ScalarValue::Position(_) | ScalarValue::Unknown => None,
            })
            .collect()
    }
    /// Admit a runtime scalar binding as a symbolic kernel index. Mutable
    /// bindings are admitted at their current version; [`Self::renew_scalar_index`]
    /// appends a fresh binder on assignment. The mutable local itself is never
    /// a stable proof object: proofs are erased, cannot be bound to runtime
    /// locals, and each use translates the *current* version at its call site.
    pub(super) fn admit_scalar_index(
        &mut self,
        id: BindingId,
        ty: Type,
        _span: Span,
    ) -> Result<()> {
        if let Some(carrier) = ty.scalar_carrier() {
            let position = self.kernel_locals.len();
            self.kernel_types.insert(id, Term::Scalar(carrier));
            self.kernel_locals.push(id);
            self.scalar_epochs.insert(id, 0);
            self.scalar_values
                .insert(id, ScalarValue::Position(position));
        }
        Ok(())
    }

    /// The machine literal a checked initializer denotes, if it is canonical.
    pub(super) fn scalar_literal(&self, ty: Type, value: &Expr) -> Option<ScalarValue> {
        let carrier = ty.scalar_carrier()?;
        let term = match (&value.kind, carrier) {
            (ExprKind::Constant(raw), Scalar::I64) => Term::i64(*raw),
            (ExprKind::Constant(raw), Scalar::Bool) => Term::boolean(*raw != 0),
            (ExprKind::Constant(_), Scalar::Unit) => Term::unit(),
            (ExprKind::Local(slot), _) => {
                let id = self
                    .slots
                    .iter()
                    .find_map(|(id, candidate)| (*candidate == *slot).then_some(*id))?;
                match self.scalar_values.get(&id) {
                    Some(ScalarValue::Literal(term)) => term.clone(),
                    _ => return None,
                }
            }
            _ => return None,
        };
        Some(ScalarValue::Literal(term))
    }

    /// Record that a mutable scalar local was assigned. Every stored kernel
    /// proof type is shifted to keep its old outer hypotheses at the same
    /// binding, then a fresh binder for the new value is appended. The de
    /// Bruijn shift is essential: growing the context at the nearest end must
    /// not reinterpret an earlier `Eq<i64, n, n>` as a different variable.
    pub(super) fn renew_scalar_index(&mut self, slot: usize, value: &Expr) -> Result<()> {
        let ty = self.locals[slot].ty;
        let Some(carrier) = ty.scalar_carrier() else {
            return Ok(());
        };
        let Some(id) = self
            .slots
            .iter()
            .find_map(|(id, candidate)| (*candidate == slot).then_some(*id))
        else {
            return Ok(());
        };
        let _ = self.locals[slot].span;
        self.kernel_aliases.remove(&id);
        self.kernel_types.insert(id, Term::Scalar(carrier));
        self.kernel_locals.push(id);
        let position = self.kernel_locals.len() - 1;
        let state = self
            .scalar_literal(ty, value)
            .unwrap_or(ScalarValue::Position(position));
        self.scalar_values.insert(id, state);
        *self.scalar_epochs.entry(id).or_insert(0) += 1;
        Ok(())
    }
    /// Leave a nested scope by truncating the kernel telescope to `mark`. A
    /// scalar whose current index pointed at a truncated binder would
    /// otherwise dangle and alias whatever binder is appended next, so it gets
    /// a fresh opaque binder at the outer level (its value is unknown here).
    pub(super) fn truncate_kernel(&mut self, mark: usize) {
        self.kernel_locals.truncate(mark);
        self.kernel_aliases.retain(|_, position| *position < mark);
        let stale = self
            .scalar_values
            .iter()
            .filter(|(_, state)| matches!(state, ScalarValue::Position(p) if *p >= mark))
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        for id in stale {
            let ty = self
                .slots
                .get(&id)
                .and_then(|slot| self.locals.get(*slot))
                .map(|local| local.ty);
            match ty {
                Some(ty) if ty.scalar_carrier().is_some() => self.fresh_scalar_value(id, ty),
                _ => {
                    self.scalar_values.remove(&id);
                }
            }
        }
    }
    /// Append a fresh unconstrained binder for a scalar whose value changed on
    /// only some path or across a loop iteration. The old binder stays in the
    /// proof prefix; later uses denote the new opaque value.
    pub(super) fn fresh_scalar_value(&mut self, id: BindingId, ty: Type) {
        let Some(carrier) = ty.scalar_carrier() else {
            return;
        };
        self.kernel_types.insert(id, Term::Scalar(carrier));
        self.kernel_locals.push(id);
        let position = self.kernel_locals.len() - 1;
        self.scalar_values
            .insert(id, ScalarValue::Position(position));
        *self.scalar_epochs.entry(id).or_insert(0) += 1;
    }
    /// The current absolute position of a symbolic scalar binder. An alias
    /// resolves to the position that was copied at its binding site.
    pub(super) fn kernel_position(&self, id: BindingId) -> Option<usize> {
        if let Some(state) = self.scalar_values.get(&id) {
            return match state {
                ScalarValue::Position(position) => Some(*position),
                ScalarValue::Literal(_) | ScalarValue::Unknown => None,
            };
        }
        if let Some(position) = self.kernel_aliases.get(&id) {
            return Some(*position);
        }
        self.kernel_locals.iter().rposition(|local| *local == id)
    }
    /// Record that `id` is a by-value scalar copy of the current version of
    /// `source`. The alias keeps the source's evaluation-point binder instead
    /// of introducing a fresh unconstrained index.
    pub(super) fn alias_scalar_index(&mut self, id: BindingId, source: BindingId) -> bool {
        if let Some(state) = self.scalar_values.get(&source).cloned() {
            match state {
                ScalarValue::Position(position) => {
                    self.scalar_aliases_position(id, position);
                    return true;
                }
                ScalarValue::Literal(term) => {
                    self.scalar_values.insert(id, ScalarValue::Literal(term));
                    return true;
                }
                ScalarValue::Unknown => return false,
            }
        }
        let Some(position) = self.kernel_position(source) else {
            return false;
        };
        self.scalar_aliases_position(id, position);
        true
    }
    pub(super) fn scalar_aliases_position(&mut self, id: BindingId, position: usize) {
        self.kernel_aliases.insert(id, position);
        self.scalar_values
            .insert(id, ScalarValue::Position(position));
    }
    /// The de Bruijn term for an in-scope symbolic runtime scalar local. The
    /// innermost binder wins, matching lexical shadowing and captures.
    pub(super) fn kernel_local_term(&self, id: BindingId) -> Option<Term> {
        if let Some(state) = self.scalar_values.get(&id) {
            match state {
                ScalarValue::Literal(term) => return Some(term.clone()),
                ScalarValue::Position(position) => {
                    let index = self.kernel_locals.len().checked_sub(1 + position)?;
                    return Some(Term::Var(index));
                }
                ScalarValue::Unknown => return None,
            }
        }
        let position = self.kernel_position(id)?;
        let index = self.kernel_locals.len().checked_sub(1 + position)?;
        Some(Term::Var(index))
    }
    /// Join the scalar index states of two branches. Equal stable values are
    /// preserved, so a proof about a literal established by both branches
    /// survives; any disagreement appends a fresh opaque binder. The joined
    /// telescope has length `live` (the branch-local binders were truncated).
    pub(super) fn join_scalars(
        &mut self,
        baseline: &BTreeMap<BindingId, ScalarValue>,
        left: &BTreeMap<BindingId, ScalarValue>,
        right: &BTreeMap<BindingId, ScalarValue>,
        live: usize,
        left_diverges: bool,
        right_diverges: bool,
    ) {
        self.join_scalar_arms(
            baseline,
            &[(left, left_diverges), (right, right_diverges)],
            live,
        );
    }
    /// N-way scalar join over `match` arms (and the two `if` branches). Only
    /// arms that reach the join point count; if every arm diverges, all of
    /// them are used. A literal survives only when every reaching arm agrees.
    pub(super) fn join_scalar_arms(
        &mut self,
        baseline: &BTreeMap<BindingId, ScalarValue>,
        arms: &[(&BTreeMap<BindingId, ScalarValue>, bool)],
        live: usize,
    ) {
        let reaching = arms
            .iter()
            .filter(|(_, diverges)| !diverges)
            .map(|(map, _)| *map)
            .collect::<Vec<_>>();
        let reaching = if reaching.is_empty() {
            arms.iter().map(|(map, _)| *map).collect()
        } else {
            reaching
        };
        for (id, base) in baseline {
            let slot = self
                .slots
                .iter()
                .find_map(|(candidate, slot)| (candidate == id).then_some(*slot));
            let Some(slot) = slot else {
                continue;
            };
            let ty = self.locals[slot].ty;
            if ty.scalar_carrier().is_none() {
                continue;
            }
            let states = reaching
                .iter()
                .map(|map| Self::map_scalar_state(map, *id, live))
                .collect::<Vec<_>>();
            let joined = if states.iter().all(Option::is_none) {
                base.clone()
            } else {
                match states.first().cloned().flatten() {
                    Some(ScalarValue::Literal(term))
                        if states
                            .iter()
                            .all(|s| s.as_ref() == Some(&ScalarValue::Literal(term.clone()))) =>
                    {
                        ScalarValue::Literal(term)
                    }
                    Some(ScalarValue::Position(position))
                        if position < live
                            && states
                                .iter()
                                .all(|s| s.as_ref() == Some(&ScalarValue::Position(position))) =>
                    {
                        ScalarValue::Position(position)
                    }
                    _ => ScalarValue::Unknown,
                }
            };
            match joined {
                ScalarValue::Unknown => self.fresh_scalar_value(*id, ty),
                state => {
                    self.scalar_values.insert(*id, state);
                }
            }
        }
    }
    pub(super) fn map_scalar_state(
        map: &BTreeMap<BindingId, ScalarValue>,
        id: BindingId,
        live: usize,
    ) -> Option<ScalarValue> {
        match map.get(&id) {
            Some(ScalarValue::Literal(term)) => Some(ScalarValue::Literal(term.clone())),
            Some(ScalarValue::Position(position)) if *position < live => {
                Some(ScalarValue::Position(*position))
            }
            Some(_) => Some(ScalarValue::Unknown),
            None => None,
        }
    }
    /// Join the scalar state of a loop body back into the enclosing scope. Any
    /// scalar the body may have assigned becomes a fresh opaque binder; an
    /// untouched scalar keeps its stable index.
    pub(super) fn join_loop_scalars(
        &mut self,
        baseline: &BTreeMap<BindingId, ScalarValue>,
        body: &BTreeMap<BindingId, ScalarValue>,
        live: usize,
    ) {
        for (id, base) in baseline {
            let slot = self
                .slots
                .iter()
                .find_map(|(candidate, slot)| (candidate == id).then_some(*slot));
            let Some(slot) = slot else {
                continue;
            };
            let ty = self.locals[slot].ty;
            if ty.scalar_carrier().is_none() {
                continue;
            }
            let body_state = Self::map_scalar_state(body, *id, live);
            if body_state.as_ref() == Some(base) {
                self.scalar_values.insert(*id, base.clone());
            } else {
                self.fresh_scalar_value(*id, ty);
            }
        }
    }
    /// Whether this expression denotes an erased logical proof or data value
    /// rather than a runtime computation. Only such expressions may introduce a
    /// proof-valued local without a runtime slot.
    pub(super) fn erased_proof_expression(&self, expr: &ast::Expr) -> bool {
        let root = match &expr.kind {
            ast::ExprKind::Call { callee, .. } => self.logical_data_root(callee),
            _ => self.logical_data_root(expr),
        };
        let Some(id) = root else {
            return false;
        };
        self.logical.names.contains_key(&id)
            || self.logical.data.contains_key(&id)
            || self.logical.constructors.contains_key(&id)
            || self.kernel_proofs.contains_key(&id)
            || self.proof_values.contains_key(&id)
            || (self.resolution.bindings[id].kind == BindingKind::Builtin
                && matches!(
                    self.resolution.bindings[id].name.as_str(),
                    "refl" | "Nat.induct" | "Eq.transport" | "Eq.elim" | "Data.elim"
                ))
    }
    /// Elaborate the right-hand side of `let p = <proof>`. A name of another
    /// proof-valued local aliases its checked term, shifted to the current
    /// telescope. Anything else is checked in the current logical context.
    pub(super) fn elaborate_proof_local(&mut self, value: &ast::Expr) -> Result<Term> {
        if let Some(id) = self.resolution.reference(value.span)
            && let Some((stored, stored_len)) = self.proof_values.get(&id).cloned()
        {
            let current = self.kernel_locals.len();
            if current < stored_len {
                return Err(Diagnostic::new(
                    value.span,
                    "proof-valued local refers to a binder outside its scope",
                ));
            }
            return self
                .logical
                .kernel
                .shift_open(&stored, current - stored_len)
                .map_err(|e| {
                    Diagnostic::new(
                        value.span,
                        format!("internal error: proof-valued local shift failed: {e}"),
                    )
                });
        }
        let term = crate::check::elaborate_value_with_aliases(
            self.resolution,
            self.logical,
            &self.kernel_bindings(),
            value,
            &self.kernel_alias_sources(),
            &self.kernel_literals(),
        )
        .map_err(|e| {
            Diagnostic::new(
                e.span,
                format!(
                    "erased proof-valued local must be a checked logical term: {}",
                    e.message
                ),
            )
        })?;
        self.logical
            .kernel
            .infer_open(&term, &self.kernel_context())
            .map_err(|e| {
                Diagnostic::new(
                    value.span,
                    format!("invalid erased proof-valued local: {e}"),
                )
            })?;
        Ok(term)
    }
    /// Translate one evaluated runtime scalar argument into a kernel term in the
    /// caller's context. Only canonical literals and immutable, in-scope scalar
    /// locals are accepted: a proof must be frozen at its source evaluation
    /// point and must not reinterpret a mutable local's final value.
    pub(super) fn scalar_argument(&self, expr: &ast::Expr, ty: Type, span: Span) -> Result<Term> {
        let Some(carrier) = ty.scalar_carrier() else {
            return Err(Diagnostic::new(
                span,
                "only i64, Bool, and Unit runtime values can be symbolic proof indices",
            ));
        };
        let literal_error = || {
            Diagnostic::new(
                expr.span,
                "a symbolic proof index must be an integer, boolean, or unit literal, or the name of an immutable scalar local; evaluate the expression into a named immutable local first",
            )
        };
        match (carrier, &expr.kind) {
            (Scalar::I64, ast::ExprKind::Integer(text)) => {
                if let Ok(value) = text.parse::<i64>() {
                    return Ok(Term::i64(value));
                }
                Err(Diagnostic::new(
                    expr.span,
                    "machine integer literal is outside the i64 range",
                ))
            }
            (
                Scalar::I64,
                ast::ExprKind::Unary {
                    op: Kind::Minus,
                    operand,
                    ..
                },
            ) => {
                let ast::ExprKind::Integer(text) = &operand.kind else {
                    return Err(literal_error());
                };
                integer(text, true, expr.span).map(Term::i64)
            }
            (Scalar::Bool, ast::ExprKind::Bool(value)) => Ok(Term::boolean(*value)),
            (Scalar::Unit, ast::ExprKind::Tuple(values)) if values.is_empty() => Ok(Term::unit()),
            (_, ast::ExprKind::Name(_) | ast::ExprKind::Field { .. }) => {
                let Some(id) = self.resolution.reference(expr.span) else {
                    return Err(literal_error());
                };
                if let Some(term) = self.kernel_local_term(id) {
                    // The runtime type checker already established the scalar
                    // carrier; this guard keeps the kernel context authoritative.
                    if self.kernel_types.get(&id).and_then(normalized_scalar) == Some(carrier) {
                        return Ok(if carrier == Scalar::Unit {
                            // Canonical singleton encoding for Unit.
                            Term::unit()
                        } else {
                            term
                        });
                    }
                    return Err(Diagnostic::new(
                        expr.span,
                        "this scalar local has a different carrier from the indexed parameter",
                    ));
                }
                if self.slots.contains_key(&id) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a mutable runtime value cannot index an erased proof; bind an immutable local at the evaluation point",
                    ));
                }
                Err(literal_error())
            }
            _ => Err(literal_error()),
        }
    }
    /// Check one erased logical argument at a call site. The declared type is
    /// elaborated in the callee's open context (caller erased binders followed
    /// by earlier erased binders of this callee), validated as a type, and then
    /// the actual earlier proof terms are substituted before checking the
    /// evidence in the caller context.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn discharge_kernel_call(
        &mut self,
        parameter: &ast::Parameter,
        evidence: &ast::Expr,
        callee_binders: &mut Vec<BindingId>,
        callee_types: &mut Vec<Term>,
        callee_actuals: &mut Vec<Term>,
        span: Span,
    ) -> Result<()> {
        if matches!(&evidence.kind, ast::ExprKind::Name(name) if name == "_") {
            return Err(Diagnostic::new(
                evidence.span,
                "cannot discharge a logical proposition by arithmetic search; pass a named proof",
            ));
        }
        let mut context = self.kernel_context();
        context.extend(callee_types.iter().cloned());
        let mut bindings = self.kernel_bindings();
        for (id, ty) in callee_binders.iter().zip(callee_types.iter()) {
            bindings.push((*id, ty.clone()));
        }
        let expected =
            crate::check::elaborate_type(self.resolution, self.logical, &bindings, &parameter.ty)
                .map_err(|e| {
                Diagnostic::new(
                    e.span,
                    format!("invalid erased logical proposition: {}", e.message),
                )
            })?;
        let inferred = self
            .logical
            .kernel
            .sort_open(&expected, &context)
            .map_err(|e| {
                Diagnostic::new(
                    span,
                    format!("invalid dependent erased parameter type: {e}"),
                )
            })?;
        let _ = inferred;
        let caller_context = self.kernel_context();
        let caller_expected = self
            .logical
            .kernel
            .substitute_outer(&expected, callee_actuals)
            .map_err(|e| {
                Diagnostic::new(
                    span,
                    format!("internal error: dependent erased substitution failed: {e}"),
                )
            })?;
        let term = if let Some(id) = self.resolution.reference(evidence.span)
            && let Some((stored, stored_len)) = self.proof_values.get(&id).cloned()
        {
            let current = self.kernel_locals.len();
            if current < stored_len {
                return Err(Diagnostic::new(
                    evidence.span,
                    "proof-valued local refers to a binder outside its scope",
                ));
            }
            self.logical
                .kernel
                .shift_open(&stored, current - stored_len)
                .map_err(|e| {
                    Diagnostic::new(
                        evidence.span,
                        format!("internal error: proof-valued local shift failed: {e}"),
                    )
                })?
        } else {
            crate::check::elaborate_value_with_aliases(
                self.resolution,
                self.logical,
                &self.kernel_bindings(),
                evidence,
                &self.kernel_alias_sources(),
                &self.kernel_literals(),
            )
            .map_err(|e| {
                Diagnostic::new(
                    e.span,
                    format!(
                        "erased argument must be a checked logical proof term: {}",
                        e.message
                    ),
                )
            })?
        };
        // A runtime scalar may occur inside a proof term (as an index), but the
        // evidence itself must be a logical value, never a runtime observation.
        if self.evidence_is_runtime_scalar(&term) {
            return Err(Diagnostic::new(
                evidence.span,
                "a runtime scalar is a symbolic index, not erased evidence; construct a checked proof term instead",
            ));
        }
        self.logical
            .kernel
            .check_open(&term, &caller_expected, &caller_context)
            .map_err(|e| {
                Diagnostic::new(
                    span,
                    format!("proof does not establish the erased proposition: {e}"),
                )
            })?;
        callee_binders.push(self.resolution.binder(parameter.span).unwrap());
        callee_types.push(expected);
        callee_actuals.push(term);
        Ok(())
    }
    /// Whether an elaborated evidence term is exactly an in-scope runtime scalar
    /// variable (rather than a logical value whose indices mention one).
    pub(super) fn evidence_is_runtime_scalar(&self, term: &Term) -> bool {
        let Term::Var(index) = term else {
            return false;
        };
        let Some(position) = self.kernel_locals.len().checked_sub(1 + index) else {
            return false;
        };
        let Some(id) = self.kernel_locals.get(position) else {
            return false;
        };
        !self.kernel_proofs.contains_key(id)
            && self
                .kernel_types
                .get(id)
                .and_then(normalized_scalar)
                .is_some()
    }
    pub(super) fn bind(&mut self, span: Span, ty: Type, mutable: bool) -> Result<usize> {
        if self.locals.len() >= 1024 {
            return Err(Diagnostic::new(
                span,
                "function exceeds the 1024-local limit",
            ));
        }
        let Some(id) = self.resolution.binder(span) else {
            return Err(Diagnostic::new(
                span,
                "unsupported executable binding pattern",
            ));
        };
        let slot = self.locals.len();
        self.locals.push(Local {
            ty,
            mutable,
            linear: false,
            pinned: false,
            grade: None,
            span,
        });
        self.slots.insert(id, slot);
        Ok(slot)
    }
    /// Allocate a checked local with no source binder. Used only for compiler
    /// temporaries whose evaluation must happen exactly once, such as the
    /// midpoint and implicit parent of a checked mutable split.
    pub(super) fn fresh_local(&mut self, span: Span, ty: Type) -> Result<usize> {
        if self.locals.len() >= 1024 {
            return Err(Diagnostic::new(
                span,
                "function exceeds the 1024-local limit",
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
        Ok(slot)
    }
    pub(super) fn slot(&self, span: Span) -> Result<usize> {
        self.resolution
            .reference(span)
            .and_then(|id| self.slots.get(&id))
            .copied()
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "expected a scalar local value; function values are not supported yet",
                )
            })
    }
}
