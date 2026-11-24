//! Postconditions (`ensures`): symbolic values, formulas and their checks.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// A type that can hold a borrow (view, reference, text or a record of
    /// them).
    pub(super) fn borrowing_type(&self, ty: Type) -> bool {
        ty.is_view()
            || ty.is_ref()
            || ty.is_text()
            || crate::runtime_types::has_borrow(self.types, ty)
            || crate::runtime_types::contains_task(self.types, ty)
    }
    // ── ENSURES: postconditions ─────────────────────────────────────────────

    /// The record or enum literal an expression evaluates to, through the
    /// blocks and one-arm matches that literals and struct updates lower to.
    pub(super) fn literal_of(expr: &Expr) -> &Expr {
        let mut current = expr;
        loop {
            match &current.kind {
                ExprKind::Block(block) if block.tail.is_some() => {
                    current = block.tail.as_deref().unwrap();
                }
                ExprKind::Match(_, arms) if arms.len() == 1 && arms[0].guard.is_none() => {
                    current = &arms[0].body;
                }
                _ => return current,
            }
        }
    }
    /// The symbolic value of a checked expression.
    pub(super) fn sym_of(&self, expr: &Expr) -> Sym {
        match self.facts.root_of(expr) {
            Some((root, steps)) => Sym::Path(root, steps),
            None => Sym::Value(Box::new(expr.clone())),
        }
    }
    pub(super) fn path_linear(
        &self,
        root: crate::facts::Root,
        steps: &[crate::facts::Step],
        range: (i128, i128),
        ty: Type,
    ) -> crate::facts::Linear {
        let term = crate::facts::path_term(root, steps);
        match term {
            crate::facts::Term::Var(slot, _) => self.facts.note_type(slot, ty),
            _ => self.facts.note_term(term, range),
        }
        crate::facts::Linear::variable(term)
    }
    pub(super) fn sym_linear(&self, sym: &Sym, ty: Type) -> Option<crate::facts::Linear> {
        match sym {
            Sym::Path(root, steps) => {
                let range = crate::facts::scalar_range(ty)?;
                Some(self.path_linear(*root, steps, range, ty))
            }
            // An argument with no linear form (an element read, say) is
            // still some value of its type: a fresh term with that range.
            Sym::Value(expr) => self.facts.linear(expr).or_else(|| {
                let range = crate::facts::scalar_range(ty)?;
                let term = crate::facts::path_term(
                    crate::facts::Root::Value(crate::facts::fresh_value()),
                    &[],
                );
                self.facts.note_term(term, range);
                Some(crate::facts::Linear::variable(term))
            }),
            Sym::Unknown => None,
        }
    }
    /// Word offset and type of a record field, without visibility checks
    /// (a postcondition may mention private fields).
    pub(super) fn record_field_raw(&self, ty: Type, name: &str) -> Option<(usize, usize, Type)> {
        let ty = self.through_shared_ref(ty);
        let layout = ty.layout().filter(|id| self.types.enums[*id].record)?;
        let variant = &self.types.enums[layout].variants[0];
        let index = variant.names.iter().position(|n| n == name)?;
        let offset = self.types.enums[layout].tag_words()
            + variant.fields[..index]
                .iter()
                .map(|field| self.types.width(*field))
                .sum::<usize>();
        Some((index, offset, variant.fields[index]))
    }
    pub(super) fn sym_field(&self, sym: &Sym, ty: Type, name: &str) -> Option<(Sym, Type)> {
        let (index, offset, field_ty) = self.record_field_raw(ty, name)?;
        let sym = match sym {
            Sym::Path(root, steps) => {
                let mut steps = steps.clone();
                steps.push(crate::facts::Step::Field(u32::try_from(offset).ok()?));
                Sym::Path(*root, steps)
            }
            Sym::Value(expr) => match &Self::literal_of(expr).kind {
                ExprKind::Construct { fields, .. } => self.sym_of(&fields[index]),
                _ => Sym::Unknown,
            },
            Sym::Unknown => Sym::Unknown,
        };
        Some((sym, field_ty))
    }
    /// ENSURES-REFS: a shared reference's paths are its referent's.
    pub(super) fn through_shared_ref(&self, ty: Type) -> Type {
        match ty {
            Type::Ref(pointer) => self.types.pointees[pointer],
            other => other,
        }
    }
    pub(super) fn variant_index(&self, ty: Type, name: &str) -> Option<usize> {
        let ty = self.through_shared_ref(ty);
        let layout = ty.layout().filter(|id| !self.types.enums[*id].record)?;
        self.types.enums[layout]
            .variants
            .iter()
            .position(|variant| variant.name == name)
    }
    pub(super) fn sym_tag(&self, sym: &Sym, ty: Type) -> Option<crate::facts::Linear> {
        let ty = self.through_shared_ref(ty);
        let layout = ty.layout().filter(|id| !self.types.enums[*id].record)?;
        let count = self.types.enums[layout].variants.len();
        match sym {
            Sym::Path(root, steps) => {
                let mut steps = steps.clone();
                steps.push(crate::facts::Step::Tag);
                let term = crate::facts::path_term(*root, &steps);
                self.facts
                    .note_term(term, (0, i128::try_from(count).ok()? - 1));
                Some(crate::facts::Linear::variable(term))
            }
            Sym::Value(expr) => match &Self::literal_of(expr).kind {
                ExprKind::Construct { tag, .. } => {
                    Some(crate::facts::Linear::constant(i128::try_from(*tag).ok()?))
                }
                _ => None,
            },
            Sym::Unknown => None,
        }
    }
    pub(super) fn sym_payload(
        &self,
        sym: &Sym,
        ty: Type,
        variant: usize,
        index: usize,
    ) -> Option<(Sym, Type)> {
        let layout = ty.layout().filter(|id| !self.types.enums[*id].record)?;
        let fields = self.types.enums[layout]
            .variants
            .get(variant)?
            .fields
            .clone();
        let field_ty = *fields.get(index)?;
        let offset = self.types.enums[layout].tag_words()
            + fields[..index]
                .iter()
                .map(|field| self.types.width(*field))
                .sum::<usize>();
        let sym = match sym {
            Sym::Path(root, steps) => {
                let mut steps = steps.clone();
                steps.push(crate::facts::Step::Payload(
                    u32::try_from(variant).ok()?,
                    u32::try_from(offset).ok()?,
                ));
                Sym::Path(*root, steps)
            }
            Sym::Value(expr) => match &Self::literal_of(expr).kind {
                ExprKind::Construct { tag, fields, .. } if *tag == variant => {
                    self.sym_of(&fields[index])
                }
                _ => Sym::Unknown,
            },
            Sym::Unknown => Sym::Unknown,
        };
        Some((sym, field_ty))
    }
    /// A name or field path in a postcondition.
    pub(super) fn ensures_value(
        &self,
        e: &ast::Expr,
        env: &BTreeMap<BindingId, (Sym, Type)>,
    ) -> Option<(Sym, Type)> {
        match &e.kind {
            ast::ExprKind::Name(_) => env.get(&self.resolution.reference(e.span)?).cloned(),
            ast::ExprKind::Field { value, name } => {
                let (sym, ty) = self.ensures_value(value, env)?;
                self.sym_field(&sym, ty, name)
            }
            _ => None,
        }
    }
    pub(super) fn ensures_linear(
        &self,
        e: &ast::Expr,
        env: &BTreeMap<BindingId, (Sym, Type)>,
    ) -> Option<crate::facts::Linear> {
        use crate::facts::Linear;
        match &e.kind {
            ast::ExprKind::Integer(n) => Some(Linear::constant(n.parse().ok()?)),
            ast::ExprKind::Bool(value) => Some(Linear::constant(i128::from(*value))),
            ast::ExprKind::Unary {
                op: Kind::Minus,
                operand,
                ..
            } => self.ensures_linear(operand, env)?.negate(),
            ast::ExprKind::Binary {
                op: op @ (Kind::Plus | Kind::Minus | Kind::Star),
                left,
                right,
            } => {
                let (l, r) = (
                    self.ensures_linear(left, env)?,
                    self.ensures_linear(right, env)?,
                );
                match op {
                    Kind::Plus => l.add(&r),
                    Kind::Minus => l.sub(&r),
                    _ if l.is_constant() => r.scale(l.constant),
                    _ if r.is_constant() => l.scale(r.constant),
                    _ => None,
                }
            }
            ast::ExprKind::Name(_) | ast::ExprKind::Field { .. } => {
                let (sym, ty) = self.ensures_value(e, env)?;
                self.sym_linear(&sym, ty)
            }
            _ => None,
        }
    }
    /// A postcondition proposition as a formula. `lenient` (a hypothesis)
    /// replaces an atom it cannot state by `true`, which only weakens it; a
    /// goal returns `None` instead.
    pub(super) fn ensures_formula(
        &self,
        e: &ast::Expr,
        env: &BTreeMap<BindingId, (Sym, Type)>,
        positive: bool,
        lenient: bool,
    ) -> Option<crate::facts::Dnf> {
        use crate::facts::{Linear, compare_dnf, dnf_and, dnf_or};
        let unknown = || lenient.then(|| vec![Vec::new()]);
        let negated = |op: &Kind| match op {
            Kind::Lt => Kind::Ge,
            Kind::Le => Kind::Gt,
            Kind::Gt => Kind::Le,
            Kind::Ge => Kind::Lt,
            Kind::EqEq => Kind::Ne,
            _ => Kind::EqEq,
        };
        match &e.kind {
            ast::ExprKind::Binary {
                op: op @ (Kind::AmpAmp | Kind::PipePipe),
                left,
                right,
            } => {
                let l = self.ensures_formula(left, env, positive, lenient)?;
                let r = self.ensures_formula(right, env, positive, lenient)?;
                if (*op == Kind::AmpAmp) == positive {
                    dnf_and(&l, &r)
                } else {
                    dnf_or(l, r)
                }
            }
            ast::ExprKind::Unary {
                op: Kind::Bang,
                operand,
                ..
            } => self.ensures_formula(operand, env, !positive, lenient),
            ast::ExprKind::Binary {
                op: op @ (Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne),
                left,
                right,
            } => {
                let op = if positive { op.clone() } else { negated(op) };
                match (
                    self.ensures_linear(left, env),
                    self.ensures_linear(right, env),
                ) {
                    (Some(l), Some(r)) => compare_dnf(l, &op, r).or_else(unknown),
                    _ => unknown(),
                }
            }
            ast::ExprKind::Is { value, variant } => {
                let Some((sym, ty)) = self.ensures_value(value, env) else {
                    return unknown();
                };
                let (Some(tag), Some(index)) =
                    (self.sym_tag(&sym, ty), self.variant_index(ty, variant))
                else {
                    return unknown();
                };
                let op = if positive { Kind::EqEq } else { Kind::Ne };
                compare_dnf(tag, &op, Linear::constant(i128::try_from(index).ok()?))
                    .or_else(unknown)
            }
            ast::ExprKind::Bool(value) => Some(if *value == positive {
                vec![Vec::new()]
            } else {
                Vec::new()
            }),
            // ENSURES-PREDICATES: `pred(args)` means the predicate's
            // `result => { P }` with the arguments for its parameters.
            ast::ExprKind::Call { callee, arguments } => {
                let Ok((predicate, definition)) = self.ensures_predicate(callee) else {
                    return unknown();
                };
                if self.ensures_depth.get() >= 16 {
                    return unknown();
                }
                let mut inner = BTreeMap::new();
                for (parameter, argument) in predicate.parameters.iter().zip(arguments) {
                    let (Some(binder), Some(value)) = (
                        self.resolution.binder(parameter.span),
                        self.ensures_value(argument, env),
                    ) else {
                        return unknown();
                    };
                    inner.insert(binder, value);
                }
                self.ensures_depth.set(self.ensures_depth.get() + 1);
                let formula = self.ensures_formula(definition, &inner, positive, lenient);
                self.ensures_depth.set(self.ensures_depth.get() - 1);
                formula.or_else(unknown)
            }
            ast::ExprKind::Name(_) | ast::ExprKind::Field { .. } => {
                match self.ensures_value(e, env) {
                    Some((sym, Type::Bool)) => match self.sym_linear(&sym, Type::Bool) {
                        Some(term) => {
                            compare_dnf(term, &Kind::EqEq, Linear::constant(i128::from(positive)))
                                .or_else(unknown)
                        }
                        None => match &sym {
                            Sym::Value(expr) => if lenient {
                                self.facts.formula(expr, positive)
                            } else {
                                self.facts.formula_exact(expr, positive)
                            }
                            .or_else(unknown),
                            _ => unknown(),
                        },
                    },
                    _ => unknown(),
                }
            }
            _ => unknown(),
        }
    }
    /// ENSURES-PREDICATES: the function a call in a proposition names, and
    /// the `P` of its `ensures result => { P }`. It must return `Bool`, take
    /// only runtime parameters, not be generic, and have
    /// `ensures !result => { !(P) }` (or `P` = `!(Q)`), so `pred(args)` is
    /// exactly `P`.
    pub(super) fn ensures_predicate(
        &self,
        callee: &ast::Expr,
    ) -> std::result::Result<(&ast::Function, &ast::Expr), String> {
        let binding = self
            .resolution
            .reference(callee.span)
            .ok_or("a proposition can only call a named predicate function")?;
        let Some(declared) = self.functions.declared.get(&binding) else {
            return Err("a proposition can only call a named predicate function".into());
        };
        let f: &ast::Function = declared.ast;
        let name = &f.name;
        if !f.generics.is_empty() || f.parameters.iter().any(|p| p.erased) {
            return Err(format!(
                "'{name}' cannot be used in a proposition: a predicate takes no type or erased parameters"
            ));
        }
        if !matches!(f.result.kind, ast::TypeKind::Named { ref path, ref arguments, .. } if arguments.is_empty() && path.len() == 1 && path[0] == "Bool")
        {
            return Err(format!(
                "'{name}' cannot be used in a proposition: a predicate returns Bool"
            ));
        }
        let clause = |truth: bool| {
            let mut found = f
                .ensures
                .iter()
                .filter(move |c| c.guard == ast::EnsuresGuard::Result(truth));
            match (found.next(), found.next()) {
                (Some(clause), None) => Some(&clause.body),
                _ => None,
            }
        };
        let (Some(holds), Some(fails)) = (clause(true), clause(false)) else {
            return Err(format!(
                "'{name}' cannot be used in a proposition: a predicate needs exactly one 'ensures result => {{ P }}' and one 'ensures !result => {{ !(P) }}'"
            ));
        };
        let negation_of = |negated: &ast::Expr, original: &ast::Expr| {
            matches!(&negated.kind, ast::ExprKind::Unary { op: Kind::Bang, operand, .. }
                if self.same_proposition(operand, original))
        };
        if !negation_of(fails, holds) && !negation_of(holds, fails) {
            return Err(format!(
                "'{name}' cannot be used in a proposition: its '!result' clause must be the negation '!( .. )' of its 'result' clause, so the call means exactly that proposition"
            ));
        }
        Ok((f, holds))
    }
    /// Syntactic equality of two propositions (names compared by binding).
    pub(super) fn same_proposition(&self, a: &ast::Expr, b: &ast::Expr) -> bool {
        use ast::ExprKind as E;
        match (&a.kind, &b.kind) {
            (E::Name(x), E::Name(y)) => {
                x == y && self.resolution.reference(a.span) == self.resolution.reference(b.span)
            }
            (E::Integer(x), E::Integer(y)) => x == y,
            (E::Bool(x), E::Bool(y)) => x == y,
            (E::Field { value: v, name: n }, E::Field { value: w, name: m }) => {
                n == m && self.same_proposition(v, w)
            }
            (
                E::Unary {
                    op: o, operand: x, ..
                },
                E::Unary {
                    op: p, operand: y, ..
                },
            ) => o == p && self.same_proposition(x, y),
            (
                E::Binary {
                    op: o,
                    left: l1,
                    right: r1,
                },
                E::Binary {
                    op: p,
                    left: l2,
                    right: r2,
                },
            ) => o == p && self.same_proposition(l1, l2) && self.same_proposition(r1, r2),
            (
                E::Is {
                    value: v,
                    variant: n,
                },
                E::Is {
                    value: w,
                    variant: m,
                },
            ) => n == m && self.same_proposition(v, w),
            (
                E::Call {
                    callee: f,
                    arguments: x,
                },
                E::Call {
                    callee: g,
                    arguments: y,
                },
            ) => {
                self.resolution.reference(f.span) == self.resolution.reference(g.span)
                    && self.resolution.reference(f.span).is_some()
                    && x.len() == y.len()
                    && x.iter().zip(y).all(|(x, y)| self.same_proposition(x, y))
            }
            _ => false,
        }
    }
    /// Every call in a postcondition must name a predicate (definition-time
    /// diagnostic); its arguments must be names or field paths.
    pub(super) fn validate_ensures_calls(&self, e: &ast::Expr) -> Result<()> {
        self.validate_ensures_calls_at(e, 0)
    }
    pub(super) fn validate_ensures_calls_at(&self, e: &ast::Expr, depth: usize) -> Result<()> {
        use ast::ExprKind as E;
        match &e.kind {
            E::Call { callee, arguments } => {
                let (predicate, definition) = self
                    .ensures_predicate(callee)
                    .map_err(|message| Diagnostic::new(callee.span, message))?;
                if predicate.parameters.len() != arguments.len() {
                    return Err(Diagnostic::new(
                        e.span,
                        format!(
                            "'{}' takes {} argument(s), found {}",
                            predicate.name,
                            predicate.parameters.len(),
                            arguments.len()
                        ),
                    ));
                }
                for argument in arguments {
                    let mut path = argument;
                    while let E::Field { value, .. } = &path.kind {
                        path = value;
                    }
                    if !matches!(path.kind, E::Name(_)) {
                        return Err(Diagnostic::new(
                            argument.span,
                            "a predicate argument in a proposition must be a name or a field path",
                        ));
                    }
                }
                if depth >= 16 {
                    return Err(Diagnostic::new(
                        e.span,
                        "predicates in propositions nest too deeply (a predicate may not use itself)",
                    ));
                }
                self.validate_ensures_calls_at(definition, depth + 1)
            }
            E::Unary { operand, .. } => self.validate_ensures_calls_at(operand, depth),
            E::Binary { left, right, .. } => {
                self.validate_ensures_calls_at(left, depth)?;
                self.validate_ensures_calls_at(right, depth)
            }
            _ => Ok(()),
        }
    }
    /// One clause as `!guard || P`, for the given parameters and result.
    pub(super) fn ensures_clause(
        &self,
        clause: &ast::Ensures,
        params: &BTreeMap<BindingId, (Sym, Type)>,
        result: &(Sym, Type),
        lenient: bool,
    ) -> Option<crate::facts::Dnf> {
        use crate::facts::{Linear, compare_dnf, dnf_or};
        let mut env = params.clone();
        env.insert(self.resolution.binder(clause.result_span)?, result.clone());
        // Where the guard fails (the clause then says nothing).
        let outside: Option<crate::facts::Dnf> = match &clause.guard {
            ast::EnsuresGuard::Always => Some(Vec::new()),
            ast::EnsuresGuard::Result(truth) => match &result.0 {
                Sym::Value(expr) if expr.ty == Type::Bool => {
                    if lenient {
                        self.facts.formula(expr, !truth)
                    } else {
                        self.facts.formula_exact(expr, !truth)
                    }
                }
                sym => self.sym_linear(sym, Type::Bool).and_then(|term| {
                    compare_dnf(term, &Kind::EqEq, Linear::constant(i128::from(!truth)))
                }),
            },
            ast::EnsuresGuard::Variant { name, binders, .. } => {
                let index = self.variant_index(result.1, name)?;
                for (position, (_, span)) in binders.iter().enumerate() {
                    let binding = self.resolution.binder(*span)?;
                    let payload = self
                        .sym_payload(&result.0, result.1, index, position)
                        .unwrap_or((Sym::Unknown, Type::Unit));
                    env.insert(binding, payload);
                }
                match &result.0 {
                    Sym::Value(expr) => match &expr.kind {
                        ExprKind::Construct { tag, .. } if *tag == index => Some(Vec::new()),
                        ExprKind::Construct { .. } => Some(vec![Vec::new()]),
                        _ => None,
                    },
                    sym => self.sym_tag(sym, result.1).and_then(|tag| {
                        compare_dnf(
                            tag,
                            &Kind::Ne,
                            Linear::constant(i128::try_from(index).ok()?),
                        )
                    }),
                }
            }
        };
        // A clause whose guard cannot be stated is dropped as a hypothesis
        // and is an error as a goal.
        let outside = outside?;
        // The guard is known not to hold: the clause is true.
        if outside.iter().any(Vec::is_empty) {
            return Some(vec![Vec::new()]);
        }
        let body = self.ensures_formula(&clause.body, &env, true, lenient)?;
        dnf_or(outside, body)
    }
    /// Prove every postcondition for a value the function returns.
    pub(super) fn check_postconditions(&mut self, value: &Expr) -> Result<()> {
        let Some(context) = self.ensures_context.clone() else {
            return Ok(());
        };
        if value.ty == Type::Never {
            return Ok(());
        }
        let params = context
            .params
            .iter()
            .map(|(id, slot)| {
                (
                    *id,
                    (
                        Sym::Path(crate::facts::Root::Var(*slot, 0), Vec::new()),
                        self.locals[*slot].ty,
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let result = (self.sym_of(value), context.result);
        for clause in &context.clauses {
            let Some(goal) = self.ensures_clause(clause, &params, &result, false) else {
                return Err(Diagnostic::new(
                    value.span,
                    "this postcondition cannot be stated for the returned value: it needs linear terms over parameters, 'result', field paths, and 'is' tests",
                )
                .with_note(clause.span, "postcondition declared here"));
            };
            let Some(certificates) = self.facts.certify(&goal, value.span, "postcondition") else {
                let known = self.facts.snapshot_formula(&goal);
                let names = (0..self.locals.len())
                    .map(|s| self.local_name(s))
                    .collect::<Vec<_>>();
                return Err(crate::facts::failure(
                    value.span,
                    &format!("ensures {}", ensures_text(clause)),
                    &known,
                    &|slot| names[slot].clone(),
                )
                .with_note(clause.span, "postcondition declared here"));
            };
            self.functions.certificates.extend(certificates);
        }
        Ok(())
    }
    /// After a call to a function with postconditions, its clauses hold of
    /// this call's result (a fresh identity) and the actual arguments.
    pub(super) fn assume_postconditions(
        &mut self,
        f: &ast::Function,
        arguments: &[Expr],
        span: Span,
        result: Type,
    ) {
        let id = self.facts.register_call(span);
        let params = f
            .parameters
            .iter()
            .filter(|p| !p.erased)
            .zip(arguments)
            .filter_map(|(p, argument)| {
                Some((
                    self.resolution.binder(p.span)?,
                    (self.sym_of(argument), argument.ty),
                ))
            })
            .collect::<BTreeMap<_, _>>();
        let result = (Sym::Path(crate::facts::Root::Value(id), Vec::new()), result);
        for clause in &f.ensures {
            if let Some(formula) = self.ensures_clause(clause, &params, &result, true)
                && formula.len() <= 32
            {
                self.facts.add_formula(formula);
            }
        }
    }
    /// In a match arm, the scrutinee has the arm's variant and the pattern's
    /// payload binders denote its payload fields.
    pub(super) fn assume_pattern(&mut self, value: &Expr, pattern: &Pattern) {
        use crate::facts::Step;
        let Some((root, steps)) = self.facts.root_of(value) else {
            return;
        };
        let Pattern::Variant { tag, fields, .. } = pattern else {
            return;
        };
        let Some(layout) = value.ty.layout() else {
            return;
        };
        let record = self.types.enums[layout].record;
        if !record && let Some(tag_term) = self.sym_tag(&Sym::Path(root, steps.clone()), value.ty) {
            let mut out = Vec::new();
            crate::facts::compare(
                tag_term,
                &Kind::EqEq,
                crate::facts::Linear::constant(*tag as i128),
                &mut out,
            );
            self.facts.add(out);
        }
        for (offset, sub) in fields {
            if let Pattern::Bind(slot) = sub {
                let mut path = steps.clone();
                path.push(if record {
                    Step::Field(*offset as u32)
                } else {
                    Step::Payload(*tag as u32, *offset as u32)
                });
                self.facts.alias(*slot, root, path);
            }
        }
    }
}
