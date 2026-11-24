//! User calls, records, structural literals and record patterns.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    pub(super) fn user_call(
        &mut self,
        id: BindingId,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let f = self.functions.declared[&id].ast;
        if arguments.len() != f.parameters.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count for '{}': expected {}, found {}",
                    f.name,
                    f.parameters.len(),
                    arguments.len()
                ),
            ));
        }
        if explicit.is_some() && f.generics.is_empty() {
            return Err(Diagnostic::new(
                span,
                format!("'{}' is not generic; remove the type arguments", f.name),
            ));
        }
        let pairs = f
            .parameters
            .iter()
            .zip(arguments)
            .filter(|(p, _)| !p.erased)
            .map(|(p, a)| (&p.ty, a))
            .collect::<Vec<_>>();
        let what = format!("'{}'", f.name);
        let hint = match expected {
            Some(expected) => Some((self.result_type_hint(&f.result)?, expected)),
            None => None,
        };
        let lifetime_binders = f
            .lifetimes
            .iter()
            .map(|lifetime| lifetime.name.clone())
            .collect::<BTreeSet<_>>();
        let lengths = self.call_runtime_lengths(f, 0, arguments)?;
        self.pending_lengths = lengths.clone();
        // Arguments of length-refined parameters: the callee keeps the bound,
        // so a refined place may be lent there; what the argument already
        // guarantees decides whether a run-time check is needed.
        let mut refined_arguments = Vec::new();
        let mut runtime_index = 0;
        for (parameter, argument) in f.parameters.iter().zip(arguments) {
            let position = runtime_index;
            if !parameter.erased {
                runtime_index += 1;
            }
            let Some(length) = &parameter.min_length else {
                continue;
            };
            let Some(length) = self.ast_integer(length, 0) else {
                continue;
            };
            let known = match &argument.kind {
                ast::ExprKind::Unary {
                    op: Kind::Amp,
                    operand,
                    ..
                } => self.place_min_length(operand),
                ast::ExprKind::Name(_) => self.place_min_length(argument),
                _ => None,
            };
            self.lending_spans
                .insert((argument.span.start, argument.span.end));
            refined_arguments.push((
                argument.span,
                position,
                length,
                known.is_some_and(|known| known >= length),
            ));
        }
        let inferred = self.infer(
            &f.generics,
            explicit,
            &pairs,
            hint.as_ref()
                .map(|(declared, expected)| (declared, *expected)),
            Some(&lifetime_binders),
            None,
            None,
            &what,
            span,
        );
        for (argument_span, _, _, _) in &refined_arguments {
            self.lending_spans
                .remove(&(argument_span.start, argument_span.end));
        }
        let (type_arguments, grade_arguments, const_arguments, effect_arguments, values) =
            inferred?;
        let index = self.functions.instance(
            self.types,
            self.resolution,
            id,
            type_arguments,
            grade_arguments,
            const_arguments,
            effect_arguments,
            None,
            Some(span),
        )?;
        let mut signature = self.functions.signatures[index].clone();
        let (lifetime_binders, lifetime_names) = signature.scope_call_lifetimes();
        self.require(signature.effects, span)?;
        let diverges = values.iter().any(|value| value.ty == Type::Never);
        // One occurrence map serves both argument invariance and the result,
        // including any fresh identities for unresolved lexical borrows.
        let lifetime_map = if diverges {
            BTreeMap::new()
        } else {
            self.resolve_call_lifetimes(
                &lifetime_binders,
                &signature.parameters,
                &values,
                &signature.lifetime_bounds,
                &lifetime_names,
                span,
            )?
        };
        let ty = if diverges {
            Type::Never
        } else if crate::runtime_types::grade_erases(signature.result_grade) {
            Type::Unit
        } else {
            let result = self
                .types
                .relabel_lifetimes(signature.result, &lifetime_map, span)?;
            self.types.rebind_lengths(result, &lengths, span)?
        };
        let mut coerced = Vec::with_capacity(values.len());
        for (position, (value, ty)) in values.into_iter().zip(&signature.parameters).enumerate() {
            let ty = self.types.relabel_lifetimes(*ty, &lifetime_map, span)?;
            let ty = self.types.rebind_lengths(ty, &lengths, span)?;
            let value = self.coerce_argument(value, ty, span)?;
            // An argument whose length is not already known to be enough is
            // checked here, once, before the call.
            let value = match refined_arguments
                .iter()
                .find(|(_, index, _, _)| *index == position)
            {
                Some((_, _, length, false)) if value.ty != Type::Never => {
                    self.reference_length_checked(value, *length)?
                }
                _ => value,
            };
            coerced.push(value);
        }
        let values = coerced;
        // Runtime parameter types aligned with the source parameter list. Erased
        // parameters are absent from the runtime signature.
        let mut signature_types = signature.parameters.iter();
        let parameter_types = f
            .parameters
            .iter()
            .map(|parameter| {
                if parameter.erased {
                    None
                } else {
                    Some(*signature_types.next().expect("runtime parameter"))
                }
            })
            .collect::<Vec<_>>();
        // Dependent erased parameters are checked left to right. A later
        // parameter type may mention an earlier erased kernel binder or an
        // immutable runtime scalar used as a symbolic index; the call-site
        // substitutes the actual scalar/proof terms.
        let mut callee_binders = Vec::new();
        let mut callee_types = Vec::new();
        let mut callee_actuals = Vec::new();
        for (position, (parameter, evidence)) in f.parameters.iter().zip(arguments).enumerate() {
            if !parameter.erased {
                let binder = self.resolution.binder(parameter.span).unwrap();
                if !diverges
                    && let Some(carrier) = parameter_types[position].and_then(Type::scalar_carrier)
                    && f.parameters[position + 1..].iter().any(|later| {
                        later.erased
                            && !matches!(later.ty.kind, ast::TypeKind::Predicate(_))
                            && type_references_binding(self.resolution, &later.ty, binder)
                    })
                {
                    let actual = self.scalar_argument(
                        &arguments[position],
                        parameter_types[position].unwrap(),
                        span,
                    )?;
                    callee_binders.push(binder);
                    callee_types.push(Term::Scalar(carrier));
                    callee_actuals.push(actual);
                }
                continue;
            }
            if diverges {
                continue;
            }
            if matches!(parameter.ty.kind, ast::TypeKind::Predicate(_)) {
                let proposition = proposition_of(self.resolution, f, parameter)?;
                self.discharge(&proposition, &values, evidence, span)?;
            } else {
                self.discharge_kernel_call(
                    parameter,
                    evidence,
                    &mut callee_binders,
                    &mut callee_types,
                    &mut callee_actuals,
                    span,
                )?;
            }
        }
        // STD-SYS-FOREIGN: runtime stubs trust their arguments, so only std
        // may call them; programs reach them through std's safe modules.
        if let Some(foreign) = self.functions.foreign_functions.get(&index)
            && foreign.symbol.starts_with("kush_sys_")
            && (self.unit == 0
                || self
                    .resolution
                    .units
                    .get(self.unit)
                    .is_none_or(|path| path.first().is_none_or(|p| p != "std")))
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' is a std-internal system call; use the safe std modules (std.file, ...) instead",
                    f.name
                ),
            ));
        }
        self.apply_effect_writes(signature.effects);
        let (statements, values) = self.two_phase_arguments(values, ty)?;
        let value = Expr {
            kind: ExprKind::Call(
                if self.functions.foreign_functions.contains_key(&index) {
                    Target::Foreign(index)
                } else {
                    Target::Function(index)
                },
                values,
            ),
            ty,
            span,
            resource: None,
        };
        if !f.ensures.is_empty()
            && ty != Type::Never
            && let ExprKind::Call(_, arguments) = &value.kind
        {
            self.assume_postconditions(f, arguments, span, ty);
        }
        let value = Self::after(statements, value);
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Infer a record literal's erased lifetime arguments from the values that
    /// supply its fields. A declared lifetime used by exactly one field whose
    /// checked value carries exactly one erased label adopts that actual label;
    /// otherwise the slot keeps a fresh local identity. This is a mapping from
    /// checked provenance, never a guess: ambiguous fields stay anonymous so a
    /// later invariant conversion must still prove identity.
    pub(super) fn infer_record_lifetimes(
        &mut self,
        pairs: &[(&ast::Type, &ast::Expr)],
        values: &[Expr],
        declared: &[ast::Lifetime],
    ) -> Vec<String> {
        let declared_names: BTreeSet<String> = declared
            .iter()
            .map(|lifetime| lifetime.name.clone())
            .collect();
        let mut candidates: BTreeMap<String, BTreeSet<String>> = declared_names
            .iter()
            .map(|name| (name.clone(), BTreeSet::new()))
            .collect();
        // Only a field whose declared type actually mentions the lifetime can
        // supply evidence for it. An unrelated field with its own borrow label
        // must not be mistaken for the declaration's identity, even when the
        // record has a single lifetime parameter.
        for ((declared_ty, _), value) in pairs.iter().zip(values) {
            let mut used = BTreeSet::new();
            type_lifetimes(declared_ty, &mut used);
            used.retain(|name| declared_names.contains(name));
            let actuals = crate::runtime_types::borrow_lifetimes(self.types, value.ty);
            let actuals = actuals
                .into_iter()
                .filter(|label| !label.is_empty() && !label.starts_with('<'))
                .collect::<BTreeSet<_>>();
            if used.len() == 1 && actuals.len() == 1 {
                let field_lifetime = used.into_iter().next().expect("one field lifetime");
                let actual = actuals.into_iter().next().expect("one actual lifetime");
                candidates.entry(field_lifetime).or_default().insert(actual);
            }
        }
        declared
            .iter()
            .map(|lifetime| {
                let actuals = candidates.get(&lifetime.name);
                match actuals {
                    Some(actuals) if actuals.len() == 1 => {
                        actuals.iter().next().expect("one candidate").clone()
                    }
                    _ => self.types.fresh_lifetime("inferred record lifetime"),
                }
            })
            .collect()
    }
    pub(super) fn record(
        &mut self,
        path: &ast::Expr,
        fields: &[(String, ast::Expr)],
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let (base, explicit) = match &path.kind {
            ast::ExprKind::Specialize { callee, arguments } => {
                (callee.as_ref(), Some(arguments.as_slice()))
            }
            _ => (path, None),
        };
        let id = self
            .resolution
            .reference(base.span)
            .filter(|id| self.types.is_record(*id))
            .ok_or_else(|| Diagnostic::new(base.span, "expected a record (struct) type name"))?;
        let (generics, declared) = self.types.record_fields(id);
        // Building a record needs every field, so every one must be visible.
        for field in declared {
            self.check_field_visible(id, &field.name, span)?;
        }
        for (name, value) in fields {
            if !declared.iter().any(|f| f.name == *name) {
                return Err(Diagnostic::new(
                    value.span,
                    format!("record has no field '{name}'"),
                ));
            }
        }
        if let Some(missing) = declared
            .iter()
            .find(|f| !fields.iter().any(|(n, _)| *n == f.name))
        {
            return Err(Diagnostic::new(
                span,
                format!("missing field '{}' in record literal", missing.name),
            ));
        }
        // Values are checked and evaluated in source order.
        let pairs = fields
            .iter()
            .map(|(name, value)| {
                (
                    &declared.iter().find(|f| f.name == *name).unwrap().ty,
                    value,
                )
            })
            .collect::<Vec<_>>();
        let mut expected_layout = expected
            .and_then(Type::layout)
            .filter(|l| self.types.enums[*l].definition == id);
        if explicit.is_none()
            && expected_layout.is_none()
            && let Some(Type::Union(union)) = expected
        {
            let matching = self.types.unions[union]
                .members
                .iter()
                .filter_map(|member| {
                    member
                        .layout()
                        .filter(|layout| self.types.enums[*layout].definition == id)
                })
                .collect::<Vec<_>>();
            match matching.as_slice() {
                [] => {}
                [layout] => expected_layout = Some(*layout),
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        "this record literal fits several union alternatives; write explicit type arguments",
                    ));
                }
            }
        }
        let declared_lifetimes = self.types.record_lifetimes(id);
        let mut explicit_lifetimes = Vec::new();
        let mut explicit_types: Vec<ast::Type> = Vec::new();
        let mut seen_type = false;
        if let Some(arguments) = explicit {
            for argument in arguments {
                if let ast::TypeKind::Lifetime(name) = &argument.kind {
                    if seen_type {
                        return Err(Diagnostic::new(
                            span,
                            "record lifetime arguments must precede type arguments",
                        ));
                    }
                    explicit_lifetimes.push(name.clone());
                } else {
                    seen_type = true;
                    explicit_types.push(argument.clone());
                }
            }
        }
        if explicit.is_some() && explicit_lifetimes.len() != declared_lifetimes.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "this record expects {} lifetime argument(s), found {}",
                    declared_lifetimes.len(),
                    explicit_lifetimes.len()
                ),
            ));
        }
        let lifetime_binders = declared_lifetimes
            .iter()
            .map(|lifetime| lifetime.name.clone())
            .collect::<BTreeSet<_>>();
        let (arguments, consts, lifetimes, values) =
            if let (None, Some(layout)) = (explicit, expected_layout) {
                let arguments = self.types.enums[layout].arguments.clone();
                let consts = self.types.enums[layout].consts.clone();
                let expected_lifetimes = self.types.enums[layout].lifetimes.clone();
                let mut subst = crate::runtime_types::Subst::default();
                let mut type_index = 0;
                let mut const_index = 0;
                for (generic, is_const) in generics.iter().zip(self.types.generic_kinds(id)) {
                    let binder = self.resolution.binder(generic.span).unwrap();
                    if is_const {
                        subst.consts.insert(binder, consts[const_index]);
                        const_index += 1;
                    } else {
                        subst.types.insert(binder, arguments[type_index]);
                        type_index += 1;
                    }
                }
                // A call argument's expected record may carry freshly generated
                // binder placeholders. Those placeholders make the fields local
                // to this occurrence; they are not the literal's actual
                // identity. Infer that identity from the checked field values
                // instead of adopting the placeholder, so the enclosing call
                // can relate the real provenance to the callee binder. Explicit
                // caller labels keep their normal annotation obligation.
                let has_placeholder = expected_lifetimes
                    .iter()
                    .any(|lifetime| lifetime.starts_with("<argument lifetime "));
                for (declared, actual) in declared_lifetimes.iter().zip(&expected_lifetimes) {
                    let actual = if has_placeholder && actual.starts_with("<argument lifetime ") {
                        self.types.fresh_lifetime("argument lifetime")
                    } else {
                        actual.clone()
                    };
                    subst.lifetimes.insert(declared.name.clone(), actual);
                }
                let mut values = Vec::new();
                for (declared, value) in &pairs {
                    let wanted = self.types.ty_in(declared, &subst)?;
                    values.push(self.expr_expected(value, Some(wanted))?);
                }
                let lifetimes = if has_placeholder {
                    let inferred = self.infer_record_lifetimes(&pairs, &values, declared_lifetimes);
                    expected_lifetimes
                        .iter()
                        .zip(inferred)
                        .map(|(expected, inferred)| {
                            if expected.starts_with("<argument lifetime ") {
                                inferred
                            } else {
                                expected.clone()
                            }
                        })
                        .collect()
                } else {
                    expected_lifetimes
                };
                (arguments, consts, lifetimes, values)
            } else {
                // When the literal has no expected type, its own declared
                // lifetime names are placeholders for values this occurrence
                // infers, not caller binders. Freshen them before checking
                // fields so a field value cannot masquerade as the record's
                // declared label; actual provenance labels stay on the value
                // and drive inference below.
                let mut placeholder_substitution = crate::runtime_types::Subst::default();
                if explicit.is_none() {
                    for lifetime in declared_lifetimes {
                        placeholder_substitution.lifetimes.insert(
                            lifetime.name.clone(),
                            self.types.fresh_lifetime("argument lifetime"),
                        );
                    }
                }
                let (arguments, _grades, consts, _effects, values) = self.infer(
                    generics,
                    if explicit.is_some() {
                        Some(explicit_types.as_slice())
                    } else {
                        None
                    },
                    &pairs,
                    None,
                    // Nested borrowed fields must be inferred from their
                    // actual values, not from the enclosing declaration's
                    // lifetime names. The final construct validates explicit
                    // outer lifetime relationships against field provenance.
                    Some(&lifetime_binders),
                    None,
                    Some(&placeholder_substitution),
                    "this record",
                    span,
                )?;
                let lifetimes = if explicit.is_some() {
                    explicit_lifetimes
                } else {
                    self.infer_record_lifetimes(&pairs, &values, declared_lifetimes)
                };
                (arguments, consts, lifetimes, values)
            };
        let layout = self
            .types
            .instantiate(id, arguments, consts, lifetimes, span)?;
        let variant = self.types.enums[layout].variants[0].clone();
        let mut diverges = false;
        for ((name, _), value) in fields.iter().zip(&values) {
            let index = variant.names.iter().position(|n| n == name).unwrap();
            self.expect(value.ty, variant.fields[index], value.span)?;
            diverges |= value.ty == Type::Never;
        }
        let order = fields
            .iter()
            .map(|(name, _)| variant.names.iter().position(|n| n == name).unwrap())
            .collect::<Vec<_>>();
        let ty = if diverges {
            Type::Never
        } else {
            Type::Enum(layout)
        };
        let construct = if order.iter().enumerate().all(|(i, o)| i == *o) {
            Expr {
                kind: ExprKind::Construct {
                    enum_id: layout,
                    tag: 0,
                    fields: values,
                },
                ty,
                span,
                resource: None,
            }
        } else {
            // Evaluate in source order into temporaries, then build in layout order.
            let mut statements = Vec::new();
            let mut slots = vec![0; order.len()];
            for (value, index) in values.into_iter().zip(&order) {
                let slot = self.temp(variant.fields[*index], value.span)?;
                self.locals[slot].linear = self.value_moves_linear(&value);
                slots[*index] = slot;
                self.define_temp_facts(slot, &value);
                statements.push(Statement::Let(slot, value));
            }
            let fields = slots
                .iter()
                .zip(&variant.fields)
                .map(|(slot, ty)| Expr {
                    kind: ExprKind::Local(*slot),
                    ty: *ty,
                    span,
                    resource: None,
                })
                .collect();
            let tail = Expr {
                kind: ExprKind::Construct {
                    enum_id: layout,
                    tag: 0,
                    fields,
                },
                ty: Type::Enum(layout),
                span,
                resource: None,
            };
            Expr {
                kind: ExprKind::Block(Block {
                    statements,
                    tail: Some(Box::new(tail)),
                    ty,
                }),
                ty,
                span,
                resource: None,
            }
        };
        match expected {
            Some(expected) => self.coerce(construct, expected, span),
            None => Ok(construct),
        }
    }
    /// STRUCT-UPDATE: `S { f: v, ..base }` (user-approved Rust semantics).
    /// `base` is checked first and, unless it is a local, evaluated into a
    /// temporary; the field values follow in source order; then `base` is
    /// consumed by a one-arm match that moves its other fields into the new
    /// record and drops the replaced ones (a linear one is rejected). Every
    /// field must be visible, as for a full literal.
    pub(super) fn record_update(
        &mut self,
        path: &ast::Expr,
        fields: &[(String, ast::Expr)],
        base_ast: &ast::Expr,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        if matches!(path.kind, ast::ExprKind::Specialize { .. }) {
            return Err(Diagnostic::new(
                path.span,
                "a struct update takes its type arguments from its base; remove them",
            ));
        }
        let id = self
            .resolution
            .reference(path.span)
            .filter(|id| self.types.is_record(*id))
            .ok_or_else(|| Diagnostic::new(path.span, "expected a record (struct) type name"))?;
        let declared = self
            .types
            .record_fields(id)
            .1
            .iter()
            .map(|field| field.name.clone())
            .collect::<Vec<_>>();
        for name in &declared {
            self.check_field_visible(id, name, span)?;
        }
        for (name, value) in fields {
            if !declared.contains(name) {
                return Err(Diagnostic::new(
                    value.span,
                    format!("record has no field '{name}'"),
                ));
            }
        }
        let base_expected = expected.filter(|ty| {
            ty.layout().is_some_and(|layout| {
                self.types.enums[layout].record && self.types.enums[layout].definition == id
            })
        });
        let mut base = self.expr_expected(base_ast, base_expected)?;
        if base.ty == Type::Never {
            return Ok(base);
        }
        let Some(layout) = base.ty.layout().filter(|layout| {
            self.types.enums[*layout].record && self.types.enums[*layout].definition == id
        }) else {
            return Err(Diagnostic::new(
                base_ast.span,
                format!(
                    "the base of this struct update must have type {}, found {}",
                    self.resolution.bindings[id].name,
                    self.types.name(base.ty)
                ),
            ));
        };
        let ty = base.ty;
        if let ExprKind::Peek(slot) = base.kind {
            base.kind = ExprKind::Local(slot);
        }
        let variant = self.types.enums[layout].variants[0].clone();
        let mut statements = Vec::new();
        let base_value = if matches!(base.kind, ExprKind::Local(_) | ExprKind::Move(_)) {
            base
        } else {
            let slot = self.temp(ty, base.span)?;
            self.locals[slot].linear = self.value_moves_linear(&base);
            self.define_temp_facts(slot, &base);
            let base_span = base.span;
            statements.push(Statement::Let(slot, base));
            Expr {
                kind: ExprKind::Local(slot),
                ty,
                span: base_span,
                resource: None,
            }
        };
        let mut overrides = BTreeMap::new();
        for (name, value_ast) in fields {
            let index = variant.names.iter().position(|n| n == name).unwrap();
            let field_ty = variant.fields[index];
            if self.linear_type(field_ty) {
                return Err(Diagnostic::new(
                    value_ast.span,
                    format!(
                        "field '{name}' is linear: a struct update would drop the base's value; destructure the base and consume it"
                    ),
                ));
            }
            let value = self.expr_expected(value_ast, Some(field_ty))?;
            if value.ty == Type::Never {
                statements.push(Statement::Expr(value));
                return Ok(Expr {
                    kind: ExprKind::Block(Block {
                        statements,
                        tail: None,
                        ty: Type::Never,
                    }),
                    ty: Type::Never,
                    span,
                    resource: None,
                });
            }
            self.expect(value.ty, field_ty, value.span)?;
            let slot = self.temp(field_ty, value.span)?;
            self.locals[slot].linear = self.value_moves_linear(&value);
            self.define_temp_facts(slot, &value);
            statements.push(Statement::Let(slot, value));
            overrides.insert(
                index,
                Expr {
                    kind: ExprKind::Local(slot),
                    ty: field_ty,
                    span,
                    resource: None,
                },
            );
        }
        // The base is read after the field values (which may read it).
        let base_root = self.facts.root_of(&base_value);
        let mut pattern_fields = Vec::new();
        let mut construct_fields = Vec::new();
        let mut offset = self.types.enums[layout].tag_words();
        for (index, field_ty) in variant.fields.iter().enumerate() {
            if let Some(value) = overrides.remove(&index) {
                // The replaced value is bound and dropped at the end of the
                // arm (a wildcard would be rejected inside a linear record).
                let slot = self.temp(*field_ty, span)?;
                pattern_fields.push((offset, Pattern::Bind(slot)));
                construct_fields.push(value);
            } else {
                let slot = self.temp(*field_ty, span)?;
                if let Some((root, steps)) = &base_root {
                    let mut steps = steps.clone();
                    steps.push(crate::facts::Step::Field(
                        u32::try_from(offset).expect("record field offset"),
                    ));
                    self.facts.alias(slot, *root, steps);
                }
                pattern_fields.push((offset, Pattern::Bind(slot)));
                construct_fields.push(Expr {
                    kind: ExprKind::Local(slot),
                    ty: *field_ty,
                    span,
                    resource: None,
                });
            }
            offset += self.types.width(*field_ty);
        }
        let pattern = Pattern::Variant {
            tag: 0,
            tagged: self.types.enums[layout].tag_words() != 0,
            niche: self.types.enums[layout].niche(),
            fields: pattern_fields,
        };
        self.linear_pattern(
            &pattern,
            self.value_moves_linear(&base_value) && !self.linear_type(ty),
        );
        let construct = Expr {
            kind: ExprKind::Construct {
                enum_id: layout,
                tag: 0,
                fields: construct_fields,
            },
            ty,
            span,
            resource: None,
        };
        // A `where len >= N` field must hold its length after an update too.
        let construct = self.establish_field_lengths(construct)?;
        let matched = Expr {
            kind: ExprKind::Match(
                Box::new(base_value),
                vec![Arm {
                    pattern,
                    guard: None,
                    body: construct,
                }],
            ),
            ty,
            span,
            resource: None,
        };
        let value = Expr {
            kind: ExprKind::Block(Block {
                statements,
                tail: Some(Box::new(matched)),
                ty,
            }),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Facts for a compiler temporary bound to `value`: its scalar value, or
    /// the symbolic identity of a whole value.
    pub(super) fn define_temp_facts(&mut self, slot: usize, value: &Expr) {
        self.facts.define(slot, value);
        if crate::facts::scalar_range(value.ty).is_none()
            && let Some((root, steps)) = self.facts.root_of(value)
        {
            self.facts.alias(slot, root, steps);
        }
    }
    /// `let x = S { .. }`: each scalar field of the literal (also of nested
    /// literals) is known as `x.f == value` (STRUCT-UPDATE).
    pub(super) fn record_literal_facts(&mut self, slot: usize, value: &Expr) {
        if self.facts.is_opaque(slot) || self.facts.root_of(value).is_some() {
            return;
        }
        let (root, steps) = self.facts.local_root(slot);
        self.construct_facts(root, steps, value, 0);
    }
    pub(super) fn construct_facts(
        &mut self,
        root: crate::facts::Root,
        steps: Vec<crate::facts::Step>,
        value: &Expr,
        depth: usize,
    ) {
        if depth > 8 {
            return;
        }
        // A literal, or a block or one-arm match whose value is one (the
        // forms record literals and struct updates lower to).
        let construct = Self::literal_of(value);
        let ExprKind::Construct {
            enum_id, fields, ..
        } = &construct.kind
        else {
            return;
        };
        if !self.types.enums[*enum_id].record {
            return;
        }
        let types = self.types.enums[*enum_id].variants[0].fields.clone();
        let mut offset = self.types.enums[*enum_id].tag_words();
        for (field, ty) in fields.iter().zip(types) {
            let Ok(word) = u32::try_from(offset) else {
                return;
            };
            let mut path = steps.clone();
            path.push(crate::facts::Step::Field(word));
            if let Some(range) = crate::facts::scalar_range(ty) {
                if let Some(known) = self.facts.linear(field) {
                    let term = self.path_linear(root, &path, range, ty);
                    self.facts.equate(term, known);
                }
            } else {
                self.construct_facts(root, path, field, depth + 1);
            }
            offset += self.types.width(ty);
        }
    }
    /// Check an anonymous structural record literal. Fields are evaluated in
    /// source order (effects and ownership stay left-to-right) and the value is
    /// built in the canonical name-sorted row. An expected structural row is a
    /// field-type hint, and the ordinary subtype coercion then performs any
    /// width or nested representation change.
    pub(super) fn structural_literal(
        &mut self,
        fields: &[(String, ast::Expr)],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        // An expected union of structural rows is treated as a finite set of
        // candidates. Each candidate supplies field-type hints; the literal
        // must be accepted by exactly one. Committing to the first alternative
        // would silently choose a representation.
        let mut candidates = Vec::new();
        match expected {
            Some(expected) if self.types.is_structural(expected) => {
                if let Some(row) = self.types.structural_row(expected) {
                    candidates.push((expected, row));
                }
            }
            Some(Type::Union(id)) => {
                for member in self.types.unions[id].members.clone() {
                    if let Some(row) = self.types.structural_row(member) {
                        candidates.push((member, row));
                    }
                }
            }
            _ => {}
        }
        let mut accepted = Vec::new();
        let mut first_error = None;
        if candidates.len() > 1 {
            for (member, row) in &candidates {
                match self.structural_literal_fields(fields, Some(row), span) {
                    Ok((value, source)) if self.subtype(source, *member) => accepted.push(value),
                    Ok(_) => {}
                    Err(error) => {
                        if first_error.is_none() {
                            first_error = Some(error);
                        }
                    }
                }
            }
        }
        let construct = match accepted.len() {
            0 if candidates.len() > 1 => {
                // Report the first candidate's real field-type error rather
                // than an opaque union mismatch.
                if let Some(error) = first_error {
                    return Err(error);
                }
                let (_, row) = &candidates[0];
                self.structural_literal_fields(fields, Some(row), span)?.0
            }
            1 => accepted.pop().expect("one accepted literal"),
            _ if accepted.len() > 1 => {
                return Err(Diagnostic::new(
                    span,
                    "this structural record literal fits several union alternatives; add an explicit annotation",
                ));
            }
            _ => {
                let row = candidates.first().map(|(_, row)| row);
                self.structural_literal_fields(fields, row, span)?.0
            }
        };
        match expected {
            Some(expected) => self.coerce(construct, expected, span),
            None => Ok(construct),
        }
    }
    /// Build one structural literal with an optional candidate-row hint.
    pub(super) fn structural_literal_fields(
        &mut self,
        fields: &[(String, ast::Expr)],
        target_row: Option<&Vec<(String, Type)>>,
        span: Span,
    ) -> Result<(Expr, Type)> {
        let mut values = Vec::with_capacity(fields.len());
        let mut diverges = false;
        for (name, value) in fields {
            let hint = target_row
                .and_then(|row| row.iter().find(|(field, _)| field == name))
                .map(|(_, ty)| *ty);
            let value = self.expr_expected(value, hint)?;
            diverges |= value.ty == Type::Never;
            values.push((name.clone(), value));
        }
        let source_row = values
            .iter()
            .map(|(name, value)| (name.clone(), value.ty))
            .collect::<Vec<_>>();
        let ty = self.types.structural(source_row, span)?;
        let canonical = self
            .types
            .structural_row(ty)
            .expect("a checked structural literal has a structural row");
        let source = ty;
        let construct = if values
            .iter()
            .map(|(name, _)| name)
            .eq(canonical.iter().map(|(name, _)| name))
        {
            Expr {
                kind: ExprKind::Construct {
                    enum_id: ty.layout().expect("structural layout"),
                    tag: 0,
                    fields: values.into_iter().map(|(_, value)| value).collect(),
                },
                ty,
                span,
                resource: None,
            }
        } else {
            let mut statements = Vec::with_capacity(values.len());
            let mut by_name = BTreeMap::new();
            for (name, value) in values {
                let field_ty = value.ty;
                let slot = self.temp(field_ty, value.span)?;
                self.locals[slot].linear = self.value_moves_linear(&value);
                statements.push(Statement::Let(slot, value));
                by_name.insert(name, slot);
            }
            let fields = canonical
                .iter()
                .map(|(name, field_ty)| Expr {
                    kind: ExprKind::Local(by_name[name]),
                    ty: *field_ty,
                    span,
                    resource: None,
                })
                .collect();
            let tail = Expr {
                kind: ExprKind::Construct {
                    enum_id: ty.layout().expect("structural layout"),
                    tag: 0,
                    fields,
                },
                ty,
                span,
                resource: None,
            };
            Expr {
                kind: ExprKind::Block(Block {
                    statements,
                    tail: Some(Box::new(tail)),
                    ty,
                }),
                ty,
                span,
                resource: None,
            }
        };
        let type_out = if diverges { Type::Never } else { ty };
        Ok((
            Expr {
                ty: type_out,
                ..construct
            },
            source,
        ))
    }
    pub(super) fn record_pattern(
        &mut self,
        pattern: &ast::Pattern,
        fields: &[(String, ast::Pattern)],
        ty: Type,
        bindings: &mut BTreeMap<String, (usize, Type)>,
    ) -> Result<Pattern> {
        let id = self
            .resolution
            .reference(pattern.span)
            .filter(|id| self.types.is_record(*id))
            .ok_or_else(|| {
                Diagnostic::new(pattern.span, "expected a record type in this pattern")
            })?;
        let Some(layout) = ty
            .layout()
            .filter(|l| self.types.enums[*l].definition == id)
        else {
            return Err(Diagnostic::new(
                pattern.span,
                format!(
                    "record pattern does not match a value of type {}",
                    self.types.name(ty)
                ),
            ));
        };
        let variant = self.types.enums[layout].variants[0].clone();
        let mut checked = Vec::new();
        let mut offset = self.types.enums[layout].tag_words();
        for (index, field_ty) in variant.fields.iter().enumerate() {
            let sub = fields.iter().find(|(n, _)| *n == variant.names[index]);
            if let Some((name, p)) = sub {
                self.check_layout_field_visible(layout, name, p.span)?;
            }
            let p = match sub {
                Some((_, p)) => self.pattern(p, *field_ty, bindings)?,
                None => Pattern::Any,
            };
            checked.push((offset, p));
            offset += self.types.width(*field_ty);
        }
        if let Some((name, p)) = fields.iter().find(|(n, _)| !variant.names.contains(n)) {
            return Err(Diagnostic::new(
                p.span,
                format!("record has no field '{name}'"),
            ));
        }
        Ok(Pattern::Variant {
            tag: 0,
            tagged: self.types.enums[layout].tag_words() != 0,
            niche: self.types.enums[layout].niche(),
            fields: checked,
        })
    }
    /// A catch-all binding is typed by the variants not yet matched.
    pub(super) fn pattern_refined(
        &mut self,
        pattern: &ast::Pattern,
        ty: Type,
        remaining: u64,
    ) -> Result<Pattern> {
        if let Some(id) = ty.layout()
            && matches!(&pattern.kind, ast::PatternKind::Name(p) if p.len() == 1)
            && !self.is_constructor_pattern(pattern)
            && remaining & self.mask(ty) != 0
        {
            let refined =
                crate::runtime_types::refine(&self.types.enums, id, remaining & self.mask(ty));
            return self.pattern(pattern, refined, &mut BTreeMap::new());
        }
        self.pattern(pattern, ty, &mut BTreeMap::new())
    }
    /// Contextual inline-array construction. A union context selects an
    /// alternative array whose length matches the literal; an exact array
    /// context keeps the declared length so the usual mismatch error is clear.
    pub(super) fn expected_array(
        &self,
        expected: Option<Type>,
        length: usize,
    ) -> Vec<(usize, Type, usize)> {
        let candidates = |expected: Type| -> Vec<(usize, Type, usize)> {
            let Some(id) = expected.layout() else {
                return Vec::new();
            };
            let Some((element, declared)) = self.types.enums[id].array else {
                return Vec::new();
            };
            vec![(id, element, declared)]
        };
        match expected {
            Some(Type::Union(id)) => self.types.unions[id]
                .members
                .iter()
                .copied()
                .filter_map(|member| {
                    let id = member.layout()?;
                    let (element, declared) = self.types.enums[id].array?;
                    (declared == length).then_some((id, element, declared))
                })
                .collect(),
            Some(expected) => candidates(expected),
            None => Vec::new(),
        }
    }
    pub(super) fn vec_literal(
        &mut self,
        values: &[ast::Expr],
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let candidates = match expected {
            Some(Type::Vec(p)) => vec![self.types.pointees[p]],
            Some(Type::Union(id)) => {
                let mut elements = Vec::new();
                for member in self.types.unions[id].members.iter() {
                    if let Type::Vec(p) = member
                        && !elements.contains(&self.types.pointees[*p])
                    {
                        elements.push(self.types.pointees[*p]);
                    }
                }
                elements
            }
            _ => Vec::new(),
        };
        if values.len() > 4096 {
            return Err(Diagnostic::new(
                span,
                "vector literals are limited to 4096 elements",
            ));
        }
        self.require(ALLOC | PANIC, span)?;
        let mut element = match candidates.len() {
            0 => None,
            1 => Some(candidates[0]),
            _ => {
                // Accumulate element constraints over every union
                // alternative; the literal must identify exactly one.
                let mut accepted = Vec::new();
                let mut first_error = None;
                for candidate in &candidates {
                    let mut checked = Vec::with_capacity(values.len());
                    let mut failed = None;
                    for value in values {
                        match self.expr_expected(value, Some(*candidate)) {
                            Ok(value) => checked.push(value),
                            Err(error) => {
                                failed = Some(error);
                                break;
                            }
                        }
                    }
                    if failed.is_none() {
                        accepted.push((*candidate, checked));
                    } else if first_error.is_none() {
                        first_error = failed;
                    }
                }
                let (element, checked) = match accepted.len() {
                    1 => accepted.pop().expect("one accepted vector element"),
                    0 => {
                        return Err(first_error
                            .expect("a vector literal candidate always attempts one element"));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            span,
                            "this vector literal fits several union alternatives; annotate the element type or write Vec::<T>::new",
                        ));
                    }
                };
                let ty = Type::Vec(self.types.pointer(element));
                let mut current = Expr {
                    kind: ExprKind::Call(
                        Target::Vec(VecOp::WithCapacity, element),
                        vec![Expr {
                            kind: ExprKind::Constant(values.len() as i64),
                            ty: Type::I64,
                            span,
                            resource: None,
                        }],
                    ),
                    ty,
                    span,
                    resource: None,
                };
                for value in checked {
                    self.expect(value.ty, element, value.span)?;
                    let diverges = value.ty == Type::Never;
                    current = Expr {
                        kind: ExprKind::Call(
                            Target::Vec(VecOp::Push, element),
                            vec![current, value],
                        ),
                        ty: if diverges { Type::Never } else { ty },
                        span,
                        resource: None,
                    };
                }
                return match expected {
                    Some(expected) => self.coerce(current, expected, span),
                    None => Ok(current),
                };
            }
        };
        let mut checked = Vec::new();
        for value in values {
            let value = self.expr_expected(value, element)?;
            if element.is_none() && value.ty != Type::Never {
                element = Some(self.types.full(value.ty, span)?);
            }
            checked.push(value);
        }
        let Some(element) = element else {
            return Err(Diagnostic::new(
                span,
                "cannot infer the element type of an empty vector; annotate it: let v: Vec<T> = [];",
            ));
        };
        if matches!(element, Type::RefMut(_) | Type::Never)
            || matches!(element, Type::Annotated(_, _) if matches!(self.unannotate(element), Type::RefMut(_)))
            || (element.is_view() && element.is_mut_slice())
        {
            return Err(Diagnostic::new(
                span,
                "vectors cannot store exclusive references or mutable slice views; a vector read copies its element, so an exclusive reference element is not admitted",
            ));
        }
        let ty = Type::Vec(self.types.pointer(element));
        let mut current = Expr {
            kind: ExprKind::Call(
                Target::Vec(VecOp::WithCapacity, element),
                vec![Expr {
                    kind: ExprKind::Constant(values.len() as i64),
                    ty: Type::I64,
                    span,
                    resource: None,
                }],
            ),
            ty,
            span,
            resource: None,
        };
        for value in checked {
            self.expect(value.ty, element, value.span)?;
            let diverges = value.ty == Type::Never;
            current = Expr {
                kind: ExprKind::Call(Target::Vec(VecOp::Push, element), vec![current, value]),
                ty: if diverges { Type::Never } else { ty },
                span,
                resource: None,
            };
        }
        match expected {
            Some(expected) => self.coerce(current, expected, span),
            None => Ok(current),
        }
    }
    /// A compile-time nonnegative index in a range endpoint, when it is one.
    /// This reuses the same checked natural evaluator as array indices, so
    /// const parameters and admitted total logical computations are folded and
    /// negative or overflowing constants are rejected.
    pub(super) fn constant_bound(&self, expr: &ast::Expr) -> Option<Result<usize>> {
        match crate::length::eval_expr(self.resolution, self.logical, &self.consts, expr) {
            Ok(Some(value)) => Some(Ok(value)),
            Ok(None) => None,
            Err(error) => Some(Err(error)),
        }
    }
}
