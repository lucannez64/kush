//! Lambdas, their inference, closures, function values and indirect calls.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    pub(super) fn lambda(
        &mut self,
        lambda: &ast::Lambda,
        span: Span,
        expected: Option<Type>,
        context: LambdaContext,
    ) -> Result<Expr> {
        let scope_root = context == LambdaContext::TaskScope;
        let quotation = context == LambdaContext::Quotation;
        let captures = self.lambda_captures(lambda, quotation);
        // EFF-CAP-LAMBDA: a lambda may capture a capability whose handler
        // runs in place. The closure is then a scoped borrow of it, checked
        // like a borrowed-capture closure (ownership and suspension rules).
        if captures.iter().any(|slot| {
            self.capability_slots.contains(slot)
                && (!self.capability_passable.contains(slot)
                    || self.capability_parameter_slots.contains(slot))
        }) {
            return Err(Diagnostic::new(
                span,
                "a lambda can only capture a capability bound by a 'handle' in this function whose handler runs in place (noncapturing, one-shot, tail-resumptive); a 'cap' parameter may be bound to a handler with code after 'resume'. Perform it directly or pass it to a function with a 'cap' parameter",
            ));
        }
        let capability_captures = (0..captures.len())
            .filter(|index| self.capability_slots.contains(&captures[*index]))
            .collect::<Vec<_>>();
        let once = !captures.is_empty();
        let inference = self.prepare_lambda_inference(lambda, span, expected)?;
        // A mutable scalar capture is a live view: the environment stores the
        // address of the caller's binding, not a copy. Immutable scalars keep
        // their existing by-value snapshot contract, and affine/borrowed
        // captures keep their existing owning/capability representation.
        let capture_refs = captures
            .iter()
            .map(|slot| {
                let local = self.locals[*slot];
                local.mutable && !local.linear && local.grade.is_none() && is_live_scalar(local.ty)
            })
            .collect::<Vec<_>>();
        if once && matches!(expected, Some(Type::Fn(_))) {
            return Err(Diagnostic::new(
                span,
                "a capturing lambda has an owned environment and must be used as 'once fn(...)'; it cannot be a copyable 'fn(...)' value",
            ));
        }
        let mut capture_linear = false;
        if let Some(slot) = captures
            .iter()
            .find(|slot| self.locals[**slot].ty.is_text())
        {
            return Err(Diagnostic::new(
                span,
                "a lambda or task cannot capture a borrowed '&str' text view; call a named function with an explicit lifetime instead",
            )
            .with_note(self.locals[*slot].span, "text view declared here"));
        }
        let borrowed_capture = capture_refs.iter().any(|by_ref| *by_ref)
            || captures.iter().any(|slot| {
                self.locals[*slot].ty.is_slice()
                    || self.locals[*slot].ty.is_ref()
                    || self.carrier_type(self.locals[*slot].ty)
                    || crate::runtime_types::is_reference_container(
                        self.types,
                        self.locals[*slot].ty,
                    )
            });
        for (capture_index, slot) in captures.iter().enumerate() {
            let local = self.locals[*slot];
            let ty = local.ty;
            if capture_refs[capture_index] {
                self.locals[*slot].pinned = true;
            }
            if crate::runtime_types::contains_task_exit_borrow(self.types, ty) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda or task cannot capture TaskExit<T> with a borrowed payload; match it inside the scope that joined it",
                )
                .with_note(local.span, "joined borrowed result declared here"));
            }
            if self.parameter_lengths.contains_key(slot) && matches!(ty, Type::RefMut(_)) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda cannot capture a parameter that keeps 'len >= N'; the closure could shorten it",
                )
                .with_note(self.locals[*slot].span, "refined parameter declared here"));
            }
            if matches!(ty, Type::Task(_) | Type::Thread(_)) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda cannot capture a task handle; join it in the scope that owns it",
                )
                .with_note(self.locals[*slot].span, "task handle declared here"));
            }
            if local.grade.is_some_and(Grade::is_zero) {
                return Err(Diagnostic::new(
                    span,
                    "a lambda cannot capture a value graded @[0]; grade zero forbids every observation, including moving it into a closure environment",
                )
                .with_note(local.span, "grade @[0] binding declared here"));
            }
            if let Some(grade) = local.grade
                && !grade.is_one()
                && !grade.is_zero()
                && !grade.is_many()
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "a lambda cannot capture a value graded @[{grade}]; a closure may be called zero or one time, so the exact use obligation cannot be transferred. Leave the value ungraded or observe it before constructing the closure"
                    ),
                )
                .with_note(local.span, "graded binding declared here"));
            }
            if local.linear || local.grade.is_some_and(Grade::is_one) || self.linear_type(ty) {
                capture_linear = true;
            }
        }
        let linear = once && capture_linear;
        if linear
            && matches!(expected, Some(Type::Once(id)) if !self.types.function_types[id].linear)
        {
            return Err(Diagnostic::new(
                span,
                "a lambda capturing linear obligations must be used as 'linear once fn(...)'; widening it to an affine 'once fn(...)' would allow an uncalled closure to drop those obligations",
            ));
        }
        if once {
            self.require(ALLOC | PANIC, span)?;
        }
        let mut parameters = Vec::with_capacity(lambda.parameters.len());
        let mut parameter_grades = Vec::with_capacity(lambda.parameters.len());
        for parameter in &lambda.parameters {
            if parameter.erased {
                return Err(Diagnostic::new(
                    parameter.span,
                    "lambda parameters cannot be erased proof parameters; function values have no erased argument list",
                ));
            }
            let (inner, grade) = split_grade(&parameter.ty);
            let grade = grade
                .map(|grade| grades::evaluate(self.resolution, &self.grades, grade))
                .transpose()?;
            let ty = self.ty(inner)?;
            self.reject_lambda_runtime_length(ty, parameter.ty.span)?;
            // Slice parameters have independent lifetimes. A lambda may also
            // take a record with borrowed slice fields by value; its per-field
            // contract travels in the callable's borrow signature.
            if !ty.is_slice()
                && !ty.is_ref()
                && !crate::runtime_types::is_borrowed_record(self.types, ty)
                && !crate::runtime_types::is_reference_container(self.types, ty)
                && !crate::runtime_types::is_borrowed_task_exit(self.types, ty)
                && crate::runtime_types::has_borrow(self.types, ty)
            {
                return Err(Diagnostic::new(
                    parameter.ty.span,
                    "a function value cannot take an owner reference or &str text-view parameter; references, slice views, reference containers, and records with borrowed fields are supported",
                ));
            }
            self.validate_grade(grade, ty, parameter.ty.span, false)?;
            parameters.push(ty);
            parameter_grades.push(grade);
        }
        let (result_inner, result_grade) =
            result_contract(self.resolution, self.types, &self.grades, &lambda.result)?;
        // An inferred result is fixed by the body below; until then it is an
        // inert placeholder that no pre-body check depends on.
        let mut result = if inference.result_from_body {
            Type::Unit
        } else {
            self.ty(&result_inner)?
        };
        self.reject_lambda_runtime_length(result, lambda.result.span)?;
        validate_result_contract(
            result_grade,
            self.owned_type(result),
            &self.types.name(result),
            lambda.result.span,
        )?;
        if result.is_view() && !result.is_slice() {
            return Err(Diagnostic::new(
                lambda.result.span,
                "a lambda cannot return a borrowed '&str' text view; use a named function or a slice view",
            ));
        }
        if crate::runtime_types::contains_task(self.types, result) {
            return Err(Diagnostic::new(
                lambda.result.span,
                "a function value cannot return a task handle; a child handle must not escape its scope",
            ));
        }
        let mut effects = match inference.row {
            LambdaRow::Declared => crate::runtime_types::effect_bits_with(
                self.resolution,
                &lambda.effects,
                &self.effect_arguments,
            )?,
            LambdaRow::Fixed(bits) => bits,
            LambdaRow::FromBody => self.all_effects(),
        };
        let lambda_lifetimes = parameters
            .iter()
            .enumerate()
            .map(|(index, ty)| (ty.is_slice() || ty.is_ref()).then(|| format!("<lambda {index}>")))
            .collect::<Vec<_>>();
        let capture_lifetimes = captures
            .iter()
            .enumerate()
            .map(|(index, slot)| {
                self.locals[*slot].ty.is_slice().then(|| {
                    self.parameter_lifetimes
                        .get(*slot)
                        .cloned()
                        .flatten()
                        .unwrap_or_else(|| format!("<lambda capture {index}>"))
                })
            })
            .collect::<Vec<_>>();
        let parameter_leaves = parameters
            .iter()
            .map(|ty| {
                if crate::runtime_types::is_borrowed_record(self.types, *ty)
                    || crate::runtime_types::is_reference_container(self.types, *ty)
                    || crate::runtime_types::is_borrowed_task_exit(self.types, *ty)
                {
                    crate::runtime_types::borrow_leaves(self.types, *ty)
                } else {
                    crate::runtime_types::reference_referent_leaves(self.types, *ty)
                }
            })
            .collect::<Result<Vec<_>>>()?;
        // Labels available from call parameters and from the closure
        // environment. Ambiguity between these origins is rejected: a scoped
        // capture result is only expressible when exactly one capture supplies
        // it, and a parameter result must stay on the parameter contract.
        let parameter_slice_mutability = lambda_lifetimes
            .iter()
            .enumerate()
            .filter_map(|(index, label)| {
                label.as_ref().map(|label| {
                    (
                        label.clone(),
                        parameters[index].is_mut_slice()
                            || matches!(parameters[index], Type::RefMut(_)),
                    )
                })
            })
            .collect::<BTreeMap<_, _>>();
        let mut parameter_leaf_labels: BTreeMap<String, bool> = BTreeMap::new();
        for leaves in &parameter_leaves {
            for leaf in leaves {
                if let Some(label) = &leaf.lifetime {
                    parameter_leaf_labels
                        .entry(label.clone())
                        .and_modify(|mutable| *mutable |= leaf.mutable)
                        .or_insert(leaf.mutable);
                }
            }
        }
        let capture_slice_labels = capture_lifetimes
            .iter()
            .enumerate()
            .filter_map(|(index, label)| {
                label.as_ref().and_then(|label| {
                    self.locals[captures[index]]
                        .ty
                        .is_slice()
                        .then(|| (label.clone(), index))
                })
            })
            .collect::<BTreeMap<_, _>>();
        let mut capture_leaf_labels: BTreeMap<String, Vec<(usize, Vec<usize>, bool)>> =
            BTreeMap::new();
        for (index, slot) in captures.iter().enumerate() {
            let ty = self.locals[*slot].ty;
            if !crate::runtime_types::is_borrowed_record(self.types, ty) {
                continue;
            }
            for leaf in crate::runtime_types::borrow_leaves(self.types, ty)? {
                if let Some(label) = &leaf.lifetime {
                    capture_leaf_labels.entry(label.clone()).or_default().push((
                        index,
                        leaf.path,
                        leaf.mutable,
                    ));
                }
            }
        }
        let mut candidates = Vec::new();
        candidates.extend(parameter_slice_mutability.keys().cloned());
        candidates.extend(parameter_leaf_labels.keys().cloned());
        candidates.extend(capture_slice_labels.keys().cloned());
        candidates.extend(capture_leaf_labels.keys().cloned());
        candidates.sort();
        candidates.dedup();
        let mut lambda_result_lifetime = None;
        let mut borrow_result_lifetime = None;
        crate::runtime_types::reject_optional_reference_boundary(
            self.types,
            result,
            lambda.result.span,
        )?;
        let mut borrow_result_leaves: Vec<crate::runtime_types::BorrowLeaf> = Vec::new();
        let mut capture_result = crate::runtime_types::CaptureResultSig::default();
        let mut capture_result_used = false;
        if result.is_slice() {
            let explicit = borrow_lifetime(&lambda.result);
            if !once
                && (explicit.is_some()
                    || lambda
                        .parameters
                        .iter()
                        .any(|parameter| borrow_lifetime(&parameter.ty).is_some()))
            {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "slice-returning lambdas use lifetime elision; use a named function for explicit lifetime binders",
                ));
            }
            let lifetime = match explicit {
                Some(name) => {
                    if !candidates.contains(&name) {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            format!(
                                "the lambda result lifetime '{name}' does not appear on a borrowed parameter, captured view, or captured record field; a lambda cannot return a borrow for an outer lifetime it does not receive"
                            ),
                        ));
                    }
                    name
                }
                None => match candidates.as_slice() {
                    [only] => only.clone(),
                    [] => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "a slice-returning lambda needs exactly one borrowed parameter, captured view, or captured record field to borrow from",
                        ));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "cannot infer this lambda result's lifetime from several borrowed parameters or captures; a scoped callable result must have exactly one possible origin",
                        ));
                    }
                },
            };
            let mut parameter_sources = Vec::new();
            if let Some(mutable) = parameter_slice_mutability.get(&lifetime) {
                parameter_sources.push(*mutable);
            }
            if let Some(mutable) = parameter_leaf_labels.get(&lifetime) {
                parameter_sources.push(*mutable);
            }
            let mut capture_sources = Vec::new();
            if let Some(index) = capture_slice_labels.get(&lifetime) {
                let mutable = self.locals[captures[*index]].ty.is_mut_slice();
                capture_sources.push((*index, None, mutable));
            }
            if let Some(leaves) = capture_leaf_labels.get(&lifetime) {
                capture_sources.extend(
                    leaves
                        .iter()
                        .map(|(capture, path, mutable)| (*capture, Some(path.clone()), *mutable)),
                );
            }
            if !parameter_sources.is_empty() && !capture_sources.is_empty() {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "this lambda result borrows from both a call parameter and a captured view; a scoped capture result and a parameter result cannot be mixed or unified",
                ));
            }
            if capture_sources.is_empty() {
                if parameter_sources.is_empty() {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "the lambda result lifetime '{lifetime}' is not outlived by any borrowed parameter, so no call could produce it"
                        ),
                    ));
                }
                if result.is_mut_slice() && !parameter_sources.iter().any(|mutable| *mutable) {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "an exclusive slice result requires an exclusive slice parameter or exclusive record field",
                    ));
                }
                lambda_result_lifetime = Some(lifetime.clone());
                borrow_result_lifetime = Some(lifetime);
            } else {
                let [(capture, path, mutable)] = capture_sources.as_slice() else {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "cannot infer this lambda result's capture origin: several captured views or record fields carry the same lifetime",
                    ));
                };
                if result.is_mut_slice() && !*mutable {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "an exclusive slice result cannot be borrowed from a shared captured view or shared captured record field",
                    ));
                }
                capture_result.slice = Some(crate::runtime_types::CaptureSliceSig {
                    capture: *capture,
                    path: path.clone(),
                    mutable: *mutable,
                });
                capture_result_used = true;
                // The child function still needs the declared result lifetime
                // for its own return check; the callable's visible result
                // lifetime stays empty because the environment is the source.
                lambda_result_lifetime = Some(lifetime);
            }
        } else if result.is_ref() {
            let explicit = borrow_lifetime(&lambda.result);
            let lifetime = match explicit {
                Some(name) => {
                    if !candidates.contains(&name) {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            format!(
                                "the lambda result lifetime '{name}' does not appear on a reference parameter, borrowed container, or borrowed record field"
                            ),
                        ));
                    }
                    name
                }
                None => match candidates.as_slice() {
                    [only] => only.clone(),
                    [] => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "a reference-returning lambda needs exactly one borrowed parameter, container, or record field to borrow from",
                        ));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "cannot infer this lambda reference result's lifetime from several borrowed inputs; use a named function or an explicit result lifetime",
                        ));
                    }
                },
            };
            if capture_slice_labels.contains_key(&lifetime)
                || capture_leaf_labels.contains_key(&lifetime)
            {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "a lambda cannot return a reference borrowed from a captured local or capture environment; derive the reference from a call parameter instead",
                ));
            }
            let parameter_mutability = parameter_slice_mutability
                .get(&lifetime)
                .copied()
                .into_iter()
                .chain(parameter_leaf_labels.get(&lifetime).copied());
            let sources = parameter_mutability.clone().collect::<Vec<_>>();
            if sources.is_empty() {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "the lambda reference result is not outlived by any reference parameter or borrowed field",
                ));
            }
            if matches!(result, Type::RefMut(_)) && !sources.iter().any(|mutable| *mutable) {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "an exclusive reference result requires an exclusive reference parameter or exclusive borrowed field",
                ));
            }
            lambda_result_lifetime = Some(lifetime.clone());
            borrow_result_lifetime = Some(lifetime);
        } else if crate::runtime_types::is_borrowed_record(self.types, result)
            || crate::runtime_types::is_reference_container(self.types, result)
            || crate::runtime_types::is_borrowed_task_exit(self.types, result)
        {
            let leaves = crate::runtime_types::borrow_leaves(self.types, result)?;
            let mut parameter_leaves = Vec::new();
            let mut capture_leaves = Vec::new();
            let slice_captures = capture_slice_labels.values().copied().collect::<Vec<_>>();
            for leaf in leaves {
                let Some(label) = &leaf.lifetime else {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "internal error: borrowed lambda result leaf has no lifetime",
                    ));
                };
                let parameter_source = parameter_leaf_labels
                    .get(label)
                    .copied()
                    .or_else(|| parameter_slice_mutability.get(label).copied());
                let capture_sources = capture_leaf_labels.get(label);
                let capture_slice_source = capture_slice_labels.get(label).copied().or_else(|| {
                    (slice_captures.len() == 1 && capture_sources.is_none())
                        .then(|| slice_captures[0])
                });
                if parameter_source.is_some()
                    && (capture_sources.is_some() || capture_slice_source.is_some())
                {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "the lambda result field lifetime '{label}' has both a call-parameter and a captured origin; the two cannot be unified"
                        ),
                    ));
                }
                if let Some(mutable) = parameter_source {
                    if leaf.mutable && !mutable {
                        return Err(Diagnostic::new(
                            lambda.result.span,
                            "an exclusive result field requires an exclusive borrowed parameter field",
                        ));
                    }
                    parameter_leaves.push(leaf);
                    continue;
                }
                let Some(sources) = capture_sources else {
                    if let Some(capture) = capture_slice_source {
                        // A payload slice field may be built directly from a
                        // captured slice view of the same declared lifetime.
                        let mutable = self.locals[captures[capture]].ty.is_mut_slice();
                        if leaf.mutable && !mutable {
                            return Err(Diagnostic::new(
                                lambda.result.span,
                                "an exclusive result field cannot be borrowed from a shared captured slice view",
                            ));
                        }
                        capture_leaves.push(crate::runtime_types::CaptureLeafSig {
                            path: leaf.path,
                            capture,
                            mutable,
                        });
                        continue;
                    }
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "the lambda result field lifetime '{label}' is not outlived by any borrowed parameter or captured record field"
                        ),
                    ));
                };
                let matching = sources
                    .iter()
                    .filter(|(_, path, _)| *path == leaf.path)
                    .collect::<Vec<_>>();
                let [(capture, _, mutable)] = matching.as_slice() else {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        format!(
                            "cannot infer this lambda result field's capture origin: field path {:?} is not supplied by exactly one captured record",
                            leaf.path
                        ),
                    ));
                };
                if leaf.mutable && !*mutable {
                    return Err(Diagnostic::new(
                        lambda.result.span,
                        "an exclusive result field cannot be borrowed from a shared captured record field",
                    ));
                }
                capture_leaves.push(crate::runtime_types::CaptureLeafSig {
                    path: leaf.path,
                    capture: *capture,
                    mutable: *mutable,
                });
            }
            if !capture_leaves.is_empty() && !parameter_leaves.is_empty() {
                return Err(Diagnostic::new(
                    lambda.result.span,
                    "this lambda returns a record mixing captured and call-parameter borrows; split the record or return one origin at a time",
                ));
            }
            if capture_leaves.is_empty() {
                borrow_result_leaves = parameter_leaves;
            } else {
                capture_result.leaves = capture_leaves;
                capture_result_used = true;
            }
        }
        let mut borrows = crate::runtime_types::BorrowSig::canonical_with_leaves(
            &lambda_lifetimes,
            borrow_result_lifetime.as_ref(),
            &parameter_leaves,
            &borrow_result_leaves,
            &BTreeSet::new(),
        );
        if capture_result_used {
            borrows.capture_result = Some(capture_result);
        }
        let capture_types = captures
            .iter()
            .map(|slot| self.locals[*slot].ty)
            .collect::<Vec<_>>();
        let capture_obligations = captures
            .iter()
            .map(|slot| {
                let local = self.locals[*slot];
                (
                    local.grade,
                    local.linear
                        || local.grade.is_some_and(Grade::is_one)
                        || self.linear_type(local.ty),
                )
            })
            .collect::<Vec<_>>();
        let capture_exprs = captures
            .iter()
            .map(|&slot| {
                let local = self.locals[slot];
                // Each closure owns its copy. The template's constant stays
                // available after this closure has been called or dropped.
                if !quotation
                    && matches!(local.ty, Type::Bytes | Type::String)
                    && self.quote_holes.values().any(|hole| *hole == slot)
                {
                    self.copy_lifted_text(slot, local.span)
                } else {
                    Expr {
                        kind: ExprKind::Local(slot),
                        ty: local.ty,
                        span: local.span,
                        resource: None,
                    }
                }
            })
            .collect::<Vec<_>>();
        // Check the lambda body in a fresh function context. A by-reference
        // scalar capture is writable inside the body; whether it actually is
        // written decides the shared/exclusive loan and proof invalidation.
        let capture_body_mutable = capture_refs.clone();
        let saved_quote_holes = self.quote_holes.clone();
        self.quote_holes = self
            .quote_holes
            .iter()
            .filter_map(|(span, slot)| {
                captures
                    .iter()
                    .position(|capture| capture == slot)
                    .map(|index| (*span, index))
            })
            .collect();
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_capabilities = std::mem::take(&mut self.capability_slots);
        let saved_passable = std::mem::take(&mut self.capability_passable);
        let saved_resumable = std::mem::take(&mut self.capability_resumable);
        let saved_framed = std::mem::take(&mut self.capability_framed);
        let saved_cap_parameters = std::mem::take(&mut self.capability_parameter_slots);
        let saved_slots = std::mem::take(&mut self.slots);
        let saved_result = self.result;
        let saved_parameter_lifetimes = std::mem::take(&mut self.parameter_lifetimes);
        let saved_declared_lifetimes = std::mem::take(&mut self.declared_lifetimes);
        let saved_result_grade = self.result_grade;
        let saved_effects = self.effects;
        let saved_loops = std::mem::take(&mut self.loops);
        let saved_facts = std::mem::take(&mut self.facts);
        let saved_written = std::mem::take(&mut self.written_slots);
        let saved_closure_writes = std::mem::take(&mut self.closure_writes);
        let saved_closure_captures = std::mem::take(&mut self.closure_captures);
        let saved_parameter_lengths = std::mem::take(&mut self.parameter_lengths);
        let capture_ids = captures
            .iter()
            .map(|slot| {
                saved_slots
                    .iter()
                    .find(|(_, outer)| *outer == slot)
                    .map(|(id, _)| *id)
            })
            .collect::<Vec<_>>();
        let kernel_mark = self.kernel_locals.len();
        let saved_scope_depth = self.scope_depth;
        let saved_scope_parallel = self.scope_parallel;
        // A handler is lexical to direct performs in the enclosing function
        // body, never to indirect calls. A lambda is a separate callable, so it
        // cannot capture the hidden handler local by name.
        let saved_handlers = std::mem::take(&mut self.handlers);
        let saved_ensures = self.ensures_context.take();
        let saved_ensures_tail = std::mem::take(&mut self.ensures_tail);
        let saved_branch_tail = std::mem::take(&mut self.branch_tail);
        let mut child_parameter_lifetimes = capture_lifetimes.clone();
        child_parameter_lifetimes.extend(lambda_lifetimes.clone());
        let saved_required = self.required_effects.replace(0);
        let checked = (|| {
            self.scope_depth = if scope_root { saved_scope_depth + 1 } else { 0 };
            self.scope_parallel = scope_root && self.next_scope_parallel;
            self.parameter_lifetimes = child_parameter_lifetimes.clone();
            for ((ty, (grade, linear)), mutable) in capture_types
                .iter()
                .zip(&capture_obligations)
                .zip(capture_body_mutable.iter())
            {
                self.locals.push(Local {
                    ty: *ty,
                    mutable: *mutable,
                    linear: *linear,
                    pinned: *mutable,
                    grade: *grade,
                    span,
                });
            }
            // Rebuild the binder map for captures from the outer checker.
            let mut capture_binders = BTreeMap::new();
            for (id, outer_slot) in &saved_slots {
                if let Some(position) = captures.iter().position(|slot| slot == outer_slot) {
                    capture_binders.insert(*id, position);
                }
            }
            self.slots = capture_binders;
            // A captured capability stays second-class inside the body.
            for index in &capability_captures {
                self.capability_slots.insert(*index);
                self.capability_passable.insert(*index);
            }
            // A by-reference scalar may also be captured, and written, by
            // other closures (several handlers sharing a counter), and any
            // call in the body may run one of them: no fact about it holds
            // across the body.
            for (index, by_ref) in capture_refs.iter().enumerate() {
                if *by_ref {
                    self.facts.make_opaque(index);
                }
            }
            // Captured scalars are symbolic indices in the body. A by-value
            // snapshot is frozen at construction; a by-reference mutable
            // capture is a versioned local whose assignment appends a fresh
            // binder exactly like any other mutable scalar.
            for (id, ty) in capture_ids.iter().zip(capture_types.iter()) {
                if let Some(id) = id {
                    self.admit_scalar_index(*id, *ty, Span::default())?;
                }
            }
            for (parameter, ty) in lambda.parameters.iter().zip(&parameters) {
                let slot = self.bind(parameter.span, *ty, false)?;
                self.locals[slot].grade = parameter_grades[slot - captures.len()];
                self.locals[slot].linear = parameter_grades[slot - captures.len()]
                    .is_some_and(Grade::is_one)
                    && self.owned_type(*ty);
                let id = self.resolution.binder(parameter.span).unwrap();
                self.admit_scalar_index(id, *ty, parameter.span)?;
            }
            self.result = result;
            self.result_grade = result_grade;
            self.effects = effects;
            self.loops.clear();
            self.facts = crate::facts::Facts::default();
            let body = if inference.result_from_body {
                self.block(&lambda.body, None)?
            } else {
                let body = self.block(&lambda.body, Some(result))?;
                self.expect(body.ty, result, span)?;
                body
            };
            if body.ty != Type::Never
                && let Some(tail) = &body.tail
                && self.observes_copyable_result(tail)
                && !self.transfers_copyable_result_from(tail)
            {
                return Err(Diagnostic::new(
                    tail.span,
                    "this lambda returns a copyable result with the must-use `@[1]` contract through an ungraded result; annotate the result as '@[1]' so every caller inherits exactly one observation, or observe the value inside the lambda",
                ));
            }
            // The lambda's own locals are in scope here, so the result-transfer
            // obligation is derived before restoring the outer checker state.
            let obligation = self.return_obligation(&body);
            let written = self.written_slots.clone();
            Ok((body, obligation, written))
        })();
        self.truncate_kernel(kernel_mark);
        self.scope_depth = saved_scope_depth;
        self.scope_parallel = saved_scope_parallel;
        self.handlers = saved_handlers;
        self.ensures_context = saved_ensures;
        self.ensures_tail = saved_ensures_tail;
        self.branch_tail = saved_branch_tail;
        let locals = std::mem::take(&mut self.locals);
        self.locals = saved_locals;
        self.quote_holes = saved_quote_holes;
        self.capability_slots = saved_capabilities;
        self.capability_passable = saved_passable;
        self.capability_resumable = saved_resumable;
        self.capability_framed = saved_framed;
        self.capability_parameter_slots = saved_cap_parameters;
        self.slots = saved_slots;
        self.result = saved_result;
        self.parameter_lifetimes = saved_parameter_lifetimes;
        self.declared_lifetimes = saved_declared_lifetimes;
        self.result_grade = saved_result_grade;
        self.effects = saved_effects;
        self.loops = saved_loops;
        self.facts = saved_facts;
        self.written_slots = saved_written;
        self.closure_writes = saved_closure_writes;
        self.parameter_lengths = saved_parameter_lengths;
        self.closure_captures = saved_closure_captures;
        let body_required = self.required_effects.replace(saved_required);
        let (body, obligation, written) = checked?;
        if inference.result_from_body {
            result = self.inferred_lambda_result(body.ty, span)?;
        }
        if matches!(inference.row, LambdaRow::FromBody) {
            effects = body_required & self.all_effects();
        }
        let function_type = self.types.function_type_with(
            parameters.clone(),
            result,
            effects,
            parameter_grades.clone(),
            result_grade,
            once,
            linear,
            borrows,
        );
        let capture_writes = (0..captures.len())
            .map(|index| written.contains(&index))
            .collect::<Vec<_>>();
        if let Some(span) = obligation
            && result_grade.is_none()
            && !self.linear_type(result)
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "this lambda returns a linear obligation through an ungraded result; annotate the result as '-> {} @[1]' so every caller must consume it, or consume the value inside the lambda",
                    self.types.name(result)
                ),
            ));
        }
        let mut grades = vec![None; captures.len()];
        grades.extend(parameter_grades.iter().copied());
        let name = if once { "once lambda" } else { "lambda" };
        let signature = Signature {
            call_contract: None,
            binding: usize::MAX,
            name: name.to_owned(),
            parameters,
            result,
            effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades: parameter_grades.clone(),
            result_grade,
            parameter_lifetimes: lambda_lifetimes.clone(),
            result_lifetime: lambda_result_lifetime.clone(),
            lifetime_bounds: BTreeSet::new(),
            self_type: None,
            default_trait: None,
            associated_consts: BTreeMap::new(),
        };
        let (local_borrowed, local_copyable) = self.local_classes(&locals);
        let function = Function {
            name: name.to_owned(),
            parameters: captures.len() + lambda.parameters.len(),
            closure: once.then_some(captures.len()),
            capture_refs: capture_refs.clone(),
            capture_writes,
            locals,
            result,
            body,
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: grades,
            result_grade,
            parameter_lifetimes: {
                let mut lifetimes = capture_lifetimes.clone();
                lifetimes.extend(lambda_lifetimes);
                lifetimes
            },
            result_lifetime: lambda_result_lifetime,
            lifetime_bounds: BTreeSet::new(),
            declared_lifetimes: BTreeSet::new(),
            index_relations: self.index_relations.clone(),
            parameter_slots: None,
            local_borrowed,
            local_copyable,
            capability_parameters: capability_captures.clone(),
            shared_environment: false,
        };
        let index = self.functions.add_synthetic(signature, function)?;
        let ty = if once {
            Type::Once(function_type)
        } else {
            Type::Fn(function_type)
        };
        let value = Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: capture_exprs,
            },
            ty,
            span,
            resource: None,
        };
        if borrowed_capture
            && expected.is_some_and(|expected| expected != ty)
            && !expected.is_some_and(|expected| matches!(expected, Type::Once(_)))
        {
            return Err(Diagnostic::new(
                span,
                "a lambda with borrowed slice captures cannot be coerced to a union or non-once function type; call it directly or bind it with its exact 'once fn(...)' type",
            ));
        }
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Fill the omitted annotations of `lambda` (I-LAMBDA-INFER) from the
    /// expected arrow or the pending hint, and decide how its result and row
    /// are inferred. Inferred types are Direct Kush types: no borrowed
    /// parameter, no union or borrowed result, no grade.
    pub(super) fn prepare_lambda_inference(
        &mut self,
        lambda: &ast::Lambda,
        span: Span,
        expected: Option<Type>,
    ) -> Result<LambdaInference> {
        let hint = self.lambda_hint.take().unwrap_or_default();
        let row_hole = matches!(lambda.effects.as_slice(), [only] if matches!(only.kind, ast::TypeKind::Infer));
        let result_hole = matches!(lambda.result.kind, ast::TypeKind::Infer);
        let parameter_hole = lambda
            .parameters
            .iter()
            .any(|parameter| matches!(parameter.ty.kind, ast::TypeKind::Infer));
        if !row_hole && !result_hole && !parameter_hole {
            return Ok(LambdaInference {
                result_from_body: false,
                row: LambdaRow::Declared,
            });
        }
        let arrow = match expected {
            Some(Type::Fn(id) | Type::Once(id)) => Some(self.types.function_types[id].clone()),
            _ => None,
        }
        .filter(|arrow| arrow.parameters.len() == lambda.parameters.len());
        for (index, parameter) in lambda.parameters.iter().enumerate() {
            if !matches!(parameter.ty.kind, ast::TypeKind::Infer) {
                continue;
            }
            let Some(ty) = hint
                .parameters
                .get(index)
                .copied()
                .flatten()
                .or_else(|| arrow.as_ref().map(|arrow| arrow.parameters[index]))
            else {
                return Err(Diagnostic::new(
                    parameter.span,
                    format!(
                        "cannot infer the type of lambda parameter '{}': no expected function type, generic call, or first use fixes it; annotate it as '{}: T'",
                        parameter.name, parameter.name
                    ),
                ));
            };
            if ty == Type::Never
                || ty.is_view()
                || ty.is_slice()
                || ty.is_ref()
                || crate::runtime_types::has_borrow(self.types, ty)
                || crate::runtime_types::contains_task(self.types, ty)
            {
                return Err(Diagnostic::new(
                    parameter.span,
                    format!(
                        "lambda parameter '{}' would be inferred as {}; borrowed, task and uninhabited parameter types are not inferred, annotate it",
                        parameter.name,
                        self.types.name(ty)
                    ),
                ));
            }
            self.lambda_holes
                .insert((parameter.ty.span.start, parameter.ty.span.end), ty);
        }
        let mut result_from_body = false;
        if result_hole {
            match hint
                .result
                .or_else(|| arrow.as_ref().map(|arrow| arrow.result))
            {
                Some(ty) => {
                    self.lambda_holes
                        .insert((lambda.result.span.start, lambda.result.span.end), ty);
                }
                None => {
                    if block_any(&lambda.body, &|kind| {
                        matches!(kind, ast::ExprKind::Return(_))
                    }) {
                        return Err(Diagnostic::new(
                            span,
                            "cannot infer the result type of a lambda that uses 'return'; annotate it as '-> T'",
                        ));
                    }
                    result_from_body = true;
                }
            }
        }
        let row = if !row_hole {
            LambdaRow::Declared
        } else if block_any(&lambda.body, &|kind| {
            matches!(
                kind,
                ast::ExprKind::Handle { .. } | ast::ExprKind::Perform { .. }
            )
        }) {
            // Handled bodies capture the row in their suspension sites, so the
            // row must be known before the body is checked.
            match &arrow {
                Some(arrow) => LambdaRow::Fixed(arrow.effects),
                None => {
                    return Err(Diagnostic::new(
                        span,
                        "cannot infer the effect row of a lambda that handles or performs an operation; annotate it as '! { ... }'",
                    ));
                }
            }
        } else {
            LambdaRow::FromBody
        };
        Ok(LambdaInference {
            result_from_body,
            row,
        })
    }
    /// The parameter and result types the first use of binding `id` (in
    /// the statements and tail after its `let`) gives an unannotated lambda:
    /// a direct call `f(a, b)` with arguments typed without context, a
    /// function argument `g(.., f, ..)` whose parameter is an arrow, or an
    /// annotated `let h: T = f`. Only literals and locals already declared
    /// at the `let` are typed, so the hint never depends on code checked
    /// later. The search is bounded; exhausting it asks for the annotation.
    pub(super) fn first_use_hint(
        &mut self,
        id: BindingId,
        lambda: &ast::Lambda,
        statements: &[ast::Statement],
        tail: Option<&ast::Expr>,
    ) -> Result<Option<LambdaHint>> {
        enum Use<'e> {
            Called(&'e [ast::Expr]),
            Argument(&'e ast::Expr, &'e [ast::Expr], usize),
            Annotated(&'e ast::Type),
            Other,
        }
        struct Search<'r> {
            resolution: &'r Resolution,
            id: BindingId,
            budget: usize,
        }
        impl Search<'_> {
            fn is(&self, expr: &ast::Expr) -> bool {
                matches!(expr.kind, ast::ExprKind::Name(_))
                    && self.resolution.reference(expr.span) == Some(self.id)
            }
            fn expr<'e>(&mut self, expr: &'e ast::Expr, depth: usize) -> Option<Option<Use<'e>>> {
                self.budget = self.budget.checked_sub(1)?;
                if depth > 256 {
                    return None;
                }
                if self.is(expr) {
                    return Some(Some(Use::Other));
                }
                if let ast::ExprKind::Call { callee, arguments } = &expr.kind {
                    if self.is(callee) {
                        return Some(Some(Use::Called(arguments)));
                    }
                    if let found @ Some(_) = self.expr(callee, depth + 1)? {
                        return Some(found);
                    }
                    for (index, argument) in arguments.iter().enumerate() {
                        if self.is(argument) {
                            return Some(Some(Use::Argument(callee, arguments, index)));
                        }
                        if let found @ Some(_) = self.expr(argument, depth + 1)? {
                            return Some(found);
                        }
                    }
                    return Some(None);
                }
                let mut children = Vec::new();
                ast_children(expr, &mut |child| children.push(child));
                for child in children {
                    if let found @ Some(_) = self.expr(child, depth + 1)? {
                        return Some(found);
                    }
                }
                Some(None)
            }
        }
        let mut search = Search {
            resolution: self.resolution,
            id,
            budget: 10_000,
        };
        let mut found = None;
        let exhausted = Diagnostic::new(
            lambda.body.span,
            "lambda type inference exhausted its search budget looking for the binding's first use; annotate the lambda",
        );
        for statement in statements {
            let (value, annotation) = match statement {
                ast::Statement::Let { value, ty, .. } => (value, ty.as_ref()),
                ast::Statement::Expr(value) => (value, None),
            };
            if let Some(annotation) = annotation
                && search.is(value)
            {
                found = Some(Use::Annotated(annotation));
                break;
            }
            match search.expr(value, 0) {
                None => return Err(exhausted),
                Some(Some(use_site)) => {
                    found = Some(use_site);
                    break;
                }
                Some(None) => {}
            }
        }
        if found.is_none()
            && let Some(tail) = tail
        {
            found = search.expr(tail, 0).ok_or(exhausted)?;
        }
        let arity = lambda.parameters.len();
        Ok(match found {
            Some(Use::Called(arguments)) if arguments.len() == arity => Some(LambdaHint {
                parameters: arguments
                    .iter()
                    .map(|argument| self.context_free_type(argument))
                    .collect(),
                result: None,
            }),
            Some(Use::Annotated(annotation)) => {
                let (inner, _) = split_grade(annotation);
                let ty = self.ty(inner)?;
                self.arrow_hint(ty, arity)
            }
            Some(Use::Argument(callee, arguments, index)) => {
                self.argument_hint(callee, arguments, index, arity)?
            }
            _ => None,
        })
    }
    pub(super) fn arrow_hint(&self, ty: Type, arity: usize) -> Option<LambdaHint> {
        let (Type::Fn(id) | Type::Once(id)) = ty else {
            return None;
        };
        let arrow = &self.types.function_types[id];
        (arrow.parameters.len() == arity).then(|| LambdaHint {
            parameters: arrow.parameters.iter().copied().map(Some).collect(),
            result: Some(arrow.result),
        })
    }
    /// A type for an argument that needs no context: a literal or a local
    /// already declared.
    pub(super) fn context_free_type(&self, expr: &ast::Expr) -> Option<Type> {
        match &expr.kind {
            ast::ExprKind::Integer(_) => Some(Type::I64),
            ast::ExprKind::Float(_) => Some(Type::Float(crate::float::FloatKind::F64)),
            ast::ExprKind::Bool(_) => Some(Type::Bool),
            ast::ExprKind::Char(_) => Some(Type::Char),
            ast::ExprKind::Name(_) => {
                let binding = self.resolution.reference(expr.span)?;
                let slot = *self.slots.get(&binding)?;
                Some(self.locals[slot].ty)
            }
            _ => None,
        }
    }
    /// The arrow a direct function call expects at argument `index`. A
    /// generic parameter type is resolved only through other arguments
    /// whose declared type is that bare type parameter.
    pub(super) fn argument_hint(
        &mut self,
        callee: &ast::Expr,
        arguments: &[ast::Expr],
        index: usize,
        arity: usize,
    ) -> Result<Option<LambdaHint>> {
        let Some(function) = self.resolution.reference(callee.span) else {
            return Ok(None);
        };
        let Some(declared) = self.functions.declared.get(&function) else {
            return Ok(None);
        };
        if declared.self_ty.is_some() || declared.ast.parameters.len() != arguments.len() {
            return Ok(None);
        }
        let ast = declared.ast;
        let type_vars = ast
            .generics
            .iter()
            .filter(|generic| {
                !is_grade_generic(self.resolution, generic)
                    && !is_const_generic(self.resolution, generic)
                    && !crate::runtime_types::is_effect_generic(self.resolution, generic)
            })
            .filter_map(|generic| self.resolution.binder(generic.span))
            .collect::<Vec<_>>();
        if ast.generics.len() != type_vars.len()
            && ast.generics.iter().any(|generic| {
                is_grade_generic(self.resolution, generic)
                    || is_const_generic(self.resolution, generic)
            })
        {
            return Ok(None);
        }
        let mut subst = crate::runtime_types::Subst::default();
        for (position, (parameter, argument)) in ast.parameters.iter().zip(arguments).enumerate() {
            if position == index {
                continue;
            }
            let (declared, _) = split_grade(&parameter.ty);
            if let ast::TypeKind::Named {
                path,
                arguments: none,
            } = &declared.kind
                && path.len() == 1
                && none.is_empty()
                && let Some(binder) = self.resolution.reference(declared.span)
                && type_vars.contains(&binder)
                && let Some(ty) = self.context_free_type(argument)
            {
                subst.types.entry(binder).or_insert(ty);
            }
        }
        let (target, _) = split_grade(&ast.parameters[index].ty);
        let ast::TypeKind::Function {
            parameters, result, ..
        } = &target.kind
        else {
            return Ok(None);
        };
        if parameters.len() != arity {
            return Ok(None);
        }
        let unresolved = |checker: &Self, ty: &ast::Type| {
            type_vars.iter().any(|var| {
                !subst.types.contains_key(var)
                    && type_mentions_binding(checker.resolution, ty, *var)
            })
        };
        let mut hint = LambdaHint::default();
        for parameter in parameters {
            let (parameter, _) = split_grade(&parameter.ty);
            hint.parameters.push(if unresolved(self, parameter) {
                None
            } else {
                self.types.ty_in(parameter, &subst).ok()
            });
        }
        let (result, _) = split_grade(result);
        if !unresolved(self, result) {
            hint.result = self.types.ty_in(result, &subst).ok();
        }
        Ok(Some(hint))
    }
    /// Validate a lambda result type inferred from its body.
    pub(super) fn inferred_lambda_result(&self, ty: Type, span: Span) -> Result<Type> {
        let reason = if ty == Type::Never {
            Some("its body never returns")
        } else if matches!(ty, Type::Union(_)) {
            Some("it would be a union, and Kush does not insert union coercions implicitly")
        } else if ty.is_view()
            || ty.is_slice()
            || ty.is_ref()
            || crate::runtime_types::has_borrow(self.types, ty)
        {
            Some("a borrowed result needs an explicit lifetime contract")
        } else if crate::runtime_types::contains_task(self.types, ty) {
            Some("a function value cannot return a task handle")
        } else {
            None
        };
        if reason.is_none() {
            self.reject_lambda_runtime_length(ty, span)?;
        }
        match reason {
            Some(reason) => Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer this lambda's result type {}: {reason}; annotate it as '-> T'",
                    self.types.name(ty)
                ),
            )),
            None => Ok(ty),
        }
    }
    /// Outer scalar slots a call to this callable may write. A direct lambda
    /// value reports the writing captures of its generated function; a local
    /// reports the captured targets recorded when it was bound. Unknown forms
    /// return `None` (they are never borrowed-capture closures in checked IR).
    /// Types a closure value captures: from a closure literal, or from the
    /// closure a local was bound to.
    pub(super) fn closure_capture_types(&self, expr: &Expr) -> Option<Vec<Type>> {
        let mut current = expr;
        while let ExprKind::Coerce { value, .. } = &current.kind {
            current = value;
        }
        match &current.kind {
            ExprKind::FnValue { captures, .. } => {
                Some(captures.iter().map(|capture| capture.ty).collect())
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                self.closure_captures.get(slot).cloned()
            }
            _ => None,
        }
    }
    /// Locals a closure value captures by reference (reads or writes).
    pub(super) fn closure_reference_targets(&self, expr: &Expr) -> Vec<usize> {
        let mut current = expr;
        while let ExprKind::Coerce { value, .. } = &current.kind {
            current = value;
        }
        let ExprKind::FnValue { function, captures } = &current.kind else {
            return vec![];
        };
        let Some(body) = self
            .functions
            .bodies
            .get(*function)
            .and_then(Option::as_ref)
        else {
            return vec![];
        };
        body.capture_refs
            .iter()
            .enumerate()
            .filter(|(_, by_reference)| **by_reference)
            .filter_map(|(index, _)| match captures.get(index)?.kind {
                ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => Some(slot),
                _ => None,
            })
            .collect()
    }
    /// Whether a value of this type gives mutable access (an exclusive view
    /// or reference, possibly inside a record or container) to storage that
    /// can hold a function value.
    pub(super) fn mutable_callable_storage(&self, ty: Type) -> bool {
        let mut pending = vec![ty];
        let mut seen = BTreeSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            match ty {
                Type::RefMut(p) | Type::SliceMut(p) => {
                    if self.contains_callable(self.types.pointees[p]) {
                        return true;
                    }
                }
                Type::Box(p)
                | Type::Vec(p)
                | Type::Ref(p)
                | Type::Slice(p)
                | Type::ArenaBox(p)
                | Type::AllocBox(p)
                | Type::AllocVec(p)
                | Type::Annotated(p, _) => pending.push(self.types.pointees[p]),
                Type::Enum(id) | Type::Variants(id, _) => {
                    for variant in &self.types.enums[id].variants {
                        pending.extend(variant.fields.iter().copied());
                    }
                }
                Type::Union(id) => pending.extend(self.types.unions[id].members.iter().copied()),
                _ => {}
            }
        }
        false
    }
    /// Whether a value of this type can hold a function value (directly, in
    /// a field, element, union member, reference, or trait object).
    pub(super) fn contains_callable(&self, ty: Type) -> bool {
        let mut pending = vec![ty];
        let mut seen = BTreeSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            match ty {
                Type::Fn(_)
                | Type::Once(_)
                | Type::Multi(_)
                | Type::DynObj(_)
                | Type::Task(_)
                | Type::Thread(_)
                | Type::AllocatorContext => return true,
                Type::Box(p)
                | Type::Vec(p)
                | Type::ArenaBox(p)
                | Type::AllocBox(p)
                | Type::AllocVec(p)
                | Type::Ref(p)
                | Type::RefMut(p)
                | Type::Slice(p)
                | Type::SliceMut(p)
                | Type::Annotated(p, _) => pending.push(self.types.pointees[p]),
                Type::Enum(id) | Type::Variants(id, _) => {
                    for variant in &self.types.enums[id].variants {
                        pending.extend(variant.fields.iter().copied());
                    }
                }
                Type::Union(id) => pending.extend(self.types.unions[id].members.iter().copied()),
                _ => {}
            }
        }
        false
    }
    pub(super) fn closure_write_targets(&self, expr: &Expr) -> Option<Vec<usize>> {
        let mut current = expr;
        loop {
            match &current.kind {
                ExprKind::Coerce { value, .. } => current = value,
                ExprKind::FnValue { function, captures } => {
                    let body = self.functions.bodies.get(*function)?.as_ref()?;
                    let targets = body
                        .capture_writes
                        .iter()
                        .enumerate()
                        .filter(|(_, writes)| **writes)
                        .filter_map(|(index, _)| match captures.get(index)?.kind {
                            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                                Some(slot)
                            }
                            _ => None,
                        })
                        .collect();
                    return Some(targets);
                }
                ExprKind::Local(slot) | ExprKind::Peek(slot) => {
                    return self.closure_writes.get(slot).cloned();
                }
                _ => return None,
            }
        }
    }
    /// Apply every callable execution path's may-write summary to the caller.
    pub(super) fn apply_closure_writes(&mut self, targets: impl IntoIterator<Item = usize>) {
        for slot in targets {
            self.invalidate_scalar_proofs(slot);
            self.written_slots.insert(slot);
        }
    }
    /// Calls with a declared operation can invoke its dynamically installed
    /// handler even when there is no lexical perform in this function.
    pub(super) fn apply_effect_writes(&mut self, effects: u16) {
        let slots = self
            .handlers
            .iter()
            .filter(|handler| self.operation_effect(&handler.operation) & effects != 0)
            .map(|handler| handler.slot)
            .collect::<Vec<_>>();
        for slot in slots {
            self.apply_handler_writes(slot);
        }
    }
    pub(super) fn apply_handler_writes(&mut self, slot: usize) {
        let targets = self.closure_writes.get(&slot).cloned().unwrap_or_default();
        self.apply_closure_writes(targets);
    }
    /// Forget proof facts and symbolic versions about a scalar location that a
    /// writing closure may have changed. The location itself remains live; only
    /// old-value evidence is invalidated.
    pub(super) fn invalidate_scalar_proofs(&mut self, slot: usize) {
        let ty = self.locals[slot].ty;
        if ty.scalar_carrier().is_some() {
            self.facts.bump(slot);
            if let Some(id) = self
                .slots
                .iter()
                .find_map(|(id, candidate)| (*candidate == slot).then_some(*id))
            {
                self.fresh_scalar_value(id, ty);
            }
        }
    }
    /// Outer local slots referenced by a lambda body. Resolution already maps
    /// every occurrence to its exact binder, so filtering by the current slot
    /// map removes lambda parameters, lambda locals, and type/grade binders.
    pub(super) fn lambda_captures(&self, lambda: &ast::Lambda, quotation: bool) -> Vec<usize> {
        if !self.quote_holes.is_empty() || !self.quote_splices.is_empty() {
            fn visit(
                c: &Checker<'_, '_>,
                expr: &ast::Expr,
                quotation: bool,
                slots: &mut BTreeSet<usize>,
            ) {
                let key = (expr.span.start, expr.span.end);
                // The quotation root serializes splice graphs. A nested
                // callable only needs the placeholder's function identity.
                if !quotation && c.quote_splices.contains_key(&key) {
                    return;
                }
                if let Some(slot) = c.quote_holes.get(&key) {
                    slots.insert(*slot);
                    return;
                }
                if let Some(id) = c.resolution.reference(expr.span)
                    && let Some(slot) = c.slots.get(&id)
                {
                    slots.insert(*slot);
                }
                ast_children(expr, &mut |child| visit(c, child, quotation, slots));
            }
            let mut slots = BTreeSet::new();
            for statement in &lambda.body.statements {
                match statement {
                    ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => {
                        visit(self, value, quotation, &mut slots)
                    }
                }
            }
            if let Some(tail) = &lambda.body.tail {
                visit(self, tail, quotation, &mut slots);
            }
            return slots.into_iter().collect();
        }
        let mut ids = BTreeSet::new();
        collect_lambda_refs(self.resolution, &lambda.body, &mut ids);
        ids.iter()
            .filter_map(|id| self.slots.get(id).copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
    /// Whether values of `ty` carry a declared `#[linear]` obligation.
    pub(super) fn linear_type(&self, ty: Type) -> bool {
        // Reachability over the finite type graph, not recursive unfolding:
        // binary recursive data would otherwise cause exponential work.
        let mut pending = vec![ty];
        let mut seen = std::collections::BTreeSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            match ty {
                Type::Box(p) | Type::Vec(p) => pending.push(self.types.pointees[p]),
                Type::Enum(id) | Type::Variants(id, _) => {
                    if self.types.enums[id].linear {
                        return true;
                    }
                    pending.extend(
                        self.types.enums[id]
                            .variants
                            .iter()
                            .flat_map(|v| v.fields.iter())
                            .copied(),
                    );
                }
                Type::Union(id) => pending.extend(self.types.unions[id].members.iter().copied()),
                Type::Once(id) if self.types.function_types[id].linear => return true,
                _ => {}
            }
        }
        false
    }
    /// A named or explicitly specialized function used as a value.
    pub(super) fn function_value(
        &mut self,
        id: BindingId,
        explicit: Option<&[ast::Type]>,
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let f = self.functions.declared[&id].ast;
        if f.foreign.is_some() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "foreign function '{}' can only be called directly; a C function pointer has no checked Kush callable type",
                    f.name
                ),
            ));
        }
        if f.parameters.iter().any(|parameter| {
            matches!(
                split_grade(&parameter.ty).0.kind,
                ast::TypeKind::Capability { .. }
            )
        }) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' has a capability parameter and can only be called directly; as a function value it would let a capability be forged or escape",
                    f.name
                ),
            ));
        }
        if f.parameters
            .iter()
            .any(|parameter| parameter.min_length.is_some())
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' has a 'where len >= N' parameter and can only be called directly, where the length is proved or checked",
                    f.name
                ),
            ));
        }
        if f.parameters.iter().any(|parameter| parameter.erased) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' has erased proof parameters and cannot be a first-class value; call it directly so the obligation is discharged at the call site",
                    f.name
                ),
            ));
        }
        if explicit.is_some() && f.generics.is_empty() {
            return Err(Diagnostic::new(
                span,
                format!("'{}' is not generic; remove the type arguments", f.name),
            ));
        }
        let what = format!("'{}'", f.name);
        let (type_arguments, grade_arguments, const_arguments, effect_arguments) = match explicit {
            Some(list) => {
                let (types, grades, consts, effects, _) = self.infer(
                    &f.generics,
                    Some(list),
                    &[],
                    None,
                    None,
                    None,
                    None,
                    &what,
                    span,
                )?;
                (types, grades, consts, effects)
            }
            None if f.generics.is_empty() => (vec![], vec![], vec![], vec![]),
            None => self.infer_function_value(f, expected, &what, span)?,
        };
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
        let signature = self.functions.signatures[index].clone();
        if signature
            .parameters
            .iter()
            .chain([&signature.result])
            .any(|ty| !crate::runtime_types::runtime_length_binders(self.types, *ty).is_empty())
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "'{}' has a runtime-length array in its signature and cannot be a first-class value; call it directly so the length binder is substituted",
                    f.name
                ),
            ));
        }
        // Slice parameters/results and borrowed record fields carry their
        // lifetime contract in the callable type. Owner references and text
        // views remain direct-call only.
        if signature
            .parameters
            .iter()
            .chain([&signature.result])
            .any(|ty| {
                !ty.is_slice()
                    && !ty.is_ref()
                    && !crate::runtime_types::is_borrowed_record(self.types, *ty)
                    && !crate::runtime_types::is_reference_container(self.types, *ty)
                    && !crate::runtime_types::is_borrowed_task_exit(self.types, *ty)
                    && crate::runtime_types::has_borrow(self.types, *ty)
            })
        {
            return Err(Diagnostic::new(
                span,
                "a function value cannot carry an owner reference or &str text view in a parameter or result type; use references, slice views, or records with borrowed fields",
            ));
        }
        let parameter_lifetimes = signature
            .parameters
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                (ty.is_slice() || ty.is_ref()).then(|| {
                    signature
                        .parameter_lifetimes
                        .get(i)
                        .cloned()
                        .flatten()
                        .unwrap_or_else(|| format!("<unnamed {i}>"))
                })
            })
            .collect::<Vec<_>>();
        let parameter_leaves = signature
            .parameters
            .iter()
            .map(|ty| {
                if crate::runtime_types::is_borrowed_record(self.types, *ty)
                    || crate::runtime_types::is_reference_container(self.types, *ty)
                    || crate::runtime_types::is_borrowed_task_exit(self.types, *ty)
                {
                    crate::runtime_types::borrow_leaves(self.types, *ty)
                } else {
                    crate::runtime_types::reference_referent_leaves(self.types, *ty)
                }
            })
            .collect::<Result<Vec<_>>>()?;
        let result_lifetime = signature
            .result
            .is_slice()
            .then(|| signature.result_lifetime.clone())
            .flatten();
        let result_lifetime = if signature.result.is_ref() {
            signature.result_lifetime.clone()
        } else {
            result_lifetime
        };
        let result_leaves =
            if crate::runtime_types::is_borrowed_record(self.types, signature.result)
                || crate::runtime_types::is_reference_container(self.types, signature.result)
                || crate::runtime_types::is_borrowed_task_exit(self.types, signature.result)
            {
                crate::runtime_types::borrow_leaves(self.types, signature.result)?
            } else {
                Vec::new()
            };
        let function_type = self.types.function_type_with(
            signature.parameters.clone(),
            signature.result,
            signature.effects,
            signature.parameter_grades.clone(),
            signature.result_grade,
            false,
            false,
            crate::runtime_types::BorrowSig::canonical_with_leaves(
                &parameter_lifetimes,
                result_lifetime.as_ref(),
                &parameter_leaves,
                &result_leaves,
                &signature.lifetime_bounds,
            ),
        );
        let value = Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![],
            },
            ty: Type::Fn(function_type),
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Infer type/const arguments of a generic function used as a value from an
    /// expected arrow type. A usage grade may also be inferred when it is the
    /// entire outer result grade and the expected arrow carries the concrete
    /// `@[1]` transfer contract; every other grade use stays explicit.
    pub(super) fn infer_function_value(
        &mut self,
        f: &ast::Function,
        expected: Option<Type>,
        what: &str,
        span: Span,
    ) -> Result<GenericArguments> {
        let Some((id, _)) = expected.and_then(Checker::function_parts) else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a generic function value needs an expected 'fn(...)' type or explicit '::<...>' specialization for {what}"
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        let runtime = f
            .parameters
            .iter()
            .filter(|p| !p.erased)
            .collect::<Vec<_>>();
        if runtime.len() != signature.parameters.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "function value for {what} expects {} runtime arguments, but the target arrow type has {}",
                    runtime.len(),
                    signature.parameters.len()
                ),
            ));
        }
        let mut type_vars = Vec::new();
        let mut grade_vars = Vec::new();
        let mut const_vars = Vec::new();
        let mut effect_vars = Vec::new();
        for generic in &f.generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            if is_grade_generic(self.resolution, generic) {
                grade_vars.push(binder);
            } else if is_const_generic(self.resolution, generic) {
                const_vars.push(binder);
            } else if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                effect_vars.push(binder);
            } else {
                type_vars.push(binder);
            }
        }
        let mut subst = crate::runtime_types::Subst::default();
        let constraint_mark = self.effect_constraints.len();
        for (parameter, actual) in runtime.iter().zip(&signature.parameters) {
            self.unify(
                split_grade(&parameter.ty).0,
                *actual,
                &type_vars,
                &const_vars,
                &effect_vars,
                &mut subst,
                span,
            )?;
        }
        let expanded_result = expand_result_aliases(self.resolution, self.types, &f.result)?;
        let (declared_result, result_grade) = split_grade(&expanded_result);
        self.unify(
            declared_result,
            signature.result,
            &type_vars,
            &const_vars,
            &effect_vars,
            &mut subst,
            span,
        )?;
        // The expected arrow's effect row is also evidence: the source may
        // perform only effects permitted by the target. This is accumulated
        // with constraints from callable parameters, then solved as one group.
        let row = crate::runtime_types::effect_row_term(self.resolution, &f.effects)?;
        let effect_generics = f
            .generics
            .iter()
            .filter(|generic| crate::runtime_types::is_effect_generic(self.resolution, generic))
            .collect::<Vec<_>>();
        let row_variables = row.variables();
        if row_variables
            .iter()
            .any(|variable| !subst.effects.contains_key(variable))
        {
            self.effect_constraints.push(EffectConstraint {
                row,
                actual: signature.effects,
                span,
            });
        }
        self.solve_effect_constraints(constraint_mark, &effect_generics, &mut subst, span)?;
        // General grade inference for a generic function value. The expected
        // arrow supplies concrete grades for its parameters and result. All
        // equations are solved simultaneously in the decidable natural or
        // finite-algebra fragment. A binder that reaches an underlying runtime
        // type, that has no expected-grade evidence, or whose equation has no
        // unique solution remains an explicit-specialization error. Unknown
        // grades are never guessed as one.
        let mut grades = Vec::new();
        if !grade_vars.is_empty() {
            let mut constraints = runtime
                .iter()
                .zip(&signature.parameter_grades)
                .filter_map(|(parameter, expected)| {
                    let declared = split_grade(&parameter.ty).1?;
                    let expected = (*expected)?;
                    Some((declared, expected))
                })
                .collect::<Vec<_>>();
            if let Some(declared) = result_grade
                && let Some(expected) = signature.result_grade
            {
                constraints.push((declared, expected));
            }
            let solved =
                grades::solve_all(self.resolution, &self.grades, &grade_vars, &constraints)?
                    .unwrap_or_default();
            for binder in &grade_vars {
                let name = &self.resolution.bindings[*binder].name;
                let in_underlying_type = runtime.iter().any(|parameter| {
                    type_mentions_binding(self.resolution, split_grade(&parameter.ty).0, *binder)
                }) || type_mentions_binding(
                    self.resolution,
                    declared_result,
                    *binder,
                );
                let reason = if in_underlying_type {
                    "it occurs in an underlying parameter or result type, where a usage grade cannot be inferred".to_owned()
                } else if let Some(value) = solved.get(binder) {
                    subst.grades.insert(*binder, *value);
                    grades.push(*value);
                    continue;
                } else if result_grade.is_none()
                    && !runtime
                        .iter()
                        .any(|parameter| split_grade(&parameter.ty).1.is_some())
                {
                    "the declaration has no grade expression for the expected arrow to determine"
                        .to_owned()
                } else {
                    "no expected parameter/result grade uniquely determines it, or its grade equation is outside the decidable natural/finite-algebra fragment".to_owned()
                };
                return Err(Diagnostic::new(
                    self.resolution.bindings[*binder].span,
                    format!(
                        "cannot infer usage grade parameter '{name}' of {what}: {reason}. Specialize it explicitly with '::<...>'"
                    ),
                ));
            }
        }
        let mut types = Vec::new();
        for generic in f.generics.iter() {
            let binder = self.resolution.binder(generic.span).unwrap();
            if is_grade_generic(self.resolution, generic) {
                continue;
            }
            if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                continue;
            }
            if is_const_generic(self.resolution, generic) {
                let Some(value) = subst.consts.get(&binder) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer natural parameter '{}' of {what}; specialize explicitly with '::<...>'",
                            generic.name
                        ),
                    ));
                };
                let _ = value;
            } else {
                let Some(ty) = subst.types.get(&binder) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer type parameter '{}' of {what}; specialize explicitly with '::<...>'",
                            generic.name
                        ),
                    ));
                };
                types.push(*ty);
            }
        }
        let consts = f
            .generics
            .iter()
            .filter(|generic| is_const_generic(self.resolution, generic))
            .map(|generic| {
                subst
                    .consts
                    .get(&self.resolution.binder(generic.span).unwrap())
                    .copied()
                    .ok_or_else(|| {
                        Diagnostic::new(
                            span,
                            format!(
                                "cannot infer natural parameter '{}' of {what}; specialize explicitly with '::<...>'",
                                generic.name
                            ),
                        )
                    })
            })
            .collect::<Result<Vec<_>>>()?;
        let effects = f
            .generics
            .iter()
            .filter(|generic| crate::runtime_types::is_effect_generic(self.resolution, generic))
            .map(|generic| {
                subst
                    .effects
                    .get(&self.resolution.binder(generic.span).unwrap())
                    .copied()
                    .ok_or_else(|| {
                        Diagnostic::new(
                            span,
                            format!(
                                "cannot infer effect row parameter '{}' of {what}; specialize explicitly with '::<...>'",
                                generic.name
                            ),
                        )
                    })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok((types, grades, consts, effects))
    }
    /// Indirect call through a function-typed value.
    pub(super) fn indirect_call(
        &mut self,
        callee: &ast::Expr,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let callee = self.expr(callee)?;
        self.indirect_call_checked(callee, arguments, expected, span)
    }
    /// Indirect call with an already checked callee value. Shared by the
    /// ordinary field-projection call path and method dispatch, so receiver
    /// evaluation happens exactly once.
    pub(super) fn indirect_call_checked(
        &mut self,
        callee: Expr,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let parts = match callee.ty {
            // A multishot token is called without being consumed.
            Type::Multi(id) => Some((id, false)),
            ty => Self::function_parts(ty),
        };
        let Some((id, _)) = parts else {
            return Err(Diagnostic::new(
                callee.span,
                format!(
                    "this value is not an executable function; expected fn(...) or once fn(...), found {}",
                    self.types.name(callee.ty)
                ),
            ));
        };
        let write_targets = self.closure_write_targets(&callee).unwrap_or_default();
        let signature = self.types.function_types[id].clone();
        if signature.parameters.len() != arguments.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count: expected {}, found {}",
                    signature.parameters.len(),
                    arguments.len()
                ),
            ));
        }
        self.require(signature.effects, span)?;
        let mut binders = BTreeSet::new();
        for ty in signature
            .parameters
            .iter()
            .copied()
            .chain(std::iter::once(signature.result))
        {
            binders.extend(crate::runtime_types::borrow_lifetimes(self.types, ty));
        }
        binders.retain(|label| !label.is_empty() && !label.starts_with('<'));
        let mut diverges = false;
        let mut checked = Vec::with_capacity(arguments.len());
        for (argument, parameter) in arguments.iter().zip(&signature.parameters) {
            // An arrow's record lifetimes are instantiated afresh at each
            // call, exactly like a direct call. The argument constructs a
            // record with its own inferred labels; the call occurrence
            // constraints relate those labels to the arrow's declared ones.
            let wanted = self
                .types
                .freshen_borrows(*parameter, &binders, argument.span)?;
            let value = self.expr_expected(argument, Some(wanted))?;
            diverges |= value.ty == Type::Never;
            checked.push(value);
        }
        let ty = if diverges {
            Type::Never
        } else {
            self.instantiated_call_result_type(
                &binders,
                &signature.parameters,
                signature.result,
                signature.result_grade,
                &BTreeSet::new(),
                &checked,
                span,
            )?
        };
        let mut values = Vec::with_capacity(checked.len());
        for (value, parameter) in checked.into_iter().zip(&signature.parameters) {
            let value_span = value.span;
            values.push(self.coerce_argument(value, *parameter, value_span)?);
        }
        // A writing closure may change a captured scalar location during the
        // call. The callee and every argument have already been evaluated, so
        // invalidate old-value facts only now: proofs established before the
        // call cannot be reused after it, while argument checking still sees
        // the pre-call value. Reading closures have no write targets.
        self.apply_closure_writes(write_targets);
        self.apply_effect_writes(signature.effects);
        let value = Expr {
            kind: ExprKind::CallIndirect {
                callee: Box::new(callee),
                arguments: values,
            },
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
}
