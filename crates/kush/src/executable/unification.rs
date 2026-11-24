//! Union patterns, type and effect-row unification and inference.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Whether `ty` mentions a type or const variable that is not yet inferred.
    pub(super) fn mentions(
        &self,
        ty: &ast::Type,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &crate::runtime_types::Subst,
    ) -> bool {
        match &ty.kind {
            ast::TypeKind::Named { arguments, .. } => {
                self.resolution.reference(ty.span).is_some_and(|id| {
                    (type_vars.contains(&id) && !subst.types.contains_key(&id))
                        || (const_vars.contains(&id) && !subst.consts.contains_key(&id))
                        || (effect_vars.contains(&id) && !subst.effects.contains_key(&id))
                }) || arguments
                    .iter()
                    .any(|a| self.mentions(a, type_vars, const_vars, effect_vars, subst))
            }
            ast::TypeKind::Borrow { inner, .. }
            | ast::TypeKind::Slice(inner)
            | ast::TypeKind::Graded { inner, .. } => {
                self.mentions(inner, type_vars, const_vars, effect_vars, subst)
            }
            ast::TypeKind::Array(inner, length) => {
                self.mentions(inner, type_vars, const_vars, effect_vars, subst)
                    || self.const_mentions(length, const_vars, subst)
            }
            ast::TypeKind::Binary { left, right, .. } => {
                self.mentions(left, type_vars, const_vars, effect_vars, subst)
                    || self.mentions(right, type_vars, const_vars, effect_vars, subst)
            }
            ast::TypeKind::Tuple(items) => items
                .iter()
                .any(|a| self.mentions(a, type_vars, const_vars, effect_vars, subst)),
            ast::TypeKind::Structural { fields, row, .. } => {
                fields.iter().any(|field| {
                    self.mentions(&field.ty, type_vars, const_vars, effect_vars, subst)
                }) || row.as_ref().is_some_and(|row| {
                    self.mentions(row, type_vars, const_vars, effect_vars, subst)
                })
            }
            ast::TypeKind::Function {
                parameters,
                result,
                effects,
                ..
            } => {
                parameters.iter().any(|parameter| {
                    self.mentions(&parameter.ty, type_vars, const_vars, effect_vars, subst)
                }) || self.mentions(result, type_vars, const_vars, effect_vars, subst)
                    || effects.iter().any(|effect| {
                        self.mentions(effect, type_vars, const_vars, effect_vars, subst)
                    })
            }
            _ => false,
        }
    }
    pub(super) fn const_mentions(
        &self,
        ty: &ast::Type,
        const_vars: &[BindingId],
        subst: &crate::runtime_types::Subst,
    ) -> bool {
        match &ty.kind {
            ast::TypeKind::Named { arguments, .. } => {
                self.resolution
                    .reference(ty.span)
                    .is_some_and(|id| const_vars.contains(&id) && !subst.consts.contains_key(&id))
                    || arguments
                        .iter()
                        .any(|a| self.const_mentions(a, const_vars, subst))
            }
            ast::TypeKind::Binary { left, right, .. } => {
                self.const_mentions(left, const_vars, subst)
                    || self.const_mentions(right, const_vars, subst)
            }
            ast::TypeKind::Function {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| self.const_mentions(&parameter.ty, const_vars, subst))
                    || self.const_mentions(result, const_vars, subst)
            }
            _ => false,
        }
    }
    /// Select one candidate at a multi-variable union partition decision.
    /// Ordinary inference takes choice zero; a cross-parameter backtracking
    /// replay takes the next index from its plan. The decision cardinality is
    /// recorded so the driver can enumerate choices deterministically.
    pub(super) fn union_partition_choice(&mut self, cardinality: usize) -> Result<usize> {
        if !self.unify_plan_active {
            if cardinality > 1 {
                self.unify_open_choice = true;
            }
            return Ok(0);
        }
        let index = self.unify_decisions.len();
        self.unify_decisions.push(cardinality);
        let choice = self.unify_plan.get(index).copied().unwrap_or(0);
        if choice >= cardinality {
            return Err(Diagnostic::new(
                Span::default(),
                "internal cross-parameter partition replay exhausted its local choices",
            ));
        }
        Ok(choice)
    }
    /// Solve a declared union pattern with exactly one bare type variable and
    /// a concrete fixed part, such as `T | i64`. The residual actual
    /// alternatives that are not covered by the fixed part determine `T`.
    ///
    /// This is deliberately a decidable residual-union rule, not row
    /// subtraction: the fixed alternatives must not mention any inference
    /// variable, and a second variable alternative is left to the ordinary
    /// error path instead of being partitioned arbitrarily. If every actual
    /// alternative is already covered by the fixed part, `T` has no unique
    /// residual binding (it could be `Never`, the fixed type itself, or a
    /// wider union), so the call is rejected rather than defaulting.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn unify_union_pattern(
        &mut self,
        pattern: &ast::Type,
        actual: Type,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<bool> {
        fn flatten<'a>(pattern: &'a ast::Type, out: &mut Vec<&'a ast::Type>) {
            match &pattern.kind {
                ast::TypeKind::Binary {
                    op: crate::lexer::Kind::Pipe,
                    left,
                    right,
                } => {
                    flatten(left, out);
                    flatten(right, out);
                }
                _ => out.push(pattern),
            }
        }
        let mut alternatives = Vec::new();
        flatten(pattern, &mut alternatives);
        // A bare unbound variable is a partition target. A variable that was
        // already solved by an earlier parameter is part of the fixed cover, as
        // is any concrete alternative.
        let mut variables: Vec<(&ast::Type, BindingId)> = Vec::new();
        let mut fixed = Vec::new();
        let mut shaped = Vec::new();
        for alternative in alternatives {
            let variable_id = matches!(
                &alternative.kind,
                ast::TypeKind::Named { path, arguments }
                    if arguments.is_empty() && path.len() == 1
            )
            .then(|| self.resolution.reference(alternative.span))
            .flatten()
            .filter(|id| type_vars.contains(id));
            if let Some(id) = variable_id
                && !subst.types.contains_key(&id)
            {
                // A repeated bare variable (`T | T | i64`) is one partition
                // target, not two; the normalized pattern is still `T | i64`.
                if !variables.iter().any(|(_, existing)| *existing == id) {
                    variables.push((alternative, id));
                }
            } else if self.mentions(alternative, type_vars, const_vars, effect_vars, subst) {
                // A constructor alternative with unbound arguments, such as
                // `Option<T>`: an indexed-union pattern.
                shaped.push(alternative);
            } else {
                fixed.push(alternative);
            }
        }
        if !shaped.is_empty() {
            return self.unify_indexed_union_pattern(
                pattern,
                variables,
                shaped,
                fixed,
                actual,
                type_vars,
                const_vars,
                effect_vars,
                subst,
                span,
            );
        }
        if variables.is_empty() || fixed.is_empty() {
            return Ok(false);
        }
        // Assign in generic declaration order, not pattern operand order, so
        // `A | B` and `B | A` (the same normalized union) infer the same way.
        variables.sort_by_key(|(_, id)| {
            type_vars
                .iter()
                .position(|candidate| candidate == id)
                .unwrap_or(usize::MAX)
        });
        let fixed_ty = {
            let mut types = Vec::with_capacity(fixed.len());
            for alternative in &fixed {
                types.push(self.types.ty_in(alternative, subst)?);
            }
            self.types.union(types, span)?
        };
        let mut residual = Vec::new();
        for member in self.types.union_members(actual) {
            if !self.subtype(member, fixed_ty) {
                residual.push(member);
            }
        }
        if residual.is_empty() {
            let names = variables
                .iter()
                .map(|(_, id)| self.resolution.bindings[*id].name.clone())
                .collect::<Vec<_>>()
                .join("', '");
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer type parameter '{names}' from the union pattern: every actual alternative of {} is already covered by the fixed part, so the residual binding is not unique. Specialize it explicitly with '::<...>'",
                    self.types.name(actual)
                ),
            ));
        }
        if variables.len() == 1 {
            let (variable, _) = variables[0];
            let residual = self.types.union(residual, span)?;
            self.unify(
                variable,
                residual,
                type_vars,
                const_vars,
                effect_vars,
                subst,
                span,
            )?;
            return Ok(true);
        }
        // Two or more unbound variables: enumerate partitions of the residual
        // alternatives with bounded backtracking. Every variable must receive
        // at least one residual alternative; fixed-covered alternatives stay
        // with the fixed part and are never redistributed, which keeps the
        // single-variable residual rule unchanged. A partition is accepted
        // only when it is unique, so symmetric assignments such as `T | U`
        // over `Bool | Unit` are an explicit ambiguity rather than an
        // arbitrary choice.
        let names = variables
            .iter()
            .map(|(_, id)| self.resolution.bindings[*id].name.clone())
            .collect::<Vec<_>>()
            .join("', '");
        if residual.len() < variables.len() {
            let residual_ty = self.types.union(residual.clone(), span)?;
            let residual_name = self.types.name(residual_ty);
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer type parameters '{names}' from the union pattern: the residual type {residual_name} has {} alternative(s) for {} unbound variables, so no partition binds every variable. Specialize explicitly with '::<...>'",
                    residual.len(),
                    variables.len()
                ),
            ));
        }
        fn assign(
            index: usize,
            members: &[Type],
            slots: &mut Vec<Vec<Type>>,
            budget: &mut usize,
            solutions: &mut Vec<Vec<Vec<Type>>>,
        ) -> bool {
            if *budget == 0 {
                return false;
            }
            *budget -= 1;
            if index == members.len() {
                if slots.iter().any(Vec::is_empty) {
                    return true;
                }
                solutions.push(slots.clone());
                return true;
            }
            let member = members[index];
            for slot in 0..slots.len() {
                slots[slot].push(member);
                if !assign(index + 1, members, slots, budget, solutions) {
                    return false;
                }
                slots[slot].pop();
            }
            true
        }
        const PARTITION_BUDGET: usize = 4096;
        let mut budget = PARTITION_BUDGET;
        let mut solutions = Vec::new();
        let mut slots = vec![Vec::new(); variables.len()];
        let complete = assign(0, &residual, &mut slots, &mut budget, &mut solutions);
        if !complete || budget == 0 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer type parameters '{names}' from the union pattern: the bounded partition search exhausted {PARTITION_BUDGET} steps. Specialize explicitly with '::<...>'"
                ),
            ));
        }
        // The search order fixes a canonical partition: residual alternatives
        // keep their normalized order and are handed to the unbound variables
        // in declaration order, with backtracking only to skip partitions that
        // leave a variable empty. Ordinary inference takes the first partition.
        // A later parameter that rejects it triggers the bounded cross-parameter
        // replay in `infer`, which reruns every constraint from the base
        // substitution with the next deterministic partition choice. The total
        // number of replay attempts is capped by
        // `UNIFY_BACKTRACK_BUDGET`; exhausting it is an explicit diagnostic.
        let choice = self.union_partition_choice(solutions.len())?;
        let solution = solutions
            .into_iter()
            .nth(choice)
            .expect("partition choice is in range");
        for ((variable, _), members) in variables.iter().zip(solution) {
            let bound = self.types.union(members, span)?;
            self.unify(
                variable,
                bound,
                type_vars,
                const_vars,
                effect_vars,
                subst,
                span,
            )?;
            if let Some(binder) = self.resolution.reference(variable.span) {
                self.partition_bound.insert(binder);
            }
        }
        Ok(true)
    }
    /// Whether a declared constructor alternative of a union pattern has the
    /// same outer constructor as an actual union member: the same nominal
    /// definition, `Box`/`Vec`, tuple arity, array, structural row that has
    /// every declared field, or arrow arity. Only such members can be covered
    /// by the alternative once its arguments are instantiated.
    pub(super) fn union_pattern_head_matches(&self, pattern: &ast::Type, actual: Type) -> bool {
        match &pattern.kind {
            ast::TypeKind::Named { arguments, .. } => {
                let Some(id) = self.resolution.reference(pattern.span) else {
                    return false;
                };
                let binding = &self.resolution.bindings[id];
                match binding.kind {
                    BindingKind::Alias => {
                        let arguments = arguments
                            .iter()
                            .filter(|argument| !matches!(argument.kind, ast::TypeKind::Lifetime(_)))
                            .collect::<Vec<_>>();
                        let Some((generics, body)) = self.types.alias_definition(id) else {
                            return false;
                        };
                        if generics.len() != arguments.len() {
                            return false;
                        }
                        let map = generics
                            .iter()
                            .zip(arguments.iter().copied())
                            .map(|(generic, argument)| {
                                (self.resolution.binder(generic.span).unwrap(), argument)
                            })
                            .collect::<BTreeMap<_, _>>();
                        let expanded = substitute_alias_type(self.resolution, body, &map);
                        self.union_pattern_head_matches(&expanded, actual)
                    }
                    BindingKind::Builtin => matches!(
                        (binding.name.as_str(), actual),
                        ("Box", Type::Box(_)) | ("Vec", Type::Vec(_))
                    ),
                    BindingKind::Data => actual
                        .layout()
                        .is_some_and(|layout| self.types.enums[layout].definition == id),
                    _ => false,
                }
            }
            ast::TypeKind::Tuple(items) => actual.layout().is_some_and(|layout| {
                let layout = &self.types.enums[layout];
                layout.tuple && layout.arguments.len() == items.len()
            }),
            ast::TypeKind::Array(..) => actual
                .layout()
                .is_some_and(|layout| self.types.enums[layout].array.is_some()),
            ast::TypeKind::Structural { fields, .. } => {
                self.types.record_row_fields(actual).is_some_and(|row| {
                    actual
                        .layout()
                        .is_some_and(|layout| self.types.enums[layout].structural)
                        && fields
                            .iter()
                            .all(|field| row.iter().any(|actual| actual.name == field.name))
                })
            }
            ast::TypeKind::Function { parameters, .. } => match actual {
                Type::Fn(id) | Type::Once(id) | Type::Multi(id) => {
                    self.types.function_types[id].parameters.len() == parameters.len()
                }
                _ => false,
            },
            _ => false,
        }
    }
    /// Solve an indexed-union pattern: a declared union with at least one
    /// constructor alternative whose arguments mention unbound variables, such
    /// as `Option<T> | Option<U>` or `Vec<T> | i64`.
    ///
    /// Every actual member not covered by the concrete fixed part is assigned
    /// to exactly one pattern alternative with the same outer constructor, or
    /// to a bare variable. Each constructor alternative is then matched against
    /// its assigned members separately, and they must agree on every argument:
    /// constructor arguments are invariant, so `Option<i64> | Option<Bool>` is
    /// never collapsed into a single `Option<i64 | Bool>`. Bare variables must
    /// receive at least one member, as in the residual and partition rules;
    /// a constructor alternative may receive none, leaving its variables to
    /// other parameters. A member that fits a constructor alternative never
    /// goes to a bare variable (the most specific alternative covers, as with
    /// the fixed part), so `T | Option<U>` over `Bool | Option<i64>` has the
    /// single solution `T = Bool, U = i64`. The enumeration is bounded and
    /// canonical (members in normalized order, alternatives in generic
    /// declaration order), and assignments with the same substitution are one
    /// choice. Several surviving choices form one decision of the cross-
    /// parameter search in `infer`, which accepts only a unique solution.
    ///
    /// Returns `false` when some member has no alternative with its
    /// constructor; the ordinary coercion check then reports the mismatch.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn unify_indexed_union_pattern(
        &mut self,
        pattern: &ast::Type,
        mut variables: Vec<(&ast::Type, BindingId)>,
        mut shaped: Vec<&ast::Type>,
        fixed: Vec<&ast::Type>,
        actual: Type,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<bool> {
        // Canonical slot order: constructor alternatives by the first unbound
        // variable they mention in declaration order, then bare variables in
        // declaration order. Pattern operand order never matters.
        let declared = type_vars
            .iter()
            .chain(const_vars)
            .copied()
            .collect::<Vec<_>>();
        let unbound_in = |this: &Self, alternative: &ast::Type| {
            declared
                .iter()
                .copied()
                .filter(|id| {
                    !subst.types.contains_key(id)
                        && !subst.consts.contains_key(id)
                        && type_references_any_binder(
                            this.resolution,
                            alternative,
                            &BTreeSet::from([*id]),
                        )
                })
                .collect::<Vec<_>>()
        };
        let position = |id: &BindingId| {
            declared
                .iter()
                .position(|candidate| candidate == id)
                .unwrap_or(usize::MAX)
        };
        shaped.sort_by_key(|alternative| {
            unbound_in(self, alternative)
                .first()
                .map_or(usize::MAX, position)
        });
        variables.sort_by_key(|(_, id)| position(id));
        let mut decided = BTreeSet::new();
        for alternative in &shaped {
            decided.extend(unbound_in(self, alternative));
        }
        decided.extend(variables.iter().map(|(_, id)| *id));
        let slots = shaped
            .iter()
            .copied()
            .chain(variables.iter().map(|(variable, _)| *variable))
            .collect::<Vec<_>>();
        let constructors = shaped.len();

        let fixed_ty = if fixed.is_empty() {
            None
        } else {
            let mut types = Vec::with_capacity(fixed.len());
            for alternative in &fixed {
                types.push(self.types.ty_in(alternative, subst)?);
            }
            Some(self.types.union(types, span)?)
        };
        let mut residual = Vec::new();
        for member in self.types.union_members(actual) {
            if !fixed_ty.is_some_and(|fixed| self.subtype(member, fixed)) {
                residual.push(member);
            }
        }
        let names = |this: &Self| {
            decided
                .iter()
                .map(|id| this.resolution.bindings[*id].name.clone())
                .collect::<Vec<_>>()
                .join("', '")
        };
        // Candidate slots of every residual member. Like the fixed part, the
        // most specific alternative covers: a member that is an instance of a
        // constructor alternative goes to one of those, never to a bare
        // variable. Only members no constructor alternative can take are
        // partitioned among the bare variables.
        let mut candidates = Vec::with_capacity(residual.len());
        for member in &residual {
            let mut slots_for = Vec::new();
            let mut member_conflict: Option<Diagnostic> = None;
            for (slot, alternative) in shaped.iter().copied().enumerate() {
                if !self.union_pattern_head_matches(alternative, *member) {
                    continue;
                }
                let base = subst.clone();
                let trial = self.unify_trial(|this| {
                    let mut scratch = base;
                    this.unify_constructor_members(
                        alternative,
                        &[*member],
                        type_vars,
                        const_vars,
                        effect_vars,
                        &mut scratch,
                        span,
                    )
                    .map(|()| scratch)
                })?;
                // A nested choice that failed on its first option may still
                // fit; the replay decides it.
                match trial.result {
                    Ok(_) => slots_for.push(slot),
                    Err(_) if trial.nested_choice => slots_for.push(slot),
                    Err(error) => {
                        member_conflict.get_or_insert(error);
                    }
                }
            }
            if slots_for.is_empty() {
                slots_for.extend(constructors..slots.len());
            }
            if slots_for.is_empty() {
                // A member with the right constructor that is still no
                // instance of any alternative is a real conflict; one with no
                // matching constructor is left to the coercion check.
                if let Some(error) = member_conflict {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer type parameter(s) '{}' from the indexed union pattern {}: {} fits no alternative ({}). Specialize explicitly with '::<...>'",
                            names(self),
                            union_pattern_spelling(pattern),
                            self.types.name(*member),
                            error.message
                        ),
                    ));
                }
                return Ok(false);
            }
            candidates.push(slots_for);
        }

        fn enumerate(
            index: usize,
            candidates: &[Vec<usize>],
            assignment: &mut Vec<usize>,
            budget: &mut usize,
            out: &mut Vec<Vec<usize>>,
        ) -> bool {
            if *budget == 0 {
                return false;
            }
            *budget -= 1;
            if index == candidates.len() {
                out.push(assignment.clone());
                return true;
            }
            for slot in &candidates[index] {
                assignment.push(*slot);
                if !enumerate(index + 1, candidates, assignment, budget, out) {
                    return false;
                }
                assignment.pop();
            }
            true
        }
        const INDEXED_BUDGET: usize = 4096;
        let mut budget = INDEXED_BUDGET;
        let mut assignments = Vec::new();
        let complete = enumerate(
            0,
            &candidates,
            &mut Vec::new(),
            &mut budget,
            &mut assignments,
        );
        if !complete {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer type parameter(s) '{}' from the indexed union pattern: the bounded assignment search exhausted {INDEXED_BUDGET} steps. Specialize explicitly with '::<...>'",
                    names(self)
                ),
            ));
        }
        let group = |assignment: &[usize]| {
            let mut members = vec![Vec::new(); slots.len()];
            for (member, slot) in residual.iter().zip(assignment) {
                members[*slot].push(*member);
            }
            members
        };
        // Check every assignment in a scratch substitution with the replay
        // disabled, so a trial leaves no decision, effect evidence, or binding
        // marks behind. Assignments whose trial took the first of several
        // nested choices are kept unverified: the call-wide replay explores
        // their other nested choices when it commits them.
        let bare = variables.iter().map(|(_, id)| *id).collect::<Vec<_>>();
        let mut choices: Vec<Vec<Vec<Type>>> = Vec::new();
        let mut verified: Vec<IndexedSolutionKey> = Vec::new();
        let mut first_conflict: Option<Diagnostic> = None;
        for assignment in &assignments {
            let members = group(assignment);
            let base = subst.clone();
            let trial = self.unify_trial(|this| {
                let mut scratch = base;
                this.commit_indexed_assignment(
                    true,
                    &slots,
                    constructors,
                    &members,
                    &bare,
                    type_vars,
                    const_vars,
                    effect_vars,
                    &mut scratch,
                    span,
                )?;
                Ok(scratch)
            })?;
            match trial.result {
                Ok(scratch) if !trial.nested_choice => {
                    // Members of bare variables the trial left unbound are
                    // part of the solution's identity.
                    let open = members[constructors..]
                        .iter()
                        .zip(&bare)
                        .map(|(members, variable)| {
                            if scratch.types.contains_key(variable) {
                                Vec::new()
                            } else {
                                members.clone()
                            }
                        })
                        .collect::<Vec<_>>();
                    let key = (scratch, trial.effects, open);
                    if !verified.iter().any(|existing| {
                        same_solution(&existing.0, &key.0, type_vars, const_vars)
                            && existing.1 == key.1
                            && existing.2 == key.2
                    }) {
                        verified.push(key);
                        choices.push(members);
                    }
                }
                Ok(_) => choices.push(members),
                Err(_) if trial.nested_choice => choices.push(members),
                Err(error) => {
                    first_conflict.get_or_insert(error);
                }
            }
        }

        if choices.is_empty() {
            let pattern_name = union_pattern_spelling(pattern);
            let actual_name = self.types.name(actual);
            let detail = match first_conflict {
                Some(error) if error.message.contains("disagree on") => format!(
                    "{}. Constructor arguments are invariant, so alternatives such as Option<i64> | Option<Bool> are never merged into one Option<...>",
                    error.message
                ),
                Some(error) => error.message,
                None => "no assignment exists".to_string(),
            };
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer type parameter(s) '{}' from the indexed union pattern {pattern_name}: no assignment of the alternatives of {actual_name} is consistent ({detail}). Specialize explicitly with '::<...>'",
                    names(self)
                ),
            ));
        }
        let several = choices.len() > 1;
        let choice = self.union_partition_choice(choices.len())?;
        let members = choices.swap_remove(choice);
        // Commit the chosen assignment for real so binding marks, effect
        // evidence, and nested decisions are recorded exactly once.
        self.commit_indexed_assignment(
            false,
            &slots,
            constructors,
            &members,
            &bare,
            type_vars,
            const_vars,
            effect_vars,
            subst,
            span,
        )?;
        if several {
            // Parameters that mention a variable of a decision with several
            // choices must not commit to a tentative expected type, so the
            // replay can still reconsider it.
            self.partition_bound.extend(decided);
        }
        Ok(true)
    }
    /// Run a speculative unification with the choice replay disabled and
    /// restore every piece of inference state afterwards. Reports whether a
    /// nested partition took the first of several choices, and the effect
    /// evidence the trial produced. Layout budget exhaustion is not a
    /// rejected choice: it is returned as an error, because treating it as
    /// one could make a later choice look unique.
    pub(super) fn unify_trial<R>(
        &mut self,
        run: impl FnOnce(&mut Self) -> Result<R>,
    ) -> Result<UnifyTrial<R>> {
        let saved_plan_active = std::mem::replace(&mut self.unify_plan_active, false);
        let saved_open = std::mem::replace(&mut self.unify_open_choice, false);
        let saved_decisions = self.unify_decisions.len();
        let saved_effects = self.effect_constraints.len();
        let saved_rows = self.row_bound.clone();
        let saved_partitions = self.partition_bound.clone();
        let result = run(self);
        let nested_choice = self.unify_open_choice;
        let effects = self.effect_constraints[saved_effects..]
            .iter()
            .map(|constraint| (constraint.row.clone(), constraint.actual))
            .collect();
        self.unify_plan_active = saved_plan_active;
        self.unify_open_choice = saved_open;
        self.unify_decisions.truncate(saved_decisions);
        self.effect_constraints.truncate(saved_effects);
        self.row_bound = saved_rows;
        self.partition_bound = saved_partitions;
        if let Err(error) = &result
            && is_layout_budget_error(error)
        {
            return Err(error.clone());
        }
        Ok(UnifyTrial {
            result,
            nested_choice,
            effects,
        })
    }
    /// Apply one indexed-union assignment: every constructor alternative to
    /// its members, every nonempty bare variable to the union of its members.
    /// A bare variable with no member is accepted only when a constructor
    /// alternative bound it (`T | Option<T>` over `Option<i64>`). A `trial`
    /// leaves still-unbound bare variables unbound instead of creating their
    /// union type: speculative assignments must not use up the union layout
    /// budget, and the caller tells such trials apart by their members.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn commit_indexed_assignment(
        &mut self,
        trial: bool,
        slots: &[&ast::Type],
        constructors: usize,
        members: &[Vec<Type>],
        bare: &[BindingId],
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        for (slot, members) in members.iter().enumerate().take(constructors) {
            if members.is_empty() {
                continue;
            }
            self.unify_constructor_members(
                slots[slot],
                members,
                type_vars,
                const_vars,
                effect_vars,
                subst,
                span,
            )?;
        }
        for (index, members) in members.iter().enumerate().skip(constructors) {
            let variable = bare[index - constructors];
            if members.is_empty() {
                if subst.types.contains_key(&variable) {
                    continue;
                }
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "bare type parameter '{}' gets no alternative: every member fits a constructor alternative or the fixed part",
                        self.resolution.bindings[variable].name
                    ),
                ));
            }
            if trial && !subst.types.contains_key(&variable) {
                continue;
            }
            let bound = self.types.union(members.clone(), span)?;
            self.unify(
                slots[index],
                bound,
                type_vars,
                const_vars,
                effect_vars,
                subst,
                span,
            )?;
        }
        Ok(())
    }
    /// Match one constructor alternative of an indexed-union pattern against
    /// each member assigned to it. Every member must induce the same binding
    /// for each variable the alternative mentions: the arguments are
    /// invariant, so differing members never widen a variable to a union.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn unify_constructor_members(
        &mut self,
        alternative: &ast::Type,
        members: &[Type],
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        let mut merged = subst.clone();
        for member in members {
            let mut candidate = subst.clone();
            self.unify(
                alternative,
                *member,
                type_vars,
                const_vars,
                effect_vars,
                &mut candidate,
                span,
            )?;
            for (id, value) in &candidate.types {
                match merged.types.get(id) {
                    Some(previous) if previous != value => {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "the alternatives assigned to {} disagree on type parameter '{}': {} and {}",
                                union_pattern_spelling(alternative),
                                self.resolution.bindings[*id].name,
                                self.types.name(*previous),
                                self.types.name(*value)
                            ),
                        ));
                    }
                    Some(_) => {}
                    None => {
                        merged.types.insert(*id, *value);
                    }
                }
            }
            for (id, value) in &candidate.consts {
                match merged.consts.get(id) {
                    Some(previous) if previous != value => {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "the alternatives assigned to {} disagree on natural parameter '{}': {previous} and {value}",
                                union_pattern_spelling(alternative),
                                self.resolution.bindings[*id].name,
                            ),
                        ));
                    }
                    Some(_) => {}
                    None => {
                        merged.consts.insert(*id, *value);
                    }
                }
            }
            merged.effects.extend(candidate.effects);
        }
        // Matching ignores concrete argument mismatches, so check that every
        // member really is an instance of the solved alternative: `Pair<B,
        // Bool>` must not take `Pair<Bool, i64>`.
        if !self.mentions(alternative, type_vars, const_vars, effect_vars, &merged) {
            let solved = self.types.ty_in(alternative, &merged)?;
            for member in members {
                if !self.subtype(*member, solved) {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "{} is not an instance of {}",
                            self.types.name(*member),
                            union_pattern_spelling(alternative)
                        ),
                    ));
                }
            }
        }
        *subst = merged;
        Ok(())
    }
    /// First-order matching of a declared type against an actual type.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn unify(
        &mut self,
        pattern: &ast::Type,
        actual: Type,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        // First-order inference through a union actual. Instead of reading the
        // first union alternative that happens to bind a variable, every
        // alternative contributes a constraint. A variable must receive the
        // same binding from every alternative that constrains it; otherwise the
        // union does not determine one specialization and the call is
        // ambiguous. A bare type variable is not distributed: it captures the
        // whole normalized union, as before.
        let bare_variable = matches!(
            &pattern.kind,
            ast::TypeKind::Named { path, arguments }
                if arguments.is_empty()
                    && self.resolution.reference(pattern.span).is_some_and(|id| type_vars.contains(&id))
                    && path.len() == 1
        );
        if matches!(
            &pattern.kind,
            ast::TypeKind::Binary {
                op: crate::lexer::Kind::Pipe,
                ..
            }
        ) && self.unify_union_pattern(
            pattern,
            actual,
            type_vars,
            const_vars,
            effect_vars,
            subst,
            span,
        )? {
            return Ok(());
        }
        if let Type::Union(id) = actual
            && !bare_variable
        {
            let members = self.types.unions[id].members.clone();
            let mut merged = subst.clone();
            let mut constrained = false;
            for member in members {
                let mut candidate = subst.clone();
                self.unify(
                    pattern,
                    member,
                    type_vars,
                    const_vars,
                    effect_vars,
                    &mut candidate,
                    span,
                )?;
                for variable in type_vars {
                    if let Some(value) = candidate.types.get(variable).copied() {
                        match merged.types.get(variable).copied() {
                            Some(previous) if previous != value => {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "union alternatives disagree on type parameter '{}': one alternative requires {} and another requires {}. Specialize it explicitly with '::<...>'",
                                        self.resolution.bindings[*variable].name,
                                        self.types.name(previous),
                                        self.types.name(value)
                                    ),
                                ));
                            }
                            Some(_) => {}
                            None => {
                                merged.types.insert(*variable, value);
                                constrained = true;
                            }
                        }
                    }
                }
                for variable in const_vars {
                    if let Some(value) = candidate.consts.get(variable).copied() {
                        match merged.consts.get(variable).copied() {
                            Some(previous) if previous != value => {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "union alternatives disagree on natural parameter '{}': one alternative requires {previous} and another requires {value}",
                                        self.resolution.bindings[*variable].name
                                    ),
                                ));
                            }
                            Some(_) => {}
                            None => {
                                merged.consts.insert(*variable, value);
                                constrained = true;
                            }
                        }
                    }
                }
            }
            if constrained {
                *subst = merged;
            }
            return Ok(());
        }
        match &pattern.kind {
            ast::TypeKind::Lifetime(_) => {}
            ast::TypeKind::Named { path, arguments } => {
                let Some(id) = self.resolution.reference(pattern.span) else {
                    return Ok(());
                };
                // `T::Item` is an associated projection, not the binder `T`
                // itself: a concrete result type never determines `T` through
                // its projection. The projection is normalized after `T` is
                // inferred from the argument types.
                if path.len() == 2
                    && arguments.is_empty()
                    && self.resolution.bindings[id].kind == BindingKind::Generic
                    && self.resolution.bindings[id].name == path[0]
                {
                    return Ok(());
                }
                let arguments = arguments
                    .iter()
                    .filter(|argument| !matches!(argument.kind, ast::TypeKind::Lifetime(_)))
                    .collect::<Vec<_>>();
                if type_vars.contains(&id) && arguments.is_empty() {
                    if actual != Type::Never
                        && !matches!(actual, Type::Ref(_) | Type::RefMut(_))
                        && !actual.is_view()
                    {
                        let full = self.types.full(actual, span)?;
                        match subst.types.get(&id).copied() {
                            Some(bound) => {
                                if !self.subtype(full, bound) {
                                    return Err(Diagnostic::new(
                                        span,
                                        format!(
                                            "type parameter '{}' was inferred as {}, but another argument requires {}; the inference group is inconsistent. Specialize it explicitly with '::<...>'",
                                            self.resolution.bindings[id].name,
                                            self.types.name(bound),
                                            self.types.name(full)
                                        ),
                                    ));
                                }
                            }
                            None => {
                                subst.types.insert(id, full);
                            }
                        }
                    }
                    return Ok(());
                }
                let kind = self.resolution.bindings[id].kind;
                if kind == BindingKind::Alias {
                    if let Some((generics, body)) = self.types.alias_definition(id)
                        && generics.len() == arguments.len()
                    {
                        let map = generics
                            .iter()
                            .zip(arguments.iter().copied())
                            .map(|(generic, argument)| {
                                (self.resolution.binder(generic.span).unwrap(), argument)
                            })
                            .collect::<BTreeMap<_, _>>();
                        let expanded = substitute_alias_type(self.resolution, body, &map);
                        self.unify(
                            &expanded,
                            actual,
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                    return Ok(());
                }
                let b = &self.resolution.bindings[id];
                match (b.kind, b.name.as_str(), actual) {
                    (BindingKind::Builtin, "Code" | "CompiledCode", Type::Enum(layout))
                        if arguments.len() == 1 && self.types.enums[layout].definition == id =>
                    {
                        let signature = self.types.enums[layout].arguments[0];
                        self.unify(
                            arguments[0],
                            signature,
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                    (BindingKind::Builtin, "Box", Type::Box(p))
                    | (BindingKind::Builtin, "Vec", Type::Vec(p))
                        if arguments.len() == 1 =>
                    {
                        let pointee = self.types.pointees[p];
                        self.unify(
                            arguments[0],
                            pointee,
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                    (BindingKind::Data, _, _) => {
                        if let Some(layout) = actual.layout()
                            && self.types.enums[layout].definition == id
                        {
                            let actual_args = self.types.enums[layout].arguments.clone();
                            let actual_consts = self.types.enums[layout].consts.clone();
                            let kinds = self.types.generic_kinds(id);
                            let mut types = actual_args.iter();
                            let mut consts = actual_consts.iter();
                            for (argument, is_const) in arguments.iter().zip(kinds) {
                                if is_const {
                                    if let Some(value) = consts.next() {
                                        self.unify_length(
                                            argument, *value, const_vars, subst, span,
                                        )?;
                                    }
                                } else if let Some(actual) = types.next() {
                                    self.unify(
                                        argument,
                                        *actual,
                                        type_vars,
                                        const_vars,
                                        effect_vars,
                                        subst,
                                        span,
                                    )?;
                                }
                            }
                        }
                    }
                    _ => {}
                };
            }
            ast::TypeKind::Borrow {
                lifetime: _,
                mutable,
                inner,
            } => match (actual, &inner.kind) {
                (Type::Ref(p), _) | (Type::RefMut(p), _) => {
                    let pointee = self.types.pointees[p];
                    self.unify(
                        inner,
                        pointee,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                (Type::Slice(p), ast::TypeKind::Slice(element)) if !*mutable => {
                    let pointee = self.types.pointees[p];
                    self.unify(
                        element,
                        pointee,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                (Type::SliceMut(p), ast::TypeKind::Slice(element)) if *mutable => {
                    let pointee = self.types.pointees[p];
                    self.unify(
                        element,
                        pointee,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                _ => {}
            },
            ast::TypeKind::Function {
                parameters,
                result,
                effects,
                ..
            } => {
                let signature = match actual {
                    Type::Fn(id) | Type::Once(id) | Type::Multi(id) => {
                        self.types.function_types[id].clone()
                    }
                    _ => return Ok(()),
                };
                if signature.parameters.len() != parameters.len() {
                    return Ok(());
                }
                for (parameter, actual) in parameters.iter().zip(&signature.parameters) {
                    let (inner, _) = split_grade(&parameter.ty);
                    self.unify(
                        inner,
                        *actual,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                }
                self.unify(
                    result,
                    signature.result,
                    type_vars,
                    const_vars,
                    effect_vars,
                    subst,
                    span,
                )?;
                self.unify_effects(effects, signature.effects, effect_vars, subst, span)?;
            }
            ast::TypeKind::Tuple(items) => {
                if items.len() == 1 {
                    return Err(Diagnostic::new(
                        pattern.span,
                        "one-element tuples are not supported; write '()' for unit or omit the trailing comma",
                    ));
                }
                if let Some(layout) = actual.layout().filter(|l| self.types.enums[*l].tuple) {
                    let elements = self.types.enums[layout].arguments.clone();
                    if elements.len() != items.len() {
                        return Err(Diagnostic::new(
                            pattern.span,
                            format!(
                                "tuple type has {} elements, but the value has {}",
                                items.len(),
                                elements.len()
                            ),
                        ));
                    }
                    for (item, element) in items.iter().zip(elements) {
                        self.unify(
                            item,
                            element,
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                }
            }
            ast::TypeKind::Structural { fields, row, .. } => {
                if let Some(layout) = actual.layout().filter(|id| self.types.enums[*id].record) {
                    let variant = self.types.enums[layout].variants[0].clone();
                    for field in fields {
                        let Some(index) = variant.names.iter().position(|name| name == &field.name)
                        else {
                            continue;
                        };
                        self.unify(
                            &field.ty,
                            variant.fields[index],
                            type_vars,
                            const_vars,
                            effect_vars,
                            subst,
                            span,
                        )?;
                    }
                    // A named row variable preserves every actual field the
                    // declared row does not mention. It is monomorphized per
                    // concrete residual row, so the binding is a structural
                    // record type whose canonical row is exactly the residual.
                    // The complete descriptors carry each field's erased borrow
                    // label, keeping call sites with distinct labels in
                    // separate specializations.
                    if let Some(row) = row {
                        let Some(binder) = self.resolution.reference(row.span) else {
                            return Err(Diagnostic::new(
                                row.span,
                                "a row variable must be a declared type parameter",
                            ));
                        };
                        if type_vars.contains(&binder) {
                            let declared = fields
                                .iter()
                                .map(|field| field.name.as_str())
                                .collect::<BTreeSet<_>>();
                            let mut residual = Vec::new();
                            for (index, mut field) in self
                                .types
                                .record_row_fields(Type::Enum(layout))
                                .expect("a checked record has a canonical row")
                                .into_iter()
                                .enumerate()
                            {
                                if declared.contains(field.name.as_str()) {
                                    continue;
                                }
                                // An unannotated literal carries no declared
                                // identity for a borrowed residual field. Give
                                // it a stable local label for this inspected
                                // row shape so a `..r` specialization can carry
                                // it into a result; ownership still checks the
                                // actual origins, so the label is never origin
                                // evidence. The layout identity keeps repeated
                                // unlabelled rows matching each other without
                                // mixing an explicit caller label.
                                if field.lifetime.is_none() && field.ty.is_view() {
                                    field.lifetime = Some(format!(
                                        "<unlabelled structural row {layout} field {index}>"
                                    ));
                                }
                                residual.push(field);
                            }
                            let residual = self.types.structural_fields(residual, span)?;
                            match subst.types.get(&binder).copied() {
                                Some(bound) => {
                                    if self.types.structural_row_fields(bound)
                                        != self.types.structural_row_fields(residual)
                                    {
                                        return Err(Diagnostic::new(
                                            span,
                                            format!(
                                                "row variable '{}' was bound to {} by another argument, but this argument's residual row is {}; a row variable must receive the same residual row from every parameter. Specialize it explicitly with '::<...>'",
                                                self.resolution.bindings[binder].name,
                                                self.types.name(bound),
                                                self.types.name(residual)
                                            ),
                                        ));
                                    }
                                }
                                None => {
                                    subst.types.insert(binder, residual);
                                    self.row_bound.insert(binder);
                                }
                            }
                        }
                    }
                }
            }
            ast::TypeKind::Array(element, length)
                if let Some((_, capacity)) = runtime_length_parts(length) =>
            {
                // `[T; n <= C]` infers `T` and `C` from a runtime-length
                // actual. The binder itself is checked by the final argument
                // coercion against the caller's substituted binder.
                if let Some(layout) = actual.layout()
                    && self.types.enums[layout].runtime_length.is_some()
                    && let Some((actual_element, actual_capacity)) =
                        self.types.enums[layout].dynamic_array
                {
                    self.unify(
                        element,
                        actual_element,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                    self.unify_length(capacity, actual_capacity, const_vars, subst, span)?;
                }
            }
            ast::TypeKind::Array(element, length) => {
                if let Some(layout) = actual.layout()
                    && let Some((actual_element, actual_length)) = self.types.enums[layout].array
                {
                    self.unify(
                        element,
                        actual_element,
                        type_vars,
                        const_vars,
                        effect_vars,
                        subst,
                        span,
                    )?;
                    self.unify_length(length, actual_length, const_vars, subst, span)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    /// Accumulate one effect-row inclusion constraint from a callable
    /// argument. A declared row `{fixed | e1 | e2}` must cover the actual
    /// callable row. Constraints from every higher-order argument are solved
    /// together by [`Self::solve_effect_constraints`], so a variable that gets
    /// evidence from several positions is the union of that evidence instead of
    /// the first argument winning. Hiding an actual effect is impossible: a
    /// solution is accepted only when every constraint is covered.
    pub(super) fn unify_effects(
        &mut self,
        declared: &[ast::Type],
        actual: u16,
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        let row = crate::runtime_types::effect_row_term(self.resolution, declared)?;
        let variables = row.variables();
        if variables.is_empty() {
            // Concrete rows are still checked by the final arrow coercion.
            return Ok(());
        }
        for variable in &variables {
            if !effect_vars.contains(variable) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "effect parameter '{}' is not in scope here",
                        self.resolution.bindings[*variable].name
                    ),
                ));
            }
        }
        // A variable already fixed by an explicit specialization is evaluated
        // directly when the constraint is solved; it is not part of the
        // remaining assignment search.
        let unbound = variables
            .iter()
            .filter(|variable| !subst.effects.contains_key(variable))
            .count();
        if unbound == 0 {
            let covered = row.evaluate(&subst.effects).ok_or_else(|| {
                Diagnostic::new(span, "internal error: effect row could not be evaluated")
            })?;
            if actual & !covered != 0 {
                return Err(self.effect_row_mismatch(actual, covered, span));
            }
        } else {
            self.effect_constraints
                .push(EffectConstraint { row, actual, span });
        }
        Ok(())
    }
    pub(super) fn effect_row_mismatch(&self, actual: u16, covered: u16, span: Span) -> Diagnostic {
        let missing = actual & !covered;
        let names = crate::runtime_types::effect_name_list(self.resolution, missing);
        Diagnostic::new(
            span,
            format!(
                "effect row mismatch: the callable argument requires {{{}}}, which is not covered by the specialized effect row",
                names.join(", ")
            ),
        )
    }
    /// Solve accumulated row constraints with a per-bit Boolean solver.
    ///
    /// The effect universe is sixteen independent concrete bits and every row
    /// operation (union, subtraction, inclusion) is bitwise, so each bit can be
    /// solved on its own. For `n` unbound row variables one bit therefore has
    /// at most `2^n` assignments instead of the previous `16^n` whole-row
    /// enumeration. The documented bound is [`MAX_EFFECT_ROW_VARIABLES`]
    /// variables per call group; a larger group is rejected with an explicit
    /// request for specialization.
    ///
    /// A solver result must be *unique componentwise-minimal*: one variable
    /// assignment is a subset of every other valid assignment. For one bit the
    /// bitwise AND of every valid assignment is the unique minimal assignment
    /// exactly when it is itself valid; if it is not, several incomparable
    /// minimal assignments exist and the call is ambiguous. The same check is
    /// applied independently to every effect bit.
    ///
    /// A variable that no constraint mentions is solved from its domain alone:
    /// an unconstrained open row defaults to `{}` (the principal, least row),
    /// and a `<e: Effects + io>` lower bound defaults to exactly the required
    /// bits. This is sound because every row equation is an inclusion and the
    /// function body is rechecked against the chosen specialization; a body
    /// that performs an effect outside its declared row is rejected before the
    /// call can hide it.
    pub(super) fn solve_effect_constraints(
        &mut self,
        mark: usize,
        effect_generics: &[&ast::Generic],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        let constraints = self.effect_constraints.split_off(mark);
        let mut allowed: BTreeMap<BindingId, u16> = BTreeMap::new();
        let mut required: BTreeMap<BindingId, u16> = BTreeMap::new();
        for generic in effect_generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            let excluded =
                crate::runtime_types::effect_excludes(self.resolution, generic)?.unwrap_or(0);
            let included =
                crate::runtime_types::effect_includes(self.resolution, generic)?.unwrap_or(0);
            allowed.insert(binder, self.all_effects() & !excluded);
            required.insert(binder, included);
        }
        let mut unbound = Vec::new();
        for generic in effect_generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            if !subst.effects.contains_key(&binder) {
                unbound.push(binder);
            }
        }
        if unbound.is_empty() {
            for generic in effect_generics {
                let binder = self.resolution.binder(generic.span).unwrap();
                let included =
                    crate::runtime_types::effect_includes(self.resolution, generic)?.unwrap_or(0);
                if let Some(bits) = subst.effects.get(&binder) {
                    let missing = included & !*bits;
                    if missing != 0 {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "specialized effect row for '{}' omits {}, which is required by '<{}: Effects + {}>'",
                                generic.name,
                                effect_names(self.resolution, missing),
                                generic.name,
                                effect_names(self.resolution, included)
                            ),
                        ));
                    }
                }
            }
            for constraint in constraints {
                let covered = constraint.row.evaluate(&subst.effects).ok_or_else(|| {
                    Diagnostic::new(
                        constraint.span,
                        "internal error: effect row could not be evaluated",
                    )
                })?;
                if constraint.actual & !covered != 0 {
                    return Err(self.effect_row_mismatch(
                        constraint.actual,
                        covered,
                        constraint.span,
                    ));
                }
            }
            return Ok(());
        }
        if unbound.len() > MAX_EFFECT_ROW_VARIABLES {
            return Err(Diagnostic::new(
                span,
                format!(
                    "effect-row constraint group has {} unbound row variables, exceeding the per-bit solver bound of {MAX_EFFECT_ROW_VARIABLES}; specialize some rows explicitly with '::<...>'",
                    unbound.len()
                ),
            ));
        }
        let rows = constraints
            .iter()
            .map(|constraint| (&constraint.row, constraint.actual))
            .collect::<Vec<_>>();
        let chosen = match crate::runtime_types::solve_row_bits(
            &unbound,
            &allowed,
            &required,
            &subst.effects,
            &rows,
            self.all_effects(),
        ) {
            crate::runtime_types::RowSolve::Solved(chosen) => chosen,
            crate::runtime_types::RowSolve::Unsatisfiable => {
                let Some(first) = constraints.first() else {
                    return Err(Diagnostic::new(
                        span,
                        "no specialization of the effect row parameters satisfies their declared bounds",
                    ));
                };
                let reachable = first
                    .row
                    .evaluate_with(&mut |variable| {
                        subst
                            .effects
                            .get(&variable)
                            .copied()
                            .or_else(|| allowed.get(&variable).copied())
                    })
                    .unwrap_or(0);
                let excluded = first.actual & !reachable;
                if excluded != 0 {
                    let names = crate::runtime_types::effect_name_list(self.resolution, excluded);
                    fn effect_spelling(ty: &ast::Type) -> String {
                        match &ty.kind {
                            ast::TypeKind::Named { path, .. } => path.join("."),
                            ast::TypeKind::Binary {
                                op: crate::lexer::Kind::Pipe,
                                left,
                                right,
                            } => format!("{} | {}", effect_spelling(left), effect_spelling(right)),
                            ast::TypeKind::Binary {
                                op: crate::lexer::Kind::Minus,
                                left,
                                right,
                            } => {
                                format!("{} - {}", effect_spelling(left), effect_spelling(right))
                            }
                            _ => "concrete effects".to_owned(),
                        }
                    }
                    let variables = first
                        .row
                        .variables()
                        .iter()
                        .map(|variable| format!("'{}'", self.resolution.bindings[*variable].name))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let bound = first.row.variables().first().and_then(|variable| {
                        effect_generics
                            .iter()
                            .find(|generic| {
                                self.resolution.binder(generic.span).as_ref() == Some(variable)
                            })
                            .and_then(|generic| generic.excludes.as_ref())
                            .map(|excludes| {
                                format!(
                                    "<{}: Effects - {}>",
                                    self.resolution.bindings[*variable].name,
                                    effect_spelling(excludes)
                                )
                            })
                    });
                    let bound = bound.unwrap_or_else(|| format!("the bound on {variables}"));
                    return Err(Diagnostic::new(
                        first.span,
                        format!(
                            "effect {} is excluded by '{bound}', but the callable argument requires it",
                            names
                                .iter()
                                .map(|name| format!("'{name}'"))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    ));
                }
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "no specialization of the effect row parameters satisfies every callable argument; the actual row {:#06b} conflicts with another argument",
                        first.actual
                    ),
                ));
            }
            crate::runtime_types::RowSolve::Ambiguous => {
                let names = unbound
                    .iter()
                    .map(|variable| format!("'{}'", self.resolution.bindings[*variable].name))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "effect row parameters {names} have several incomparable minimal solutions; the callable arguments do not identify one row. Specialize them explicitly with '::<...>'"
                    ),
                ));
            }
        };
        for (variable, bits) in chosen {
            subst.effects.insert(variable, bits);
        }
        Ok(())
    }
    /// Infer or check one array-length expression against an actual length. A
    /// bare unbound const parameter is inferred; every other expression is
    /// evaluated with the current const substitution.
    pub(super) fn unify_length(
        &self,
        declared: &ast::Type,
        actual: usize,
        const_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<()> {
        if let ast::TypeKind::Named { arguments, .. } = &declared.kind
            && arguments.is_empty()
            && let Some(id) = self.resolution.reference(declared.span)
            && const_vars.contains(&id)
        {
            match subst.consts.get(&id) {
                Some(value) if *value != actual => {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "array length mismatch: a previous argument bound the length parameter to {value}, but this argument has length {actual}"
                        ),
                    ));
                }
                Some(_) => return Ok(()),
                None => {
                    subst.consts.insert(id, actual);
                    return Ok(());
                }
            }
        }
        match crate::length::eval_type(self.resolution, self.logical, &subst.consts, declared) {
            Ok(value) if value == actual => Ok(()),
            Ok(value) => Err(Diagnostic::new(
                span,
                format!("array length mismatch: expected {value}, found {actual}"),
            )),
            Err(error) => Err(Diagnostic::new(
                span,
                format!(
                    "cannot infer the array length parameter from length {actual} or check its declared length: {}",
                    error.message
                ),
            )),
        }
    }
    /// Replay the accumulated type constraints over every deterministic
    /// choice plan. Every multi-variable union partition and indexed-union
    /// assignment with several local choices is a decision point; the driver
    /// enumerates plans in lexicographic order and reruns the *whole*
    /// constraint list from `base`, so an earlier choice can change when a
    /// later parameter rejects it. Every surviving plan is collected and
    /// plans that give the same type/natural substitution are one solution,
    /// so the caller can accept exactly one solution and report several as
    /// ambiguous. At most [`UNIFY_BACKTRACK_BUDGET`] complete replays are
    /// attempted; exhausting the budget is an explicit diagnostic because
    /// uniqueness is then unknown.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn replay_unification(
        &mut self,
        constraints: &[(&ast::Type, Type)],
        result_hint: bool,
        base: Option<&crate::runtime_types::Subst>,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        span: Span,
    ) -> Result<Vec<ReplaySolution>> {
        let mut plan: Vec<usize> = Vec::new();
        let mut attempts = 0usize;
        let mut solutions: Vec<ReplaySolution> = Vec::new();
        let saved_rows = std::mem::take(&mut self.row_bound);
        loop {
            if attempts >= UNIFY_BACKTRACK_BUDGET {
                self.row_bound = saved_rows;
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cross-parameter type inference exhausted its {UNIFY_BACKTRACK_BUDGET}-replay budget while searching union partitions, so it cannot tell whether the solution is unique. Specialize the ambiguous parameters explicitly with '::<...>'"
                    ),
                ));
            }
            attempts += 1;
            self.unify_plan = plan.clone();
            self.unify_decisions.clear();
            self.unify_plan_active = true;
            let effect_mark = self.effect_constraints.len();
            let mut candidate = base.cloned().unwrap_or_default();
            let mut failure = None;
            let mut hint_rows = Vec::new();
            for (index, (pattern, actual)) in constraints.iter().enumerate() {
                if let Err(error) = self.unify(
                    pattern,
                    *actual,
                    type_vars,
                    const_vars,
                    effect_vars,
                    &mut candidate,
                    span,
                ) {
                    failure = Some(error);
                    break;
                }
                // As in the first pass, a wider-closed expected result row
                // must not fix a row variable before the arguments do.
                if index == 0 && result_hint {
                    for binder in std::mem::take(&mut self.row_bound) {
                        if let Some(bound) = candidate.types.remove(&binder) {
                            hint_rows.push((binder, bound));
                        }
                    }
                }
            }
            for (binder, bound) in hint_rows {
                candidate.types.entry(binder).or_insert(bound);
            }
            self.unify_plan_active = false;
            self.row_bound.clear();
            // Each plan's effect-row evidence is kept with its solution and
            // never accumulated across plans.
            let effects = self.effect_constraints.split_off(effect_mark);
            if let Some(error) = &failure
                && is_layout_budget_error(error)
            {
                self.row_bound = saved_rows;
                return Err(error.clone());
            }
            if failure.is_none() {
                let key = effects
                    .iter()
                    .map(|constraint| (constraint.row.clone(), constraint.actual))
                    .collect::<Vec<_>>();
                let duplicate = solutions.iter().any(|existing| {
                    same_solution(&existing.subst, &candidate, type_vars, const_vars)
                        && existing
                            .effects
                            .iter()
                            .map(|constraint| (constraint.row.clone(), constraint.actual))
                            .eq(key.iter().cloned())
                });
                if !duplicate {
                    let valid = self.solution_satisfies(
                        constraints,
                        result_hint,
                        &candidate,
                        type_vars,
                        const_vars,
                        effect_vars,
                    )?;
                    solutions.push(ReplaySolution {
                        subst: candidate,
                        effects,
                        valid,
                    });
                    // Two valid solutions already decide ambiguity.
                    if solutions.iter().filter(|solution| solution.valid).count() > 1 {
                        self.row_bound = saved_rows;
                        return Ok(solutions);
                    }
                }
            }
            // Advance the most recent decision that still has an untried
            // choice, dropping every later decision from the plan.
            let mut advanced = false;
            let mut index = self.unify_decisions.len();
            while index > 0 {
                index -= 1;
                let cardinality = self.unify_decisions[index];
                let current = plan.get(index).copied().unwrap_or(0);
                if current + 1 < cardinality {
                    // Earlier decisions keep their current choice, including
                    // the implicit zero of a plan shorter than this index.
                    plan.resize(index, 0);
                    plan.push(current + 1);
                    advanced = true;
                    break;
                }
            }
            if !advanced {
                self.row_bound = saved_rows;
                return Ok(solutions);
            }
        }
    }
    /// Whether a replayed substitution passes the subtype checks the call
    /// will make: every argument against its instantiated parameter type,
    /// and the instantiated result against the expected type. First-order
    /// matching ignores variance, so this is what separates a real solution
    /// from one that only matched leniently.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn solution_satisfies(
        &mut self,
        constraints: &[(&ast::Type, Type)],
        result_hint: bool,
        candidate: &crate::runtime_types::Subst,
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
    ) -> Result<bool> {
        for (index, (pattern, actual)) in constraints.iter().enumerate() {
            if self.mentions(pattern, type_vars, const_vars, effect_vars, candidate) {
                continue;
            }
            let declared = match self.types.ty_in(pattern, candidate) {
                Ok(declared) => declared,
                Err(error) if is_layout_budget_error(&error) => return Err(error),
                Err(_) => continue,
            };
            let holds = if index == 0 && result_hint {
                self.subtype(declared, *actual)
            } else {
                self.subtype(*actual, declared)
            };
            if !holds {
                return Ok(false);
            }
        }
        Ok(true)
    }
    /// Check values against declared types, inferring type and const variables
    /// left to right. Returns type, grade, and const arguments plus the checked
    /// values. `base` carries substitutions already fixed by the callee, such as
    /// the trait arguments of an inherited default method; declared parameter
    /// types that mention them resolve instead of looking like unbound type
    /// parameters.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer(
        &mut self,
        generics: &[ast::Generic],
        explicit: Option<&[ast::Type]>,
        pairs: &[(&ast::Type, &ast::Expr)],
        result: Option<(&ast::Type, Type)>,
        freshen_binders: Option<&BTreeSet<String>>,
        self_type: Option<Type>,
        base: Option<&crate::runtime_types::Subst>,
        what: &str,
        span: Span,
    ) -> Result<Inferred> {
        // A nested call inside an argument runs its own inference; keep the
        // enclosing call's tentative-binding marks intact across it.
        let partitions = std::mem::take(&mut self.partition_bound);
        let rows = std::mem::take(&mut self.row_bound);
        let open = std::mem::replace(&mut self.unify_open_choice, false);
        let inferred = self.infer_inner(
            generics,
            explicit,
            pairs,
            result,
            freshen_binders,
            self_type,
            base,
            what,
            span,
        );
        self.partition_bound = partitions;
        self.row_bound = rows;
        self.unify_open_choice = open;
        inferred
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_inner(
        &mut self,
        generics: &[ast::Generic],
        explicit: Option<&[ast::Type]>,
        pairs: &[(&ast::Type, &ast::Expr)],
        result: Option<(&ast::Type, Type)>,
        freshen_binders: Option<&BTreeSet<String>>,
        self_type: Option<Type>,
        base: Option<&crate::runtime_types::Subst>,
        what: &str,
        span: Span,
    ) -> Result<Inferred> {
        let mut type_generics = Vec::new();
        let mut const_generics = Vec::new();
        let mut grade_generics = Vec::new();
        let mut effect_generics = Vec::new();
        for generic in generics {
            if is_grade_generic(self.resolution, generic) {
                grade_generics.push(generic);
            } else if is_const_generic(self.resolution, generic) {
                const_generics.push(generic);
            } else if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                effect_generics.push(generic);
            } else {
                type_generics.push(generic);
            }
        }
        let type_vars = type_generics
            .iter()
            .map(|generic| self.resolution.binder(generic.span).unwrap())
            .collect::<Vec<_>>();
        let const_vars = const_generics
            .iter()
            .map(|generic| self.resolution.binder(generic.span).unwrap())
            .collect::<Vec<_>>();
        let effect_vars = effect_generics
            .iter()
            .map(|generic| self.resolution.binder(generic.span).unwrap())
            .collect::<Vec<_>>();
        let mut subst = base.cloned().unwrap_or_default();
        subst.self_type = self_type;
        subst.lengths = std::mem::take(&mut self.pending_lengths);
        let constraint_mark = self.effect_constraints.len();
        // `(declared pattern, actual type)` for every parameter and result
        // hint. A failed unification is deferred only long enough for the
        // bounded cross-parameter replay to try another partition.
        let mut constraints: Vec<(&ast::Type, Type)> = Vec::new();
        let mut unify_error: Option<Diagnostic> = None;
        let mut hint_rows: Vec<(BindingId, Type)> = Vec::new();
        self.partition_bound.clear();
        self.row_bound.clear();
        self.unify_open_choice = false;
        let mut grade_arguments = Vec::new();
        if let Some(list) = explicit {
            if list.len() != generics.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "{what} expects {} type/grade/const/effect arguments, found {}",
                        generics.len(),
                        list.len()
                    ),
                ));
            }
            let mut type_index = 0;
            let mut const_index = 0;
            for (generic, argument) in generics.iter().zip(list) {
                if is_grade_generic(self.resolution, generic) {
                    grade_arguments.push(grades::evaluate(
                        self.resolution,
                        &self.grades,
                        argument,
                    )?);
                } else if is_const_generic(self.resolution, generic) {
                    let value = crate::length::eval_type(
                        self.resolution,
                        self.logical,
                        &self.consts,
                        argument,
                    )?;
                    subst.consts.insert(const_vars[const_index], value);
                    const_index += 1;
                } else if crate::runtime_types::is_effect_generic(self.resolution, generic) {
                    let binder = self.resolution.binder(generic.span).unwrap();
                    let value = crate::runtime_types::effect_bits_with(
                        self.resolution,
                        std::slice::from_ref(argument),
                        &self.effect_arguments,
                    )?;
                    subst.effects.insert(binder, value);
                } else {
                    let ty = self.ty(argument)?;
                    let ty = self.types.full(ty, span)?;
                    subst.types.insert(type_vars[type_index], ty);
                    type_index += 1;
                }
            }
        } else {
            // Record every type constraint so a later cross-parameter replay
            // can solve the whole group from the base substitution instead of
            // committing to the first union partition.
            if let Some((declared, expected)) = result {
                constraints.push((declared, expected));
                let before = subst.clone();
                if let Err(error) = self.unify(
                    declared,
                    expected,
                    &type_vars,
                    &const_vars,
                    &effect_vars,
                    &mut subst,
                    span,
                ) {
                    subst = before;
                    unify_error.get_or_insert(error);
                }
                // The expected result type may be *wider-closed* than the
                // call's real result (`let n: struct { x: i64 } = keep(w)`
                // drops fields afterwards). It must not fix a row variable
                // before the arguments do, so set those bindings aside and
                // use them only for variables no argument binds.
                for binder in std::mem::take(&mut self.row_bound) {
                    if let Some(bound) = subst.types.remove(&binder) {
                        hint_rows.push((binder, bound));
                    }
                }
            }
        }
        let parameter_grade_exprs = pairs
            .iter()
            .map(|(declared, _)| split_grade(declared).1.cloned())
            .collect::<Vec<_>>();
        let mut values = Vec::new();
        // Unannotated noncapturing lambdas whose parameter type still mentions
        // an unsolved generic are checked after the other arguments, with
        // the parameter and result types those arguments fix
        // (I-LAMBDA-INFER). Evaluation order is unchanged: only the checking
        // order differs, and such a lambda captures nothing.
        let mut postponed: Vec<(usize, &ast::Type, &ast::Expr)> = Vec::new();
        for (declared, value) in pairs.iter() {
            let (declared, _) = split_grade(declared);
            if let ast::ExprKind::Lambda(lambda) = &value.kind
                && lambda_has_holes(lambda)
                && self.lambda_captures(lambda, false).is_empty()
                && self.mentions(declared, &type_vars, &const_vars, &effect_vars, &subst)
            {
                postponed.push((values.len(), declared, value));
                values.push(Expr {
                    kind: ExprKind::Constant(0),
                    ty: Type::Unit,
                    span: value.span,
                    resource: None,
                });
                continue;
            }
            // A runtime-length array parameter takes the ordinary contextual
            // path below, so a literal argument gets the length-proof rule.
            if let (ast::TypeKind::Array(element, length), ast::ExprKind::Array(items)) =
                (&declared.kind, &value.kind)
                && runtime_length_parts(length).is_none()
            {
                let checked = self.infer_array_argument(
                    element,
                    length,
                    items,
                    &type_vars,
                    &const_vars,
                    &effect_vars,
                    &mut subst,
                    span,
                )?;
                constraints.push((declared, checked.ty));
                values.push(checked);
                continue;
            }
            let tentative_partition =
                type_references_any_binder(self.resolution, declared, &self.partition_bound);
            let tentative_row =
                type_references_any_binder(self.resolution, declared, &self.row_bound);
            let wanted = if tentative_partition
                || tentative_row
                || self.mentions(declared, &type_vars, &const_vars, &effect_vars, &subst)
            {
                None
            } else {
                Some(self.types.ty_in(declared, &subst)?)
            };
            // A call argument's record lifetimes are instantiated from the
            // argument value, not forced to the callee's declaration names.
            // Freshening keeps the construction checked against local
            // provenance while the call boundary relates the two sets.
            let wanted = match (wanted, freshen_binders) {
                (Some(ty), Some(binders)) => {
                    Some(self.types.freshen_borrows(ty, binders, value.span)?)
                }
                (other, _) => other,
            };
            // A capability argument must be a capability local, passed as is.
            let capability_parameter = matches!(declared.kind, ast::TypeKind::Capability { .. });
            if capability_parameter {
                let slot = matches!(value.kind, ast::ExprKind::Name(_))
                    .then(|| self.resolution.reference(value.span))
                    .flatten()
                    .and_then(|id| self.slots.get(&id).copied())
                    .filter(|slot| self.capability_slots.contains(slot));
                let Some(slot) = slot else {
                    return Err(Diagnostic::new(
                        value.span,
                        "a 'cap' parameter takes a capability bound by 'handle Op as op' or a 'cap' parameter, passed by name",
                    ));
                };
                // A capturing handler stays in its dynamic frame; the callee
                // gets a trampoline that performs the operation there. The
                // argument is a placeholder (the capability local at the
                // parameter's type) until the body's await points are marked.
                if let Some((operation, arrow, effects)) =
                    self.capability_framed.get(&slot).copied()
                {
                    let (_, ty) = self.capability_thunk(operation, arrow, effects, value.span)?;
                    let Some(wanted) = wanted else {
                        return Err(Diagnostic::new(
                            value.span,
                            "a capturing capability needs a concrete 'cap' parameter",
                        ));
                    };
                    if !self.subtype(ty, wanted) {
                        return Err(Diagnostic::new(
                            value.span,
                            "this capability's handler is capturing and reaches callees through its frame: pass it to a 'cap Op ! {..}' parameter whose row holds the handler's own effects",
                        ));
                    }
                    constraints.push((declared, wanted));
                    values.push(Expr {
                        kind: ExprKind::Local(slot),
                        ty: wanted,
                        span: value.span,
                        resource: None,
                    });
                    continue;
                }
                if !self.capability_passable.contains(&slot)
                    && !self.capability_resumable.contains(&slot)
                {
                    return Err(Diagnostic::new(
                        value.span,
                        "this capability's handler is capturing or multishot, or it runs in place and performs declared operations, so it can only be performed in its own 'handle' body",
                    ));
                }
                self.capability_argument = true;
            }
            let value = self.expr_expected(value, wanted);
            self.capability_argument = false;
            let value = value?;
            constraints.push((declared, value.ty));
            let before = subst.clone();
            if let Err(error) = self.unify(
                declared,
                value.ty,
                &type_vars,
                &const_vars,
                &effect_vars,
                &mut subst,
                span,
            ) {
                subst = before;
                unify_error.get_or_insert(error);
            }
            values.push(value);
        }
        for (index, declared, value) in postponed {
            let ast::ExprKind::Lambda(lambda) = &value.kind else {
                unreachable!("only lambdas are postponed")
            };
            let mut hint = LambdaHint::default();
            if let ast::TypeKind::Function {
                parameters, result, ..
            } = &declared.kind
                && parameters.len() == lambda.parameters.len()
            {
                for parameter in parameters {
                    let (parameter, _) = split_grade(&parameter.ty);
                    hint.parameters.push(
                        if self.mentions(parameter, &type_vars, &const_vars, &effect_vars, &subst) {
                            None
                        } else {
                            Some(self.types.ty_in(parameter, &subst)?)
                        },
                    );
                }
                let (result, _) = split_grade(result);
                if !self.mentions(result, &type_vars, &const_vars, &effect_vars, &subst) {
                    hint.result = Some(self.types.ty_in(result, &subst)?);
                }
            }
            self.lambda_hint = Some(hint);
            let checked = self.expr_expected(value, None);
            self.lambda_hint = None;
            let checked = checked?;
            constraints.push((declared, checked.ty));
            let before = subst.clone();
            if let Err(error) = self.unify(
                declared,
                checked.ty,
                &type_vars,
                &const_vars,
                &effect_vars,
                &mut subst,
                span,
            ) {
                subst = before;
                unify_error.get_or_insert(error);
            }
            values[index] = checked;
        }
        for (binder, bound) in hint_rows {
            subst.types.entry(binder).or_insert(bound);
        }
        if explicit.is_some()
            && let Some(error) = unify_error.take()
        {
            return Err(error);
        }
        if unify_error.is_some() || self.unify_open_choice {
            // A failed first pass, or a first pass that took one of several
            // choices: search every deterministic choice plan. Inference is
            // principal for this fragment: it accepts only when exactly one
            // substitution satisfies the whole constraint group.
            let mut replay_base = base.cloned().unwrap_or_default();
            replay_base.self_type = self_type;
            let solutions = self.replay_unification(
                &constraints,
                result.is_some() && explicit.is_none(),
                Some(&replay_base),
                &type_vars,
                &const_vars,
                &effect_vars,
                span,
            )?;
            // Plans that pass the call's subtype checks are the solutions;
            // only when none does are the leniently matched ones reported.
            let complete = solutions.iter().filter(|solution| solution.valid).count() < 2;
            let mut solutions = if solutions.iter().any(|solution| solution.valid) {
                solutions
                    .into_iter()
                    .filter(|solution| solution.valid)
                    .collect::<Vec<_>>()
            } else {
                solutions
            };
            if solutions.len() > 1 {
                let spell = |this: &Self, solution: &crate::runtime_types::Subst| {
                    type_vars
                        .iter()
                        .filter_map(|var| {
                            solution.types.get(var).map(|ty| {
                                format!(
                                    "{} = {}",
                                    this.resolution.bindings[*var].name,
                                    this.types.name(*ty)
                                )
                            })
                        })
                        .chain(const_vars.iter().filter_map(|var| {
                            solution.consts.get(var).map(|value| {
                                format!("{} = {value}", this.resolution.bindings[*var].name)
                            })
                        }))
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                let mut spelled = solutions
                    .iter()
                    .take(3)
                    .map(|solution| spell(self, &solution.subst))
                    .collect::<Vec<_>>();
                if spelled.windows(2).any(|pair| pair[0] == pair[1]) {
                    for (index, text) in spelled.iter_mut().enumerate() {
                        if !text.is_empty() {
                            text.push_str(", ");
                        }
                        text.push_str(&format!("effect-row assignment #{}", index + 1));
                    }
                }
                let shown = spelled
                    .iter()
                    .map(|text| format!("[{text}]"))
                    .collect::<Vec<_>>()
                    .join(" or ");
                let more = if complete && solutions.len() > 3 {
                    format!(" (and {} more)", solutions.len() - 3)
                } else {
                    String::new()
                };
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "type inference for {what} is ambiguous: the union alternatives can be split as {shown}{more}, and no argument or expected type decides between them. Specialize the type arguments explicitly with '::<...>'"
                    ),
                ));
            }
            match solutions.pop() {
                Some(replayed) => {
                    subst = replayed.subst;
                    // The chosen plan's effect evidence replaces the first
                    // pass's, which may belong to another choice.
                    self.effect_constraints.truncate(constraint_mark);
                    self.effect_constraints.extend(replayed.effects);
                }
                None => {
                    let Some(error) = unify_error else {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "type inference for {what} found no solution when it searched every union partition, although the first pass matched. Specialize the type arguments explicitly with '::<...>'"
                            ),
                        ));
                    };
                    if self.partition_bound.is_empty() {
                        return Err(error);
                    }
                    let names = self
                        .partition_bound
                        .iter()
                        .map(|binder| format!("'{}'", self.resolution.bindings[*binder].name))
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "no partition of the union alternatives satisfies every parameter for {names}; the bounded cross-parameter search tried every deterministic partition. Specialize the type arguments explicitly with '::<...>'"
                        ),
                    ));
                }
            }
        }
        self.solve_effect_constraints(constraint_mark, &effect_generics, &mut subst, span)?;
        // General grade inference for direct calls: solve grade parameters from
        // explicitly graded arguments. All equations are accumulated and solved
        // simultaneously; an ungraded argument never invents a grade.
        if explicit.is_none() && !grade_generics.is_empty() {
            let binders = grade_generics
                .iter()
                .map(|generic| self.resolution.binder(generic.span).unwrap())
                .collect::<Vec<_>>();
            let constraints = parameter_grade_exprs
                .iter()
                .zip(&values)
                .filter_map(|(grade_expr, value)| {
                    let grade_expr = grade_expr.as_ref()?;
                    let actual = self.expression_grade(value)?;
                    Some((grade_expr, actual))
                })
                .collect::<Vec<_>>();
            let solved = grades::solve_all(self.resolution, &self.grades, &binders, &constraints)?
                .unwrap_or_default();
            for (generic, binder) in grade_generics.iter().zip(&binders) {
                let Some(value) = solved.get(binder) else {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer usage grade parameter '{}' of {what}: no argument is explicitly graded @[{}] or its grade equation has no unique solution in the decidable natural/finite-algebra fragment. Specialize it explicitly with '::<...>'",
                            generic.name, generic.name
                        ),
                    ));
                };
                grade_arguments.push(*value);
            }
        }
        let mut type_arguments = Vec::new();
        for (var, generic) in type_vars.iter().zip(&type_generics) {
            let Some(ty) = subst.types.get(var) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot infer type parameter '{}' of {what}; write explicit type arguments with ::<...>",
                        generic.name
                    ),
                ));
            };
            type_arguments.push(*ty);
        }
        let mut const_arguments = Vec::new();
        for (var, generic) in const_vars.iter().zip(&const_generics) {
            let Some(value) = subst.consts.get(var) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot infer natural length parameter '{}' of {what}; pass an inline array argument or specialize it explicitly with ::<...>",
                        generic.name
                    ),
                ));
            };
            const_arguments.push(*value);
        }
        let mut effect_arguments = Vec::new();
        for (var, generic) in effect_vars.iter().zip(&effect_generics) {
            let Some(value) = subst.effects.get(var) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot infer effect row parameter '{}' of {what}; pass a callable argument whose effects identify the row, or specialize it explicitly with ::<...>",
                        generic.name
                    ),
                ));
            };
            effect_arguments.push(*value);
        }
        Ok((
            type_arguments,
            grade_arguments,
            const_arguments,
            effect_arguments,
            values,
        ))
    }
    /// Check an inline array literal directly against a parametric array
    /// parameter such as `[T; N]`. This is what makes length inference
    /// unambiguous: the literal's length binds `N`, and its first element
    /// binds an unconstrained element type. Without this path the literal
    /// would default to a `Vec<T>` because there is no complete expected type.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_array_argument(
        &mut self,
        element_decl: &ast::Type,
        length_decl: &ast::Type,
        items: &[ast::Expr],
        type_vars: &[BindingId],
        const_vars: &[BindingId],
        effect_vars: &[BindingId],
        subst: &mut crate::runtime_types::Subst,
        span: Span,
    ) -> Result<Expr> {
        let known = if self.mentions(element_decl, type_vars, const_vars, effect_vars, subst) {
            None
        } else {
            Some(self.types.ty_in(element_decl, subst)?)
        };
        let mut checked = Vec::new();
        for item in items {
            if let (
                ast::TypeKind::Array(inner_element, inner_length),
                ast::ExprKind::Array(inner),
            ) = (&element_decl.kind, &item.kind)
            {
                checked.push(self.infer_array_argument(
                    inner_element,
                    inner_length,
                    inner,
                    type_vars,
                    const_vars,
                    effect_vars,
                    subst,
                    span,
                )?);
            } else {
                checked.push(self.expr_expected(item, known)?);
            }
        }
        let element = match known {
            Some(element) => element,
            None => {
                let Some(first) = checked.iter().find(|value| value.ty != Type::Never) else {
                    return Err(Diagnostic::new(
                        span,
                        "cannot infer the element type of an empty array literal; annotate the binding or specialize the function explicitly",
                    ));
                };
                let first = self.types.full(first.ty, span)?;
                self.unify(
                    element_decl,
                    first,
                    type_vars,
                    const_vars,
                    effect_vars,
                    subst,
                    span,
                )?;
                if self.mentions(element_decl, type_vars, const_vars, effect_vars, subst) {
                    return Err(Diagnostic::new(
                        span,
                        "cannot infer the array element type; write explicit type arguments with ::<...>",
                    ));
                }
                self.types.ty_in(element_decl, subst)?
            }
        };
        self.unify_length(length_decl, items.len(), const_vars, subst, span)?;
        if self.const_mentions(length_decl, const_vars, subst) {
            return Err(Diagnostic::new(
                span,
                "cannot infer the natural array length parameter; write explicit specialization with ::<...>",
            ));
        }
        let ty = self.types.array(element, items.len(), span)?;
        let Type::Enum(layout) = ty else {
            unreachable!("array construction returns an enum layout")
        };
        let mut diverges = false;
        let mut fields = Vec::with_capacity(checked.len());
        for value in checked {
            let at = value.span;
            let value = self.coerce(value, element, at)?;
            diverges |= value.ty == Type::Never;
            fields.push(value);
        }
        Ok(Expr {
            kind: ExprKind::Construct {
                enum_id: layout,
                tag: 0,
                fields,
            },
            ty: if diverges {
                Type::Never
            } else {
                Type::Enum(layout)
            },
            span,
            resource: None,
        })
    }
}
