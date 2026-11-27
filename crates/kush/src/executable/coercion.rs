//! Subtyping, expected-type checks, coercions, call lifetimes and adapters.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Normalized subtyping over variant sets, heterogeneous unions, and
    /// `Never`. Intersections are already eliminated during type lowering.
    pub(super) fn subtype(&self, actual: Type, expected: Type) -> bool {
        self.types.subtype(actual, expected)
    }
    pub(super) fn expect(&self, actual: Type, expected: Type, span: Span) -> Result<()> {
        if self.subtype(actual, expected) {
            return Ok(());
        }
        let mut message = format!(
            "type mismatch: expected {}, found {}",
            self.types.name(expected),
            self.types.name(actual)
        );
        let binder = |ty: Type| {
            ty.layout()
                .and_then(|id| self.types.enums[id].runtime_length)
        };
        if let (Some(left), Some(right)) = (binder(expected), binder(actual))
            && left != right
            && self.resolution.bindings[left].name == self.resolution.bindings[right].name
        {
            message.push_str(&format!(
                " (the lengths are two different bindings both named '{}'; a shadowed binding is a new length)",
                self.resolution.bindings[left].name
            ));
        }
        if actual.layout().is_some()
            && actual.layout() == expected.layout()
            && self.mask(actual) & self.mask(expected) != 0
        {
            let extra = self.mask(actual) & !self.mask(expected);
            let missing = self.types.name(crate::runtime_types::refine(
                &self.types.enums,
                actual.layout().unwrap(),
                extra,
            ));
            message.push_str(&format!(" (the value may also be {missing})"));
        }
        Err(Diagnostic::new(span, message))
    }
    /// A subtype whose runtime representation is already identical: a variant
    /// mask can be typed as the full enum with no tag change.
    pub(super) fn same_layout(&self, actual: Type, expected: Type) -> bool {
        self.types.same_representation(actual, expected)
            || (actual.layout().is_some()
                && actual.layout() == expected.layout()
                && self.subtype(actual, expected))
    }
    /// Whether a structural row can be compared with `==`: every leaf is a
    /// copyable scalar (integers, Char, Bool, Unit) and nested structural rows
    /// recurse. Floating-point leaves are excluded because their equality is
    /// numeric (`-0.0 == 0.0`, NaN) while the inline representation compares
    /// raw words; owning, borrowed, union, callable, and nominal fields are
    /// excluded so equality never moves or inspects an opaque payload.
    pub(super) fn structurally_comparable(&self, ty: Type) -> bool {
        let Some(layout) = ty.layout().filter(|id| self.types.enums[*id].structural) else {
            return false;
        };
        self.types.enums[layout].variants[0]
            .fields
            .iter()
            .all(|field| {
                if field.layout().is_some() {
                    self.structurally_comparable(*field)
                } else {
                    matches!(
                        field,
                        Type::I64 | Type::Int(_) | Type::Char | Type::Bool | Type::Unit
                    )
                }
            })
    }
    /// Check a same-scope lifetime conversion with the occurrence-specific
    /// witness. Call and coercion expressions are skipped because a callee's
    /// declared labels are instantiated by the actual arguments; ownership
    /// retains that provenance independently. Every label reachable from the
    /// two occurrences is classified from this function's declared lifetime
    /// binders plus compiler-internal elided identities. A label that is not
    /// declared here belongs to a callee or nested instantiation and defers
    /// per occurrence to ownership evidence; every same-scope label that this
    /// witness can classify must still satisfy the conversion.
    pub(super) fn check_static_lifetime_witness(
        &self,
        value: &Expr,
        expected: Type,
        span: Span,
    ) -> Result<()> {
        if self.call_boundary > 0 {
            return Ok(());
        }
        if !crate::runtime_types::has_borrow(self.types, value.ty)
            && !crate::runtime_types::has_borrow(self.types, expected)
        {
            return Ok(());
        }
        // A freshly generated argument placeholder is not an occurrence
        // identity: the enclosing call relates the value's real provenance to
        // the callee binder through its occurrence constraints. Nested block,
        // lambda, `if`, and `match` checks still run normally because this
        // exemption is keyed to the placeholder itself, not to a call-wide
        // suppression depth.
        if crate::runtime_types::borrow_lifetimes(self.types, expected)
            .iter()
            .any(|label| label.starts_with("<argument "))
        {
            return Ok(());
        }
        // Shape compatibility owns its own diagnostics. This judgment is a
        // refinement, never a replacement for erased structure.
        if !self.subtype(value.ty, expected) {
            return Ok(());
        }
        let mut env = crate::variance::LabelEnv::new();
        for name in &self.declared_lifetimes {
            env.free(name);
        }
        for name in self.parameter_lifetimes.iter().flatten() {
            env.free(name);
        }
        if let Some(name) = &self.result_lifetime {
            env.free(name);
        }
        let evidence = crate::variance::ClosureEvidence {
            outlives: |long: &str, short: &str| {
                crate::executable::outlives(&self.lifetime_bounds, long, short)
            },
        };
        let source = crate::variance::TypeOccurrence::new(value.ty);
        let target = crate::variance::TypeOccurrence::new(expected);
        match crate::variance::witness(self.types, &source, &target, &env, &evidence) {
            Ok(_) => Ok(()),
            Err(error) => Err(Diagnostic::new(
                span,
                format!(
                    "lifetime mismatch: {} is not a lifetime-compatible {}",
                    self.types.name(value.ty),
                    self.types.name(expected)
                ),
            )
            .with_note(span, error.message())),
        }
    }
    /// Coerce an expression into a callee parameter. Callee-declared lifetime
    /// labels are instantiated by this call; the callable contract and the
    /// ownership provenance mapping own that relation, so the same-scope
    /// contextual witness must not reinterpret them as caller labels.
    pub(super) fn coerce_argument(
        &mut self,
        value: Expr,
        expected: Type,
        span: Span,
    ) -> Result<Expr> {
        self.call_boundary += 1;
        let result = self.coerce(value, expected, span);
        self.call_boundary -= 1;
        result
    }
    /// Record one callee binder occurrence against the actual label supplied
    /// by the argument value. Only labels declared by the callee are
    /// instantiated; labels that came from a caller type argument stay rigid
    /// and keep their ordinary same-scope obligations.
    pub(super) fn record_call_lifetime_occurrence(
        &self,
        callee: Option<&str>,
        actual: Option<&str>,
        position: crate::variance::SignSet,
        binders: &BTreeSet<String>,
        occurrences: &mut BTreeMap<String, Vec<CallLifetimeOccurrence>>,
    ) {
        let Some(callee) = callee else {
            return;
        };
        if !binders.contains(callee) {
            return;
        }
        let Some(polarity) = crate::variance::LabelPolarity::of(position) else {
            return;
        };
        occurrences
            .entry(callee.to_owned())
            .or_default()
            .push(CallLifetimeOccurrence {
                actual: actual.unwrap_or("").to_owned(),
                polarity,
            });
    }
    /// Whether either checked type mentions a lifetime binder being
    /// instantiated. This prunes unrelated recursive shapes before the
    /// occurrence walk descends into their fields.
    pub(super) fn call_type_mentions_binder(&self, ty: Type, binders: &BTreeSet<String>) -> bool {
        crate::runtime_types::borrow_lifetimes(self.types, ty)
            .iter()
            .any(|label| binders.contains(label))
    }
    /// Walk one callee parameter against its checked argument value, recording
    /// every declared binder occurrence at its composed variance position.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn collect_call_lifetime_occurrences(
        &self,
        callee: Type,
        actual: Type,
        position: crate::variance::SignSet,
        binders: &BTreeSet<String>,
        occurrences: &mut BTreeMap<String, Vec<CallLifetimeOccurrence>>,
        depth: usize,
    ) -> Result<()> {
        if depth >= 64 {
            return Err(Diagnostic::new(
                Span::default(),
                "call lifetime instantiation exceeded its finite nesting budget; this call is too deeply nested to prove",
            ));
        }
        if position.is_unused()
            || (!self.call_type_mentions_binder(callee, binders)
                && !self.call_type_mentions_binder(actual, binders))
        {
            return Ok(());
        }
        if let Some(fields) = self.types.structural_row_fields(callee)
            && let Some(actual_fields) = self.types.record_row_fields(actual)
        {
            for field in fields {
                if let Some(actual) = actual_fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                {
                    let position = position.compose(crate::variance::SignSet::INVARIANT);
                    self.record_call_lifetime_occurrence(
                        field.lifetime.as_deref(),
                        actual.lifetime.as_deref(),
                        position,
                        binders,
                        occurrences,
                    );
                    self.collect_call_lifetime_occurrences(
                        field.ty,
                        actual.ty,
                        position,
                        binders,
                        occurrences,
                        depth + 1,
                    )?;
                }
            }
            return Ok(());
        }
        match (callee, actual) {
            (
                Type::Annotated(callee_pointee, callee_label),
                Type::Annotated(actual_pointee, actual_label),
            ) => {
                let callee_label = self.types.reference_label_name(callee_label);
                let actual_label = self.types.reference_label_name(actual_label);
                self.record_call_lifetime_occurrence(
                    callee_label.as_deref(),
                    actual_label.as_deref(),
                    position,
                    binders,
                    occurrences,
                );
                let callee_inner = self.types.pointees[callee_pointee];
                let actual_inner = self.types.pointees[actual_pointee];
                self.collect_call_lifetime_occurrences(
                    callee_inner,
                    actual_inner,
                    position.compose(crate::variance::SignSet::POSITIVE),
                    binders,
                    occurrences,
                    depth + 1,
                )
            }
            (Type::Annotated(callee_pointee, callee_label), other) => {
                let callee_label = self.types.reference_label_name(callee_label);
                self.record_call_lifetime_occurrence(
                    callee_label.as_deref(),
                    None,
                    position,
                    binders,
                    occurrences,
                );
                let callee_inner = self.types.pointees[callee_pointee];
                self.collect_call_lifetime_occurrences(
                    callee_inner,
                    other,
                    position.compose(crate::variance::SignSet::POSITIVE),
                    binders,
                    occurrences,
                    depth + 1,
                )
            }
            (callee, Type::Annotated(actual_pointee, _)) => {
                let actual_inner = self.types.pointees[actual_pointee];
                self.collect_call_lifetime_occurrences(
                    callee,
                    actual_inner,
                    position.compose(crate::variance::SignSet::POSITIVE),
                    binders,
                    occurrences,
                    depth + 1,
                )
            }
            (Type::Enum(callee_id), Type::Enum(actual_id))
            | (Type::Enum(callee_id), Type::Variants(actual_id, _))
            | (Type::Variants(callee_id, _), Type::Enum(actual_id))
            | (Type::Variants(callee_id, _), Type::Variants(actual_id, _)) => {
                if self.types.enums[callee_id].definition != self.types.enums[actual_id].definition
                {
                    return Ok(());
                }
                let definition = self.types.enums[callee_id].definition;
                let record = self.types.enums[callee_id].record;
                let callee_lifetimes = self.types.enums[callee_id].lifetimes.clone();
                let actual_lifetimes = self.types.enums[actual_id].lifetimes.clone();
                for (index, (callee_label, actual_label)) in
                    callee_lifetimes.iter().zip(&actual_lifetimes).enumerate()
                {
                    let variance = if record {
                        self.types
                            .variance
                            .of(definition, index)
                            .unwrap_or(crate::variance::SignSet::INVARIANT)
                    } else {
                        crate::variance::SignSet::INVARIANT
                    };
                    self.record_call_lifetime_occurrence(
                        Some(callee_label),
                        Some(actual_label),
                        position.compose(variance),
                        binders,
                        occurrences,
                    );
                }
                let callee_arguments = self.types.enums[callee_id].arguments.clone();
                let actual_arguments = self.types.enums[actual_id].arguments.clone();
                for (callee_argument, actual_argument) in
                    callee_arguments.iter().zip(&actual_arguments)
                {
                    self.collect_call_lifetime_occurrences(
                        *callee_argument,
                        *actual_argument,
                        position.compose(crate::variance::SignSet::INVARIANT),
                        binders,
                        occurrences,
                        depth + 1,
                    )?;
                }
                if record {
                    return Ok(());
                }
                let callee_variants = self.types.enums[callee_id].variants.clone();
                let actual_variants = self.types.enums[actual_id].variants.clone();
                for (callee_variant, actual_variant) in callee_variants.iter().zip(&actual_variants)
                {
                    for (callee_field, actual_field) in
                        callee_variant.fields.iter().zip(&actual_variant.fields)
                    {
                        self.collect_call_lifetime_occurrences(
                            *callee_field,
                            *actual_field,
                            position.compose(crate::variance::SignSet::INVARIANT),
                            binders,
                            occurrences,
                            depth + 1,
                        )?;
                    }
                }
                Ok(())
            }
            (Type::Ref(callee_pointee), Type::Ref(actual_pointee))
            | (Type::RefMut(callee_pointee), Type::RefMut(actual_pointee))
            | (Type::RefMut(callee_pointee), Type::Ref(actual_pointee))
            | (Type::Slice(callee_pointee), Type::Slice(actual_pointee))
            | (Type::SliceMut(callee_pointee), Type::SliceMut(actual_pointee))
            | (Type::Box(callee_pointee), Type::Box(actual_pointee))
            | (Type::Vec(callee_pointee), Type::Vec(actual_pointee)) => {
                let callee_inner = self.types.pointees[callee_pointee];
                let actual_inner = self.types.pointees[actual_pointee];
                self.collect_call_lifetime_occurrences(
                    callee_inner,
                    actual_inner,
                    position.compose(if matches!(callee, Type::RefMut(_) | Type::SliceMut(_)) {
                        crate::variance::SignSet::INVARIANT
                    } else {
                        crate::variance::SignSet::POSITIVE
                    }),
                    binders,
                    occurrences,
                    depth + 1,
                )
            }
            (Type::ArenaBox(callee_pointee), Type::ArenaBox(actual_pointee))
            | (Type::AllocBox(callee_pointee), Type::AllocBox(actual_pointee))
            | (Type::AllocVec(callee_pointee), Type::AllocVec(actual_pointee))
            | (Type::Task(callee_pointee), Type::Task(actual_pointee))
            | (Type::Thread(callee_pointee), Type::Thread(actual_pointee)) => {
                let callee_inner = self.types.pointees[callee_pointee];
                let actual_inner = self.types.pointees[actual_pointee];
                self.collect_call_lifetime_occurrences(
                    callee_inner,
                    actual_inner,
                    position.compose(crate::variance::SignSet::INVARIANT),
                    binders,
                    occurrences,
                    depth + 1,
                )
            }
            (Type::Union(callee_id), Type::Union(actual_id)) => {
                let callee_members = self.types.unions[callee_id].members.clone();
                let actual_members = self.types.unions[actual_id].members.clone();
                if callee_members.len() != actual_members.len() {
                    return Ok(());
                }
                for (callee_member, actual_member) in callee_members.iter().zip(&actual_members) {
                    self.collect_call_lifetime_occurrences(
                        *callee_member,
                        *actual_member,
                        position,
                        binders,
                        occurrences,
                        depth + 1,
                    )?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    /// Collect every binder occurrence for one call. `parameters` are the
    /// callee's checked parameter types and `values` are the already-checked
    /// arguments, before their runtime coercion replaces the argument's own
    /// lifetime labels with the parameter type.
    pub(super) fn call_lifetime_occurrences(
        &self,
        parameters: &[Type],
        values: &[Expr],
        binders: &BTreeSet<String>,
    ) -> Result<BTreeMap<String, Vec<CallLifetimeOccurrence>>> {
        let mut occurrences = BTreeMap::new();
        for (parameter, value) in parameters.iter().zip(values) {
            self.collect_call_lifetime_occurrences(
                *parameter,
                value.ty,
                crate::variance::SignSet::POSITIVE,
                binders,
                &mut occurrences,
                0,
            )?;
        }
        Ok(occurrences)
    }
    /// Resolve each callee binder from all of its parameter occurrences.
    /// Invariant occurrences must agree on one actual identity; covariant and
    /// contravariant occurrences may use a different actual lifetime only when
    /// an established outlives edge proves the required direction. A binder
    /// with no parameter occurrence keeps a distinct opaque identity so an
    /// unresolved callee label can never masquerade as a caller binder with the
    /// same printed name.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn resolve_call_lifetimes(
        &mut self,
        binders: &BTreeSet<String>,
        parameters: &[Type],
        values: &[Expr],
        bounds: &BTreeSet<(String, String)>,
        binder_names: &BTreeMap<String, String>,
        span: Span,
    ) -> Result<BTreeMap<String, String>> {
        let mut occurrences = self.call_lifetime_occurrences(parameters, values, binders)?;
        let mut map = BTreeMap::new();
        for binder in binders {
            let binder_name = binder_names.get(binder).unwrap_or(binder);
            let occurrences = occurrences.remove(binder).unwrap_or_default();
            let actuals = occurrences
                .iter()
                .map(|occurrence| occurrence.actual.clone())
                .filter(|actual| !actual.is_empty())
                .collect::<BTreeSet<_>>();
            if actuals.is_empty() {
                if occurrences.is_empty() {
                    // No parameter occurrence at all: no caller identity can
                    // ever supply this binder. Keep a distinct opaque identity
                    // so its printed name cannot collide with a caller binder.
                    map.insert(
                        binder.clone(),
                        self.types.fresh_lifetime("callee result lifetime"),
                    );
                } else {
                    // The only occurrences are outer borrow positions whose
                    // actual lexical lifetime is owned by the ownership
                    // provenance pass, not by a record label in the checked
                    // type. Preserving the binder name keeps the declared
                    // bounds between this call's own result labels provable
                    // through their provenance; a fresh identity here would
                    // reject legitimate result-parameter relabeling.
                    map.insert(binder.clone(), binder.clone());
                }
                continue;
            }
            // Compiler-inferred and elided labels are occurrence placeholders,
            // not caller identities. When every supplied record label is one of
            // these, the call has no named identity to prove or collide with;
            // the ownership provenance pass remains authoritative.
            let named = actuals
                .iter()
                .filter(|actual| !is_opaque_call_label(actual))
                .cloned()
                .collect::<BTreeSet<_>>();
            if named.is_empty() {
                map.insert(
                    binder.clone(),
                    self.types.fresh_lifetime("callee result lifetime"),
                );
                continue;
            }
            let invokes_invariant = occurrences
                .iter()
                .filter(|occurrence| {
                    occurrence.polarity == crate::variance::LabelPolarity::Invariant
                })
                .collect::<Vec<_>>();
            if invokes_invariant
                .iter()
                .any(|occurrence| is_opaque_call_label(&occurrence.actual))
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "this call cannot prove the invariant lifetime '{binder_name}': one occurrence supplies an inferred/elided identity while another supplies a named lifetime"
                    ),
                ));
            }
            let invariants = invokes_invariant
                .iter()
                .map(|occurrence| occurrence.actual.clone())
                .filter(|actual| !actual.is_empty())
                .collect::<BTreeSet<_>>();
            let candidate = if !invariants.is_empty() {
                if invariants.len() > 1 {
                    let names = invariants
                        .iter()
                        .map(|actual| format!("'{actual}"))
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "this call instantiates lifetime '{binder_name}' invariantly from several argument lifetimes ({names}); an invariant occurrence requires one actual lifetime identity"
                        ),
                    ));
                }
                let candidate = invariants.into_iter().next().expect("one invariant actual");
                for occurrence in &occurrences {
                    if occurrence.actual.is_empty() || is_opaque_call_label(&occurrence.actual) {
                        continue;
                    }
                    match occurrence.polarity {
                        crate::variance::LabelPolarity::Positive => {
                            if !outlives(&self.lifetime_bounds, &occurrence.actual, &candidate) {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "this call cannot use lifetime '{}' where '{binder_name}' is invariant '{}': no established outlives edge proves '{}: '{}",
                                        occurrence.actual, candidate, occurrence.actual, candidate
                                    ),
                                ));
                            }
                        }
                        crate::variance::LabelPolarity::Negative => {
                            if !outlives(&self.lifetime_bounds, &candidate, &occurrence.actual) {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "this call cannot use lifetime '{}' where '{binder_name}' is invariant '{}': no established outlives edge proves '{}: '{}",
                                        occurrence.actual, candidate, candidate, occurrence.actual
                                    ),
                                ));
                            }
                        }
                        crate::variance::LabelPolarity::Invariant => {
                            if occurrence.actual != candidate {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "this call instantiates lifetime '{binder_name}' invariantly from both '{}' and '{}'; an invariant occurrence requires one actual lifetime identity",
                                        occurrence.actual, candidate
                                    ),
                                ));
                            }
                        }
                    }
                }
                candidate
            } else if actuals.len() == 1 {
                actuals.into_iter().next().expect("one actual lifetime")
            } else {
                let candidates = named
                    .iter()
                    .filter(|candidate| {
                        occurrences.iter().all(|occurrence| {
                            if occurrence.actual.is_empty()
                                || is_opaque_call_label(&occurrence.actual)
                            {
                                return true;
                            }
                            match occurrence.polarity {
                                crate::variance::LabelPolarity::Positive => {
                                    outlives(&self.lifetime_bounds, &occurrence.actual, candidate)
                                }
                                crate::variance::LabelPolarity::Negative => {
                                    outlives(&self.lifetime_bounds, candidate, &occurrence.actual)
                                }
                                crate::variance::LabelPolarity::Invariant => false,
                            }
                        })
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                match candidates.as_slice() {
                    [candidate] => candidate.clone(),
                    [] => {
                        let names = named
                            .iter()
                            .map(|actual| format!("'{actual}"))
                            .collect::<Vec<_>>()
                            .join(", ");
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "cannot choose one actual lifetime for callee lifetime '{binder_name}' from covariant argument occurrences ({names}); no candidate satisfies every required outlives edge"
                            ),
                        ));
                    }
                    _ => {
                        let minimal = candidates.iter().find(|candidate| {
                            candidates.iter().all(|other| {
                                other == *candidate
                                    || outlives(&self.lifetime_bounds, other, candidate)
                            })
                        });
                        match minimal {
                            Some(candidate) => candidate.clone(),
                            None => {
                                let names = candidates
                                    .iter()
                                    .map(|actual| format!("'{actual}"))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "cannot choose one actual lifetime for callee lifetime '{binder_name}': the covariant argument lifetimes {names} are incomparable, so no checked common identity exists"
                                    ),
                                ));
                            }
                        }
                    }
                }
            };
            map.insert(binder.clone(), candidate);
        }
        for (long, short) in bounds {
            if !binders.contains(long) || !binders.contains(short) {
                continue;
            }
            let (Some(long), Some(short)) = (map.get(long), map.get(short)) else {
                continue;
            };
            // An opaque label carries no caller identity, so there is no
            // caller outlives edge to check; the ownership provenance pass
            // owns the label relation for result-derived provenance.
            if long.starts_with('<') || short.starts_with('<') {
                continue;
            }
            if !outlives(&self.lifetime_bounds, long, short) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "this call instantiates the callee bound '{long}: {short}', but no caller outlives edge proves '{}: '{}",
                        long.trim_start_matches('\''),
                        short.trim_start_matches('\'')
                    ),
                ));
            }
        }
        Ok(map)
    }
    /// Instantiate a call result from the actual argument provenance. Every
    /// unresolved callee binder becomes a distinct opaque identity, never its
    /// raw printed name, so a caller binder with the same name cannot pose as
    /// the callee's identity.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn instantiated_call_result_type(
        &mut self,
        binders: &BTreeSet<String>,
        parameters: &[Type],
        result: Type,
        result_grade: Option<Grade>,
        bounds: &BTreeSet<(String, String)>,
        values: &[Expr],
        span: Span,
    ) -> Result<Type> {
        if crate::runtime_types::grade_erases(result_grade) {
            return Ok(Type::Unit);
        }
        let map = self.resolve_call_lifetimes(
            binders,
            parameters,
            values,
            bounds,
            &BTreeMap::new(),
            span,
        )?;
        self.types.relabel_lifetimes(result, &map, span)
    }
    /// Insert the deterministic runtime conversion needed to use `value` as
    /// `expected`. Same-layout refinements stay narrow (no runtime work); atom
    /// injection and union repacking become explicit `Coerce` nodes.
    pub(super) fn coerce(&mut self, value: Expr, expected: Type, span: Span) -> Result<Expr> {
        if value.ty == Type::Never || value.ty == expected {
            return Ok(value);
        }
        self.check_static_lifetime_witness(&value, expected, span)?;
        if let Type::DynObj(object) = expected {
            // A concrete value becomes an open trait object by registering a
            // checked member vtable entry and allocating its payload. The
            // conversion is explicit, observable in the allocation budget, and
            // therefore requires the `alloc` effect.
            if let Type::DynObj(from) = value.ty {
                let source = &self.types.objects[from].components;
                let target = &self.types.objects[object].components;
                if !target.iter().all(|component| source.contains(component)) {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "type mismatch: expected {}, found {}; a trait object only upcasts to an object over a subset of its traits",
                            self.types.name(expected),
                            self.types.name(value.ty)
                        ),
                    ));
                }
                self.add_dyn_upcast(from, object, span)?;
                return Ok(Expr {
                    kind: ExprKind::Coerce {
                        value: Box::new(value),
                        to: expected,
                        coercion: Coercion::DynUpcast { from, to: object },
                    },
                    ty: expected,
                    span,
                    resource: None,
                });
            }
            let member = self.register_dyn_member(object, value.ty, span)?;
            let member_type = value.ty;
            self.require(ALLOC, span)?;
            return Ok(Expr {
                kind: ExprKind::Coerce {
                    value: Box::new(value),
                    to: expected,
                    coercion: Coercion::DynBox {
                        member,
                        member_type,
                    },
                },
                ty: expected,
                span,
                resource: None,
            });
        }
        if self.types.is_structural(expected) {
            return self.coerce_struct(value, expected, span);
        }
        if !self.subtype(value.ty, expected) {
            self.expect(value.ty, expected, span)?;
            debug_assert!(false, "expect returned for a non-subtype");
        }
        if self.same_layout(value.ty, expected) {
            return Ok(value);
        }
        if matches!(value.ty, Type::Fn(_) | Type::Once(_))
            && matches!(expected, Type::Fn(_) | Type::Once(_))
        {
            return self.coerce_function(value, expected, span);
        }
        if let (Type::Multi(source), Type::Multi(target)) = (value.ty, expected) {
            // Tokens are made only by the compiler: a wider token type is
            // accepted only when no adapter is needed.
            let source = self.types.function_types[source].clone();
            let target = self.types.function_types[target].clone();
            if self.arrow_rep_change(&source, &target) {
                return Err(Diagnostic::new(
                    span,
                    "a multishot resumption token cannot be adapted to a token type with a different representation",
                ));
            }
            let mut value = value;
            value.ty = expected;
            return Ok(value);
        }
        let Type::Union(target_id) = expected else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "internal error: no representation conversion from {} to {}",
                    self.types.name(value.ty),
                    self.types.name(expected)
                ),
            ));
        };
        let target_members = self.types.unions[target_id].members.clone();
        let coercion = if let Type::Union(source_id) = value.ty {
            let source_members = self.types.unions[source_id].members.clone();
            let mut map = Vec::with_capacity(source_members.len());
            for member in source_members {
                let Some(tag) = target_members.iter().position(|target| {
                    self.subtype(member, *target)
                        && self.union_member_representation_compatible(member, *target)
                }) else {
                    if target_members
                        .iter()
                        .any(|target| self.subtype(member, *target))
                    {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "repacking union alternative {} as {} would change its representation (a callable convention or a record layout); match and convert that alternative explicitly first",
                                self.types.name(member),
                                self.types.name(expected)
                            ),
                        ));
                    }
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "internal error: union member {} has no target alternative in {}",
                            self.types.name(member),
                            self.types.name(expected)
                        ),
                    ));
                };
                map.push(tag);
            }
            Coercion::Repack { map }
        } else {
            let Some(tag) = target_members
                .iter()
                .position(|target| *target == value.ty)
                .or_else(|| {
                    target_members
                        .iter()
                        .position(|target| self.subtype(value.ty, *target))
                })
            else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "internal error: {} has no alternative in {}",
                        self.types.name(value.ty),
                        self.types.name(expected)
                    ),
                ));
            };
            // A callable atom may need its checked adapter (for example a pure
            // `fn` used in a `once fn` alternative, which needs a null-env
            // thunk). Adapt before injecting; a raw payload copy would change
            // the indirect-call ABI.
            // Convert the value to the selected member first: a callable may
            // need its adapter, and a record may need a structural width/order
            // conversion that drops erased fields. Injecting raw words would
            // reinterpret fields and leak owners.
            let member = target_members[tag];
            let value = if self.same_layout(value.ty, member) {
                value
            } else {
                self.coerce(value, member, span)?
            };
            let ty = expected;
            return Ok(Expr {
                kind: ExprKind::Coerce {
                    value: Box::new(value),
                    to: expected,
                    coercion: Coercion::Inject { tag },
                },
                ty,
                span,
                resource: None,
            });
        };
        let ty = expected;
        Ok(Expr {
            kind: ExprKind::Coerce {
                value: Box::new(value),
                to: expected,
                coercion,
            },
            ty,
            span,
            resource: None,
        })
    }
    /// A checked width/row conversion into an anonymous structural record.
    /// Fields are matched by name, the target row is canonical (sorted), and
    /// omitted source fields are dropped by the runtime conversion. A nested
    /// representation change in a retained field is rejected explicitly: the
    /// supported fragment copies fields that already have the target
    /// representation, while width/order changes still require a real
    /// conversion. This is a deliberate limit, not a silent relabeling.
    pub(super) fn retained_struct_labels(
        &mut self,
        source: Type,
        expected: Type,
        rename: Option<&BTreeMap<String, String>>,
        span: Span,
    ) -> Result<Type> {
        let mut fields = self
            .types
            .structural_row_fields(expected)
            .expect("structural target");
        if let Some(source_fields) = self.types.record_row_fields(source) {
            for field in &mut fields {
                let name = rename
                    .and_then(|map| map.get(&field.name))
                    .unwrap_or(&field.name);
                if let Some(source) = source_fields.iter().find(|source| &source.name == name) {
                    if field.lifetime.is_none() {
                        field.lifetime = source.lifetime.clone();
                    }
                    if self.types.is_structural(field.ty) && source.ty.layout().is_some() {
                        field.ty = self.retained_struct_labels(source.ty, field.ty, None, span)?;
                    }
                }
            }
        }
        self.types.structural_fields(fields, span)
    }
    /// Whether a nested structural source may acquire the target row's labels
    /// through an ordinary checked conversion. Direct borrowed fields already
    /// allow an unlabelled source to take the annotation; nested rows need the
    /// same per-leaf rule instead of comparing the interned row types for exact
    /// identity. A named source label still has to match the target exactly, so
    /// this never relabels one concrete caller lifetime as another.
    pub(super) fn structural_labels_acquirable(&self, source: Type, target: Type) -> bool {
        let (Some(source_fields), Some(target_fields)) = (
            self.types.structural_row_fields(source),
            self.types.structural_row_fields(target),
        ) else {
            return false;
        };
        if source_fields.len() != target_fields.len() {
            return false;
        }
        for target_field in &target_fields {
            let Some(source_field) = source_fields
                .iter()
                .find(|source_field| source_field.name == target_field.name)
            else {
                return false;
            };
            match (
                self.types.is_structural(source_field.ty),
                self.types.is_structural(target_field.ty),
            ) {
                (true, true) => {
                    if !self.structural_labels_acquirable(source_field.ty, target_field.ty) {
                        return false;
                    }
                }
                (false, false) => {
                    if source_field.ty != target_field.ty {
                        return false;
                    }
                }
                _ => return false,
            }
            if let (Some(source_label), Some(target_label)) =
                (&source_field.lifetime, &target_field.lifetime)
                && !crate::runtime_types::is_opaque_row_label(source_label)
                && source_label != target_label
            {
                return false;
            }
        }
        true
    }
    pub(super) fn coerce_struct(
        &mut self,
        value: Expr,
        expected: Type,
        span: Span,
    ) -> Result<Expr> {
        let expected = self.retained_struct_labels(value.ty, expected, None, span)?;
        let coercion = self.struct_coercion(value.ty, expected, span, 0)?;
        Ok(Expr {
            kind: ExprKind::Coerce {
                value: Box::new(value),
                to: expected,
                coercion,
            },
            ty: expected,
            span,
            resource: None,
        })
    }
    /// Check an explicit structural conversion `value as struct { ... }`.
    /// Field renaming is expressed only here: the target row keeps its own
    /// canonical names, while `from source` selects the source field. The
    /// conversion is an ordinary checked `Coercion::Struct`, so field owners
    /// are moved exactly once and unmentioned fields are cleaned up.
    pub(super) fn structural_cast(
        &mut self,
        value_ast: &ast::Expr,
        target: &ast::Type,
        span: Span,
    ) -> Result<Expr> {
        let ast::TypeKind::Structural { fields, open, row } = &target.kind else {
            return Err(Diagnostic::new(
                span,
                "an 'as' structural conversion target must be an anonymous structural row, as in 'value as struct { b: i64 from a }'",
            ));
        };
        if *open || row.is_some() {
            return Err(Diagnostic::new(
                span,
                "a renaming structural cast needs a closed target row; give every target field explicitly",
            ));
        }
        let mut mapping = BTreeMap::new();
        let mut cleaned = Vec::with_capacity(fields.len());
        for field in fields {
            if let Some(source) = &field.source
                && mapping.insert(field.name.clone(), source.clone()).is_some()
            {
                return Err(Diagnostic::new(
                    field.span,
                    format!("duplicate target field '{}' in structural cast", field.name),
                ));
            }
            cleaned.push(ast::Field {
                name: field.name.clone(),
                source: None,
                ty: field.ty.clone(),
                span: field.span,
                public: true,
                min_length: None,
            });
        }
        let mut seen_sources = BTreeSet::new();
        for source in mapping.values() {
            if !seen_sources.insert(source.clone()) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "structural cast maps source field '{source}' to more than one target field"
                    ),
                ));
            }
        }
        let cleaned = ast::Type {
            kind: ast::TypeKind::Structural {
                fields: cleaned,
                open: false,
                row: None,
            },
            span: target.span,
        };
        let target_ty = self.ty(&cleaned)?;
        let value = self.expr(value_ast)?;
        let rename = (!mapping.is_empty()).then_some(&mapping);
        let target_ty = self.retained_struct_labels(value.ty, target_ty, rename, span)?;
        let coercion = self.struct_coercion_mapped(value.ty, target_ty, rename, span, 0)?;
        Ok(Expr {
            kind: ExprKind::Coerce {
                value: Box::new(value),
                to: target_ty,
                coercion,
            },
            ty: target_ty,
            span,
            resource: None,
        })
    }
    /// Build the checked field mapping for a record-to-structural conversion.
    /// A retained field may itself need a nested structural conversion or an
    /// atom-to-union injection; union-to-union repacking is rejected because it
    /// needs its own control flow and should be written as an explicit field
    /// conversion. The depth budget keeps nested rows finite.
    pub(super) fn struct_coercion(
        &mut self,
        source: Type,
        expected: Type,
        span: Span,
        depth: usize,
    ) -> Result<Coercion> {
        self.struct_coercion_mapped(source, expected, None, span, depth)
    }
    /// Build a structural conversion, optionally with explicit source-field
    /// names (`value as struct { b: i64 from a }`). Every kept source field
    /// must be used exactly once, so a rename can never duplicate an owner or
    /// silently reinterpret field offsets.
    pub(super) fn struct_coercion_mapped(
        &mut self,
        source: Type,
        expected: Type,
        rename: Option<&BTreeMap<String, String>>,
        span: Span,
        depth: usize,
    ) -> Result<Coercion> {
        if depth >= 32 {
            return Err(Diagnostic::new(
                span,
                "structural field coercion nesting budget exhausted (32)",
            ));
        }
        let Some(target_row) = self.types.structural_row(expected) else {
            return Err(Diagnostic::new(
                span,
                "internal error: structural conversion target is not a structural record",
            ));
        };
        let Some(source_layout) = source.layout().filter(|id| self.types.enums[*id].record) else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: expected {}, found {}",
                    self.types.name(expected),
                    self.types.name(source)
                ),
            ));
        };
        let source_variant = self.types.enums[source_layout].variants[0].clone();
        let mut used_sources = BTreeSet::new();
        let mut kept = Vec::with_capacity(target_row.len());
        for (target_index, (name, target_ty)) in target_row.iter().enumerate() {
            let source_name = rename
                .and_then(|rename| rename.get(name))
                .map(String::as_str)
                .unwrap_or(name);
            self.check_layout_field_visible(source_layout, source_name, span)?;
            let Some(source_index) = source_variant
                .names
                .iter()
                .position(|source| source == source_name)
            else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot convert {} to {}: the source row has no field '{source_name}'{}",
                        self.types.name(source),
                        self.types.name(expected),
                        if source_name == name {
                            String::new()
                        } else {
                            format!(" for target field '{name}'")
                        }
                    ),
                ));
            };
            if !used_sources.insert(source_index) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "structural conversion uses source field '{source_name}' for more than one target field; each source field can be moved only once"
                    ),
                ));
            }
            let source_ty = source_variant.fields[source_index];
            if !self.subtype(source_ty, *target_ty) {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot convert field '{source_name}' from {} to {} in structural record conversion",
                        self.types.name(source_ty),
                        self.types.name(*target_ty)
                    ),
                ));
            }
            if crate::runtime_types::has_borrow(self.types, *target_ty)
                || crate::runtime_types::has_mutable_borrow(self.types, *target_ty)
            {
                // Nested rows follow the same per-leaf rule as direct fields:
                // an unlabelled source leaf may acquire the target annotation
                // through this checked conversion, while every named source
                // label must still match exactly.
                let nested_acquisition = self.types.is_structural(source_ty)
                    && self.types.is_structural(*target_ty)
                    && self.structural_labels_acquirable(source_ty, *target_ty);
                if source_ty != *target_ty && !nested_acquisition {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot convert field '{source_name}' from {} to {}: borrowed leaves are invariant under structural conversion",
                            self.types.name(source_ty),
                            self.types.name(*target_ty)
                        ),
                    ));
                }
                let source_label = self.types.enums[source_layout]
                    .field_lifetimes
                    .get(source_index)
                    .cloned()
                    .flatten();
                let target_label = self.types.enums[expected.layout().expect("structural target")]
                    .field_lifetimes
                    .get(target_index)
                    .cloned()
                    .flatten();
                if let (Some(source_label), Some(target_label)) = (source_label, target_label)
                    && !crate::runtime_types::is_opaque_row_label(&source_label)
                    && source_label != target_label
                {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot convert field '{source_name}' from a '{source_label}' borrow to an '{target_label}' borrow: borrowed leaves are invariant under structural conversion"
                        ),
                    ));
                }
            }
            let nested = self.nested_field_coercion(source_ty, *target_ty, span, depth + 1)?;
            kept.push((target_index, source_index, nested));
        }
        let mut drops = Vec::new();
        for (source_index, source_ty) in source_variant.fields.iter().enumerate() {
            if used_sources.contains(&source_index) {
                continue;
            }
            if crate::runtime_types::contains_linear(self.types, *source_ty)
                || crate::runtime_types::contains_dyn_object(self.types, *source_ty)
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "cannot erase field '{}' of type {} through structural width subtyping: it carries a linear obligation that the target cannot consume",
                        source_variant.names[source_index],
                        self.types.name(*source_ty)
                    ),
                ));
            }
            drops.push((source_index, *source_ty));
        }
        drops.reverse();
        Ok(Coercion::Struct {
            source,
            kept,
            drops,
        })
    }
    /// A nested field conversion that stays inside the structural conversion's
    /// own representation. Only two cases need work: a nested structural row
    /// (recursive field mapping) and an atom injected into a union alternative.
    pub(super) fn nested_field_coercion(
        &mut self,
        source: Type,
        target: Type,
        span: Span,
        depth: usize,
    ) -> Result<Option<Coercion>> {
        if self.same_layout(source, target) {
            return Ok(None);
        }
        if !self.subtype(source, target) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot convert field from {} to {}",
                    self.types.name(source),
                    self.types.name(target)
                ),
            ));
        }
        if self.types.is_structural(target) {
            return Ok(Some(self.struct_coercion(source, target, span, depth)?));
        }
        // A retained field whose arrow type changes representation needs a
        // generated adapter. The field value is dynamic at this point, so the
        // adapter must carry it in an owned environment; that allocation is
        // charged to the enclosing function's effect row.
        if let (Some((_, source_once)), Some((target_id, target_once))) =
            (Self::function_parts(source), Self::function_parts(target))
        {
            let rep_change = {
                let source_index = Self::function_parts(source).expect("checked callable").0;
                let source_fn = &self.types.function_types[source_index];
                let target_fn = &self.types.function_types[target_id];
                self.arrow_rep_change(source_fn, target_fn)
            };
            if source_once == target_once && !rep_change {
                return Ok(None);
            }
            if !source_once && !target_once {
                return Err(Diagnostic::new(
                    span,
                    "a structural field of pure function type cannot change its parameter/result representation: a pure function has no environment for the generated adapter. Bind the function and adapt it explicitly before the structural coercion",
                ));
            }
            debug_assert!(
                target_once,
                "an owning callable is not a subtype of a pure arrow"
            );
            let function = self.call_adapter(source, target_id, span)?;
            return Ok(Some(Coercion::Callable {
                function,
                capture: Some(source),
                target,
            }));
        }
        let Type::Union(target_id) = target else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "structural field would need an unsupported nested representation change from {} to {}; convert the field explicitly before the structural coercion",
                    self.types.name(source),
                    self.types.name(target)
                ),
            ));
        };
        let target_members = self.types.unions[target_id].members.clone();
        if let Type::Union(source_id) = source {
            let source_members = self.types.unions[source_id].members.clone();
            let mut map = Vec::with_capacity(source_members.len());
            for member in source_members {
                let Some(tag) = target_members.iter().position(|target| {
                    self.subtype(member, *target)
                        && self.union_member_representation_compatible(member, *target)
                }) else {
                    if target_members
                        .iter()
                        .any(|target| self.subtype(member, *target))
                    {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "nested union field conversion from {} to {} would change a member representation (a callable convention or a record layout); convert the field explicitly first",
                                self.types.name(source),
                                self.types.name(target)
                            ),
                        ));
                    }
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "internal error: nested union member {} has no target alternative in {}",
                            self.types.name(member),
                            self.types.name(target)
                        ),
                    ));
                };
                map.push(tag);
            }
            return Ok(Some(Coercion::Repack { map }));
        }
        let Some(tag) = target_members
            .iter()
            .position(|member| self.subtype(source, *member))
        else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "internal error: field {} has no alternative in {}",
                    self.types.name(source),
                    self.types.name(target)
                ),
            ));
        };
        if !self.union_member_representation_compatible(source, target_members[tag]) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "a field cannot be injected into union alternative {} inside a structural coercion because its representation changes (a callable convention or a record layout); convert the field explicitly first",
                    self.types.name(target_members[tag])
                ),
            ));
        }
        Ok(Some(Coercion::Inject { tag }))
    }
    /// Whether a union-to-union repack can copy a member's payload words
    /// directly. Callable members may only cross when the calling convention
    /// and parameter/result representations are identical.
    pub(super) fn union_member_representation_compatible(
        &self,
        source: Type,
        target: Type,
    ) -> bool {
        match (Self::function_parts(source), Self::function_parts(target)) {
            (Some((source_id, source_once)), Some((target_id, target_once))) => {
                source_once == target_once && {
                    let source = &self.types.function_types[source_id];
                    let target = &self.types.function_types[target_id];
                    !self.arrow_rep_change(source, target)
                }
            }
            // A non-callable payload is copied word for word, so it must
            // already have the target member's layout; a structural width or
            // order change needs a real conversion.
            (None, None) => self.same_layout(source, target),
            _ => false,
        }
    }
    /// Coerce a value-position block to a join type, synthesizing a unit tail
    /// when a `Unit` branch must be injected into a union.
    pub(super) fn coerce_block(
        &mut self,
        mut block: Block,
        target: Type,
        span: Span,
    ) -> Result<Block> {
        if block.ty == Type::Never || self.same_layout(block.ty, target) {
            return Ok(block);
        }
        if !self.subtype(block.ty, target) {
            self.expect(block.ty, target, span)?;
        }
        let tail = match block.tail.take() {
            Some(tail) => *tail,
            None => Expr {
                kind: ExprKind::Constant(0),
                ty: Type::Unit,
                span,
                resource: None,
            },
        };
        let tail = self.coerce(tail, target, span)?;
        block.tail = Some(Box::new(tail));
        block.ty = target;
        Ok(block)
    }
    /// Whether a union alternative may be narrowed to `requested` by copying
    /// its payload words. Enum variant masks share a layout; callable
    /// alternatives require the same calling convention and identical
    /// parameter/result representations, because a pattern has no place to
    /// insert an adapter.
    pub(super) fn narrow_representation_compatible(&self, member: Type, requested: Type) -> bool {
        if self.same_layout(member, requested) {
            return true;
        }
        match (member, requested) {
            (Type::Fn(a), Type::Fn(b)) | (Type::Once(a), Type::Once(b)) => {
                let source = &self.types.function_types[a];
                let target = &self.types.function_types[b];
                !self.arrow_rep_change(source, target)
            }
            _ => false,
        }
    }
    /// Split a callable type into its signature table index and call mode.
    pub(super) fn function_parts(ty: Type) -> Option<(usize, bool)> {
        match ty {
            Type::Fn(id) => Some((id, false)),
            Type::Once(id) => Some((id, true)),
            _ => None,
        }
    }
    /// The underlying static function index of a function value, through a
    /// checked coercion wrapper. Used to validate task-body result obligations.
    pub(super) fn callable_function(expr: &Expr) -> Option<usize> {
        match &expr.kind {
            ExprKind::FnValue { function, .. } => Some(*function),
            ExprKind::Coerce { value, .. } => Self::callable_function(value),
            _ => None,
        }
    }
    /// Whether moving between these arrow types changes the word
    /// representation of an argument or result. Such conversions require a
    /// checked adapter; same-layout variance needs no runtime work.
    ///
    /// Grade-zero parameters are physically absent. A `@[0]` source parameter
    /// used where a non-erased contract is expected (or the reverse) therefore
    /// changes the calling convention even when the logical parameter lists
    /// are identical. Treating that as a raw compatible cast would shift every
    /// later argument.
    pub(super) fn arrow_rep_change(&self, source: &FunctionType, target: &FunctionType) -> bool {
        if source.parameters.len() != target.parameters.len() {
            return true;
        }
        // Each declared resumptive operation of the row is a hidden
        // capability parameter (docs/one-handler-model.md rule 4).
        let resumptive = self.resumptive_bits();
        if source.effects & resumptive != target.effects & resumptive {
            return true;
        }
        let mut rep_change = false;
        for index in 0..source.parameters.len() {
            let source_erased = source.parameter_erased(index);
            let target_erased = target.parameter_erased(index);
            if source_erased != target_erased
                || (!source_erased
                    && !self.same_layout(source.parameters[index], target.parameters[index]))
            {
                rep_change = true;
            }
        }
        let source_result_erased = crate::runtime_types::grade_erases(source.result_grade);
        let target_result_erased = crate::runtime_types::grade_erases(target.result_grade);
        if source_result_erased != target_result_erased
            || (!source_result_erased && !self.same_layout(source.result, target.result))
        {
            rep_change = true;
        }
        rep_change
    }
    /// Coerce a function value to a supertype. Pure-to-once is a null-env
    /// padding operation with no allocation. Representation-changing variance
    /// is compiled to a checked adapter function, never a function-pointer cast.
    pub(super) fn coerce_function(
        &mut self,
        value: Expr,
        expected: Type,
        span: Span,
    ) -> Result<Expr> {
        let actual = value.ty;
        let (Some((source_id, source_once)), Some((target_id, target_once))) =
            (Self::function_parts(actual), Self::function_parts(expected))
        else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "type mismatch: expected {}, found {}",
                    self.types.name(expected),
                    self.types.name(actual)
                ),
            ));
        };
        let source = self.types.function_types[source_id].clone();
        let target = self.types.function_types[target_id].clone();
        let rep_change = self.arrow_rep_change(&source, &target);
        if !source_once && target_once {
            // A once callable has a different calling convention (an
            // environment argument). A static pure source is wrapped by a
            // no-allocation thunk that ignores the null environment; a dynamic
            // pure source is captured by an allocating once adapter.
            if let ExprKind::FnValue { function, captures } = &value.kind
                && captures.is_empty()
            {
                let function = *function;
                let adapted = if rep_change {
                    let pure = self.pure_adapter(function, target_id, span)?;
                    let ExprKind::FnValue { function, captures } = pure.kind else {
                        unreachable!("pure adapter is a function value")
                    };
                    debug_assert!(captures.is_empty());
                    function
                } else {
                    function
                };
                return self.once_thunk(adapted, target_id, span);
            }
            return self.closure_adapter(value, target_id, span);
        }
        if !rep_change {
            let mut value = value;
            value.ty = expected;
            return Ok(value);
        }
        if source_once {
            return self.closure_adapter(value, target_id, span);
        }
        if let ExprKind::FnValue { function, captures } = &value.kind
            && captures.is_empty()
        {
            return self.pure_adapter(*function, target_id, span);
        }
        Err(Diagnostic::new(
            span,
            "representation-changing conversion of a dynamic pure function value would need a capturing adapter; bind it with an explicit 'once fn' type or use a direct function name",
        ))
    }
    /// Reject an adapter whose body allocates but whose arrow effect row does
    /// not expose `alloc`/`panic`.
    pub(super) fn check_adapter_effects(
        &self,
        body: &Block,
        signature: &FunctionType,
        span: Span,
    ) -> Result<()> {
        if block_allocates(body) && signature.effects & (ALLOC | PANIC) != ALLOC | PANIC {
            return Err(Diagnostic::new(
                span,
                "this function-value conversion needs a capturing adapter; add 'alloc' to the target arrow effect row",
            ));
        }
        Ok(())
    }
    /// Register a synthetic adapter body with a checked callable signature.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn register_adapter(
        &mut self,
        name: &str,
        signature: &FunctionType,
        capture_types: Vec<Type>,
        env_parameter: bool,
        locals: Vec<Local>,
        body: Block,
        span: Span,
    ) -> Result<usize> {
        let captures = capture_types.len();
        let mut parameter_grades = vec![None; captures];
        parameter_grades.extend(signature.parameter_grades.iter().copied());
        // The adapter is checked against the callable's borrow contract, like
        // a named function with the same explicit lifetimes.
        let mut parameter_lifetimes = vec![None; captures];
        parameter_lifetimes.extend(
            (0..signature.parameters.len())
                .map(|i| signature.borrows.parameters.get(i).cloned().flatten()),
        );
        let function = Function {
            name: name.to_owned(),
            parameters: captures + signature.parameters.len(),
            closure: (captures != 0)
                .then_some(captures)
                .or(env_parameter.then_some(0)),
            capture_refs: vec![false; captures],
            capture_writes: vec![false; captures],
            locals,
            result: signature.result,
            body,
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades,
            result_grade: signature.result_grade,
            parameter_lifetimes: parameter_lifetimes.clone(),
            result_lifetime: signature.borrows.result.clone(),
            lifetime_bounds: signature.borrows.bounds.clone(),
            declared_lifetimes: BTreeSet::new(),
            index_relations: BTreeSet::new(),
            parameter_slots: None,
            local_borrowed: vec![],
            local_copyable: vec![],
            capability_parameters: vec![],
            shared_environment: false,
        };
        let synthetic = Signature {
            call_contract: None,
            associated_consts: BTreeMap::new(),
            binding: usize::MAX,
            name: name.to_owned(),
            parameters: signature.parameters.clone(),
            result: signature.result,
            effects: signature.effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades: signature.parameter_grades.clone(),
            result_grade: signature.result_grade,
            parameter_lifetimes: parameter_lifetimes[captures..].to_vec(),
            result_lifetime: signature.borrows.result.clone(),
            lifetime_bounds: signature.borrows.bounds.clone(),
            self_type: None,
            default_trait: None,
        };
        self.functions.add_synthetic(synthetic, function)
    }
    /// A pure, noncapturing adapter for a statically known source function.
    /// It has the target parameter/result representation and directly calls the
    /// source, applying only checked value coercions.
    pub(super) fn pure_adapter(
        &mut self,
        source: usize,
        target_id: usize,
        span: Span,
    ) -> Result<Expr> {
        let key = (Some(source), Type::Fn(0), Type::Fn(target_id));
        if let Some(index) = self.functions.adapter_cache.get(&key).copied() {
            return Ok(Expr {
                kind: ExprKind::FnValue {
                    function: index,
                    captures: vec![],
                },
                ty: Type::Fn(target_id),
                span,
                resource: None,
            });
        }
        let target = self.types.function_types[target_id].clone();
        let source_signature = self.functions.signatures[source].clone();
        let locals = target
            .parameters
            .iter()
            .map(|ty| Local {
                ty: *ty,
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span,
            })
            .collect::<Vec<_>>();
        let mut arguments = Vec::with_capacity(target.parameters.len());
        for (index, (target_parameter, source_parameter)) in target
            .parameters
            .iter()
            .zip(&source_signature.parameters)
            .enumerate()
        {
            if target.parameter_erased(index) || source_signature.parameter_erased(index) {
                // One side of this conversion has no physical slot. The
                // adapter must not read an unmaterialized local or treat the
                // value as ABI-compatible; the erased position is evaluated as
                // a dummy and dropped by the callee's own erasure.
                arguments.push(Expr {
                    kind: ExprKind::Erased(*source_parameter),
                    ty: *source_parameter,
                    span,
                    resource: None,
                });
                continue;
            }
            let argument = Expr {
                kind: ExprKind::Local(index),
                ty: *target_parameter,
                span,
                resource: None,
            };
            arguments.push(self.coerce_argument(argument, *source_parameter, span)?);
        }
        let erased_result = crate::runtime_types::grade_erases(source_signature.result_grade);
        let call = Expr {
            kind: ExprKind::Call(Target::Function(source), arguments),
            ty: if erased_result {
                Type::Unit
            } else {
                source_signature.result
            },
            span,
            resource: None,
        };
        let result = if erased_result {
            call
        } else {
            self.coerce(call, target.result, span)?
        };
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(result)),
            ty: if crate::runtime_types::grade_erases(target.result_grade) {
                Type::Unit
            } else {
                target.result
            },
        };
        self.check_adapter_effects(&body, &target, span)?;
        let pure_id = self.types.function_type_with(
            target.parameters.clone(),
            target.result,
            target.effects,
            target.parameter_grades.clone(),
            target.result_grade,
            false,
            false,
            target.borrows.clone(),
        );
        let index =
            self.register_adapter("fn adapter", &target, vec![], false, locals, body, span)?;
        self.functions.adapter_cache.insert(key, index);
        Ok(Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![],
            },
            ty: Type::Fn(pure_id),
            span,
            resource: None,
        })
    }
    /// A no-allocation once-callable thunk for a statically known pure source.
    /// The once ABI passes an environment word; this wrapper ignores it and
    /// directly calls the source function.
    pub(super) fn once_thunk(
        &mut self,
        source: usize,
        target_id: usize,
        span: Span,
    ) -> Result<Expr> {
        let key = (Some(source), Type::Once(0), Type::Fn(target_id));
        if let Some(index) = self.functions.adapter_cache.get(&key).copied() {
            return Ok(Expr {
                kind: ExprKind::FnValue {
                    function: index,
                    captures: vec![],
                },
                ty: Type::Once(target_id),
                span,
                resource: None,
            });
        }
        let target = self.types.function_types[target_id].clone();
        let source_signature = self.functions.signatures[source].clone();
        let locals = target
            .parameters
            .iter()
            .map(|ty| Local {
                ty: *ty,
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span,
            })
            .collect::<Vec<_>>();
        let mut arguments = Vec::with_capacity(target.parameters.len());
        for (index, (target_parameter, source_parameter)) in target
            .parameters
            .iter()
            .zip(&source_signature.parameters)
            .enumerate()
        {
            if target.parameter_erased(index) || source_signature.parameter_erased(index) {
                // One side of this conversion has no physical slot. The
                // adapter must not read an unmaterialized local or treat the
                // value as ABI-compatible; the erased position is evaluated as
                // a dummy and dropped by the callee's own erasure.
                arguments.push(Expr {
                    kind: ExprKind::Erased(*source_parameter),
                    ty: *source_parameter,
                    span,
                    resource: None,
                });
                continue;
            }
            let argument = Expr {
                kind: ExprKind::Local(index),
                ty: *target_parameter,
                span,
                resource: None,
            };
            arguments.push(self.coerce_argument(argument, *source_parameter, span)?);
        }
        let erased_result = crate::runtime_types::grade_erases(source_signature.result_grade);
        let call = Expr {
            kind: ExprKind::Call(Target::Function(source), arguments),
            ty: if erased_result {
                Type::Unit
            } else {
                source_signature.result
            },
            span,
            resource: None,
        };
        let result = if erased_result {
            call
        } else {
            self.coerce(call, target.result, span)?
        };
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(result)),
            ty: if crate::runtime_types::grade_erases(target.result_grade) {
                Type::Unit
            } else {
                target.result
            },
        };
        self.check_adapter_effects(&body, &target, span)?;
        let index =
            self.register_adapter("once fn thunk", &target, vec![], true, locals, body, span)?;
        self.functions.adapter_cache.insert(key, index);
        Ok(Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![],
            },
            ty: Type::Once(target_id),
            span,
            resource: None,
        })
    }
    /// Register the checked adapter body used by a capturing callable
    /// conversion. The adapter's first local is the source callable and it
    /// calls that value indirectly. The returned function index is shared by
    /// ordinary closure conversion and by a structural field conversion, so
    /// both paths use one checked adapter per signature.
    pub(super) fn call_adapter(
        &mut self,
        source_ty: Type,
        target_id: usize,
        span: Span,
    ) -> Result<usize> {
        self.require(ALLOC | PANIC, span)?;
        let target = self.types.function_types[target_id].clone();
        let (source_id, _) = Self::function_parts(source_ty).expect("checked callable");
        let source = self.types.function_types[source_id].clone();
        let mut locals = vec![Local {
            ty: source_ty,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span,
        }];
        locals.extend(target.parameters.iter().map(|ty| Local {
            ty: *ty,
            mutable: false,
            linear: false,
            pinned: false,
            grade: None,
            span,
        }));
        let callee = Expr {
            kind: ExprKind::Local(0),
            ty: source_ty,
            span,
            resource: None,
        };
        let mut arguments = Vec::with_capacity(target.parameters.len());
        for (index, (target_parameter, source_parameter)) in
            target.parameters.iter().zip(&source.parameters).enumerate()
        {
            if target.parameter_erased(index) || source.parameter_erased(index) {
                arguments.push(Expr {
                    kind: ExprKind::Erased(*source_parameter),
                    ty: *source_parameter,
                    span,
                    resource: None,
                });
                continue;
            }
            let argument = Expr {
                kind: ExprKind::Local(index + 1),
                ty: *target_parameter,
                span,
                resource: None,
            };
            arguments.push(self.coerce_argument(argument, *source_parameter, span)?);
        }
        let erased_result = crate::runtime_types::grade_erases(source.result_grade);
        let call = Expr {
            kind: ExprKind::CallIndirect {
                callee: Box::new(callee),
                arguments,
            },
            ty: if erased_result {
                Type::Unit
            } else {
                source.result
            },
            span,
            resource: None,
        };
        let result = if erased_result {
            call
        } else {
            self.coerce(call, target.result, span)?
        };
        let body = Block {
            statements: vec![],
            tail: Some(Box::new(result)),
            ty: if crate::runtime_types::grade_erases(target.result_grade) {
                Type::Unit
            } else {
                target.result
            },
        };
        self.check_adapter_effects(&body, &target, span)?;
        self.register_adapter(
            "once fn adapter",
            &target,
            vec![source_ty],
            false,
            locals,
            body,
            span,
        )
    }
    /// A once-consuming capturing adapter. The source callable is moved into
    /// the closure environment exactly once; a call consumes it and the
    /// callee's normal cleanup drops any remaining captures.
    pub(super) fn closure_adapter(
        &mut self,
        value: Expr,
        target_id: usize,
        span: Span,
    ) -> Result<Expr> {
        let source_ty = value.ty;
        let index = self.call_adapter(source_ty, target_id, span)?;
        Ok(Expr {
            kind: ExprKind::FnValue {
                function: index,
                captures: vec![value],
            },
            ty: Type::Once(target_id),
            span,
            resource: None,
        })
    }
}
