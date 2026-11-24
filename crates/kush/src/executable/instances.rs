//! Function instances: specialization, signatures, adapters and inferred rows.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl<'a> Functions<'a> {
    /// The concrete self type of a method instance, if it belongs to an impl.
    pub(super) fn self_type_for(
        &self,
        binding: BindingId,
        impl_arguments: Option<usize>,
    ) -> Option<Type> {
        if let Some(index) = impl_arguments {
            return Some(self.impl_instantiations[index].self_type);
        }
        self.declared
            .get(&binding)
            .and_then(|declared| declared.self_ty)
    }
    /// The concrete trait specialization of a method instance. Concrete impl
    /// methods and inherited defaults derive it from the impl registration;
    /// generic impls derive it from the selected instantiation.
    pub(super) fn trait_arguments_for(
        &self,
        binding: BindingId,
        impl_arguments: Option<usize>,
    ) -> Option<TraitArguments> {
        if let Some(index) = impl_arguments {
            return Some(self.impl_instantiations[index].trait_arguments.clone());
        }
        let declared = self.declared.get(&binding)?;
        let index = declared.default_specialization?;
        Some(self.default_specializations[index].1.clone())
    }
    /// Intern one concrete instantiation of a generic impl header and compute
    /// its receiver type and trait specialization. Deduplicated so each method
    /// body is checked once per impl-argument list.
    pub(super) fn intern_impl(
        &mut self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        header: usize,
        arguments: ImplArguments,
    ) -> Result<usize> {
        if let Some(index) = self
            .impl_instantiation_cache
            .get(&(header, arguments.clone()))
        {
            return Ok(*index);
        }
        let definition = self.impl_headers[header].clone();
        let substitution = impl_arguments_subst(resolution, &definition.generics, &arguments);
        let self_type = types.ty_in(&definition.self_ty, &substitution)?;
        let trait_arguments = match definition.trait_id {
            Some(trait_id) => {
                let generics = self.traits[&trait_id].generics.clone();
                evaluate_trait_arguments(
                    types,
                    resolution,
                    self.logical,
                    &generics,
                    &definition.trait_arguments,
                    &substitution,
                    &resolution.bindings[trait_id].name,
                    definition.span,
                )?
            }
            None => TraitArguments::default(),
        };
        let index = self.impl_instantiations.len();
        self.impl_instantiations.push(ImplInstantiation {
            header,
            arguments: arguments.clone(),
            self_type,
            trait_arguments,
        });
        self.impl_instantiation_cache
            .insert((header, arguments), index);
        Ok(index)
    }
    /// Whether a trait obligation is met by an exact concrete impl or by at
    /// least one applicable generic impl. Used for impl-header bounds and
    /// bounded-generic discharge.
    pub(super) fn obligation_holds(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        trait_id: BindingId,
        required: &TraitArguments,
        self_ty: Type,
        depth: usize,
    ) -> Result<bool> {
        if self
            .trait_impls
            .contains_key(&(trait_id, required.clone(), self_ty))
        {
            return Ok(true);
        }
        if depth >= 8 {
            return Ok(false);
        }
        Ok(!self
            .matching_impls(types, resolution, trait_id, required, self_ty, depth + 1)?
            .is_empty())
    }
    /// All generic impls of `trait_id` whose header pattern matches the
    /// concrete receiver and trait arguments, with their generic parameters
    /// solved. Declaration-time coherence guarantees that any two matches are
    /// specialization-comparable; dispatch still checks for a unique most
    /// specific match.
    pub(super) fn matching_impls(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        trait_id: BindingId,
        required: &TraitArguments,
        self_ty: Type,
        depth: usize,
    ) -> Result<Vec<ImplMatch>> {
        if depth >= 8 {
            return Ok(Vec::new());
        }
        let definition = self.traits[&trait_id].clone();
        let mut out = Vec::new();
        for (index, header) in self.impl_headers.iter().enumerate() {
            if header.trait_id != Some(trait_id) || header.concrete.is_some() {
                continue;
            }
            let mut bindings = PatternBindings::default();
            if !match_type_pattern(
                resolution,
                types,
                &header.self_ty,
                self_ty,
                &mut bindings,
                0,
            )? {
                continue;
            }
            if !match_trait_argument_patterns(
                resolution,
                types,
                self.logical,
                &definition.generics,
                &header.trait_arguments,
                required,
                &mut bindings,
            )? {
                continue;
            }
            let solved = solved_impl_arguments(resolution, &header.generics, &bindings);
            let mut bounds_hold = true;
            for generic in &header.generics {
                let Some(bound) = &generic.bound else {
                    continue;
                };
                let Some(bound_trait) = resolution.reference(bound.span) else {
                    continue;
                };
                if resolution.bindings[bound_trait].kind != BindingKind::Trait {
                    continue;
                }
                let argument_ast = match &bound.kind {
                    ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                    _ => Vec::new(),
                };
                let bound_generics = self.traits[&bound_trait].generics.clone();
                let subst = bindings.subst();
                let required_bound = evaluate_trait_arguments(
                    types,
                    resolution,
                    self.logical,
                    &bound_generics,
                    &argument_ast,
                    &subst,
                    &resolution.bindings[bound_trait].name,
                    generic.span,
                )?;
                let actual = bindings
                    .types
                    .get(&resolution.binder(generic.span).unwrap())
                    .copied()
                    .expect("matched header parameter is solved");
                if !self.obligation_holds(
                    types,
                    resolution,
                    bound_trait,
                    &required_bound,
                    actual,
                    depth + 1,
                )? {
                    bounds_hold = false;
                    break;
                }
            }
            if bounds_hold {
                out.push(ImplMatch {
                    header: index,
                    arguments: solved,
                });
            }
        }
        Ok(out)
    }
    /// Match only the self-type pattern of an impl header against a concrete
    /// receiver. Used by unqualified dispatch, which must discover every trait
    /// that could provide a name before selecting a specialization.
    pub(super) fn match_header_for_receiver(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        header_index: usize,
        self_ty: Type,
        depth: usize,
    ) -> Result<Option<ImplMatch>> {
        let header = self.impl_headers[header_index].clone();
        if header.concrete.is_some() {
            return Ok(None);
        }
        let mut bindings = PatternBindings::default();
        if !match_type_pattern(
            resolution,
            types,
            &header.self_ty,
            self_ty,
            &mut bindings,
            0,
        )? {
            return Ok(None);
        }
        // Unqualified dispatch sees only the receiver. A parameter determined
        // solely by a trait argument cannot be solved here; returning `None`
        // leaves the call to explicit qualification instead of instantiating an
        // arbitrary representative.
        for generic in &header.generics {
            let binder = resolution.binder(generic.span).unwrap();
            let solved = match generic_category(resolution, generic) {
                GenericCategory::Type => bindings.types.contains_key(&binder),
                GenericCategory::Const => bindings.consts.contains_key(&binder),
                GenericCategory::Grade => bindings.grades.contains_key(&binder),
                GenericCategory::Effect => bindings.effects.contains_key(&binder),
            };
            if !solved {
                return Ok(None);
            }
        }
        let arguments = solved_impl_arguments(resolution, &header.generics, &bindings);
        for generic in &header.generics {
            let Some(bound) = &generic.bound else {
                continue;
            };
            let Some(bound_trait) = resolution.reference(bound.span) else {
                continue;
            };
            if resolution.bindings[bound_trait].kind != BindingKind::Trait {
                continue;
            }
            let argument_ast = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                _ => Vec::new(),
            };
            let bound_generics = self.traits[&bound_trait].generics.clone();
            let subst = bindings.subst();
            let required = evaluate_trait_arguments(
                types,
                resolution,
                self.logical,
                &bound_generics,
                &argument_ast,
                &subst,
                &resolution.bindings[bound_trait].name,
                generic.span,
            )?;
            let actual = bindings
                .types
                .get(&resolution.binder(generic.span).unwrap())
                .copied()
                .expect("matched header parameter is solved");
            if !self.obligation_holds(
                types,
                resolution,
                bound_trait,
                &required,
                actual,
                depth + 1,
            )? {
                return Ok(None);
            }
        }
        Ok(Some(ImplMatch {
            header: header_index,
            arguments,
        }))
    }
    /// The concrete trait specialization produced by one solved impl header.
    pub(super) fn trait_arguments_for_match(
        &self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        header_index: usize,
        arguments: &ImplArguments,
    ) -> Result<TraitArguments> {
        let header = self.impl_headers[header_index].clone();
        let Some(trait_id) = header.trait_id else {
            return Ok(TraitArguments::default());
        };
        if let Some(index) = self
            .impl_instantiation_cache
            .get(&(header_index, arguments.clone()))
        {
            return Ok(self.impl_instantiations[*index].trait_arguments.clone());
        }
        let subst = impl_arguments_subst(resolution, &header.generics, arguments);
        // The trait arguments may themselves mention impl type parameters; the
        // substitution above already covers every category.
        let generics = self.traits[&trait_id].generics.clone();
        evaluate_trait_arguments(
            types,
            resolution,
            self.logical,
            &generics,
            &header.trait_arguments,
            &subst,
            &resolution.bindings[trait_id].name,
            header.span,
        )
    }
    /// Pick the unique most-specific match. Coherence has already rejected
    /// incomparable overlaps; a remaining tie is an internal ambiguity error
    /// rather than an arbitrary declaration-order choice.
    pub(super) fn select_most_specific(
        &self,
        resolution: &Resolution,
        matches: &[ImplMatch],
    ) -> Option<ImplMatch> {
        if matches.len() == 1 {
            return matches.first().cloned();
        }
        let mut candidates = Vec::new();
        for candidate in matches {
            let mut dominated = false;
            for other in matches {
                if candidate.header == other.header && candidate.arguments == other.arguments {
                    continue;
                }
                let a = &self.impl_headers[candidate.header];
                let b = &self.impl_headers[other.header];
                if header_subsumes(resolution, a, b) && !header_subsumes(resolution, b, a) {
                    // The other header is more specific.
                    dominated = true;
                    break;
                }
            }
            if !dominated {
                candidates.push(candidate.clone());
            }
        }
        (candidates.len() == 1).then(|| candidates.remove(0))
    }

    /// A fresh, unspellable identity for one elided input borrow. Every elided
    /// input gets its own identity, so independent inputs never collapse into a
    /// single inferred lifetime.
    pub(super) fn fresh_elided_lifetime(&mut self) -> String {
        let index = self.elided_lifetimes;
        self.elided_lifetimes += 1;
        format!("<elided lifetime {index}>")
    }
    /// The proposition of an erased parameter, over earlier runtime parameters.
    pub(super) fn proposition(
        &self,
        resolution: &Resolution,
        parameter: &ast::Parameter,
    ) -> Result<crate::facts::Proposition> {
        let f = self
            .declared
            .values()
            .find(|d| d.ast.parameters.iter().any(|p| std::ptr::eq(p, parameter)))
            .map(|d| d.ast)
            .expect("parameter of a declared function");
        proposition_of(resolution, f, parameter)
    }
    /// Find or create the instance of `binding` for a concrete list of type,
    /// grade, and compile-time natural arguments. New instances are queued for
    /// body checking.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn instance(
        &mut self,
        types: &mut Types<'a>,
        resolution: &Resolution,
        binding: BindingId,
        type_arguments: Vec<Type>,
        grade_arguments: Vec<Grade>,
        const_arguments: Vec<usize>,
        effect_arguments: Vec<u16>,
        impl_arguments: Option<usize>,
        origin: Option<Span>,
    ) -> Result<usize> {
        let key = (
            binding,
            type_arguments,
            grade_arguments,
            const_arguments,
            effect_arguments,
            impl_arguments,
        );
        if let Some(index) = self.instances.get(&key) {
            return Ok(*index);
        }
        let declared = self.declared[&binding];
        let f = declared.ast;
        let count = self.instance_counts.entry(binding).or_default();
        if *count >= MAX_INSTANCES {
            return Err(Diagnostic::new(
                origin.unwrap_or(declared.span),
                "executable limit exceeded (256 instances of one function); polymorphic recursion cannot be specialized",
            ));
        }
        *count += 1;
        let (_, key_types, key_grades, key_naturals, key_effects, key_impl) = &key;
        if !(key_types.is_empty()
            && key_grades.is_empty()
            && key_naturals.is_empty()
            && key_effects.is_empty()
            && key_impl.is_none())
        {
            if self.generic_instances >= MAX_GENERIC_INSTANCES {
                return Err(Diagnostic::new(
                    origin.unwrap_or(declared.span),
                    "executable limit exceeded (1024 instances of generic functions in all; polymorphic recursion, or very many distinct specializations)",
                ));
            }
            self.generic_instances += 1;
        }
        let mut type_generics = Vec::new();
        let mut grade_generics = Vec::new();
        let mut const_generics = Vec::new();
        let mut effect_generics = Vec::new();
        for generic in &f.generics {
            if is_grade_generic(resolution, generic) {
                grade_generics.push(generic);
            } else if is_const_generic(resolution, generic) {
                const_generics.push(generic);
            } else if crate::runtime_types::is_effect_generic(resolution, generic) {
                effect_generics.push(generic);
            } else {
                type_generics.push(generic);
            }
        }
        if type_generics.len() != key.1.len()
            || grade_generics.len() != key.2.len()
            || const_generics.len() != key.3.len()
            || effect_generics.len() != key.4.len()
        {
            return Err(Diagnostic::new(
                origin.unwrap_or(declared.span),
                "internal error: generic specialization argument count does not match its category",
            ));
        }
        // Every explicit, inferred, or forwarded effect argument reaches this
        // single specialization point, including arguments for methods and
        // materialized trait defaults. A bounded binder `<e: Effects - ...>`
        // restricts which concrete rows are valid, and `<e: Effects + ...>`
        // requires bits in every specialization; neither hides or subtracts an
        // effect from the declaration's own row.
        for (generic, effects) in effect_generics.iter().zip(&key.4) {
            let excluded = crate::runtime_types::effect_excludes(resolution, generic)?.unwrap_or(0);
            let illegal = effects & excluded;
            if illegal != 0 {
                return Err(Diagnostic::new(
                    origin.unwrap_or(generic.span),
                    format!(
                        "effect argument {{{}}} for '{}' includes {}, which is excluded by '<{}: Effects - {}>'",
                        effect_names(resolution, *effects),
                        generic.name,
                        effect_names(resolution, illegal),
                        generic.name,
                        effect_names(resolution, excluded)
                    ),
                ));
            }
            let included = crate::runtime_types::effect_includes(resolution, generic)?.unwrap_or(0);
            let missing = included & !effects;
            if missing != 0 {
                return Err(Diagnostic::new(
                    origin.unwrap_or(generic.span),
                    format!(
                        "effect argument {{{}}} for '{}' omits {}, which is required by '<{}: Effects + {}>'",
                        effect_names(resolution, *effects),
                        generic.name,
                        effect_names(resolution, missing),
                        generic.name,
                        effect_names(resolution, included)
                    ),
                ));
            }
        }
        // A structural row type argument is a monomorphized canonical row, not
        // an erased lifetime-bearing nominal identity: its borrowed fields keep
        // their provenance through the ordinary structural conversion rules.
        // This is what lets a row variable preserve a borrowed field. Nominal
        // borrowed records still cannot cross an ordinary generic parameter.
        if key
            .1
            .iter()
            .any(|ty| crate::runtime_types::has_borrow(types, *ty) && !types.is_structural(*ty))
        {
            return Err(Diagnostic::new(
                origin.unwrap_or(declared.span),
                "a borrowed record cannot be passed through an ordinary generic type parameter; lifetimes are not erased at this boundary",
            ));
        }
        let mut substitution = crate::runtime_types::Subst {
            self_type: declared.self_ty,
            ..Default::default()
        };
        for (g, ty) in type_generics.iter().zip(&key.1) {
            substitution
                .types
                .insert(resolution.binder(g.span).unwrap(), *ty);
        }
        let mut const_substitution = const_generics
            .iter()
            .zip(&key.3)
            .map(|(g, value)| (resolution.binder(g.span).unwrap(), *value))
            .collect::<BTreeMap<_, _>>();
        let mut grade_substitution = grade_generics
            .iter()
            .zip(&key.2)
            .map(|(g, grade)| (resolution.binder(g.span).unwrap(), *grade))
            .collect::<BTreeMap<_, _>>();
        let mut effect_substitution = effect_generics
            .iter()
            .zip(&key.4)
            .map(|(g, effects)| (resolution.binder(g.span).unwrap(), *effects))
            .collect::<BTreeMap<_, _>>();
        // A generic impl supplies concrete values for its own parameters. They
        // join the same substitution maps as the method's generics; the
        // declaration rejects a method binder that reuses an impl parameter
        // name, so the keys cannot collide.
        if let Some(index) = impl_arguments {
            let instantiation = self.impl_instantiations[index].clone();
            let header = self.impl_headers[instantiation.header].clone();
            for (generic, ty) in header.generics.iter().zip(&instantiation.arguments.types) {
                substitution
                    .types
                    .insert(resolution.binder(generic.span).unwrap(), *ty);
            }
        }
        // A materialized trait default also needs its trait's concrete
        // arguments. `Self` is substituted above and trait parameters are
        // ordinary binders, so they join the same substitution maps. Method
        // parameters may not reuse a trait parameter name, so the keys cannot
        // collide.
        if let Some(index) = declared.default_specialization {
            let (trait_id, stored) = self.default_specializations[index].clone();
            let arguments = self
                .trait_arguments_for(binding, impl_arguments)
                .unwrap_or(stored);
            let definition = self.traits[&trait_id].clone();
            insert_trait_arguments(
                resolution,
                &definition.generics,
                &arguments,
                &mut substitution,
                &mut const_substitution,
                &mut grade_substitution,
                &mut effect_substitution,
            );
        }
        substitution.consts = const_substitution.clone();
        substitution.grades = grade_substitution.clone();
        substitution.effects = effect_substitution.clone();
        // Normalize `Self::Item` through this impl's associated values. The
        // value is an AST type, so it is lowered with the same substitution
        // and may mention the impl's generic parameters.
        let mut associated_consts = BTreeMap::new();
        if let Some(index) = declared.impl_associated {
            let associated = self.impl_associated[index].clone();
            substitution.associated_types = associated.types;
            associated_consts = associated.consts;
        }
        // `Self` for a generic impl is its header pattern lowered with the
        // concrete impl arguments selected by dispatch.
        let instantiated_self =
            impl_arguments.map(|index| self.impl_instantiations[index].self_type);
        substitution.self_type = instantiated_self.or(declared.self_ty);
        // A type argument may not name a runtime-length binder of the function
        // being instantiated. Only a recursive call can write one, and in the
        // new activation that binder holds a different value, so a value of
        // the old length would get the new length's type.
        // An inherited trait default runs under a synthesized per-impl
        // binding, but its parameters and locals are owned by the trait
        // method's own binding; both count as the function's own.
        let body_owner = f
            .parameters
            .iter()
            .find_map(|parameter| resolution.binder(parameter.span))
            .and_then(|parameter| resolution.bindings[parameter].owner);
        for ty in substitution.types.values().chain(&substitution.self_type) {
            let captured = crate::runtime_types::runtime_length_binders(types, *ty)
                .into_iter()
                .find(|binder| {
                    let owner = resolution.bindings[*binder].owner;
                    owner == Some(binding) || (owner.is_some() && owner == body_owner)
                });
            if let Some(binder) = captured {
                return Err(Diagnostic::new(
                    origin.unwrap_or(declared.span),
                    format!(
                        "a type argument of '{}' mentions its own length binder '{}'; each call gets a new '{}', so pass the array as an ordinary runtime-length parameter instead",
                        f.name, resolution.bindings[binder].name, resolution.bindings[binder].name
                    ),
                ));
            }
        }
        // Projections in an impl's own associated values may depend on a bound
        // of an impl parameter, as in `impl<T: Show> Wrap for W<T> { type Out =
        // T.Out; }`. Install those projections before lowering signatures.
        if let Some(index) = impl_arguments {
            let instantiation = self.impl_instantiations[index].clone();
            let header = self.impl_headers[instantiation.header].clone();
            for (generic, actual) in header.generics.iter().zip(&instantiation.arguments.types) {
                let Some(bound) = &generic.bound else {
                    continue;
                };
                let Some(trait_id) = resolution.reference(bound.span) else {
                    continue;
                };
                if resolution.bindings[trait_id].kind != BindingKind::Trait {
                    continue;
                }
                let argument_ast = match &bound.kind {
                    ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                    _ => Vec::new(),
                };
                let definition = self.traits[&trait_id].clone();
                let required = evaluate_trait_arguments(
                    types,
                    resolution,
                    self.logical,
                    &definition.generics,
                    &argument_ast,
                    &substitution,
                    &resolution.bindings[trait_id].name,
                    generic.span,
                )?;
                let binder = resolution.binder(generic.span).unwrap();
                if let Some(associated) = self
                    .trait_associated
                    .get(&(trait_id, required.clone(), *actual))
                    .cloned()
                {
                    for (name, value) in associated.types {
                        let lowered = types.ty_in(&value, &substitution)?;
                        substitution.projections.insert((binder, name), lowered);
                    }
                } else if let Some(selected) = self.select_most_specific(
                    resolution,
                    &self.matching_impls(types, resolution, trait_id, &required, *actual, 0)?,
                ) {
                    let selected_header = self.impl_headers[selected.header].clone();
                    let mut impl_substitution = substitution.clone();
                    for (impl_generic, ty) in selected_header
                        .generics
                        .iter()
                        .zip(&selected.arguments.types)
                    {
                        impl_substitution
                            .types
                            .insert(resolution.binder(impl_generic.span).unwrap(), *ty);
                    }
                    for (name, value) in selected_header.associated.types {
                        let lowered = types.ty_in(&value, &impl_substitution)?;
                        substitution.projections.insert((binder, name), lowered);
                    }
                }
            }
        }
        // Trait bounds are discharged at specialization time, before the body
        // is checked. A missing impl is an error even when the body never calls
        // a trait method. Bound arguments are substituted through this
        // instance's generic arguments, so `T: Convert<U>` selects the impl for
        // the concrete `U`.
        for (generic, actual) in type_generics.iter().zip(&key.1) {
            let Some(bound) = &generic.bound else {
                continue;
            };
            let Some(trait_id) = resolution.reference(bound.span) else {
                continue;
            };
            if resolution.bindings[trait_id].kind != BindingKind::Trait {
                continue;
            }
            let bound_arguments = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.clone(),
                _ => Vec::new(),
            };
            let definition = self.traits[&trait_id].clone();
            let required = evaluate_trait_arguments(
                types,
                resolution,
                self.logical,
                &definition.generics,
                &bound_arguments,
                &substitution,
                &resolution.bindings[trait_id].name,
                generic.span,
            )?;
            if !self.obligation_holds(types, resolution, trait_id, &required, *actual, 0)? {
                let trait_name = &resolution.bindings[trait_id].name;
                let specialization = if definition.generics.is_empty() {
                    trait_name.clone()
                } else {
                    format!(
                        "{trait_name}<{}>",
                        trait_specialization_name(
                            resolution,
                            types,
                            &definition.generics,
                            &required
                        )
                    )
                };
                return Err(Diagnostic::new(
                    generic.span,
                    format!(
                        "type '{}' does not implement trait '{specialization}' required by '{}: {}'",
                        types.name(*actual),
                        generic.name,
                        specialization
                    ),
                ));
            }
            let binder = resolution
                .binder(generic.span)
                .expect("generic parameter has a binder");
            if let Some(associated) = self
                .trait_associated
                .get(&(trait_id, required.clone(), *actual))
                .cloned()
            {
                for (name, value) in associated.types {
                    let lowered = types.ty_in(&value, &substitution)?;
                    substitution.projections.insert((binder, name), lowered);
                }
            } else {
                // A generic impl supplies the projection. Solve it and lower
                // the associated value with both the method's and the impl's
                // parameters substituted.
                let matches =
                    self.matching_impls(types, resolution, trait_id, &required, *actual, 0)?;
                if let Some(selected) = self.select_most_specific(resolution, &matches) {
                    let header = self.impl_headers[selected.header].clone();
                    let mut impl_substitution = substitution.clone();
                    for (impl_generic, ty) in header.generics.iter().zip(&selected.arguments.types)
                    {
                        impl_substitution
                            .types
                            .insert(resolution.binder(impl_generic.span).unwrap(), *ty);
                    }
                    for (name, value) in header.associated.types {
                        let lowered = types.ty_in(&value, &impl_substitution)?;
                        substitution.projections.insert((binder, name), lowered);
                    }
                }
            }
        }
        let mut parameters = Vec::new();
        let mut parameter_grades = Vec::new();
        let mut parameter_lifetimes = Vec::new();
        let mut parameter_binders = Vec::new();
        let mut parameter_binder_lifetimes = BTreeMap::new();
        let mut parameter_field_lifetimes: BTreeMap<BindingId, BTreeMap<String, String>> =
            BTreeMap::new();
        let mut declared_lifetimes = BTreeSet::new();
        let mut input_lifetimes: Vec<(String, Span, Option<String>)> = Vec::new();
        for lifetime in &f.lifetimes {
            if !declared_lifetimes.insert(lifetime.name.clone()) {
                return Err(Diagnostic::new(
                    lifetime.span,
                    format!("duplicate lifetime parameter '{}'", lifetime.name),
                ));
            }
            if f.generics
                .iter()
                .any(|generic| generic.name == lifetime.name)
            {
                return Err(Diagnostic::new(
                    lifetime.span,
                    "lifetime parameters must be distinct from type, natural, grade, and effect generics",
                ));
            }
        }
        let mut lifetime_bounds = build_lifetime_bounds(&f.lifetimes)?;
        for p in f.parameters.iter().filter(|p| !p.erased) {
            let (ty, grade) = split_grade(&p.ty);
            if !matches!(ty.kind, ast::TypeKind::Capability { .. }) {
                reject_capability_type(ty)?;
            }
            parameters.push(types.ty_in(ty, &substitution)?);
            parameter_grades.push(
                grade
                    .map(|grade| grades::evaluate(resolution, &grade_substitution, grade))
                    .transpose()?,
            );
            let mut used = BTreeSet::new();
            type_lifetimes(ty, &mut used);
            if let Some(unknown) = used.iter().find(|name| !declared_lifetimes.contains(*name)) {
                return Err(Diagnostic::new(
                    p.ty.span,
                    format!(
                        "undeclared lifetime '{unknown}'; declare it in the function's lifetime parameter list"
                    ),
                ));
            }
            let explicit_lifetime = borrow_lifetime(ty);
            let lifetime = match &explicit_lifetime {
                Some(name) => Some(name.clone()),
                None if matches!(&ty.kind, ast::TypeKind::Borrow { .. }) => {
                    // Each elided input borrow is independent. It gets a fresh
                    // internal identity rather than a shared default lifetime.
                    Some(self.fresh_elided_lifetime())
                }
                None => None,
            };
            if let Some(name) = &lifetime
                && !input_lifetimes
                    .iter()
                    .any(|(existing, _, _)| existing == name)
            {
                input_lifetimes.push((name.clone(), p.ty.span, explicit_lifetime));
            }
            parameter_lifetimes.push(lifetime.clone());
            let binder = resolution.binder(p.span);
            parameter_binders.push(binder);
            if let (Some(binder), Some(name)) = (binder, &lifetime) {
                parameter_binder_lifetimes.insert(binder, name.clone());
            }
            if let Some(binder) = binder {
                let mut fields = BTreeMap::new();
                collect_parameter_field_lifetimes(
                    types,
                    parameters.last().copied().unwrap(),
                    &mut fields,
                )?;
                if !fields.is_empty() {
                    parameter_field_lifetimes.insert(binder, fields);
                }
            }
            // A by-value borrowed record contributes one candidate per field
            // lifetime, so elided slice results can be inferred from a single
            // record source exactly as from a single slice parameter.
            if crate::runtime_types::is_borrowed_record(types, parameters.last().copied().unwrap())
            {
                let mut record_lifetimes = BTreeSet::new();
                for leaf in
                    crate::runtime_types::borrow_leaves(types, parameters.last().copied().unwrap())?
                {
                    if let Some(name) = leaf.lifetime {
                        record_lifetimes.insert(name.clone());
                        if !input_lifetimes
                            .iter()
                            .any(|(existing, _, _)| existing == &name)
                        {
                            input_lifetimes.push((name.clone(), p.ty.span, Some(name)));
                        }
                    }
                }
                if let Some(binder) = binder
                    && record_lifetimes.len() == 1
                    && !parameter_binder_lifetimes.contains_key(&binder)
                {
                    parameter_binder_lifetimes
                        .insert(binder, record_lifetimes.into_iter().next().unwrap());
                }
            }
        }
        if let Some(body) = &f.body {
            // Local destructuring and simple aliases can carry a parameter
            // lifetime into the return position. Propagate them before the
            // result lifetime seed is chosen.
            collect_local_lifetimes(
                resolution,
                &self.declared,
                body,
                &mut parameter_binder_lifetimes,
                &mut parameter_field_lifetimes,
            );
        }
        let parameter_nested_lifetimes = f
            .parameters
            .iter()
            .filter(|parameter| !parameter.erased)
            .map(|parameter| nested_borrow_lifetime(&parameter.ty))
            .collect::<Vec<_>>();
        let (result_ty, result_grade) =
            result_contract(resolution, types, &grade_substitution, &f.result)?;
        let result = types.ty_in(&result_ty, &substitution)?;
        validate_result_contract(
            result_grade,
            crate::runtime_types::type_owns(&types.enums, &types.unions, result, 0),
            &types.name(result),
            f.result.span,
        )?;
        let mut used = BTreeSet::new();
        type_lifetimes(&f.result, &mut used);
        if let Some(unknown) = used.iter().find(|name| !declared_lifetimes.contains(*name)) {
            return Err(Diagnostic::new(
                f.result.span,
                format!(
                    "undeclared lifetime '{unknown}'; declare it in the function's lifetime parameter list"
                ),
            ));
        }
        // Lifetime analysis intentionally uses the written result type, not the
        // alias-expanded runtime type, so an alias result keeps the existing
        // explicit-lifetime requirement. Result *grades* are separate metadata
        // and are already split above.
        let written_result = split_grade(&f.result).0;
        let explicit_result_lifetime = borrow_lifetime(written_result);
        let result_was_explicit = explicit_result_lifetime.is_some();
        // Resolve an elided borrowed structural result field from the
        // function's single input borrow lifetime before result metadata is
        // collected. This mirrors ordinary slice-result elision; every other
        // case stays unresolved and is rejected below.
        let result =
            resolve_elided_structural_result(types, result, &input_lifetimes, f.result.span)?;
        // Stable parameter-leaf origins solved over the concrete call graph.
        // Map each origin back to this instance's declared or elided lifetime
        // labels. Every origin must map to a real lifetime: rejecting an
        // unmapped path keeps a partial summary from masquerading as complete.
        let mut summary_sources = BTreeSet::new();
        // Per-result-leaf outlives edges inferred from the frozen summaries.
        // They are added to `lifetime_bounds` after the result lifetime is
        // chosen, so ownership sees every reachable owner.
        let mut summary_bounds: BTreeSet<(String, String)> = BTreeSet::new();
        let mut result_field_lifetimes = BTreeMap::new();
        collect_parameter_field_lifetimes(types, result, &mut result_field_lifetimes)?;
        if let Some(summary) = self.summaries.get(binding) {
            let map_origin = |origin: &recursive_lifetimes::Origin| {
                summary_origin_lifetime(
                    origin,
                    &parameter_lifetimes,
                    &parameter_binders,
                    &parameter_field_lifetimes,
                )
                .map_err(|what| {
                    Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot map a recursive lifetime summary origin to a declared lifetime: {what}. Annotate the result lifetime explicitly or name the borrowed field's lifetime"
                        ),
                    )
                })
            };
            let mut root_origins = BTreeSet::new();
            for (path, origins) in &summary.leaves {
                if path.is_empty() {
                    root_origins.extend(origins.iter().cloned());
                    if result.is_view() || result.is_ref() {
                        for origin in origins {
                            summary_sources.insert(map_origin(origin)?);
                        }
                    }
                    continue;
                }
                let target = result_field_lifetimes
                    .get(&path.join("."))
                    .cloned()
                    .ok_or_else(|| {
                        Diagnostic::new(
                            f.result.span,
                            format!(
                                "cannot map a recursive lifetime summary result path '{}' to a declared result field lifetime. Annotate the result type explicitly or name the borrowed field's lifetime",
                                path.join(".")
                            ),
                        )
                    })?;
                if summary.inferred_contract {
                    for origin in origins {
                        let source = map_origin(origin)?;
                        if source != target {
                            summary_bounds.insert((source, target.clone()));
                        }
                    }
                }
            }
            // A whole-value origin on a record result contributes to every
            // declared borrowed field. Try the leaf-specific input path first
            // (an identity/forwarding function keeps each field's own owner),
            // then conservatively fall back to the parameter root.
            if summary.inferred_contract
                && !root_origins.is_empty()
                && !(result.is_view() || result.is_ref())
            {
                for (field_path, target) in &result_field_lifetimes {
                    let components = field_path
                        .split('.')
                        .filter(|part| !part.is_empty())
                        .collect::<Vec<_>>();
                    for origin in &root_origins {
                        let mut specific = origin.clone();
                        specific
                            .path
                            .extend(components.iter().map(|part| (*part).to_owned()));
                        let source = match map_origin(&specific) {
                            Ok(source) => source,
                            Err(_) => map_origin(origin)?,
                        };
                        if source != *target {
                            summary_bounds.insert((source, target.clone()));
                        }
                    }
                }
            }
        }
        let result_lifetime = match explicit_result_lifetime {
            Some(lifetime) => Some(lifetime),
            None if (result.is_view() || result.is_ref())
                && matches!(&written_result.kind, ast::TypeKind::Borrow { .. }) =>
            {
                // Conservative elision: infer only when the input side names
                // exactly one distinct borrow lifetime. Independent anonymous
                // inputs stay independent, so their result is ambiguous.
                match input_lifetimes.as_slice() {
                    [] => {
                        return Err(Diagnostic::new(
                            f.result.span,
                            "this borrowed slice result cannot be returned: the function has no borrowed input to infer its lifetime from. Add a borrowed slice parameter or annotate the result explicitly",
                        ));
                    }
                    [(lifetime, _, _)] => Some(lifetime.clone()),
                    candidates => {
                        // More than one input lifetime exists. Infer from the
                        // function body only when every returned value is
                        // syntactically rooted in one parameter lifetime. The
                        // ownership pass still checks that lifetime against
                        // every returned origin, so this seed never widens a
                        // borrow beyond what the body actually returns.
                        let mut returned = Vec::new();
                        if let Some(body) = &f.body {
                            collect_block_returns(body, &mut returned);
                            if let Some(tail) = &body.tail {
                                returned.push(tail);
                            }
                        }
                        let mut body_lifetimes = BTreeSet::new();
                        for value in returned {
                            value_lifetime_candidates(
                                resolution,
                                &self.declared,
                                value,
                                &parameter_binder_lifetimes,
                                &parameter_field_lifetimes,
                                &mut body_lifetimes,
                            );
                        }
                        // The finite fixed point over direct call edges adds
                        // origins that no single syntactic return exposes,
                        // including mutually recursive forwarding. It is a
                        // union with the local seed, never a replacement: every
                        // owner seen either way stays in the summary.
                        body_lifetimes.extend(summary_sources.iter().cloned());
                        let inferred = body_lifetimes.into_iter().collect::<Vec<_>>();
                        if let [only] = inferred.as_slice() {
                            Some(only.clone())
                        } else if inferred.len() > 1 {
                            // The body can return a borrow from several input
                            // lifetimes. The result is an anonymous internal
                            // lifetime: it is outlived by every contributing
                            // source, so both backends still retain all owners
                            // through the result's last use. At a call site the
                            // shortest provable caller lifetime is selected, or
                            // the result stays anonymous when no order can be
                            // proved (see instantiate_result_lifetime).
                            Some(self.fresh_elided_lifetime())
                        } else {
                            let mut diagnostic = Diagnostic::new(
                                f.result.span,
                                if inferred.is_empty() {
                                    format!(
                                        "cannot infer this borrowed slice result's lifetime: the function has {} distinct input borrow lifetimes and its body does not return one directly. Annotate the returned input and the result with one explicit lifetime, as in 'fn f<'a>(s: &'a [i64]) -> &'a [i64]'",
                                        candidates.len()
                                    )
                                } else {
                                    format!(
                                        "cannot infer this borrowed slice result's lifetime from the function body: return positions mention {} distinct parameter lifetimes. Annotate the returned input and the result with one shared lifetime",
                                        inferred.len()
                                    )
                                },
                            );
                            for (_, span, explicit) in candidates {
                                diagnostic = diagnostic.with_note(
                                    *span,
                                    match explicit {
                                        Some(name) => {
                                            format!(
                                                "candidate input lifetime '{name}' declared here"
                                            )
                                        }
                                        None => "candidate elided input borrow declared here"
                                            .to_string(),
                                    },
                                );
                            }
                            return Err(diagnostic);
                        }
                    }
                }
            }
            None => None,
        };
        // Per-field result summaries add the outlives relation needed for
        // every declared result leaf. This is a guarantee, not a caller
        // precondition: it is derived from a possible returned origin.
        for (source, target) in &summary_bounds {
            if source == target || outlives(&lifetime_bounds, source, target) {
                continue;
            }
            if outlives(&lifetime_bounds, target, source) {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "cannot infer an outlives bound for result lifetime '{target}': the returned value can have both the longer lifetime '{source}' and the shorter one; use one shared lifetime or return the record fields with distinct lifetimes"
                    ),
                ));
            }
            lifetime_bounds.insert((source.clone(), target.clone()));
        }
        // Independent required preconditions. These are exported only for an
        // inferable declaration: an explicit outlives bound, trait/impl
        // contract, or function-value arrow is never silently strengthened.
        // Inherent methods own their contract like free functions; a trait
        // impl or generic impl method must match its trait/template exactly.
        let trait_bound_method = declared.impl_template.is_some()
            || self
                .trait_impls
                .values()
                .any(|methods| methods.values().any(|method| method.binding == binding));
        if !trait_bound_method
            && declared.default_specialization.is_none()
            && f.lifetimes
                .iter()
                .all(|lifetime| lifetime.bounds.is_empty())
            && self
                .summaries
                .get(binding)
                .is_some_and(|summary| summary.inferred_contract)
            && let Some(summary) = self.summaries.get(binding)
        {
            for requirement in &summary.requirements {
                let long = requirement_origin_lifetime(
                    &requirement.long,
                    &parameter_lifetimes,
                    &parameter_nested_lifetimes,
                    &parameter_binders,
                    &parameter_field_lifetimes,
                )
                .map_err(|what| {
                    Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot map a recursive lifetime requirement to a declared input lifetime: {what}. Annotate the outlives bound explicitly"
                        ),
                    )
                })?;
                let short = requirement_origin_lifetime(
                    &requirement.short,
                    &parameter_lifetimes,
                    &parameter_nested_lifetimes,
                    &parameter_binders,
                    &parameter_field_lifetimes,
                )
                .map_err(|what| {
                    Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot map a recursive lifetime requirement to a declared input lifetime: {what}. Annotate the outlives bound explicitly"
                        ),
                    )
                })?;
                if long == short || outlives(&lifetime_bounds, &long, &short) {
                    continue;
                }
                if outlives(&lifetime_bounds, &short, &long) {
                    return Err(Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot infer the recursive precondition '{long}: {short}': the opposite relation already holds; use one shared lifetime or bind the values to matching parameters"
                        ),
                    ));
                }
                lifetime_bounds.insert((long, short));
            }
        }
        lifetime_bounds = close_lifetime_bounds(lifetime_bounds);
        // An optional reference may be a parameter: it lives for the call,
        // like any reference argument. A result still needs provenance.
        crate::runtime_types::reject_optional_reference_boundary(types, result, f.result.span)?;
        // An explicit result lifetime need not repeat the caller's declared
        // outlives bounds: when the body returns a parameter borrow that does
        // not already outlive the result, infer that relation. Every returned
        // source contributes, which is conservative when a function can return
        // more than one parameter borrow. The inferred edges are closed
        // transitively and used by the same call-site validation as explicit
        // bounds.
        let inferred_internal_result = result_lifetime
            .as_deref()
            .is_some_and(|name| name.starts_with('<'));
        if (result_was_explicit || inferred_internal_result)
            && (result.is_view() || result.is_ref())
            && let Some(result_lifetime) = &result_lifetime
            && let Some(body) = &f.body
        {
            let mut returned = Vec::new();
            collect_block_returns(body, &mut returned);
            if let Some(tail) = &body.tail {
                returned.push(tail);
            }
            let mut sources = BTreeSet::new();
            for value in returned {
                value_lifetime_candidates(
                    resolution,
                    &self.declared,
                    value,
                    &parameter_binder_lifetimes,
                    &parameter_field_lifetimes,
                    &mut sources,
                );
            }
            // Recursive forwarding contributes its frozen fixed-point origins
            // in addition to the local syntactic seed.
            sources.extend(summary_sources.iter().cloned());
            // An explicit result may only receive bounds from a parameter's
            // own declared lifetime: selecting a different field lifetime of a
            // multi-lifetime record stays an explicit error. An inferred
            // anonymous result may also be bounded by record-field lifetimes,
            // which is exactly the multi-source intersection case.
            let parameter_bound_lifetimes = if inferred_internal_result {
                input_lifetimes
                    .iter()
                    .map(|(name, _, _)| name.clone())
                    .collect::<BTreeSet<_>>()
            } else {
                parameter_lifetimes
                    .iter()
                    .flatten()
                    .cloned()
                    .collect::<BTreeSet<_>>()
            };
            sources.retain(|source| parameter_bound_lifetimes.contains(source));
            for source in sources {
                if source == *result_lifetime
                    || outlives(&lifetime_bounds, &source, result_lifetime)
                {
                    continue;
                }
                if outlives(&lifetime_bounds, result_lifetime, &source) {
                    return Err(Diagnostic::new(
                        f.result.span,
                        format!(
                            "cannot infer an outlives bound for result lifetime '{result_lifetime}': the returned value has the longer lifetime '{source}'; use one shared lifetime instead"
                        ),
                    ));
                }
                lifetime_bounds.insert((source, result_lifetime.clone()));
            }
            lifetime_bounds = close_lifetime_bounds(lifetime_bounds);
        }
        // A structural row may now carry resolved borrow labels from its
        // annotation or a `..r` specialization. Each borrowed leaf is checked
        // below against the parameters that carry it; an unlabelled leaf stays
        // an explicit rejection because no caller lifetime relation can be
        // recovered for it.
        if result.is_view() {
            let Some(lifetime) = &result_lifetime else {
                return Err(Diagnostic::new(
                    f.result.span,
                    if result.is_mut_slice() {
                        "a borrowed '&mut [T]' result cannot be returned without an explicit lifetime, as in '-> &'a mut [T]'"
                    } else if result.is_text() {
                        "a borrowed '&str' result cannot be returned without an explicit lifetime, as in '-> &'a str'"
                    } else {
                        "a borrowed slice result cannot be returned without an explicit lifetime, as in '-> &'a [T]'"
                    },
                ));
            };
            let parameter_leaf_sets = parameters
                .iter()
                .map(|ty| crate::runtime_types::borrow_leaves(types, *ty))
                .collect::<Result<Vec<_>>>()?;
            let matching = parameter_lifetimes
                .iter()
                .zip(parameters.iter())
                .zip(&parameter_leaf_sets)
                .filter(|((parameter, _), leaves)| {
                    parameter
                        .as_ref()
                        .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                        || leaves.iter().any(|leaf| {
                            leaf.lifetime
                                .as_ref()
                                .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                        })
                })
                .map(|((parameter, ty), leaves)| (parameter, ty, leaves))
                .collect::<Vec<_>>();
            if matching.is_empty() {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "result lifetime '{lifetime}' does not appear on any parameter that outlives it; a borrowed return must be tied to caller-owned storage. Declare an outlives bound such as 'fn f<'long: 'short, 'short>(s: &'long [i64]) -> &'short [i64]'"
                    ),
                ));
            }
            if result.is_mut_slice()
                && !matching.iter().any(|(_, ty, leaves)| {
                    ty.is_mut_slice()
                        || leaves.iter().any(|leaf| {
                            leaf.mutable
                                && leaf
                                    .lifetime
                                    .as_ref()
                                    .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                        })
                })
            {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "an exclusive '&mut [T]' result lifetime '{lifetime}' must appear on an exclusive '&mut [T]' parameter that outlives it; shared storage cannot be returned mutably"
                    ),
                ));
            }
        } else if result.is_ref() {
            let pointee = result.ref_pointee().expect("reference pointee");
            // A returned reference must name the caller-owned storage of a
            // matching reference parameter. Nominal records, Box, Vec, Bytes,
            // and String all have stable caller-owned storage when reached
            // through such a parameter; a reference to a by-value parameter or
            // a local remains a dangling-borrow error in the ownership pass.
            let result_pointee = types.pointees[pointee].full();
            let Some(lifetime) = &result_lifetime else {
                return Err(Diagnostic::new(
                    f.result.span,
                    "a borrowed reference result requires a declared result lifetime, as in '-> &'a Record' or '-> &'a mut Record'",
                ));
            };
            let mutable_result = matches!(result, Type::RefMut(_));
            let matching = parameter_lifetimes
                .iter()
                .zip(parameters.iter())
                .filter(|(parameter, ty)| {
                    reference_reaches_type(types, **ty, result_pointee, mutable_result)
                        && parameter
                            .as_ref()
                            .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                })
                .collect::<Vec<_>>();
            let parameter_leaf_sets = parameters
                .iter()
                .map(|ty| crate::runtime_types::borrow_leaves(types, *ty))
                .collect::<Result<Vec<_>>>()?;
            let referent_leaf_sets = parameters
                .iter()
                .map(|ty| match ty.ref_pointee() {
                    Some(pointer) => {
                        crate::runtime_types::borrow_leaves(types, types.pointees[pointer])
                    }
                    None => Ok(Vec::new()),
                })
                .collect::<Result<Vec<_>>>()?;
            // A reference element stored in a by-value container parameter is
            // backed by caller-owned storage too; its declared element
            // lifetime supplies the same outlives relation.
            let container_leaf = parameter_leaf_sets.iter().any(|leaves| {
                leaves.iter().any(|leaf| {
                    leaf.lifetime
                        .as_ref()
                        .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                })
            });
            // A shared reference field stored inside the referent of a
            // reference parameter is caller-owned storage too. Its declared
            // field lifetime was instantiated in the parameter's record type,
            // so projecting it through the reference keeps that relation.
            let referent_field_leaf = |wanted_mutable: bool| {
                parameters
                    .iter()
                    .zip(&referent_leaf_sets)
                    .any(|(ty, leaves)| {
                        ty.is_ref()
                            && leaves.iter().any(|leaf| {
                                leaf.mutable == wanted_mutable
                                    && leaf.lifetime.as_ref().is_some_and(|name| {
                                        outlives(&lifetime_bounds, name, lifetime)
                                    })
                            })
                    })
            };
            if matching.is_empty() && !container_leaf && !referent_field_leaf(mutable_result) {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "reference result lifetime '{lifetime}' does not appear on any reference parameter to the same '{}' pointee that outlives it; a returned reference must borrow caller-owned storage",
                        types.name(result_pointee)
                    ),
                ));
            }
            if mutable_result
                && !matching
                    .iter()
                    .any(|(_, ty)| matches!(ty, Type::RefMut(_) | Type::SliceMut(_)))
                && !referent_field_leaf(true)
                && !parameter_leaf_sets.iter().any(|leaves| {
                    leaves.iter().any(|leaf| {
                        leaf.mutable
                            && leaf
                                .lifetime
                                .as_ref()
                                .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                    })
                })
            {
                return Err(Diagnostic::new(
                    f.result.span,
                    format!(
                        "an exclusive '&mut {}' result lifetime '{lifetime}' must appear on an exclusive '&mut' parameter to the same pointee that outlives it; shared storage cannot be returned mutably",
                        types.name(result_pointee)
                    ),
                ));
            }
        } else if result
            .layout()
            .is_some_and(|layout| types.enums[layout].borrowed)
            || crate::runtime_types::is_reference_container(types, result)
        {
            // Every borrowed leaf of a returned record, including a structural
            // row, must name a signature label that a parameter carries. A
            // label from a `..r` specialization or an elided input is a rigid
            // occurrence identity, not a callee declaration, so it is validated
            // by the parameter relation rather than the declared-name set. The
            // field annotation is an obligation only: the ownership pass checks
            // each actual value origin against the same paths below.
            let parameter_leaf_sets = parameters
                .iter()
                .map(|ty| crate::runtime_types::borrow_leaves(types, *ty))
                .collect::<Result<Vec<_>>>()?;
            for leaf in crate::runtime_types::borrow_leaves(types, result)? {
                let Some(lifetime) = &leaf.lifetime else {
                    return Err(Diagnostic::new(
                        f.result.span,
                        "a returned record cannot carry a borrowed field without a declared lifetime; name the field's lifetime from a parameter, as in 'struct { view: &'a [T] }', or preserve it through a '..r' row variable",
                    ));
                };
                let declared_here = declared_lifetimes.contains(lifetime);
                let carried =
                    parameter_lifetimes
                        .iter()
                        .zip(parameters.iter())
                        .zip(&parameter_leaf_sets)
                        .any(|((parameter, ty), leaves)| {
                            (parameter
                                .as_ref()
                                .is_some_and(|name| outlives(&lifetime_bounds, name, lifetime))
                                && (!leaf.mutable
                                    || ty.is_mut_slice()
                                    || matches!(ty, Type::RefMut(_))))
                                || leaves.iter().any(|parameter_leaf| {
                                    parameter_leaf.lifetime.as_ref().is_some_and(|name| {
                                        outlives(&lifetime_bounds, name, lifetime)
                                    }) && (!leaf.mutable || parameter_leaf.mutable)
                                })
                        });
                if !carried {
                    let detail = if declared_here {
                        String::new()
                    } else {
                        format!(
                            " (lifetime '{lifetime}' is neither declared by this function nor supplied by a parameter's borrowed field)"
                        )
                    };
                    return Err(Diagnostic::new(
                        f.result.span,
                        if leaf.mutable {
                            format!(
                                "exclusive borrowed record result lifetime '{lifetime}' does not appear on an exclusive '&mut [T]' parameter or mutable record-field parameter that outlives it; a returned mutable field must borrow caller-owned exclusive storage{detail}"
                            )
                        } else {
                            format!(
                                "borrowed record result lifetime '{lifetime}' does not appear on any parameter that outlives it; a returned record must borrow caller-owned storage{detail}"
                            )
                        },
                    ));
                }
            }
        }
        if crate::runtime_types::contains_task(types, result) {
            return Err(Diagnostic::new(
                f.result.span,
                "a function cannot return a task handle; a child handle must not escape its scope",
            ));
        }
        let specialized =
            !key.1.is_empty() || !key.2.is_empty() || !key.3.is_empty() || !key.4.is_empty();
        let name = if !specialized {
            f.name.clone()
        } else {
            let mut type_values = key.1.iter();
            let mut grade_values = key.2.iter();
            let mut const_values = key.3.iter();
            let mut effect_values = key.4.iter();
            let arguments = f
                .generics
                .iter()
                .filter_map(|generic| {
                    if is_grade_generic(resolution, generic) {
                        grade_values.next().map(|grade| grade.to_string())
                    } else if is_const_generic(resolution, generic) {
                        const_values.next().map(|value| value.to_string())
                    } else if crate::runtime_types::is_effect_generic(resolution, generic) {
                        effect_values.next().map(|effects| {
                            let names =
                                crate::runtime_types::effect_name_list(resolution, *effects);
                            format!("{{{}}}", names.join(", "))
                        })
                    } else {
                        type_values.next().map(|ty| types.name(*ty))
                    }
                })
                .collect::<Vec<_>>();
            format!("{}::<{}>", f.name, arguments.join(", "))
        };
        let effects = if f.row_omitted() {
            if !self.inferred_rows.contains(&binding) {
                return Err(Diagnostic::new(
                    declared.span,
                    "only a private function may omit its effect row; add '! {..}' after the result type",
                ));
            }
            // FND-ROWS-INFER: the row this pass assumes, grown by any
            // instance already checked.
            self.rows.guesses.get(&binding).copied().unwrap_or(0)
                | self.rows.found.get(&binding).copied().unwrap_or(0)
        } else {
            crate::runtime_types::effect_bits_with(resolution, &f.effects, &effect_substitution)?
        };
        let foreign = if let Some(symbol) = &f.foreign {
            if effects & IO == 0 && !PURE_HOST_SYMBOLS.contains(&symbol.as_str()) {
                return Err(Diagnostic::new(
                    declared.span,
                    "a foreign call has unchecked host side effects and requires the 'io' effect in its declared row",
                ));
            }
            let shape = result
                .layout()
                .and_then(|layout| types.enums[layout].result);
            validate_foreign_function(
                types,
                symbol.starts_with("kush_sys_"),
                &parameters,
                result,
                shape,
                &parameter_grades,
                result_grade,
                declared.span,
            )?;
            Some(ForeignFunction {
                symbol: symbol.clone(),
                parameters: parameters.clone(),
                result,
                fallible: shape,
            })
        } else {
            None
        };
        let default_trait = declared
            .default_specialization
            .map(|index| self.default_specializations[index].clone());
        // Rename only labels written in the callee declaration. Substituted
        // type arguments (including residual rows) already belong to the caller
        // and must never be captured by a same-spelled callee binder.
        let call_contract = if f.lifetimes.is_empty() {
            None
        } else {
            let mut scoped = substitution.clone();
            let mut binders = BTreeSet::new();
            let mut names = BTreeMap::new();
            for lifetime in &f.lifetimes {
                let identity = types.fresh_lifetime(&format!("callee '{}", lifetime.name));
                scoped
                    .lifetimes
                    .insert(lifetime.name.clone(), identity.clone());
                binders.insert(identity.clone());
                names.insert(identity, lifetime.name.clone());
            }
            let rename = |name: &String| {
                scoped
                    .lifetimes
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| name.clone())
            };
            Some(CallLifetimeContract {
                parameters: f
                    .parameters
                    .iter()
                    .filter(|p| !p.erased)
                    .map(|p| types.ty_in(split_grade(&p.ty).0, &scoped))
                    .collect::<Result<Vec<_>>>()?,
                result: types.ty_in(&result_ty, &scoped)?,
                binders,
                names,
                bounds: lifetime_bounds
                    .iter()
                    .map(|(a, b)| (rename(a), rename(b)))
                    .collect(),
            })
        };
        let index = self.signatures.len();
        self.signatures.push(Signature {
            call_contract,
            binding,
            origin: origin
                .filter(|_| specialized)
                .map(|span| (span, format!("'{name}'"))),
            name: name.clone(),
            parameters: parameters.clone(),
            result,
            effects,
            span: declared.span,
            substitution: substitution.types,
            consts: const_substitution,
            grades: grade_substitution,
            effect_arguments: effect_substitution,
            parameter_grades: parameter_grades.clone(),
            result_grade,
            parameter_lifetimes: parameter_lifetimes.clone(),
            result_lifetime: result_lifetime.clone(),
            lifetime_bounds: lifetime_bounds.clone(),
            self_type: substitution.self_type,
            default_trait,
            associated_consts,
        });
        self.instances.insert(key, index);
        if let Some(foreign) = foreign {
            self.foreign_functions.insert(index, foreign);
            // A foreign declaration has no source body. Store an inert,
            // already-checked body so the pending-body loop and the ownership
            // pass see the ordinary parameter/result shape, while the native
            // backend declares an import instead of defining this instance.
            let locals = parameters
                .iter()
                .map(|ty| Local {
                    ty: *ty,
                    mutable: false,
                    linear: false,
                    pinned: false,
                    grade: None,
                    span: declared.span,
                })
                .collect();
            self.bodies.push(Some(Function {
                name: name.clone(),
                parameters: parameters.len(),
                closure: None,
                capture_refs: vec![],
                capture_writes: vec![],
                locals,
                result,
                body: Block {
                    statements: Vec::new(),
                    tail: Some(Box::new(Expr {
                        kind: ExprKind::Constant(0),
                        ty: result,
                        span: declared.span,
                        resource: None,
                    })),
                    ty: result,
                },
                span: declared.span,
                resources: Vec::new(),
                local_resources: Vec::new(),
                parameter_grades: parameter_grades.clone(),
                result_grade,
                parameter_lifetimes: parameter_lifetimes.clone(),
                result_lifetime: result_lifetime.clone(),
                lifetime_bounds: lifetime_bounds.clone(),
                declared_lifetimes: declared
                    .ast
                    .lifetimes
                    .iter()
                    .map(|lifetime| lifetime.name.clone())
                    .collect(),
                index_relations: BTreeSet::new(),
                parameter_slots: None,
                local_borrowed: vec![],
                local_copyable: vec![],
                capability_parameters: vec![],
                shared_environment: false,
            }));
        } else {
            self.bodies.push(None);
            self.pending.push(index);
        }
        Ok(index)
    }
    /// Register a synthetic, already-checked function body (lambda or adapter).
    /// Synthetic entries share the same index space as declared instances, so
    /// an `FnValue` code pointer stays stable.
    /// Not counted against [`MAX_INSTANCES`]: each one belongs to an instance
    /// that is.
    pub(super) fn add_synthetic(
        &mut self,
        signature: Signature,
        function: Function,
    ) -> Result<usize> {
        let index = self.signatures.len();
        self.signatures.push(signature);
        self.bodies.push(Some(function));
        Ok(index)
    }
    /// FND-ROWS-INFER: record the row a checked instance of an inferred
    /// function requires. Signatures made later see it at once; a body
    /// already checked that names the function saw a smaller row, so the pass
    /// is stale and runs again.
    pub(super) fn settle_inferred_row(&mut self, binding: BindingId, required: u16) {
        let found = self.rows.found.entry(binding).or_insert(0);
        *found |= required;
        let row = *found | self.rows.guesses.get(&binding).copied().unwrap_or(0);
        let mut grew = false;
        for signature in &mut self.signatures {
            if signature.binding == binding && signature.effects != row {
                signature.effects = row;
                grew = true;
            }
        }
        if grew
            && self.checked_bodies.iter().any(|body| {
                self.body_refs
                    .get(body)
                    .is_some_and(|refs| refs.contains(&binding))
            })
        {
            self.rows.stale = true;
        }
    }
}
