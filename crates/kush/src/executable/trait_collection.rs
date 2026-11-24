//! Collecting traits, impls and methods; trait objects.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

/// Allocate one synthetic function binding for every trait default that an impl
/// inherits, keyed by the impl declaration's start offset and the method name.
/// This is a syntactic pre-pass: it does not type-check, and it must run before
/// type lowering borrows the resolver table. Impls that are later rejected may
/// leave unused bindings behind; they never enter the checked program.
pub(super) fn collect_default_bindings(
    module: &ast::Module,
    resolution: &mut Resolution,
) -> Result<BTreeMap<(usize, String), BindingId>> {
    let mut traits = BTreeMap::new();
    for declaration in &module.items {
        if let ast::ItemKind::Trait { methods, .. } = &declaration.item.kind {
            let id = resolution.declarations[&declaration.item.span.start];
            traits.insert(
                id,
                methods
                    .iter()
                    .map(|method| {
                        (
                            method.function.name.clone(),
                            method.function.body.is_some(),
                            method.span,
                        )
                    })
                    .collect::<Vec<_>>(),
            );
        }
    }
    let mut bindings = BTreeMap::new();
    for declaration in &module.items {
        let ast::ItemKind::Impl {
            trait_path: Some(trait_path),
            methods,
            ..
        } = &declaration.item.kind
        else {
            continue;
        };
        let Some(trait_id) = resolution.reference(trait_path.span) else {
            continue;
        };
        let Some(declared) = traits.get(&trait_id) else {
            continue;
        };
        // The body is checked in the module that declares the trait: that is
        // where its free names were resolved, so a private helper of the trait's
        // module stays callable even when the impl lives in another module.
        let unit = resolution.unit_of.get(&trait_id).copied().unwrap_or(0);
        let public = resolution.public.contains(&trait_id);
        let implemented = methods
            .iter()
            .map(|method| method.function.name.as_str())
            .collect::<BTreeSet<_>>();
        for (name, has_body, span) in declared {
            if !*has_body || implemented.contains(name.as_str()) {
                continue;
            }
            let binding = resolution.synthesize_method(name, *span, unit, public);
            bindings.insert((declaration.item.span.start, name.clone()), binding);
        }
    }
    Ok(bindings)
}
/// Collect declared traits and concrete impls, validate their contracts, and
/// register every impl method as an ordinary checked function. Static dispatch
/// lowers a method call to `Target::Function`, so there are no vtables, trait
/// values, or runtime dispatch tables.
pub(super) fn collect_methods<'a>(
    module: &'a ast::Module,
    resolution: &Resolution,
    default_bindings: &BTreeMap<(usize, String), BindingId>,
    types: &mut Types<'a>,
    logical: &crate::check::LogicalEnvironment,
    functions: &mut Functions<'a>,
) -> Result<Vec<BindingId>> {
    let mut bindings = Vec::new();
    let mut trait_methods_to_check = Vec::new();
    for declaration in &module.items {
        let ast::ItemKind::Trait {
            name,
            generics,
            associated,
            methods,
        } = &declaration.item.kind
        else {
            continue;
        };
        let id = resolution.declarations[&declaration.item.span.start];
        validate_associated_type_defaults(associated)?;
        let mut associated_items = BTreeMap::new();
        for item in associated {
            match item {
                ast::Associated::Type { name, value, .. } => {
                    if let Some(default) = value {
                        let associated_names = associated
                            .iter()
                            .filter_map(|item| {
                                matches!(item, ast::Associated::Type { .. })
                                    .then_some(item.name().to_owned())
                            })
                            .collect();
                        if type_mentions_self_outside_assoc(default, &associated_names) {
                            return Err(Diagnostic::new(
                                default.span,
                                "an associated type default may not mention bare 'Self'; write a concrete type, a trait parameter, or a projection 'Self::Other'",
                            ));
                        }
                        // Validate the default's own syntax now. Trait
                        // parameters are still symbolic here, so only
                        // structurally invalid defaults are rejected at the
                        // declaration; per-impl lowering validates concrete
                        // substitutions.
                        let consts = generics
                            .iter()
                            .filter(|generic| {
                                crate::runtime_types::is_const_generic(resolution, generic)
                            })
                            .filter_map(|generic| resolution.binder(generic.span))
                            .collect::<BTreeSet<_>>();
                        validate_type_template(resolution, default, &consts, false, true)?;
                    }
                    associated_items.insert(
                        name.clone(),
                        TraitAssociated::Type {
                            default: value.clone(),
                        },
                    );
                }
                ast::Associated::Const {
                    name, ty, value, ..
                } => {
                    if type_mentions_self(ty) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "an associated constant's type may not mention 'Self'; write a concrete scalar type",
                        ));
                    }
                    let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                    if !const_scalar_type(types, lowered) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "associated constants must have a compile-time scalar, tuple, or inline-array type; scalar types are i8/i16/i32/i64/u8/u16/u32/u64, Bool, or Char",
                        ));
                    }
                    associated_items.insert(
                        name.clone(),
                        TraitAssociated::Const {
                            ty: ty.clone(),
                            default: value.clone(),
                        },
                    );
                }
            }
        }
        for generic in generics {
            if let Some(bound) = &generic.bound {
                match resolution
                    .reference(bound.span)
                    .map(|id| &resolution.bindings[id])
                {
                    Some(binding)
                        if binding.kind == BindingKind::Builtin
                            && matches!(
                                binding.name.as_str(),
                                "Type" | "Nat" | "Grade" | "Effects"
                            ) => {}
                    Some(binding) if binding.kind == BindingKind::Trait => {
                        return Err(Diagnostic::new(
                            generic.span,
                            "trait parameters with trait bounds are not supported in this subset; put the bound on the function type parameter that uses this trait, as in 'fn f<T: Trait<...>>(value: T)'",
                        ));
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            generic.span,
                            "trait parameter bounds must name Type, Nat, Grade, or Effects",
                        ));
                    }
                }
            }
            if generic_category(resolution, generic) == GenericCategory::Effect {
                return Err(Diagnostic::new(
                    generic.span,
                    "effect-row parameters are not supported on traits; declare the effect parameter on the generic function or method that needs it",
                ));
            }
        }
        let mut signatures = BTreeMap::new();
        for method in methods {
            let f = &method.function;
            if f.total {
                return Err(Diagnostic::new(
                    method.span,
                    "trait methods are executable declarations and cannot be 'total'",
                ));
            }
            if let Some(method_generic) = f
                .generics
                .iter()
                .find(|method_generic| generics.iter().any(|g| g.name == method_generic.name))
            {
                return Err(Diagnostic::new(
                    method_generic.span,
                    format!(
                        "method parameter '{}' must be distinct from the trait's parameters to avoid capture; rename one of them",
                        method_generic.name
                    ),
                ));
            }
            if Checker::builtin_method(&f.name) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "trait method '{}' uses a reserved builtin method name; builtin receiver methods take precedence, so choose another name",
                        f.name
                    ),
                ));
            }
            let Some(receiver) = f.parameters.first() else {
                return Err(Diagnostic::new(
                    method.span,
                    "a trait method must declare an owned receiver as its first parameter: 'self: Self'",
                ));
            };
            if receiver.erased || receiver.name != "self" {
                return Err(Diagnostic::new(
                    receiver.span,
                    "the first method parameter must be the receiver, written 'self: Self'",
                ));
            }
            if !valid_trait_receiver(&receiver.ty) {
                return Err(Diagnostic::new(
                    receiver.ty.span,
                    "a trait method receiver must be written 'self: Self', 'self: &Self', 'self: &mut Self', '&self', or '&mut self'",
                ));
            }
            for parameter in &f.parameters {
                if let Some(length) = &parameter.min_length {
                    return Err(Diagnostic::new(
                        length.span,
                        "'where len >= N' parameters are supported on functions, not on methods yet",
                    ));
                }
                if parameter.erased && type_mentions_self(&parameter.ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "erased method parameters may not mention 'Self' in this subset",
                    ));
                }
            }
            validate_erased_parameters(resolution, logical, f)?;
            validate_length_templates(resolution, f)?;
            validate_runtime_length_signature(resolution, f, true)?;
            if signatures
                .insert(
                    f.name.clone(),
                    TraitMethod {
                        span: method.span,
                        function: f,
                    },
                )
                .is_some()
            {
                return Err(Diagnostic::new(
                    method.span,
                    format!("duplicate method '{}' in trait '{name}'", f.name),
                ));
            }
            trait_methods_to_check.push(f);
        }
        functions.traits.insert(
            id,
            TraitDefinition {
                generics: generics.clone(),
                associated: associated_items,
                associated_order: associated
                    .iter()
                    .map(|item| item.name().to_owned())
                    .collect(),
                methods: signatures,
            },
        );
    }
    for declaration in &module.items {
        let ast::ItemKind::Impl {
            generics: impl_generics,
            trait_path,
            self_ty,
            associated,
            methods,
        } = &declaration.item.kind
        else {
            continue;
        };
        let span = declaration.item.span;
        let trait_id = match trait_path {
            Some(trait_path) => {
                let id = resolution.reference(trait_path.span).ok_or_else(|| {
                    Diagnostic::new(trait_path.span, "trait path did not resolve")
                })?;
                if resolution.bindings[id].kind != BindingKind::Trait {
                    return Err(Diagnostic::new(
                        trait_path.span,
                        format!(
                            "'{}' is not a declared trait; an impl must name 'impl Trait for Type' or provide an inherent 'impl Type'",
                            resolution.bindings[id].name
                        ),
                    ));
                }
                Some(id)
            }
            None => None,
        };
        if !impl_generics.is_empty() {
            bindings.extend(collect_generic_impl(
                span,
                impl_generics,
                trait_path.as_ref(),
                trait_id,
                self_ty,
                associated,
                methods,
                default_bindings,
                resolution,
                types,
                logical,
                functions,
            )?);
            continue;
        }
        if type_has_open_row(self_ty) {
            return Err(Diagnostic::new(
                self_ty.span,
                "an impl self type cannot use an open row ('..'); impl headers match one exact canonical structural row",
            ));
        }
        let self_key = types.ty_in(self_ty, &crate::runtime_types::Subst::default())?;
        if matches!(
            self_key,
            Type::Ref(_)
                | Type::RefMut(_)
                | Type::Slice(_)
                | Type::SliceMut(_)
                | Type::Str
                | Type::StrMut
                | Type::Task(_)
                | Type::Thread(_)
                | Type::Stdin
                | Type::Stdout
                | Type::Never
        ) || crate::runtime_types::has_borrow(types, self_key)
        {
            return Err(Diagnostic::new(
                self_ty.span,
                "impls require an owned, non-borrowed concrete type; borrowed records, views, references, and task handles cannot be impl targets in this subset",
            ));
        }
        if trait_id.is_none() && self_key.layout().is_none() {
            return Err(Diagnostic::new(
                self_ty.span,
                "inherent impls require a nominal record or enum type",
            ));
        }
        let record_fields = self_key
            .layout()
            .filter(|id| types.enums[*id].record)
            .map(|id| {
                types.enums[id].variants[0]
                    .names
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>()
            })
            .unwrap_or_default();
        let trait_definition = trait_id.and_then(|id| functions.traits.get(&id).cloned());
        let trait_methods = trait_definition
            .as_ref()
            .map(|definition| definition.methods.clone())
            .unwrap_or_default();
        let trait_generics = trait_definition
            .as_ref()
            .map(|definition| definition.generics.clone())
            .unwrap_or_default();
        let trait_argument_ast = match trait_path {
            Some(ast::Type {
                kind: ast::TypeKind::Named { arguments, .. },
                ..
            }) => arguments.as_slice(),
            _ => &[],
        };
        let trait_arguments = if let Some(trait_id) = trait_id {
            for argument in trait_argument_ast {
                if type_mentions_self(argument) {
                    return Err(Diagnostic::new(
                        argument.span,
                        "'Self' cannot appear in a trait's specialization arguments; write the concrete impl target type",
                    ));
                }
            }
            evaluate_trait_arguments(
                types,
                resolution,
                logical,
                &trait_generics,
                trait_argument_ast,
                &crate::runtime_types::Subst::default(),
                &resolution.bindings[trait_id].name,
                span,
            )?
        } else {
            TraitArguments::default()
        };
        let trait_argument_names = trait_generics
            .iter()
            .zip(trait_argument_ast)
            .map(|(generic, argument)| (generic.name.clone(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut impl_associated = ImplAssociated::default();
        let trait_associated = trait_definition
            .as_ref()
            .map(|definition| definition.associated.clone())
            .unwrap_or_default();
        let mut provided = BTreeSet::new();
        for item in associated {
            match item {
                ast::Associated::Type { name, value, span } => {
                    let Some(value) = value else {
                        return Err(Diagnostic::new(
                            *span,
                            "an associated type in an impl requires a value: 'type Name = Type;'",
                        ));
                    };
                    if type_mentions_self(value) {
                        return Err(Diagnostic::new(
                            value.span,
                            "an associated type value may not mention 'Self'; write a concrete type",
                        ));
                    }
                    if trait_id.is_some()
                        && !matches!(
                            trait_associated.get(name),
                            Some(TraitAssociated::Type { .. })
                        )
                    {
                        return Err(Diagnostic::new(
                            *span,
                            format!(
                                "associated type '{name}' is not declared by the implemented trait"
                            ),
                        ));
                    }
                    if trait_id.is_none() {
                        return Err(Diagnostic::new(
                            *span,
                            "inherent impls define associated constants only; associated types require a trait declaration",
                        ));
                    }
                    if !provided.insert(name.clone()) {
                        return Err(Diagnostic::new(
                            *span,
                            format!("duplicate item '{name}' in one impl"),
                        ));
                    }
                    // Lower the value once so a malformed or cyclic projection
                    // is diagnosed at the impl rather than at an arbitrary use.
                    types.ty_in(value, &crate::runtime_types::Subst::default())?;
                    impl_associated.types.insert(name.clone(), value.clone());
                }
                ast::Associated::Const {
                    name,
                    ty,
                    value,
                    span,
                } => {
                    if type_mentions_self(ty) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "an associated constant's type may not mention 'Self'; write a concrete scalar type",
                        ));
                    }
                    let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                    if !const_scalar_type(types, lowered) {
                        return Err(Diagnostic::new(
                            ty.span,
                            "associated constants must have a compile-time scalar, tuple, or inline-array type; scalar types are i8/i16/i32/i64/u8/u16/u32/u64, Bool, or Char",
                        ));
                    }
                    if trait_id.is_some()
                        && !matches!(
                            trait_associated.get(name),
                            Some(TraitAssociated::Const { .. })
                        )
                    {
                        return Err(Diagnostic::new(
                            *span,
                            format!(
                                "associated constant '{name}' is not declared by the implemented trait"
                            ),
                        ));
                    }
                    if !provided.insert(name.clone()) {
                        return Err(Diagnostic::new(
                            *span,
                            format!("duplicate item '{name}' in one impl"),
                        ));
                    }
                    let declared_ty = match trait_associated.get(name) {
                        Some(TraitAssociated::Const { ty: declared, .. }) => {
                            Some(types.ty_in(declared, &crate::runtime_types::Subst::default())?)
                        }
                        _ => None,
                    };
                    if let Some(declared_ty) = declared_ty
                        && declared_ty != lowered
                    {
                        return Err(Diagnostic::new(
                            ty.span,
                            format!(
                                "associated constant '{name}' must have the declared type {}",
                                types.name(declared_ty)
                            ),
                        ));
                    }
                    let Some(value) = value else {
                        // A default in the trait is inherited below.
                        continue;
                    };
                    let checked =
                        evaluate_associated_const(types, value, lowered, &impl_associated.consts)?;
                    impl_associated.consts.insert(name.clone(), checked);
                }
            }
        }
        if let Some(trait_id) = trait_id {
            let associated_order = trait_definition
                .as_ref()
                .map(|definition| definition.associated_order.clone())
                .unwrap_or_default();
            for name in &associated_order {
                let Some(item) = trait_associated.get(name) else {
                    continue;
                };
                match item {
                    TraitAssociated::Type { default } => {
                        if !impl_associated.types.contains_key(name) {
                            let Some(default) = default else {
                                return Err(Diagnostic::new(
                                    span,
                                    format!(
                                        "missing associated type '{name}' for trait '{}' on {}",
                                        resolution.bindings[trait_id].name,
                                        types.name(self_key)
                                    ),
                                ));
                            };
                            impl_associated.types.insert(name.clone(), default.clone());
                        }
                    }
                    TraitAssociated::Const { ty, default } => {
                        if impl_associated.consts.contains_key(name) {
                            continue;
                        }
                        let Some(default) = default else {
                            return Err(Diagnostic::new(
                                span,
                                format!(
                                    "missing associated constant '{name}' for trait '{}' on {}",
                                    resolution.bindings[trait_id].name,
                                    types.name(self_key)
                                ),
                            ));
                        };
                        let lowered = types.ty_in(ty, &crate::runtime_types::Subst::default())?;
                        let checked = evaluate_associated_const(
                            types,
                            default,
                            lowered,
                            &impl_associated.consts,
                        )?;
                        impl_associated.consts.insert(name.clone(), checked);
                    }
                }
            }
        }
        let associated_index =
            (!impl_associated.types.is_empty() || !impl_associated.consts.is_empty()).then(|| {
                functions.impl_associated.push(impl_associated.clone());
                functions.impl_associated.len() - 1
            });
        if trait_id.is_none() && !impl_associated.consts.is_empty() {
            functions
                .inherent_consts
                .insert(self_key, impl_associated.consts.clone());
        }
        let mut definitions = BTreeMap::new();
        for method in methods {
            let f = &method.function;
            if f.total {
                return Err(Diagnostic::new(
                    method.span,
                    "impl methods are executable declarations and cannot be 'total'",
                ));
            }
            // A function of an inherent impl without a `self` receiver is an
            // associated function, called as `Type.name(..)`.
            let associated_fn = trait_id.is_none()
                && f.parameters
                    .first()
                    .is_none_or(|first| first.erased || first.name != "self");
            if !associated_fn {
                let Some(receiver) = f.parameters.first() else {
                    return Err(Diagnostic::new(
                        method.span,
                        "a method must declare a receiver as its first parameter: 'self: Self'/'self: &Self'/'self: &mut Self' or the concrete target type",
                    ));
                };
                if receiver.erased || receiver.name != "self" {
                    return Err(Diagnostic::new(
                        receiver.span,
                        "the first method parameter must be the receiver, written 'self: Self', 'self: &Self', 'self: &mut Self', or the concrete target type",
                    ));
                }
                checked_method_receiver(types, &receiver.ty, self_key)?;
            }
            // Builtin and field names only shadow dot-calls, which never
            // reach an associated function.
            if !associated_fn && Checker::builtin_method(&f.name) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' uses a reserved builtin method name; builtin receiver methods take precedence, so choose another name",
                        f.name
                    ),
                ));
            }
            if !associated_fn && record_fields.contains(&f.name) {
                return Err(Diagnostic::new(
                    method.span,
                    format!(
                        "method '{}' collides with a record field of the same name; field projection takes precedence in dot-call syntax, so rename the method",
                        f.name
                    ),
                ));
            }
            if trait_id.is_some() {
                let Some(expected) = trait_methods.get(&f.name) else {
                    return Err(Diagnostic::new(
                        method.span,
                        format!(
                            "method '{}' is not declared by the implemented trait",
                            f.name
                        ),
                    ));
                };
                if method_contract_key(
                    resolution,
                    expected.function,
                    Some(self_ty),
                    Some(&trait_argument_names),
                    Some(&impl_associated.types),
                )? != method_contract_key(
                    resolution,
                    f,
                    Some(self_ty),
                    None,
                    Some(&impl_associated.types),
                )? {
                    return Err(Diagnostic::new(
                        method.span,
                        format!(
                            "method '{}' does not match the trait signature exactly; parameters, parameter grades, erasure markers, result type, generic parameters and bounds, effect exclusions, lifetimes, effects, and substituted trait arguments must match",
                            f.name
                        ),
                    ));
                }
            }
            for parameter in &f.parameters {
                if let Some(length) = &parameter.min_length {
                    return Err(Diagnostic::new(
                        length.span,
                        "'where len >= N' parameters are supported on functions, not on methods yet",
                    ));
                }
                if parameter.erased && type_mentions_self(&parameter.ty) {
                    return Err(Diagnostic::new(
                        parameter.ty.span,
                        "erased method parameters may not mention 'Self' in this subset",
                    ));
                }
            }
            validate_erased_parameters(resolution, logical, f)?;
            validate_length_templates(resolution, f)?;
            validate_runtime_length_signature(resolution, f, true)?;
            let binding = resolution.method(method.span).ok_or_else(|| {
                Diagnostic::new(method.span, "internal error: impl method has no binding")
            })?;
            let definition = MethodDefinition {
                binding,
                public: method.public,
                unit: resolution.unit_of.get(&binding).copied().unwrap_or(0),
                impl_arguments: None,
            };
            if associated_fn {
                let owner = self_key
                    .layout()
                    .map(|layout| types.enums[layout].definition)
                    .ok_or_else(|| {
                        Diagnostic::new(
                            method.span,
                            "associated functions need a nominal record or enum type",
                        )
                    })?;
                let table = functions.associated_fns.entry(owner).or_default();
                if definitions.contains_key(&f.name)
                    || table.insert(f.name.clone(), definition).is_some()
                {
                    return Err(Diagnostic::new(
                        method.span,
                        format!("duplicate method or associated function '{}'", f.name),
                    ));
                }
            } else if definitions.insert(f.name.clone(), definition).is_some()
                || self_key
                    .layout()
                    .and_then(|layout| {
                        functions
                            .associated_fns
                            .get(&types.enums[layout].definition)
                    })
                    .is_some_and(|table| table.contains_key(&f.name))
            {
                return Err(Diagnostic::new(
                    method.span,
                    format!("duplicate method or associated function '{}'", f.name),
                ));
            }
            functions.declared.insert(
                binding,
                Declared {
                    ast: f,
                    span: method.span,
                    self_ty: Some(self_key),
                    default_specialization: None,
                    impl_associated: associated_index,
                    impl_template: None,
                },
            );
            bindings.push(binding);
        }
        if let Some(trait_id) = trait_id {
            let trait_public = resolution.public.contains(&trait_id);
            let impl_unit = resolution.item_units.get(&span.start).copied().unwrap_or(0);
            for (name, method) in &trait_methods {
                if definitions.contains_key(name) {
                    continue;
                }
                if method.function.body.is_none() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "missing implementation of trait method '{name}' for {}",
                            types.name(self_key)
                        ),
                    ));
                }
                // An inherited default is materialized as a fresh checked
                // function specialized to this impl's `Self` and trait
                // arguments. It is never shared with another impl: `Self` and
                // trait parameters are substituted per impl.
                let receiver = method
                    .function
                    .parameters
                    .first()
                    .expect("trait receiver was validated at declaration");
                checked_method_receiver(types, &receiver.ty, self_key)?;
                if record_fields.contains(name) {
                    return Err(Diagnostic::new(
                        method.span,
                        format!(
                            "inherited default method '{name}' collides with a record field of the same name; field projection takes precedence in dot-call syntax, so rename the method"
                        ),
                    ));
                }
                let binding = *default_bindings
                    .get(&(span.start, name.clone()))
                    .ok_or_else(|| {
                        Diagnostic::new(
                            method.span,
                            "internal error: inherited default method has no binding",
                        )
                    })?;
                let index = functions.default_specializations.len();
                functions
                    .default_specializations
                    .push((trait_id, trait_arguments.clone()));
                functions.declared.insert(
                    binding,
                    Declared {
                        ast: method.function,
                        span: method.span,
                        self_ty: Some(self_key),
                        default_specialization: Some(index),
                        impl_associated: associated_index,
                        impl_template: None,
                    },
                );
                definitions.insert(
                    name.clone(),
                    MethodDefinition {
                        binding,
                        public: trait_public,
                        unit: impl_unit,
                        impl_arguments: None,
                    },
                );
                bindings.push(binding);
            }
            let specialization = if trait_generics.is_empty() {
                resolution.bindings[trait_id].name.clone()
            } else {
                format!(
                    "{}<{}>",
                    resolution.bindings[trait_id].name,
                    trait_specialization_name(resolution, types, &trait_generics, &trait_arguments)
                )
            };
            if functions
                .trait_impls
                .insert(
                    (trait_id, trait_arguments.clone(), self_key),
                    definitions.clone(),
                )
                .is_some()
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "duplicate implementation of trait '{specialization}' for {}",
                        types.name(self_key)
                    ),
                ));
            }
            for (name, definition) in &definitions {
                functions
                    .methods_by_type
                    .entry(self_key)
                    .or_default()
                    .entry(name.clone())
                    .or_default()
                    .push((trait_id, trait_arguments.clone(), *definition));
            }
            if !impl_associated.consts.is_empty() {
                functions.trait_consts.insert(
                    (trait_id, trait_arguments.clone(), self_key),
                    impl_associated.consts.clone(),
                );
            }
            functions.trait_associated.insert(
                (trait_id, trait_arguments.clone(), self_key),
                impl_associated.clone(),
            );
        } else {
            let inherent = functions.inherent.entry(self_key).or_default();
            for (name, definition) in definitions {
                if inherent.insert(name.clone(), definition).is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "duplicate inherent method '{name}' for {}",
                            types.name(self_key)
                        ),
                    ));
                }
            }
        }
        // Record every concrete impl as a ground header too. Coherence compares
        // it with generic headers: a concrete receiver is an instance of a
        // matching blanket/generic header, which is the specialization axis.
        functions.impl_headers.push(ImplHeader {
            trait_id,
            generics: Vec::new(),
            self_ty: self_ty.clone(),
            trait_arguments: trait_argument_ast.to_vec(),
            associated: impl_associated.clone(),
            methods: match trait_id {
                Some(trait_id) => functions
                    .trait_impls
                    .get(&(trait_id, trait_arguments.clone(), self_key))
                    .cloned()
                    .unwrap_or_default(),
                None => functions
                    .inherent
                    .get(&self_key)
                    .cloned()
                    .unwrap_or_default(),
            },
            span,
            concrete: Some((trait_arguments.clone(), self_key)),
        });
    }
    // Declaration-time coherence. Two impl headers that can apply to the same
    // receiver and trait specialization must be specialization-comparable: one
    // must be an instance of the other. Incomparable overlaps are rejected
    // rather than resolved by declaration order.
    for (left_index, left) in functions.impl_headers.iter().enumerate() {
        for right in functions.impl_headers.iter().skip(left_index + 1) {
            if left.trait_id != right.trait_id {
                continue;
            }
            if left.concrete.is_some() && right.concrete.is_some() {
                // Exact duplicate concrete impls are diagnosed by the exact
                // trait-impl table; distinct concrete headers are disjoint.
                continue;
            }
            if !headers_overlap(resolution, left, right) {
                continue;
            }
            // Several inherent impls for the same type may coexist when their
            // method names are disjoint. Trait impls always repeat the trait's
            // method set, so any equivalent trait header is a duplicate.
            if left.trait_id.is_none()
                && !left
                    .methods
                    .keys()
                    .any(|name| right.methods.contains_key(name))
            {
                continue;
            }
            let left_covers = header_subsumes(resolution, left, right);
            let right_covers = header_subsumes(resolution, right, left);
            let left_label = impl_header_label(resolution, types, left);
            let right_label = impl_header_label(resolution, types, right);
            if left_covers && right_covers {
                return Err(Diagnostic::new(
                    right.span,
                    format!(
                        "duplicate implementation: {left_label} and {right_label} cover the same receiver and trait specialization; keep one impl",
                    ),
                ));
            }
            if !left_covers && !right_covers {
                return Err(Diagnostic::new(
                    right.span,
                    format!(
                        "overlapping implementations {left_label} and {right_label} are incomparable: neither pattern is more specific, so dispatch has no deterministic winner; make the impls disjoint or specialize one pattern",
                    ),
                ));
            }
        }
    }
    // Trait-bound arity is a declaration property. It is checked once every
    // trait definition is registered, including bounds on ordinary functions
    // and on generic methods that are never instantiated.
    for function in functions
        .declared
        .values()
        .map(|declared| declared.ast)
        .chain(trait_methods_to_check)
    {
        for generic in &function.generics {
            let Some(bound) = &generic.bound else {
                continue;
            };
            let Some(trait_id) = resolution.reference(bound.span) else {
                continue;
            };
            if resolution.bindings[trait_id].kind != BindingKind::Trait {
                continue;
            }
            let arguments = match &bound.kind {
                ast::TypeKind::Named { arguments, .. } => arguments.len(),
                _ => 0,
            };
            let expected = functions.traits[&trait_id].generics.len();
            if arguments != expected {
                return Err(Diagnostic::new(
                    generic.span,
                    format!(
                        "trait '{}' expects {expected} argument(s), found {arguments}",
                        resolution.bindings[trait_id].name
                    ),
                ));
            }
        }
    }
    Ok(bindings)
}

/// Build the closed-world representation of every usable trait object after
/// all impls are known. A trait is object-safe here only when:
///
/// - it has no generic or blanket impls, so the member set is finite;
/// - every trait parameter is an ordinary type (no Nat/Grade/Effect arguments);
/// - every method takes an owned `self: Self` receiver, has no method generics
///   or lifetimes, and mentions neither `Self` nor erased proof parameters in
///   its remaining parameters or result;
/// - every concrete impl of one specialization agrees on each associated type
///   and constant value used by the object.
///
/// The object is the normalized union of the concrete impl targets. Borrowed
/// receivers are rejected rather than silently copying or moving a derived
/// payload; supporting them needs a checked borrowed-trait-object capability.
pub(super) fn prepare_trait_objects<'a>(
    types: &mut Types<'a>,
    resolution: &Resolution,
    functions: &mut Functions<'a>,
) -> Result<()> {
    let traits = functions
        .traits
        .iter()
        .map(|(id, definition)| (*id, definition.clone()))
        .collect::<Vec<_>>();
    for (trait_id, definition) in traits {
        let trait_name = resolution.bindings[trait_id].name.clone();
        let dynamic = types.dynamic_traits.contains(&trait_id);
        let mut reason: Option<String> = None;
        // Trait parameters may be type, natural, grade, or effect arguments.
        // The dynamic representation stores the checked specialization, so a
        // non-type argument is identity like a type argument; it never changes
        // the two-word object layout.
        let associated_type_names = definition
            .associated
            .iter()
            .filter_map(|(name, item)| {
                matches!(item, TraitAssociated::Type { .. }).then_some(name.clone())
            })
            .collect::<BTreeSet<_>>();
        if reason.is_none() {
            for (name, method) in &definition.methods {
                let f = method.function;
                let Some(receiver) = f.parameters.first() else {
                    continue;
                };
                match &receiver.ty.kind {
                    ast::TypeKind::SelfType => {}
                    ast::TypeKind::Borrow {
                        mutable: false,
                        inner,
                        ..
                    } if matches!(inner.kind, ast::TypeKind::SelfType) => {}
                    ast::TypeKind::Borrow {
                        mutable: true,
                        inner,
                        ..
                    } if matches!(inner.kind, ast::TypeKind::SelfType) => {}
                    _ => {
                        reason = Some(format!(
                            "method '{name}' receiver must be 'self: Self', 'self: &Self', '&self', 'self: &mut Self', or '&mut self'"
                        ));
                        break;
                    }
                }
                if !f.generics.is_empty() && !dynamic {
                    reason = Some(format!(
                        "method '{name}' is generic; a generic method cannot be dispatched through a closed-world union object"
                    ));
                    break;
                }
                // A borrowed result is checked against the selected member's
                // lifetime contract at each call site. An owned receiver has no
                // receiver lifetime, so a result can only borrow caller-owned
                // storage (another argument) and remains valid after dispatch.
                if let Some(parameter) = f.parameters[1..].iter().find(|parameter| {
                    parameter.erased
                        || type_mentions_self_outside_assoc(&parameter.ty, &associated_type_names)
                }) {
                    reason = Some(if parameter.erased {
                        format!(
                            "method '{name}' has an erased proof parameter; proof terms cannot be erased through dynamic dispatch"
                        )
                    } else {
                        format!(
                            "method '{name}' mentions 'Self' in a non-receiver parameter, so its ABI would differ per impl"
                        )
                    });
                    break;
                }
                if type_mentions_self_outside_assoc(&f.result, &associated_type_names) {
                    reason = Some(format!(
                        "method '{name}' mentions 'Self' in its result, so dynamic dispatch would erase the concrete result type"
                    ));
                    break;
                }
                // A dynamic call has no static callee whose length binders the
                // call site could replace with the caller's.
                if f.parameters
                    .iter()
                    .map(|parameter| &parameter.ty)
                    .chain(std::iter::once(&f.result))
                    .any(type_mentions_runtime_length)
                {
                    reason = Some(format!(
                        "method '{name}' mentions a runtime-length array [T; n <= C]; call it through a concrete receiver"
                    ));
                    break;
                }
            }
        }
        if reason.is_none()
            && !dynamic
            && functions
                .impl_headers
                .iter()
                .any(|header| header.trait_id == Some(trait_id) && header.concrete.is_none())
        {
            reason = Some(format!(
                "trait '{trait_name}' has a generic or blanket impl, so its set of concrete members is open"
            ));
        }
        let mut groups: BTreeMap<TraitArguments, Vec<Type>> = BTreeMap::new();
        let mut object_associated: BTreeMap<TraitArguments, BTreeMap<String, Type>> =
            BTreeMap::new();
        if reason.is_none() {
            let mut concrete: Vec<(TraitArguments, Type, ImplAssociated)> = Vec::new();
            for header in &functions.impl_headers {
                if header.trait_id == Some(trait_id)
                    && let Some((arguments, member)) = &header.concrete
                {
                    concrete.push((arguments.clone(), *member, header.associated.clone()));
                }
            }
            if reason.is_none() {
                if concrete.is_empty() {
                    // An open dynamic object may have no concrete impl at
                    // declaration time: every member can come from a generic
                    // or blanket impl and is registered at its coercion site.
                    if !dynamic {
                        reason = Some(format!("trait '{trait_name}' has no concrete impls"));
                    }
                } else {
                    let mut associated_consts: BTreeMap<
                        TraitArguments,
                        BTreeMap<String, ConstValue>,
                    > = BTreeMap::new();
                    for (arguments, member, associated) in &concrete {
                        groups.entry(arguments.clone()).or_default().push(*member);
                        // A default associated type may mention the trait's
                        // type, Nat, Grade, or effect parameters. Lower it with
                        // this specialization's arguments, exactly like a
                        // method signature, so two impls using the same
                        // default do not spuriously disagree.
                        let mut member_substitution = crate::runtime_types::Subst::default();
                        let mut member_consts = BTreeMap::new();
                        let mut member_grades = BTreeMap::new();
                        let mut member_effects = BTreeMap::new();
                        insert_trait_arguments(
                            resolution,
                            &definition.generics,
                            arguments,
                            &mut member_substitution,
                            &mut member_consts,
                            &mut member_grades,
                            &mut member_effects,
                        );
                        member_substitution.consts = member_consts;
                        member_substitution.grades = member_grades;
                        member_substitution.effects = member_effects;
                        member_substitution.associated_types = associated.types.clone();
                        let types_entry = object_associated.entry(arguments.clone()).or_default();
                        for (name, value) in &associated.types {
                            let lowered = types.ty_in(value, &member_substitution)?;
                            if let Some(previous) = types_entry.get(name)
                                && *previous != lowered
                            {
                                reason = Some(format!(
                                    "impls of trait '{trait_name}' disagree on associated type '{name}'; a dyn object needs one projected type"
                                ));
                                break;
                            }
                            types_entry.insert(name.clone(), lowered);
                        }
                        let consts_entry = associated_consts.entry(arguments.clone()).or_default();
                        for (name, value) in &associated.consts {
                            if let Some(previous) = consts_entry.get(name)
                                && previous != value
                            {
                                reason = Some(format!(
                                    "impls of trait '{trait_name}' disagree on associated constant '{name}'; a dyn object would have ambiguous constant projection"
                                ));
                                break;
                            }
                            consts_entry.insert(name.clone(), value.clone());
                        }
                        if reason.is_some() {
                            break;
                        }
                    }
                }
            }
        }
        for (arguments, mut members) in groups {
            if dynamic {
                // Open objects do not enumerate members in the value layout.
                // Concrete impls still contribute agreed associated values for
                // method signatures; generic impls are checked when a concrete
                // member is registered at a coercion site.
                if let Some(values) = object_associated.get(&arguments) {
                    types.agree_object_projections(trait_id, &arguments, values)?;
                }
                continue;
            }
            members.sort();
            members.dedup();
            let object = match types.object_union(members, resolution.bindings[trait_id].span) {
                Ok(object) => object,
                Err(error) => {
                    // A trait with many impls that is never used as `dyn` must
                    // not make an otherwise valid program fail.
                    reason = Some(format!(
                        "cannot build a closed-world union: {}",
                        error.message
                    ));
                    break;
                }
            };
            if let Some(values) = object_associated.get(&arguments) {
                types.agree_object_projections(trait_id, &arguments, values)?;
            }
            types
                .dyn_objects
                .insert((trait_id, arguments.clone()), object);
            functions
                .object_traits
                .entry(object)
                .or_default()
                .push((trait_id, arguments));
        }
        if let Some(reason) = reason {
            // A trait object used in an already-laid-out nominal field cannot
            // defer this to the first `dyn` lowering: the layout is committed.
            if types
                .objects
                .iter()
                .any(|object| object.components.iter().any(|(id, _)| *id == trait_id))
            {
                return Err(Diagnostic::new(
                    resolution.bindings[trait_id].span,
                    format!("trait '{trait_name}' is not object-safe: {reason}"),
                ));
            }
            types.dyn_errors.insert(trait_id, reason);
        }
    }
    for entries in functions.object_traits.values_mut() {
        entries.sort();
        entries.dedup();
    }
    Ok(())
}
