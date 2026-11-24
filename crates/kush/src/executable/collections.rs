//! Runtime-sized arrays and vector calls.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Runtime-sized inline array constructors and reads. The capacity is a
    /// compile-time bound; only the length is dynamic. `DynArray.new` and
    /// `DynArray.push` preserve the inline representation (no heap allocation),
    /// while `DynArray.len`/`DynArray.get` borrow the value for the call, so a
    /// view into the dynamic stack storage cannot escape its lexical owner.
    pub(super) fn dyn_array_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let from_expected = expected.and_then(|ty| {
            ty.layout()
                .and_then(|id| self.types.enums[id].dynamic_array)
        });
        let explicit_layout = match explicit {
            Some([element_ty, capacity_ty]) => {
                let element = self.ty(element_ty)?;
                let element = self.types.full(element, span)?;
                let capacity = crate::length::eval_type(
                    self.resolution,
                    self.logical,
                    &self.consts,
                    capacity_ty,
                )?;
                Some((element, capacity))
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    "DynArray expects two arguments: an element type and a compile-time capacity",
                ));
            }
            None => None,
        };
        let expected_binder = expected
            .and_then(|ty| ty.layout())
            .and_then(|id| self.types.enums[id].runtime_length);
        match name {
            "Array.fill" => {
                let (element, capacity) = explicit_layout.or(from_expected).ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        "cannot infer the element type and capacity of Array.fill; annotate the binding as [T; n <= C] or write Array.fill::<T, C>(n, value)",
                    )
                })?;
                if arguments.len() != 2 {
                    return Err(Diagnostic::new(
                        span,
                        "Array.fill takes the length binder and one copyable element",
                    ));
                }
                let binder_error = || {
                    Diagnostic::new(
                        arguments[0].span,
                        "the length of Array.fill must be the name of an immutable i64 parameter or local; it becomes the n of [T; n <= C]",
                    )
                };
                let ast::ExprKind::Name(_) = &arguments[0].kind else {
                    return Err(binder_error());
                };
                let binder = self
                    .resolution
                    .reference(arguments[0].span)
                    .ok_or_else(binder_error)?;
                self.runtime_length_slot(binder, arguments[0].span)?;
                if let Some(expected_binder) = expected_binder
                    && expected_binder != binder
                {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!(
                            "Array.fill builds a [T; {} <= C], but the expected type has length '{}'",
                            self.resolution.bindings[binder].name,
                            self.resolution.bindings[expected_binder].name
                        ),
                    ));
                }
                let ty = self.types.runtime_array(element, capacity, binder, span)?;
                let length = self.expr_expected(&arguments[0], Some(Type::I64))?;
                self.expect(length.ty, Type::I64, arguments[0].span)?;
                let value = self.expr_expected(&arguments[1], Some(element))?;
                self.expect(value.ty, element, arguments[1].span)?;
                if self.owned_type(element) || self.linear_type(element) || element.is_view() {
                    return Err(Diagnostic::new(
                        arguments[1].span,
                        "Array.fill copies its element into every slot; owning, linear, and view elements need a literal with a proved length",
                    ));
                }
                let term = self.runtime_length_term(binder, arguments[0].span)?;
                let proved = self.try_prove(
                    vec![
                        (crate::facts::Linear::constant(0), Kind::Le, term.clone()),
                        (
                            term,
                            Kind::Le,
                            crate::facts::Linear::constant(capacity as i128),
                        ),
                    ],
                    &format!("0 <= n && n <= {capacity}"),
                    span,
                );
                if !proved {
                    self.require(PANIC, span)?;
                }
                let value = Expr {
                    kind: ExprKind::DynArrayFill {
                        length: Box::new(length),
                        value: Box::new(value),
                        element,
                        capacity,
                        check: !proved,
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
            "DynArray.new" if expected_binder.is_some() => Err(Diagnostic::new(
                span,
                "a runtime-length array [T; n <= C] cannot start empty; build it with Array.fill(n, value) or a literal whose length is proved equal to n",
            )),
            "DynArray.new" => {
                let (element, capacity) = explicit_layout.or(from_expected).ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        "cannot infer the DynArray element type and capacity; annotate the binding or write DynArray.new::<T, capacity>()",
                    )
                })?;
                let ty = self.types.dynamic_array(element, capacity, span)?;
                if !arguments.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.new takes no value arguments; push elements with DynArray.push",
                    ));
                }
                let value = Expr {
                    kind: ExprKind::DynArrayNew { element, capacity },
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "DynArray.push" => {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.push infers its element type from the array argument",
                    ));
                }
                if arguments.len() != 2 {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.push takes the array and one element",
                    ));
                }
                let array = if let Some(expected) = expected {
                    self.expr_expected(&arguments[0], Some(expected))?
                } else {
                    self.expr(&arguments[0])?
                };
                let Some((element, capacity)) = array
                    .ty
                    .layout()
                    .and_then(|id| self.types.enums[id].dynamic_array)
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        "DynArray.push requires a runtime-sized inline array",
                    ));
                };
                self.reject_length_change(array.ty, name, arguments[0].span)?;
                let ty = array.ty;
                let value = self.expr_expected(&arguments[1], Some(element))?;
                self.expect(value.ty, element, arguments[1].span)?;
                self.require(PANIC, span)?;
                let value = Expr {
                    kind: ExprKind::DynArrayPush {
                        array: Box::new(array),
                        value: Box::new(value),
                        element,
                        capacity,
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
            "DynArray.set" | "DynArray.pop" => {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes no type arguments"),
                    ));
                }
                let wanted = if name == "DynArray.set" { 3 } else { 1 };
                if arguments.len() != wanted {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes {wanted} argument(s)"),
                    ));
                }
                let array = if let Some(expected) = expected {
                    // `pop` returns a tuple, so its array position cannot use
                    // the whole expected type as a hint; only `set` can.
                    if name == "DynArray.set" {
                        self.expr_expected(&arguments[0], Some(expected))?
                    } else {
                        self.expr(&arguments[0])?
                    }
                } else {
                    self.expr(&arguments[0])?
                };
                let Some((element, capacity)) = array
                    .ty
                    .layout()
                    .and_then(|id| self.types.enums[id].dynamic_array)
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!("{name} requires a runtime-sized inline array"),
                    ));
                };
                if name == "DynArray.pop" {
                    self.reject_length_change(array.ty, name, arguments[0].span)?;
                }
                if self.owned_type(element) || self.linear_type(element) || element.is_view() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "{name} moves or copies its element; owning, linear, and view elements need an explicit consuming operation"
                        ),
                    ));
                }
                if name == "DynArray.set" {
                    let index = self.expr_expected(&arguments[1], Some(Type::I64))?;
                    self.expect(index.ty, Type::I64, arguments[1].span)?;
                    let value = self.expr_expected(&arguments[2], Some(element))?;
                    self.expect(value.ty, element, arguments[2].span)?;
                    self.require(PANIC, span)?;
                    let ty = array.ty;
                    let value = Expr {
                        kind: ExprKind::DynArraySet {
                            array: Box::new(array),
                            index: Box::new(index),
                            value: Box::new(value),
                            element,
                            capacity,
                        },
                        ty,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => self.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                self.require(PANIC, span)?;
                let ty = self.types.tuple(vec![array.ty, element], span)?;
                let value = Expr {
                    kind: ExprKind::DynArrayPop {
                        array: Box::new(array),
                        element,
                        capacity,
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
            "DynArray.len" | "DynArray.get" => {
                if explicit.is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes no type arguments"),
                    ));
                }
                let wanted = if name == "DynArray.get" { 2 } else { 1 };
                if arguments.len() != wanted {
                    return Err(Diagnostic::new(
                        span,
                        format!("{name} takes {wanted} argument(s)"),
                    ));
                }
                let array = self.expr(&arguments[0])?;
                let Some(pointer) = array.ty.ref_pointee() else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!("{name} requires a '&DynArray<T, capacity>' borrow"),
                    ));
                };
                let ty = self.types.pointees[pointer];
                let Some((element, _capacity)) = ty
                    .layout()
                    .and_then(|id| self.types.enums[id].dynamic_array)
                else {
                    return Err(Diagnostic::new(
                        arguments[0].span,
                        format!("{name} requires a borrow of a runtime-sized inline array"),
                    ));
                };
                if name == "DynArray.len" {
                    let value = Expr {
                        kind: ExprKind::Call(
                            Target::DynArray(DynArrayOp::Len, element),
                            vec![array],
                        ),
                        ty: Type::I64,
                        span,
                        resource: None,
                    };
                    return match expected {
                        Some(expected) => self.coerce(value, expected, span),
                        None => Ok(value),
                    };
                }
                if self.owned_type(element) || self.linear_type(element) || element.is_view() {
                    return Err(Diagnostic::new(
                        span,
                        "DynArray.get copies its element; owning, linear, and view elements need an explicit consuming operation",
                    ));
                }
                self.require(PANIC, span)?;
                let index = self.expr_expected(&arguments[1], Some(Type::I64))?;
                self.expect(index.ty, Type::I64, arguments[1].span)?;
                let value = Expr {
                    kind: ExprKind::Call(
                        Target::DynArray(DynArrayOp::Get, element),
                        vec![array, index],
                    ),
                    ty: element,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            _ => Err(Diagnostic::new(
                span,
                format!("unsupported DynArray operation '{name}'"),
            )),
        }
    }
    pub(super) fn vec_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let arity = match name {
            "Vec.new" => 0,
            "Vec.with_capacity" | "Vec.len" | "Vec.pop" | "Vec.clear" => 1,
            "Vec.get"
            | "Vec.push"
            | "Vec.map_in_place"
            | "Vec.map_in_place_grow"
            | "Vec.reserve"
            | "Vec.try_reserve"
            | "Vec.replace" => 2,
            "Vec.map_chain_in_place" | "Vec.map_chain_in_place_grow" => 3,
            _ => 3,
        };
        if arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        if name == "Vec.pop" {
            return Err(Diagnostic::new(
                span,
                "Vec.pop is not available yet; read with Vec.get/Vec.at and rebuild",
            ));
        }
        if explicit.is_some()
            && !matches!(
                name,
                "Vec.new"
                    | "Vec.with_capacity"
                    | "Vec.map_in_place"
                    | "Vec.map_in_place_grow"
                    | "Vec.map_chain_in_place"
                    | "Vec.map_chain_in_place_grow"
            )
        {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        if name == "Vec.map_in_place" {
            return self.vec_map_call(false, explicit, arguments, expected, span);
        }
        if name == "Vec.map_in_place_grow" {
            return self.vec_map_call(true, explicit, arguments, expected, span);
        }
        if name == "Vec.map_chain_in_place" {
            return self.vec_map_chain_call(false, explicit, arguments, expected, span);
        }
        if name == "Vec.map_chain_in_place_grow" {
            return self.vec_map_chain_call(true, explicit, arguments, expected, span);
        }
        if matches!(name, "Vec.new" | "Vec.with_capacity") {
            let element = match (explicit, expected) {
                (Some([t]), _) => {
                    let ty = self.ty(t)?;
                    self.types.full(ty, span)?
                }
                (Some(_), _) => return Err(Diagnostic::new(span, "Vec expects one element type")),
                (None, Some(Type::Vec(p))) => self.types.pointees[p],
                (None, Some(Type::Union(id))) => {
                    let mut elements = Vec::new();
                    for member in self.types.unions[id].members.iter() {
                        if let Type::Vec(p) = member
                            && !elements.contains(&self.types.pointees[*p])
                        {
                            elements.push(self.types.pointees[*p]);
                        }
                    }
                    match elements.as_slice() {
                        [element] => *element,
                        [] => {
                            return Err(Diagnostic::new(
                                span,
                                "the expected union has no Vec<T> alternative for this constructor",
                            ));
                        }
                        _ => {
                            return Err(Diagnostic::new(
                                span,
                                "this empty vector constructor fits several union alternatives; write the element type explicitly as Vec.new::<T>()",
                            ));
                        }
                    }
                }
                _ => {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "cannot infer the element type; annotate the binding (let v: Vec<T> = {name}(...)) or write {name}::<T>(...)"
                        ),
                    ));
                }
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
            if crate::runtime_types::contains_task(self.types, element) {
                return Err(Diagnostic::new(
                    span,
                    "task handles cannot be stored in Vec; join them in the scope that owns them",
                ));
            }
            self.require(ALLOC | PANIC, span)?;
            let capacity = if name == "Vec.new" {
                unit(ExprKind::Constant(0), Type::I64)
            } else {
                let c = self.expr_expected(&arguments[0], Some(Type::I64))?;
                self.expect(c.ty, Type::I64, c.span)?;
                c
            };
            let ty = if capacity.ty == Type::Never {
                Type::Never
            } else {
                Type::Vec(self.types.pointer(element))
            };
            let value = unit(
                ExprKind::Call(Target::Vec(VecOp::WithCapacity, element), vec![capacity]),
                ty,
            );
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if matches!(arguments[0].kind, ast::ExprKind::Name(_))
            && let Some(length) = self.place_min_length(&arguments[0])
        {
            match name {
                "Vec.clear" => {
                    return Err(Diagnostic::new(
                        span,
                        "this parameter keeps 'len >= N'; clearing it would break that",
                    ));
                }
                "Vec.replace" => self.replace_min_length = Some(length),
                _ => {}
            }
            self.refined_use_ok = true;
        }
        let first = self.expr(&arguments[0]);
        self.refined_use_ok = false;
        let first = first?;
        self.vec_call_with(name, first, &arguments[1..], expected, span)
    }
    /// Vector/Bytes `.at` builtin with an already checked receiver. The
    /// receiver is evaluated exactly once, before `rest`.
    pub(super) fn vec_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let arity = match name {
            "Vec.len" | "Vec.clear" => 0,
            "Vec.get" | "Vec.push" | "Vec.reserve" | "Vec.try_reserve" | "Vec.replace" => 1,
            _ => 2,
        };
        if rest.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        let mut borrowed_mutation = false;
        let buffer = match (name, first.ty) {
            ("Bytes.at", Type::Ref(p) | Type::RefMut(p))
                if self.types.pointees[p] == Type::Bytes =>
            {
                Type::Bytes
            }
            ("Vec.len" | "Vec.get" | "Vec.at", Type::Ref(p) | Type::RefMut(p))
                if matches!(self.types.pointees[p], Type::Vec(_)) =>
            {
                self.types.pointees[p]
            }
            (
                "Vec.push" | "Vec.set" | "Vec.clear" | "Vec.reserve" | "Vec.try_reserve",
                Type::Vec(_),
            ) => first.ty,
            (
                "Vec.push" | "Vec.set" | "Vec.clear" | "Vec.reserve" | "Vec.replace",
                Type::RefMut(p),
            ) if matches!(self.types.pointees[p], Type::Vec(_)) => {
                borrowed_mutation = true;
                self.types.pointees[p]
            }
            (_, Type::Never) => return Ok(first),
            _ => {
                let wanted = match name {
                    "Bytes.at" => "&Bytes",
                    "Vec.push" | "Vec.set" | "Vec.clear" | "Vec.reserve" | "Vec.try_reserve" => {
                        "an owned Vec<T> (it is consumed and returned), or an exclusive '&mut Vec<T>' for an in-place update"
                    }
                    "Vec.replace" => "an exclusive '&mut Vec<T>' whose vector is swapped out",
                    _ => "&Vec<T>",
                };
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "{name} expects {wanted}, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
        };
        let element = match buffer {
            Type::Vec(p) => self.types.pointees[p],
            _ => Type::I64,
        };
        let mut values = vec![first];
        let index_position = matches!(name, "Vec.get" | "Vec.at" | "Vec.set" | "Bytes.at");
        if index_position {
            let index = self.expr_expected(&rest[0], Some(Type::I64))?;
            self.expect(index.ty, Type::I64, index.span)?;
            values.push(index);
        }
        if matches!(name, "Vec.push" | "Vec.set") {
            let value = self.expr_expected(&rest[arity - 1], Some(element))?;
            self.expect(value.ty, element, value.span)?;
            if crate::runtime_types::contains_task(self.types, value.ty) {
                return Err(Diagnostic::new(
                    value.span,
                    "task handles cannot be stored in Vec; join them in the scope that owns them",
                ));
            }
            values.push(value);
        }
        if name == "Vec.replace" {
            if crate::runtime_types::has_borrow(self.types, element) {
                return Err(Diagnostic::new(
                    span,
                    "Vec.replace moves vectors of owned or copyable elements; this element holds a borrow",
                ));
            }
            let value = self.expr_expected(&rest[0], Some(buffer))?;
            self.expect(value.ty, buffer, value.span)?;
            // Into a length-refined field: the new vector is checked to keep
            // the promised length, once, like a record construction.
            let value = match self.replace_min_length.take() {
                Some(length) => self.length_checked(value, buffer, length)?,
                None => value,
            };
            values.push(value);
        }
        if matches!(name, "Vec.reserve" | "Vec.try_reserve") {
            let additional = self.expr_expected(&rest[0], Some(Type::I64))?;
            self.expect(additional.ty, Type::I64, additional.span)?;
            values.push(additional);
        }
        if matches!(name, "Vec.get" | "Vec.at") && self.owned_type(element) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} copies the element, but {} owns resources",
                    self.types.name(element)
                ),
            ));
        }
        let (op, effects, ty) = match name {
            "Vec.len" => (VecOp::Len, 0, Type::I64),
            "Vec.clear" if borrowed_mutation => (VecOp::ClearBorrowed, 0, Type::Unit),
            "Vec.replace" => (VecOp::ReplaceBorrowed, 0, buffer),
            "Vec.clear" => (VecOp::Clear, 0, buffer),
            "Vec.reserve" if borrowed_mutation => {
                (VecOp::ReserveBorrowed, ALLOC | PANIC, Type::Unit)
            }
            "Vec.reserve" => (VecOp::Reserve, ALLOC | PANIC, buffer),
            "Vec.try_reserve" => {
                let (result, shape) = self.types.result_type(buffer, buffer, span)?;
                (
                    VecOp::TryReserve {
                        ok_tag: shape.ok_tag,
                        err_tag: shape.err_tag,
                    },
                    ALLOC,
                    result,
                )
            }
            "Vec.get" => (VecOp::Get, PANIC, self.unannotate(element)),
            "Vec.at" | "Bytes.at" => (VecOp::At, 0, self.unannotate(element)),
            "Vec.push" if borrowed_mutation => (VecOp::PushBorrowed, ALLOC | PANIC, Type::Unit),
            "Vec.push" => (VecOp::Push, ALLOC | PANIC, buffer),
            "Vec.set" if borrowed_mutation => (VecOp::SetBorrowed, PANIC, Type::Unit),
            _ => (VecOp::Set, PANIC, buffer),
        };
        self.require(effects, span)?;
        if values.iter().any(|v| v.ty == Type::Never) {
            return Ok(unit(
                ExprKind::Call(Target::Vec(op, element), values),
                Type::Never,
            ));
        }
        if op == VecOp::At {
            use crate::facts::{ParamLinear, ParamTerm, Proposition};
            let proposition = Proposition {
                disjuncts: vec![vec![
                    (
                        ParamLinear::constant(0),
                        Kind::Le,
                        ParamLinear::variable(ParamTerm::Param(1), 1),
                    ),
                    (
                        ParamLinear::variable(ParamTerm::Param(1), 1),
                        Kind::Lt,
                        ParamLinear::variable(ParamTerm::Len(0), 1),
                    ),
                ]],
                booleans: Vec::new(),
                text: format!(
                    "0 <= index && index < {}.len(buffer)",
                    if buffer == Type::Bytes {
                        "Bytes"
                    } else {
                        "Vec"
                    }
                ),
            };
            self.discharge(&proposition, &values, &rest[1], span)?;
        }
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        if name == "Bytes.at" {
            let index = values.pop().unwrap();
            let bytes = values.pop().unwrap();
            let value = unit(
                ExprKind::BytesAt(Box::new(bytes), Box::new(index)),
                Type::I64,
            );
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let (statements, values) = self.two_phase_arguments(values, ty)?;
        let value = Self::after(
            statements,
            unit(ExprKind::Call(Target::Vec(op, element), values), ty),
        );
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Check an allocation-preserving `Vec.map_in_place(values, f)`.
    ///
    /// The callback must be a copyable `fn(T) -> U ! {e}`. Its effects are
    /// required by the enclosing function, so a `noalloc` function rejects an
    /// allocating callback independently of any optimization. `once` and
    /// linear-once callbacks are rejected because the transform would duplicate
    /// the callable across elements. The result layout must be no wider than
    /// the source element layout, because the vector allocation is preserved.
    pub(super) fn vec_map_call(
        &mut self,
        grow: bool,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if grow {
            // Growth is an explicit allocating fallback and may abort on
            // exhausted storage, exactly like `Box.reuse_grow`.
            self.require(ALLOC | PANIC, span)?;
        }
        let vector = self.expr(&arguments[0])?;
        let Type::Vec(index) = vector.ty else {
            if vector.ty == Type::Never {
                let _ = self.expr(&arguments[1])?;
                return Ok(vector);
            }
            return Err(Diagnostic::new(
                vector.span,
                format!(
                    "Vec.map_in_place consumes an owned Vec<T>; found {} (borrows and slice views cannot be transformed in place)",
                    self.types.name(vector.ty)
                ),
            ));
        };
        let source = self.types.pointees[index];
        if crate::runtime_types::has_borrow(self.types, source) {
            return Err(Diagnostic::new(
                span,
                "Vec.map_in_place cannot transform a vector of borrowed reference elements; the in-place callback would repack or copy a loan descriptor",
            ));
        }
        if self.linear_type(source) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "vectors cannot hold linear values; in-place transformation cannot consume {}",
                    self.types.name(source)
                ),
            ));
        }
        let callback = self.expr(&arguments[1])?;
        if callback.ty == Type::Never {
            // Unreachable, but keep the callback in the IR so evaluation order
            // and any pending-owner cleanup remain explicit.
            let target = match explicit {
                Some([ty]) => self.ty(ty)?,
                Some(_) => {
                    return Err(Diagnostic::new(
                        span,
                        "Vec.map_in_place accepts at most one result element type",
                    ));
                }
                None => source,
            };
            return Ok(Expr {
                kind: ExprKind::VecMap {
                    vector: Box::new(vector),
                    callbacks: vec![callback],
                    source,
                    target,
                    grow,
                },
                ty: Type::Never,
                span,
                resource: None,
            });
        }
        let Type::Fn(callback_id) = callback.ty else {
            if matches!(callback.ty, Type::Once(_)) {
                return Err(Diagnostic::new(
                    callback.span,
                    "Vec.map_in_place calls its callback once per element; a once or linear-once callback cannot be duplicated. Use a noncapturing fn value",
                ));
            }
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place expects a noncapturing fn(T) -> U value, found {}",
                    self.types.name(callback.ty)
                ),
            ));
        };
        let signature = self.types.function_types[callback_id].clone();
        if signature.parameters.len() != 1 {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place expects a one-argument callback, found {} parameters",
                    signature.parameters.len()
                ),
            ));
        }
        let parameter = signature.parameters[0];
        if signature.parameter_erased(0) {
            return Err(Diagnostic::new(
                callback.span,
                "Vec.map_in_place cannot use a callback whose element parameter is graded @[0]; the transform still passes each element to the callback",
            ));
        }
        if signature.result_erased() {
            return Err(Diagnostic::new(
                callback.span,
                "Vec.map_in_place cannot use a callback whose result is graded @[0]; the transform stores each returned element",
            ));
        }
        if !self.subtype(source, parameter) || !self.same_layout(source, parameter) {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place callback parameter {} must accept the vector element {} with the same runtime layout",
                    self.types.name(parameter),
                    self.types.name(source)
                ),
            ));
        }
        self.require(signature.effects, span)?;
        let target = match explicit {
            Some([ty]) => {
                let target = self.ty(ty)?;
                self.types.full(target, span)?
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    "Vec.map_in_place accepts at most one result element type",
                ));
            }
            None => match expected {
                Some(Type::Vec(p)) => self.types.pointees[p],
                _ => signature.result,
            },
        };
        if !self.subtype(signature.result, target) || !self.same_layout(signature.result, target) {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_in_place callback returns {}, but the result element layout is {}; an in-place transform cannot insert a representation-changing coercion",
                    self.types.name(signature.result),
                    self.types.name(target)
                ),
            ));
        }
        if matches!(target, Type::Ref(_) | Type::RefMut(_) | Type::Never) || target.is_view() {
            return Err(Diagnostic::new(
                span,
                "vector elements must be concrete runtime values, not references, slice views, or Never",
            ));
        }
        if self.linear_type(target) {
            return Err(Diagnostic::new(
                span,
                "Vec.map_in_place cannot store linear result elements in a vector",
            ));
        }
        if crate::runtime_types::contains_task(self.types, target) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Vec; join them in the scope that owns them",
            ));
        }
        let source_width = self.types.width(source);
        let target_width = self.types.width(target);
        if !grow && target_width > source_width {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_in_place cannot widen elements from {source_width} to {target_width} word(s) in the preserved allocation; build a new Vec<{}> instead, or use Vec.map_in_place_grow for an explicit {{alloc, panic}} fallback",
                    self.types.name(target)
                ),
            ));
        }
        // Automatic fusion is selected after all bodies are checked, where the
        // analysis can inspect callee effect rows, recursion, and loops. The
        // operation still records the explicit nested map structure here.
        let (vector, mut callbacks, source) = (Box::new(vector), Vec::new(), source);
        callbacks.push(callback);
        let ty = Type::Vec(self.types.pointer(target));
        let value = Expr {
            kind: ExprKind::VecMap {
                vector,
                callbacks,
                source,
                target,
                grow,
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
    /// Check the explicit interleaved transform
    /// `Vec.map_chain_in_place(values, f, g)`.
    ///
    /// The order is fixed by the operation: every element sees `f` and then
    /// `g` before the next element starts (`f(0), g(0), f(1), g(1), ...`).
    /// This is not compiler-selected fusion: both callbacks are always kept in
    /// the IR, their effects are required independently, and no nested map or
    /// chain is flattened automatically. Intermediate callback results may use
    /// a wider transient SSA layout than the source element; only the final
    /// element layout has to fit the preserved allocation.
    pub(super) fn vec_map_chain_call(
        &mut self,
        grow: bool,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if grow {
            self.require(ALLOC | PANIC, span)?;
        }
        let vector = self.expr(&arguments[0])?;
        if vector.ty == Type::Never {
            // The receiver diverges before either callback is evaluated, but
            // still check both callback expressions for diagnostics and
            // effect demands.
            let _ = self.expr(&arguments[1])?;
            let _ = self.expr(&arguments[2])?;
            return Ok(vector);
        }
        let Type::Vec(index) = vector.ty else {
            return Err(Diagnostic::new(
                vector.span,
                format!(
                    "Vec.map_chain_in_place consumes an owned Vec<T>; found {} (borrows and slice views cannot be transformed in place)",
                    self.types.name(vector.ty)
                ),
            ));
        };
        let source = self.types.pointees[index];
        if crate::runtime_types::has_borrow(self.types, source) {
            return Err(Diagnostic::new(
                span,
                "Vec.map_chain_in_place cannot transform a vector of borrowed reference elements; the in-place chain would repack or copy a loan descriptor",
            ));
        }
        if self.linear_type(source) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "vectors cannot hold linear values; an in-place chain cannot consume {}",
                    self.types.name(source)
                ),
            ));
        }
        // Callback expressions are evaluated exactly once, left to right,
        // before the element loop starts; an empty vector still evaluates both.
        let first = self.expr(&arguments[1])?;
        let second = self.expr(&arguments[2])?;
        let explicit_target = match explicit {
            Some([ty]) => {
                let target = self.ty(ty)?;
                Some(self.types.full(target, span)?)
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    "Vec.map_chain_in_place accepts at most one result element type",
                ));
            }
            None => None,
        };
        let never = |vector: Box<Expr>, callbacks, target: Type| Expr {
            kind: ExprKind::VecMap {
                vector,
                callbacks,
                source,
                target,
                grow,
            },
            ty: Type::Never,
            span,
            resource: None,
        };
        if first.ty == Type::Never {
            // Evaluating the first callback value diverges, so the second
            // callback expression is unreachable. Keep the first callback in
            // the IR so its evaluation and cleanup are explicit.
            return Ok(never(
                Box::new(vector),
                vec![first],
                explicit_target.unwrap_or(source),
            ));
        }
        if second.ty == Type::Never {
            return Ok(never(
                Box::new(vector),
                vec![first, second],
                explicit_target.unwrap_or(source),
            ));
        }
        let intermediate = self.vec_map_chain_step(&first, source, "first", span)?;
        self.vec_map_chain_payload(intermediate, first.span, "first")?;
        let result = self.vec_map_chain_step(&second, intermediate, "second", span)?;
        self.vec_map_chain_payload(result, second.span, "second")?;
        let target = explicit_target.unwrap_or(match expected {
            Some(Type::Vec(p)) => self.types.pointees[p],
            _ => result,
        });
        if !self.subtype(result, target) || !self.same_layout(result, target) {
            return Err(Diagnostic::new(
                second.span,
                format!(
                    "Vec.map_chain_in_place second callback returns {}, but the final result element layout is {}; an in-place chain cannot insert a representation-changing coercion",
                    self.types.name(result),
                    self.types.name(target)
                ),
            ));
        }
        self.vec_map_chain_payload(target, span, "final")?;
        let source_width = self.types.width(source);
        let target_width = self.types.width(target);
        if !grow && target_width > source_width {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_chain_in_place cannot widen elements from {source_width} to {target_width} word(s) in the preserved allocation; build a new Vec<{}> instead, or use Vec.map_chain_in_place_grow for an explicit {{alloc, panic}} fallback",
                    self.types.name(target)
                ),
            ));
        }
        let ty = Type::Vec(self.types.pointer(target));
        let value = Expr {
            kind: ExprKind::VecMap {
                vector: Box::new(vector),
                callbacks: vec![first, second],
                source,
                target,
                grow,
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
    /// Check one reusable `fn(T) -> U` step of a chain against its input type.
    pub(super) fn vec_map_chain_step(
        &mut self,
        callback: &Expr,
        input: Type,
        position: &str,
        span: Span,
    ) -> Result<Type> {
        let Type::Fn(id) = callback.ty else {
            if matches!(callback.ty, Type::Once(_)) {
                return Err(Diagnostic::new(
                    callback.span,
                    "Vec.map_chain_in_place calls each callback once per element; a once or linear-once callback cannot be reused across elements. Use noncapturing fn values",
                ));
            }
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place expects a noncapturing fn(T) -> U value for its {position} callback, found {}",
                    self.types.name(callback.ty)
                ),
            ));
        };
        let signature = self.types.function_types[id].clone();
        if signature.parameters.len() != 1 {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place {position} callback must take exactly one argument, found {} parameters",
                    signature.parameters.len()
                ),
            ));
        }
        let parameter = signature.parameters[0];
        if signature.parameter_erased(0) || signature.result_erased() {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place {position} callback cannot erase its element parameter or result; every element is observed and every result is stored"
                ),
            ));
        }
        if !self.subtype(input, parameter) || !self.same_layout(input, parameter) {
            return Err(Diagnostic::new(
                callback.span,
                format!(
                    "Vec.map_chain_in_place {position} callback parameter {} must accept {} with the same runtime layout",
                    self.types.name(parameter),
                    self.types.name(input)
                ),
            ));
        }
        self.require(signature.effects, span)?;
        Ok(signature.result)
    }
    /// Reject payloads a vector slot cannot represent, including transient
    /// chain results. Linear obligations, views, task handles, and `Never`
    /// cannot be moved through an in-place element slot.
    pub(super) fn vec_map_chain_payload(&self, ty: Type, span: Span, position: &str) -> Result<()> {
        if matches!(ty, Type::Ref(_) | Type::RefMut(_) | Type::Never) || ty.is_view() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_chain_in_place cannot carry the {position} value {}; references, slice views, and Never are not concrete vector payloads",
                    self.types.name(ty)
                ),
            ));
        }
        if self.linear_type(ty) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "Vec.map_chain_in_place cannot store linear {position} elements in a vector"
                ),
            ));
        }
        if crate::runtime_types::contains_task(self.types, ty) {
            return Err(Diagnostic::new(
                span,
                "task handles cannot be stored in Vec; join them in the scope that owns them",
            ));
        }
        Ok(())
    }
    /// Facts about locals assigned anywhere in a loop body, or written by a
    /// callable the loop may execute, do not survive into it: the next
    /// iteration may observe the new value.
    pub(super) fn bump_assigned(&mut self, body: &ast::Block, condition: Option<&ast::Expr>) {
        type Out<'e> = Vec<(Span, Option<&'e ast::Expr>)>;
        struct Calls<'e, 'r> {
            resolution: &'r Resolution,
            values: BTreeMap<BindingId, Vec<&'e ast::Expr>>,
            active: BTreeSet<BindingId>,
            /// Bindings whose possible values were already followed in this
            /// pass (CHECK-LOOP-PERF). Every write reached through `invoke`
            /// is recorded with an unknown direction, so following a binding
            /// again only adds duplicates; without this, a body that passes
            /// reassigned locals to calls re-walked all their assignments at
            /// every call, cubic in the body's length.
            expanded: BTreeSet<BindingId>,
            invoked: BTreeSet<BindingId>,
            handlers: Vec<&'e ast::Expr>,
            may_execute: bool,
            collecting: bool,
        }
        fn invoke<'e>(value: &'e ast::Expr, out: &mut Out<'e>, calls: &mut Calls<'e, '_>) {
            if calls.collecting {
                return;
            }
            match &value.kind {
                ast::ExprKind::Lambda(lambda) => {
                    let mut writes = Vec::new();
                    block(&lambda.body, &mut writes, calls);
                    out.extend(writes.into_iter().map(|(span, _)| (span, None)));
                }
                ast::ExprKind::Name(_) => {
                    if let Some(id) = calls.resolution.reference(value.span) {
                        follow(id, out, calls);
                    }
                }
                ast::ExprKind::Block(body) => {
                    if let Some(tail) = &body.tail {
                        invoke(tail, out, calls);
                    }
                }
                ast::ExprKind::If {
                    then, otherwise, ..
                } => {
                    if let Some(tail) = &then.tail {
                        invoke(tail, out, calls);
                    }
                    if let Some(otherwise) = otherwise {
                        invoke(otherwise, out, calls);
                    }
                }
                ast::ExprKind::Match { arms, .. } => {
                    for arm in arms {
                        invoke(&arm.body, out, calls);
                    }
                }
                // A callable taken from a tuple, array, or record may be one
                // of several stored values, so every element may execute.
                ast::ExprKind::Tuple(values) | ast::ExprKind::Array(values) => {
                    for value in values {
                        invoke(value, out, calls);
                    }
                }
                ast::ExprKind::StructuralLiteral(fields) => {
                    for (_, value) in fields {
                        invoke(value, out, calls);
                    }
                }
                ast::ExprKind::Record { fields, base, .. } => {
                    for (_, value) in fields {
                        invoke(value, out, calls);
                    }
                    if let Some(base) = base {
                        invoke(base, out, calls);
                    }
                }
                ast::ExprKind::Field { value: base, .. }
                | ast::ExprKind::Index { value: base, .. } => invoke(base, out, calls),
                ast::ExprKind::Specialize { callee, .. }
                | ast::ExprKind::Cast { value: callee, .. } => invoke(callee, out, calls),
                _ => {
                    // An unknown invoked value can contain any referenced callable.
                    let mut references = BTreeSet::new();
                    collect_expr_refs(calls.resolution, value, &mut references);
                    for id in references {
                        follow(id, out, calls);
                    }
                }
            }
        }
        /// Invoke every value `id` may hold, once per pass. A binding that is
        /// active (being followed further up) is completed by that frame.
        fn follow<'e>(id: BindingId, out: &mut Out<'e>, calls: &mut Calls<'e, '_>) {
            calls.invoked.insert(id);
            if calls.expanded.contains(&id) || !calls.active.insert(id) {
                return;
            }
            if let Some(values) = calls.values.get(&id).cloned() {
                for value in values {
                    invoke(value, out, calls);
                }
            }
            calls.active.remove(&id);
            calls.expanded.insert(id);
        }
        fn effects<'e>(out: &mut Out<'e>, calls: &mut Calls<'e, '_>) {
            if calls.collecting {
                return;
            }
            calls.may_execute = true;
            // Unknown calls may perform an operation handled here. Temporarily
            // remove the handlers while expanding them to avoid resumption cycles.
            let handlers = std::mem::take(&mut calls.handlers);
            for handler in &handlers {
                invoke(handler, out, calls);
            }
            calls.handlers = handlers;
        }
        fn block<'e>(b: &'e ast::Block, out: &mut Out<'e>, calls: &mut Calls<'e, '_>) {
            for s in &b.statements {
                match s {
                    ast::Statement::Let { pattern, value, .. } => {
                        expr(value, out, calls);
                        if calls.collecting
                            && let Some(id) = calls.resolution.binder(pattern.span)
                        {
                            calls.values.entry(id).or_default().push(value);
                        }
                    }
                    ast::Statement::Expr(e) => expr(e, out, calls),
                }
            }
            if let Some(t) = &b.tail {
                expr(t, out, calls);
            }
        }
        fn expr<'e>(e: &'e ast::Expr, out: &mut Out<'e>, calls: &mut Calls<'e, '_>) {
            use ast::ExprKind as K;
            match &e.kind {
                K::Binary {
                    op: Kind::Eq,
                    left,
                    right,
                } => {
                    out.push((left.span, Some(right)));
                    expr(right, out, calls);
                    if calls.collecting
                        && let Some(id) = calls.resolution.reference(left.span)
                    {
                        calls.values.entry(id).or_default().push(right);
                    }
                }
                K::Binary { left, right, .. }
                | K::Index {
                    value: left,
                    index: right,
                } => {
                    expr(left, out, calls);
                    expr(right, out, calls);
                }
                K::Slice { value, start, end } => {
                    expr(value, out, calls);
                    if let Some(start) = start {
                        expr(start, out, calls);
                    }
                    if let Some(end) = end {
                        expr(end, out, calls);
                    }
                }
                K::Unary {
                    op: Kind::Amp,
                    mutable: true,
                    operand,
                } if matches!(operand.kind, K::Name(_)) => {
                    // `&mut x` may write `x` through the reference: an update
                    // of unknown direction.
                    out.push((operand.span, None));
                }
                K::Unary { operand, .. }
                | K::Try(operand)
                | K::Cast { value: operand, .. }
                | K::Is { value: operand, .. }
                | K::Field { value: operand, .. } => expr(operand, out, calls),
                K::Return(Some(v)) | K::Break(Some(v)) => expr(v, out, calls),
                K::Tuple(vs) | K::Array(vs) => vs.iter().for_each(|v| expr(v, out, calls)),
                K::Call { callee, arguments } => {
                    effects(out, calls);
                    expr(callee, out, calls);
                    invoke(callee, out, calls);
                    // Callbacks passed to unknown callees may execute, including
                    // Task.scope callbacks and effect resumptions.
                    for argument in arguments {
                        invoke(argument, out, calls);
                    }
                    arguments.iter().for_each(|v| expr(v, out, calls));
                }
                K::Lambda(lambda) => {
                    if calls.collecting {
                        block(&lambda.body, out, calls);
                    }
                }
                K::Handle { handler, body, .. } => {
                    expr(handler, out, calls);
                    calls.handlers.push(handler);
                    block(body, out, calls);
                    calls.handlers.pop();
                }
                K::Perform { value, .. } => {
                    effects(out, calls);
                    expr(value, out, calls);
                }
                K::Specialize { callee, .. } => expr(callee, out, calls),
                K::Block(b) | K::Loop(b) => block(b, out, calls),
                K::While {
                    condition, body, ..
                } => {
                    expr(condition, out, calls);
                    block(body, out, calls);
                }
                K::If {
                    condition,
                    then,
                    otherwise,
                } => {
                    expr(condition, out, calls);
                    block(then, out, calls);
                    if let Some(o) = otherwise {
                        expr(o, out, calls);
                    }
                }
                K::Match { value, arms } => {
                    expr(value, out, calls);
                    for arm in arms {
                        if let Some(g) = &arm.guard {
                            expr(g, out, calls);
                        }
                        expr(&arm.body, out, calls);
                    }
                }
                K::Record { fields, base, .. } => {
                    fields.iter().for_each(|(_, v)| expr(v, out, calls));
                    if let Some(base) = base {
                        expr(base, out, calls);
                    }
                }
                K::StructuralLiteral(fields) => {
                    fields.iter().for_each(|(_, v)| expr(v, out, calls))
                }
                K::Name(_)
                | K::Integer(_)
                | K::Float(_)
                | K::String(_)
                | K::Char(_)
                | K::Bool(_)
                | K::Continue
                | K::Return(None)
                | K::Break(None) => {}
            }
        }
        let mut calls = Calls {
            resolution: self.resolution,
            values: BTreeMap::new(),
            active: BTreeSet::new(),
            expanded: BTreeSet::new(),
            invoked: BTreeSet::new(),
            handlers: Vec::new(),
            may_execute: false,
            collecting: true,
        };
        let mut assignments = Vec::new();
        block(body, &mut assignments, &mut calls);
        if let Some(condition) = condition {
            expr(condition, &mut assignments, &mut calls);
        }
        // Resolve all callable alternatives before following calls: a value
        // assigned later in the body may be invoked on the next iteration.
        assignments.clear();
        calls.collecting = false;
        block(body, &mut assignments, &mut calls);
        if let Some(condition) = condition {
            expr(condition, &mut assignments, &mut calls);
        }
        // Per slot: +1 if every update is `x = x + c` (c >= 0), -1 if every
        // update is `x = x - c` (c >= 0), 0 otherwise.
        let mut direction: BTreeMap<usize, i8> = BTreeMap::new();
        for (span, value) in &assignments {
            let Ok(slot) = self.slot(*span) else { continue };
            let step =
                match value.map(|value| &value.kind) {
                    Some(ast::ExprKind::Binary {
                        op: op @ (Kind::Plus | Kind::Minus),
                        left,
                        right,
                    }) if matches!(&left.kind, ast::ExprKind::Name(_))
                        && self.slot(left.span) == Ok(slot)
                        && matches!(&right.kind, ast::ExprKind::Integer(_)) =>
                    {
                        if *op == Kind::Plus { 1 } else { -1 }
                    }
                    _ => 0,
                };
            direction
                .entry(slot)
                .and_modify(|d| {
                    if *d != step {
                        *d = 0
                    }
                })
                .or_insert(step);
        }
        // Constructing or merely referencing a callable does not execute it.
        // Only invoked values contribute their existing capture-write summaries.
        for id in calls.invoked {
            if let Some(targets) = self
                .slots
                .get(&id)
                .and_then(|slot| self.closure_writes.get(slot))
            {
                for target in targets {
                    direction.insert(*target, 0);
                }
            }
        }
        // An operation in the loop may call an enclosing handler without
        // referring to its synthesized local binding in the source tree.
        for handler in self.handlers.iter().filter(|_| calls.may_execute) {
            if let Some(targets) = self.closure_writes.get(&handler.slot) {
                for target in targets {
                    direction.insert(*target, 0);
                }
            }
        }
        for (slot, step) in direction {
            if step == 0 {
                // A record or enum reassigned in the loop loses its facts and
                // aliases at the loop head too.
                if self.locals[slot].ty.scalar_carrier().is_none() {
                    self.facts.bump(slot);
                }
                self.invalidate_scalar_proofs(slot);
            } else {
                self.facts.bump_monotone(slot, step > 0);
            }
        }
    }
}
