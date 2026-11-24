//! Method calls: builtin, inherent, trait, generic and dynamically dispatched methods, and the places they borrow.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Whether `name` is one of the builtin methods eligible for receiver
    /// syntax. Builtin dispatch is checked first and the name is reserved:
    /// user-defined methods may not reuse it, so there is no ambiguous
    /// reinterpretation between a builtin and an impl method.
    pub(super) fn builtin_method(name: &str) -> bool {
        matches!(
            name,
            "len"
                | "capacity"
                | "get"
                | "at"
                | "try_get"
                | "push"
                | "push_reserved"
                | "clear"
                | "reserve"
                | "try_reserve"
                | "copy"
                | "set"
                | "as_bytes"
                | "as_str"
                | "as_mut_str"
                | "make_ascii_uppercase"
                | "make_ascii_lowercase"
                | "set_scalar"
                | "bytes"
                | "substr"
                | "to_string"
                | "byte_at"
                | "scalar_at"
                | "scalar_len"
                | "from_utf8"
                | "take"
                | "read"
                | "code"
                | "convert"
                | "try_convert"
                | "truncate"
                | "wrapping_add"
                | "wrapping_sub"
                | "wrapping_mul"
                | "saturating_add"
                | "saturating_sub"
                | "saturating_mul"
                | "checked_add"
                | "checked_sub"
                | "checked_mul"
                | "abs"
                | "sqrt"
                | "is_nan"
                | "is_infinite"
                | "is_finite"
                | "to_f64"
                | "try_to_f32"
                | "try_to_int"
        )
    }
    /// Auto-borrow an owning receiver for a read-only builtin. The receiver is
    /// already checked exactly once; only a direct local may become `&name`,
    /// matching the existing borrow rules. A value that is already a reference
    /// is passed through unchanged.
    pub(super) fn method_borrow(&mut self, first: Expr) -> Result<Expr> {
        if matches!(first.ty, Type::Ref(_) | Type::RefMut(_)) {
            return Ok(first);
        }
        if !matches!(
            first.ty,
            Type::Box(_)
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::Task(_)
                | Type::Thread(_)
        ) {
            return Err(Diagnostic::new(
                first.span,
                format!(
                    "this builtin method needs an immutable borrow, but a temporary {} cannot be borrowed; bind it to a local first",
                    self.types.name(first.ty)
                ),
            ));
        }
        let ExprKind::Local(slot) = first.kind else {
            return Err(Diagnostic::new(
                first.span,
                "borrow an owned Box/Bytes/String/Vec/Task local directly; temporary borrows are not supported",
            ));
        };
        let ty = self.locals[slot].ty;
        Ok(Expr {
            kind: ExprKind::Borrow(slot),
            ty: Type::Ref(self.types.pointer(ty)),
            span: first.span,
            resource: None,
        })
    }
    /// Receiver-style call to an existing builtin. The receiver is checked
    /// before the remaining arguments and appears first in the lowered call, so
    /// evaluation order, loan retention, effects, proofs, and Option/Result
    /// shapes are exactly those of the namespace form.
    pub(super) fn method_call(
        &mut self,
        receiver: &ast::Expr,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        // A read-only builtin on an owning field (`m.memory.len()`) borrows
        // the field in place, as `&m.memory` would, instead of moving it out.
        let read_only = matches!(
            name,
            "len"
                | "capacity"
                | "get"
                | "try_get"
                | "at"
                | "copy"
                | "byte_at"
                | "scalar_at"
                | "scalar_len"
                | "as_bytes"
                | "as_str"
                | "substr"
                | "read"
        );
        let owning_field = read_only
            && matches!(receiver.kind, ast::ExprKind::Field { .. })
            && self.is_place(receiver)
            && self.place_type(receiver).is_some_and(|ty| {
                matches!(ty, Type::Vec(_) | Type::Bytes | Type::String | Type::Box(_))
            });
        // A mutating Vec builtin on a field (`m.log.push(x)`) updates the
        // field in place through `&mut m.log`, instead of consuming it.
        let mutated_field = matches!(name, "push" | "set" | "clear" | "reserve" | "replace")
            && matches!(receiver.kind, ast::ExprKind::Field { .. })
            && self.is_place(receiver)
            && self
                .place_type(receiver)
                .is_some_and(|ty| matches!(ty, Type::Vec(_)));
        let first = if owning_field {
            self.container_receiver(receiver, false)?
        } else if mutated_field {
            if self.place_min_length(receiver).is_some() {
                if name == "clear" {
                    return Err(Diagnostic::new(
                        span,
                        "this field keeps 'len >= N'; clearing it would break that",
                    ));
                }
                // push, set and reserve cannot shorten the vector; replace
                // checks the incoming vector's length.
                self.writing_bounded_field = true;
                if name == "replace" {
                    self.replace_min_length = self.place_min_length(receiver);
                }
            }
            let first = self.container_receiver(receiver, true);
            self.writing_bounded_field = false;
            first?
        } else {
            if matches!(receiver.kind, ast::ExprKind::Name(_))
                && let Some(length) = self.place_min_length(receiver)
            {
                match name {
                    "clear" => {
                        return Err(Diagnostic::new(
                            span,
                            "this parameter keeps 'len >= N'; clearing it would break that",
                        ));
                    }
                    "replace" => self.replace_min_length = Some(length),
                    _ => {}
                }
                self.refined_use_ok = true;
            }
            let first = self.expr(receiver);
            self.refined_use_ok = false;
            first?
        };
        if first.ty == Type::Never {
            return Ok(first);
        }
        let ty = first.ty;
        let integer_method = ty.int_kind().is_some()
            && matches!(
                name,
                "convert"
                    | "try_convert"
                    | "truncate"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "wrapping_mul"
                    | "saturating_add"
                    | "saturating_sub"
                    | "saturating_mul"
                    | "checked_add"
                    | "checked_sub"
                    | "checked_mul"
            );
        let float_method = ty.float_kind().is_some()
            && matches!(
                name,
                "abs"
                    | "sqrt"
                    | "is_nan"
                    | "is_infinite"
                    | "is_finite"
                    | "to_f64"
                    | "try_to_f32"
                    | "try_to_int"
            );
        if explicit.is_some() && !integer_method && !float_method {
            return Err(Diagnostic::new(
                span,
                format!("builtin method '{name}' takes no type arguments"),
            ));
        }
        let unsupported = |c: &Self| {
            Diagnostic::new(
                span,
                format!(
                    "no supported builtin method '{name}' for {}; this name is reserved for builtin dispatch, so choose a non-reserved name for a user-defined method",
                    c.types.name(ty)
                ),
            )
        };
        // Scalar/text/box receiver forms.
        if ty.int_kind().is_some()
            && matches!(
                name,
                "convert"
                    | "try_convert"
                    | "truncate"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "wrapping_mul"
                    | "saturating_add"
                    | "saturating_sub"
                    | "saturating_mul"
                    | "checked_add"
                    | "checked_sub"
                    | "checked_mul"
            )
        {
            let canonical = format!("Int.{name}");
            return self.int_call_with(
                Some(first),
                &canonical,
                explicit,
                arguments,
                expected,
                span,
            );
        }
        if name == "code" && ty == Type::Char {
            return self.int_call_with(
                Some(first),
                "Char.code",
                explicit,
                arguments,
                expected,
                span,
            );
        }
        if ty.float_kind().is_some() && float_method {
            let canonical = format!("Float.{name}");
            return self.float_call_with(
                Some(first),
                &canonical,
                explicit,
                arguments,
                expected,
                span,
            );
        }
        if name == "take" && matches!(ty, Type::Box(_)) {
            if explicit.is_some() || !arguments.is_empty() {
                return Err(Diagnostic::new(span, "Box.take takes no arguments"));
            }
            let Type::Box(index) = ty else { unreachable!() };
            let result = self.types.pointees[index];
            return Ok(Expr {
                kind: ExprKind::BoxTake(Box::new(first)),
                ty: result,
                span,
                resource: None,
            });
        }
        if name == "read" && matches!(ty, Type::Box(_) | Type::Ref(_)) {
            if explicit.is_some() || !arguments.is_empty() {
                return Err(Diagnostic::new(span, "Box.read takes no arguments"));
            }
            let first = self.method_borrow(first)?;
            let Type::Ref(pointer) = first.ty else {
                unreachable!()
            };
            let Type::Box(index) = self.types.pointees[pointer] else {
                return Err(unsupported(self));
            };
            let result = self.types.pointees[index];
            return Ok(Expr {
                kind: ExprKind::BoxRead(Box::new(first)),
                ty: result,
                span,
                resource: None,
            });
        }
        // Collection and text methods dispatch on the receiver type.
        let pointee = |c: &Self, ty: Type| match ty {
            Type::Ref(p) | Type::RefMut(p) => Some(c.types.pointees[p]),
            other => Some(other),
        };
        let base = pointee(self, ty);
        if name == "len" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Len, first, arguments, expected, span);
        }
        if name == "capacity" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Capacity, first, arguments, expected, span);
        }
        if name == "get" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Get, first, arguments, expected, span);
        }
        if name == "copy" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Copy, first, arguments, expected, span);
        }
        if name == "push" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Push, first, arguments, expected, span);
        }
        if name == "push_reserved" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::PushReserved, first, arguments, expected, span);
        }
        if name == "clear" && matches!(base, Some(Type::Bytes)) {
            return self.bytes_method(BytesOp::Clear, first, arguments, expected, span);
        }
        if name == "from_utf8" && matches!(base, Some(Type::Bytes)) {
            return self.string_call_with("String.from_utf8", first, arguments, expected, span);
        }
        if name == "at" && matches!(base, Some(Type::Bytes)) {
            let first = self.method_borrow(first)?;
            return self.vec_call_with("Bytes.at", first, arguments, expected, span);
        }
        if matches!(base, Some(Type::Slice(_)) | Some(Type::SliceMut(_))) {
            let method = match name {
                "len" | "get" | "try_get" | "at" | "set" => name,
                _ => return Err(unsupported(self)),
            };
            return self.slice_call_with(
                &format!("Slice.{method}"),
                first,
                arguments,
                expected,
                span,
            );
        }
        if matches!(base, Some(Type::Vec(_))) {
            let (method, borrow) = match name {
                "len" | "get" | "at" => (name, true),
                "clear" | "push" | "reserve" | "try_reserve" | "set" | "replace" => (name, false),
                _ => return Err(unsupported(self)),
            };
            let first = if borrow {
                self.method_borrow(first)?
            } else {
                first
            };
            return self.vec_call_with(&format!("Vec.{method}"), first, arguments, expected, span);
        }
        if matches!(base, Some(Type::String)) {
            if name == "as_mut_str" {
                // `s.as_mut_str()` auto-borrows a direct `let mut` String
                // local exclusively, exactly as `&mut s`.
                let first = match first.kind {
                    ExprKind::Local(slot) => self.borrow_local(slot, true, first.span)?,
                    _ => first,
                };
                return self.string_call_with(
                    "String.as_mut_str",
                    first,
                    arguments,
                    expected,
                    span,
                );
            }
            let (method, borrow) = match name {
                "len" | "scalar_len" | "byte_at" | "scalar_at" | "as_bytes" | "as_str"
                | "substr" => (name, true),
                "bytes" => (name, false),
                _ => return Err(unsupported(self)),
            };
            let first = if borrow {
                self.method_borrow(first)?
            } else {
                first
            };
            return self.string_call_with(
                &format!("String.{method}"),
                first,
                arguments,
                expected,
                span,
            );
        }
        if matches!(base, Some(Type::Str | Type::StrMut)) {
            let method = match name {
                "len"
                | "scalar_len"
                | "byte_at"
                | "scalar_at"
                | "to_string"
                | "substr"
                | "make_ascii_uppercase"
                | "make_ascii_lowercase"
                | "set_scalar" => name,
                _ => return Err(unsupported(self)),
            };
            return self.str_call_with(&format!("Str.{method}"), first, arguments, expected, span);
        }
        Err(unsupported(self))
    }
    /// The field `name` of a record type, as a word offset and field type.
    pub(super) fn record_field_of_type(&self, ty: Type, name: &str) -> Option<(usize, Type)> {
        let id = ty.layout().filter(|id| self.types.enums[*id].record)?;
        let variant = &self.types.enums[id].variants[0];
        let index = variant.names.iter().position(|field| field == name)?;
        let offset = self.types.enums[id].tag_words()
            + variant.fields[..index]
                .iter()
                .map(|field| self.types.width(*field))
                .sum::<usize>();
        Some((offset, variant.fields[index]))
    }
    /// Drain hidden temporary-owner statements created while checking the
    /// current statement into the list that owns their lexical scope.
    pub(super) fn drain_hoisted(&mut self, base: usize, out: &mut Vec<Statement>) {
        out.extend(self.hoisted.drain(base..));
    }
    /// Declare hidden storage for a temporary owner so a checked reference can
    /// point at a real address. Only the declaration is hoisted into the
    /// enclosing statement list: its initializer runs at the expression's
    /// source position through `ExprKind::InitOwner`/`BorrowInit`. The hidden
    /// binding owns the value exactly once and its resource drops at the end
    /// of the block that contains the reference, after the reference's checked
    /// last use; an uninitialized declaration cleans up as a no-op.
    pub(super) fn hoist_owner(&mut self, ty: Type, mutable: bool, span: Span) -> Result<usize> {
        let slot = self.fresh_local(span, ty)?;
        self.locals[slot].mutable = mutable;
        self.locals[slot].pinned = true;
        self.hoisted.push(Statement::Declare(slot));
        Ok(slot)
    }
    /// Check a whole-local borrow. Records, trait objects, and owning handles
    /// use the existing call-scoped semantics; scalar, array, and enum places
    /// borrow their stack storage directly. Any borrowed local is pinned so
    /// the native backend gives the reference a stable address.
    pub(super) fn borrow_local(&mut self, slot: usize, mutable: bool, span: Span) -> Result<Expr> {
        // Writes through an exclusive borrow are invisible to the facts.
        if mutable {
            self.facts.make_opaque(slot);
        }
        let ty = self.locals[slot].ty;
        if ty.is_ref() {
            return Err(Diagnostic::new(
                span,
                "nested references are not supported; pass the reference binding itself, or use '&*p' / '&mut *p' to reborrow",
            ));
        }
        if ty.is_view() {
            return Err(Diagnostic::new(
                span,
                "a borrowed view is already a reference-like capability; pass it directly, or derive a subview with '&name[start..end]'",
            ));
        }
        if matches!(
            ty,
            Type::Task(_) | Type::Thread(_) | Type::Fn(_) | Type::Once(_) | Type::Multi(_)
        ) {
            return Err(Diagnostic::new(
                span,
                "this value has no checked reference form; task handles, function pointers, and closures are passed or consumed directly",
            ));
        }
        if mutable && !self.locals[slot].mutable {
            return Err(Diagnostic::new(
                span,
                "cannot mutably borrow an immutable binding; declare it with let mut",
            ));
        }
        let record = ty.layout().is_some_and(|id| self.types.enums[id].record);
        let object = matches!(ty, Type::DynObj(_))
            || (matches!(ty, Type::Union(_)) && self.functions.object_traits.contains_key(&ty));
        let owner = matches!(
            ty,
            Type::Box(_)
                | Type::Arena
                | Type::ArenaBox(_)
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
        );
        if mutable
            && !record
            && !object
            && !owner
            && ty.layout().is_none()
            && ty.scalar_carrier().is_none()
            && !matches!(ty, Type::Int(_) | Type::Float(_) | Type::Char)
        {
            return Err(Diagnostic::new(
                span,
                "mutable place borrows support scalar, array, record, trait-object, Box<T>, Arena, ArenaBox<T>, Bytes, String, and Vec<T> storage",
            ));
        }
        self.locals[slot].pinned = true;
        Ok(Expr {
            kind: ExprKind::Borrow(slot),
            ty: if mutable {
                Type::RefMut(self.types.pointer(ty))
            } else {
                Type::Ref(self.types.pointer(ty))
            },
            span,
            resource: None,
        })
    }
    /// Build a checked place expression rooted at a local binding, a stored
    /// reference, or hidden temporary storage. The result is not evaluated as
    /// a value; it denotes storage.
    pub(super) fn checked_place(&mut self, expr: &ast::Expr, mutable: bool) -> Result<Expr> {
        match &expr.kind {
            ast::ExprKind::Name(name) if name != "_" => {
                let slot = self.slot(expr.span)?;
                Ok(Expr {
                    kind: ExprKind::Peek(slot),
                    ty: self.locals[slot].ty,
                    span: expr.span,
                    resource: None,
                })
            }
            ast::ExprKind::Field { value, name }
                if self.resolution.reference(expr.span).is_none() =>
            {
                let base = self.checked_place(value, mutable)?;
                let (offset, ty) = if base.ty.is_ref() {
                    let Some(pointer) = base.ty.ref_pointee() else {
                        return Err(Diagnostic::new(expr.span, "invalid reference pointee"));
                    };
                    let pointee = self.types.pointees[pointer];
                    let Some(id) = pointee.layout().filter(|id| self.types.enums[*id].record)
                    else {
                        return Err(Diagnostic::new(
                            expr.span,
                            "field access requires a nominal record",
                        ));
                    };
                    self.check_layout_field_visible(id, name, expr.span)?;
                    let variant = &self.types.enums[id].variants[0];
                    let Some(index) = variant.names.iter().position(|field| field == name) else {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!("no field named '{name}'"),
                        ));
                    };
                    let offset = self.types.enums[id].tag_words()
                        + variant.fields[..index]
                            .iter()
                            .map(|field| self.types.width(*field))
                            .sum::<usize>();
                    (offset, variant.fields[index])
                } else {
                    let base_ty = base.ty;
                    if base_ty.layout().is_none() {
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "field access requires a record value, found {}",
                                self.types.name(base_ty)
                            ),
                        ));
                    }
                    self.record_offset(base_ty, name, expr.span)?
                };
                Ok(Expr {
                    kind: ExprKind::Project(Box::new(base), offset),
                    ty,
                    span: expr.span,
                    resource: None,
                })
            }
            ast::ExprKind::Index { value, index } => {
                let base = self.checked_place(value, mutable)?;
                if base.ty.is_text() {
                    return Err(Diagnostic::new(
                        expr.span,
                        "a &str view is not indexed by a single index; use Str.byte_at or Str.scalar_at",
                    ));
                }
                let element = if let Some(pointer) = base.ty.slice_element() {
                    // `&s[i]` / `&mut s[i]` address one element of a slice
                    // view. The view is a capability over its owners, so the
                    // element reference narrows that capability; the bound
                    // (and a byte-backed view) is checked at creation.
                    if mutable && !base.ty.is_mut_slice() {
                        return Err(Diagnostic::new(
                            expr.span,
                            "cannot create an exclusive element reference from a shared '&[T]' view; shared storage cannot be upgraded",
                        ));
                    }
                    let element = self.types.pointees[pointer];
                    if element.is_view() || element.is_ref() {
                        return Err(Diagnostic::new(
                            expr.span,
                            "an element reference would alias a borrowed view or reference; read the element by value instead",
                        ));
                    }
                    self.require(PANIC, expr.span)?;
                    let index = self.expr_expected(index, Some(Type::I64))?;
                    self.expect(index.ty, Type::I64, index.span)?;
                    if self.owned_type(element) || self.linear_type(element) {
                        return Err(Diagnostic::new(
                            expr.span,
                            "an index reference would alias an owning or linear element; move the element out with Vec.pop/Box.take or borrow a non-owning element",
                        ));
                    }
                    let id = self.index_place_id(&base, &index);
                    return Ok(Expr {
                        kind: ExprKind::PlaceIndex {
                            base: Box::new(base),
                            index: Box::new(index),
                            id,
                        },
                        ty: element,
                        span: expr.span,
                        resource: None,
                    });
                } else if let Type::Vec(pointer) = base.ty {
                    self.types.pointees[pointer]
                } else if let Some((element, _)) =
                    base.ty.layout().and_then(|id| self.types.enums[id].array)
                {
                    element
                } else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "index places require an inline array or Vec<T> storage; slice views are indexed by value, not by address",
                    ));
                };
                if self.owned_type(element) || self.linear_type(element) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "an index reference would alias an owning or linear element; move the element out with Vec.pop/Box.take or borrow a non-owning element",
                    ));
                }
                // A compile-time index into an inline array is proved once at
                // check time; otherwise the place carries a panicking bound.
                let mut proven = false;
                if let Some((_, length)) =
                    base.ty.layout().and_then(|id| self.types.enums[id].array)
                    && let Some(position) = crate::length::eval_expr(
                        self.resolution,
                        self.logical,
                        &self.consts,
                        index,
                    )?
                {
                    if position >= length {
                        return Err(Diagnostic::new(index.span, "array index out of bounds"));
                    }
                    proven = true;
                }
                if !proven {
                    self.require(PANIC, expr.span)?;
                }
                let index = self.expr_expected(index, Some(Type::I64))?;
                self.expect(index.ty, Type::I64, index.span)?;
                let id = self.index_place_id(&base, &index);
                Ok(Expr {
                    kind: ExprKind::PlaceIndex {
                        base: Box::new(base),
                        index: Box::new(index),
                        id,
                    },
                    ty: element,
                    span: expr.span,
                    resource: None,
                })
            }
            _ => {
                // A call result or literal has no stable storage yet. Hoist it
                // into a hidden owning local so the reference points at a real
                // address with checked cleanup.
                let value = self.expr_expected(expr, None)?;
                if value.ty.is_view() || value.ty == Type::Str || value.ty == Type::Never {
                    return Err(Diagnostic::new(
                        expr.span,
                        "this value has no addressable storage to borrow",
                    ));
                }
                let ty = value.ty;
                let slot = self.hoist_owner(ty, mutable, expr.span)?;
                Ok(Expr {
                    kind: ExprKind::InitOwner {
                        slot,
                        value: Box::new(value),
                    },
                    ty,
                    span: expr.span,
                    resource: None,
                })
            }
        }
    }
    /// Give a new index place its identity and record which earlier index
    /// places of the same root binding provably hold a different index here.
    /// The facts are those at this (the later) place; the earlier index is a
    /// versioned term, so a relation never depends on a stale value. Only a
    /// proved disequality is recorded; nothing is assumed.
    pub(super) fn index_place_id(&mut self, base: &Expr, index: &Expr) -> usize {
        fn root(place: &Expr) -> Option<usize> {
            match &place.kind {
                ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => Some(*slot),
                ExprKind::Project(base, _) | ExprKind::PlaceIndex { base, .. } => root(base),
                ExprKind::Coerce { value, .. } => root(value),
                _ => None,
            }
        }
        self.next_index_place += 1;
        let id = self.next_index_place;
        if let (Some(root), Some(linear)) = (root(base), self.facts.linear(index)) {
            for earlier in self.facts.distinct_index_places(root, &linear) {
                self.index_relations.insert((earlier, id));
            }
            self.facts.record_index_place(id, root, linear);
        }
        id
    }
    /// The mutability of the capability that owns a checked place.
    pub(super) fn place_mutable(&self, place: &Expr) -> bool {
        match &place.kind {
            ExprKind::Peek(slot) | ExprKind::Local(slot) | ExprKind::Move(slot) => match place.ty {
                Type::Ref(_) | Type::Slice(_) => false,
                Type::RefMut(_) | Type::SliceMut(_) => true,
                _ => self.locals[*slot].mutable,
            },
            ExprKind::Project(base, _) => self.place_mutable(base),
            ExprKind::PlaceIndex { base, .. } => self.place_mutable(base),
            ExprKind::Coerce { value, .. } => self.place_mutable(value),
            _ => false,
        }
    }
    /// Borrow a field chain or index place. The resulting reference aliases
    /// the root owner's storage; the ownership pass keeps the root and every
    /// ancestor capability loaned until the reference's last use.
    pub(super) fn borrow_place_expr(
        &mut self,
        operand: &ast::Expr,
        mutable: bool,
        span: Span,
    ) -> Result<Expr> {
        let place = self.checked_place(operand, mutable)?;
        if mutable && let Some(root) = place_root_slot(&place) {
            self.facts.make_opaque(root);
        }
        let ty = place.ty;
        if ty.is_view() || ty == Type::Str || ty.is_ref() {
            return Err(Diagnostic::new(
                span,
                "this place holds a borrowed view or reference; pass it directly, or use '&record.view[..]' for a subview",
            ));
        }
        if matches!(
            ty,
            Type::Arena
                | Type::ArenaBox(_)
                | Type::Allocator
                | Type::Task(_)
                | Type::Thread(_)
                | Type::DynObj(_)
                | Type::Union(_)
                | Type::Fn(_)
                | Type::Once(_)
                | Type::Multi(_)
        ) {
            return Err(Diagnostic::new(
                span,
                "this field type has no checked addressable place form; bind the value, use a direct local borrow, or use its container/receiver operation",
            ));
        }
        if mutable
            && matches!(
                ty,
                Type::AllocBox(_) | Type::AllocVec(_) | Type::AllocatorContext
            )
        {
            return Err(Diagnostic::new(
                span,
                "allocator-owned handles support shared place references; mutate their contents with their checked container operations",
            ));
        }
        if mutable && !self.place_mutable(&place) {
            return Err(Diagnostic::new(
                span,
                "cannot mutably borrow a place through an immutable binding or a shared reference; declare the owner with 'let mut' or use '&mut'",
            ));
        }
        let pointer = self.types.pointer(ty);
        Ok(Expr {
            kind: ExprKind::BorrowPlace(Box::new(place)),
            ty: if mutable {
                Type::RefMut(pointer)
            } else {
                Type::Ref(pointer)
            },
            span,
            resource: None,
        })
    }
    /// Consuming dispatch on a projected object field, `root.a.b.method()`.
    /// The root aggregate is consumed exactly as a destructuring pattern
    /// would consume it: every level of the path is matched into hidden
    /// bindings, the selected field moves into the receiver, and every sibling
    /// field is released when the call's scope ends. A linear sibling cannot
    /// be released implicitly, and a field behind a reference cannot be moved
    /// at all. Returns the receiver (a hidden binding) and the match levels
    /// that `wrap_consumed_field` puts around the call.
    pub(super) fn consume_object_field(
        &mut self,
        place: Expr,
        span: Span,
    ) -> Result<(Expr, Vec<ConsumedLevel>)> {
        let mut path = Vec::new();
        let mut current = &place;
        let root = loop {
            match &current.kind {
                ExprKind::Project(base, offset) => {
                    path.push((*offset, base.ty));
                    current = base;
                }
                ExprKind::Peek(slot) | ExprKind::Local(slot) if !current.ty.is_ref() => {
                    break *slot;
                }
                _ => {
                    return Err(Diagnostic::new(
                        place.span,
                        "cannot move a trait object out of a field behind a reference; call a borrowed method, or move the owning aggregate itself",
                    ));
                }
            }
        };
        path.reverse();
        let mut levels = Vec::new();
        let mut scrutinee = root;
        for (offset, container) in path {
            let Some(layout) = container.layout().filter(|id| self.types.enums[*id].record) else {
                return Err(Diagnostic::new(
                    place.span,
                    "internal error: projected object field has no record layout",
                ));
            };
            let variant = self.types.enums[layout].variants[0].clone();
            let mut field_offset = self.types.enums[layout].tag_words();
            let mut fields = Vec::new();
            let mut selected = None;
            for (index, field_ty) in variant.fields.iter().enumerate() {
                if field_offset != offset && self.linear_type(*field_ty) {
                    let name = variant
                        .names
                        .get(index)
                        .cloned()
                        .unwrap_or_else(|| index.to_string());
                    return Err(Diagnostic::new(
                        place.span,
                        format!(
                            "consuming dispatch on a projected field releases its sibling fields, but field '{name}' of {} is linear; destructure the aggregate and consume that field",
                            self.types.name(container)
                        ),
                    ));
                }
                let slot = self.temp(*field_ty, span)?;
                if field_offset == offset {
                    selected = Some(slot);
                }
                fields.push((field_offset, Pattern::Bind(slot)));
                field_offset += self.types.width(*field_ty);
            }
            let Some(selected) = selected else {
                return Err(Diagnostic::new(
                    place.span,
                    "internal error: projected object field offset is not a field boundary",
                ));
            };
            levels.push((
                scrutinee,
                container,
                Pattern::Variant {
                    tag: 0,
                    tagged: self.types.enums[layout].tag_words() != 0,
                    niche: self.types.enums[layout].niche(),
                    fields,
                },
            ));
            scrutinee = selected;
        }
        Ok((
            Expr {
                kind: ExprKind::Local(scrutinee),
                ty: place.ty,
                span: place.span,
                resource: None,
            },
            levels,
        ))
    }
    /// The checked storage place of a trait object stored in a field chain
    /// `root.a.b`, rooted at a local aggregate or a stored record reference.
    /// `None` for anything else (including a non-object field), so the caller
    /// keeps its ordinary receiver path and diagnostics.
    pub(super) fn object_field_place(&mut self, expr: &ast::Expr) -> Option<Expr> {
        if !matches!(expr.kind, ast::ExprKind::Field { .. }) || !self.is_place(expr) {
            return None;
        }
        let place = self.checked_place(expr, false).ok()?;
        self.is_object_type(place.ty).then_some(place)
    }
    /// Whether `ty` is a trait object in either representation.
    pub(super) fn is_object_type(&self, ty: Type) -> bool {
        matches!(ty, Type::DynObj(_))
            || (matches!(ty, Type::Union(_)) && self.functions.object_traits.contains_key(&ty))
    }
    /// A checked reference to a projected trait-object field for in-place
    /// dispatch. Exclusive dispatch needs a mutable owner capability, exactly
    /// like `&mut root.field`.
    pub(super) fn borrow_object_field(
        &mut self,
        place: Expr,
        mutable: bool,
        span: Span,
    ) -> Result<Expr> {
        if mutable && !self.place_mutable(&place) {
            return Err(Diagnostic::new(
                span,
                "a mutable dynamic method on a field needs a mutable owner; declare the owner with 'let mut' or reach it through '&mut'",
            ));
        }
        let pointer = self.types.pointer(place.ty);
        Ok(Expr {
            kind: ExprKind::BorrowPlace(Box::new(place)),
            ty: if mutable {
                Type::RefMut(pointer)
            } else {
                Type::Ref(pointer)
            },
            span,
            resource: None,
        })
    }
    /// Whether an expression is a pure place: a local name or a field chain
    /// rooted at one. Such receivers use the same non-moving read path as
    /// ordinary field projection.
    pub(super) fn is_place(&self, expr: &ast::Expr) -> bool {
        match &expr.kind {
            ast::ExprKind::Name(name) if name != "_" => self.slot(expr.span).is_ok(),
            ast::ExprKind::Field { value, .. }
                if self.resolution.reference(expr.span).is_none() =>
            {
                self.is_place(value)
            }
            _ => false,
        }
    }
    /// Recognize `receiver.Trait.method` and the generic-trait spelling
    /// `receiver.Trait::<Arguments>.method` as explicitly qualified static
    /// dispatch. The resolver recorded the trait binding on the
    /// `receiver.Trait` selector node.
    pub(super) fn qualified_method<'x>(
        &self,
        target: &'x ast::Expr,
    ) -> Option<(&'x ast::Expr, &'x str, BindingId, Option<&'x [ast::Type]>)> {
        let ast::ExprKind::Field { value, name } = &target.kind else {
            return None;
        };
        match &value.kind {
            ast::ExprKind::Field {
                value: receiver, ..
            } => {
                let id = self.resolution.reference(value.span)?;
                (self.resolution.bindings[id].kind == BindingKind::Trait).then_some((
                    receiver.as_ref(),
                    name.as_str(),
                    id,
                    None,
                ))
            }
            ast::ExprKind::Specialize { callee, arguments } => {
                let ast::ExprKind::Field {
                    value: receiver, ..
                } = &callee.kind
                else {
                    return None;
                };
                let id = self.resolution.reference(callee.span)?;
                (self.resolution.bindings[id].kind == BindingKind::Trait).then_some((
                    receiver.as_ref(),
                    name.as_str(),
                    id,
                    Some(arguments.as_slice()),
                ))
            }
            _ => None,
        }
    }
    /// Resolve one explicitly supplied trait specialization at the call site.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn call_site_trait_arguments(
        &mut self,
        trait_id: BindingId,
        explicit: Option<&[ast::Type]>,
        span: Span,
    ) -> Result<TraitArguments> {
        let definition = self.functions.traits[&trait_id].clone();
        let trait_name = self.resolution.bindings[trait_id].name.clone();
        if definition.generics.is_empty() {
            if explicit.is_some_and(|explicit| !explicit.is_empty()) {
                return Err(Diagnostic::new(
                    span,
                    format!("trait '{trait_name}' takes no type arguments"),
                ));
            }
            return Ok(TraitArguments::default());
        }
        let Some(explicit) = explicit else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "trait '{trait_name}' is generic; qualify the call with its arguments, as in 'receiver.{trait_name}::<...>.method(...)'"
                ),
            ));
        };
        let substitution = crate::runtime_types::Subst {
            types: self.substitution.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effect_arguments.clone(),
            lifetimes: BTreeMap::new(),
            self_type: self.self_type,
            associated_types: BTreeMap::new(),
            projections: BTreeMap::new(),
            self_projections: BTreeMap::new(),
            lengths: BTreeMap::new(),
        };
        evaluate_trait_arguments(
            self.types,
            self.resolution,
            self.logical,
            &definition.generics,
            explicit,
            &substitution,
            &trait_name,
            span,
        )
    }
    pub(super) fn lookup_method(
        &mut self,
        ty: Type,
        name: &str,
        trait_id: Option<(BindingId, TraitArguments)>,
        span: Span,
    ) -> Result<MethodDefinition> {
        let key = ty.full();
        if let Some((trait_id, trait_arguments)) = trait_id {
            let definition = self.functions.traits[&trait_id].clone();
            let trait_name = self.resolution.bindings[trait_id].name.clone();
            let specialization = if definition.generics.is_empty() {
                trait_name.clone()
            } else {
                format!(
                    "{trait_name}<{}>",
                    trait_specialization_name(
                        self.resolution,
                        self.types,
                        &definition.generics,
                        &trait_arguments
                    )
                )
            };
            if let Some(methods) =
                self.functions
                    .trait_impls
                    .get(&(trait_id, trait_arguments.clone(), key))
            {
                return methods.get(name).copied().ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!("trait '{specialization}' has no method '{name}'"),
                    )
                });
            }
            let mut matches = self.functions.matching_impls(
                self.types,
                self.resolution,
                trait_id,
                &trait_arguments,
                key,
                0,
            )?;
            matches.retain(|candidate| {
                self.functions.impl_headers[candidate.header]
                    .methods
                    .contains_key(name)
            });
            let selected = self
                .functions
                .select_most_specific(self.resolution, &matches);
            let Some(selected) = selected else {
                if matches.is_empty() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "type '{}' does not implement trait '{specialization}'",
                            self.types.name(ty)
                        ),
                    ));
                }
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "method '{name}' on '{}' has several incomparable generic impls; coherence requires a unique most-specific impl",
                        self.types.name(ty)
                    ),
                ));
            };
            let index = self.functions.intern_impl(
                self.types,
                self.resolution,
                selected.header,
                selected.arguments,
            )?;
            let mut definition = *self.functions.impl_headers[selected.header]
                .methods
                .get(name)
                .expect("candidate was filtered by method name");
            definition.impl_arguments = Some(index);
            return Ok(definition);
        }
        if let Some(definition) = self
            .functions
            .inherent
            .get(&key)
            .and_then(|methods| methods.get(name))
        {
            return Ok(*definition);
        }
        // Generic inherent impls apply only when no exact inherent method
        // exists; a concrete `impl Type` is always more specific.
        if let Some(generic) = self.generic_method_candidates(key, name, None, span)? {
            return Ok(generic);
        }
        let mut candidates = self
            .functions
            .methods_by_type
            .get(&key)
            .and_then(|methods| methods.get(name))
            .cloned()
            .unwrap_or_default();
        candidates.sort_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        // Inside a materialized default body, an unqualified call on `Self`
        // prefers the enclosing trait specialization (the enclosing trait
        // itself when it is not generic). Without this, a generic trait
        // implemented at several specializations could not call its own
        // sibling methods from a default body without redundant qualification.
        if candidates.len() > 1
            && self
                .self_type
                .is_some_and(|self_type| self_type.full() == key)
            && let Some((enclosing_trait, enclosing_arguments)) = &self.default_trait
        {
            let matching = candidates
                .iter()
                .filter(|(trait_id, arguments, _)| {
                    trait_id == enclosing_trait && arguments == enclosing_arguments
                })
                .cloned()
                .collect::<Vec<_>>();
            if let [single] = matching.as_slice() {
                return Ok(single.2);
            }
        }
        // Add applicable generic impls for every trait. Per trait, the unique
        // most-specific header wins; a concrete impl of the same trait and
        // arguments still supersedes a generic one.
        let mut generic_by_trait: BTreeMap<BindingId, Vec<ImplMatch>> = BTreeMap::new();
        for header_index in 0..self.functions.impl_headers.len() {
            let Some(trait_id) = self.functions.impl_headers[header_index].trait_id else {
                continue;
            };
            if self.functions.impl_headers[header_index].concrete.is_some()
                || !self.functions.impl_headers[header_index]
                    .methods
                    .contains_key(name)
            {
                continue;
            }
            if let Some(candidate) = self.functions.match_header_for_receiver(
                self.types,
                self.resolution,
                header_index,
                key,
                0,
            )? {
                generic_by_trait
                    .entry(trait_id)
                    .or_default()
                    .push(candidate);
            }
        }
        let mut generic_candidates = Vec::new();
        for (trait_id, matches) in generic_by_trait {
            let Some(selected) = self
                .functions
                .select_most_specific(self.resolution, &matches)
            else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "method '{name}' on '{}' has several incomparable generic impls of trait '{}'",
                        self.types.name(ty),
                        self.resolution.bindings[trait_id].name
                    ),
                ));
            };
            let required = self.functions.trait_arguments_for_match(
                self.types,
                self.resolution,
                selected.header,
                &selected.arguments,
            )?;
            if self
                .functions
                .trait_impls
                .contains_key(&(trait_id, required.clone(), key))
            {
                continue;
            }
            if !self.functions.impl_headers[selected.header]
                .methods
                .contains_key(name)
            {
                continue;
            }
            let index = self.functions.intern_impl(
                self.types,
                self.resolution,
                selected.header,
                selected.arguments,
            )?;
            let mut definition = *self.functions.impl_headers[selected.header]
                .methods
                .get(name)
                .expect("filtered by method name");
            definition.impl_arguments = Some(index);
            generic_candidates.push((trait_id, required, definition));
        }
        // Deduplicate identical (trait, arguments) generic candidates that can
        // arise when several specializations of the same trait match.
        generic_candidates.sort_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        generic_candidates.dedup_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        candidates.extend(generic_candidates);
        candidates.sort_by_key(|(trait_id, arguments, _)| (*trait_id, arguments.clone()));
        match candidates.as_slice() {
            [] => Err(Diagnostic::new(
                span,
                format!(
                    "no method '{name}' for '{}'; define an inherent method, implement a trait, or check the receiver type",
                    self.types.name(ty)
                ),
            )),
            [single] => Ok(single.2),
            many => {
                let traits = many
                    .iter()
                    .map(|(trait_id, arguments, _)| {
                        let def = &self.functions.traits[trait_id];
                        if def.generics.is_empty() {
                            self.resolution.bindings[*trait_id].name.clone()
                        } else {
                            format!(
                                "{}<{}>",
                                self.resolution.bindings[*trait_id].name,
                                trait_specialization_name(
                                    self.resolution,
                                    self.types,
                                    &def.generics,
                                    arguments
                                )
                            )
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                Err(Diagnostic::new(
                    span,
                    format!(
                        "method '{name}' on '{}' is ambiguous: it is provided by traits {traits}. Disambiguate as 'receiver.Trait.method(...)' or 'receiver.Trait::<...>.method(...)' for a generic trait",
                        self.types.name(ty)
                    ),
                ))
            }
        }
    }
    /// Generic inherent method lookup. Returns `None` when no generic inherent
    /// impl matches; several incomparable matches are an ambiguity error.
    pub(super) fn generic_method_candidates(
        &mut self,
        key: Type,
        name: &str,
        trait_id: Option<BindingId>,
        span: Span,
    ) -> Result<Option<MethodDefinition>> {
        let mut matches = Vec::new();
        for (header_index, header) in self.functions.impl_headers.iter().enumerate() {
            if header.trait_id != trait_id
                || header.concrete.is_some()
                || !header.methods.contains_key(name)
            {
                continue;
            }
            if trait_id.is_some() {
                continue;
            }
            if let Some(candidate) = self.functions.match_header_for_receiver(
                self.types,
                self.resolution,
                header_index,
                key,
                0,
            )? {
                matches.push(candidate);
            }
        }
        if matches.is_empty() {
            return Ok(None);
        }
        let selected = self
            .functions
            .select_most_specific(self.resolution, &matches);
        let Some(selected) = selected else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "inherent method '{name}' on '{}' has several incomparable generic impls",
                    self.types.name(key)
                ),
            ));
        };
        let index = self.functions.intern_impl(
            self.types,
            self.resolution,
            selected.header,
            selected.arguments,
        )?;
        let mut definition = *self.functions.impl_headers[selected.header]
            .methods
            .get(name)
            .expect("candidate was filtered by method name");
        definition.impl_arguments = Some(index);
        Ok(Some(definition))
    }
    /// Whether this method's declared receiver is `&self` (`Some(false)`) or
    /// `&mut self` (`Some(true)`), or is taken by value (`None`).
    pub(super) fn method_receiver_borrow(&self, binding: BindingId) -> Option<bool> {
        let f = self.functions.declared.get(&binding)?.ast;
        match &f.parameters.first()?.ty.kind {
            ast::TypeKind::Borrow { mutable, .. } => Some(*mutable),
            _ => None,
        }
    }
    pub(super) fn check_method_visibility(
        &self,
        definition: MethodDefinition,
        name: &str,
        span: Span,
    ) -> Result<()> {
        if definition.public || definition.unit == self.unit {
            return Ok(());
        }
        let module = self
            .resolution
            .units
            .get(definition.unit)
            .map(|path| path.join("."))
            .filter(|path| !path.is_empty())
            .unwrap_or_else(|| "<root>".to_owned());
        Err(Diagnostic::new(
            span,
            format!("method '{name}' is private to module '{module}'; mark it 'pub'"),
        ))
    }
    /// Check a user-defined receiver-style call. The receiver is checked
    /// exactly once before the remaining arguments and lowers to the same
    /// `Target::Function` call node as a namespace call.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn user_method_call(
        &mut self,
        receiver_ast: &ast::Expr,
        name: &str,
        trait_id: Option<BindingId>,
        trait_arguments_ast: Option<&[ast::Type]>,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let trait_arguments = match trait_id {
            Some(trait_id) => {
                Some(self.call_site_trait_arguments(trait_id, trait_arguments_ast, span)?)
            }
            None => None,
        };
        let trait_selection = trait_id.zip(trait_arguments);
        // Field projection wins over an unqualified method with the same name.
        // Method declarations that would collide with a record field are
        // rejected when the impl is registered, so this cannot silently make a
        // method unreachable.
        // A trait object stored in a field (of a local aggregate, or behind a
        // stored record reference) is a checked place: dispatch borrows that
        // exact storage instead of reading or copying the field.
        // An owning field (a record that owns storage, reached through a
        // local or a reference) cannot be read as a value. A `&self` or
        // `&mut self` method borrows it in place instead.
        if matches!(receiver_ast.kind, ast::ExprKind::Field { .. })
            && self.is_place(receiver_ast)
            && let Some(field_ty) = self.place_type(receiver_ast)
            && self.owned_type(field_ty)
            && !self.is_object_type(field_ty)
            && field_ty.layout().is_some()
        {
            let definition = self.lookup_method(field_ty, name, trait_selection.clone(), span)?;
            self.check_method_visibility(definition, name, span)?;
            let Some(mutable) = self.method_receiver_borrow(definition.binding) else {
                return Err(Diagnostic::new(
                    receiver_ast.span,
                    "cannot move an owned field into a method receiver; destructure the record or tuple into a local first",
                ));
            };
            let borrow = ast::Expr {
                kind: ast::ExprKind::Unary {
                    op: Kind::Amp,
                    mutable,
                    operand: Box::new(receiver_ast.clone()),
                },
                span: receiver_ast.span,
            };
            let receiver = self.expr(&borrow)?;
            return self.invoke_method(
                definition.binding,
                definition.impl_arguments,
                receiver_ast,
                receiver,
                explicit,
                arguments,
                expected,
                span,
            );
        }
        let mut receiver = if let Some(place) = self.object_field_place(receiver_ast) {
            place
        } else if self.is_place(receiver_ast) {
            self.place(receiver_ast)?
        } else {
            self.expr(receiver_ast)?
        };
        if receiver.ty == Type::Never {
            return Ok(receiver);
        }
        // A projected owning field is still owned by its aggregate. Static
        // consuming or mutable dispatch must not copy it into a temporary
        // receiver. Dynamic shared dispatch is handled below by borrowing the
        // field in place; owning and mutable projected receivers stay rejected.
        let dynamic_object = matches!(receiver.ty, Type::DynObj(_))
            || (matches!(receiver.ty, Type::Union(_))
                && self.functions.object_traits.contains_key(&receiver.ty))
            || receiver.ty.ref_pointee().is_some_and(|pointer| {
                let pointee = self.types.pointees[pointer];
                matches!(pointee, Type::DynObj(_))
                    || (matches!(pointee, Type::Union(_))
                        && self.functions.object_traits.contains_key(&pointee))
            });
        if matches!(receiver.kind, ExprKind::Project(..))
            && self.owned_type(receiver.ty)
            && !dynamic_object
        {
            return Err(Diagnostic::new(
                receiver.span,
                "cannot move an owned field into a method receiver; destructure the record or tuple into a local first",
            ));
        }
        if let Some(pointer) = receiver.ty.ref_pointee() {
            let pointee = self.types.pointees[pointer];
            if matches!(pointee, Type::DynObj(_)) {
                return self.dyn_object_method_call(
                    receiver,
                    name,
                    trait_selection.clone(),
                    explicit,
                    arguments,
                    expected,
                    span,
                );
            }
            if matches!(pointee, Type::Union(_))
                && self.functions.object_traits.contains_key(&pointee)
            {
                return self.dynamic_method_call(
                    receiver,
                    name,
                    trait_selection.clone(),
                    arguments,
                    expected,
                    span,
                );
            }
        }
        if matches!(receiver.ty, Type::DynObj(_)) {
            return self.dyn_object_method_call(
                receiver,
                name,
                trait_selection.clone(),
                explicit,
                arguments,
                expected,
                span,
            );
        }
        if matches!(receiver.ty, Type::Union(_))
            && self.functions.object_traits.contains_key(&receiver.ty)
        {
            return self.dynamic_method_call(
                receiver,
                name,
                trait_selection.clone(),
                arguments,
                expected,
                span,
            );
        }
        let lookup_ty = match receiver.ty.ref_pointee() {
            Some(pointer) if self.types.pointees[pointer].layout().is_some() => {
                self.types.pointees[pointer]
            }
            _ => receiver.ty,
        };
        if trait_id.is_none()
            && !receiver.ty.is_ref()
            && self.record_field_of_type(receiver.ty, name).is_some()
        {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "'{name}' is a callable record field, and field projection takes precedence over method dispatch: a projected field call takes no explicit type arguments"
                    ),
                ));
            }
            let callee = self.project_field(receiver, name, receiver_ast.span, None)?;
            return self.indirect_call_checked(callee, arguments, expected, span);
        }
        let definition = self.lookup_method(lookup_ty, name, trait_selection, span)?;
        self.check_method_visibility(definition, name, span)?;
        if let Some(mutable) = self.method_receiver_borrow(definition.binding) {
            // An existing reference is passed on as the receiver, exactly as
            // it would be passed to an ordinary function: the call reborrows
            // it, and `&mut` serves a `&self` method.
            if receiver.ty.is_ref() {
                if mutable && !matches!(receiver.ty, Type::RefMut(_)) {
                    return Err(Diagnostic::new(
                        receiver_ast.span,
                        "this method takes '&mut self', but the receiver is a shared reference",
                    ));
                }
                if let ExprKind::Peek(slot) = receiver.kind {
                    receiver.kind = ExprKind::Local(slot);
                }
                return self.invoke_method(
                    definition.binding,
                    definition.impl_arguments,
                    receiver_ast,
                    receiver,
                    explicit,
                    arguments,
                    expected,
                    span,
                );
            }
            // A field (or deeper place) of a local or reference is borrowed in
            // place, exactly as an explicit `&place` / `&mut place` would be.
            if !matches!(receiver.kind, ExprKind::Peek(_) | ExprKind::Local(_))
                && self.is_place(receiver_ast)
            {
                let borrow = ast::Expr {
                    kind: ast::ExprKind::Unary {
                        op: Kind::Amp,
                        mutable,
                        operand: Box::new(receiver_ast.clone()),
                    },
                    span: receiver_ast.span,
                };
                let receiver = self.expr(&borrow)?;
                return self.invoke_method(
                    definition.binding,
                    definition.impl_arguments,
                    receiver_ast,
                    receiver,
                    explicit,
                    arguments,
                    expected,
                    span,
                );
            }
            let (ExprKind::Peek(slot) | ExprKind::Local(slot)) = receiver.kind else {
                return Err(Diagnostic::new(
                    receiver_ast.span,
                    "a borrowed method receiver must be a place (a local or one of its fields); bind a temporary to a local first",
                ));
            };
            if mutable {
                if !self.locals[slot].mutable {
                    return Err(Diagnostic::new(
                        receiver_ast.span,
                        "cannot mutably borrow an immutable binding; declare it with let mut",
                    ));
                }
                if lookup_ty
                    .layout()
                    .is_some_and(|id| self.types.enums[id].borrowed)
                {
                    return Err(Diagnostic::new(
                        receiver_ast.span,
                        "cannot mutably borrow a record with borrowed fields; only its owning metadata may be updated through an owning value",
                    ));
                }
            }
            let pointee = self.types.pointer(lookup_ty);
            let ty = if mutable {
                Type::RefMut(pointee)
            } else {
                Type::Ref(pointee)
            };
            receiver = Expr {
                kind: ExprKind::Borrow(slot),
                ty,
                span: receiver_ast.span,
                resource: None,
            };
        } else {
            if receiver.ty.is_ref() {
                return Err(Diagnostic::new(
                    receiver_ast.span,
                    "this method takes its receiver by value, but the receiver is a borrowed reference; call an '&self'/'&mut self' method or pass the owner itself",
                ));
            }
            // A direct local receiver is consumed by an owned method. A Peek
            // was a non-moving read for field detection; switch it to Local so
            // the normal ownership pass sees one move.
            if let ExprKind::Peek(slot) = &receiver.kind {
                let slot = *slot;
                let ty = receiver.ty;
                let receiver_span = receiver.span;
                receiver = Expr {
                    kind: ExprKind::Local(slot),
                    ty,
                    span: receiver_span,
                    resource: None,
                };
            }
        }
        self.invoke_method(
            definition.binding,
            definition.impl_arguments,
            receiver_ast,
            receiver,
            explicit,
            arguments,
            expected,
            span,
        )
    }
    /// Resolve `T.NAME` for a generic parameter `T` with a trait bound. The
    /// concrete constant is selected by the same impl solver used for `T.Out`;
    /// the projection is a compile-time literal for the current specialization.
    pub(super) fn generic_associated_const(
        &mut self,
        binder: BindingId,
        name: &str,
        span: Span,
    ) -> Result<Option<ConstValue>> {
        let Some(declared) = self.functions.declared.get(&self.binding).copied() else {
            return Ok(None);
        };
        let impl_generic = declared.impl_template.and_then(|template| {
            self.functions.impl_headers[template]
                .generics
                .iter()
                .find(|generic| self.resolution.binder(generic.span) == Some(binder))
        });
        let Some(generic) = declared
            .ast
            .generics
            .iter()
            .find(|generic| self.resolution.binder(generic.span) == Some(binder))
            .or(impl_generic)
        else {
            return Ok(None);
        };
        let Some(bound) = &generic.bound else {
            return Ok(None);
        };
        let Some(trait_id) = self.resolution.reference(bound.span) else {
            return Ok(None);
        };
        if self.resolution.bindings[trait_id].kind != BindingKind::Trait {
            return Ok(None);
        }
        let Some(actual) = self.substitution.get(&binder).copied() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot project associated constant '{name}' from an unspecialized generic parameter '{}'",
                    self.resolution.bindings[binder].name
                ),
            ));
        };
        let definition = self.functions.traits[&trait_id].clone();
        let argument_ast = match &bound.kind {
            ast::TypeKind::Named { arguments, .. } => arguments.clone(),
            _ => Vec::new(),
        };
        let substitution = crate::runtime_types::Subst {
            types: self.substitution.clone(),
            consts: self.consts.clone(),
            grades: self.grades.clone(),
            effects: self.effect_arguments.clone(),
            lifetimes: BTreeMap::new(),
            self_type: self.self_type,
            associated_types: BTreeMap::new(),
            projections: BTreeMap::new(),
            self_projections: BTreeMap::new(),
            lengths: BTreeMap::new(),
        };
        let required = evaluate_trait_arguments(
            self.types,
            self.resolution,
            self.functions.logical,
            &definition.generics,
            &argument_ast,
            &substitution,
            &self.resolution.bindings[trait_id].name,
            generic.span,
        )?;
        if let Some(values) = self
            .functions
            .trait_consts
            .get(&(trait_id, required.clone(), actual))
        {
            return Ok(values.get(name).cloned());
        }
        let matches = self.functions.matching_impls(
            self.types,
            self.resolution,
            trait_id,
            &required,
            actual,
            0,
        )?;
        if let Some(selected) = self
            .functions
            .select_most_specific(self.resolution, &matches)
        {
            return Ok(self.functions.impl_headers[selected.header]
                .associated
                .consts
                .get(name)
                .cloned());
        }
        Ok(None)
    }
    /// Lower the checked contract of one object method: trait-argument and
    /// `Self` substitution, associated projection normalization, usage grades,
    /// result contract, and the declared effect row.
    pub(super) fn dyn_method_contract(
        &mut self,
        trait_id: BindingId,
        trait_arguments: &TraitArguments,
        name: &str,
        method_arguments: Option<&MethodArguments>,
        span: Span,
    ) -> Result<DynMethodContract> {
        let definition = self.functions.traits[&trait_id].clone();
        let method = definition
            .methods
            .get(name)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "trait '{}' has no method '{name}'",
                        self.resolution.bindings[trait_id].name
                    ),
                )
            })?
            .function;
        let mode = trait_receiver_mode(method);
        let mut substitution = crate::runtime_types::Subst::default();
        let mut consts = BTreeMap::new();
        let mut grades = BTreeMap::new();
        let mut effects = BTreeMap::new();
        insert_trait_arguments(
            self.resolution,
            &definition.generics,
            trait_arguments,
            &mut substitution,
            &mut consts,
            &mut grades,
            &mut effects,
        );
        substitution.consts = consts;
        substitution.grades = grades;
        substitution.effects = effects;
        // Method type/grade/natural/effect parameters are monomorphized at this
        // call site, exactly like a static generic call.
        if let Some(arguments) = method_arguments {
            let mut type_index = 0;
            let mut const_index = 0;
            let mut grade_index = 0;
            let mut effect_index = 0;
            for generic in &method.generics {
                let Some(binder) = self.resolution.binder(generic.span) else {
                    continue;
                };
                match generic_category(self.resolution, generic) {
                    GenericCategory::Type => {
                        if let Some(ty) = arguments.types.get(type_index) {
                            substitution.types.insert(binder, *ty);
                        }
                        type_index += 1;
                    }
                    GenericCategory::Const => {
                        if let Some(value) = arguments.consts.get(const_index) {
                            substitution.consts.insert(binder, *value);
                        }
                        const_index += 1;
                    }
                    GenericCategory::Grade => {
                        if let Some(grade) = arguments.grades.get(grade_index) {
                            substitution.grades.insert(binder, *grade);
                        }
                        grade_index += 1;
                    }
                    GenericCategory::Effect => {
                        if let Some(bits) = arguments.effects.get(effect_index) {
                            substitution.effects.insert(binder, *bits);
                        }
                        effect_index += 1;
                    }
                }
            }
        }
        substitution.self_projections = self
            .types
            .object_projections
            .get(&(trait_id, trait_arguments.clone()))
            .cloned()
            .unwrap_or_default();
        let mut parameters = Vec::new();
        let mut parameter_grades = Vec::new();
        for parameter in &method.parameters[1..] {
            let (ty, grade) = split_grade(&parameter.ty);
            parameters.push(self.types.ty_in(ty, &substitution)?);
            parameter_grades.push(
                grade
                    .map(|grade| grades::evaluate(self.resolution, &substitution.grades, grade))
                    .transpose()?,
            );
        }
        let (result_ast, result_grade) = result_contract(
            self.resolution,
            self.types,
            &substitution.grades,
            &method.result,
        )?;
        let result = self.types.ty_in(&result_ast, &substitution)?;
        let effects = crate::runtime_types::effect_bits_with(
            self.resolution,
            &method.effects,
            &substitution.effects,
        )?;
        let value_type = if result_grade.is_some_and(Grade::is_zero) {
            Type::Unit
        } else {
            result
        };
        Ok(DynMethodContract {
            mode,
            parameters,
            parameter_grades,
            result,
            result_grade,
            effects,
            value_type,
        })
    }
    /// Resolve and instantiate the checked method for every concrete member of
    /// a closed-world union object, returning `(tag, member, function)`. Used
    /// by in-place borrowed dispatch, which must not copy the payload.
    pub(super) fn union_member_functions(
        &mut self,
        trait_id: BindingId,
        trait_arguments: &TraitArguments,
        name: &str,
        span: Span,
    ) -> Result<Vec<(usize, Type, usize)>> {
        let object = self
            .types
            .dyn_objects
            .get(&(trait_id, trait_arguments.clone()))
            .copied()
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "internal error: closed-world object has no union representation",
                )
            })?;
        let members = self.types.union_members(object);
        let contract = self.dyn_method_contract(trait_id, trait_arguments, name, None, span)?;
        let mut out = Vec::with_capacity(members.len());
        for (tag, member) in members.into_iter().enumerate() {
            let impl_methods = self
                .functions
                .trait_impls
                .get(&(trait_id, trait_arguments.clone(), member))
                .cloned()
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "object member '{}' has no impl for method '{name}'",
                            self.types.name(member)
                        ),
                    )
                })?;
            let definition = impl_methods.get(name).copied().ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' does not implement dynamic method '{name}'",
                        self.types.name(member)
                    ),
                )
            })?;
            let function = self.functions.instance(
                self.types,
                self.resolution,
                definition.binding,
                vec![],
                vec![],
                vec![],
                vec![],
                definition.impl_arguments,
                Some(span),
            )?;
            let signature = self.functions.signatures[function].clone();
            if signature.parameters.len() != contract.parameters.len() + 1
                || signature.parameters[1..] != contract.parameters[..]
                || signature.parameter_grades[1..] != contract.parameter_grades[..]
                || signature.result != contract.result
                || signature.result_grade != contract.result_grade
                || signature.effects != contract.effects
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' has a different ABI for method '{name}'; object-safe methods must have identical non-receiver parameter and result types, usage contracts, and effects across impls",
                        self.types.name(member)
                    ),
                ));
            }
            out.push((tag, member, function));
        }
        Ok(out)
    }
    /// Associated-type values supplied by the impl selected for one concrete
    /// member, lowered with that impl's parameters. The dynamic representation
    /// has one fixed ABI per object specialization, so the first registered
    /// member fixes these projections and every later member must agree.
    pub(super) fn member_associated_projections(
        &mut self,
        member: Type,
        selected: MethodDefinition,
        trait_id: BindingId,
        trait_arguments: &TraitArguments,
        span: Span,
    ) -> Result<BTreeMap<String, Type>> {
        let Some(index) = selected.impl_arguments else {
            return Ok(BTreeMap::new());
        };
        let declared = self.functions.declared[&selected.binding];
        let Some(associated_index) = declared.impl_associated else {
            return Ok(BTreeMap::new());
        };
        let associated = self.functions.impl_associated[associated_index].clone();
        let instantiation = self.functions.impl_instantiations[index].clone();
        let header = self.functions.impl_headers[instantiation.header].clone();
        let mut substitution = crate::runtime_types::Subst {
            self_type: Some(member),
            associated_types: associated.types.clone(),
            ..Default::default()
        };
        let mut consts = BTreeMap::new();
        let mut grades = BTreeMap::new();
        let mut effects = BTreeMap::new();
        let mut type_index = 0;
        let mut const_index = 0;
        let mut grade_index = 0;
        let mut effect_index = 0;
        for generic in &header.generics {
            let binder = self.resolution.binder(generic.span).unwrap();
            match generic_category(self.resolution, generic) {
                GenericCategory::Type => {
                    substitution
                        .types
                        .insert(binder, instantiation.arguments.types[type_index]);
                    type_index += 1;
                }
                GenericCategory::Const => {
                    consts.insert(binder, instantiation.arguments.consts[const_index]);
                    const_index += 1;
                }
                GenericCategory::Grade => {
                    grades.insert(binder, instantiation.arguments.grades[grade_index]);
                    grade_index += 1;
                }
                GenericCategory::Effect => {
                    effects.insert(binder, instantiation.arguments.effects[effect_index]);
                    effect_index += 1;
                }
            }
        }
        substitution.consts = consts;
        substitution.grades = grades;
        substitution.effects = effects;
        let definition = self.functions.traits[&trait_id].clone();
        let mut trait_consts = BTreeMap::new();
        let mut trait_grades = BTreeMap::new();
        let mut trait_effects = BTreeMap::new();
        insert_trait_arguments(
            self.resolution,
            &definition.generics,
            trait_arguments,
            &mut substitution,
            &mut trait_consts,
            &mut trait_grades,
            &mut trait_effects,
        );
        substitution.consts.extend(trait_consts);
        substitution.grades.extend(trait_grades);
        substitution.effects.extend(trait_effects);
        let mut out = BTreeMap::new();
        for (name, value) in &associated.types {
            let lowered = self.types.ty_in(value, &substitution)?;
            out.insert(name.clone(), lowered);
        }
        let _ = span;
        Ok(out)
    }
    /// Register the concrete member `member` in the dynamic vtable of
    /// `object`. Every object-safe trait method is selected and instantiated
    /// for this member, including generic/blanket impls and inherited
    /// defaults. Registration is idempotent and re-entrant: a method body may
    /// itself coerce the same member type.
    pub(super) fn register_dyn_member(
        &mut self,
        object: usize,
        member: Type,
        span: Span,
    ) -> Result<usize> {
        let member = member.full();
        let info = self
            .types
            .objects
            .get(object)
            .cloned()
            .ok_or_else(|| Diagnostic::new(span, "internal error: unknown trait object"))?;
        if self.functions.dyn_members.len() <= object {
            self.functions.dyn_members.resize_with(object + 1, Vec::new);
        }
        if let Some(index) = self.functions.dyn_members[object]
            .iter()
            .position(|entry| entry.member == member)
        {
            return Ok(index);
        }
        if matches!(member, Type::DynObj(_)) {
            return Err(Diagnostic::new(
                span,
                "a trait object cannot be a concrete member of another trait object",
            ));
        }
        if member.is_ref()
            || member.is_slice()
            || member.is_text()
            || crate::runtime_types::has_borrow(self.types, member)
            || crate::runtime_types::contains_task(self.types, member)
        {
            return Err(Diagnostic::new(
                span,
                "a dynamically dispatched trait object stores an owned payload; a borrowed view, borrowed record, or task handle cannot be its concrete member. Own the value or keep the borrow call-scoped",
            ));
        }
        let index = self.functions.dyn_members[object].len();
        self.functions.dyn_members[object].push(DynMember {
            member,
            methods: BTreeMap::new(),
        });
        // One method table per listed trait: each key carries the trait's
        // position in the object's canonical component list.
        let mut methods = BTreeMap::new();
        for (component, (trait_id, arguments)) in info.components.iter().cloned().enumerate() {
            let definition = self.functions.traits[&trait_id].clone();
            if let Some(first_name) = definition.methods.keys().next().cloned() {
                let selected = self.lookup_method(
                    member,
                    &first_name,
                    Some((trait_id, arguments.clone())),
                    span,
                )?;
                let projections = self
                    .member_associated_projections(member, selected, trait_id, &arguments, span)?;
                let key = (trait_id, arguments.clone());
                for (name, lowered) in projections {
                    let previous = self
                        .types
                        .object_projections
                        .get(&key)
                        .and_then(|values| values.get(&name))
                        .copied();
                    if let Some(previous) = &previous
                        && *previous != lowered
                    {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "concrete member '{}' projects associated type '{name}' as {}, but this object specialization already fixed it as {}; a dyn object has one fixed ABI",
                                self.types.name(member),
                                self.types.name(lowered),
                                self.types.name(*previous)
                            ),
                        ));
                    }
                    self.types
                        .object_projections
                        .entry(key.clone())
                        .or_default()
                        .insert(name, lowered);
                }
            }
            for (name, method) in &definition.methods {
                // Generic methods are monomorphized per call-site argument list and
                // registered on demand; eager registration only covers the
                // non-generic fixed entries.
                if !method.function.generics.is_empty() {
                    continue;
                }
                let selected =
                    self.lookup_method(member, name, Some((trait_id, arguments.clone())), span)?;
                let function = self.functions.instance(
                    self.types,
                    self.resolution,
                    selected.binding,
                    vec![],
                    vec![],
                    vec![],
                    vec![],
                    selected.impl_arguments,
                    Some(span),
                )?;
                let contract = self.dyn_method_contract(trait_id, &arguments, name, None, span)?;
                let signature = self.functions.signatures[function].clone();
                if signature.parameters.len() != contract.parameters.len() + 1
                    || signature.parameters[1..] != contract.parameters[..]
                    || signature.parameter_grades[1..] != contract.parameter_grades[..]
                    || signature.result != contract.result
                    || signature.result_grade != contract.result_grade
                    || signature.effects != contract.effects
                {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "concrete member '{}' has a different ABI for object method '{name}'; dynamically dispatched methods must agree on every non-receiver parameter, result, usage grade, and effect across members",
                            self.types.name(member)
                        ),
                    ));
                }
                methods.insert(DynMethodKey::in_component(component, name), function);
            }
        }
        self.functions.dyn_members[object][index].methods = methods;
        // A call site may already have recorded a generic-method instance
        // before this member was coerced. Instantiate every recorded contract
        // for the new member now.
        if let Some(contracts) = self.functions.dyn_methods.get(&object).cloned() {
            for (key, contract) in contracts {
                self.register_dyn_method_for_member(object, index, &key, &contract, span)?;
            }
        }
        // Every object this one upcasts to must be able to name the member.
        let targets = self
            .functions
            .dyn_upcasts
            .iter()
            .filter(|(from, _)| *from == object)
            .map(|(_, to)| *to)
            .collect::<Vec<_>>();
        for target in targets {
            self.register_dyn_member(target, member, span)?;
        }
        Ok(index)
    }
    /// Record a checked upcast edge and register every current member of
    /// `from` in `to`; later members follow through `register_dyn_member`.
    pub(super) fn add_dyn_upcast(&mut self, from: usize, to: usize, span: Span) -> Result<()> {
        if !self.functions.dyn_upcasts.insert((from, to)) {
            return Ok(());
        }
        let members = self
            .functions
            .dyn_members
            .get(from)
            .map(|members| members.iter().map(|entry| entry.member).collect::<Vec<_>>())
            .unwrap_or_default();
        for member in members {
            self.register_dyn_member(to, member, span)?;
        }
        Ok(())
    }
    /// Instantiate one monomorphized generic method for one registered member
    /// and insert it into that member's dispatch table.
    pub(super) fn register_dyn_method_for_member(
        &mut self,
        object: usize,
        member_index: usize,
        key: &DynMethodKey,
        contract: &DynMethodContract,
        span: Span,
    ) -> Result<()> {
        if self.functions.dyn_members[object][member_index]
            .methods
            .contains_key(key)
        {
            return Ok(());
        }
        let member = self.functions.dyn_members[object][member_index].member;
        let component = self.types.objects[object].components[key.component].clone();
        let selected = self.lookup_method(member, &key.name, Some(component), span)?;
        let function = self.functions.instance(
            self.types,
            self.resolution,
            selected.binding,
            key.types.clone(),
            key.grades.clone(),
            key.consts.clone(),
            key.effects.clone(),
            selected.impl_arguments,
            Some(span),
        )?;
        let signature = self.functions.signatures[function].clone();
        if signature.parameters.len() != contract.parameters.len() + 1
            || signature.parameters[1..] != contract.parameters[..]
            || signature.parameter_grades[1..] != contract.parameter_grades[..]
            || signature.result != contract.result
            || signature.result_grade != contract.result_grade
            || signature.effects != contract.effects
        {
            return Err(Diagnostic::new(
                span,
                format!(
                    "concrete member '{}' has a different ABI for generic object method '{}'; dynamically dispatched methods must agree on every non-receiver parameter, result, usage grade, and effect for the same method arguments",
                    self.types.name(member),
                    key.name
                ),
            ));
        }
        self.functions.dyn_members[object][member_index]
            .methods
            .insert(key.clone(), function);
        Ok(())
    }
    /// Record the contract of a monomorphized generic method for one dynamic
    /// object and instantiate it for every member registered so far.
    pub(super) fn ensure_dyn_method(
        &mut self,
        object: usize,
        key: &DynMethodKey,
        contract: &DynMethodContract,
        span: Span,
    ) -> Result<()> {
        self.functions
            .dyn_methods
            .entry(object)
            .or_default()
            .entry(key.clone())
            .or_insert_with(|| contract.clone());
        let count = self.functions.dyn_members.get(object).map_or(0, Vec::len);
        for member_index in 0..count {
            self.register_dyn_method_for_member(object, member_index, key, contract, span)?;
        }
        Ok(())
    }
    /// Dynamic dispatch on an open/generic trait object. The value carries a
    /// checked member identifier; the backends resolve it against the
    /// registered vtable and call the selected checked function.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn dyn_object_method_call(
        &mut self,
        receiver: Expr,
        name: &str,
        trait_selection: Option<(BindingId, TraitArguments)>,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let borrowed_object = receiver.ty.ref_pointee().map(|pointer| {
            let pointee = self.types.pointees[pointer];
            (pointee, receiver.ty)
        });
        let object_ty = borrowed_object
            .map(|(object, _)| object)
            .unwrap_or(receiver.ty);
        let Type::DynObj(object) = object_ty else {
            return Err(Diagnostic::new(
                span,
                "internal error: dynamic object call on a non-object receiver",
            ));
        };
        let info = self
            .types
            .objects
            .get(object)
            .cloned()
            .ok_or_else(|| Diagnostic::new(span, "internal error: unknown trait object"))?;
        // Select the listed trait that provides `name`: the qualified trait
        // when the call spells one, otherwise the unique trait declaring it.
        let component = if let Some(selection) = &trait_selection {
            info.components
                .iter()
                .position(|component| component == selection)
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!(
                            "trait object '{}' does not represent the requested trait specialization",
                            info.name
                        ),
                    )
                })?
        } else {
            let providers = info
                .components
                .iter()
                .enumerate()
                .filter(|(_, (trait_id, _))| {
                    self.functions.traits[trait_id].methods.contains_key(name)
                })
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            match providers.as_slice() {
                [single] => *single,
                [] if info.components.len() == 1 => 0,
                [] => {
                    return Err(Diagnostic::new(
                        span,
                        format!("no trait of '{}' declares method '{name}'", info.name),
                    ));
                }
                _ => {
                    let traits = providers
                        .iter()
                        .map(|index| {
                            self.resolution.bindings[info.components[*index].0]
                                .name
                                .clone()
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "dynamic method '{name}' is provided by traits {traits}; disambiguate as 'receiver.Trait.method(...)'"
                        ),
                    ));
                }
            }
        };
        let (trait_id, trait_arguments) = info.components[component].clone();
        let method = self.functions.traits[&trait_id]
            .methods
            .get(name)
            .map(|method| method.function)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "trait '{}' has no method '{name}'",
                        self.resolution.bindings[trait_id].name
                    ),
                )
            })?;
        if explicit.is_some() && method.generics.is_empty() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "method '{name}' is not generic: non-generic methods take no explicit type arguments"
                ),
            ));
        }
        let mut method_arguments = MethodArguments::default();
        let mut prechecked: Option<Vec<Expr>> = None;
        if !method.generics.is_empty() {
            let pairs = method.parameters[1..]
                .iter()
                .zip(arguments)
                .filter(|(parameter, _)| !parameter.erased)
                .map(|(parameter, argument)| (&parameter.ty, argument))
                .collect::<Vec<_>>();
            let what = format!("method '{name}'");
            let hint = match expected {
                Some(expected) => Some((self.result_type_hint(&method.result)?, expected)),
                None => None,
            };
            let binders = method
                .lifetimes
                .iter()
                .map(|lifetime| lifetime.name.clone())
                .collect::<BTreeSet<_>>();
            let (types, grades, consts, effects, values) = self.infer(
                &method.generics,
                explicit,
                &pairs,
                hint.as_ref()
                    .map(|(declared, expected)| (declared, *expected)),
                Some(&binders),
                None,
                None,
                &what,
                span,
            )?;
            method_arguments = MethodArguments {
                types,
                consts,
                grades,
                effects,
            };
            prechecked = Some(values);
        }
        let method_arguments_ref = (!method.generics.is_empty()).then_some(&method_arguments);
        let contract =
            self.dyn_method_contract(trait_id, &trait_arguments, name, method_arguments_ref, span)?;
        let key = DynMethodKey {
            component,
            name: name.to_owned(),
            types: method_arguments.types.clone(),
            consts: method_arguments.consts.clone(),
            grades: method_arguments.grades.clone(),
            effects: method_arguments.effects.clone(),
        };
        if arguments.len() != contract.parameters.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count for dynamic method '{name}': expected {}, found {}",
                    contract.parameters.len(),
                    arguments.len()
                ),
            ));
        }
        if contract.result_grade.is_some_and(|grade| !grade.is_zero()) {
            return Err(Diagnostic::new(
                span,
                "a dynamic method cannot return an exact-use @[1] or must-use copyable result; consume the object statically or return an ordinary or erased value",
            ));
        }
        self.require(contract.effects, span)?;
        // The receiver is either an owned two-word fat object or a one-word
        // reference to one. Borrowed dispatch never copies the payload, so
        // owning and linear members stay in place.
        let reference_slot = match &receiver.kind {
            ExprKind::Peek(slot) | ExprKind::Local(slot) => Some(*slot),
            _ => None,
        };
        let mut consumed_field = Vec::new();
        let receiver = if let Some((_, reference_ty)) = borrowed_object {
            match (contract.mode, reference_ty) {
                (ReceiverMode::Owned, _) => {
                    return Err(Diagnostic::new(
                        span,
                        "cannot call an owning dynamic method through a borrowed trait object; call it on the owning value instead",
                    ));
                }
                (ReceiverMode::Mutable, Type::Ref(_)) => {
                    return Err(Diagnostic::new(
                        span,
                        "cannot call an exclusive dynamic method through a shared '&dyn' reference; bind the object with '&mut' or call on the owning local",
                    ));
                }
                _ => {}
            }
            receiver
        } else {
            match contract.mode {
                ReceiverMode::Owned => {
                    if matches!(receiver.kind, ExprKind::Project(..)) {
                        let (field, levels) = self.consume_object_field(receiver, span)?;
                        consumed_field = levels;
                        field
                    } else if let ExprKind::Peek(slot) = &receiver.kind {
                        let slot = *slot;
                        let ty = receiver.ty;
                        let receiver_span = receiver.span;
                        Expr {
                            kind: ExprKind::Local(slot),
                            ty,
                            span: receiver_span,
                            resource: None,
                        }
                    } else {
                        receiver
                    }
                }
                ReceiverMode::Shared | ReceiverMode::Mutable => {
                    if let Some(slot) = reference_slot {
                        if contract.mode == ReceiverMode::Mutable && !self.locals[slot].mutable {
                            return Err(Diagnostic::new(
                                span,
                                "a mutable dynamic method requires a mutable object binding; declare it with 'let mut'",
                            ));
                        }
                        let pointee = self.types.pointer(object_ty);
                        let ty = if contract.mode == ReceiverMode::Mutable {
                            Type::RefMut(pointee)
                        } else {
                            Type::Ref(pointee)
                        };
                        Expr {
                            kind: ExprKind::Borrow(slot),
                            ty,
                            span,
                            resource: None,
                        }
                    } else if matches!(receiver.kind, ExprKind::Project(..)) {
                        // A projected object field is borrowed in place, so
                        // the aggregate is never moved or copied, writes stay
                        // in the field, and a returned view keeps the owner
                        // borrowed like any other place reference.
                        let mutable = contract.mode == ReceiverMode::Mutable;
                        self.borrow_object_field(receiver, mutable, span)?
                    } else {
                        // A temporary receiver owns its payload just like a
                        // local. Its hidden storage is declared in the
                        // enclosing statement list (exactly like `&temp()`),
                        // initialized here in source order, and released at
                        // the end of that block. A receiver-tied view of it is
                        // therefore checked like a view of an ordinary local.
                        let mutable = contract.mode == ReceiverMode::Mutable;
                        let slot = self.hoist_owner(object_ty, mutable, span)?;
                        let borrow = self.borrow_local(slot, mutable, span)?;
                        Expr {
                            kind: ExprKind::BorrowInit {
                                slot,
                                value: Box::new(receiver),
                            },
                            ty: borrow.ty,
                            span,
                            resource: None,
                        }
                    }
                }
            }
        };
        let mut values = vec![receiver];
        if let Some(prechecked) = prechecked {
            for (value, ty) in prechecked.into_iter().zip(&contract.parameters) {
                values.push(self.coerce_argument(value, *ty, span)?);
            }
        } else {
            for (argument, ty) in arguments.iter().zip(&contract.parameters) {
                let value = self.expr_expected(argument, Some(*ty))?;
                values.push(self.coerce_argument(value, *ty, span)?);
            }
        }
        self.ensure_dyn_method(object, &key, &contract, span)?;
        let spec = self.functions.dyn_calls.len();
        self.functions.dyn_calls.push(DynCallSpec {
            object,
            trait_name: self.resolution.bindings[trait_id].name.clone(),
            method: name.to_owned(),
            key,
            mode: contract.mode,
            parameter_grades: contract.parameter_grades.clone(),
            result: contract.result,
            result_grade: contract.result_grade,
        });
        let value = Expr {
            kind: ExprKind::Call(Target::DynCall { spec }, values),
            ty: contract.value_type,
            span,
            resource: None,
        };
        let value = wrap_consumed_field(consumed_field, value);
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Dynamic dispatch on a closed-world trait object. Returns `None` when the
    /// receiver's union does not represent a trait providing this name, so the
    /// ordinary static path can produce its usual diagnostic.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn dynamic_method_call(
        &mut self,
        receiver: Expr,
        name: &str,
        trait_selection: Option<(BindingId, TraitArguments)>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        // A stored borrowed object is a reference to the same closed-world
        // union. Dispatch reads a copy through the reference; a copyable object
        // has value semantics, so this neither moves nor duplicates owning
        // storage. Mutable dispatch writes the updated object back through an
        // exclusive reference.
        let borrowed_object = receiver.ty.ref_pointee().map(|pointer| {
            let pointee = self.types.pointees[pointer];
            (pointee, receiver.ty)
        });
        let object_ty = borrowed_object
            .map(|(object, _)| object)
            .unwrap_or(receiver.ty);
        let Some(entries) = self.functions.object_traits.get(&object_ty).cloned() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "no dynamic method '{name}' is available for '{}'",
                    self.types.name(object_ty)
                ),
            ));
        };
        let entry = if let Some((trait_id, arguments)) = trait_selection {
            entries
                .iter()
                .find(|(id, args)| *id == trait_id && *args == arguments)
                .cloned()
        } else {
            let matching = entries
                .iter()
                .filter(|(trait_id, _)| self.functions.traits[trait_id].methods.contains_key(name))
                .cloned()
                .collect::<Vec<_>>();
            match matching.as_slice() {
                [] => {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "no trait represented by '{}' declares dynamic method '{name}'; qualify an object trait or use a static impl",
                            self.types.name(receiver.ty)
                        ),
                    ));
                }
                [single] => Some(single.clone()),
                _ => {
                    let traits = matching
                        .iter()
                        .map(|(id, _)| self.resolution.bindings[*id].name.clone())
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "dynamic method '{name}' is provided by traits {traits}; disambiguate as 'receiver.Trait.method(...)'"
                        ),
                    ));
                }
            }
        };
        let Some((trait_id, trait_arguments)) = entry else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "trait object '{}' does not represent the requested trait specialization",
                    self.types.name(receiver.ty)
                ),
            ));
        };
        let method = self.functions.traits[&trait_id]
            .methods
            .get(name)
            .map(|method| method.function)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "trait '{}' has no method '{name}'",
                        self.resolution.bindings[trait_id].name
                    ),
                )
            })?;
        let receiver_mode = trait_receiver_mode(method);
        let mut consumed_field = Vec::new();
        let receiver = if receiver_mode == ReceiverMode::Owned
            && matches!(receiver.kind, ExprKind::Project(..))
        {
            let (field, levels) = self.consume_object_field(receiver, span)?;
            consumed_field = levels;
            field
        } else {
            receiver
        };
        let direct_receiver_slot = match &receiver.kind {
            ExprKind::Peek(slot) | ExprKind::Local(slot) => Some(*slot),
            _ => None,
        };
        let projected = matches!(receiver_mode, ReceiverMode::Shared | ReceiverMode::Mutable)
            && matches!(receiver.kind, ExprKind::Project(..));
        // A temporary receiver of a borrowed method gets hidden storage in the
        // enclosing statement list, exactly like an open object, so it also
        // dispatches in place and owning or linear members are never copied.
        let temporary = borrowed_object.is_none()
            && !matches!(receiver.kind, ExprKind::Project(..))
            && direct_receiver_slot.is_none()
            && matches!(receiver_mode, ReceiverMode::Shared | ReceiverMode::Mutable);
        let in_place = borrowed_object.is_some()
            || projected
            || temporary
            || (matches!(receiver_mode, ReceiverMode::Shared | ReceiverMode::Mutable)
                && direct_receiver_slot.is_some());
        if in_place {
            // Borrowed closed-world objects dispatch in place through a stored
            // reference or a borrowed direct local. No payload copy is made, so
            // owning and linear members remain valid and mutations stay visible
            // to the owner.
            let (reference_ty, receiver) = if let Some((_, reference_ty)) = borrowed_object {
                match (reference_ty, receiver_mode) {
                    (Type::Ref(_), ReceiverMode::Mutable) => {
                        return Err(Diagnostic::new(
                            span,
                            "cannot call an exclusive dynamic method through a shared '&dyn' reference; bind the object with '&mut' or call on the owning local",
                        ));
                    }
                    (_, ReceiverMode::Owned) => {
                        return Err(Diagnostic::new(
                            span,
                            "cannot call an owning dynamic method through a borrowed trait object; call it on the owning value instead",
                        ));
                    }
                    _ => {}
                }
                (reference_ty, receiver)
            } else if projected {
                let mutable = receiver_mode == ReceiverMode::Mutable;
                let borrow = self.borrow_object_field(receiver, mutable, span)?;
                (borrow.ty, borrow)
            } else if temporary {
                let mutable = receiver_mode == ReceiverMode::Mutable;
                let slot = self.hoist_owner(object_ty, mutable, span)?;
                let borrow = self.borrow_local(slot, mutable, span)?;
                let ty = borrow.ty;
                (
                    ty,
                    Expr {
                        kind: ExprKind::BorrowInit {
                            slot,
                            value: Box::new(receiver),
                        },
                        ty,
                        span,
                        resource: None,
                    },
                )
            } else {
                let slot = direct_receiver_slot.expect("in-place dispatch has a direct receiver");
                if receiver_mode == ReceiverMode::Owned {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: owned dispatch is not an in-place borrowed call",
                    ));
                }
                if receiver_mode == ReceiverMode::Mutable && !self.locals[slot].mutable {
                    return Err(Diagnostic::new(
                        span,
                        "a mutable dynamic method requires a mutable object binding; declare it with 'let mut'",
                    ));
                }
                let pointee = self.types.pointer(object_ty);
                let ty = if receiver_mode == ReceiverMode::Mutable {
                    Type::RefMut(pointee)
                } else {
                    Type::Ref(pointee)
                };
                (
                    ty,
                    Expr {
                        kind: ExprKind::Borrow(slot),
                        ty,
                        span,
                        resource: None,
                    },
                )
            };
            let _ = reference_ty;
            let contract =
                self.dyn_method_contract(trait_id, &trait_arguments, name, None, span)?;
            if arguments.len() != contract.parameters.len() {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "wrong argument count for dynamic method '{name}': expected {}, found {}",
                        contract.parameters.len(),
                        arguments.len()
                    ),
                ));
            }
            if contract.result_grade.is_some_and(|grade| !grade.is_zero()) {
                return Err(Diagnostic::new(
                    span,
                    "a dynamic method cannot return an exact-use @[1] or must-use copyable result; consume the object statically or return an ordinary or erased value",
                ));
            }
            self.require(contract.effects, span)?;
            let mut values = vec![receiver];
            for (argument, ty) in arguments.iter().zip(&contract.parameters) {
                let value = self.expr_expected(argument, Some(*ty))?;
                values.push(self.coerce_argument(value, *ty, span)?);
            }
            let members = self.union_member_functions(trait_id, &trait_arguments, name, span)?;
            let spec = self.functions.union_calls.len();
            self.functions.union_calls.push(UnionCallSpec {
                mode: receiver_mode,
                parameter_grades: contract.parameter_grades.clone(),
                result: contract.result,
                result_grade: contract.result_grade,
                members,
            });
            let value = Expr {
                kind: ExprKind::Call(Target::UnionBorrowCall { spec }, values),
                ty: contract.value_type,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        // Every borrowed receiver (stored reference, direct local, projected
        // field, or temporary in hidden storage) dispatched in place above, so
        // only a consuming receiver remains. It moves the object into the
        // checked dispatcher exactly once.
        if receiver_mode != ReceiverMode::Owned || borrowed_object.is_some() {
            return Err(Diagnostic::new(
                span,
                "internal error: a borrowed closed-world dispatch was not lowered in place",
            ));
        }
        let (dispatcher, _) = self.dynamic_dispatcher(trait_id, &trait_arguments, name, span)?;
        let signature = self.functions.signatures[dispatcher].clone();
        if arguments.len() + 1 != signature.parameters.len() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count for dynamic method '{name}': expected {}, found {}",
                    signature.parameters.len().saturating_sub(1),
                    arguments.len()
                ),
            ));
        }
        self.require(signature.effects, span)?;
        let mut receiver = receiver;
        if let ExprKind::Peek(slot) = &receiver.kind {
            let slot = *slot;
            let ty = receiver.ty;
            let receiver_span = receiver.span;
            receiver = Expr {
                kind: ExprKind::Local(slot),
                ty,
                span: receiver_span,
                resource: None,
            };
        }
        let mut values = vec![receiver];
        for (argument, ty) in arguments.iter().zip(&signature.parameters[1..]) {
            let value = self.expr_expected(argument, Some(*ty))?;
            values.push(self.coerce_argument(value, *ty, span)?);
        }
        self.apply_effect_writes(signature.effects);
        let value = Expr {
            kind: ExprKind::Call(Target::Function(dispatcher), values),
            ty: call_result_type(&signature),
            span,
            resource: None,
        };
        let value = wrap_consumed_field(consumed_field, value);
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    /// Build (or reuse) the checked dispatcher for one consuming object
    /// method. The dispatcher takes the object union by value, matches its
    /// concrete alternative, and calls that impl's method. No vtable, erasure,
    /// or runtime allocation is introduced, and every alternative remains an
    /// ordinary checked function call. Borrowed receivers never use a
    /// dispatcher: they dispatch in place through `UnionBorrowCall`.
    pub(super) fn dynamic_dispatcher(
        &mut self,
        trait_id: BindingId,
        trait_arguments: &TraitArguments,
        name: &str,
        span: Span,
    ) -> Result<(usize, Type)> {
        let key = (trait_id, trait_arguments.clone(), name.to_owned());
        if let Some(entry) = self.functions.dynamic_dispatch.get(&key) {
            return Ok(*entry);
        }
        let definition = self.functions.traits[&trait_id].clone();
        let method = definition
            .methods
            .get(name)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "trait '{}' has no method '{name}'",
                        self.resolution.bindings[trait_id].name
                    ),
                )
            })?
            .function;
        let object = self
            .types
            .dyn_objects
            .get(&(trait_id, trait_arguments.clone()))
            .copied()
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "internal error: trait object has no closed-world representation",
                )
            })?;
        let members = self.types.union_members(object);
        let mut substitution = crate::runtime_types::Subst::default();
        let mut consts = BTreeMap::new();
        let mut grades = BTreeMap::new();
        let mut effects = BTreeMap::new();
        insert_trait_arguments(
            self.resolution,
            &definition.generics,
            trait_arguments,
            &mut substitution,
            &mut consts,
            &mut grades,
            &mut effects,
        );
        substitution.consts = consts;
        substitution.grades = grades;
        substitution.effects = effects;
        substitution.self_projections = self
            .types
            .object_projections
            .get(&(trait_id, trait_arguments.clone()))
            .cloned()
            .unwrap_or_default();
        let mut parameters = vec![object];
        let mut parameter_grades = vec![None];
        for parameter in &method.parameters[1..] {
            let (ty, grade) = split_grade(&parameter.ty);
            parameters.push(self.types.ty_in(ty, &substitution)?);
            parameter_grades.push(
                grade
                    .map(|grade| grades::evaluate(self.resolution, &substitution.grades, grade))
                    .transpose()?,
            );
        }
        let (result, result_grade) = result_contract(
            self.resolution,
            self.types,
            &substitution.grades,
            &method.result,
        )?;
        let result = self.types.ty_in(&result, &substitution)?;
        if result_grade.is_some_and(|grade| !grade.is_zero()) || self.linear_type(result) {
            return Err(Diagnostic::new(
                span,
                "a dynamic method cannot return an owning/exact-use @[1] contract; consume the object statically or return an ordinary or erased copyable value",
            ));
        }
        let result_erased = result_grade.is_some_and(Grade::is_zero);
        let method_value_type = if result_erased { Type::Unit } else { result };
        let function_result = method_value_type;
        let mut locals = parameters
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
        let mut total_effects = 0u16;
        let mut signatures = Vec::new();
        let mut witness_lifetimes: Option<WitnessLifetimes> = None;
        for member in &members {
            let Some(impl_methods) =
                self.functions
                    .trait_impls
                    .get(&(trait_id, trait_arguments.clone(), *member))
            else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' has no impl for method '{name}'",
                        self.types.name(*member)
                    ),
                ));
            };
            let Some(definition) = impl_methods.get(name) else {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' does not implement dynamic method '{name}'",
                        self.types.name(*member)
                    ),
                ));
            };
            let index = self.functions.instance(
                self.types,
                self.resolution,
                definition.binding,
                vec![],
                vec![],
                vec![],
                vec![],
                definition.impl_arguments,
                Some(span),
            )?;
            let signature = self.functions.signatures[index].clone();
            if signature.parameters.len() != parameters.len()
                || signature.parameters[1..] != parameters[1..]
                || signature.parameter_grades[1..] != parameter_grades[1..]
                || signature.result != result
                || signature.result_grade != result_grade
            {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "object member '{}' has a different ABI for method '{name}'; object-safe methods must have identical non-receiver parameter and result types and usage contracts across impls",
                        self.types.name(*member)
                    ),
                ));
            }
            total_effects |= signature.effects;
            if witness_lifetimes.is_none() {
                witness_lifetimes = Some((
                    signature.parameter_lifetimes.clone(),
                    signature.result_lifetime.clone(),
                    signature.lifetime_bounds.clone(),
                ));
            }
            signatures.push((index, *member));
        }
        let mut arms = Vec::new();
        for (tag, (index, member)) in signatures.into_iter().enumerate() {
            let payload = locals.len();
            locals.push(Local {
                ty: member,
                mutable: false,
                linear: false,
                pinned: false,
                grade: None,
                span,
            });
            let receiver_argument = Expr {
                kind: ExprKind::Local(payload),
                ty: member,
                span,
                resource: None,
            };
            let mut call_arguments = vec![receiver_argument];
            for (slot, ty) in parameters.iter().enumerate().skip(1) {
                call_arguments.push(
                    if crate::runtime_types::grade_erases(parameter_grades[slot]) {
                        // The dispatcher's own parameter is physically absent;
                        // never read its unmaterialized local.
                        Expr {
                            kind: ExprKind::Erased(*ty),
                            ty: *ty,
                            span,
                            resource: None,
                        }
                    } else {
                        Expr {
                            kind: ExprKind::Local(slot),
                            ty: *ty,
                            span,
                            resource: None,
                        }
                    },
                );
            }
            let method_call = Expr {
                kind: ExprKind::Call(Target::Function(index), call_arguments),
                ty: method_value_type,
                span,
                resource: None,
            };
            let body = method_call;
            arms.push(Arm {
                pattern: Pattern::Type {
                    tag,
                    member,
                    inner: Box::new(Pattern::Bind(payload)),
                },
                guard: None,
                body,
            });
        }
        let scrutinee = Expr {
            kind: ExprKind::Local(0),
            ty: object,
            span,
            resource: None,
        };
        let body = Block {
            statements: Vec::new(),
            tail: Some(Box::new(Expr {
                kind: ExprKind::Match(Box::new(scrutinee), arms),
                ty: function_result,
                span,
                resource: None,
            })),
            ty: function_result,
        };
        let (witness_parameter_lifetimes, witness_result_lifetime, witness_bounds) =
            witness_lifetimes
                .unwrap_or_else(|| (vec![None; parameters.len()], None, BTreeSet::new()));
        let function = Function {
            name: format!(
                "<dyn {}::{}>",
                self.resolution.bindings[trait_id].name, name
            ),
            parameters: parameters.len(),
            closure: None,
            capture_refs: vec![],
            capture_writes: vec![],
            locals,
            result: function_result,
            body,
            span,
            resources: vec![],
            local_resources: vec![],
            parameter_grades: parameter_grades.clone(),
            result_grade,
            parameter_lifetimes: witness_parameter_lifetimes.clone(),
            result_lifetime: witness_result_lifetime.clone(),
            lifetime_bounds: witness_bounds.clone(),
            declared_lifetimes: BTreeSet::new(),
            index_relations: BTreeSet::new(),
            parameter_slots: None,
            local_borrowed: vec![],
            local_copyable: vec![],
            capability_parameters: vec![],
            shared_environment: false,
        };
        let signature = Signature {
            call_contract: None,
            binding: usize::MAX,
            name: function.name.clone(),
            parameters,
            result: function_result,
            effects: total_effects,
            span,
            substitution: BTreeMap::new(),
            consts: BTreeMap::new(),
            grades: BTreeMap::new(),
            effect_arguments: BTreeMap::new(),
            origin: None,
            parameter_grades,
            result_grade,
            parameter_lifetimes: witness_parameter_lifetimes,
            result_lifetime: witness_result_lifetime,
            lifetime_bounds: witness_bounds,
            self_type: None,
            default_trait: None,
            associated_consts: BTreeMap::new(),
        };
        let index = self.functions.add_synthetic(signature, function)?;
        self.functions
            .dynamic_dispatch
            .insert(key, (index, method_value_type));
        Ok((index, method_value_type))
    }
    /// The trait-argument substitution of an inherited default method, if the
    /// method was materialized from a trait default. Generic method inference
    /// uses it to resolve trait parameters that appear in the declared
    /// signature, exactly like `Self`.
    pub(super) fn default_method_substitution(
        &self,
        binding: BindingId,
        impl_arguments: Option<usize>,
    ) -> Option<crate::runtime_types::Subst> {
        let declared = self.functions.declared[&binding];
        let index = declared.default_specialization?;
        let (trait_id, _) = self.functions.default_specializations[index].clone();
        let definition = &self.functions.traits[&trait_id];
        let mut substitution = crate::runtime_types::Subst {
            self_type: self.functions.self_type_for(binding, impl_arguments),
            ..Default::default()
        };
        let arguments = self
            .functions
            .trait_arguments_for(binding, impl_arguments)
            .unwrap_or_default();
        let mut consts = BTreeMap::new();
        let mut grades = BTreeMap::new();
        let mut effects = BTreeMap::new();
        insert_trait_arguments(
            self.resolution,
            &definition.generics,
            &arguments,
            &mut substitution,
            &mut consts,
            &mut grades,
            &mut effects,
        );
        substitution.consts = consts;
        substitution.grades = grades;
        substitution.effects = effects;
        Some(substitution)
    }
    /// Lower one statically dispatched method call to an ordinary checked
    /// function call whose first argument is the receiver.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn invoke_method(
        &mut self,
        binding: BindingId,
        impl_arguments: Option<usize>,
        receiver_ast: &ast::Expr,
        receiver: Expr,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let f = self.functions.declared[&binding].ast;
        if f.parameters.len() != arguments.len() + 1 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "wrong argument count for method '{}': expected {}, found {}",
                    f.name,
                    f.parameters.len().saturating_sub(1),
                    arguments.len()
                ),
            ));
        }
        if explicit.is_some() && f.generics.is_empty() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "method '{}' is not generic: non-generic methods take no explicit type arguments",
                    f.name
                ),
            ));
        }
        let lifetime_binders = f
            .lifetimes
            .iter()
            .map(|lifetime| lifetime.name.clone())
            .collect::<BTreeSet<_>>();
        // Runtime-length binders in the method signature are replaced by the
        // caller's bindings, exactly as for a free-function call.
        let lengths = self.call_runtime_lengths(f, 1, arguments)?;
        let mut prechecked = None;
        let mut generic_arguments = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        if !f.generics.is_empty() {
            self.pending_lengths = lengths.clone();
            let pairs = f.parameters[1..]
                .iter()
                .zip(arguments)
                .filter(|(parameter, _)| !parameter.erased)
                .map(|(parameter, argument)| (&parameter.ty, argument))
                .collect::<Vec<_>>();
            let what = format!("method '{}'", f.name);
            let self_type = self.functions.self_type_for(binding, impl_arguments);
            let base = self.default_method_substitution(binding, impl_arguments);
            let hint = match expected {
                Some(expected) => Some((self.result_type_hint(&f.result)?, expected)),
                None => None,
            };
            let (types, grades, consts, effects, values) = self.infer(
                &f.generics,
                explicit,
                &pairs,
                hint.as_ref()
                    .map(|(declared, expected)| (declared, *expected)),
                Some(&lifetime_binders),
                self_type,
                base.as_ref(),
                &what,
                span,
            )?;
            generic_arguments = (types, grades, consts, effects);
            prechecked = Some(values.into_iter());
        }
        let index = self.functions.instance(
            self.types,
            self.resolution,
            binding,
            generic_arguments.0,
            generic_arguments.1,
            generic_arguments.2,
            generic_arguments.3,
            impl_arguments,
            Some(span),
        )?;
        let mut signature = self.functions.signatures[index].clone();
        let (lifetime_binders, lifetime_names) = signature.scope_call_lifetimes();
        self.require(signature.effects, span)?;
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
        let mut callee_binders = Vec::new();
        let mut callee_types = Vec::new();
        let mut callee_actuals = Vec::new();
        let mut diverges = false;
        let mut values = Vec::with_capacity(f.parameters.len());
        // The receiver occupies runtime position zero. If a later erased
        // logical parameter names it as a symbolic scalar, record that binder
        // exactly as `user_call` does for ordinary arguments.
        let receiver_type = parameter_types[0].expect("method receiver is not erased");
        let receiver_binder = self.resolution.binder(f.parameters[0].span).unwrap();
        if f.parameters[1..].iter().any(|later| {
            later.erased
                && !matches!(later.ty.kind, ast::TypeKind::Predicate(_))
                && type_references_binding(self.resolution, &later.ty, receiver_binder)
        }) {
            let actual = self.scalar_argument(receiver_ast, receiver_type, span)?;
            callee_binders.push(receiver_binder);
            callee_types.push(Term::Scalar(
                receiver_type.scalar_carrier().expect("scalar receiver"),
            ));
            callee_actuals.push(actual);
        }
        values.push(receiver);
        let mut checked_arguments = prechecked.map(|values| values.into_iter());
        for (offset, (parameter, evidence)) in f.parameters[1..].iter().zip(arguments).enumerate() {
            let position = offset + 1;
            if !parameter.erased {
                let ty = parameter_types[position].expect("runtime parameter");
                let binder = self.resolution.binder(parameter.span).unwrap();
                if !diverges
                    && let Some(carrier) = ty.scalar_carrier()
                    && f.parameters[position + 1..].iter().any(|later| {
                        later.erased
                            && !matches!(later.ty.kind, ast::TypeKind::Predicate(_))
                            && type_references_binding(self.resolution, &later.ty, binder)
                    })
                {
                    let actual = self.scalar_argument(evidence, ty, span)?;
                    callee_binders.push(binder);
                    callee_types.push(Term::Scalar(carrier));
                    callee_actuals.push(actual);
                }
                let value = match checked_arguments.as_mut() {
                    Some(values) => values
                        .next()
                        .expect("inferred method argument in runtime order"),
                    None => {
                        let ty = self.types.rebind_lengths(ty, &lengths, evidence.span)?;
                        let wanted = if lifetime_binders.is_empty() {
                            ty
                        } else {
                            self.types
                                .freshen_borrows(ty, &lifetime_binders, evidence.span)?
                        };
                        self.expr_expected(evidence, Some(wanted))?
                    }
                };
                diverges |= value.ty == Type::Never;
                values.push(value);
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
        diverges |= values.iter().any(|value| value.ty == Type::Never);
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
        for (value, ty) in values.into_iter().zip(&signature.parameters) {
            let ty = self.types.relabel_lifetimes(*ty, &lifetime_map, span)?;
            let ty = self.types.rebind_lengths(ty, &lengths, span)?;
            coerced.push(self.coerce_argument(value, ty, span)?);
        }
        self.apply_effect_writes(signature.effects);
        let (statements, coerced) = self.two_phase_arguments(coerced, ty)?;
        let value = Expr {
            kind: ExprKind::Call(Target::Function(index), coerced),
            ty,
            span,
            resource: None,
        };
        // ENSURES-METHODS: a method call gets its postconditions like a
        // direct call; the receiver is the first argument.
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
    /// Two-phase exclusive borrows for a call's arguments. Passing an
    /// exclusive reference (`m`, `&mut x`, `&mut m.field`) has no side
    /// effect, so the call may take it after its other arguments have been
    /// evaluated. When another argument reads the same root
    /// (`push(m, m.pc)`), the non-place arguments and those reads are
    /// evaluated first, in order, into hidden locals, and the reference is
    /// taken last. Without this, the reborrow would be live while `m.pc` is
    /// read, and the read would be rejected. Returns the statements to run
    /// before the call and the call's arguments.
    pub(super) fn two_phase_arguments(
        &mut self,
        arguments: Vec<Expr>,
        ty: Type,
    ) -> Result<(Vec<Statement>, Vec<Expr>)> {
        fn root(expr: &Expr) -> Option<usize> {
            match &expr.kind {
                ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Borrow(slot) => {
                    Some(*slot)
                }
                ExprKind::BorrowPlace(inner) | ExprKind::Project(inner, _) => root(inner),
                _ => None,
            }
        }
        fn mentions(expr: &Expr, slot: usize) -> bool {
            if let ExprKind::Local(s) | ExprKind::Peek(s) | ExprKind::Borrow(s) = &expr.kind
                && *s == slot
            {
                return true;
            }
            let mut found = false;
            expr.for_each_child(&mut |child| found = found || mentions(child, slot));
            found
        }
        if ty == Type::Never || arguments.iter().any(|a| a.ty == Type::Never) {
            return Ok((Vec::new(), arguments));
        }
        let exclusive: Vec<Option<usize>> = arguments
            .iter()
            .map(|argument| match argument.ty {
                Type::RefMut(_) => root(argument),
                _ => None,
            })
            .collect();
        let roots: Vec<usize> = exclusive.iter().flatten().copied().collect();
        if roots.is_empty() {
            return Ok((Vec::new(), arguments));
        }
        let reads_root = |index: usize, argument: &Expr| {
            exclusive[index].is_none() && roots.iter().any(|&slot| mentions(argument, slot))
        };
        if !arguments.iter().enumerate().any(|(i, a)| reads_root(i, a)) {
            return Ok((Vec::new(), arguments));
        }
        // Reads of a borrowed root, and any argument with effects (which
        // must keep its order relative to them), are evaluated early.
        let early: Vec<bool> = arguments
            .iter()
            .enumerate()
            .map(|(i, a)| exclusive[i].is_none() && (reads_root(i, a) || root(a).is_none()))
            .collect();
        // A reference or view cannot be parked in a hidden local without a
        // lifetime of its own; leave such calls as they are.
        if arguments
            .iter()
            .zip(&early)
            .any(|(a, early)| *early && (a.ty.is_ref() || a.ty.is_view()))
        {
            return Ok((Vec::new(), arguments));
        }
        let mut statements = Vec::new();
        let mut values = Vec::with_capacity(arguments.len());
        for (argument, early) in arguments.into_iter().zip(early) {
            if !early || matches!(argument.kind, ExprKind::Constant(_)) {
                values.push(argument);
                continue;
            }
            let slot = self.fresh_local(argument.span, argument.ty)?;
            let local = Expr {
                kind: ExprKind::Local(slot),
                ty: argument.ty,
                span: argument.span,
                resource: None,
            };
            statements.push(Statement::Let(slot, argument));
            values.push(local);
        }
        Ok((statements, values))
    }
    /// Wrap a call in the statements its two-phase arguments need.
    pub(super) fn after(statements: Vec<Statement>, call: Expr) -> Expr {
        if statements.is_empty() {
            return call;
        }
        let ty = call.ty;
        let span = call.span;
        Expr {
            kind: ExprKind::Block(Block {
                statements,
                tail: Some(Box::new(call)),
                ty,
            }),
            ty,
            span,
            resource: None,
        }
    }
}
