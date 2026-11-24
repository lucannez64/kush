//! Slice and text views and their calls.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Build a slice view over a local owner or another slice view.
    pub(super) fn slice_view(
        &mut self,
        value: &ast::Expr,
        start: Option<&ast::Expr>,
        end: Option<&ast::Expr>,
        mutable: bool,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        let (base, element, static_length, field) = if let ast::ExprKind::Slice {
            value: inner,
            start: inner_start,
            end: inner_end,
        } = &value.kind
        {
            let base = self.slice_view(
                inner,
                inner_start.as_deref(),
                inner_end.as_deref(),
                mutable,
                value.span,
                None,
            )?;
            if base.ty.is_text() {
                return self.text_view_from_expr(base, start, end, mutable, span, expected);
            }
            let Some(pointer) = base.ty.slice_element() else {
                unreachable!("slice construction has slice type")
            };
            (base, self.types.pointees[pointer], None, None)
        } else if matches!(value.kind, ast::ExprKind::Field { .. })
            && !self.field_root_is_local_record(value)
            && let Some((base, element, path)) = self.indirect_dyn_field_place(value, mutable)?
        {
            // A DynArray field reached through a record reference or a
            // temporary record. A reference root aliases the caller's record;
            // a temporary is hoisted into hidden storage that outlives the view
            // until the enclosing block ends.
            (base, element, None, Some(path))
        } else if matches!(value.kind, ast::ExprKind::Field { .. }) {
            // A nested record-field borrow: `outer.inner.view[..]`. The root is
            // still a direct local owner; the projection is checked by the
            // ownership pass, which keeps the field path and its owner loaned.
            let old_place = self.field_place;
            self.field_place = true;
            let checked = self.expr(value);
            self.field_place = old_place;
            let base = checked?;
            if let Some((element, _capacity)) = base
                .ty
                .layout()
                .and_then(|id| self.types.enums[id].dynamic_array)
            {
                // A view over a DynArray field of a record place. The record
                // root must be a direct local so both backends can pin its
                // storage; the field path identifies the live inline slots.
                let Some((root, path)) = self.projection_root(&base) else {
                    return Err(Diagnostic::new(
                        value.span,
                        "a DynArray field view requires a record binding rooted at a direct local; bind the record to a local first",
                    ));
                };
                if mutable && !self.locals[root].mutable {
                    return Err(Diagnostic::new(
                        value.span,
                        "cannot create an exclusive '&mut [T]' view of a field of an immutable record binding; declare the record with 'let mut'",
                    )
                    .with_note(self.locals[root].span, "record declared here"));
                }
                (base, element, None, Some(path))
            } else {
                let Some(pointer) = base.ty.slice_element() else {
                    return Err(Diagnostic::new(
                        value.span,
                        format!(
                            "only a borrowed slice field or a DynArray field can be sub-sliced through a record projection, found {}",
                            self.types.name(base.ty)
                        ),
                    ));
                };
                if mutable && !base.ty.is_mut_slice() {
                    return Err(Diagnostic::new(
                        value.span,
                        "cannot create an exclusive '&mut [T]' view from a shared record field; shared storage cannot be upgraded",
                    ));
                }
                (base, self.types.pointees[pointer], None, None)
            }
        } else {
            let slot = self.slot(value.span).map_err(|_| {
                Diagnostic::new(
                    value.span,
                    "a slice or text view must borrow a local array, Vec, Bytes, String, view, or record field; bind the owner to a local first",
                )
            })?;
            let ty = self.locals[slot].ty;
            if ty.is_text() {
                if mutable && ty == Type::Str {
                    return Err(Diagnostic::new(
                        value.span,
                        "cannot create an exclusive '&mut str' view from a shared '&str'; shared text cannot be upgraded",
                    )
                    .with_note(self.locals[slot].span, "shared text view declared here"));
                }
                let base = Expr {
                    kind: ExprKind::Local(slot),
                    ty,
                    span: value.span,
                    resource: None,
                };
                return self.text_view_from_expr(base, start, end, mutable, span, expected);
            }
            if mutable && !self.locals[slot].mutable && !ty.is_slice() {
                return Err(Diagnostic::new(
                    value.span,
                    "cannot create an exclusive '&mut [T]' view of an immutable binding; declare the owner with 'let mut'",
                )
                .with_note(self.locals[slot].span, "owner declared here"));
            }
            if let Some((element, length)) = ty.layout().and_then(|id| self.types.enums[id].array) {
                (
                    Expr {
                        kind: ExprKind::Peek(slot),
                        ty,
                        span: value.span,
                        resource: None,
                    },
                    element,
                    Some(length),
                    None,
                )
            } else if let Some((element, _capacity)) = ty
                .layout()
                .and_then(|id| self.types.enums[id].dynamic_array)
            {
                // The view covers the live prefix: its length is the runtime
                // length word, not the compile-time capacity. A reborrow via
                // `Borrow` keeps the owner loaned for the view's lexical scope,
                // so push/pop/assignment cannot run while the view is live. An
                // exclusive view requires a mutable binding (checked above) and
                // is the only way to write slots through the view.
                let owner = self.types.pointer(ty);
                (
                    Expr {
                        kind: ExprKind::Borrow(slot),
                        ty: if mutable {
                            Type::RefMut(owner)
                        } else {
                            Type::Ref(owner)
                        },
                        span: value.span,
                        resource: None,
                    },
                    element,
                    None,
                    None,
                )
            } else if let Type::Vec(pointer) = ty {
                let element = self.types.pointees[pointer];
                let owner = self.types.pointer(ty);
                (
                    Expr {
                        kind: ExprKind::Borrow(slot),
                        ty: Type::Ref(owner),
                        span: value.span,
                        resource: None,
                    },
                    element,
                    None,
                    None,
                )
            } else if ty == Type::Bytes {
                (
                    Expr {
                        kind: ExprKind::Borrow(slot),
                        ty: Type::Ref(self.types.pointer(Type::Bytes)),
                        span: value.span,
                        resource: None,
                    },
                    Type::I64,
                    None,
                    None,
                )
            } else if ty == Type::String {
                return Err(Diagnostic::new(
                    value.span,
                    "String does not support byte slicing; use String.byte_at or String.scalar_at, convert explicitly with String.as_bytes, or borrow text with String.as_str / String.substr",
                ));
            } else if let Type::SliceMut(pointer) = ty {
                // A mutable view may be narrowed to a shared or exclusive
                // child. Ownership checking records the parent capability and
                // rejects shared-to-mutable upgrades.
                (
                    Expr {
                        kind: ExprKind::Local(slot),
                        ty,
                        span: value.span,
                        resource: None,
                    },
                    self.types.pointees[pointer],
                    None,
                    None,
                )
            } else if let Type::Slice(pointer) = ty {
                if mutable {
                    return Err(Diagnostic::new(
                        value.span,
                        "a shared '&[T]' view cannot be upgraded to an exclusive '&mut [T]' view",
                    ));
                }
                (
                    Expr {
                        kind: ExprKind::Local(slot),
                        ty,
                        span: value.span,
                        resource: None,
                    },
                    self.types.pointees[pointer],
                    None,
                    None,
                )
            } else {
                return Err(Diagnostic::new(
                    value.span,
                    format!(
                        "cannot slice {}; bind an inline array, Vec<T>, Bytes, or &[T] view to a local first",
                        self.types.name(ty)
                    ),
                ));
            }
        };
        // THREAD-ATOMICS: atomics are shared through views; only the
        // `Atomic.*` operations read or write their elements.
        if self.owned_type(element) && !matches!(element, Type::Atomic | Type::Channel(_)) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "cannot form a slice view over owning or linear elements ({}); element reads would copy an owner",
                    self.types.name(element)
                ),
            ));
        }
        let mut checked = false;
        let mut start_constant = None;
        let mut end_constant = None;
        if let Some(length) = static_length {
            let start_value = match start {
                Some(start) => self.constant_bound(start).transpose()?,
                None => Some(0),
            };
            let end_value = match end {
                Some(end) => self.constant_bound(end).transpose()?,
                None => Some(length),
            };
            if let (Some(start_value), Some(end_value)) = (start_value, end_value) {
                if start_value > end_value || end_value > length {
                    return Err(Diagnostic::new(
                        span,
                        format!("slice range is out of bounds for an array of length {length}"),
                    ));
                }
            } else {
                checked = true;
            }
            start_constant = start_value;
            end_constant = end_value;
        } else {
            checked = start.is_some() || end.is_some();
        }
        if checked {
            self.require(PANIC, span)?;
        }
        let number = |value: usize, span: Span| -> Result<Expr> {
            let value = i64::try_from(value).map_err(|_| {
                Diagnostic::new(span, "slice bound is too large for a runtime i64 index")
            })?;
            Ok(Expr {
                kind: ExprKind::Constant(value),
                ty: Type::I64,
                span,
                resource: None,
            })
        };
        let start = match (start, start_constant) {
            (Some(start), Some(value)) => Some(number(value, start.span)?),
            (Some(start), None) => Some(self.expr_expected(start, Some(Type::I64))?),
            (None, _) => None,
        };
        let end = match (end, end_constant) {
            (Some(end), Some(value)) => Some(number(value, end.span)?),
            (Some(end), None) => Some(self.expr_expected(end, Some(Type::I64))?),
            (None, Some(value)) => Some(number(value, span)?),
            (None, None) => None,
        };
        if let Some(start) = &start {
            self.expect(start.ty, Type::I64, start.span)?;
        }
        if let Some(end) = &end {
            self.expect(end.ty, Type::I64, end.span)?;
        }
        self.slice_from_expr(
            base, start, end, element, checked, mutable, span, expected, field,
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn slice_from_expr(
        &mut self,
        base: Expr,
        start: Option<Expr>,
        end: Option<Expr>,
        element: Type,
        check: bool,
        mutable: bool,
        span: Span,
        expected: Option<Type>,
        field: Option<Vec<usize>>,
    ) -> Result<Expr> {
        if check {
            self.require(PANIC, span)?;
        }
        let pointer = self.types.pointer(element);
        let ty = if mutable {
            Type::SliceMut(pointer)
        } else {
            Type::Slice(pointer)
        };
        let value = Expr {
            kind: ExprKind::Slice {
                base: Box::new(base),
                start: start.map(Box::new),
                end: end.map(Box::new),
                element,
                check,
                split: None,
                text: false,
                field,
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
    /// Build a checked borrowed text view over `base`, which must be a
    /// `&String` borrow or another `&str` view. Any supplied bound adds a
    /// runtime `0 <= start <= end <= byte length` check plus UTF-8 scalar
    /// boundary checks at both endpoints; these are enforced in both backends.
    /// A checked text view over `base` (a `&String`/`&mut String` owner
    /// reference or a text view). `mutable` makes an exclusive `&mut str`,
    /// which needs an exclusive base.
    pub(super) fn text_view_from_expr(
        &mut self,
        base: Expr,
        start: Option<&ast::Expr>,
        end: Option<&ast::Expr>,
        mutable: bool,
        span: Span,
        expected: Option<Type>,
    ) -> Result<Expr> {
        if mutable && !matches!(base.ty, Type::StrMut | Type::RefMut(_)) {
            return Err(Diagnostic::new(
                base.span,
                "an exclusive '&mut str' view needs an exclusive '&mut String' or '&mut str' source; shared text cannot be upgraded",
            ));
        }
        let check = start.is_some() || end.is_some();
        if check {
            self.require(PANIC, span)?;
        }
        let start = match start {
            Some(start) => {
                let value = self.expr_expected(start, Some(Type::I64))?;
                self.expect(value.ty, Type::I64, value.span)?;
                Some(value)
            }
            None => None,
        };
        let end = match end {
            Some(end) => {
                let value = self.expr_expected(end, Some(Type::I64))?;
                self.expect(value.ty, Type::I64, value.span)?;
                Some(value)
            }
            None => None,
        };
        let value = Expr {
            kind: ExprKind::Slice {
                base: Box::new(base),
                start: start.map(Box::new),
                end: end.map(Box::new),
                element: Type::I64,
                check,
                split: None,
                text: true,
                field: None,
            },
            ty: if mutable { Type::StrMut } else { Type::Str },
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
    pub(super) fn slice_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        if explicit.is_some() {
            return Err(Diagnostic::new(
                span,
                format!("{name} takes no type arguments"),
            ));
        }
        let expected_arguments = match name {
            "Slice.len" => 1,
            "Slice.get" => 2,
            "Slice.try_get" => 2,
            "Slice.set" => 3,
            "Slice.split_at_mut" => 2,
            _ => 3,
        };
        if arguments.len() != expected_arguments {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {expected_arguments} arguments, found {}",
                    arguments.len()
                ),
            ));
        }
        if name == "Slice.split_at_mut" {
            return Err(Diagnostic::new(
                span,
                "Slice.split_at_mut produces a restricted nonescaping borrow pair; use it directly as let (left, right) = Slice.split_at_mut(view, mid);",
            ));
        }
        let first = self.expr(&arguments[0])?;
        self.slice_call_with(name, first, &arguments[1..], expected, span)
    }
    /// Slice builtin with an already checked receiver (function call or method
    /// syntax). The receiver is evaluated exactly once, before `rest`.
    pub(super) fn slice_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = match name {
            "Slice.len" => 0,
            "Slice.get" | "Slice.try_get" => 1,
            "Slice.set" => 2,
            _ => 2,
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {} argument(s) after its receiver, found {}",
                    wanted,
                    rest.len()
                ),
            ));
        }
        let Some(pointer) = first.ty.slice_element() else {
            if first.ty == Type::Never {
                return Ok(first);
            }
            return Err(Diagnostic::new(
                first.span,
                format!(
                    "{name} expects a &[T] or &mut [T] slice view, found {}",
                    self.types.name(first.ty)
                ),
            ));
        };
        let mutable_view = first.ty == Type::SliceMut(pointer);
        if name == "Slice.set" && !mutable_view {
            return Err(Diagnostic::new(
                first.span,
                "Slice.set requires an exclusive mutable view '&mut [T]'; a shared '&[T]' view cannot be written",
            ));
        }
        let element = self.types.pointees[pointer];
        if self.owned_type(element) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} copies the element, but {} owns resources or is linear",
                    self.types.name(element)
                ),
            ));
        }
        if name == "Slice.len" {
            let ty = Type::I64;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(Expr {
                kind: ExprKind::Call(Target::Slice(SliceOp::Len, element), vec![first]),
                ty,
                span,
                resource: None,
            });
        }
        let index = self.expr_expected(&rest[0], Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        if name == "Slice.try_get" {
            if self.owned_type(element) || self.linear_type(element) {
                return Err(Diagnostic::new(
                    span,
                    "Slice.try_get can only copy elements; owning or linear elements cannot be returned by value from a slice view",
                ));
            }
            // The result is the conventional Option<T> shape, so a user
            // declaration may name its variants in either order.
            let option = self
                .resolution
                .slice_options
                .get(&(span.start, span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(span, "Slice.try_get requires Option<T> in scope")
                })?;
            let shape = self.types.option(option, element, span)?;
            let ty = shape.result;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            let op = SliceOp::TryGet {
                some_tag: shape.some_tag,
                none_tag: shape.none_tag,
                option: shape
                    .result
                    .layout()
                    .expect("the conventional Option is an enum layout"),
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Slice(op, element), vec![first, index]),
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if name == "Slice.set" {
            let value = self.expr_expected(&rest[1], Some(element))?;
            self.expect(value.ty, element, value.span)?;
            if self.owned_type(value.ty) || self.linear_type(value.ty) {
                return Err(Diagnostic::new(
                    value.span,
                    "Slice.set can only store copyable elements; moving an owner into a slice view is not supported",
                ));
            }
            self.require(PANIC, span)?;
            let values = vec![first, index, value];
            return Ok(Expr {
                kind: ExprKind::Call(Target::Slice(SliceOp::Set, element), values),
                ty: Type::Unit,
                span,
                resource: None,
            });
        }
        let values = vec![first, index];
        if name == "Slice.get" {
            self.require(PANIC, span)?;
        } else {
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
                text: "0 <= index && index < Slice.len(slice)".to_owned(),
            };
            self.discharge(&proposition, &values, &rest[1], span)?;
        }
        let ty = if values.iter().any(|value| value.ty == Type::Never) {
            Type::Never
        } else {
            element
        };
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        let op = if name == "Slice.get" {
            SliceOp::Get
        } else {
            SliceOp::At
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Slice(op, element), values),
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
