//! Builtin calls on bytes, integers, floats, strings and text views.
//!
//! Split from `executable.rs` (FND-SPLIT-EXEC).
use super::*;

impl Checker<'_, '_> {
    /// Byte-buffer builtin with an already checked receiver.
    pub(super) fn bytes_method(
        &mut self,
        op: BytesOp,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = match op {
            BytesOp::Len | BytesOp::Capacity | BytesOp::Copy | BytesOp::Clear => 0,
            BytesOp::Get | BytesOp::Push | BytesOp::PushReserved => 1,
            BytesOp::WithCapacity => {
                return Err(Diagnostic::new(
                    span,
                    "Bytes.with_capacity is constructed as Bytes.with_capacity(n), not as a method",
                ));
            }
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "this byte method expects {wanted} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        let first = if op.borrowed() {
            self.method_borrow(first)?
        } else {
            if first.ty != Type::Bytes {
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "this byte method consumes an owned Bytes value, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
            first
        };
        let effects = match op {
            BytesOp::Len | BytesOp::Capacity | BytesOp::Clear => 0,
            BytesOp::Get | BytesOp::PushReserved => PANIC,
            _ => ALLOC | PANIC,
        };
        self.require(effects, span)?;
        if op == BytesOp::Get {
            self.record_bounds(Container::Bytes, None, span);
        }
        let mut values = vec![first];
        if matches!(op, BytesOp::Get | BytesOp::Push | BytesOp::PushReserved) {
            let value = self.expr_expected(&rest[0], Some(Type::I64))?;
            self.expect(value.ty, Type::I64, value.span)?;
            values.push(value);
        }
        let ty = match op {
            BytesOp::Len | BytesOp::Capacity | BytesOp::Get => Type::I64,
            _ => Type::Bytes,
        };
        let ty = if values.iter().any(|value| value.ty == Type::Never) {
            Type::Never
        } else {
            ty
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Bytes(op), values),
            ty,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }

    /// Explicit integer and character builtins.
    pub(super) fn int_call(
        &mut self,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        self.int_call_with(None, name, explicit, arguments, expected, span)
    }
    /// Integer/Char builtin with an already checked first argument for method
    /// syntax. `first` is the receiver; `arguments` holds only the remaining
    /// source arguments. Evaluation order and target inference are unchanged.
    pub(super) fn int_call_with(
        &mut self,
        first: Option<Expr>,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        use crate::int::{ArithOp, IntKind, IntOp};
        let first_count = usize::from(first.is_some());
        let arity = match name {
            "print_int" | "Int.convert" | "Int.try_convert" | "Int.truncate" | "Char.code"
            | "Char.from_code" => 1,
            _ => 2,
        };
        if first_count + arguments.len() != arity {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {arity} argument(s), found {}",
                    first_count + arguments.len()
                ),
            ));
        }
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let option = |c: &mut Self, payload: Type| -> Result<crate::runtime_types::OptionShape> {
            let id = c
                .resolution
                .slice_options
                .get(&(span.start, span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(span, format!("{name} requires Option<T> in scope"))
                })?;
            c.types.option(id, payload, span)
        };
        let int_arg =
            |c: &mut Self, arg: &ast::Expr, hint: Option<Type>| -> Result<(Expr, IntKind)> {
                let value = c.expr_expected(arg, hint)?;
                match value.ty.int_kind() {
                    Some(kind) => Ok((value, kind)),
                    None if value.ty == Type::Never => Ok((value, IntKind::I64)),
                    None => Err(Diagnostic::new(
                        arg.span,
                        format!(
                            "{name} expects an integer, found {}",
                            c.types.name(value.ty)
                        ),
                    )),
                }
            };
        let first_kind = |c: &Self, value: &Expr| -> Result<IntKind> {
            value.ty.int_kind().ok_or_else(|| {
                Diagnostic::new(
                    value.span,
                    format!(
                        "{name} expects an integer, found {}",
                        c.types.name(value.ty)
                    ),
                )
            })
        };
        match name {
            "print_int" => {
                let (value, kind) = int_arg(self, &arguments[0], None)?;
                self.require(IO | PANIC, span)?;
                return Ok(unit(
                    ExprKind::Call(Target::PrintInt(kind), vec![value]),
                    Type::Unit,
                ));
            }
            "Char.code" => {
                let value = match first {
                    Some(value) => value,
                    None => self.expr_expected(&arguments[0], Some(Type::Char))?,
                };
                self.expect(value.ty, Type::Char, value.span)?;
                let ty = Type::Int(IntKind::U32);
                if let Some(expected) = expected {
                    self.expect(ty, expected, span)?;
                }
                return Ok(unit(
                    ExprKind::Call(
                        Target::Int(IntOp::Convert, IntKind::U32, IntKind::U32),
                        vec![value],
                    ),
                    ty,
                ));
            }
            "Char.from_code" => {
                let (value, kind) =
                    int_arg(self, &arguments[first_count], Some(Type::Int(IntKind::U32)))?;
                if kind != IntKind::U32 {
                    return Err(Diagnostic::new(
                        arguments[first_count].span,
                        "Char.from_code expects a u32 code point",
                    ));
                }
                let shape = option(self, Type::Char)?;
                let op = IntOp::CharFromCode {
                    some_tag: shape.some_tag,
                    none_tag: shape.none_tag,
                };
                return Ok(unit(
                    ExprKind::Call(Target::Int(op, kind, kind), vec![value]),
                    shape.result,
                ));
            }
            _ => {}
        }
        // The target integer type comes from `::<T>` or the expected type.
        let explicit_target = match explicit {
            Some([ty]) => {
                let ty = self.ty(ty)?;
                Some(ty.int_kind().ok_or_else(|| {
                    Diagnostic::new(span, format!("{name} needs an integer type argument"))
                })?)
            }
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    format!("{name} takes one type argument"),
                ));
            }
            None => None,
        };
        let optional = matches!(
            name,
            "Int.try_convert" | "Int.checked_add" | "Int.checked_sub" | "Int.checked_mul"
        );
        let expected_target = expected.and_then(|e| {
            if optional {
                e.layout()
                    .and_then(|id| self.types.enums[id].arguments.first().copied())
            } else {
                Some(e)
            }
        });
        if arity == 1 {
            let target = explicit_target
                .or_else(|| expected_target.and_then(Type::int_kind))
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        format!("{name} needs a target integer type: annotate the result or write {name}::<T>(...)"),
                    )
                })?;
            let (value, source) = match first {
                Some(value) => {
                    let kind = first_kind(self, &value)?;
                    (value, kind)
                }
                None => int_arg(self, &arguments[0], None)?,
            };
            let op = match name {
                "Int.convert" => {
                    if !source.fits_in(target) {
                        return Err(Diagnostic::new(
                            span,
                            format!(
                                "Int.convert from {} to {} could lose information; use Int.try_convert (checked) or Int.truncate (wrapping)",
                                source.name(),
                                target.name()
                            ),
                        ));
                    }
                    IntOp::Convert
                }
                "Int.truncate" => IntOp::Truncate,
                _ => {
                    let shape = option(self, Type::int(target))?;
                    IntOp::TryConvert {
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    }
                }
            };
            let ty = match op {
                IntOp::TryConvert { .. } => option(self, Type::int(target))?.result,
                _ => Type::int(target),
            };
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(Target::Int(op, source, target), vec![value]),
                ty,
            ));
        }
        // Two-operand arithmetic: both operands share the result's kind.
        let hint = explicit_target
            .or_else(|| expected_target.and_then(Type::int_kind))
            .map(Type::int);
        let (left, right) = match first {
            Some(left) => {
                let kind = first_kind(self, &left)?;
                let (right, _) = int_arg(self, &arguments[0], Some(Type::int(kind)))?;
                (left, right)
            }
            None if is_int_literal(&arguments[0]) && !is_int_literal(&arguments[1]) => {
                let (right, kind) = int_arg(self, &arguments[1], hint)?;
                let (left, _) = int_arg(self, &arguments[0], Some(Type::int(kind)))?;
                (left, right)
            }
            None => {
                let (left, kind) = int_arg(self, &arguments[0], hint)?;
                let (right, _) = int_arg(self, &arguments[1], Some(Type::int(kind)))?;
                (left, right)
            }
        };
        let kind = self
            .same_int(left.ty, right.ty, span)?
            .int_kind()
            .unwrap_or(IntKind::I64);
        let arith = match name.rsplit('_').next() {
            Some("add") => ArithOp::Add,
            Some("sub") => ArithOp::Sub,
            Some("mul") => ArithOp::Mul,
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unknown integer builtin {name}"),
                ));
            }
        };
        let (op, ty) = if name.starts_with("Int.wrapping_") {
            (IntOp::Wrapping(arith), Type::int(kind))
        } else if name.starts_with("Int.saturating_") {
            (IntOp::Saturating(arith), Type::int(kind))
        } else {
            let shape = option(self, Type::int(kind))?;
            (
                IntOp::Checked(arith, shape.some_tag, shape.none_tag),
                shape.result,
            )
        };
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        Ok(unit(
            ExprKind::Call(Target::Int(op, kind, kind), vec![left, right]),
            ty,
        ))
    }
    /// Check one float-builtin operand. `first` is the already checked method
    /// receiver; otherwise the remaining source argument is checked with the
    /// target's kind as a literal hint.
    pub(super) fn float_argument(
        &mut self,
        first: Option<Expr>,
        argument: Option<&ast::Expr>,
        hint: Option<crate::float::FloatKind>,
        name: &str,
    ) -> Result<(Expr, crate::float::FloatKind)> {
        let value = match first {
            Some(value) => value,
            None => {
                let argument = argument.expect("checked float builtin arity");
                self.expr_expected(argument, hint.map(Type::float))?
            }
        };
        match value.ty.float_kind() {
            Some(kind) => Ok((value, kind)),
            None if value.ty == Type::Never => Ok((value, crate::float::FloatKind::F64)),
            None => Err(Diagnostic::new(
                value.span,
                format!(
                    "{name} expects a floating-point value, found {}",
                    self.types.name(value.ty)
                ),
            )),
        }
    }
    /// Check the integer source of an integer -> float conversion.
    pub(super) fn int_argument(
        &mut self,
        first: Option<Expr>,
        argument: Option<&ast::Expr>,
        name: &str,
    ) -> Result<(Expr, crate::int::IntKind)> {
        let value = match first {
            Some(value) => value,
            None => {
                let argument = argument.expect("checked int builtin arity");
                self.expr_expected(argument, None)?
            }
        };
        match value.ty.int_kind() {
            Some(kind) => Ok((value, kind)),
            None if value.ty == Type::Never => Ok((value, crate::int::IntKind::I64)),
            None => Err(Diagnostic::new(
                value.span,
                format!(
                    "{name} expects an integer, found {}",
                    self.types.name(value.ty)
                ),
            )),
        }
    }
    /// Explicit float builtins and conversions. Every operation is unary; the
    /// receiver form is checked before these arguments and appears first.
    pub(super) fn float_call_with(
        &mut self,
        first: Option<Expr>,
        name: &str,
        explicit: Option<&[ast::Type]>,
        arguments: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        use crate::float::{FloatKind, FloatOp};
        let first_count = usize::from(first.is_some());
        if first_count + arguments.len() != 1 {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects 1 argument, found {}",
                    first_count + arguments.len()
                ),
            ));
        }
        let unit = |kind, ty| Expr {
            kind,
            ty,
            span,
            resource: None,
        };
        let option = |c: &mut Self, payload: Type| -> Result<crate::runtime_types::OptionShape> {
            let id = c
                .resolution
                .slice_options
                .get(&(span.start, span.end))
                .copied()
                .ok_or_else(|| {
                    Diagnostic::new(span, format!("{name} requires Option<T> in scope"))
                })?;
            c.types.option(id, payload, span)
        };
        // Fixed-result operations need no target annotation.
        let simple = match name {
            "Float.abs" => Some(FloatOp::Abs(FloatKind::F64)),
            "Float.sqrt" => Some(FloatOp::Sqrt(FloatKind::F64)),
            "Float.is_nan" => Some(FloatOp::IsNan(FloatKind::F64)),
            "Float.is_infinite" => Some(FloatOp::IsInfinite(FloatKind::F64)),
            "Float.is_finite" => Some(FloatOp::IsFinite(FloatKind::F64)),
            _ => None,
        };
        if let Some(base) = simple {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    format!("{name} takes no type arguments"),
                ));
            }
            let hint = expected.and_then(Type::float_kind);
            let (value, kind) = self.float_argument(first, arguments.first(), hint, name)?;
            let op = match base {
                FloatOp::Abs(_) => FloatOp::Abs(kind),
                FloatOp::Sqrt(_) => FloatOp::Sqrt(kind),
                FloatOp::IsNan(_) => FloatOp::IsNan(kind),
                FloatOp::IsInfinite(_) => FloatOp::IsInfinite(kind),
                FloatOp::IsFinite(_) => FloatOp::IsFinite(kind),
                _ => unreachable!(),
            };
            let ty = match op {
                FloatOp::IsNan(_) | FloatOp::IsInfinite(_) | FloatOp::IsFinite(_) => Type::Bool,
                _ => Type::float(kind),
            };
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(ExprKind::Call(Target::Float(op), vec![value]), ty));
        }
        if name == "print_float" {
            if explicit.is_some() {
                return Err(Diagnostic::new(span, "print_float takes no type arguments"));
            }
            let (value, kind) = self.float_argument(first, arguments.first(), None, name)?;
            self.require(IO | PANIC, span)?;
            return Ok(unit(
                ExprKind::Call(Target::PrintFloat(kind), vec![value]),
                Type::Unit,
            ));
        }
        if name == "Float.to_f64" {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    "Float.to_f64 takes no type arguments",
                ));
            }
            let hint = expected
                .and_then(Type::float_kind)
                .filter(|k| *k == FloatKind::F64);
            let (value, kind) = self.float_argument(first, arguments.first(), hint, name)?;
            if let Some(expected) = expected {
                self.expect(Type::float(FloatKind::F64), expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(Target::Float(FloatOp::ToF64(kind)), vec![value]),
                Type::float(FloatKind::F64),
            ));
        }
        if name == "Float.try_to_f32" {
            if explicit.is_some() {
                return Err(Diagnostic::new(
                    span,
                    "Float.try_to_f32 takes no type arguments",
                ));
            }
            let (value, kind) = self.float_argument(first, arguments.first(), None, name)?;
            let shape = option(self, Type::float(FloatKind::F32))?;
            let ty = shape.result;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(
                    Target::Float(FloatOp::TryToF32 {
                        source: kind,
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    }),
                    vec![value],
                ),
                ty,
            ));
        }
        let explicit_kind = match explicit {
            Some([ty]) => Some(self.ty(ty)?),
            Some(_) => {
                return Err(Diagnostic::new(
                    span,
                    format!("{name} takes one type argument"),
                ));
            }
            None => None,
        };
        if name == "Float.try_to_int" {
            if let Some(ty) = explicit_kind
                && ty.int_kind().is_none()
            {
                return Err(Diagnostic::new(
                    span,
                    "Float.try_to_int needs an integer type argument",
                ));
            }
            let target = explicit_kind
                .and_then(Type::int_kind)
                .or_else(|| {
                    expected.and_then(|e| {
                        e.layout()
                            .and_then(|id| self.types.enums[id].arguments.first().copied())
                            .and_then(Type::int_kind)
                    })
                })
                .ok_or_else(|| {
                    Diagnostic::new(
                        span,
                        "Float.try_to_int needs a target integer type: annotate the Option result or write Float.try_to_int::<i64>(...)",
                    )
                })?;
            let (value, source) = self.float_argument(first, arguments.first(), None, name)?;
            let shape = option(self, Type::int(target))?;
            let ty = shape.result;
            if let Some(expected) = expected {
                self.expect(ty, expected, span)?;
            }
            return Ok(unit(
                ExprKind::Call(
                    Target::Float(FloatOp::TryToInt {
                        source,
                        target,
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    }),
                    vec![value],
                ),
                ty,
            ));
        }
        // Integer -> float forms choose their target float from `::<T>` or the
        // expected type.
        let target = explicit_kind
            .and_then(Type::float_kind)
            .or_else(|| expected.and_then(Type::float_kind))
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "{name} needs a target float type: annotate the result or write {name}::<f32|f64>(...)"
                    ),
                )
            })?;
        if let Some(ty) = explicit_kind
            && ty.float_kind().is_none()
        {
            return Err(Diagnostic::new(
                span,
                format!("{name} needs an f32 or f64 type argument"),
            ));
        }
        let (value, source) = self.int_argument(first, arguments.first(), name)?;
        let (op, ty) = match name {
            "Float.from_int" => {
                if source.bits() > target.mantissa_bits() {
                    return Err(Diagnostic::new(
                        span,
                        format!(
                            "Float.from_int cannot represent every {} value exactly in {}; use Float.try_from_int (checked at runtime) or Float.from_int_rounded (documented rounding)",
                            source.name(),
                            target.name()
                        ),
                    ));
                }
                (FloatOp::FromInt { source, target }, Type::float(target))
            }
            "Float.from_int_rounded" => (
                FloatOp::FromIntRounded { source, target },
                Type::float(target),
            ),
            "Float.try_from_int" => {
                let shape = option(self, Type::float(target))?;
                (
                    FloatOp::TryFromInt {
                        source,
                        target,
                        some_tag: shape.some_tag,
                        none_tag: shape.none_tag,
                    },
                    shape.result,
                )
            }
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unknown float builtin {name}"),
                ));
            }
        };
        if let Some(expected) = expected {
            self.expect(ty, expected, span)?;
        }
        Ok(unit(ExprKind::Call(Target::Float(op), vec![value]), ty))
    }
    /// Checked UTF-8 text builtins. Construction is restricted to a literal or
    /// the fallible conversion from an owned byte buffer; arbitrary bytes are
    /// never treated as text without validation.
    pub(super) fn string_call(
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
        if name == "String.from" {
            if arguments.len() != 1 {
                return Err(Diagnostic::new(
                    span,
                    "String.from expects exactly one string literal",
                ));
            }
            let ast::ExprKind::String(text) = &arguments[0].kind else {
                return Err(Diagnostic::new(
                    arguments[0].span,
                    "String.from requires exactly one string literal; use String.from_utf8 for runtime bytes",
                ));
            };
            self.require(ALLOC | PANIC, span)?;
            let value = Expr {
                kind: ExprKind::BytesLiteral(text.as_bytes().to_vec()),
                ty: Type::String,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if arguments.is_empty() {
            return Err(Diagnostic::new(span, format!("{name} expects a receiver")));
        }
        let first = self.expr(&arguments[0])?;
        self.string_call_with(name, first, &arguments[1..], expected, span)
    }
    /// The checked receiver of a text builtin is already evaluated exactly
    /// once. `rest` contains only the remaining source arguments.
    pub(super) fn string_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = if matches!(name, "String.from_utf8" | "String.bytes") {
            0
        } else if matches!(name, "String.byte_at" | "String.scalar_at") {
            1
        } else if name == "String.substr" {
            2
        } else {
            0
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {wanted} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        let borrowed = matches!(
            name,
            "String.len"
                | "String.scalar_len"
                | "String.byte_at"
                | "String.scalar_at"
                | "String.as_bytes"
                | "String.as_str"
                | "String.as_mut_str"
                | "String.substr"
        );
        let first = if first.ty == Type::Never {
            return Ok(first);
        } else if borrowed {
            match first.ty {
                Type::Ref(p) | Type::RefMut(p) if self.types.pointees[p] == Type::String => first,
                _ => {
                    return Err(Diagnostic::new(
                        first.span,
                        format!(
                            "{name} expects a &String or &mut String, found {}; borrow an owned local with &name",
                            self.types.name(first.ty)
                        ),
                    ));
                }
            }
        } else if name == "String.from_utf8" {
            if first.ty != Type::Bytes {
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "String.from_utf8 consumes an owned Bytes value, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
            first
        } else if name == "String.bytes" {
            if first.ty != Type::String {
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "String.bytes consumes an owned String, found {}",
                        self.types.name(first.ty)
                    ),
                ));
            }
            first
        } else {
            return Err(Diagnostic::new(
                span,
                format!("unknown text builtin {name}"),
            ));
        };
        match name {
            "String.as_str" => self.text_view_from_expr(first, None, None, false, span, expected),
            "String.as_mut_str" => {
                if !matches!(first.ty, Type::RefMut(_)) {
                    return Err(Diagnostic::new(
                        first.span,
                        "String.as_mut_str needs an exclusive '&mut String'; borrow a 'let mut' String local with &mut name",
                    ));
                }
                self.text_view_from_expr(first, None, None, true, span, expected)
            }
            "String.substr" => self.text_view_from_expr(
                first,
                Some(&rest[0]),
                Some(&rest[1]),
                false,
                span,
                expected,
            ),
            "String.len" | "String.scalar_len" => {
                let op = if name == "String.len" {
                    StringOp::Len
                } else {
                    StringOp::ScalarLen
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(op), vec![first]),
                    ty: Type::I64,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.byte_at" => {
                let index = self.expr_expected(&rest[0], Some(Type::I64))?;
                self.expect(index.ty, Type::I64, index.span)?;
                self.require(PANIC, span)?;
                let ty = if index.ty == Type::Never {
                    Type::Never
                } else {
                    Type::I64
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(StringOp::ByteAt), vec![first, index]),
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.scalar_at" => {
                let index = self.expr_expected(&rest[0], Some(Type::I64))?;
                self.expect(index.ty, Type::I64, index.span)?;
                let option = self
                    .resolution
                    .slice_options
                    .get(&(span.start, span.end))
                    .copied()
                    .ok_or_else(|| {
                        Diagnostic::new(span, "String.scalar_at requires Option<Char> in scope")
                    })?;
                let shape = self.types.option(option, Type::Char, span)?;
                let op = StringOp::ScalarAt {
                    some_tag: shape.some_tag,
                    none_tag: shape.none_tag,
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(op), vec![first, index]),
                    ty: shape.result,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.from_utf8" => {
                let (ty, shape) = self.types.result_type(Type::String, Type::Bytes, span)?;
                let op = StringOp::FromUtf8 {
                    ok_tag: shape.ok_tag,
                    err_tag: shape.err_tag,
                };
                let value = Expr {
                    kind: ExprKind::Call(Target::String(op), vec![first]),
                    ty,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.as_bytes" => {
                self.require(ALLOC | PANIC, span)?;
                let value = Expr {
                    kind: ExprKind::Call(Target::String(StringOp::AsBytes), vec![first]),
                    ty: Type::Bytes,
                    span,
                    resource: None,
                };
                match expected {
                    Some(expected) => self.coerce(value, expected, span),
                    None => Ok(value),
                }
            }
            "String.bytes" => {
                let value = Expr {
                    kind: ExprKind::Call(Target::String(StringOp::IntoBytes), vec![first]),
                    ty: Type::Bytes,
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
                format!("unknown text builtin {name}"),
            )),
        }
    }
    pub(super) fn str_call(
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
        if arguments.is_empty() {
            return Err(Diagnostic::new(span, format!("{name} expects a receiver")));
        }
        let first = self.expr(&arguments[0])?;
        self.str_call_with(name, first, &arguments[1..], expected, span)
    }
    /// The checked receiver of a borrowed text builtin is already evaluated
    /// exactly once. A text view is a copyable shared descriptor, so reads do
    /// not move it and the owner's loan stays governed by the binding's last
    /// use.
    pub(super) fn str_call_with(
        &mut self,
        name: &str,
        first: Expr,
        rest: &[ast::Expr],
        expected: Option<Type>,
        span: Span,
    ) -> Result<Expr> {
        let wanted = match name {
            "Str.len"
            | "Str.scalar_len"
            | "Str.to_string"
            | "Str.make_ascii_uppercase"
            | "Str.make_ascii_lowercase" => 0,
            "Str.byte_at" | "Str.scalar_at" => 1,
            "Str.substr" | "Str.set_scalar" => 2,
            _ => {
                return Err(Diagnostic::new(
                    span,
                    format!("unknown borrowed text builtin {name}"),
                ));
            }
        };
        if rest.len() != wanted {
            return Err(Diagnostic::new(
                span,
                format!(
                    "{name} expects {wanted} argument(s) after its receiver, found {}",
                    rest.len()
                ),
            ));
        }
        if first.ty == Type::Never {
            return Ok(first);
        }
        if !first.ty.is_text() {
            return Err(Diagnostic::new(
                first.span,
                format!(
                    "{name} expects a borrowed &str text view, found {}; create one with String.as_str or String.substr",
                    self.types.name(first.ty)
                ),
            ));
        }
        if name == "Str.substr" {
            return self.text_view_from_expr(
                first,
                Some(&rest[0]),
                Some(&rest[1]),
                false,
                span,
                expected,
            );
        }
        if matches!(
            name,
            "Str.make_ascii_uppercase" | "Str.make_ascii_lowercase" | "Str.set_scalar"
        ) {
            if first.ty != Type::StrMut {
                return Err(Diagnostic::new(
                    first.span,
                    format!(
                        "{name} writes through an exclusive '&mut str' view, found {}; create one with String.as_mut_str(&mut s) or &mut view[start..end]",
                        self.types.name(first.ty)
                    ),
                ));
            }
            let (op, arguments) = if name == "Str.set_scalar" {
                // The scalar at byte offset `index` is replaced by `scalar`
                // only when both encode to the same number of UTF-8 bytes and
                // `index` is a scalar boundary; anything else panics, so the
                // view stays valid UTF-8 and keeps its length.
                self.require(PANIC, span)?;
                let index = self.expr_expected(&rest[0], Some(Type::I64))?;
                self.expect(index.ty, Type::I64, index.span)?;
                let scalar = self.expr_expected(&rest[1], Some(Type::Char))?;
                self.expect(scalar.ty, Type::Char, scalar.span)?;
                (StrOp::SetScalar, vec![first, index, scalar])
            } else if name == "Str.make_ascii_uppercase" {
                (StrOp::AsciiUpper, vec![first])
            } else {
                (StrOp::AsciiLower, vec![first])
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Str(op), arguments),
                ty: Type::Unit,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if name == "Str.to_string" {
            self.require(ALLOC | PANIC, span)?;
            let value = Expr {
                kind: ExprKind::Call(Target::Str(StrOp::ToString), vec![first]),
                ty: Type::String,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        if name == "Str.len" || name == "Str.scalar_len" {
            let op = if name == "Str.len" {
                StrOp::Len
            } else {
                StrOp::ScalarLen
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Str(op), vec![first]),
                ty: Type::I64,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let index = self.expr_expected(&rest[0], Some(Type::I64))?;
        self.expect(index.ty, Type::I64, index.span)?;
        if name == "Str.byte_at" {
            self.require(PANIC, span)?;
            let ty = if index.ty == Type::Never {
                Type::Never
            } else {
                Type::I64
            };
            let value = Expr {
                kind: ExprKind::Call(Target::Str(StrOp::ByteAt), vec![first, index]),
                ty,
                span,
                resource: None,
            };
            return match expected {
                Some(expected) => self.coerce(value, expected, span),
                None => Ok(value),
            };
        }
        let option = self
            .resolution
            .slice_options
            .get(&(span.start, span.end))
            .copied()
            .ok_or_else(|| Diagnostic::new(span, "Str.scalar_at requires Option<Char> in scope"))?;
        let shape = self.types.option(option, Type::Char, span)?;
        let op = StrOp::ScalarAt {
            some_tag: shape.some_tag,
            none_tag: shape.none_tag,
        };
        let value = Expr {
            kind: ExprKind::Call(Target::Str(op), vec![first, index]),
            ty: shape.result,
            span,
            resource: None,
        };
        match expected {
            Some(expected) => self.coerce(value, expected, span),
            None => Ok(value),
        }
    }
}
