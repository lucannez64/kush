//! IEEE-754 binary32/binary64 values. Every value occupies one 64-bit word:
//! `f64` stores its raw IEEE bits and `f32` stores its 32 bits zero-extended
//! in the low half. All arithmetic and comparisons are the ordinary IEEE
//! operations: division by zero produces an infinity (or NaN for `0/0`),
//! overflow produces an infinity, and NaN compares unequal to everything,
//! including itself. No float operation panics.
//!
//! Printing uses the shortest decimal representation that round-trips at the
//! value's own width, in plain (non-exponent) notation. Special values print
//! as `NaN`, `inf`, `-inf`, `0`, and `-0`.
use crate::{Diagnostic, Span, lexer::Kind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FloatKind {
    F32,
    F64,
}

impl FloatKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }
    /// Number of exact integer bits in the significand. This is the widest
    /// integer magnitude every value of which is exactly representable.
    pub fn mantissa_bits(self) -> u32 {
        match self {
            Self::F32 => 24,
            Self::F64 => 53,
        }
    }
    pub(crate) fn infinity_bits(self) -> u64 {
        match self {
            Self::F32 => 0x7f80_0000,
            Self::F64 => 0x7ff0_0000_0000_0000,
        }
    }
    pub(crate) fn sign_mask(self) -> u64 {
        match self {
            Self::F32 => 1 << 31,
            Self::F64 => 1 << 63,
        }
    }
    /// Decode a stored word into the value's own width.
    pub fn decode(self, word: i64) -> f64 {
        match self {
            Self::F32 => f64::from(f32::from_bits(word as u32)),
            Self::F64 => f64::from_bits(word as u64),
        }
    }
    /// Store an `f64` by narrowing to this kind. Only used where the caller
    /// already performed the checked/rounded `f32` conversion.
    fn encode(self, value: f64) -> i64 {
        match self {
            Self::F32 => (value as f32).to_bits() as i64,
            Self::F64 => value.to_bits() as i64,
        }
    }
}

/// Check and encode one float literal. A literal that overflows its contextual
/// kind is rejected; underflow to zero or a subnormal is ordinary IEEE
/// rounding and is accepted.
pub(crate) fn literal(
    text: &str,
    kind: FloatKind,
    span: Span,
) -> std::result::Result<i64, Diagnostic> {
    let value = text
        .parse::<f64>()
        .map_err(|_| Diagnostic::new(span, format!("malformed floating-point literal '{text}'")))?;
    if !value.is_finite() {
        return Err(Diagnostic::new(
            span,
            format!("floating-point literal is too large for {}", kind.name()),
        ));
    }
    match kind {
        FloatKind::F64 => Ok(value.to_bits() as i64),
        FloatKind::F32 => {
            let narrowed = value as f32;
            if !narrowed.is_finite() {
                return Err(Diagnostic::new(
                    span,
                    "floating-point literal is too large for f32 (its range is about 3.4e38); write it as f64 or scale it"
                        .to_string(),
                ));
            }
            Ok(narrowed.to_bits() as i64)
        }
    }
}

/// IEEE binary operation. No case panics or overflows.
pub(crate) fn binary(kind: FloatKind, op: &Kind, a: i64, b: i64) -> i64 {
    match kind {
        FloatKind::F32 => {
            let (x, y) = (f32::from_bits(a as u32), f32::from_bits(b as u32));
            let result = match op {
                Kind::Plus => x + y,
                Kind::Minus => x - y,
                Kind::Star => x * y,
                Kind::Slash => x / y,
                Kind::Percent => x % y,
                _ => unreachable!("checked float operator"),
            };
            result.to_bits() as i64
        }
        FloatKind::F64 => {
            let (x, y) = (f64::from_bits(a as u64), f64::from_bits(b as u64));
            let result = match op {
                Kind::Plus => x + y,
                Kind::Minus => x - y,
                Kind::Star => x * y,
                Kind::Slash => x / y,
                Kind::Percent => x % y,
                _ => unreachable!("checked float operator"),
            };
            result.to_bits() as i64
        }
    }
}

/// IEEE comparison. `==` is false and `!=` is true for NaN; ordered
/// comparisons are false when either operand is NaN.
pub(crate) fn compare(kind: FloatKind, op: &Kind, a: i64, b: i64) -> bool {
    let (x, y) = (kind.decode(a), kind.decode(b));
    match op {
        Kind::Lt => x < y,
        Kind::Le => x <= y,
        Kind::Gt => x > y,
        Kind::Ge => x >= y,
        Kind::EqEq => x == y,
        Kind::Ne => x != y,
        _ => unreachable!("float comparison"),
    }
}

/// IEEE negation flips the sign bit, including for zero and NaN payloads.
pub(crate) fn negate(kind: FloatKind, word: i64) -> i64 {
    (word as u64 ^ kind.sign_mask()) as i64
}

/// Arithmetic forms of the explicit float builtins.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FloatOp {
    Abs(FloatKind),
    Sqrt(FloatKind),
    IsNan(FloatKind),
    IsInfinite(FloatKind),
    IsFinite(FloatKind),
    /// Statically exact integer -> float conversion.
    FromInt {
        source: crate::int::IntKind,
        target: FloatKind,
    },
    /// Explicitly rounding integer -> float conversion (nearest, ties even).
    FromIntRounded {
        source: crate::int::IntKind,
        target: FloatKind,
    },
    /// Integer -> float, `Some` only when the value is exactly representable.
    TryFromInt {
        source: crate::int::IntKind,
        target: FloatKind,
        some_tag: usize,
        none_tag: usize,
    },
    /// Exact widening (or identity) to `f64`.
    ToF64(FloatKind),
    /// `f64 -> f32` (or identity) returning `None` on finite overflow.
    TryToF32 {
        source: FloatKind,
        some_tag: usize,
        none_tag: usize,
    },
    /// Truncating float -> integer conversion returning `None` when the
    /// truncated value is non-finite or outside the target range.
    TryToInt {
        source: FloatKind,
        target: crate::int::IntKind,
        some_tag: usize,
        none_tag: usize,
    },
}

/// Whether a mathematical integer (given as `i128`) is exactly representable
/// in a float with `mantissa_bits` fraction bits.
pub(crate) fn integer_is_exact(value: i128, mantissa_bits: u32) -> bool {
    let magnitude = value.unsigned_abs();
    if magnitude == 0 {
        return true;
    }
    let bits = 128 - magnitude.leading_zeros();
    if bits <= mantissa_bits {
        return true;
    }
    magnitude.trailing_zeros() >= bits - mantissa_bits
}

/// Truncate toward zero and range-check one float against an integer kind.
fn truncate_to_int(kind: crate::int::IntKind, value: f64) -> Option<i64> {
    if !value.is_finite() {
        return None;
    }
    let truncated = value.trunc();
    if kind.signed() {
        // Both bounds are exactly representable powers of two. The upper bound
        // is exclusive, so the f64 value 2^(bits-1) is correctly rejected even
        // though it is the rounding of i64::MAX.
        let low = -(2f64).powi(kind.bits() as i32 - 1);
        let high = (2f64).powi(kind.bits() as i32 - 1);
        if !(truncated >= low && truncated < high) {
            return None;
        }
        Some(truncated as i64)
    } else {
        let high = (2f64).powi(kind.bits() as i32);
        if !(truncated >= 0.0 && truncated < high) {
            return None;
        }
        // The value is in [0, 2^64), so this conversion is exact.
        Some((truncated as u64) as i64)
    }
}

/// Evaluate an explicit float builtin. Returns `(present, word)`; `present` is
/// false only for the `None` result of an Option-returning form.
pub(crate) fn builtin(op: FloatOp, args: &[i64]) -> (bool, i64) {
    match op {
        FloatOp::Abs(kind) => (true, (args[0] as u64 & !kind.sign_mask()) as i64),
        FloatOp::Sqrt(kind) => {
            let value = kind.decode(args[0]).sqrt();
            (true, kind.encode(value))
        }
        FloatOp::IsNan(kind) => (true, i64::from(kind.decode(args[0]).is_nan())),
        FloatOp::IsInfinite(kind) => (true, i64::from(kind.decode(args[0]).is_infinite())),
        FloatOp::IsFinite(kind) => (true, i64::from(kind.decode(args[0]).is_finite())),
        FloatOp::FromInt { source, target } | FloatOp::FromIntRounded { source, target } => {
            let value = source.decode(args[0]);
            (true, target.encode(value as f64))
        }
        FloatOp::TryFromInt {
            source,
            target,
            some_tag,
            none_tag,
        } => {
            let value = source.decode(args[0]);
            if integer_is_exact(value, target.mantissa_bits()) {
                (true, target.encode(value as f64))
            } else {
                let _ = (some_tag, none_tag);
                (false, 0)
            }
        }
        FloatOp::ToF64(source) => (
            true,
            match source {
                FloatKind::F32 => f64::from(f32::from_bits(args[0] as u32)).to_bits() as i64,
                FloatKind::F64 => args[0],
            },
        ),
        FloatOp::TryToF32 {
            source,
            some_tag,
            none_tag,
        } => {
            let _ = (some_tag, none_tag);
            let value = source.decode(args[0]);
            let narrowed = value as f32;
            // Finite overflow is rejected; NaN and infinities are represented,
            // and finite underflow to zero/subnormal is accepted.
            if value.is_finite() && !narrowed.is_finite() {
                (false, 0)
            } else {
                (true, narrowed.to_bits() as i64)
            }
        }
        FloatOp::TryToInt {
            source,
            target,
            some_tag,
            none_tag,
        } => {
            let _ = (some_tag, none_tag);
            match truncate_to_int(target, source.decode(args[0])) {
                Some(value) => (true, value),
                None => (false, 0),
            }
        }
    }
}

/// Shortest round-trip decimal in plain notation, matching the native C
/// runtime's spelling for every finite value, signed zero, and non-finite
/// value.
pub(crate) fn format(kind: FloatKind, word: i64) -> String {
    match kind {
        FloatKind::F32 => format!("{}", f32::from_bits(word as u32)),
        FloatKind::F64 => format!("{}", f64::from_bits(word as u64)),
    }
}
