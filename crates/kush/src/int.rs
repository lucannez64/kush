//! Fixed-width machine integers. Every integer occupies one 64-bit word:
//! signed kinds are stored sign-extended and unsigned kinds zero-extended
//! (`u64` uses the raw bit pattern). Arithmetic is checked for the kind's own
//! range in every build; explicit wrapping/saturating/checked operations and
//! conversions are separate builtins.
use crate::lexer::Kind;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum IntKind {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}
pub(crate) const ALL: [IntKind; 8] = [
    IntKind::I8,
    IntKind::I16,
    IntKind::I32,
    IntKind::I64,
    IntKind::U8,
    IntKind::U16,
    IntKind::U32,
    IntKind::U64,
];
impl IntKind {
    pub fn named(name: &str) -> Option<Self> {
        ALL.into_iter().find(|kind| kind.name() == name)
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
        }
    }
    /// Stable index used by the native runtime's integer conversion helpers.
    pub fn index(self) -> i64 {
        match self {
            Self::I8 => 0,
            Self::I16 => 1,
            Self::I32 => 2,
            Self::I64 => 3,
            Self::U8 => 4,
            Self::U16 => 5,
            Self::U32 => 6,
            Self::U64 => 7,
        }
    }
    pub fn bits(self) -> u32 {
        match self {
            Self::I8 | Self::U8 => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 => 32,
            Self::I64 | Self::U64 => 64,
        }
    }
    pub fn signed(self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }
    pub fn min(self) -> i128 {
        if self.signed() {
            -(1i128 << (self.bits() - 1))
        } else {
            0
        }
    }
    pub fn max(self) -> i128 {
        if self.signed() {
            (1i128 << (self.bits() - 1)) - 1
        } else {
            (1i128 << self.bits()) - 1
        }
    }
    /// Every value of `self` is a value of `target`.
    pub fn fits_in(self, target: IntKind) -> bool {
        self.min() >= target.min() && self.max() <= target.max()
    }
    /// Encode a mathematical value, if it is in range.
    pub fn encode(self, value: i128) -> Option<i64> {
        (self.min()..=self.max())
            .contains(&value)
            .then_some(value as u64 as i64)
    }
    /// The mathematical value of a stored word.
    pub fn decode(self, word: i64) -> i128 {
        if self.signed() {
            i128::from(word)
        } else {
            i128::from(word as u64)
        }
    }
    /// Two's-complement truncation to this width.
    pub fn wrap(self, value: i128) -> i64 {
        let bits = self.bits();
        let mask = if bits == 64 {
            u64::MAX as u128
        } else {
            (1u128 << bits) - 1
        };
        let low = (value as u128) & mask;
        let signed = if self.signed() && bits < 128 && low >> (bits - 1) & 1 == 1 {
            low as i128 - (1i128 << bits)
        } else {
            low as i128
        };
        signed as u64 as i64
    }
    pub fn saturate(self, value: i128) -> i64 {
        value.clamp(self.min(), self.max()) as u64 as i64
    }
}
/// Checked binary operation. `None` means a panic: overflow, division by
/// zero, or a shift amount outside `0..bits`. The shift amount is already
/// decoded by the caller from its own kind.
pub(crate) fn binary(kind: IntKind, op: &Kind, a: i64, b: i64, shift: i128) -> Option<i64> {
    let (x, y) = (kind.decode(a), kind.decode(b));
    let result = match op {
        Kind::Plus => x.checked_add(y)?,
        Kind::Minus => x.checked_sub(y)?,
        Kind::Star => x.checked_mul(y)?,
        Kind::Slash => {
            if y == 0 {
                return None;
            }
            x / y
        }
        Kind::Percent => {
            // MIN % -1 is reported as overflow, like MIN / -1.
            if y == 0 || (kind.signed() && x == kind.min() && y == -1) {
                return None;
            }
            x % y
        }
        Kind::Amp => return Some(a & b),
        Kind::Pipe => return Some(a | b),
        Kind::Caret => return Some(a ^ b),
        Kind::Shl | Kind::Shr => {
            if !(0..i128::from(kind.bits())).contains(&shift) {
                return None;
            }
            let amount = shift as u32;
            return Some(if *op == Kind::Shl {
                kind.wrap(x << amount)
            } else {
                kind.wrap(x >> amount)
            });
        }
        _ => unreachable!("checked integer operator"),
    };
    kind.encode(result)
}
pub(crate) fn compare(kind: IntKind, op: &Kind, a: i64, b: i64) -> bool {
    let (x, y) = (kind.decode(a), kind.decode(b));
    match op {
        Kind::Lt => x < y,
        Kind::Le => x <= y,
        Kind::Gt => x > y,
        Kind::Ge => x >= y,
        Kind::EqEq => x == y,
        Kind::Ne => x != y,
        _ => unreachable!("integer comparison"),
    }
}
/// Bitwise complement, kept in canonical form for the kind.
pub(crate) fn not(kind: IntKind, a: i64) -> i64 {
    kind.wrap(!kind.decode(a))
}
/// Arithmetic forms of the explicit integer builtins.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum IntOp {
    /// Lossless widening (checked statically).
    Convert,
    /// Range-checked conversion returning `Option`.
    TryConvert {
        some_tag: usize,
        none_tag: usize,
    },
    /// Two's-complement truncation to the target width.
    Truncate,
    Wrapping(ArithOp),
    Saturating(ArithOp),
    Checked(ArithOp, usize, usize),
    /// `Char.from_code`: a `u32` code point to `Option<Char>`.
    CharFromCode {
        some_tag: usize,
        none_tag: usize,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ArithOp {
    Add,
    Sub,
    Mul,
}
impl ArithOp {
    pub fn apply(self, a: i128, b: i128) -> Option<i128> {
        match self {
            Self::Add => a.checked_add(b),
            Self::Sub => a.checked_sub(b),
            Self::Mul => a.checked_mul(b),
        }
    }
}
/// Evaluate an explicit integer builtin. Returns `(present, word)`: `present`
/// is false for a `None` result of the Option-returning forms.
pub(crate) fn builtin(op: IntOp, source: IntKind, target: IntKind, args: &[i64]) -> (bool, i64) {
    let a = source.decode(args[0]);
    match op {
        IntOp::CharFromCode { .. } => match u32::try_from(a).ok().and_then(char::from_u32) {
            Some(ch) => (true, i64::from(u32::from(ch))),
            None => (false, 0),
        },
        IntOp::Convert => (true, target.encode(a).expect("lossless conversion")),
        IntOp::TryConvert { .. } => match target.encode(a) {
            Some(word) => (true, word),
            None => (false, 0),
        },
        IntOp::Truncate => (true, target.wrap(a)),
        IntOp::Wrapping(arith) | IntOp::Saturating(arith) | IntOp::Checked(arith, _, _) => {
            let b = source.decode(args[1]);
            // i128 overflow is only possible for u64 * u64, which saturates high.
            let exact = arith.apply(a, b);
            match op {
                IntOp::Wrapping(_) => (
                    true,
                    exact.map_or_else(|| target.wrap(a.wrapping_mul(b)), |v| target.wrap(v)),
                ),
                IntOp::Saturating(_) => (true, target.saturate(exact.unwrap_or(i128::MAX))),
                _ => match exact.and_then(|v| target.encode(v)) {
                    Some(word) => (true, word),
                    None => (false, 0),
                },
            }
        }
    }
}
