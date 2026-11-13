//! Canonical arbitrary-precision nonnegative integers used by the logical kernel.
//! No machine-word or digit bound: kernel fuel, charged per limb touched, and
//! the source size limit bound the work and storage of numerals.
use std::{fmt, str::FromStr};

const BASE: u32 = 1_000_000_000;

/// Little-endian base-10^9 limbs. Zero has no limbs; positive values have a
/// nonzero last limb. Private storage makes all constructible values canonical.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct Natural {
    limbs: Vec<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidDecimal,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidDecimal => f.write_str("expected a nonempty ASCII decimal natural number"),
        }
    }
}
impl std::error::Error for Error {}

impl Natural {
    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }
    pub fn decimal_digits(&self) -> usize {
        self.limbs.last().map_or(1, |last| {
            (self.limbs.len() - 1) * 9 + last.ilog10() as usize + 1
        })
    }
    /// Kernel fuel is charged proportionally to the storage touched by numeric
    /// operations. This is not an instruction-accurate execution-time bound.
    pub(crate) fn work(&self) -> usize {
        self.limbs.len().max(1)
    }
    pub fn successor(&self) -> Self {
        let mut result = self.clone();
        let mut carry = true;
        for limb in &mut result.limbs {
            if *limb == BASE - 1 {
                *limb = 0;
            } else {
                *limb += 1;
                carry = false;
                break;
            }
        }
        if carry {
            result.limbs.push(1);
        }
        result
    }
    /// None at zero; there is no saturating subtraction in the proof kernel.
    pub fn predecessor(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let mut result = self.clone();
        for limb in &mut result.limbs {
            if *limb == 0 {
                *limb = BASE - 1;
            } else {
                *limb -= 1;
                break;
            }
        }
        while result.limbs.last() == Some(&0) {
            result.limbs.pop();
        }
        Some(result)
    }
    /// Convert a machine-representable natural. Compile-time array lengths use
    /// this only after every kernel computation has been checked; an
    /// out-of-range value is an explicit error, never a truncation.
    pub fn to_usize(&self) -> Option<usize> {
        let mut value = 0usize;
        for limb in self.limbs.iter().rev() {
            value = value.checked_mul(BASE as usize)?;
            value = value.checked_add(*limb as usize)?;
        }
        Some(value)
    }
}
impl FromStr for Natural {
    type Err = Error;
    fn from_str(text: &str) -> Result<Self, Error> {
        if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
            return Err(Error::InvalidDecimal);
        }
        let digits = text.trim_start_matches('0');
        let limbs = digits
            .as_bytes()
            .rchunks(9)
            .map(|chunk| {
                chunk
                    .iter()
                    .fold(0, |value, digit| value * 10 + u32::from(digit - b'0'))
            })
            .collect();
        Ok(Self { limbs })
    }
}
impl From<u64> for Natural {
    fn from(mut value: u64) -> Self {
        let mut limbs = Vec::new();
        while value != 0 {
            limbs.push((value % u64::from(BASE)) as u32);
            value /= u64::from(BASE);
        }
        Self { limbs }
    }
}
impl fmt::Display for Natural {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some((last, rest)) = self.limbs.split_last() else {
            return f.write_str("0");
        };
        write!(f, "{last}")?;
        for limb in rest.iter().rev() {
            write!(f, "{limb:09}")?;
        }
        Ok(())
    }
}
impl fmt::Debug for Natural {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
