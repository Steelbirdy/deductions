use std::cmp::Ordering;
use std::{fmt, ops};

#[derive(Debug, Copy, Clone, Hash)]
pub enum FuzzyBool {
    False,
    True,
    Unknown,
}

use FuzzyBool::*;

impl FuzzyBool {
    /// Returns `true` only if `self` is `True`.
    ///
    /// # Example
    /// ```
    /// # use deductions::FuzzyBool;
    /// assert!(FuzzyBool::True.is_true());
    /// assert!(!FuzzyBool::False.is_true());
    /// assert!(!FuzzyBool::Unknown.is_true());
    /// ```
    #[inline]
    pub const fn is_true(self) -> bool {
        matches!(self, True)
    }

    /// Returns `true` only if `self` is `False`.
    ///
    /// # Example
    /// ```
    /// # use deductions::FuzzyBool;
    /// assert!(!FuzzyBool::True.is_false());
    /// assert!(FuzzyBool::False.is_false());
    /// assert!(!FuzzyBool::Unknown.is_false());
    /// ```
    #[inline]
    pub const fn is_false(self) -> bool {
        matches!(self, False)
    }

    /// Returns `true` only if `self` is `Unknown`.
    ///
    /// # Example
    /// ```
    /// # use deductions::FuzzyBool;
    /// assert!(!FuzzyBool::True.is_unknown());
    /// assert!(!FuzzyBool::False.is_unknown());
    /// assert!(FuzzyBool::Unknown.is_unknown());
    /// ```
    #[inline]
    pub const fn is_unknown(self) -> bool {
        matches!(self, Unknown)
    }

    /// Checks for structural equality of `FuzzyBool`s.
    ///
    /// # Example
    /// ```
    /// # use deductions::FuzzyBool;
    /// assert!(FuzzyBool::True.is_same(FuzzyBool::True));
    /// assert!(FuzzyBool::Unknown.is_same(FuzzyBool::Unknown));
    /// assert!(!FuzzyBool::True.is_same(FuzzyBool::False));
    /// ```
    #[inline]
    pub const fn is_same(self, rhs: FuzzyBool) -> bool {
        matches!(
            (self, rhs),
            (True, True) | (False, False) | (Unknown, Unknown)
        )
    }

    /// Checks for equality of `FuzzyBool`s. Returns `Unknown` if either is `Unknown`.
    ///
    /// # Example
    /// ```
    /// # use deductions::FuzzyBool;
    /// assert!(FuzzyBool::True.equals(FuzzyBool::True).is_true());
    /// assert!(FuzzyBool::True.equals(FuzzyBool::False).is_false());
    /// assert!(FuzzyBool::True.equals(FuzzyBool::Unknown).is_unknown());
    /// ```
    #[inline]
    #[must_use]
    pub const fn equals(self, rhs: FuzzyBool) -> FuzzyBool {
        match (self, rhs) {
            (True, True) | (False, False) => True,
            (True, False) | (False, True) => False,
            _ => Unknown,
        }
    }

    /// Checks for inequality of `FuzzyBool`s. Returns `Unknown` if either is `Unknown`.
    ///
    /// # Example
    /// ```
    /// # use deductions::FuzzyBool;
    /// assert!(FuzzyBool::True.not_equals(FuzzyBool::True).is_false());
    /// assert!(FuzzyBool::True.not_equals(FuzzyBool::False).is_true());
    /// assert!(FuzzyBool::True.not_equals(FuzzyBool::Unknown).is_unknown());
    /// ```
    #[inline]
    #[must_use]
    pub const fn not_equals(self, rhs: FuzzyBool) -> FuzzyBool {
        match (self, rhs) {
            (True, False) | (False, True) => True,
            (True, True) | (False, False) => False,
            _ => Unknown,
        }
    }

    /// Logical conjunction
    #[inline]
    #[must_use]
    pub const fn and(self, rhs: FuzzyBool) -> FuzzyBool {
        match (self, rhs) {
            (True, True) => True,
            (False, _) | (_, False) => False,
            _ => Unknown,
        }
    }

    /// Logical disjunction
    #[inline]
    #[must_use]
    pub const fn or(self, rhs: FuzzyBool) -> FuzzyBool {
        match (self, rhs) {
            (False, False) => False,
            (True, _) | (_, True) => True,
            _ => Unknown,
        }
    }

    /// Logical exclusive disjunction
    #[inline]
    #[must_use]
    pub const fn xor(self, rhs: FuzzyBool) -> FuzzyBool {
        match (self, rhs) {
            (True, False) | (False, True) => True,
            (True, True) | (False, False) => False,
            _ => Unknown,
        }
    }

    /// Logical negation
    #[inline]
    #[must_use]
    pub const fn negate(self) -> FuzzyBool {
        match self {
            True => False,
            False => True,
            Unknown => Unknown,
        }
    }

    /// Implication using Kleene Logic.
    ///
    /// This is equivalent to `NOT(A) OR B`.
    #[inline]
    #[must_use]
    pub const fn kleene_implication(self, rhs: FuzzyBool) -> FuzzyBool {
        match (self, rhs) {
            (True, False) => False,
            (False, _) | (_, True) => True,
            _ => Unknown,
        }
    }

    /// Implication using Łukasiewicz Logic.
    ///
    /// The Łukasiewicz Ł3 has the same tables for AND, OR, and NOT as the Kleene logic used elsewhere,
    /// but differs in its definition of implication in that "unknown => unknown" is true.
    #[inline]
    #[must_use]
    pub const fn lukasiewicz_implication(self, rhs: FuzzyBool) -> FuzzyBool {
        match (self, rhs) {
            (True, False) => False,
            (Unknown, Unknown) => True,
            (False, _) | (_, True) => True,
            _ => Unknown,
        }
    }

    /// Compares two `FuzzyBool`s similarly to `bool`s, where `true` is greater than `false`.
    ///
    /// `Unknown` values cannot be compared and thus return `None`.
    #[inline]
    pub const fn compare(self, rhs: FuzzyBool) -> Option<Ordering> {
        match (self, rhs) {
            (Unknown, _) | (_, Unknown) => None,
            (True, True) | (False, False) => Some(Ordering::Equal),
            (True, False) => Some(Ordering::Greater),
            (False, True) => Some(Ordering::Less),
        }
    }

    #[inline]
    pub const fn as_bool(self) -> Option<bool> {
        match self {
            True => Some(true),
            False => Some(false),
            Unknown => None,
        }
    }
}

impl Default for FuzzyBool {
    #[inline]
    fn default() -> Self {
        False
    }
}

impl<B: Into<FuzzyBool> + Copy> PartialEq<B> for FuzzyBool {
    #[inline]
    fn eq(&self, other: &B) -> bool {
        self.equals((*other).into()).is_true()
    }
}

impl PartialEq<FuzzyBool> for bool {
    #[inline]
    fn eq(&self, other: &FuzzyBool) -> bool {
        *other == *self
    }
}

impl Eq for FuzzyBool {}

impl<B: Into<FuzzyBool> + Copy> PartialOrd<B> for FuzzyBool {
    #[inline]
    fn partial_cmp(&self, other: &B) -> Option<Ordering> {
        self.compare((*other).into())
    }

    #[inline]
    fn lt(&self, other: &B) -> bool {
        matches!((self, (*other).into()), (False, True))
    }

    #[inline]
    fn le(&self, other: &B) -> bool {
        matches!((self, (*other).into()), (False, _) | (_, True))
    }

    #[inline]
    fn gt(&self, other: &B) -> bool {
        matches!((self, (*other).into()), (True, False))
    }

    #[inline]
    fn ge(&self, other: &B) -> bool {
        matches!((self, (*other).into()), (True, _) | (_, False))
    }
}

impl PartialOrd<FuzzyBool> for bool {
    #[inline]
    fn partial_cmp(&self, other: &FuzzyBool) -> Option<Ordering> {
        other.partial_cmp(self)
    }

    #[inline]
    fn lt(&self, other: &FuzzyBool) -> bool {
        other.lt(self)
    }

    #[inline]
    fn le(&self, other: &FuzzyBool) -> bool {
        other.le(self)
    }

    #[inline]
    fn gt(&self, other: &FuzzyBool) -> bool {
        other.gt(self)
    }

    #[inline]
    fn ge(&self, other: &FuzzyBool) -> bool {
        other.ge(self)
    }
}

impl ops::Not for FuzzyBool {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        self.negate()
    }
}

macro_rules! bit_op_impl {
    ($op:ident, $name:ident, $func:ident, $asn:ident, $asn_func:ident) => {
        impl ops::$name for FuzzyBool {
            type Output = Self;

            #[inline]
            fn $func(self, rhs: FuzzyBool) -> Self::Output {
                self.$op(rhs)
            }
        }

        impl ops::$asn for FuzzyBool {
            #[inline]
            fn $asn_func(&mut self, rhs: FuzzyBool) {
                *self = self.$op(rhs);
            }
        }

        impl ops::$name<bool> for FuzzyBool {
            type Output = Self;

            #[inline]
            fn $func(self, rhs: bool) -> Self::Output {
                self.$op(rhs.into())
            }
        }

        impl ops::$asn<bool> for FuzzyBool {
            #[inline]
            fn $asn_func(&mut self, rhs: bool) {
                *self = self.$op(rhs.into());
            }
        }

        impl ops::$name<FuzzyBool> for bool {
            type Output = FuzzyBool;

            #[inline]
            fn $func(self, rhs: FuzzyBool) -> Self::Output {
                rhs.$op(self.into())
            }
        }
    };
}

bit_op_impl!(and, BitAnd, bitand, BitAndAssign, bitand_assign);
bit_op_impl!(or, BitOr, bitor, BitOrAssign, bitor_assign);
bit_op_impl!(xor, BitXor, bitxor, BitXorAssign, bitxor_assign);

impl fmt::Display for FuzzyBool {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            True => "true",
            False => "false",
            Unknown => "unknown",
        };
        f.write_str(s)
    }
}

impl From<bool> for FuzzyBool {
    #[inline]
    fn from(b: bool) -> Self {
        if b {
            True
        } else {
            False
        }
    }
}

impl From<Option<bool>> for FuzzyBool {
    #[inline]
    fn from(b: Option<bool>) -> Self {
        b.map_or(Unknown, |b| b.into())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct UnknownError;

impl TryFrom<FuzzyBool> for bool {
    type Error = UnknownError;

    #[inline]
    fn try_from(value: FuzzyBool) -> Result<Self, Self::Error> {
        match value {
            True => Ok(true),
            False => Ok(false),
            Unknown => Err(UnknownError),
        }
    }
}

impl<'a> ops::Not for &'a FuzzyBool {
    type Output = <FuzzyBool as ops::Not>::Output;

    #[inline]
    fn not(self) -> Self::Output {
        FuzzyBool::not(*self)
    }
}

macro_rules! forward_ref_impl {
    (impl $imp:ident, $func:ident for $T:ty, $U:ty) => {
        impl<'a> ops::$imp<$U> for &'a $T {
            type Output = <$T as ops::$imp<$U>>::Output;

            #[inline]
            fn $func(self, rhs: $U) -> Self::Output {
                ops::$imp::$func(*self, rhs)
            }
        }

        impl<'a> ops::$imp<&'a $U> for $T {
            type Output = <$T as ops::$imp<$U>>::Output;

            #[inline]
            fn $func(self, rhs: &'a $U) -> Self::Output {
                ops::$imp::$func(self, *rhs)
            }
        }

        impl<'a, 'b> ops::$imp<&'b $U> for &'a $T {
            type Output = <$T as ops::$imp<$U>>::Output;

            #[inline]
            fn $func(self, rhs: &'b $U) -> Self::Output {
                ops::$imp::$func(*self, *rhs)
            }
        }
    };
}

forward_ref_impl!(impl BitAnd, bitand for FuzzyBool, FuzzyBool);
forward_ref_impl!(impl BitOr, bitor for FuzzyBool, FuzzyBool);
forward_ref_impl!(impl BitXor, bitxor for FuzzyBool, FuzzyBool);

forward_ref_impl!(impl BitAnd, bitand for FuzzyBool, bool);
forward_ref_impl!(impl BitOr, bitor for FuzzyBool, bool);
forward_ref_impl!(impl BitXor, bitxor for FuzzyBool, bool);

forward_ref_impl!(impl BitAnd, bitand for bool, FuzzyBool);
forward_ref_impl!(impl BitOr, bitor for bool, FuzzyBool);
forward_ref_impl!(impl BitXor, bitxor for bool, FuzzyBool);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_fuzzy_eq {
        ($a:expr, $b:expr) => {
            assert!($a.is_same($b))
        };
    }

    const T: FuzzyBool = FuzzyBool::True;
    const F: FuzzyBool = FuzzyBool::False;
    const U: FuzzyBool = FuzzyBool::Unknown;

    #[test]
    fn test_fuzzy_not() {
        assert_fuzzy_eq!(!T, F);
        assert_fuzzy_eq!(!F, T);
        assert_fuzzy_eq!(!U, U);
    }

    #[test]
    fn test_fuzzy_and() {
        assert_fuzzy_eq!(T & T, T);
        assert_fuzzy_eq!(T & F, F);
        assert_fuzzy_eq!(T & U, U);
        assert_fuzzy_eq!(F & F, F);
        assert_fuzzy_eq!(F & U, F);
        assert_fuzzy_eq!(U & U, U);
        assert_fuzzy_eq!(T & F & U, F);
    }

    #[test]
    fn test_fuzzy_or() {
        assert_fuzzy_eq!(T | T, T);
        assert_fuzzy_eq!(T | F, T);
        assert_fuzzy_eq!(T | U, T);
        assert_fuzzy_eq!(F | F, F);
        assert_fuzzy_eq!(F | U, U);
        assert_fuzzy_eq!(U | U, U);
        assert_fuzzy_eq!(T | F | U, T);
    }

    #[test]
    fn test_fuzzy_xor() {
        assert_fuzzy_eq!(T ^ T, F);
        assert_fuzzy_eq!(T ^ F, T);
        assert_fuzzy_eq!(T ^ U, U);
        assert_fuzzy_eq!(F ^ F, F);
        assert_fuzzy_eq!(F ^ U, U);
        assert_fuzzy_eq!(U ^ U, U);
        assert_fuzzy_eq!(T ^ F ^ U, U);
    }

    #[test]
    fn test_kleene_implication() {
        macro_rules! check {
            ($a:ident -> $b:ident == $c:ident) => {
                assert_fuzzy_eq!($a.kleene_implication($b), $c)
            };
        }

        check!(T -> T == T);
        check!(T -> F == F);
        check!(T -> U == U);
        check!(F -> F == T);
        check!(F -> U == T);
        check!(U -> U == U);
    }

    #[test]
    fn test_lukasiewicz_implication() {
        macro_rules! check {
            ($a:ident -> $b:ident == $c:ident) => {
                assert_fuzzy_eq!($a.lukasiewicz_implication($b), $c)
            };
        }

        check!(T -> T == T);
        check!(T -> F == F);
        check!(T -> U == U);
        check!(F -> F == T);
        check!(F -> U == T);
        check!(U -> U == T);
    }

    #[test]
    fn test_fuzzy_compare() {
        use Ordering::*;

        assert_eq!(T.compare(T), Some(Equal));
        assert_eq!(T.compare(F), Some(Greater));
        assert_eq!(T.compare(U), None);
        assert_eq!(F.compare(F), Some(Equal));
        assert_eq!(F.compare(U), None);
        assert_eq!(U.compare(U), None);
    }
}
