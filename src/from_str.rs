use crate::Arena;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::str::FromStr;

#[cfg(test)]
#[macro_use]
mod tests {
    use super::*;

    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
    pub enum NumberType {
        Real,
        Rational,
        Integer,
        Irrational,
        Complex,
        ExtendedReal,
        Finite,
        Infinite,
    }

    impl FromStr for NumberType {
        type Err = String;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(match s {
                "real" => Self::Real,
                "rational" => Self::Rational,
                "integer" => Self::Integer,
                "irrational" => Self::Irrational,
                "complex" => Self::Complex,
                "extended_real" => Self::ExtendedReal,
                "finite" => Self::Finite,
                "infinite" => Self::Infinite,
                _ => return Err(s.to_string()),
            })
        }
    }
}

pub mod rule {
    use super::{logic::ParseLogicError, *};
    use crate::{rules::Rule, Logic};

    #[derive(Debug)]
    pub enum ParseRuleError<E> {
        ParseLogic(ParseLogicError<E>),
        Empty,
        UnexpectedEnd(&'static str),
        NoOperator,
        MultipleOperators,
    }

    #[derive(Copy, Clone)]
    enum Operator {
        Implies,
        Equals,
    }

    impl Operator {
        const OP_CHARS: &'static [char] = &['-', '>', '='];

        fn try_from_str(s: &str) -> Option<Self> {
            Some(match s {
                "->" => Self::Implies,
                "==" => Self::Equals,
                _ => return None,
            })
        }
    }

    macro_rules! rule_from_str {
        ($name:ident, $T:ty, $err:ty, |$s:ident: $s_ty:ty|) => {
            pub fn $name(arena: &mut Arena<$T>, $s: $s_ty) -> Result<Self, ParseRuleError<$err>> {
                let mut ch = $s
                    .char_indices()
                    .filter(|(_, c)| Operator::OP_CHARS.contains(c))
                    .filter_map(|(i, _)| Operator::try_from_str(&$s[i..=i + 1]).map(|op| (i, op)));

                let (op_i, op) = ch.next().ok_or(ParseRuleError::NoOperator)?;

                if $s.len() - op_i < 2 {
                    return Err(ParseRuleError::UnexpectedEnd("right-hand side of rule"));
                }

                if ch.next().is_some() {
                    return Err(ParseRuleError::MultipleOperators);
                }

                let lhs = Logic::$name(arena, &$s[..op_i])?;
                let rhs = Logic::$name(arena, &$s[op_i + 2..].trim_start())?;

                match op {
                    Operator::Implies => Ok(Self::Implies(lhs, rhs)),
                    Operator::Equals => Ok(Self::Equals(lhs, rhs)),
                }
            }
        };
    }

    impl<T: Eq + Hash + FromStr> Rule<T> {
        rule_from_str!(from_str, T, T::Err, |s: &str|);
    }

    impl<'a> Rule<&'a str> {
        rule_from_str!(str_from_str, &'a str, std::convert::Infallible, |s: &'a str|);
    }

    impl<E> fmt::Display for ParseRuleError<E>
    where
        E: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::ParseLogic(err) => fmt::Display::fmt(err, f),
                Self::Empty => f.write_str("cannot parse empty string into `Rule`"),
                Self::UnexpectedEnd(expected) => {
                    write!(f, "unexpected end of input: expected {}", expected)
                }
                Self::NoOperator => {
                    f.write_str("rules must use a rule operator (ex. '->' or '==')")
                }
                Self::MultipleOperators => f.write_str("too many rule operators"),
            }
        }
    }

    impl<E> Error for ParseRuleError<E>
    where
        E: Error + 'static,
    {
        fn source(&self) -> Option<&(dyn Error + 'static)> {
            match self {
                Self::ParseLogic(err) => Some(err),
                _ => None,
            }
        }
    }

    impl<E> From<ParseLogicError<E>> for ParseRuleError<E> {
        fn from(err: ParseLogicError<E>) -> Self {
            ParseRuleError::ParseLogic(err)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::super::tests::NumberType;
        use super::*;

        #[test]
        fn test_rule_from_str() {
            use NumberType::*;

            let arena = &mut Arena::new();

            let parse = |arena: &mut Arena<NumberType>, s: &str| Rule::from_str(arena, s).unwrap();

            assert_eq!(
                parse(arena, "integer -> rational"),
                rule!(arena, Integer -> Rational)
            );
            assert_eq!(
                parse(arena, "rational -> real"),
                rule!(arena, Rational -> Real)
            );
            assert_eq!(
                parse(arena, "real -> complex"),
                rule!(arena, Real -> Complex)
            );
            assert_eq!(
                parse(arena, "extended_real -> real | infinite"),
                rule!(arena, ExtendedReal -> Real | Infinite)
            );
            assert_eq!(
                parse(arena, "real == extended_real & finite"),
                rule!(arena, Real == ExtendedReal & Finite)
            );
            assert_eq!(
                parse(arena, "irrational == real & !rational"),
                rule!(arena, Irrational == Real & !Rational)
            );
            assert_eq!(
                parse(arena, "infinite == !finite"),
                rule!(arena, Infinite == !Finite)
            );
        }
    }
}

pub mod logic {
    use super::{atom::ParseAtomError, *};
    use crate::{Atom, Logic};

    #[derive(Debug)]
    pub enum ParseLogicError<E> {
        ParseAtom(ParseAtomError<E>),
        Empty,
        UnexpectedSymbol(&'static str, String),
        UnexpectedEnd,
    }

    #[derive(Copy, Clone)]
    enum Operator {
        And,
        Or,
    }

    impl Operator {
        fn try_from_str(s: &str) -> Option<Self> {
            Some(match s {
                "&" => Self::And,
                "|" => Self::Or,
                _ => return None,
            })
        }
    }

    macro_rules! logic_from_str {
        ($name:ident, $T:ty, $err:ty, |$s:ident: $s_ty:ty|) => {
            pub fn $name(arena: &mut Arena<$T>, $s: $s_ty) -> Result<Self, ParseLogicError<$err>> {
                let mut parts = $s.split_whitespace();

                let a = parts.next().ok_or(ParseLogicError::Empty)?;

                let mut lhs = Logic::Atom(Atom::$name(arena, a)?);

                while let Some(op) = parts.next() {
                    let op = Operator::try_from_str(op).ok_or_else(|| {
                        ParseLogicError::UnexpectedSymbol("operator", op.to_string())
                    })?;

                    let b = parts.next().ok_or(ParseLogicError::UnexpectedEnd)?;

                    let rhs = Atom::$name(arena, b)?;
                    let operands = [lhs, Logic::Atom(rhs)];

                    lhs = match op {
                        Operator::And => Logic::and(operands),
                        Operator::Or => Logic::or(operands),
                    };
                }

                Ok(lhs)
            }
        };
    }

    impl<T: Eq + Hash + FromStr> Logic<T> {
        logic_from_str!(from_str, T, T::Err, |s: &str|);
    }

    impl<'a> Logic<&'a str> {
        logic_from_str!(str_from_str, &'a str, std::convert::Infallible, |s: &'a str|);
    }

    impl<E> fmt::Display for ParseLogicError<E>
    where
        E: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::ParseAtom(err) => fmt::Display::fmt(err, f),
                Self::Empty => f.write_str("cannot parse empty string into `Logic`"),
                Self::UnexpectedSymbol(expected, found) => {
                    write!(
                        f,
                        "unexpected symbol: expected {}, found {}",
                        expected, found
                    )
                }
                Self::UnexpectedEnd => {
                    f.write_str("unexpected end of input: cannot parse incomplete expression")
                }
            }
        }
    }

    impl<E> Error for ParseLogicError<E>
    where
        E: Error + 'static,
    {
        fn source(&self) -> Option<&(dyn Error + 'static)> {
            match self {
                Self::ParseAtom(err) => Some(err),
                _ => None,
            }
        }
    }

    impl<E> From<ParseAtomError<E>> for ParseLogicError<E> {
        fn from(err: ParseAtomError<E>) -> Self {
            Self::ParseAtom(err)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::super::tests::NumberType;
        use super::*;

        #[test]
        fn test_logic_from_str() {
            use NumberType::*;

            let arena = &mut Arena::new();

            let parse = |arena: &mut Arena<NumberType>, s: &str| Logic::from_str(arena, s).unwrap();

            assert_eq!(
                parse(arena, "real & rational"),
                logic!(arena, Real & Rational)
            );
            assert_eq!(
                parse(arena, "!integer & rational"),
                logic!(arena, !Integer & Rational)
            );
            assert_eq!(
                parse(arena, "real | !integer & rational"),
                logic!(arena, Real | !Integer & Rational)
            );
        }
    }
}

pub mod atom {
    use super::*;
    use crate::Atom;

    #[derive(Debug)]
    pub enum ParseAtomError<E> {
        ParseValue(E),
        BangSpace,
        Empty,
    }

    macro_rules! atom_from_str {
        ($name:ident, $T:ty, $err:ty, |$s:ident: $s_ty:ty| $parse_expr:expr) => {
            pub fn $name(arena: &mut Arena<$T>, $s: $s_ty) -> Result<Self, ParseAtomError<$err>> {
                let ($s, truth_value) = if let Some($s) = $s.strip_prefix('!') {
                    if $s.is_empty() {
                        return Err(ParseAtomError::BangSpace);
                    }
                    ($s, false)
                } else if $s.is_empty() {
                    return Err(ParseAtomError::Empty);
                } else {
                    ($s, true)
                };

                let id = arena.insert($parse_expr);

                Ok(Self::new(id, truth_value))
            }
        };
    }

    impl<T: Eq + Hash + FromStr> Atom<T> {
        atom_from_str!(from_str, T, T::Err, |s: &str| s.parse::<T>()?);
    }

    impl<'a> Atom<&'a str> {
        atom_from_str!(
            str_from_str,
            &'a str,
            std::convert::Infallible,
            |s: &'a str| s
        );
    }

    impl<E> fmt::Display for ParseAtomError<E>
    where
        E: fmt::Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::ParseValue(err) => fmt::Display::fmt(err, f),
                Self::BangSpace => f.write_str("do not put a space after `!`"),
                Self::Empty => f.write_str("cannot parse empty string into `Atom`"),
            }
        }
    }

    impl<E> Error for ParseAtomError<E>
    where
        E: Error + 'static,
    {
        fn source(&self) -> Option<&(dyn Error + 'static)> {
            match self {
                Self::ParseValue(err) => Some(err),
                _ => None,
            }
        }
    }

    impl<E> From<E> for ParseAtomError<E> {
        fn from(err: E) -> Self {
            Self::ParseValue(err)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::super::tests::NumberType;
        use super::*;

        #[test]
        fn test_atom_from_str() {
            use NumberType::*;

            let arena = &mut Arena::new();

            let parse = |arena: &mut Arena<NumberType>, s: &str| {
                Atom::<NumberType>::from_str(arena, s).unwrap()
            };

            assert_eq!(parse(arena, "real"), atom!(arena, Real));
            assert_eq!(parse(arena, "!real"), atom!(arena, !Real));
            assert_eq!(parse(arena, "rational"), atom!(arena, Rational));
            assert_eq!(parse(arena, "!rational"), atom!(arena, !Rational));
            assert_eq!(parse(arena, "integer"), atom!(arena, Integer));
            assert_eq!(parse(arena, "!integer"), atom!(arena, !Integer));
        }
    }
}
