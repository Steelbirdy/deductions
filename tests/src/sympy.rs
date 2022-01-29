use deductions::{rules, CheckedRules, FactKB};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Fact {
    Commutative,
    Complex,
    Imaginary,
    Real,
    Integer,
    Odd,
    Even,
    Prime,
    Composite,
    Zero,
    NonZero,
    Rational,
    Algebraic,
    Transcendental,
    Irrational,
    Finite,
    Infinite,
    Negative,
    NonNegative,
    Positive,
    NonPositive,
    Hermitian,
    AntiHermitian,
    NonInteger,
    ExtendedReal,
    ExtendedNegative,
    ExtendedNonNegative,
    ExtendedPositive,
    ExtendedNonPositive,
    ExtendedNonZero,
}

lazy_static::lazy_static! {
    pub static ref SYMPY_RULES: CheckedRules<Fact> = {
        use Fact::*;

        CheckedRules::new(rules![
            [Integer                -> Rational]
            [Rational               -> Real]
            [Rational               -> Algebraic]
            [Algebraic              -> Complex]
            [Transcendental         == Complex & !Algebraic]
            [Real                   -> Hermitian]
            [Imaginary              -> Complex]
            [Imaginary              -> AntiHermitian]
            [ExtendedReal           -> Commutative]
            [Complex                -> Commutative]
            [Complex                -> Finite]

            [Odd                    == Integer & !Even]
            [Even                   == Integer & !Odd]

            [Real                   -> Complex]
            [ExtendedReal           -> Real | Infinite]
            [Real                   == ExtendedReal & Finite]

            [ExtendedReal           == ExtendedNegative | Zero | ExtendedPositive]
            [ExtendedNegative       == ExtendedNonPositive & ExtendedNonZero]
            [ExtendedPositive       == ExtendedNonNegative & ExtendedNonZero]

            [ExtendedNonPositive    == ExtendedReal & !ExtendedPositive]
            [ExtendedNonNegative    == ExtendedReal & !ExtendedNegative]

            [Real                   == Negative | Zero | Positive]
            [Negative               == NonPositive & NonZero]
            [Positive               == NonNegative & NonZero]

            [NonPositive            == Real & !Positive]
            [NonNegative            == Real & !Negative]

            [Positive               == ExtendedPositive & Finite]
            [Negative               == ExtendedNegative & Finite]
            [NonPositive            == ExtendedNonPositive & Finite]
            [NonNegative            == ExtendedNonNegative & Finite]
            [NonZero                == ExtendedNonZero & Finite]

            [Zero                   -> Even & Finite]
            [Zero                   == ExtendedNonNegative & ExtendedNonPositive]
            [Zero                   == NonNegative & NonPositive]
            [NonZero                -> Real]

            [Prime                  -> Integer & Positive]
            [Composite              -> Integer & Positive & !Prime]
            [!Composite             -> !Positive | !Even | Prime]

            [Irrational             == Real & !Rational]

            [Imaginary              -> !ExtendedReal]

            [Infinite               == !Finite]
            [NonInteger             == ExtendedReal & !Integer]
            [ExtendedNonZero        == ExtendedReal & !Zero]
        ]).unwrap()
    };
}

pub fn knowledge_base() -> FactKB<'static, Fact> {
    FactKB::new(&*SYMPY_RULES)
}
