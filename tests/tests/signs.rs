mod simple;

use deductions::{rules, CheckedRules, FactKB, FuzzyBool};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Sign {
    Pos,
    Neg,
    Zero,
    NonZero,
    NonPos,
    NonNeg,
}

lazy_static::lazy_static! {
    pub static ref SIGN_RULES: CheckedRules<Sign> = {
        use Sign::*;

        CheckedRules::new(rules!(
            [Neg        -> !Zero & !Pos]
            [Pos        -> !Zero & !Neg]
            [NonNeg     == !Neg]
            [NonPos     == !Pos]
            [NonZero    == !Zero]
        )).unwrap()
    };
}

#[test]
fn test_assume_positive() {
    use Sign::*;
    use FuzzyBool::*;

    let mut kb = FactKB::new(&*SIGN_RULES);
    kb.assume(Pos, true).unwrap();

    assert_eq!(kb.get(Pos), Some(True));
    assert_eq!(kb.get(Neg), Some(False));
    assert_eq!(kb.get(Zero), Some(False));
    assert_eq!(kb.get(NonZero), Some(True));
    assert_eq!(kb.get(NonPos), Some(False));
    assert_eq!(kb.get(NonNeg), Some(True));
}

#[test]
fn test_assume_zero() {
    use Sign::*;
    use FuzzyBool::*;

    let mut kb = FactKB::new(&*SIGN_RULES);
    kb.assume(Zero, true).unwrap();

    assert_eq!(kb.get(Pos), Some(False));
    assert_eq!(kb.get(Neg), Some(False));
    assert_eq!(kb.get(Zero), Some(True));
    assert_eq!(kb.get(NonZero), Some(False));
    assert_eq!(kb.get(NonPos), Some(True));
    assert_eq!(kb.get(NonNeg), Some(True));
}

#[test]
fn test_assume_not_zero() {
    use Sign::*;
    use FuzzyBool::*;

    let mut kb = FactKB::new(&*SIGN_RULES);
    kb.assume(Zero, false).unwrap();

    assert_eq!(kb.get(Pos), None);
    assert_eq!(kb.get(Neg), None);
    assert_eq!(kb.get(Zero), Some(False));
    assert_eq!(kb.get(NonZero), Some(True));
    assert_eq!(kb.get(NonPos), None);
    assert_eq!(kb.get(NonNeg), None);
}
