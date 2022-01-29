use tests::sympy::{knowledge_base, Fact::*};

use deductions::FuzzyBool::*;

#[test]
fn test_simple_extension() {
    let mut kb = knowledge_base();
    kb.assume(Integer, true).unwrap();

    assert_eq!(kb.get(Integer), Some(True));
    assert_eq!(kb.get(Rational), Some(True));
    assert_eq!(kb.get(Zero), None);
    assert_eq!(kb.get(Positive), None);
    assert_eq!(kb.get(Even), None);

    kb.assume(Zero, true).unwrap();
    assert_eq!(kb.get(Zero), Some(True));
    assert_eq!(kb.get(NonZero), Some(False));
    assert_eq!(kb.get(Positive), Some(False));
    assert_eq!(kb.get(NonNegative), Some(True));
    assert_eq!(kb.get(Even), Some(True));
    assert_eq!(kb.get(Prime), Some(False));
}
