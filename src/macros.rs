#[macro_export]
macro_rules! rules {
    (@rule $arena:ident [$($lhs:tt)*]: -> $($x:tt)+) => {
        $crate::Rule::Implies($crate::rules!(@logic $arena: $($lhs)*), $crate::rules!(@logic $arena: $($x)+))
    };
    (@rule $arena:ident [$($lhs:tt)*]: == $($x:tt)+) => {
        $crate::Rule::Equals($crate::rules!(@logic $arena: $($lhs)*), $crate::rules!(@logic $arena: $($x)+))
    };
    (@rule $arena:ident [$($lhs:tt)*]: $a:tt $($x:tt)+) => {
        $crate::rules!(@rule $arena [$($lhs)* $a]: $($x)+)
    };

    // Special cases: no `&` nor `|`
    (@logic $arena:ident: ! $a:tt) => {
        $crate::Logic::Atom($crate::Atom::new($arena.insert($a), false))
    };
    (@logic $arena:ident: $a:tt) => {
        $crate::Logic::Atom($crate::Atom::new($arena.insert($a), true))
    };
    (@logic $arena:ident: $($x:tt)+) => {
        $crate::rules!(@logic_atom $arena []: $($x)+)
    };
    (@logic_atom $arena:ident [$($lhs:tt)*]: ! $a:tt $($x:tt)*) => {
        $crate::rules!(@logic_check $arena [$($lhs)*; $crate::Logic::Atom($crate::Atom::new($arena.insert($a), false))]: $($x)*)
    };
    (@logic_atom $arena:ident [$($lhs:tt)*]: $a:tt $($x:tt)*) => {
        $crate::rules!(@logic_check $arena [$($lhs)*; $crate::Logic::Atom($crate::Atom::new($arena.insert($a), true))]: $($x)*)
    };
    (@logic_check $arena:ident [; $lhs:expr; $op:ident; $rhs:expr]: $($x:tt)*) => {
        $crate::rules!(@logic_op $arena [; $crate::Logic::$op([$lhs, $rhs])]: $($x)*)
    };
    (@logic_check $arena:ident [; $lhs:expr]: $($x:tt)*) => {
        $crate::rules!(@logic_op $arena [; $lhs]: $($x)*)
    };
    (@logic_op $arena:ident [; $lhs:expr]: & $($x:tt)+) => {
        $crate::rules!(@logic_atom $arena [; $lhs; and]: $($x)+)
    };
    (@logic_op $arena:ident [; $lhs:expr]: | $($x:tt)+) => {
        $crate::rules!(@logic_atom $arena [; $lhs; or]: $($x)+)
    };
    (@logic_op $arena:ident [; $lhs:expr]: ) => {
        $lhs
    };

    ($([$($x:tt)+])+) => {
        {
            let mut facts = $crate::Arena::new();
            let rules = [$($crate::rules!(@rule facts []: $($x)+)),+];
            $crate::Rules::new(facts, rules)
        }
    };
}

#[cfg(test)]
mod tests {
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
    pub enum Assumption {
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
    use crate::{CheckedRules, FactKB};
    use Assumption::*;

    #[test]
    fn test_large_input() {
        let rules = rules![
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
        ];

        let checked = CheckedRules::new(rules).unwrap();

        let [real, integer, imaginary] = vars!(checked, Real, Integer, Imaginary);

        let mut kb = FactKB::new(&checked);
        kb.assume_all([real, integer].map(crate::Atom::into_fuzzy_pair))
            .unwrap();

        assert_eq!(kb.get(imaginary), Some(false.into()));

        // test prerequisites
        assert!(kb
            .prereqs(Integer)
            .unwrap()
            .find(|x| *x == &Rational)
            .is_some());
    }
}
