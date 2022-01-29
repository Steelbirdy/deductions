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
