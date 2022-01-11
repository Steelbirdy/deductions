macro_rules! atom {
    ($arena:ident, $a:ident) => {
        $crate::Atom::new($arena.insert($a), true)
    };
    ($arena:ident, ! $a:ident) => {
        $crate::Atom::new($arena.insert($a), false)
    };
    ($arena:ident, $a:literal) => {
        $crate::Atom::new($arena.insert($a), true)
    };
    ($arena:ident, ! $a:literal) => {
        $crate::Atom::new($arena.insert($a), false)
    };
    ($arena:ident, $a:path) => {
        $crate::Atom::new($arena.insert($a), true)
    };
    ($arena:ident, ! $a:path) => {
        $crate::Atom::new($arena.insert($a), false)
    };
}

macro_rules! logic {
    // Special cases: no `&` nor `|`
    ($arena:ident, $a:tt) => {
        $crate::Logic::Atom(atom!($arena, $a))
    };
    ($arena:ident, ! $a:tt) => {
        $crate::Logic::Atom(atom!($arena, ! $a))
    };

    ($arena:ident, $($x:tt)+) => {
        logic!(@atom $arena []: $($x)+)
    };
    (@atom $arena:ident [$($lhs:tt)*]: ! $a:tt $($x:tt)*) => {
        logic!(@check $arena [$($lhs)*; logic!($arena, ! $a)]: $($x)*)
    };
    (@atom $arena:ident [$($lhs:tt)*]: $a:tt $($x:tt)*) => {
        logic!(@check $arena [$($lhs)*; logic!($arena, $a)]: $($x)*)
    };
    (@check $arena:ident [; $lhs:expr; $op:ident; $rhs:expr]: $($x:tt)*) => {
        logic!(@op $arena [; $crate::Logic::$op([$lhs, $rhs])]: $($x)*)
    };
    (@check $arena:ident [; $lhs:expr]: $($x:tt)*) => {
        logic!(@op $arena [; $lhs]: $($x)*)
    };
    (@op $arena:ident [; $lhs:expr]: & $($x:tt)+) => {
        logic!(@atom $arena [; $lhs; and]: $($x)+)
    };
    (@op $arena:ident [; $lhs:expr]: | $($x:tt)+) => {
        logic!(@atom $arena [; $lhs; or]: $($x)+)
    };
    (@op $arena:ident [; $lhs:expr]: ) => {
        $lhs
    };
}

macro_rules! rule {
    ($arena:ident, $($x:tt)+) => {
        rule!(@inner $arena []: $($x)+)
    };
    (@inner $arena:ident [$($lhs:tt)*]: -> $($x:tt)+) => {
        $crate::Rule::Implies(logic!($arena, $($lhs)*), logic!($arena, $($x)+))
    };
    (@inner $arena:ident [$($lhs:tt)*]: == $($x:tt)+) => {
        $crate::Rule::Equals(logic!($arena, $($lhs)*), logic!($arena, $($x)+))
    };
    (@inner $arena:ident [$($lhs:tt)*]: $a:tt $($x:tt)+) => {
        rule!(@inner $arena [$($lhs)* $a]: $($x)+)
    };
}

macro_rules! rules {
    (@inner $arena:ident [$(; $done:expr)+] []: ) => {
        [$($done),+]
    };
    (@inner $arena:ident [$($done:tt)*] [$($current:tt)+]: ; $($x:tt)*) => {
        rules!(@inner $arena [$($done)*; rule!($arena, $($current)+)] []: $($x)*)
    };
    (@inner $arena:ident [$($done:tt)*] [$($current:tt)*]: $a:tt $($x:tt)+) => {
        rules!(@inner $arena [$($done)*] [$($current)* $a]: $($x)+)
    };
    ($($x:tt)+) => {
        {
            let mut facts = $crate::Arena::new();
            let rules = rules!(@inner facts [] []: $($x)+);
            $crate::Rules::new(facts, rules)
        }
    };
}
