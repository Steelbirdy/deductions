// TODO: Tests

#[macro_export]
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

#[macro_export]
macro_rules! logic {
    // Special cases: no `&` nor `|`
    ($arena:ident, $a:tt) => {
        $crate::Logic::Atom($crate::atom!($arena, $a))
    };
    ($arena:ident, ! $a:tt) => {
        $crate::Logic::Atom($crate::atom!($arena, ! $a))
    };

    ($arena:ident, $($x:tt)+) => {
        $crate::logic!(@atom $arena []: $($x)+)
    };
    (@atom $arena:ident [$($lhs:tt)*]: ! $a:tt $($x:tt)*) => {
        $crate::logic!(@check $arena [$($lhs)*; $crate::logic!($arena, ! $a)]: $($x)*)
    };
    (@atom $arena:ident [$($lhs:tt)*]: $a:tt $($x:tt)*) => {
        $crate::logic!(@check $arena [$($lhs)*; $crate::logic!($arena, $a)]: $($x)*)
    };
    (@check $arena:ident [; $lhs:expr; $op:ident; $rhs:expr]: $($x:tt)*) => {
        $crate::logic!(@op $arena [; $crate::Logic::$op([$lhs, $rhs])]: $($x)*)
    };
    (@check $arena:ident [; $lhs:expr]: $($x:tt)*) => {
        $crate::logic!(@op $arena [; $lhs]: $($x)*)
    };
    (@op $arena:ident [; $lhs:expr]: & $($x:tt)+) => {
        $crate::logic!(@atom $arena [; $lhs; and]: $($x)+)
    };
    (@op $arena:ident [; $lhs:expr]: | $($x:tt)+) => {
        $crate::logic!(@atom $arena [; $lhs; or]: $($x)+)
    };
    (@op $arena:ident [; $lhs:expr]: ) => {
        $lhs
    };
}

#[macro_export]
macro_rules! rule {
    ($arena:ident, $($x:tt)+) => {
        $crate::rule!(@inner $arena []: $($x)+)
    };
    (@inner $arena:ident [$($lhs:tt)*]: -> $($x:tt)+) => {
        $crate::Rule::Implies($crate::logic!($arena, $($lhs)*), $crate::logic!($arena, $($x)+))
    };
    (@inner $arena:ident [$($lhs:tt)*]: == $($x:tt)+) => {
        $crate::Rule::Equals($crate::logic!($arena, $($lhs)*), $crate::logic!($arena, $($x)+))
    };
    (@inner $arena:ident [$($lhs:tt)*]: $a:tt $($x:tt)+) => {
        $crate::rule!(@inner $arena [$($lhs)* $a]: $($x)+)
    };
}

#[macro_export]
macro_rules! rules {
    (@inner $arena:ident [$(; $done:expr)+] []: ) => {
        [$($done),+]
    };
    (@inner $arena:ident [$($done:tt)*] [$($current:tt)+]: ; $($x:tt)*) => {
        $crate::rules!(@inner $arena [$($done)*; $crate::rule!($arena, $($current)+)] []: $($x)*)
    };
    (@inner $arena:ident [$($done:tt)*] [$($current:tt)*]: $a:tt $($x:tt)+) => {
        $crate::rules!(@inner $arena [$($done)*] [$($current)* $a]: $($x)+)
    };
    ($($x:tt)+) => {
        {
            let mut facts = $crate::Arena::new();
            let rules = $crate::rules!(@inner facts [] []: $($x)+);
            $crate::Rules::new(facts, rules)
        }
    };
}
