macro_rules! fill_arena {
    ($arena:ident, $($sym:expr),+ $(,)?) => {
        {
            [$($crate::Atom::new($arena.insert($sym), true)),+]
        }
    };
}
