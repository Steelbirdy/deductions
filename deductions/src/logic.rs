use crate::{Atom, FuzzyBool};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops;

pub enum Logic<T> {
    Atom(Atom<T>),
    Bool(FuzzyBool),
    And(And<Logic<T>>),
    Or(Or<Logic<T>>),
}

impl<T> Logic<T> {
    pub const TRUE: Self = Logic::Bool(FuzzyBool::True);
    pub const FALSE: Self = Logic::Bool(FuzzyBool::False);

    pub fn and(args: impl IntoIterator<Item = Logic<T>>) -> Self {
        And::new(args).simplify()
    }

    pub fn or(args: impl IntoIterator<Item = Logic<T>>) -> Self {
        Or::new(args).simplify()
    }

    fn cmp_atoms_first(&self, other: &Self) -> Ordering {
        use Logic::*;

        match (self, other) {
            (Atom(x), Atom(y)) => x.cmp(y),
            (Atom(_), _) => Ordering::Less,
            (Bool(_), Atom(_)) => Ordering::Greater,
            (And(x), And(y)) => x.cmp_atoms_first(y),
            (Or(x), Or(y)) => x.cmp_atoms_first(y),
            // The rest is arbitrary because we only care about `Atom`s being first.
            (Bool(x), Bool(y)) => x.partial_cmp(y).unwrap_or(Ordering::Equal),
            (Bool(_), _) | (And(_), Or(_)) => Ordering::Less,
            (And(_), _) | (Or(_), _) => Ordering::Greater,
        }
    }

    fn negate(&mut self) {
        use Logic::*;

        match self {
            Atom(x) => x.negate(),
            Bool(x) => *x = !*x,
            And(x) => {
                x.negate();
                *self = Logic::or(x.0.drain(..));
            }
            Or(x) => {
                x.negate();
                *self = Logic::and(x.0.drain(..));
            }
        }
    }

    fn expand(self) -> Self {
        use Logic::*;

        match self {
            And(x) => x.expand(),
            _ => self,
        }
    }
}

impl<T> ops::Not for Logic<T> {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        self.negate();
        self
    }
}

impl<T> fmt::Debug for Logic<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Logic::*;

        match self {
            Atom(x) => f.debug_tuple("Atom").field(x).finish(),
            Bool(x) => f.debug_tuple("Bool").field(x).finish(),
            And(x) => f.debug_tuple("And").field(x).finish(),
            Or(x) => f.debug_tuple("Or").field(x).finish(),
        }
    }
}

impl<T> Clone for Logic<T> {
    fn clone(&self) -> Self {
        use Logic::*;

        match self {
            Atom(x) => Atom(*x),
            Bool(x) => Bool(*x),
            And(x) => And(x.clone()),
            Or(x) => Or(x.clone()),
        }
    }
}

impl<T> Eq for Logic<T> {}

impl<T> PartialEq for Logic<T> {
    fn eq(&self, other: &Self) -> bool {
        use Logic::*;

        match (self, other) {
            (Atom(a), Atom(b)) => a.eq(b),
            (Bool(a), Bool(b)) => a.eq(b),
            (And(a), And(b)) => a.eq(b),
            (Or(a), Or(b)) => a.eq(b),
            _ => false,
        }
    }
}

impl<T> Hash for Logic<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use Logic::*;

        match self {
            Atom(x) => x.hash(state),
            Bool(x) => x.hash(state),
            And(x) => x.hash(state),
            Or(x) => x.hash(state),
        }
    }
}

macro_rules! and_or_impl {
    ($Name:ident, $Other:ident, $ShortCircuit:ident, $OtherBool:ident) => {
        #[derive(Debug, Clone, Eq, PartialEq, Hash)]
        pub struct $Name<T>(Vec<T>);

        impl<T> $Name<T> {
            pub fn new(args: impl IntoIterator<Item = T>) -> $Name<T> {
                $Name(args.into_iter().collect())
            }

            pub fn args(&self) -> &[T] {
                &self.0
            }

            pub fn args_mut(&mut self) -> &mut [T] {
                &mut self.0
            }

            pub fn into_args(self) -> Vec<T> {
                self.0
            }
        }

        impl<T> $Name<Logic<T>> {
            fn flatten(&mut self) {
                let mut i = 0;
                while let Some(arg) = self.0.get(i) {
                    if matches!(arg, Logic::$Name(_)) {
                        let arg = match self.0.swap_remove(i) {
                            Logic::$Name(x) => x,
                            _ => unreachable!("already checked"),
                        };
                        self.0.extend(arg.0);
                    } else {
                        i += 1;
                    }
                }
            }

            fn simplify(mut self) -> Logic<T> {
                use crate::FuzzyBool::*;

                self.flatten();

                let mut found = false;
                self.0.retain(|x| match x {
                    Logic::Bool($ShortCircuit) => {
                        found = true;
                        true
                    }
                    Logic::Bool($OtherBool) => false,
                    _ => !found,
                });

                if found {
                    return Logic::Bool($ShortCircuit);
                } else if self.0.is_empty() {
                    return Logic::Bool($OtherBool);
                } else if self.0.len() == 1 {
                    return self.0.pop().unwrap();
                }

                self.0.sort_by(|x, y| x.cmp_atoms_first(y));
                self.0.dedup();

                for w in self.0.windows(2) {
                    match w {
                        [Logic::Atom(a), Logic::Atom(b)] => {
                            if *a == !*b {
                                return Logic::Bool($ShortCircuit);
                            }
                        }
                        _ => break,
                    }
                }

                Logic::$Name(self)
            }

            fn cmp_atoms_first(&self, other: &Self) -> Ordering {
                let mut iter = self.0.iter().zip(&other.0);
                while let Some((a, b)) = iter.next() {
                    match a.cmp_atoms_first(b) {
                        Ordering::Equal => continue,
                        x => return x,
                    }
                }
                Ordering::Equal
            }

            fn negate(&mut self) {
                for x in &mut self.0 {
                    x.negate();
                }
            }
        }

        impl<T> ops::Not for $Name<T>
        where
            T: ops::Not<Output = T>,
        {
            type Output = $Other<T>;

            fn not(self) -> Self::Output {
                let args = self.0.into_iter().map(|x| !x);
                $Other::new(args)
            }
        }
    };
}

and_or_impl!(And, Or, False, True);
and_or_impl!(Or, And, True, False);

impl<T> And<Logic<T>> {
    pub fn expand(mut self) -> Logic<T> {
        let idx = match self.0.iter().position(|x| matches!(x, Logic::Or(_))) {
            Some(x) => x,
            None => return Logic::And(self),
        };

        let arg = self.0.swap_remove(idx);
        let arg = match arg {
            Logic::Or(a) => a,
            _ => unreachable!("already checked"),
        };

        let terms = arg
            .0
            .into_iter()
            .map(|a| Logic::and(self.0.iter().cloned().chain(std::iter::once(a))))
            .map(Logic::expand);

        let ret = Or::new(terms);
        ret.simplify()
    }

    pub fn try_into_atoms(self) -> Option<And<Atom<T>>> {
        self.0
            .into_iter()
            .try_fold(Vec::new(), |mut ret, b| {
                if let Logic::Atom(b) = b {
                    ret.push(b);
                    Some(ret)
                } else {
                    None
                }
            })
            .map(And::new)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplify() {
        const T: Logic<()> = Logic::TRUE;
        const F: Logic<()> = Logic::FALSE;

        // And[] -> True
        // Or[]  -> False
        assert_eq!(Logic::and([]), T);
        assert_eq!(Logic::or([]), F);

        // And[a] -> a
        // Or[a]  -> a
        assert_eq!(Logic::and([T]), T);
        assert_eq!(Logic::and([F]), F);
        assert_eq!(Logic::or([T]), T);
        assert_eq!(Logic::or([F]), F);

        let mut arena = crate::Arena::new();
        let [a, b, c, d] = fill_arena!(arena, "a", "b", "c", "d");

        fn at(a: Atom<&str>) -> Logic<&str> {
            Logic::Atom(a)
        }

        // And[a, !a] -> False
        // Or[a, !a]  -> True
        assert_eq!(Logic::and([a, !a].map(at)), Logic::FALSE);
        assert_eq!(Logic::or([a, !a].map(at)), Logic::TRUE);

        assert_eq!(Logic::and([F, F]), F);
        assert_eq!(Logic::and([F, T]), F);
        assert_eq!(Logic::and([T, F]), F);
        assert_eq!(Logic::and([T, T]), T);

        assert_eq!(Logic::or([F, F]), F);
        assert_eq!(Logic::or([F, T]), T);
        assert_eq!(Logic::or([T, F]), T);
        assert_eq!(Logic::or([T, T]), T);

        // And[a, True]  -> a
        // And[a, False] -> False
        // Or[a, True]   -> True
        // Or[a, False]  -> a
        assert_eq!(Logic::and([at(a), Logic::TRUE]), at(a));
        assert_eq!(Logic::and([at(a), Logic::FALSE]), Logic::FALSE);
        assert_eq!(Logic::or([at(a), Logic::TRUE]), Logic::TRUE);
        assert_eq!(Logic::or([at(a), Logic::FALSE]), at(a));

        // And[a,b,a] -> And[a,b]
        // Or[a,b,a]  -> Or[a,b]
        assert_eq!(Logic::and([a, b, a].map(at)), Logic::and([a, b].map(at)));
        assert_eq!(Logic::or([a, b, a].map(at)), Logic::or([a, b].map(at)));

        // And[And[a,b], And[c,d]] -> And[a,b,c,d]
        // Or[Or[a,b], Or[c,d]]    -> Or[a,b,c,d]
        assert_eq!(
            Logic::and([Logic::and([a, b].map(at)), Logic::and([c, d].map(at))]),
            Logic::and([a, b, c, d].map(at)),
        );
        assert_eq!(
            Logic::or([Logic::or([a, b].map(at)), Logic::or([c, d].map(at))]),
            Logic::or([a, b, c, d].map(at)),
        );

        assert_eq!(
            Logic::or([
                at(a),
                Logic::and([b, c, d].map(at)),
                Logic::and([b, d].map(at)),
                Logic::and([b, c, d].map(at)),
                at(a),
                Logic::and([b, d].map(at)),
            ]),
            Logic::or([
                at(a),
                Logic::and([b, c, d].map(at)),
                Logic::and([b, d].map(at))
            ]),
        );
    }

    #[test]
    fn test_expand() {
        let mut arena = crate::Arena::new();
        let [a, b, c, d] = fill_arena!(arena, "a", "b", "c", "d");

        fn at(a: Atom<&str>) -> Logic<&str> {
            Logic::Atom(a)
        }

        let t = Logic::and([Logic::or([a, b].map(at)), at(c)]);
        assert_eq!(
            t.expand(),
            Logic::or([
                Logic::And(And::new([a, c].map(at))),
                Logic::And(And::new([b, c].map(at)))
            ])
        );

        let t = Logic::and([Logic::or([a, !b].map(at)), at(b)]);
        assert_eq!(t.expand(), Logic::And(And::new([a, b].map(at))));

        let t = Logic::and([Logic::or([a, b].map(at)), Logic::or([c, d].map(at))]);
        assert_eq!(
            t.expand(),
            Logic::Or(Or::new([
                Logic::And(And::new([a, c].map(at))),
                Logic::And(And::new([a, d].map(at))),
                Logic::And(And::new([b, c].map(at))),
                Logic::And(And::new([b, d].map(at))),
            ]))
        );
    }
}
