use crate::{Atom, FuzzyBool};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops;

// TODO: Tests
pub enum Logic<T> {
    Atom(Atom<T>),
    Bool(FuzzyBool),
    And(And<Logic<T>>),
    Or(Or<Logic<T>>),
}

impl<T> Logic<T> {
    pub fn and(args: impl IntoIterator<Item = Logic<T>>) -> Self {
        And::new(args).simplify()
    }

    pub fn or(args: impl IntoIterator<Item = Logic<T>>) -> Self {
        Or::new(args).simplify()
    }

    fn ord_atoms_first(&self, other: &Self) -> Ordering {
        use Logic::*;

        match (self, other) {
            (Atom(x), Atom(y)) => x.cmp(y),
            (Atom(_), _) => Ordering::Less,
            (Bool(_), Atom(_)) => Ordering::Greater,
            (And(x), And(y)) => x.ord_atoms_first(y),
            (Or(x), Or(y)) => x.ord_atoms_first(y),
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
            Or(x) => x.expand(),
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
            pub fn expand(mut self) -> Logic<T> {
                if let Some(idx) = self.0.iter().position(|x| matches!(x, Logic::$Other(_))) {
                    // This doesn't matter because AND and OR are commutative.
                    let arg = self.0.swap_remove(idx);

                    let arg = match arg {
                        Logic::$Other(a) => a,
                        _ => unreachable!("already checked"),
                    };

                    let terms = arg.0.into_iter().map(|a| {
                        let mut new_args = self.0.clone();
                        new_args.push(a);
                        $Name::new(new_args).expand()
                    });

                    let ret = $Other::new(terms);
                    ret.simplify()
                } else {
                    Logic::$Name(self)
                }
            }

            pub fn try_into_atoms(self) -> Option<$Name<Atom<T>>> {
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
                    .map($Name::new)
            }

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
                self.0.retain(|x| {
                    if found {
                        false
                    } else {
                        match x {
                            Logic::Bool($ShortCircuit) => false,
                            Logic::Bool($OtherBool) => {
                                found = true;
                                true
                            }
                            _ => true,
                        }
                    }
                });

                if self.0.is_empty() {
                    return Logic::Bool($ShortCircuit);
                } else if self.0.len() == 1 {
                    return self.0.pop().unwrap();
                }

                self.0.sort_by(|x, y| x.ord_atoms_first(y));

                for w in self.0.windows(2) {
                    match w {
                        [Logic::Atom(a), Logic::Atom(b)] => {
                            if *a == !*b {
                                return Logic::Bool($OtherBool);
                            }
                        }
                        _ => break,
                    }
                }

                Logic::$Name(self)
            }

            fn ord_atoms_first(&self, other: &Self) -> Ordering {
                let mut iter = self.0.iter().zip(&other.0);
                while let Some((a, b)) = iter.next() {
                    match a.ord_atoms_first(b) {
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
