use crate::{Arena, CheckedRules, Inconsistent, Logic};
use std::hash::Hash;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Rule<T> {
    Implies(Logic<T>, Logic<T>),
    Equals(Logic<T>, Logic<T>),
}

impl<T> Rule<T> {
    /// Converts `a == b` into `a -> b` and `b -> a`
    pub fn into_implications(self) -> impl Iterator<Item = (Logic<T>, Logic<T>)> {
        let (first, next) = match self {
            Self::Implies(a, b) => ((a, b), None),
            Self::Equals(a, b) => ((a.clone(), b.clone()), Some((b, a))),
        };
        std::iter::once(first).chain(next)
    }
}

pub struct Rules<T> {
    pub(crate) facts: Arena<T>,
    pub(crate) rules: Vec<Rule<T>>,
}

impl<T> Rules<T> {
    pub fn new(facts: Arena<T>, rules: impl IntoIterator<Item = Rule<T>>) -> Self {
        Self {
            facts,
            rules: rules.into_iter().collect(),
        }
    }
}

impl<T: Eq + Hash> Rules<T> {
    pub fn check(self) -> Result<CheckedRules<T>, Inconsistent> {
        self.try_into()
    }
}

impl<T> IntoIterator for Rules<T> {
    type Item = Rule<T>;
    type IntoIter = std::vec::IntoIter<Rule<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.rules.into_iter()
    }
}
