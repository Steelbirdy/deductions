use crate::{Arena, Logic};
use std::hash::Hash;

// TODO: Tests for macros

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Rule<T> {
    Implies(Logic<T>, Logic<T>),
    Equals(Logic<T>, Logic<T>),
}

impl<T> Rule<T> {
    /// Converts `a == b` into `a -> b` and `b -> a`
    pub fn into_implications(self) -> impl Iterator<Item = (Logic<T>, Logic<T>)> {
        let (iter, next) = match self {
            Self::Implies(a, b) => (std::iter::once((a, b)), None),
            Self::Equals(a, b) => (std::iter::once((a.clone(), b.clone())), Some((b, a))),
        };
        iter.chain(next)
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

impl<T> IntoIterator for Rules<T> {
    type Item = Rule<T>;
    type IntoIter = std::vec::IntoIter<Rule<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.rules.into_iter()
    }
}
