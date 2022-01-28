use crate::arena::Id;
use crate::FuzzyBool;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops;

pub struct Atom<T> {
    id: Id<T>,
    truth_value: bool,
}

impl<T> Atom<T> {
    #[inline]
    pub fn new(id: Id<T>, truth_value: bool) -> Self {
        Self { id, truth_value }
    }

    #[inline]
    pub fn id(&self) -> &Id<T> {
        &self.id
    }

    #[inline]
    pub fn truth_value(&self) -> bool {
        self.truth_value
    }

    #[inline]
    pub(crate) fn into_fuzzy_pair(self) -> (Id<T>, FuzzyBool) {
        (self.id, self.truth_value.into())
    }

    pub(crate) fn negate(&mut self) {
        self.truth_value = !self.truth_value;
    }
}

impl<T> fmt::Debug for Atom<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Atom")
            .field("id", &self.id)
            .field("truth_value", &self.truth_value)
            .finish()
    }
}

impl<T> Copy for Atom<T> {}

impl<T> Clone for Atom<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Eq for Atom<T> {}

impl<T> PartialEq for Atom<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id) && self.truth_value == other.truth_value
    }
}

impl<T> Ord for Atom<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.id
            .cmp(&other.id)
            .then_with(|| self.truth_value.cmp(&other.truth_value))
    }
}

impl<T> PartialOrd for Atom<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Hash for Atom<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.truth_value.hash(state);
    }
}

impl<T> ops::Not for Atom<T> {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        self.negate();
        self
    }
}
