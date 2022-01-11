#[macro_use]
mod test_utils;

#[macro_use]
mod macros;

mod arena;
mod atom;
mod facts;
mod from_str;
mod fuzzy_bool;
mod logic;
mod rules;

pub use arena::{Arena, Id};
pub use atom::Atom;
pub use facts::{CheckedRules, FactKB, Inconsistent, InconsistentAssumptions};
pub use fuzzy_bool::FuzzyBool;
pub use logic::{And, Logic, Or};
pub use rules::{Rule, Rules};
