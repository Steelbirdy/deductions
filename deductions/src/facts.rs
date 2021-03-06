use crate::{And, Arena, Atom, FuzzyBool, Id, Logic, Rules};
use std::borrow::Borrow;
use std::fmt;
use std::hash::Hash;

pub type HashSet<T> = ahash::AHashSet<T>;
pub type HashMap<K, V> = ahash::AHashMap<K, V>;

pub type AlphaImplication<T> = (Atom<T>, Atom<T>);
pub type AlphaRules<T> = HashMap<Atom<T>, HashSet<Atom<T>>>;
pub type BetaImplication<T> = (And<Atom<T>>, Atom<T>);
pub type BetaRules<T> = HashMap<Atom<T>, (HashSet<Atom<T>>, HashSet<usize>)>;
pub type BetaTriggers<T> = HashMap<Atom<T>, HashSet<usize>>;
pub type Prerequisites<T> = HashMap<Id<T>, HashSet<Id<T>>>;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Inconsistent;

impl fmt::Display for Inconsistent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("implications are inconsistent: for some `a`, `a -> !a`")
    }
}

impl std::error::Error for Inconsistent {}

/// Computes the transitive closure of a list of implications.
///
/// Uses Warshall's algorithm, as described on slide 5 [here](https://cs.winona.edu/lin/cs440/ch08-2.pdf).
pub fn transitive_closure<T: Eq + Hash>(
    implications: impl IntoIterator<Item = AlphaImplication<T>>,
) -> HashSet<AlphaImplication<T>> {
    let mut ret: HashSet<_> = implications.into_iter().collect();
    let all_items: Vec<_> = ret.iter().copied().flat_map(|(a, b)| [a, b]).collect();

    for &i in &all_items {
        for &j in &all_items {
            if ret.contains(&(i, j)) {
                for &k in &all_items {
                    if ret.contains(&(j, k)) {
                        ret.insert((i, k));
                    }
                }
            }
        }
    }

    ret
}

/// Deduce all implications
///
/// # Example
/// Given a set of logic rules:
///
/// a -> b \
/// b -> c
///
/// we deduce all possible rules:
///
/// a  -> b, c \
/// b  -> c
/// !b -> !a
/// !c -> !a, !b
pub fn deduce_alpha_implications<T: Eq + Hash>(
    implications: impl IntoIterator<Item = AlphaImplication<T>>,
) -> Result<AlphaRules<T>, Inconsistent> {
    let implications = implications
        .into_iter()
        .flat_map(|(a, b)| [(a, b), (!b, !a)]);
    let mut ret = AlphaRules::new();
    let impls_closure = transitive_closure(implications);

    for (a, b) in impls_closure {
        // Skip `a -> a` cyclic input
        if a != b {
            ret.entry(a).or_default().insert(b);
            ret.entry(!b).or_default().insert(!a);
        }
    }

    // clean up tautologies and check consistency
    for (&a, impls) in &mut ret {
        let not_a = !a;
        if impls.contains(&not_a) {
            return Err(Inconsistent);
        }
    }

    Ok(ret)
}

/// Apply additional beta-rules (AND conditions) to already-built
/// alpha implication tables.
///
/// # Example
/// alpha_implications:
///
/// a -> \[b, !c, d] \
/// b -> \[d]
///
/// beta_rules:
///
/// &(b,d) -> e
///
/// the we extend `a`'s rules to:
///
/// a -> \[b, !c, d, e]
pub fn apply_beta_to_alpha_route<T: Eq + Hash>(
    alpha_rules: AlphaRules<T>,
    beta_rules: Vec<BetaImplication<T>>,
) -> BetaRules<T> {
    let mut ret: BetaRules<T> = alpha_rules
        .into_iter()
        .map(|(x, x_impls)| (x, (x_impls, Default::default())))
        .collect();

    for (b_cond, _) in beta_rules.iter() {
        for &bk in b_cond.args() {
            ret.entry(bk).or_default();
        }
    }

    let mut seen_static_extension = true;
    while seen_static_extension {
        seen_static_extension = false;

        let keys: Vec<_> = ret.keys().copied().collect();
        for (b_cond, b_impl) in beta_rules.iter() {
            let b_args: HashSet<_> = b_cond.args().iter().cloned().collect();
            for &x in &keys {
                let (x_impls, _) = ret.get_mut(&x).unwrap();
                let mut remove_x = x_impls.insert(x);

                // alpha: ... -> a  beta: &(...) -> a      (non-informative)
                if !x_impls.contains(b_impl) && b_args.is_subset(x_impls) {
                    x_impls.insert(*b_impl);

                    // we introduced a new implication - now we have to restore
                    // completeness of the whole set
                    if let Some((b_impl_impl, _)) = ret.get(b_impl).cloned() {
                        let (x_impls, _) = ret.get_mut(&x).unwrap();
                        remove_x &= !b_impl_impl.contains(&x);
                        x_impls.extend(b_impl_impl);
                    }

                    seen_static_extension = true;
                }

                if remove_x {
                    let (x_impls, _) = ret.get_mut(&x).unwrap();
                    x_impls.remove(&x);
                }
            }
        }
    }

    // attach beta-nodes which can possibly be triggered by an alpha chain
    for (b_idx, (b_cond, b_impl)) in beta_rules.into_iter().enumerate() {
        let b_args: HashSet<_> = b_cond.into_args().into_iter().collect();
        for (&x, (x_impls, bb)) in ret.iter_mut() {
            // alpha: ... -> a  beta: &(...) -> a  (non-informative)
            if b_impl == x || x_impls.contains(&b_impl) {
                continue;
            }

            let remove_x = x_impls.insert(x);

            // alpha: x -> a...  beta: &(!a,...) -> ...  (will never trigger)
            // alpha: x -> a...  beta: &(...) -> !a      (will never trigger)
            if x_impls
                .iter()
                .copied()
                .any(|xi| b_args.contains(&(!xi)) || !xi == b_impl)
            {
                if remove_x {
                    x_impls.remove(&x);
                }
                continue;
            }

            if x_impls.intersection(&b_args).next().is_some() {
                bb.insert(b_idx);
            }

            if remove_x {
                x_impls.remove(&x);
            }
        }
    }

    ret
}

/// Build prerequisites table from rules.
///
/// # Example
/// Given a set of logic rules:
///
/// a -> b, c \
/// b -> c
///
/// we build prerequisites (from what points something can be deduced):
///
/// b <- a \
/// c <- a, b
///
/// Note however that these prerequisites may not be enough to prove a fact.
/// An example is `a -> b`, where prereq(a) is b, and prereq(b) is a.
/// That's because a=T -> b=T and b=F -> a=F, but a=F -> b=?
pub fn rules_to_prereqs<T: Eq + Hash>(rules: AlphaRules<T>) -> Prerequisites<T> {
    let mut prereqs = Prerequisites::new();

    for (a, rules) in rules {
        let a = *a.id();
        for r in rules.into_iter().map(|x| *x.id()) {
            prereqs.entry(r).or_default().insert(a);
        }
    }
    prereqs
}

// Rules Prover

/// Prover of logic rules
///
/// Given a set of initial rules, the prover tries to prove all possible rules
/// which follow from given premises.
///
/// As a result, proven rules are always either in one of two forms: alpha or
/// beta:
///
/// ## Alpha rules
/// Rules of the form:
///
/// a -> b & c & d & ...
///
/// ## Beta rules
/// Rules of the form:
///
/// (a & b & ...) -> c & d & ...
///
/// i.e. beta rules are join conditions that say that something follows when
/// *several* facts are true at the same time.
pub struct Prover<T> {
    rules_seen: HashSet<(Logic<T>, Logic<T>)>,
    alpha_rules: Vec<AlphaImplication<T>>,
    beta_rules: Vec<BetaImplication<T>>,
}

impl<T> Default for Prover<T> {
    fn default() -> Self {
        Self {
            rules_seen: HashSet::new(),
            alpha_rules: Vec::new(),
            beta_rules: Vec::new(),
        }
    }
}

impl<T> Prover<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn into_rules(self) -> (Vec<AlphaImplication<T>>, Vec<BetaImplication<T>>) {
        (self.alpha_rules, self.beta_rules)
    }
}

impl<T: Eq + Hash> Prover<T> {
    pub fn process_rule(&mut self, a: Logic<T>, b: Logic<T>) {
        let rule = (a, b);
        if matches!(rule, (Logic::Bool(_), _) | (_, Logic::Bool(_))) {
            return;
        }

        if self.rules_seen.contains(&rule) {
            return;
        }

        self.rules_seen.insert(rule.clone());

        self._process_rule(rule);
    }

    fn _process_rule(&mut self, (a, b): (Logic<T>, Logic<T>)) {
        match (a, b) {
            // right part first

            // a -> b & c  -->  a -> b ; a -> c
            // (?) FIXME: this is only correct when (b & c) != {}!
            (a, Logic::And(b)) => {
                for b_arg in b.into_args() {
                    self.process_rule(a.clone(), b_arg);
                }
            }

            // a -> b | c  ->  !b & !c -> !a
            //             ->   a & !b ->  c
            //             ->   a & !c ->  b
            (a, Logic::Or(b)) => {
                // detect tautology first
                if matches!(a, Logic::Atom(_)) {
                    // tautology:  a -> a|c|...
                    if b.args().contains(&a) {
                        // Tautology: a -> a|c|...
                        return;
                    }
                }

                let b_args = b.args().iter().cloned().map(|x| !x);
                self.process_rule(Logic::and(b_args), !a.clone());

                for b_idx in 0..b.args().len() {
                    let mut b_args = b.args().to_vec();
                    let b_arg = b_args.swap_remove(b_idx);
                    self.process_rule(Logic::and([a.clone(), !b_arg]), Logic::or(b_args));
                }
            }

            // left part

            // a & b -> c  --> IRREDUCIBLE CASE -- WE STORE IT AS IS
            //                 (this will be the basis of the beta-network)
            (Logic::And(a), b) => {
                if a.args().contains(&b) {
                    // Tautology: a & b -> a
                    return;
                }

                let b = match b {
                    Logic::Atom(b) => b,
                    _ => unreachable!("everything else has been filtered out"),
                };

                let a = a
                    .try_into_atoms()
                    .expect("other cases are handled earlier in the `match`");
                self.beta_rules.push((a, b));

                // NOTE: at present we ignore  !c -> !a | !b
            }
            (Logic::Or(a), b) => {
                if a.args().contains(&b) {
                    // Tautology: a | b -> a
                    return;
                }

                for a_arg in a.into_args() {
                    self.process_rule(a_arg, b.clone());
                }
            }

            // Both `a` and `b` are atoms (i.e. an alpha rule)
            (Logic::Atom(a), Logic::Atom(b)) => {
                // a  ->  b
                self.alpha_rules.push((a, b));
                // !b -> !a
                self.alpha_rules.push((!b, !a));
            }
            (Logic::Bool(_), _) | (_, Logic::Bool(_)) => {
                unreachable!("filtered out in `process_rule`")
            }
        }
    }
}

#[derive(Clone)]
pub struct CheckedRules<T> {
    pub(crate) defined_facts: Arena<T>,
    alpha_rules: AlphaRules<T>,
    beta_rules: Vec<BetaImplication<T>>,
    beta_triggers: BetaTriggers<T>,
    prereqs: Prerequisites<T>,
}

impl<T: Eq + Hash> CheckedRules<T> {
    pub fn new(rules: Rules<T>) -> Result<Self, Inconsistent> {
        let mut p = Prover::new();
        let facts = rules.facts;

        for rule in rules.rules {
            for (a, b) in rule.into_implications() {
                p.process_rule(a, b);
            }
        }

        let (alpha_rules, beta) = p.into_rules();

        // deduce alpha implications
        let alpha_rules = deduce_alpha_implications(alpha_rules)?;

        // now:
        // - apply beta rules to alpha chains (aka static extension)
        // - further associate beta rules to alpha chain (for inference at runtime)
        let beta_rules = apply_beta_to_alpha_route(alpha_rules, beta.clone());

        // build relations (forward chains)
        let (alpha_rules, beta_triggers): (AlphaRules<_>, _) = beta_rules
            .into_iter()
            .map(|(k, (a, b))| ((k, a), (k, b)))
            .unzip();

        // build prereqs (backward chains)
        let prereqs = rules_to_prereqs(alpha_rules.clone());

        Ok(Self {
            defined_facts: facts,
            alpha_rules,
            beta_rules: beta,
            beta_triggers,
            prereqs,
        })
    }
}

impl<T: Eq + Hash> TryFrom<Rules<T>> for CheckedRules<T> {
    type Error = Inconsistent;

    fn try_from(rules: Rules<T>) -> Result<Self, Self::Error> {
        Self::new(rules)
    }
}

// TODO: Use something else instead of the ID
#[derive(Eq, PartialEq)]
pub struct InconsistentAssumptions<T> {
    kb: String,
    fact_id: Id<T>,
    value: FuzzyBool,
}

impl<T> std::error::Error for InconsistentAssumptions<T> {}

impl<T> fmt::Debug for InconsistentAssumptions<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InconsistentAssumptions")
            .field("kb", &self.kb)
            .field("fact_id", &self.fact_id)
            .field("value", &self.value)
            .finish()
    }
}

impl<T> fmt::Display for InconsistentAssumptions<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}, {:?}={}", self.kb, self.fact_id, self.value)
    }
}

pub trait BaseKey<T> {
    fn id<'a>(&self, kb: &FactKB<'a, T>) -> Option<Id<T>>;
}

impl<T> BaseKey<T> for Id<T> {
    fn id<'a>(&self, _: &FactKB<'a, T>) -> Option<Id<T>> {
        Some(*self)
    }
}

impl<T> BaseKey<T> for Atom<T> {
    fn id<'a>(&self, _: &FactKB<'a, T>) -> Option<Id<T>> {
        Some(*self.id())
    }
}

impl<T: Eq + Hash> BaseKey<T> for T {
    fn id<'a>(&self, kb: &FactKB<'a, T>) -> Option<Id<T>> {
        kb.rules.defined_facts.get_id_of(self)
    }
}

impl<'k, T: Eq + Hash> BaseKey<T> for &'k T {
    fn id<'a>(&self, kb: &FactKB<'a, T>) -> Option<Id<T>> {
        kb.rules.defined_facts.get_id_of(self)
    }
}

// TODO: Use a simpler Hasher for this HashMap to prevent unnecessary slowdown
/// A simple propositional knowledge base relying on compiled inference rules.
#[derive(Clone)]
pub struct FactKB<'a, T> {
    rules: &'a CheckedRules<T>,
    kb: HashMap<Id<T>, FuzzyBool>,
}

impl<'a, T> FactKB<'a, T> {
    pub fn new(rules: &'a CheckedRules<T>) -> Self {
        Self {
            rules,
            kb: HashMap::new(),
        }
    }

    pub fn get<K: BaseKey<T>>(&self, key: K) -> Option<FuzzyBool> {
        let id = key.id(self)?;
        self.kb.get(&id).copied()
    }

    pub fn prereqs<K: BaseKey<T>>(&self, key: K) -> Option<impl Iterator<Item = &T> + '_> {
        let id = key.id(self)?;
        Some(
            self.rules
                .prereqs
                // keys for prereqs are always true
                .get(&id)?
                .iter()
                .map(|x| self.rules.defined_facts.get(x).unwrap()),
        )
    }

    pub fn assumptions(&self) -> impl Iterator<Item = (&T, FuzzyBool)> + '_ {
        self.kb.iter().map(|(a, b)| {
            let t = self.rules.defined_facts.get(a).unwrap();
            (t, *b)
        })
    }

    /// Add fact k=v to the knowledge base.
    ///
    /// Returns `true` if the KB was updated, `false` otherwise.
    pub fn tell<K: BaseKey<T>>(
        &mut self,
        key: K,
        truth_value: impl Into<FuzzyBool>,
    ) -> Result<bool, InconsistentAssumptions<T>> {
        let id = match key.id(self) {
            Some(x) => x,
            None => return Ok(false),
        };

        let truth_value = truth_value.into();
        let should_update = self.tell_no_update(*id.borrow(), truth_value)?;
        if should_update {
            self.kb.insert(id, truth_value);
        }
        Ok(should_update)
    }

    pub fn assume(
        &mut self,
        key: impl BaseKey<T>,
        truth_value: impl Into<FuzzyBool>,
    ) -> Result<(), InconsistentAssumptions<T>> {
        let id = match key.id(self) {
            Some(x) => x,
            None => return Ok(()),
        };
        let truth_value = truth_value.into();

        let mut facts = vec![(id, truth_value)];
        self.deduce_all_facts(&mut facts)
    }

    pub fn assume_all(
        &mut self,
        facts: impl IntoIterator<Item = (impl BaseKey<T>, impl Into<FuzzyBool>)>,
    ) -> Result<(), InconsistentAssumptions<T>> {
        let mut facts = facts
            .into_iter()
            .filter_map(|(a, b)| a.id(self).map(|x| (x, b.into())))
            .collect();

        self.deduce_all_facts(&mut facts)
    }

    /// Update the KB with all the implications of a list of facts.
    ///
    /// This is the workhorse, so keep it *fast*.
    fn deduce_all_facts(
        &mut self,
        facts: &mut Vec<(Id<T>, FuzzyBool)>,
    ) -> Result<(), InconsistentAssumptions<T>> {
        let mut beta_may_trigger = HashSet::new();
        let mut to_update = Vec::new();

        while !facts.is_empty() {
            for (k, v) in facts.drain(..) {
                let v = if !self.tell(k, v)? || v.is_unknown() {
                    continue;
                } else {
                    match v.as_bool() {
                        Some(v) => v,
                        None => unreachable!(),
                    }
                };

                let atom = Atom::new(k, v);

                if let Some(implies) = self.rules.alpha_rules.get(&atom) {
                    for x in implies {
                        let (id, truth) = x.into_fuzzy_pair();
                        if self.tell_no_update(id, truth)? {
                            to_update.push(*x);
                        }
                    }
                }

                self.kb
                    .extend(to_update.drain(..).map(Atom::into_fuzzy_pair));

                if let Some(triggers) = self.rules.beta_triggers.get(&atom) {
                    beta_may_trigger.extend(triggers.iter().copied());
                }
            }

            for b_idx in beta_may_trigger.drain() {
                let (b_cond, b_impl) = match self.rules.beta_rules.get(b_idx) {
                    Some(x) => x,
                    None => continue,
                };

                if b_cond.args().iter().all(|arg| {
                    let (id, b) = arg.into_fuzzy_pair();
                    self.get(id).map_or(false, |a| a.is_same(b))
                }) {
                    facts.push(b_impl.into_fuzzy_pair());
                }
            }
        }

        Ok(())
    }

    fn tell_no_update(&self, k: Id<T>, v: FuzzyBool) -> Result<bool, InconsistentAssumptions<T>> {
        match self.get(k) {
            Some(b) if !b.is_unknown() => {
                if b.is_same(v) {
                    Ok(false)
                } else {
                    Err(InconsistentAssumptions {
                        kb: format!("{:?}", self),
                        fact_id: k,
                        value: v,
                    })
                }
            }
            _ => Ok(true),
        }
    }
}

impl<T> fmt::Debug for FactKB<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("{\n")?;
        for (k, v) in &self.kb {
            writeln!(f, "\t{:?}: {:?},", k, v)?;
        }
        Ok(())
    }
}

impl<T> Eq for FactKB<'_, T> {}

impl<T> PartialEq for FactKB<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.kb.eq(&other.kb)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    macro_rules! alpha_map {
        ($($a:expr => [$($b:expr),* $(,)?]),* $(,)?) => {
            [
                $(($a, [$($b),*].into_iter().collect::<HashSet<_>>())),*
            ].into_iter().collect::<AlphaRules<_>>()
        };
    }

    macro_rules! prereqs {
        ($($a:expr => [$($b:expr),* $(,)?]),* $(,)?) => {
            [
                $((*$a.id(), [$(*$b.id()),*].into_iter().collect::<HashSet<_>>())),*
            ].into_iter().collect::<Prerequisites<_>>()
        };
    }

    macro_rules! beta_rules {
        ($(&($($a:expr),+) => $b:expr),* $(,)?) => {
            Vec::from([
                $((And::new([$($a),*]), $b)),*
            ])
        };
    }

    macro_rules! beta_map {
        ($($a:expr => ({$($b:expr),*}, [$($b_idx:literal),*])),* $(,)?) => {
            [
                $(($a, ([$($b),*].into_iter().collect::<HashSet<_>>(), [$($b_idx),*].into_iter().collect::<HashSet<_>>()))),*
            ].into_iter().collect::<BetaRules<_>>()
        };
    }

    #[test]
    fn test_deduce_alpha_implications() {
        fn doit<'a>(
            i: impl IntoIterator<Item = AlphaImplication<&'a str>>,
        ) -> Result<(AlphaRules<&'a str>, Prerequisites<&'a str>), Inconsistent> {
            let i = deduce_alpha_implications(i)?;
            let p = rules_to_prereqs(i.clone());
            Ok((i, p))
        }

        let mut arena = Arena::new();
        let [a, b, c, d, e, na] = fill_arena!(arena, "a", "b", "c", "d", "e", "na");

        // transitivity
        let (i, p) = doit([(a, b), (b, c)]).unwrap();
        assert_eq!(
            i,
            alpha_map!(a => [b, c], b => [c], !b => [!a], !c => [!a, !b])
        );
        assert_eq!(p, prereqs!(a => [b, c], b => [a, c], c => [a, b]));

        // duplicate entry
        let (i, p) = doit([(a, b), (b, c), (b, c)]).unwrap();
        assert_eq!(
            i,
            alpha_map!(
                a => [b, c],
                b => [c],
                !b => [!a],
                !c => [!a, !b],
            )
        );
        assert_eq!(
            p,
            prereqs!(
                a => [b, c],
                b => [a, c],
                c => [a, b],
            )
        );

        // cycle tolerance
        assert_eq!(doit([(a, a), (a, a)]).unwrap(), (alpha_map!(), prereqs!()),);
        assert_eq!(
            doit([(a, b), (b, a)]).unwrap(),
            (
                alpha_map!(a => [b], b => [a], !a => [!b], !b => [!a]),
                prereqs!(a => [b], b => [a])
            ),
        );

        // catches inconsistency
        assert!(doit([(a, !a)]).is_err());
        assert!(doit([(a, b), (b, !a)]).is_err());
        assert!(doit([(a, b), (b, c), (b, na), (na, !a)]).is_err());

        // handles implications with negations
        let (i, p) = doit([(a, !b), (c, b)]).unwrap();
        assert_eq!(
            i,
            alpha_map!(
                a => [!b, !c],
                b => [!a],
                c => [b, !a],
                !b => [!c],
            )
        );
        assert_eq!(
            p,
            prereqs!(
                a => [b, c],
                b => [a, c],
                c => [a, b],
            )
        );
        let (i, p) = doit([(!a, b), (a, c)]).unwrap();
        assert_eq!(
            i,
            alpha_map!(
                a => [c],
                !a => [b],
                !b => [a, c],
                !c => [!a, b],
            )
        );
        assert_eq!(
            p,
            prereqs!(
                a => [b, c],
                b => [a, c],
                c => [a, b],
            )
        );

        // long deductions
        let (i, p) = doit([(a, b), (b, c), (c, d), (d, e)]).unwrap();
        assert_eq!(
            i,
            alpha_map!(
                a => [b, c, d, e],
                b => [c, d, e],
                c => [d, e],
                d => [e],
                !b => [!a],
                !c => [!a, !b],
                !d => [!a, !b, !c],
                !e => [!a, !b, !c, !d],
            )
        );
        assert_eq!(
            p,
            prereqs!(
                a => [b, c, d, e],
                b => [a, c, d, e],
                c => [a, b, d, e],
                d => [a, b, c, e],
                e => [a, b, c, d],
            )
        );

        // something related to a real use
        let mut arena = Arena::new();
        let [rat, real, int] = fill_arena!(arena, "rat", "real", "int");
        let (i, p) = doit([(rat, real), (int, rat)]).unwrap();
        assert_eq!(
            i,
            alpha_map!(
                int => [rat, real],
                rat => [real],
                !real => [!rat, !int],
                !rat => [!int],
            )
        );
        assert_eq!(
            p,
            prereqs!(
                rat => [int, real],
                real => [int, rat],
                int => [rat, real],
            )
        );
    }

    #[test]
    fn test_apply_beta_to_alpha_route() {
        let mut arena = Arena::new();
        let [x, y, z, a, b, c, d, e, p] =
            fill_arena!(arena, "x", "y", "z", "a", "b", "c", "d", "e", "p");

        // x -> a       &(a,b) -> x    --  x -> a
        let alpha = alpha_map!(x => [a]);
        let beta = beta_rules!(&(a, b) => x);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a}, []), a => ({}, [0]), b => ({}, [0])),
        );

        // x -> a       &(a,!x) -> b    --  x -> a
        let alpha = alpha_map!(x => [a]);
        let beta = beta_rules!(&(a, !x) => b);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a}, []), !x => ({}, [0]), a => ({}, [0])),
        );

        // x -> a b     &(a,b) -> c     --  x -> a b c
        let alpha = alpha_map!(x => [a, b]);
        let beta = beta_rules!(&(a, b) => c);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b, c}, []), a => ({}, [0]), b => ({}, [0])),
        );

        // x -> a       &(a,b) -> y     -- x -> a [#0]
        let alpha = alpha_map!(x => [a]);
        let beta = beta_rules!(&(a, b) => y);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a}, [0]), a => ({}, [0]), b => ({}, [0])),
        );

        // x -> a b c       &(a,b) -> c     --  x -> a b c
        let alpha = alpha_map!(x => [a, b, c]);
        let beta = beta_rules!(&(a, b) => c);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b, c}, []), a => ({}, [0]), b => ({}, [0])),
        );

        // x -> a b     &(a,b,c) -> y       --  x -> a b [#0]
        let alpha = alpha_map!(x => [a, b]);
        let beta = beta_rules!(&(a, b, c) => y);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b}, [0]), a => ({}, [0]), b => ({}, [0]), c => ({}, [0])),
        );

        // x -> a b     &(a,b) -> c         -- x -> a b c d
        // c -> d                              c -> d
        let alpha = alpha_map!(x => [a, b], c => [d]);
        let beta = beta_rules!(&(a, b) => c);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b, c, d}, []), c => ({d}, []), a => ({}, [0]), b => ({}, [0])),
        );

        // x -> a b     &(a,b) -> c         --  x -> a b c d e
        // c -> d       &(c,d) -> e             c -> d e
        let alpha = alpha_map!(x => [a, b], c => [d]);
        let beta = beta_rules!(&(a, b) => c, &(c, d) => e);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b, c, d, e}, []), c => ({d, e}, []), a => ({}, [0]), b => ({}, [0]), d => ({}, [1])),
        );

        // x -> a b     &(a,y) -> z         --  x -> a b y z
        //              &(a,b) -> y
        let alpha = alpha_map!(x => [a, b]);
        let beta = beta_rules!(&(a, y) => z, &(a, b) => y);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b, y, z}, []), a => ({}, [0, 1]), y => ({}, [0]), b => ({}, [1])),
        );

        // x -> a b     &(a,!b) -> c        --  x -> a b
        let alpha = alpha_map!(x => [a, b]);
        let beta = beta_rules!(&(a, !b) => c);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b}, []), a => ({}, [0]), !b => ({}, [0])),
        );

        // !x -> !a !b      &(!a,b) -> c        --  !x -> !a !b
        let alpha = alpha_map!(!x => [!a, !b]);
        let beta = beta_rules!(&(!a, b) => c);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(!x => ({!a, !b}, []), !a => ({}, [0]), b => ({}, [0])),
        );

        // x -> a b         &(b,c) -> !a        --  x -> a b
        let alpha = alpha_map!(x => [a, b]);
        let beta = beta_rules!(&(b, c) => !a);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b}, []), b => ({}, [0]), c => ({}, [0])),
        );

        // x -> a b         &(a,b) -> c         -- x -> a b c p
        // c -> p a
        let alpha = alpha_map!(x => [a, b], c => [p, a]);
        let beta = beta_rules!(&(a, b) => c);
        assert_eq!(
            apply_beta_to_alpha_route(alpha, beta),
            beta_map!(x => ({a, b, c, p}, []), c => ({p, a}, []), a => ({}, [0]), b => ({}, [0])),
        );
    }

    macro_rules! checked_rules {
        ($($x:tt)+) => {
            CheckedRules::try_from(Rules::str_from_str($($x)+).unwrap())
        };
    }

    #[test]
    fn test_fact_rules_parse() {
        let f = checked_rules!(["a -> b"]).unwrap();
        let [a, b] = vars!(f, "a", "b");
        assert_eq!(f.prereqs, prereqs!(b => [a], a => [b]));

        let f = checked_rules!(["a -> !b"]).unwrap();
        let [a, b] = vars!(f, "a", "b");
        assert_eq!(f.prereqs, prereqs!(b => [a], a => [b]));

        let f = checked_rules!(["!a -> b"]).unwrap();
        let [a, b] = vars!(f, "a", "b");
        assert_eq!(f.prereqs, prereqs!(b => [a], a => [b]));

        let f = checked_rules!(["!a -> !b"]).unwrap();
        let [a, b] = vars!(f, "a", "b");
        assert_eq!(f.prereqs, prereqs!(b => [a], a => [b]));

        let f = checked_rules!(["!z == nz"]).unwrap();
        let [z, nz] = vars!(f, "z", "nz");
        assert_eq!(f.prereqs, prereqs!(z => [nz], nz => [z]));

        #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
        enum IntType {
            Pos,
            Neg,
            Zero,
            NonPos,
            NonNeg,
            NonZero,
        }
        use IntType::*;

        impl FromStr for IntType {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Ok(match s {
                    "pos" => Pos,
                    "neg" => Neg,
                    "zero" => Zero,
                    "npos" => NonPos,
                    "nneg" => NonNeg,
                    "nzero" => NonZero,
                    _ => return Err(s.to_string()),
                })
            }
        }

        let f = Rules::<IntType>::from_str([
            "neg == npos & nzero",
            "pos == nneg & nzero",
            "zero == nneg & npos",
        ])
        .unwrap();
        let f = CheckedRules::new(f).unwrap();

        let [pos, neg, zero, npos, nneg, nzero] = vars!(f, Pos, Neg, Zero, NonPos, NonNeg, NonZero);

        assert_eq!(
            f.prereqs,
            prereqs!(
                neg => [npos, nzero],
                pos => [nneg, nzero],
                zero => [nneg, npos],
                npos => [neg, zero],
                nneg => [pos, zero],
                nzero => [neg, pos],
            )
        );
    }

    #[test]
    #[should_panic]
    fn test_fact_rules_parse_err() {
        let _ = checked_rules!(["a -> !a"]).unwrap();
    }

    macro_rules! assert_fuzzy_eq {
        ($a:expr, $b:expr) => {{
            let a = $a;
            let b = $b;
            for (k, va) in a {
                let vb = b.get(&k).copied().unwrap();
                assert!(va.is_same(vb));
            }
        }};
    }

    macro_rules! assert_deduced {
        ($f:ident, [$($a:expr),*] -> [$($b:expr),*]) => {
            {
                let mut kb = FactKB::new(&$f);
                kb.assume_all([$($a),*].map(Atom::into_fuzzy_pair)).unwrap();
                assert_fuzzy_eq!(kb.kb, [$($b),*].into_iter().map(Atom::into_fuzzy_pair).collect::<HashMap<_, _>>());
            }
        };
    }

    #[test]
    fn test_fact_rules_deduce() {
        let f = checked_rules!(["a -> b", "b -> c", "b -> d", "c -> e"]).unwrap();

        let [a, b, c, d, e] = vars!(f, "a", "b", "c", "d", "e");

        fn doit<'a>(
            f: &CheckedRules<&'a str>,
            facts: impl IntoIterator<Item = (Id<&'a str>, FuzzyBool)>,
        ) -> Result<HashMap<Id<&'a str>, FuzzyBool>, InconsistentAssumptions<&'a str>> {
            let mut kb = FactKB::new(f);
            kb.assume_all(facts)?;
            Ok(kb.kb)
        }

        assert_deduced!(f, [a] -> [a, b, c, d, e]);
        assert_deduced!(f, [b] -> [b, c, d, e]);
        assert_deduced!(f, [c] -> [c, e]);
        assert_deduced!(f, [d] -> [d]);
        assert_deduced!(f, [e] -> [e]);
        assert_deduced!(f, [!a] -> [!a]);
        assert_deduced!(f, [!b] -> [!a, !b]);
        assert_deduced!(f, [!c] -> [!a, !b, !c]);
        assert_deduced!(f, [!d] -> [!a, !b, !d]);

        assert_fuzzy_eq!(
            doit(&f, [(f.get_id("a"), FuzzyBool::Unknown)]).unwrap(),
            [(f.get_id("a"), FuzzyBool::Unknown)]
                .into_iter()
                .collect::<HashMap<_, _>>()
        );
    }

    #[test]
    fn test_fact_rules_deduce_2() {
        // pos/neg/zero, but rules are insufficient to derive all relations
        let f = checked_rules!(["pos -> !neg", "pos -> !z"]).unwrap();

        let [pos, neg, z] = vars!(f, "pos", "neg", "z");

        assert_deduced!(f, [pos] -> [pos, !neg, !z]);
        assert_deduced!(f, [!pos] -> [!pos]);
        assert_deduced!(f, [neg] -> [!pos, neg]);
        assert_deduced!(f, [!neg] -> [!neg]);
        assert_deduced!(f, [z] -> [!pos, z]);
        assert_deduced!(f, [!z] -> [!z]);

        // pos/neg/zero, rules are sufficient to derive all relations
        let f = checked_rules!(["pos -> !neg", "neg -> !pos", "pos -> !z", "neg -> !z"]).unwrap();

        let [pos, neg, z] = vars!(f, "pos", "neg", "z");

        assert_deduced!(f, [pos] -> [pos, !neg, !z]);
        assert_deduced!(f, [!pos] -> [!pos]);
        assert_deduced!(f, [neg] -> [!pos, neg, !z]);
        assert_deduced!(f, [!neg] -> [!neg]);
        assert_deduced!(f, [z] -> [!pos, !neg, z]);
        assert_deduced!(f, [!z] -> [!z]);
    }

    #[test]
    fn test_fact_rules_deduce_multiple() {
        let f = checked_rules!(["real == pos | npos"]).unwrap();

        let [real, pos, npos] = vars!(f, "real", "pos", "npos");

        assert_deduced!(f, [real] -> [real]);
        assert_deduced!(f, [!real] -> [!real, !pos, !npos]);
        assert_deduced!(f, [pos] -> [real, pos]);
        assert_deduced!(f, [npos] -> [real, npos]);

        // key tests below
        assert_deduced!(f, [!pos, !npos] -> [!real, !pos, !npos]);
        assert_deduced!(f, [real, !pos] -> [real, !pos, npos]);
        assert_deduced!(f, [real, !npos] -> [real, pos, !npos]);

        assert_deduced!(f, [pos, !npos] -> [real, pos, !npos]);
        assert_deduced!(f, [!pos, npos] -> [real, !pos, npos]);
    }

    #[test]
    fn test_fact_rules_deduce_multiple_2() {
        let f = checked_rules!(["real == neg | zero | pos"]).unwrap();

        let [real, neg, zero, pos] = vars!(f, "real", "neg", "zero", "pos");

        assert_deduced!(f, [real] -> [real]);
        assert_deduced!(f, [!real] -> [!real, !neg, !zero, !pos]);
        assert_deduced!(f, [neg] -> [real, neg]);
        assert_deduced!(f, [zero] -> [real, zero]);
        assert_deduced!(f, [pos] -> [real, pos]);

        // key tests below
        assert_deduced!(f, [!neg, !zero, !pos] -> [!real, !neg, !zero, !pos]);
        assert_deduced!(f, [real, !neg] -> [real, !neg]);
        assert_deduced!(f, [real, !zero] -> [real, !zero]);
        assert_deduced!(f, [real, !pos] -> [real, !pos]);

        assert_deduced!(f, [real, !zero, !pos] -> [real, neg, !zero, !pos]);
        assert_deduced!(f, [real, !neg, !pos] -> [real, !neg, zero, !pos]);
        assert_deduced!(f, [real, !neg, !zero] -> [real, !neg, !zero, pos]);

        assert_deduced!(f, [neg, !zero, !pos] -> [real, neg, !zero, !pos]);
        assert_deduced!(f, [!neg, zero, !pos] -> [real, !neg, zero, !pos]);
        assert_deduced!(f, [!neg, !zero, pos] -> [real, !neg, !zero, pos]);
    }

    #[test]
    fn test_fact_rules_deduce_base() {
        // deduction that starts from base
        let f = checked_rules!([
            "real  == neg | zero | pos",
            "neg   -> real & !zero & !pos",
            "pos   -> real & !zero & !neg",
        ])
        .unwrap();

        let [real, neg, zero, pos] = vars!(f, "real", "neg", "zero", "pos");

        let mut base = FactKB::new(&f);

        base.assume_all([real, !neg].map(Atom::into_fuzzy_pair))
            .unwrap();
        assert_eq!(
            base.kb,
            [real, !neg]
                .into_iter()
                .map(Atom::into_fuzzy_pair)
                .collect::<HashMap<_, _>>()
        );

        base.assume_all([!zero].map(Atom::into_fuzzy_pair)).unwrap();
        assert_eq!(
            base.kb,
            [real, !neg, !zero, pos]
                .into_iter()
                .map(Atom::into_fuzzy_pair)
                .collect::<HashMap<_, _>>()
        );
    }

    #[test]
    fn test_fact_rules_deduce_static_ext() {
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
        enum NumType {
            Real,
            Neg,
            Zero,
            Pos,
            NonNeg,
            NonPos,
        }

        use NumType::*;

        // verify that static beta-extensions deduction takes place
        let f = CheckedRules::try_from(rules![
            [Real   == Neg | Zero | Pos]
            [Neg    -> Real & !Zero & !Pos]
            [Pos    -> Real & !Zero & !Neg]
            [NonNeg == Real & !Neg]
            [NonPos == Real & !Pos]
        ])
        .unwrap();

        let [neg, zero, pos, nneg, npos] = vars!(f, Neg, Zero, Pos, NonNeg, NonPos);

        assert!(f.alpha_rules.get(&neg).unwrap().contains(&npos));
        assert!(f.alpha_rules.get(&pos).unwrap().contains(&nneg));
        assert!(f.alpha_rules.get(&zero).unwrap().contains(&nneg));
        assert!(f.alpha_rules.get(&zero).unwrap().contains(&npos));
    }
}
