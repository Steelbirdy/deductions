use indexmap::IndexSet;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::sync::atomic;

type ArenaId = u32;
type AtomicArenaId = atomic::AtomicU32;

static ARENA_COUNTER: AtomicArenaId = AtomicArenaId::new(1);

#[inline]
fn next_arena_id() -> ArenaId {
    ARENA_COUNTER.fetch_add(1, atomic::Ordering::SeqCst)
}

pub struct Id<T> {
    index: usize,
    arena_id: ArenaId,
    __phantom: PhantomData<T>,
}

impl<T> Id<T> {
    #[inline]
    pub const fn new(index: usize, arena_id: ArenaId) -> Self {
        Self {
            index,
            arena_id,
            __phantom: PhantomData,
        }
    }
}

impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Id")
            .field("index", &self.index)
            .field("arena_id", &self.arena_id)
            .finish()
    }
}

impl<T> Copy for Id<T> {}

impl<T> Clone for Id<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Eq for Id<T> {}

impl<T> PartialEq for Id<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.arena_id == other.arena_id
    }
}

impl<T> Ord for Id<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.index
            .cmp(&other.index)
            .then_with(|| self.arena_id.cmp(&other.arena_id))
    }
}

impl<T> PartialOrd for Id<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Hash for Id<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.arena_id.hash(state);
    }
}

pub struct Arena<T> {
    arena_id: ArenaId,
    items: IndexSet<T>,
}

impl<T> Arena<T> {
    #[inline]
    pub fn new() -> Self {
        Self {
            arena_id: 0,
            items: IndexSet::new(),
        }
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            arena_id: 0,
            items: IndexSet::with_capacity(capacity),
        }
    }

    #[inline]
    pub fn get(&self, id: Id<T>) -> Option<&T> {
        if self.arena_id != id.arena_id {
            None
        } else {
            self.items.get_index(id.index)
        }
    }

    pub fn into_iter_indexed(mut self) -> impl Iterator<Item = (Id<T>, T)> {
        self.init_arena_id();

        let arena_id = self.arena_id;
        let get_id = move |idx: usize| Id::new(idx, arena_id);

        self.into_iter()
            .enumerate()
            .map(move |(idx, sym)| (get_id(idx), sym))
    }

    fn get_id(&self, index: usize) -> Id<T> {
        debug_assert_ne!(
            self.arena_id, 0,
            "arena id was used before being initialized"
        );

        Id::new(index, self.arena_id)
    }

    #[inline]
    fn init_arena_id(&mut self) {
        if self.arena_id == 0 {
            self.arena_id = next_arena_id();
        }
    }
}

impl<T: Eq + Hash> Arena<T> {
    #[inline]
    pub fn get_id_of(&self, x: &T) -> Option<Id<T>> {
        self.items.get_index_of(x).map(|idx| self.get_id(idx))
    }

    #[inline]
    pub fn insert(&mut self, x: T) -> Id<T> {
        self.init_arena_id();

        let (index, _) = self.items.insert_full(x);
        self.get_id(index)
    }
}

impl<T> Default for Arena<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> fmt::Debug for Arena<T>
where
    IndexSet<T>: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.items.fmt(f)
    }
}

impl<T> Clone for Arena<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let items = self.items.clone();
        Self { arena_id: 0, items }
    }

    fn clone_from(&mut self, source: &Self) {
        self.items = source.items.clone();
    }
}

impl<T> IntoIterator for Arena<T> {
    type Item = <indexmap::set::IntoIter<T> as Iterator>::Item;
    type IntoIter = indexmap::set::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

impl<T, U> PartialEq<Arena<U>> for Arena<T>
where
    IndexSet<T>: PartialEq<IndexSet<U>>,
{
    #[inline]
    fn eq(&self, other: &Arena<U>) -> bool {
        self.items.eq(&other.items)
    }
}
