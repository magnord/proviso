//! Append-only arenas addressed by typed ids, and dense side tables keyed by those ids.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// A typed index into an [`Arena`].
pub struct Id<T> {
    raw: u32,
    _marker: PhantomData<fn() -> T>,
}

impl<T> Id<T> {
    pub fn index(self) -> usize {
        self.raw as usize
    }
}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Id<T> {}

impl<T> PartialEq for Id<T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<T> Eq for Id<T> {}

impl<T> Hash for Id<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.raw)
    }
}

/// Storage for one kind of node. Nodes are never removed, so ids stay valid.
pub struct Arena<T> {
    items: Vec<T>,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Arena { items: Vec::new() }
    }
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc(&mut self, item: T) -> Id<T> {
        let raw = u32::try_from(self.items.len()).expect("arena holds more than u32::MAX nodes");
        self.items.push(item);
        Id { raw, _marker: PhantomData }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<T> Index<Id<T>> for Arena<T> {
    type Output = T;

    fn index(&self, id: Id<T>) -> &T {
        &self.items[id.index()]
    }
}

impl<T> IndexMut<Id<T>> for Arena<T> {
    fn index_mut(&mut self, id: Id<T>) -> &mut T {
        &mut self.items[id.index()]
    }
}

/// Facts about the nodes of one arena, such as their types, stored densely by id.
pub struct SideTable<T, V> {
    values: Vec<Option<V>>,
    _marker: PhantomData<fn() -> T>,
}

impl<T, V> Default for SideTable<T, V> {
    fn default() -> Self {
        SideTable { values: Vec::new(), _marker: PhantomData }
    }
}

impl<T, V> SideTable<T, V> {
    pub fn insert(&mut self, id: Id<T>, value: V) {
        let index = id.index();
        if index >= self.values.len() {
            self.values.resize_with(index + 1, || None);
        }
        self.values[index] = Some(value);
    }

    pub fn get(&self, id: Id<T>) -> Option<&V> {
        self.values.get(id.index()).and_then(Option::as_ref)
    }

    /// Every value in the table, in id order.
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.values.iter().flatten()
    }
}
