use std::cell::Cell;

use rustc_hash::FxHashMap;
use typed_arena::Arena;

use crate::equiv_classes::EquivClasses;

/// Disjoint sets
pub struct DisjointSets<'a, T> {
    arena: &'a Arena<DisjointSet<'a, T>>,
    pub elements: FxHashMap<T, &'a DisjointSet<'a, T>>,
}

impl<'a, T> DisjointSets<'a, T> {
    #[inline]
    pub fn new(arena: &'a Arena<DisjointSet<'a, T>>) -> Self {
        DisjointSets {
            arena,
            elements: FxHashMap::default(),
        }
    }
}

impl<'a, T: Copy + Eq + std::hash::Hash> DisjointSets<'a, T> {
    #[inline]
    pub fn union(&mut self, t1: T, t2: T) {
        let t1 = *self
            .elements
            .entry(t1)
            .or_insert_with(|| self.arena.alloc(DisjointSet::new(t1)));
        let t2 = *self
            .elements
            .entry(t2)
            .or_insert_with(|| self.arena.alloc(DisjointSet::new(t2)));
        t1.union(t2);
    }

    #[inline]
    pub fn insert(&mut self, t: T) {
        self.elements
            .entry(t)
            .or_insert_with(|| self.arena.alloc(DisjointSet::new(t)));
    }

    #[inline]
    pub fn contains(&self, t: T) -> bool {
        self.elements.contains_key(&t)
    }

    #[inline]
    pub fn find_set(&self, t: T) -> Option<T> {
        Some(self.elements.get(&t)?.find_set().id())
    }

    #[inline]
    pub fn equiv(&self, t1: T, t2: T) -> Option<bool> {
        Some(self.find_set(t1)? == self.find_set(t2)?)
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.elements.keys().copied()
    }

    #[inline]
    pub fn to_equiv_classes(&self) -> EquivClasses<T> {
        let mut classes = EquivClasses::new();
        for t in self.elements.keys() {
            classes.insert(*t, |a, b| self.equiv(*a, *b).unwrap());
        }
        classes
    }
}

/// A disjoint set (also known as union-find) data structure.
#[derive(Debug)]
pub struct DisjointSet<'a, T> {
    id: T,
    parent: Cell<Option<&'a DisjointSet<'a, T>>>,
    rank: Cell<usize>,
}

impl<T> PartialEq for DisjointSet<'_, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl<T> Eq for DisjointSet<'_, T> {}

impl<'a, T> DisjointSet<'a, T> {
    #[inline]
    pub fn new(id: T) -> Self {
        DisjointSet {
            id,
            parent: Cell::new(None),
            rank: Cell::new(0),
        }
    }

    pub fn find_set(&self) -> &Self {
        match self.parent.get() {
            None => self,
            Some(parent) => {
                let new_parent = parent.find_set();
                self.parent.set(Some(new_parent));
                new_parent
            }
        }
    }

    #[inline]
    pub fn union(&'a self, other: &'a Self) -> &'a Self {
        let this = self.find_set();
        let that = other.find_set();
        if this != that { this.link(that) } else { this }
    }

    fn link(&'a self, other: &'a Self) -> &'a Self {
        if self.rank > other.rank {
            other.parent.set(Some(self));
            self
        } else {
            self.parent.set(Some(other));
            if self.rank == other.rank {
                other.rank.set(other.rank.get() + 1);
            }
            other
        }
    }
}

impl<T: Copy> DisjointSet<'_, T> {
    #[inline]
    pub fn id(&self) -> T {
        self.find_set().id
    }
}
