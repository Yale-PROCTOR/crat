use std::{alloc::Allocator, borrow::Borrow};

use smallvec::SmallVec;

pub trait AssocExt<K, V>
where K: Eq
{
    fn get_by_key<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq;

    fn get_by_key_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq;
}

impl<K: Eq, V, A: Allocator> AssocExt<K, V> for Vec<(K, V), A> {
    #[inline]
    fn get_by_key<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.iter()
            .find_map(|(key, value)| (key.borrow() == k).then_some(value))
    }

    #[inline]
    fn get_by_key_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.iter_mut()
            .find_map(|(key, value)| (<K as Borrow<Q>>::borrow(&*key) == k).then_some(value))
    }
}

impl<K: Eq, V, const N: usize> AssocExt<K, V> for SmallVec<[(K, V); N]> {
    #[inline]
    fn get_by_key<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.iter()
            .find_map(|(key, value)| (key.borrow() == k).then_some(value))
    }

    #[inline]
    fn get_by_key_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        self.iter_mut()
            .find_map(|(key, value)| (<K as Borrow<Q>>::borrow(&*key) == k).then_some(value))
    }
}
