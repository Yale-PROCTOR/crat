use rustc_index::{Idx, bit_set::BitRelations};

macro_rules! define_bitset {
    ($name:ident, $iter_name:ident, $word_ty:ty) => {
        /// Bit set that can hold up to a specific number of elements.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name<T> {
            word: $word_ty,
            _marker: std::marker::PhantomData<T>,
        }

        impl<T> Default for $name<T> {
            fn default() -> Self {
                Self::new_empty()
            }
        }

        impl<T: Idx + std::fmt::Debug> std::fmt::Debug for $name<T> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_set().entries(self.iter()).finish()
            }
        }

        impl<T> $name<T> {
            #[inline]
            pub fn new_empty() -> Self {
                Self {
                    word: 0,
                    _marker: std::marker::PhantomData,
                }
            }

            #[inline]
            pub fn clear(&mut self) {
                self.word = 0;
            }

            #[inline]
            pub fn count(&self) -> usize {
                self.word.count_ones() as usize
            }

            #[inline]
            pub fn is_empty(&self) -> bool {
                self.word == 0
            }

            #[inline]
            pub fn insert_all(&mut self, domain_size: u32) {
                self.word = (1 as $word_ty).overflowing_shl(domain_size).0 - 1;
            }

            #[inline]
            pub fn superset(&self, other: &$name<T>) -> bool {
                (self.word & other.word) == other.word
            }

            #[inline]
            pub fn iter(&self) -> $iter_name<'_, T> {
                $iter_name {
                    word: self.word,
                    _marker: std::marker::PhantomData,
                }
            }
        }

        impl<T: Idx> $name<T> {
            #[inline]
            fn word_mask(elem: T) -> $word_ty {
                1 << elem.index()
            }

            #[inline]
            pub fn new<I: IntoIterator<Item = T>>(iter: I) -> Self {
                let mut set = Self::new_empty();
                for elem in iter {
                    set.insert(elem);
                }
                set
            }

            #[inline]
            pub fn contains(&self, elem: T) -> bool {
                let mask = Self::word_mask(elem);
                (self.word & mask) != 0
            }

            #[inline]
            pub fn insert(&mut self, elem: T) -> bool {
                let mask = Self::word_mask(elem);
                let old_word = self.word;
                self.word |= mask;
                old_word != self.word
            }

            #[inline]
            pub fn remove(&mut self, elem: T) -> bool {
                let mask = Self::word_mask(elem);
                let old_word = self.word;
                self.word &= !mask;
                old_word != self.word
            }
        }

        pub struct $iter_name<'a, T> {
            word: $word_ty,
            _marker: std::marker::PhantomData<&'a T>,
        }

        impl<T: Idx> Iterator for $iter_name<'_, T> {
            type Item = T;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                if self.word == 0 {
                    return None;
                }
                let idx = self.word.trailing_zeros() as $word_ty;
                self.word &= !(1 << idx);
                Some(T::new(idx as usize))
            }
        }

        impl<T: Idx> BitRelations<$name<T>> for $name<T> {
            fn union(&mut self, other: &$name<T>) -> bool {
                bitwise(&mut self.word, other.word, |a, b| a | b)
            }

            fn subtract(&mut self, other: &$name<T>) -> bool {
                bitwise(&mut self.word, other.word, |a, b| a & !b)
            }

            fn intersect(&mut self, other: &$name<T>) -> bool {
                bitwise(&mut self.word, other.word, |a, b| a & b)
            }
        }
    };
}

define_bitset!(BitSet8, BitIter8, u8);
define_bitset!(BitSet16, BitIter16, u16);
define_bitset!(BitSet32, BitIter32, u32);
define_bitset!(BitSet64, BitIter64, u64);

#[inline]
fn bitwise<T: Copy + Eq, Op>(out_val: &mut T, in_val: T, op: Op) -> bool
where Op: Fn(T, T) -> T {
    let old_val = *out_val;
    let new_val = op(old_val, in_val);
    *out_val = new_val;
    old_val != new_val
}
