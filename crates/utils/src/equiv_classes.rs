//! Equivalence classes
use rustc_index::IndexVec;

/// Equivalence classes for a type `T`.
#[derive(Debug, Default, Clone)]
pub struct EquivClasses<T>(pub IndexVec<EquivClassId, Vec<T>>);

impl<T> EquivClasses<T> {
    #[inline]
    pub fn new() -> Self {
        Self(IndexVec::new())
    }

    /// Inserts a value into the proper equivalence class.
    #[inline]
    pub fn insert<F: FnMut(&T, &T) -> bool>(&mut self, v: T, mut cmp: F) {
        for equiv_class in &mut self.0 {
            if cmp(&v, &equiv_class[0]) {
                equiv_class.push(v);
                return;
            }
        }
        self.0.push(vec![v]);
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "equiv{}"]
    /// A unique identifier for an equivalence class.
    pub struct EquivClassId {}
}
