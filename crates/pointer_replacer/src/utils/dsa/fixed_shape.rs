use std::alloc::{Allocator, Global};

/// Fixed shape `Vec<Vec<I>>`
#[derive(Clone, Debug)]
pub struct VecVec<I, A: Allocator = Global> {
    indices: Vec<usize, A>,
    data: Vec<I, A>,
}

impl<I, A: Allocator> std::ops::Index<usize> for VecVec<I, A> {
    type Output = [I];

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        let end = self.indices[index + 1];
        let start = self.indices[index];
        &self.data[start..end]
    }
}

impl<I, A: Allocator> std::ops::IndexMut<usize> for VecVec<I, A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let end = self.indices[index + 1];
        let start = self.indices[index];
        &mut self.data[start..end]
    }
}

impl<I> VecVec<I> {
    pub fn builder() -> VecVecBuilder<I> {
        Self::with_capacity(0, 0)
    }

    pub fn with_capacity(indices_capacity: usize, data_capacity: usize) -> VecVecBuilder<I> {
        let mut indices = Vec::with_capacity(indices_capacity + 1);
        indices.push(0);
        let data = Vec::with_capacity(data_capacity);
        let vec_array = VecVec { indices, data };
        VecVecBuilder {
            vec_vec: vec_array,
            start_index: 0,
            num_cur_items: 0,
        }
    }

    pub fn with_indices_capacity(size: usize) -> VecVecBuilder<I> {
        let mut indices = Vec::with_capacity(size + 1);
        indices.push(0);
        let data = Vec::new();
        let vec_array = VecVec { indices, data };
        VecVecBuilder {
            vec_vec: vec_array,
            start_index: 0,
            num_cur_items: 0,
        }
    }
}

#[derive(Debug)]
pub struct VecVecBuilder<I, A: Allocator = Global> {
    vec_vec: VecVec<I, A>,
    start_index: usize,
    num_cur_items: usize,
}

impl<I, A: Allocator> VecVecBuilder<I, A> {
    #[inline]
    pub fn push_element(&mut self, item: I) {
        self.vec_vec.data.push(item);
        self.num_cur_items += 1;
    }

    #[inline]
    pub fn push_vec(&mut self, items: impl Iterator<Item = I>) {
        debug_assert_eq!(self.num_cur_items, 0);
        let old_len = self.vec_vec.data.len();
        self.vec_vec.data.extend(items);
        self.start_index += self.vec_vec.data.len() - old_len;
        self.vec_vec.indices.push(self.start_index);
    }

    #[inline]
    pub fn complete_cur_vec(&mut self) {
        self.start_index += std::mem::take(&mut self.num_cur_items);
        self.vec_vec.indices.push(self.start_index);
    }

    #[inline]
    pub fn complete(self) -> VecVec<I, A> {
        self.vec_vec
    }

    #[allow(unused)]
    #[inline]
    pub fn get(&self, index: usize) -> &[I] {
        if index + 1 >= self.vec_vec.indices.len() {
            panic!("the entry for {index} is still under construction")
        }
        &self.vec_vec[index]
    }
}

impl<I> From<Vec<Vec<I>>> for VecVec<I> {
    fn from(value: Vec<Vec<I>>) -> Self {
        let mut builder = VecVec::with_indices_capacity(value.len() + 1);
        for vec in value {
            builder.push_vec(vec.into_iter());
        }
        builder.complete()
    }
}
