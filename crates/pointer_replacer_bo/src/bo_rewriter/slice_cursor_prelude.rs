//! Legacy cursor wrapper emitted as BO-owned program text.

pub(crate) const SLICE_CURSOR_PRELUDE: &str = r#"pub mod slice_cursor {
    use std::ops::Index;
    use std::ops::IndexMut;
    use std::ops::Range;
    use std::ops::RangeFrom;
    use std::ops::RangeFull;
    use std::ops::RangeTo;

    pub struct SliceCursorMut<'a, T> {
        base: &'a mut [T],
        pos: usize,
    }

    impl<'a, T> SliceCursorMut<'a, T> {
        pub fn new(base: &'a mut [T]) -> Self {
            Self { base, pos: 0 }
        }

        pub fn with_pos(base: &'a mut [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub fn empty() -> Self {
            Self { base: &mut [], pos: 0 }
        }

        pub fn from_mut(val: &'a mut T) -> Self {
            Self { base: std::slice::from_mut(val), pos: 0 }
        }

        pub unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            unsafe { Self::from_raw_parts_mut(ptr as *mut T, len) }
        }

        pub unsafe fn from_raw_parts_mut(ptr: *mut T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts_mut(ptr, len) }, pos: 0 }
        }

        pub fn as_deref_mut(&mut self) -> SliceCursorMut<'_, T> {
            SliceCursorMut { base: &mut self.base[..], pos: self.pos }
        }

        pub fn as_deref(self) -> SliceCursor<'a, T> {
            SliceCursor { base: self.base, pos: self.pos }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub fn offset_by(mut self, offset: isize) -> Self {
            self.seek(offset);
            self
        }

        pub fn is_empty(&self) -> bool {
            self.pos >= self.base.len()
        }

        pub fn as_mut_ptr(&mut self) -> *mut T {
            self.base[self.pos..].as_mut_ptr()
        }

        pub fn as_ptr(&self) -> *const T {
            self.base[self.pos..].as_ptr()
        }

        pub fn first(&self) -> Option<&T> {
            self.base.get(self.pos)
        }

        pub fn first_mut(&mut self) -> Option<&mut T> {
            self.base.get_mut(self.pos)
        }

        pub fn as_slice(&self) -> &[T] {
            &self.base[self.pos..]
        }

        pub fn as_slice_mut(&mut self) -> &mut [T] {
            &mut self.base[self.pos..]
        }
    }

    pub struct SliceCursor<'a, T> {
        base: &'a [T],
        pos: usize,
    }

    impl<'a, T> Copy for SliceCursor<'a, T> {}

    impl<'a, T> Clone for SliceCursor<'a, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<'a, T> SliceCursor<'a, T> {
        pub fn new(slice: &'a [T]) -> Self {
            Self { base: slice, pos: 0 }
        }

        pub fn with_pos(base: &'a [T], pos: usize) -> Self {
            Self { base, pos }
        }

        pub fn empty() -> Self {
            Self { base: &[], pos: 0 }
        }

        pub fn from_ref(val: &'a T) -> Self {
            Self { base: std::slice::from_ref(val), pos: 0 }
        }

        pub unsafe fn from_raw_parts(ptr: *const T, len: usize) -> Self {
            Self { base: unsafe { std::slice::from_raw_parts(ptr, len) }, pos: 0 }
        }

        pub fn seek(&mut self, offset: isize) {
            self.pos = self.pos.wrapping_add_signed(offset);
        }

        pub fn offset_by(mut self, offset: isize) -> Self {
            self.seek(offset);
            self
        }

        pub fn is_empty(&self) -> bool {
            self.pos >= self.base.len()
        }

        pub fn as_ptr(&self) -> *const T {
            self.base[self.pos..].as_ptr()
        }

        pub fn first(&self) -> Option<&T> {
            self.base.get(self.pos)
        }

        pub fn as_slice(&self) -> &'a [T] {
            &self.base[self.pos..]
        }
    }

    #[inline(always)]
    fn abs_idx(pos: usize, index: isize) -> usize {
        pos.wrapping_add_signed(index)
    }

    macro_rules! impl_readable_index {
        ($cursor_type:ident, $($idx_type:ty),*) => {
            $(
                impl<T> Index<$idx_type> for $cursor_type<'_, T> {
                    type Output = T;
                    #[inline]
                    fn index(&self, index: $idx_type) -> &Self::Output {
                        &self.base[abs_idx(self.pos, index as isize)]
                    }
                }

                impl<T> Index<Range<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: Range<$idx_type>) -> &Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        let end = abs_idx(self.pos, range.end as isize);
                        &self.base[start..end]
                    }
                }

                impl<T> Index<RangeFrom<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: RangeFrom<$idx_type>) -> &Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        &self.base[start..]
                    }
                }

                impl<T> Index<RangeTo<$idx_type>> for $cursor_type<'_, T> {
                    type Output = [T];
                    #[inline]
                    fn index(&self, range: RangeTo<$idx_type>) -> &Self::Output {
                        let end = abs_idx(self.pos, range.end as isize);
                        &self.base[self.pos..end]
                    }
                }
            )*

            impl<T> Index<RangeFull> for $cursor_type<'_, T> {
                type Output = [T];
                #[inline]
                fn index(&self, _: RangeFull) -> &Self::Output {
                    &self.base[self.pos..]
                }
            }
        };
    }

    macro_rules! impl_mutable_index {
        ($($idx_type:ty),*) => {
            $(
                impl<T> IndexMut<$idx_type> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, index: $idx_type) -> &mut Self::Output {
                        let i = abs_idx(self.pos, index as isize);
                        &mut self.base[i]
                    }
                }

                impl<T> IndexMut<Range<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: Range<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[start..end]
                    }
                }

                impl<T> IndexMut<RangeFrom<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeFrom<$idx_type>) -> &mut Self::Output {
                        let start = abs_idx(self.pos, range.start as isize);
                        &mut self.base[start..]
                    }
                }

                impl<T> IndexMut<RangeTo<$idx_type>> for SliceCursorMut<'_, T> {
                    #[inline]
                    fn index_mut(&mut self, range: RangeTo<$idx_type>) -> &mut Self::Output {
                        let end = abs_idx(self.pos, range.end as isize);
                        &mut self.base[self.pos..end]
                    }
                }
            )*

            impl<T> IndexMut<RangeFull> for SliceCursorMut<'_, T> {
                #[inline]
                fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
                    &mut self.base[self.pos..]
                }
            }
        };
    }

    impl_readable_index!(SliceCursorMut, isize, usize, i32);
    impl_readable_index!(SliceCursor, isize, usize, i32);
    impl_mutable_index!(isize, usize, i32);

    // ---- BO addendum (slicecursor lane, relay 009; the legacy text above is
    // preserved verbatim). An ADDRESS view of the cursor's position, used only
    // for orderings and differences: it never indexes, so a position past the
    // window (a C address computed before a clamp) is a value, not a panic.
    // `pos()` is the index the R394-1 form names.
    impl<'a, T> SliceCursorMut<'a, T> {
        pub fn pos(&self) -> usize {
            self.pos
        }

        pub fn addr(&self) -> *const T {
            self.base.as_ptr().wrapping_add(self.pos)
        }

        pub fn addr_mut(&mut self) -> *mut T {
            self.base.as_mut_ptr().wrapping_add(self.pos)
        }
    }

    impl<'a, T> SliceCursor<'a, T> {
        pub fn pos(&self) -> usize {
            self.pos
        }

        pub fn addr(&self) -> *const T {
            self.base.as_ptr().wrapping_add(self.pos)
        }
    }
}"#;

#[cfg(test)]
mod tests {
    use super::SLICE_CURSOR_PRELUDE;

    const WITNESSES: &str = r#"
use slice_cursor::{SliceCursor, SliceCursorMut};

#[test]
fn shared_backward_walk_and_tail_bridge() {
    let values = *b"abc\0";
    let mut cursor = SliceCursor::with_pos(&values, 3);
    while cursor[-1_isize] != b'a' {
        cursor.seek(-1);
    }
    assert_eq!(cursor[0_isize], b'b');
    assert_eq!(cursor.as_slice(), b"bc\0");
    assert_eq!(cursor.as_ptr(), values[1..].as_ptr());
    assert_eq!(cursor.offset_by(-1)[0_isize], b'a');
    assert_eq!(cursor[0_isize], b'b');
}

#[test]
fn mutable_previous_output_and_reborrow() {
    let mut output = [3_i32, 7, 0, 0];
    let mut cursor = SliceCursorMut::with_pos(&mut output, 2);
    cursor[0_isize] = cursor[-1_isize] + cursor[-2_isize];
    {
        let mut previous = cursor.as_deref_mut().offset_by(-1);
        previous[0_isize] += 1;
    }
    cursor.seek(1);
    cursor[0_isize] = cursor[-1_isize] + cursor[-2_isize];
    assert_eq!(cursor.as_slice(), &[18]);
    assert_eq!(output, [3, 8, 10, 18]);
}

#[test]
fn signed_ranges_and_shared_conversion() {
    let mut values = [1, 2, 3, 4, 5];
    let mut cursor = SliceCursorMut::with_pos(&mut values, 2);
    assert_eq!(&cursor[-2_isize..1_isize], &[1, 2, 3]);
    cursor[-1_isize..1_isize].copy_from_slice(&[20, 30]);
    assert_eq!(&cursor[-1_isize..], &[20, 30, 4, 5]);
    assert_eq!(&cursor[..2_isize], &[30, 4]);
    assert_eq!(&cursor[..], &[30, 4, 5]);
    let shared = cursor.as_deref();
    assert_eq!(shared[-1_isize], 20);
    assert_eq!(shared.as_slice(), &[30, 4, 5]);
}

#[test]
fn raw_base_and_mutable_tail_bridge() {
    let mut values = [10, 20, 30];
    let ptr = values.as_mut_ptr();
    // SAFETY: values supplies the entire valid, aligned, exclusively borrowed range.
    let mut cursor = unsafe { SliceCursorMut::from_raw_parts_mut(ptr, 3) };
    cursor.seek(2);
    cursor[-1_isize] = 25;
    assert_eq!(cursor.as_mut_ptr(), ptr.wrapping_add(2));
    assert_eq!(values, [10, 25, 30]);
}

#[test]
#[should_panic]
fn before_base_read_is_bounds_checked() {
    let cursor = SliceCursor::new(&[1, 2]);
    let _ = cursor[-1_isize];
}

#[test]
#[should_panic]
fn past_end_write_is_bounds_checked() {
    let mut values = [1, 2];
    let mut cursor = SliceCursorMut::new(&mut values);
    cursor[2_isize] = 3;
}

#[test]
fn empty_nullable_and_singleton_constructors() {
    let absent: Option<SliceCursorMut<'_, i32>> = None;
    assert!(absent.is_none());
    assert!(SliceCursor::<i32>::empty().is_empty());
    assert!(SliceCursorMut::<i32>::empty().is_empty());
    let mut value = 4;
    let mut cursor = SliceCursorMut::from_mut(&mut value);
    *cursor.first_mut().unwrap() = 8;
    assert_eq!(cursor.first(), Some(&8));
    assert_eq!(SliceCursor::from_ref(&value)[0_isize], 8);
}
"#;

    #[test]
    fn emitted_legacy_wrapper_compiles_and_checks_signed_accesses() {
        let directory =
            std::env::temp_dir().join(format!("bo-slice-cursor-prelude-{}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        let source = directory.join("fixture.rs");
        let binary = directory.join("fixture");
        std::fs::write(&source, format!("{SLICE_CURSOR_PRELUDE}\n{WITNESSES}")).unwrap();
        let compilation = std::process::Command::new("rustc")
            .args(["--edition=2024", "--test"])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "cursor prelude fixture failed to compile: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        let execution = std::process::Command::new(&binary).output().unwrap();
        assert!(
            execution.status.success(),
            "cursor prelude fixture failed: {}\n{}",
            String::from_utf8_lossy(&execution.stdout),
            String::from_utf8_lossy(&execution.stderr)
        );
        std::fs::remove_dir_all(directory).unwrap();
    }
}
