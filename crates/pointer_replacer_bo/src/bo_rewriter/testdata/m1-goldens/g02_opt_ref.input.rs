// g02 — the nullability pairing on a THIN form, and the pinned witness for one
// further dimension: DECLARED-NONCONST but USE-READONLY resolves to a SHARED
// reference. `p` is written `*mut i32` and only ever read through, and the
// mutability authority is use-derived, so the emitted form is `Option<&i32>`.
//
// g01 (`*mut`, written) and g03 (`*const`, read) cannot witness that: their
// declaration and their use agree. g02 is the only golden where the two differ.
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g02_maybe(p: *mut i32) -> i32 {
    if p.is_null() { return 0; }
    *p
}
