#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g21_ok(p: &mut i32) {
    *p = 1;
}

pub unsafe fn g21_aliased(a: *mut i32, b: *mut i32) {
    *a += *b;
}

pub unsafe fn g21_clean() {
    let mut x: i32 = 0;
    g21_ok(&mut x);
}

pub unsafe fn g21_dirty(q: *mut i32) {
    g21_aliased(q, q);
}
