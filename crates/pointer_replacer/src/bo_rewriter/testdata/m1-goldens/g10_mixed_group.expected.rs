#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g10_mixed(a: *mut i32, b: *mut i32, solo: &mut i32, c: i32) -> i32 {
    let mut q: *mut i32 = a;
    if c > 0 {
        q = b;
    }
    *q = c;
    *solo += 1;
    *a + *b + *solo
}
