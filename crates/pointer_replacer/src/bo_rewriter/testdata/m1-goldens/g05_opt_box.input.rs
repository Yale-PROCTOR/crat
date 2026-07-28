#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g05_alloc_maybe(c: i32) -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let mut v = 0;
    if !p.is_null() {
        *p = c;
        v = *p;
    }
    free(p as *mut core::ffi::c_void);
    v
}
