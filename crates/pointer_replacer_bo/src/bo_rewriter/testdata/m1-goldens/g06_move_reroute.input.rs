#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g06_fill(p: *mut i32) {
    *p = 9;
}

pub unsafe fn g06_main() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    g06_fill(p);
    let v = *q;
    free(q as *mut core::ffi::c_void);
    v
}
