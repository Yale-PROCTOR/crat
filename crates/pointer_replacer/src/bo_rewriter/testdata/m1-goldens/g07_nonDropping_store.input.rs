#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g07_leak_then_realloc(c: i32) -> i32 {
    let mut p: *mut i32 = malloc(4) as *mut i32;
    p = malloc(4) as *mut i32;
    *p = c;
    let v = *p;
    free(p as *mut core::ffi::c_void);
    v
}
