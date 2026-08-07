#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g18_second(p: &[i32]) -> i32 {
    let q: &[i32] = &p[1..];
    q[0]
}
