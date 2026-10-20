#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g11_sum(p: &[i32], len: usize) -> i32 {
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < len {
        total += p[i];
        i += 1;
    }
    total
}
