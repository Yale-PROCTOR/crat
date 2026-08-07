#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g17_fill(mut p: *mut i32, len: usize) {
    let mut i: usize = 0;
    while i < len {
        *p = 1;
        p = p.offset(1);
        i += 1;
    }
}
