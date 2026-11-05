#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g12_fill(p: *mut i32, len: usize) {
    let mut i: usize = 0;
    while i < len {
        *p.offset(i as isize) = i as i32;
        i += 1;
    }
}
