#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g13_sum(p: Option<&[i32]>, len: usize) -> i32 {
    if p.is_none() {
        return 0;
    }
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < len {
        total += p.unwrap()[i];
        i += 1;
    }
    total
}
