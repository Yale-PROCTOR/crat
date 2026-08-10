#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g20_bump(p: *mut i32) -> i32 {
    *p += 1;
    *p
}

pub unsafe fn g20_via(q: *mut i32) -> i32 {
    g20_bump(q)
}

pub unsafe fn g20_root() -> i32 {
    let mut x: i32 = 0;
    g20_via(&mut x)
}
