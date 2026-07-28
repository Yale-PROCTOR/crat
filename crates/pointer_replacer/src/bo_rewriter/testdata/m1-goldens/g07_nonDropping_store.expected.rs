#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g07_leak_then_realloc(c: i32) -> i32 {
    let mut p: Box<i32> = Box::new(0);
    core::mem::forget(core::mem::replace(&mut p, Box::new(0)));
    *p = c;
    let v = *p;
    drop(p);
    v
}
