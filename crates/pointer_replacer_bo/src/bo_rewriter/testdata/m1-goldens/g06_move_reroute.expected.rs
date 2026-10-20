#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g06_fill(p: &mut i32) {
    *p = 9;
}

pub unsafe fn g06_main() -> i32 {
    let p: Box<i32> = Box::new(0);
    let mut q: Box<i32> = p;
    g06_fill(&mut *q);
    let v = *q;
    drop(q);
    v
}
