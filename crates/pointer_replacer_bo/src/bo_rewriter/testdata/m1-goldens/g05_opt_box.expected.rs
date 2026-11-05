#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g05_alloc_maybe(c: i32) -> i32 {
    let mut p: Option<Box<i32>> = Some(Box::new(0));
    let mut v = 0;
    if p.is_some() {
        **p.as_mut().unwrap() = c;
        v = **p.as_ref().unwrap();
    }
    drop(p.take());
    v
}
