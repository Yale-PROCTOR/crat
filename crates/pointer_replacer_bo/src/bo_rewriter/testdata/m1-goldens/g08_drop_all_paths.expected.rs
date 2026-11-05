#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g08_two_paths(c: i32) -> i32 {
    let mut p: Box<i32> = Box::new(0);
    *p = c;
    if c > 0 {
        let v = *p;
        drop(p);
        return v;
    }
    drop(p);
    0
}
