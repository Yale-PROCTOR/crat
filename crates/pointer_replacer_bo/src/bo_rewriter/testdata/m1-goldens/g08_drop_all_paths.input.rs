#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn g08_two_paths(c: i32) -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    *p = c;
    if c > 0 {
        let v = *p;
        free(p as *mut core::ffi::c_void);
        return v;
    }
    free(p as *mut core::ffi::c_void);
    0
}
