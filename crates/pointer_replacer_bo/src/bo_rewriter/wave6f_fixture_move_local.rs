#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types)]
// w6f-move-local-frame
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
unsafe extern "C" fn consume(mut p: *mut i32, mut k: i32) -> i32 {
    let mut r = *p + k;
    free(p as *mut core::ffi::c_void);
    return r;
}
#[no_mangle]
pub unsafe extern "C" fn producer() -> i32 {
    let mut p = malloc(::std::mem::size_of::<i32>()) as *mut i32;
    *p = 7 as i32;
    return consume(p, *p);
}
