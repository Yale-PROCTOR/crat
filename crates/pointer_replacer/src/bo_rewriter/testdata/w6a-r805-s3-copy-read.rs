// wave-6a relay 147 (R805-3): S3 as the numbers lane translated it with the
// c2rust fork (analysis-fanout 048, fixtures/c2rust-fork/s3_copy_read), its
// lib.rs and src/s3_copy_read.rs in one file.
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
pub mod src {
pub mod s3_copy_read {
extern "C" {
    fn malloc(__size: size_t) -> *mut ::core::ffi::c_void;
    fn free(__ptr: *mut ::core::ffi::c_void);
}
pub type size_t = usize;
#[no_mangle]
pub unsafe extern "C" fn copy_read() -> ::core::ffi::c_int {
    let mut buf = malloc(
        (4 as size_t)
            .wrapping_mul(::core::mem::size_of::<::core::ffi::c_int>() as size_t),
    ) as *mut ::core::ffi::c_int;
    *buf = 7 as ::core::ffi::c_int;
    let mut p = buf;
    let mut v = *p;
    free(buf as *mut ::core::ffi::c_void);
    return v;
}
unsafe fn main_0() -> ::core::ffi::c_int {
    let mut v = copy_read();
    return 0 as ::core::ffi::c_int;
}
pub fn main() {
    unsafe { ::std::process::exit(main_0() as i32) }
}
}
}
