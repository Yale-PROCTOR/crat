use super::run_ownership_case_with_box_candidates;

const SOURCE: &str = r####"
#![warn(mutable_transmutes)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![feature(c_variadic)]
#![feature(extern_types)]
#![feature(linkage)]
#![feature(rustc_private)]
#![feature(thread_local)]
#![feature(builtin_syntax)]
#![feature(core_intrinsics)]
#![feature(derive_clone_copy)]
#![feature(hint_must_use)]
#![feature(panic_internals)]
pub mod src {
    pub mod lib {
        extern "C" {
            fn strrchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
        }
        #[no_mangle]
        pub unsafe extern "C" fn tool_basename(
            mut path: *mut core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let mut s1: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut s2: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            s1 = strrchr(path, '/' as i32);
            s2 = strrchr(path, '\\' as i32);
            if !s1.is_null() && !s2.is_null() {
                path = if s1 > s2 {
                    s1.offset(1 as core::ffi::c_int as isize)
                } else {
                    s2.offset(1 as core::ffi::c_int as isize)
                };
            } else if !s1.is_null() {
                path = s1.offset(1 as core::ffi::c_int as isize);
            } else if !s2.is_null() {
                path = s2.offset(1 as core::ffi::c_int as isize);
            }
            path
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("basename_lib", SOURCE, &[], &[]);
}
