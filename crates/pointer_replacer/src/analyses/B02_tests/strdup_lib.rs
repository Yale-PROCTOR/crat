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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn custom_strdup(
            str: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let mut len: size_t = 0;
            let mut newstr: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            if str.is_null() {
                return NULL as *mut core::ffi::c_char;
            }
            len = (strlen(str)).wrapping_add(1 as size_t);
            newstr = malloc(len) as *mut core::ffi::c_char;
            if newstr.is_null() {
                return NULL as *mut core::ffi::c_char;
            }
            memcpy(
                newstr as *mut core::ffi::c_void,
                str as *const core::ffi::c_void,
                len,
            );
            newstr
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("strdup_lib", SOURCE, &[], &[]);
}
