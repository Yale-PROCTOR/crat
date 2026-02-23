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
            fn free(__ptr: *mut core::ffi::c_void);
        }
        pub type size_t = usize;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn UTIL_createLinePointers(
            buffer: *mut core::ffi::c_char,
            numLines: size_t,
            bufferSize: size_t,
        ) -> *mut *const core::ffi::c_char {
            let mut lineIndex: size_t = 0 as size_t;
            let mut pos: size_t = 0 as size_t;
            let bufferPtrs: *mut core::ffi::c_void =
                malloc(
                    numLines.wrapping_mul(
                        ::core::mem::size_of::<*mut *const core::ffi::c_char>() as size_t
                    ),
                ) as *mut core::ffi::c_void;
            let linePointers: *mut *const core::ffi::c_char =
                bufferPtrs as *mut *const core::ffi::c_char;
            if bufferPtrs.is_null() {
                return std::ptr::null_mut::<*const core::ffi::c_char>();
            }
            while lineIndex < numLines && pos < bufferSize {
                let mut len: size_t = 0 as size_t;
                let fresh0 = lineIndex;
                lineIndex = lineIndex.wrapping_add(1);
                *linePointers.add(fresh0) = buffer.add(pos);
                while pos.wrapping_add(len) < bufferSize
                    && *buffer.add(pos.wrapping_add(len)) as core::ffi::c_int != '\0' as i32
                {
                    len = len.wrapping_add(1);
                }
                pos = (pos as core::ffi::c_ulong).wrapping_add(len as core::ffi::c_ulong) as size_t
                    as size_t;
                if pos < bufferSize {
                    pos = pos.wrapping_add(1);
                }
            }
            if lineIndex != numLines {
                free(bufferPtrs);
                return std::ptr::null_mut::<*const core::ffi::c_char>();
            }
            linePointers
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates(
        "lines_in_buffer_lib",
        SOURCE,
        &["UTIL_createLinePointers#bufferPtrs"],
        &[],
    );
}
