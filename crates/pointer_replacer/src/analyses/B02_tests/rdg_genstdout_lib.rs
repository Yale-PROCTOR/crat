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
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn exit(__status: core::ffi::c_int) -> !;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strrchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn strerror(__errnum: core::ffi::c_int) -> *mut core::ffi::c_char;
            fn __errno_location() -> *mut core::ffi::c_int;
        }
        pub type size_t = usize;
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        pub type FILE = _IO_FILE;
        #[repr(C)]
        pub struct _IO_FILE {
            pub _flags: core::ffi::c_int,
            pub _IO_read_ptr: *mut core::ffi::c_char,
            pub _IO_read_end: *mut core::ffi::c_char,
            pub _IO_read_base: *mut core::ffi::c_char,
            pub _IO_write_base: *mut core::ffi::c_char,
            pub _IO_write_ptr: *mut core::ffi::c_char,
            pub _IO_write_end: *mut core::ffi::c_char,
            pub _IO_buf_base: *mut core::ffi::c_char,
            pub _IO_buf_end: *mut core::ffi::c_char,
            pub _IO_save_base: *mut core::ffi::c_char,
            pub _IO_backup_base: *mut core::ffi::c_char,
            pub _IO_save_end: *mut core::ffi::c_char,
            pub _markers: *mut _IO_marker,
            pub _chain: *mut _IO_FILE,
            pub _fileno: core::ffi::c_int,
            pub _flags2: core::ffi::c_int,
            pub _old_offset: __off_t,
            pub _cur_column: core::ffi::c_ushort,
            pub _vtable_offset: core::ffi::c_schar,
            pub _shortbuf: [core::ffi::c_char; 1],
            pub _lock: *mut core::ffi::c_void,
            pub _offset: __off64_t,
            pub _codecvt: *mut _IO_codecvt,
            pub _wide_data: *mut _IO_wide_data,
            pub _freeres_list: *mut _IO_FILE,
            pub _freeres_buf: *mut core::ffi::c_void,
            pub __pad5: size_t,
            pub _mode: core::ffi::c_int,
            pub _unused2: [core::ffi::c_char; 20],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for _IO_FILE {}
        #[automatically_derived]
        impl ::core::clone::Clone for _IO_FILE {
            #[inline]
            fn clone(&self) -> _IO_FILE {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_marker>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<__off_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_ushort>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_schar>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 1]>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<__off64_t>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_codecvt>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_wide_data>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 20]>;
                *self
            }
        }
        pub type _IO_lock_t = ();
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn extractFilename(
            path: *const core::ffi::c_char,
            separator: core::ffi::c_char,
        ) -> *const core::ffi::c_char {
            let search: *const core::ffi::c_char = strrchr(path, separator as core::ffi::c_int);
            if search.is_null() {
                return path;
            }
            search.offset(1 as core::ffi::c_int as isize)
        }
        #[no_mangle]
        pub unsafe extern "C" fn FIO_createFilename_fromOutDir(
            path: *const core::ffi::c_char,
            outDirName: *const core::ffi::c_char,
            suffixLen: size_t,
        ) -> *mut core::ffi::c_char {
            let mut filenameStart: *const core::ffi::c_char = std::ptr::null::<core::ffi::c_char>();
            let mut separator: core::ffi::c_char = 0;
            let mut result: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            separator = '/' as i32 as core::ffi::c_char;
            filenameStart = extractFilename(path, separator);
            result = calloc(
                1 as size_t,
                (strlen(outDirName))
                    .wrapping_add(1 as size_t)
                    .wrapping_add(strlen(filenameStart))
                    .wrapping_add(suffixLen)
                    .wrapping_add(1 as size_t),
            ) as *mut core::ffi::c_char;
            if result.is_null() {
                fprintf(
                    stderr,
                    b"zstd: FIO_createFilename_fromOutDir: %s\0" as *const u8
                        as *const core::ffi::c_char,
                    strerror(*__errno_location()),
                );
                exit(30 as core::ffi::c_int);
            }
            memcpy(
                result as *mut core::ffi::c_void,
                outDirName as *const core::ffi::c_void,
                strlen(outDirName),
            );
            if *outDirName.add((strlen(outDirName)).wrapping_sub(1 as size_t)) as core::ffi::c_int
                == separator as core::ffi::c_int
            {
                memcpy(
                    result.add(strlen(outDirName)) as *mut core::ffi::c_void,
                    filenameStart as *const core::ffi::c_void,
                    strlen(filenameStart),
                );
            } else {
                memcpy(
                    result.add(strlen(outDirName)) as *mut core::ffi::c_void,
                    &mut separator as *mut core::ffi::c_char as *const core::ffi::c_void,
                    1 as size_t,
                );
                memcpy(
                    result
                        .add(strlen(outDirName))
                        .offset(1 as core::ffi::c_int as isize)
                        as *mut core::ffi::c_void,
                    filenameStart as *const core::ffi::c_void,
                    strlen(filenameStart),
                );
            }
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("rdg_genstdout_lib", SOURCE, &[], &[]);
}
