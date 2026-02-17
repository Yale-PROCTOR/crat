use super::run_ownership_case;

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
            fn realloc(__ptr: *mut core::ffi::c_void, __size: size_t) -> *mut core::ffi::c_void;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strdup(__s: *const core::ffi::c_char) -> *mut core::ffi::c_char;
            fn strstr(
                __haystack: *const core::ffi::c_char,
                __needle: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn searchAndReplace(
            orig: *const core::ffi::c_char,
            search: *const core::ffi::c_char,
            value: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let mut p: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let orig_len: size_t = strlen(orig) as size_t;
            let search_len: size_t = strlen(search) as size_t;
            let value_len: size_t = strlen(value) as size_t;
            let mut inx_start: size_t = 0;
            let mut tmp: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut tmp_offset: size_t = 0 as size_t;
            let mut total_bytes_allocated: size_t = 1 as size_t;
            let mut from: size_t = 0;
            p = strstr(orig, search);
            if p.is_null() {
                tmp = strdup(orig);
                return tmp;
            }
            inx_start = p.offset_from(orig) as core::ffi::c_long as size_t;
            from = inx_start.wrapping_add(search_len);
            if inx_start > 0 as size_t {
                total_bytes_allocated = inx_start.wrapping_add(1 as size_t);
                tmp = malloc(
                    (::core::mem::size_of::<core::ffi::c_char>() as size_t)
                        .wrapping_mul(total_bytes_allocated),
                ) as *mut core::ffi::c_char;
                if tmp.is_null() {
                    return std::ptr::null_mut::<core::ffi::c_char>();
                }
                strncpy(tmp, orig, inx_start);
                tmp_offset = inx_start;
            }
            while !p.is_null() {
                total_bytes_allocated = (total_bytes_allocated as core::ffi::c_ulong)
                    .wrapping_add(value_len as core::ffi::c_ulong)
                    as size_t as size_t;
                tmp = realloc(tmp as *mut core::ffi::c_void, total_bytes_allocated)
                    as *mut core::ffi::c_char;
                if tmp.is_null() {
                    return std::ptr::null_mut::<core::ffi::c_char>();
                }
                strncpy(
                    tmp.add(tmp_offset),
                    value,
                    total_bytes_allocated.wrapping_sub(tmp_offset),
                );
                tmp_offset = (tmp_offset as core::ffi::c_ulong)
                    .wrapping_add(value_len as core::ffi::c_ulong)
                    as size_t as size_t;
                p = strstr(orig.add(inx_start).add(search_len), search);
                if !p.is_null() {
                    let inx_start2: size_t = p.offset_from(orig) as core::ffi::c_long as size_t;
                    if inx_start2 > from {
                        let gap: size_t = inx_start2.wrapping_sub(from);
                        total_bytes_allocated = (total_bytes_allocated as core::ffi::c_ulong)
                            .wrapping_add(gap as core::ffi::c_ulong)
                            as size_t as size_t;
                        tmp = realloc(tmp as *mut core::ffi::c_void, total_bytes_allocated)
                            as *mut core::ffi::c_char;
                        if tmp.is_null() {
                            return std::ptr::null_mut::<core::ffi::c_char>();
                        }
                        strncpy(tmp.add(tmp_offset), orig.add(from), gap);
                        tmp_offset = (tmp_offset as core::ffi::c_ulong)
                            .wrapping_add(gap as core::ffi::c_ulong)
                            as size_t as size_t;
                    }
                    inx_start = inx_start2;
                }
                from = inx_start.wrapping_add(search_len);
            }
            if from < orig_len && from > 0 as size_t {
                total_bytes_allocated = (total_bytes_allocated as core::ffi::c_ulong)
                    .wrapping_add(orig_len.wrapping_sub(from) as core::ffi::c_ulong)
                    as size_t as size_t;
                tmp = realloc(tmp as *mut core::ffi::c_void, total_bytes_allocated)
                    as *mut core::ffi::c_char;
                if tmp.is_null() {
                    return std::ptr::null_mut::<core::ffi::c_char>();
                }
                strncpy(
                    tmp.add(tmp_offset),
                    orig.add(from),
                    orig_len.wrapping_sub(from),
                );
            }
            *tmp.add(total_bytes_allocated.wrapping_sub(1 as size_t)) =
                '\0' as i32 as core::ffi::c_char;
            tmp
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("search_and_replace_lib", SOURCE);
}
