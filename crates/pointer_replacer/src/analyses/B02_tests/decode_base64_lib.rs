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
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const TRUE: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const FALSE: core::ffi::c_int = 0 as core::ffi::c_int;
        unsafe extern "C" fn decode(c: core::ffi::c_char) -> core::ffi::c_uchar {
            if c as core::ffi::c_int >= 'A' as i32 && c as core::ffi::c_int <= 'Z' as i32 {
                return (c as core::ffi::c_int - 'A' as i32) as core::ffi::c_uchar;
            }
            if c as core::ffi::c_int >= 'a' as i32 && c as core::ffi::c_int <= 'z' as i32 {
                return (c as core::ffi::c_int - 'a' as i32 + 26 as core::ffi::c_int)
                    as core::ffi::c_uchar;
            }
            if c as core::ffi::c_int >= '0' as i32 && c as core::ffi::c_int <= '9' as i32 {
                return (c as core::ffi::c_int - '0' as i32 + 52 as core::ffi::c_int)
                    as core::ffi::c_uchar;
            }
            if c as core::ffi::c_int == '+' as i32 {
                return 62 as core::ffi::c_uchar;
            }
            63 as core::ffi::c_uchar
        }
        unsafe extern "C" fn is_base64(c: core::ffi::c_char) -> core::ffi::c_int {
            if c as core::ffi::c_int >= 'A' as i32 && c as core::ffi::c_int <= 'Z' as i32
                || c as core::ffi::c_int >= 'a' as i32 && c as core::ffi::c_int <= 'z' as i32
                || c as core::ffi::c_int >= '0' as i32 && c as core::ffi::c_int <= '9' as i32
                || c as core::ffi::c_int == '+' as i32
                || c as core::ffi::c_int == '/' as i32
                || c as core::ffi::c_int == '=' as i32
            {
                return TRUE;
            }
            FALSE
        }
        #[no_mangle]
        pub unsafe extern "C" fn decode_base64(
            src: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            if !src.is_null() && *src as core::ffi::c_int != 0 {
                let mut dest: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
                let mut p: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
                let mut k: core::ffi::c_int = 0;
                let mut l: core::ffi::c_int =
                    (strlen(src)).wrapping_add(1 as size_t) as core::ffi::c_int;
                let mut buf: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
                dest = calloc(
                    ::core::mem::size_of::<core::ffi::c_char>() as size_t,
                    (l + 13 as core::ffi::c_int) as size_t,
                ) as *mut core::ffi::c_char;
                if dest.is_null() {
                    return std::ptr::null_mut::<core::ffi::c_char>();
                }
                p = dest as *mut core::ffi::c_uchar;
                buf = malloc(l as size_t) as *mut core::ffi::c_uchar;
                if buf.is_null() {
                    free(dest as *mut core::ffi::c_void);
                    return std::ptr::null_mut::<core::ffi::c_char>();
                }
                k = 0 as core::ffi::c_int;
                l = 0 as core::ffi::c_int;
                while *src.offset(k as isize) != 0 {
                    if is_base64(*src.offset(k as isize)) != 0 {
                        let fresh0 = l;
                        l += 1;
                        *buf.offset(fresh0 as isize) =
                            *src.offset(k as isize) as core::ffi::c_uchar;
                    }
                    k += 1;
                }
                k = 0 as core::ffi::c_int;
                while k < l {
                    let mut c1: core::ffi::c_char = 'A' as i32 as core::ffi::c_char;
                    let mut c2: core::ffi::c_char = 'A' as i32 as core::ffi::c_char;
                    let mut c3: core::ffi::c_char = 'A' as i32 as core::ffi::c_char;
                    let mut c4: core::ffi::c_char = 'A' as i32 as core::ffi::c_char;
                    let mut b1: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                    let mut b2: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                    let mut b3: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                    let mut b4: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                    c1 = *buf.offset(k as isize) as core::ffi::c_char;
                    if (k + 1 as core::ffi::c_int) < l {
                        c2 = *buf.offset((k + 1 as core::ffi::c_int) as isize) as core::ffi::c_char;
                    }
                    if (k + 2 as core::ffi::c_int) < l {
                        c3 = *buf.offset((k + 2 as core::ffi::c_int) as isize) as core::ffi::c_char;
                    }
                    if (k + 3 as core::ffi::c_int) < l {
                        c4 = *buf.offset((k + 3 as core::ffi::c_int) as isize) as core::ffi::c_char;
                    }
                    b1 = decode(c1);
                    b2 = decode(c2);
                    b3 = decode(c3);
                    b4 = decode(c4);
                    *p = ((b1 as core::ffi::c_int) << 2 as core::ffi::c_int
                        | b2 as core::ffi::c_int >> 4 as core::ffi::c_int)
                        as core::ffi::c_uchar;
                    let fresh1 = *p;
                    p = p.offset(1);
                    if c3 as core::ffi::c_int != '=' as i32 {
                        *p = ((b2 as core::ffi::c_int & 0xf as core::ffi::c_int)
                            << 4 as core::ffi::c_int
                            | b3 as core::ffi::c_int >> 2 as core::ffi::c_int)
                            as core::ffi::c_uchar;
                        let fresh2 = *p;
                        p = p.offset(1);
                    }
                    if c4 as core::ffi::c_int != '=' as i32 {
                        *p = ((b3 as core::ffi::c_int & 0x3 as core::ffi::c_int)
                            << 6 as core::ffi::c_int
                            | b4 as core::ffi::c_int)
                            as core::ffi::c_uchar;
                        let fresh3 = *p;
                        p = p.offset(1);
                    }
                    k += 4 as core::ffi::c_int;
                }
                free(buf as *mut core::ffi::c_void);
                return dest;
            }
            std::ptr::null_mut::<core::ffi::c_char>()
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("decode_base64_lib", SOURCE, &["buf", "dest"], &[]);
}
