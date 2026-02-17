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
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        unsafe extern "C" fn encode(u: core::ffi::c_uchar) -> core::ffi::c_char {
            if (u as core::ffi::c_int) < 26 as core::ffi::c_int {
                return ('A' as i32 + u as core::ffi::c_int) as core::ffi::c_char;
            }
            if (u as core::ffi::c_int) < 52 as core::ffi::c_int {
                return ('a' as i32 + (u as core::ffi::c_int - 26 as core::ffi::c_int))
                    as core::ffi::c_char;
            }
            if (u as core::ffi::c_int) < 62 as core::ffi::c_int {
                return ('0' as i32 + (u as core::ffi::c_int - 52 as core::ffi::c_int))
                    as core::ffi::c_char;
            }
            if u as core::ffi::c_int == 62 as core::ffi::c_int {
                return '+' as i32 as core::ffi::c_char;
            }
            '/' as i32 as core::ffi::c_char
        }
        #[no_mangle]
        pub unsafe extern "C" fn encode_base64(
            mut size: core::ffi::c_int,
            src: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let mut i: core::ffi::c_int = 0;
            let mut out: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut p: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            if src.is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            if size == 0 {
                size = strlen(src as *mut core::ffi::c_char) as core::ffi::c_int;
            }
            out = calloc(
                ::core::mem::size_of::<core::ffi::c_char>() as size_t,
                (size * 4 as core::ffi::c_int / 3 as core::ffi::c_int + 4 as core::ffi::c_int)
                    as size_t,
            ) as *mut core::ffi::c_char;
            if out.is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            p = out;
            i = 0 as core::ffi::c_int;
            while i < size {
                let mut b1: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                let mut b2: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                let mut b3: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                let mut b4: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                let mut b5: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                let mut b6: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                let mut b7: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
                b1 = *src.offset(i as isize) as core::ffi::c_uchar;
                if (i + 1 as core::ffi::c_int) < size {
                    b2 = *src.offset((i + 1 as core::ffi::c_int) as isize) as core::ffi::c_uchar;
                }
                if (i + 2 as core::ffi::c_int) < size {
                    b3 = *src.offset((i + 2 as core::ffi::c_int) as isize) as core::ffi::c_uchar;
                }
                b4 = (b1 as core::ffi::c_int >> 2 as core::ffi::c_int) as core::ffi::c_uchar;
                b5 = ((b1 as core::ffi::c_int & 0x3 as core::ffi::c_int) << 4 as core::ffi::c_int
                    | b2 as core::ffi::c_int >> 4 as core::ffi::c_int)
                    as core::ffi::c_uchar;
                b6 = ((b2 as core::ffi::c_int & 0xf as core::ffi::c_int) << 2 as core::ffi::c_int
                    | b3 as core::ffi::c_int >> 6 as core::ffi::c_int)
                    as core::ffi::c_uchar;
                b7 = (b3 as core::ffi::c_int & 0x3f as core::ffi::c_int) as core::ffi::c_uchar;
                *p = encode(b4);
                let fresh0 = *p;
                p = p.offset(1);
                *p = encode(b5);
                let fresh1 = *p;
                p = p.offset(1);
                if (i + 1 as core::ffi::c_int) < size {
                    *p = encode(b6);
                    let fresh2 = *p;
                    p = p.offset(1);
                } else {
                    *p = '=' as i32 as core::ffi::c_char;
                    let fresh3 = *p;
                    p = p.offset(1);
                }
                if (i + 2 as core::ffi::c_int) < size {
                    *p = encode(b7);
                    let fresh4 = *p;
                    p = p.offset(1);
                } else {
                    *p = '=' as i32 as core::ffi::c_char;
                    let fresh5 = *p;
                    p = p.offset(1);
                }
                i += 3 as core::ffi::c_int;
            }
            out
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("encode_base64_lib", SOURCE);
}
