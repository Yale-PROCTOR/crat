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
    pub mod container_of {
        extern "C" {
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
            fn memset(
                __s: *mut core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct test {
            pub a: core::ffi::c_int,
            pub b: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for test {}
        #[automatically_derived]
        impl ::core::clone::Clone for test {
            #[inline]
            fn clone(&self) -> test {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_container_of_a(i: *mut core::ffi::c_int) -> *mut test {
            {
                (i as *mut core::ffi::c_char).offset(
                    -({
                        builtin # offset_of(crate::src::container_of::test, a)
                    } as isize),
                ) as *mut test
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_container_of_b(i: *mut core::ffi::c_int) -> *mut test {
            {
                (i as *mut core::ffi::c_char).offset(
                    -({
                        builtin # offset_of(crate::src::container_of::test, b)
                    } as isize),
                ) as *mut test
            }
        }
        unsafe fn main_0(
            argc: core::ffi::c_int,
            argv: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            let a: core::ffi::c_int = atoi(*argv.offset(1 as core::ffi::c_int as isize));
            let b: core::ffi::c_int = atoi(*argv.offset(2 as core::ffi::c_int as isize));
            let mut t: test = test { a: 0, b: 0 };
            memset(
                &mut t as *mut test as *mut core::ffi::c_void,
                0 as core::ffi::c_int,
                ::core::mem::size_of::<test>() as size_t,
            );
            t.a = a;
            t.b = b;
            printf(
                b"%d\n\0" as *const u8 as *const core::ffi::c_char,
                (*find_container_of_a(&mut t.a)).a + (*find_container_of_b(&mut t.b)).b,
            );
            0
        }
        pub fn main() {
            let mut args: Vec<*mut core::ffi::c_char> = Vec::new();
            for arg in ::std::env::args() {
                args.push(
                    (::std::ffi::CString::new(arg))
                        .expect("Failed to convert argument into CString.")
                        .into_raw(),
                );
            }
            args.push(::core::ptr::null_mut());
            unsafe {
                ::std::process::exit(main_0(
                    (args.len() - 1) as core::ffi::c_int,
                    args.as_mut_ptr() as *mut *mut core::ffi::c_char,
                ) as i32)
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("container_of", SOURCE);
}
