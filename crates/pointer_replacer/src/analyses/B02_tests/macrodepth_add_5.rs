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
    pub mod mdcore {
        extern "C" {
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
        }
        pub const INIT_add: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn op_add(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a + b
        }
        #[no_mangle]
        pub unsafe extern "C" fn op_sub(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a - b
        }
        #[no_mangle]
        pub unsafe extern "C" fn op_mul(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a * b
        }
        unsafe extern "C" fn accum_add(n: core::ffi::c_int) -> core::ffi::c_int {
            let mut acc: core::ffi::c_int = INIT_add;
            match n {
                1 => {
                    acc += 0 as core::ffi::c_int;
                }
                2 => {
                    acc += 0 as core::ffi::c_int;
                    acc += 1 as core::ffi::c_int;
                }
                3 => {
                    acc += 0 as core::ffi::c_int;
                    acc += 1 as core::ffi::c_int;
                    acc += 2 as core::ffi::c_int;
                }
                4 => {
                    acc += 0 as core::ffi::c_int;
                    acc += 1 as core::ffi::c_int;
                    acc += 2 as core::ffi::c_int;
                    acc += 3 as core::ffi::c_int;
                }
                5 => {
                    acc += 0 as core::ffi::c_int;
                    acc += 1 as core::ffi::c_int;
                    acc += 2 as core::ffi::c_int;
                    acc += 3 as core::ffi::c_int;
                    acc += 4 as core::ffi::c_int;
                }
                6 => {
                    acc += 0 as core::ffi::c_int;
                    acc += 1 as core::ffi::c_int;
                    acc += 2 as core::ffi::c_int;
                    acc += 3 as core::ffi::c_int;
                    acc += 4 as core::ffi::c_int;
                    acc += 5 as core::ffi::c_int;
                }
                0 | _ => {}
            }
            acc
        }
        #[no_mangle]
        pub static mut G_OP: Option<
            unsafe extern "C" fn(core::ffi::c_int, core::ffi::c_int) -> core::ffi::c_int,
        > = unsafe {
            Some(
                op_add
                    as unsafe extern "C" fn(core::ffi::c_int, core::ffi::c_int) -> core::ffi::c_int,
            )
        };
        #[no_mangle]
        pub static mut G_OP_NAME: *const core::ffi::c_char =
            b"add\0" as *const u8 as *const core::ffi::c_char;
        #[no_mangle]
        pub unsafe extern "C" fn helper_call(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let r: core::ffi::c_int = op_add(a, b);
            let mut acc: core::ffi::c_int = INIT_add;
            acc += 0 as core::ffi::c_int;
            acc += 1 as core::ffi::c_int;
            acc += 2 as core::ffi::c_int;
            acc += 3 as core::ffi::c_int;
            acc += 4 as core::ffi::c_int;
            printf(
                b"helper.call=%d helper.acc=%d\n\0" as *const u8 as *const core::ffi::c_char,
                r,
                acc,
            );
            r + acc
        }
        #[no_mangle]
        pub unsafe extern "C" fn helper_ptr(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let fp: Option<
                unsafe extern "C" fn(core::ffi::c_int, core::ffi::c_int) -> core::ffi::c_int,
            > = Some(
                op_add
                    as unsafe extern "C" fn(core::ffi::c_int, core::ffi::c_int) -> core::ffi::c_int,
            );
            let r: core::ffi::c_int = fp.expect("non-null function pointer")(a, b);
            printf(
                b"helper.ptr=%d\n\0" as *const u8 as *const core::ffi::c_char,
                r,
            );
            r
        }
        #[no_mangle]
        pub unsafe extern "C" fn use_generated(n: core::ffi::c_int) -> core::ffi::c_int {
            let r: core::ffi::c_int = accum_add(n);
            printf(
                b"gen.acc=%d\n\0" as *const u8 as *const core::ffi::c_char,
                r,
            );
            r
        }
    }
    pub mod mdmain {
        use crate::src::mdcore::helper_call;
        use crate::src::mdcore::helper_ptr;
        use crate::src::mdcore::op_add;
        use crate::src::mdcore::use_generated;
        use crate::src::mdcore::G_OP;
        use crate::src::mdcore::G_OP_NAME;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn strtol(
                __nptr: *const core::ffi::c_char,
                __endptr: *mut *mut core::ffi::c_char,
                __base: core::ffi::c_int,
            ) -> core::ffi::c_long;
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
        }
        pub type size_t = usize;
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
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
        pub type FILE = _IO_FILE;
        pub const REPEAT: core::ffi::c_int = 5 as core::ffi::c_int;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const INIT_add: core::ffi::c_int = 0 as core::ffi::c_int;
        unsafe fn main_0(
            argc: core::ffi::c_int,
            argv: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            if argc < 3 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"usage: %s A B\n\0" as *const u8 as *const core::ffi::c_char,
                    *argv.offset(0 as core::ffi::c_int as isize),
                );
                return 2 as core::ffi::c_int;
            }
            let a: core::ffi::c_int = atoi(*argv.offset(1 as core::ffi::c_int as isize));
            let b: core::ffi::c_int = atoi(*argv.offset(2 as core::ffi::c_int as isize));
            let r_call: core::ffi::c_int = op_add(a, b);
            let mut acc: core::ffi::c_int = INIT_add;
            acc += 0 as core::ffi::c_int;
            acc += 1 as core::ffi::c_int;
            acc += 2 as core::ffi::c_int;
            acc += 3 as core::ffi::c_int;
            acc += 4 as core::ffi::c_int;
            let x1: core::ffi::c_int = helper_call(a, b);
            let x2: core::ffi::c_int = helper_ptr(a, b);
            let x3: core::ffi::c_int = use_generated(REPEAT);
            let g: core::ffi::c_int = G_OP.expect("non-null function pointer")(a, b);
            printf(
                b"op=%s call=%d acc=%d g.call=%d\n\0" as *const u8 as *const core::ffi::c_char,
                G_OP_NAME,
                r_call,
                acc,
                g,
            );
            printf(
                b"summary=%d\n\0" as *const u8 as *const core::ffi::c_char,
                r_call + acc + x1 + x2 + x3 + g,
            );
            0 as core::ffi::c_int
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
    run_ownership_case("macrodepth_add_5", SOURCE);
}
