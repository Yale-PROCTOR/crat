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
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn memset(
                __s: *mut core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn __assert_fail(
                __assertion: *const core::ffi::c_char,
                __file: *const core::ffi::c_char,
                __line: core::ffi::c_uint,
                __function: *const core::ffi::c_char,
            ) -> !;
        }
        pub type size_t = usize;
        pub type __uint8_t = u8;
        pub type __uint16_t = u16;
        pub type __uint32_t = u32;
        pub type __uint64_t = u64;
        pub type uint8_t = __uint8_t;
        pub type uint16_t = __uint16_t;
        pub type uint32_t = __uint32_t;
        pub type uint64_t = __uint64_t;
        #[repr(C)]
        pub struct cp_state_t {
            pub bits: uint64_t,
            pub count: core::ffi::c_int,
            pub words: *mut uint32_t,
            pub word_count: core::ffi::c_int,
            pub word_index: core::ffi::c_int,
            pub bits_left: core::ffi::c_int,
            pub final_word_available: core::ffi::c_int,
            pub final_word: uint32_t,
            pub out: *mut core::ffi::c_char,
            pub out_end: *mut core::ffi::c_char,
            pub begin: *mut core::ffi::c_char,
            pub lookup: [uint16_t; 512],
            pub lit: [uint32_t; 288],
            pub dst: [uint32_t; 32],
            pub len: [uint32_t; 19],
            pub nlit: uint32_t,
            pub ndst: uint32_t,
            pub nlen: uint32_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for cp_state_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for cp_state_t {
            #[inline]
            fn clone(&self) -> cp_state_t {
                let _: ::core::clone::AssertParamIsClone<uint64_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut uint32_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<uint32_t>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<[uint16_t; 512]>;
                let _: ::core::clone::AssertParamIsClone<[uint32_t; 288]>;
                let _: ::core::clone::AssertParamIsClone<[uint32_t; 32]>;
                let _: ::core::clone::AssertParamIsClone<[uint32_t; 19]>;
                *self
            }
        }
        #[no_mangle]
        pub static mut cp_error_reason: *const core::ffi::c_char = 0 as *const core::ffi::c_char;
        #[no_mangle]
        pub static mut cp_fixed_table: [uint8_t; 320] = [
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
        ];
        #[no_mangle]
        pub static mut cp_permutation_order: [uint8_t; 19] = [
            16 as core::ffi::c_int as uint8_t,
            17 as core::ffi::c_int as uint8_t,
            18 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            6 as core::ffi::c_int as uint8_t,
            10 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            11 as core::ffi::c_int as uint8_t,
            4 as core::ffi::c_int as uint8_t,
            12 as core::ffi::c_int as uint8_t,
            3 as core::ffi::c_int as uint8_t,
            13 as core::ffi::c_int as uint8_t,
            2 as core::ffi::c_int as uint8_t,
            14 as core::ffi::c_int as uint8_t,
            1 as core::ffi::c_int as uint8_t,
            15 as core::ffi::c_int as uint8_t,
        ];
        #[no_mangle]
        pub static mut cp_len_extra_bits: [uint8_t; 31] = [
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            1 as core::ffi::c_int as uint8_t,
            1 as core::ffi::c_int as uint8_t,
            1 as core::ffi::c_int as uint8_t,
            1 as core::ffi::c_int as uint8_t,
            2 as core::ffi::c_int as uint8_t,
            2 as core::ffi::c_int as uint8_t,
            2 as core::ffi::c_int as uint8_t,
            2 as core::ffi::c_int as uint8_t,
            3 as core::ffi::c_int as uint8_t,
            3 as core::ffi::c_int as uint8_t,
            3 as core::ffi::c_int as uint8_t,
            3 as core::ffi::c_int as uint8_t,
            4 as core::ffi::c_int as uint8_t,
            4 as core::ffi::c_int as uint8_t,
            4 as core::ffi::c_int as uint8_t,
            4 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
        ];
        #[no_mangle]
        pub static mut cp_len_base: [uint32_t; 31] = [
            3 as core::ffi::c_int as uint32_t,
            4 as core::ffi::c_int as uint32_t,
            5 as core::ffi::c_int as uint32_t,
            6 as core::ffi::c_int as uint32_t,
            7 as core::ffi::c_int as uint32_t,
            8 as core::ffi::c_int as uint32_t,
            9 as core::ffi::c_int as uint32_t,
            10 as core::ffi::c_int as uint32_t,
            11 as core::ffi::c_int as uint32_t,
            13 as core::ffi::c_int as uint32_t,
            15 as core::ffi::c_int as uint32_t,
            17 as core::ffi::c_int as uint32_t,
            19 as core::ffi::c_int as uint32_t,
            23 as core::ffi::c_int as uint32_t,
            27 as core::ffi::c_int as uint32_t,
            31 as core::ffi::c_int as uint32_t,
            35 as core::ffi::c_int as uint32_t,
            43 as core::ffi::c_int as uint32_t,
            51 as core::ffi::c_int as uint32_t,
            59 as core::ffi::c_int as uint32_t,
            67 as core::ffi::c_int as uint32_t,
            83 as core::ffi::c_int as uint32_t,
            99 as core::ffi::c_int as uint32_t,
            115 as core::ffi::c_int as uint32_t,
            131 as core::ffi::c_int as uint32_t,
            163 as core::ffi::c_int as uint32_t,
            195 as core::ffi::c_int as uint32_t,
            227 as core::ffi::c_int as uint32_t,
            258 as core::ffi::c_int as uint32_t,
            0 as core::ffi::c_int as uint32_t,
            0 as core::ffi::c_int as uint32_t,
        ];
        #[no_mangle]
        pub static mut cp_dist_extra_bits: [uint8_t; 32] = [
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            1 as core::ffi::c_int as uint8_t,
            1 as core::ffi::c_int as uint8_t,
            2 as core::ffi::c_int as uint8_t,
            2 as core::ffi::c_int as uint8_t,
            3 as core::ffi::c_int as uint8_t,
            3 as core::ffi::c_int as uint8_t,
            4 as core::ffi::c_int as uint8_t,
            4 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            5 as core::ffi::c_int as uint8_t,
            6 as core::ffi::c_int as uint8_t,
            6 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            7 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            8 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            9 as core::ffi::c_int as uint8_t,
            10 as core::ffi::c_int as uint8_t,
            10 as core::ffi::c_int as uint8_t,
            11 as core::ffi::c_int as uint8_t,
            11 as core::ffi::c_int as uint8_t,
            12 as core::ffi::c_int as uint8_t,
            12 as core::ffi::c_int as uint8_t,
            13 as core::ffi::c_int as uint8_t,
            13 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
            0 as core::ffi::c_int as uint8_t,
        ];
        #[no_mangle]
        pub static mut cp_dist_base: [uint32_t; 32] = [
            1 as core::ffi::c_int as uint32_t,
            2 as core::ffi::c_int as uint32_t,
            3 as core::ffi::c_int as uint32_t,
            4 as core::ffi::c_int as uint32_t,
            5 as core::ffi::c_int as uint32_t,
            7 as core::ffi::c_int as uint32_t,
            9 as core::ffi::c_int as uint32_t,
            13 as core::ffi::c_int as uint32_t,
            17 as core::ffi::c_int as uint32_t,
            25 as core::ffi::c_int as uint32_t,
            33 as core::ffi::c_int as uint32_t,
            49 as core::ffi::c_int as uint32_t,
            65 as core::ffi::c_int as uint32_t,
            97 as core::ffi::c_int as uint32_t,
            129 as core::ffi::c_int as uint32_t,
            193 as core::ffi::c_int as uint32_t,
            257 as core::ffi::c_int as uint32_t,
            385 as core::ffi::c_int as uint32_t,
            513 as core::ffi::c_int as uint32_t,
            769 as core::ffi::c_int as uint32_t,
            1025 as core::ffi::c_int as uint32_t,
            1537 as core::ffi::c_int as uint32_t,
            2049 as core::ffi::c_int as uint32_t,
            3073 as core::ffi::c_int as uint32_t,
            4097 as core::ffi::c_int as uint32_t,
            6145 as core::ffi::c_int as uint32_t,
            8193 as core::ffi::c_int as uint32_t,
            12289 as core::ffi::c_int as uint32_t,
            16385 as core::ffi::c_int as uint32_t,
            24577 as core::ffi::c_int as uint32_t,
            0 as core::ffi::c_int as uint32_t,
            0 as core::ffi::c_int as uint32_t,
        ];
        unsafe extern "C" fn cp_would_overflow(
            s: *mut cp_state_t,
            num_bits: core::ffi::c_int,
        ) -> core::ffi::c_int {
            ((*s).bits_left + (*s).count - num_bits < 0 as core::ffi::c_int) as core::ffi::c_int
        }
        unsafe extern "C" fn cp_ptr(s: *mut cp_state_t) -> *mut core::ffi::c_char {
            if (*s).bits_left & 7 as core::ffi::c_int == 0 {
            } else {
                __assert_fail(b"!(s->bits_left & 7)\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    95 as core::ffi::c_uint,
                    ([b'c' as i8, b'h' as i8, b'a' as i8, b'r' as i8,
                                    b' ' as i8, b'*' as i8, b'c' as i8, b'p' as i8, b'_' as i8,
                                    b'p' as i8, b't' as i8, b'r' as i8, b'(' as i8, b'c' as i8,
                                    b'p' as i8, b'_' as i8, b's' as i8, b't' as i8, b'a' as i8,
                                    b't' as i8, b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                    b'*' as i8, b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_4846: {};
            (((*s).words).offset((*s).word_index as isize) as *mut core::ffi::c_char)
                .offset(-(((*s).count / 8 as core::ffi::c_int) as isize))
        }
        unsafe extern "C" fn cp_peak_bits(
            s: *mut cp_state_t,
            num_bits_to_read: core::ffi::c_int,
        ) -> uint64_t {
            if (*s).count < num_bits_to_read {
                if (*s).word_index < (*s).word_count {
                    let fresh3 = (*s).word_index;
                    (*s).word_index += 1;
                    let word: uint32_t = *((*s).words).offset(fresh3 as isize);
                    (*s).bits = ((*s).bits as core::ffi::c_ulong
                        | ((word as uint64_t) << (*s).count) as core::ffi::c_ulong)
                        as uint64_t;
                    (*s).count += 32 as core::ffi::c_int;
                    if (*s).word_index <= (*s).word_count {
                    } else {
                        __assert_fail(b"s->word_index <= s->word_count\0" as
                                    *const u8 as *const core::ffi::c_char,
                            b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                                    as *const u8 as *const core::ffi::c_char,
                            104 as core::ffi::c_uint,
                            ([b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                            b'6' as i8, b'4' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                            b'c' as i8, b'p' as i8, b'_' as i8, b'p' as i8, b'e' as i8,
                                            b'a' as i8, b'k' as i8, b'_' as i8, b'b' as i8, b'i' as i8,
                                            b't' as i8, b's' as i8, b'(' as i8, b'c' as i8, b'p' as i8,
                                            b'_' as i8, b's' as i8, b't' as i8, b'a' as i8, b't' as i8,
                                            b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8,
                                            b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                            b')' as i8, b'\0' as i8]).as_ptr());
                    }
                    'c_2429: {};
                } else if (*s).final_word_available != 0 {
                    let word_0: uint32_t = (*s).final_word;
                    (*s).bits = ((*s).bits as core::ffi::c_ulong
                        | ((word_0 as uint64_t) << (*s).count) as core::ffi::c_ulong)
                        as uint64_t;
                    (*s).count += (*s).bits_left;
                    (*s).final_word_available = 0 as core::ffi::c_int;
                }
            }
            (*s).bits
        }
        unsafe extern "C" fn cp_consume_bits(
            s: *mut cp_state_t,
            num_bits_to_read: core::ffi::c_int,
        ) -> uint32_t {
            if (*s).count >= num_bits_to_read {
            } else {
                __assert_fail(b"s->count >= num_bits_to_read\0" as *const u8
                        as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    115 as core::ffi::c_uint,
                    ([b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b'3' as i8, b'2' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b'c' as i8, b'o' as i8,
                                    b'n' as i8, b's' as i8, b'u' as i8, b'm' as i8, b'e' as i8,
                                    b'_' as i8, b'b' as i8, b'i' as i8, b't' as i8, b's' as i8,
                                    b'(' as i8, b'c' as i8, b'p' as i8, b'_' as i8, b's' as i8,
                                    b't' as i8, b'a' as i8, b't' as i8, b'e' as i8, b'_' as i8,
                                    b't' as i8, b' ' as i8, b'*' as i8, b',' as i8, b' ' as i8,
                                    b'i' as i8, b'n' as i8, b't' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2253: {};
            let bits: uint32_t = ((*s).bits
                & ((1 as core::ffi::c_int as uint64_t) << num_bits_to_read)
                    .wrapping_sub(1 as uint64_t)) as uint32_t;
            (*s).bits >>= num_bits_to_read;
            (*s).count -= num_bits_to_read;
            (*s).bits_left -= num_bits_to_read;
            bits
        }
        unsafe extern "C" fn cp_read_bits(
            s: *mut cp_state_t,
            num_bits_to_read: core::ffi::c_int,
        ) -> uint32_t {
            if num_bits_to_read <= 32 as core::ffi::c_int {
            } else {
                __assert_fail(b"num_bits_to_read <= 32\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    123 as core::ffi::c_uint,
                    ([b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b'3' as i8, b'2' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b'r' as i8, b'e' as i8,
                                    b'a' as i8, b'd' as i8, b'_' as i8, b'b' as i8, b'i' as i8,
                                    b't' as i8, b's' as i8, b'(' as i8, b'c' as i8, b'p' as i8,
                                    b'_' as i8, b's' as i8, b't' as i8, b'a' as i8, b't' as i8,
                                    b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8,
                                    b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_3039: {};
            if num_bits_to_read >= 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"num_bits_to_read >= 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    124 as core::ffi::c_uint,
                    ([b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b'3' as i8, b'2' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b'r' as i8, b'e' as i8,
                                    b'a' as i8, b'd' as i8, b'_' as i8, b'b' as i8, b'i' as i8,
                                    b't' as i8, b's' as i8, b'(' as i8, b'c' as i8, b'p' as i8,
                                    b'_' as i8, b's' as i8, b't' as i8, b'a' as i8, b't' as i8,
                                    b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8,
                                    b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_3002: {};
            if (*s).bits_left > 0 as core::ffi::c_int {
            } else {
                __assert_fail(b"s->bits_left > 0\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    125 as core::ffi::c_uint,
                    ([b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b'3' as i8, b'2' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b'r' as i8, b'e' as i8,
                                    b'a' as i8, b'd' as i8, b'_' as i8, b'b' as i8, b'i' as i8,
                                    b't' as i8, b's' as i8, b'(' as i8, b'c' as i8, b'p' as i8,
                                    b'_' as i8, b's' as i8, b't' as i8, b'a' as i8, b't' as i8,
                                    b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8,
                                    b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_2961: {};
            if (*s).count <= 64 as core::ffi::c_int {
            } else {
                __assert_fail(b"s->count <= 64\0" as *const u8 as
                        *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    126 as core::ffi::c_uint,
                    ([b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b'3' as i8, b'2' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b'r' as i8, b'e' as i8,
                                    b'a' as i8, b'd' as i8, b'_' as i8, b'b' as i8, b'i' as i8,
                                    b't' as i8, b's' as i8, b'(' as i8, b'c' as i8, b'p' as i8,
                                    b'_' as i8, b's' as i8, b't' as i8, b'a' as i8, b't' as i8,
                                    b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8,
                                    b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_2920: {};
            if cp_would_overflow(s, num_bits_to_read) == 0 {
            } else {
                __assert_fail(b"!cp_would_overflow(s, num_bits_to_read)\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    127 as core::ffi::c_uint,
                    ([b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b'3' as i8, b'2' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b'r' as i8, b'e' as i8,
                                    b'a' as i8, b'd' as i8, b'_' as i8, b'b' as i8, b'i' as i8,
                                    b't' as i8, b's' as i8, b'(' as i8, b'c' as i8, b'p' as i8,
                                    b'_' as i8, b's' as i8, b't' as i8, b'a' as i8, b't' as i8,
                                    b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8,
                                    b',' as i8, b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8,
                                    b')' as i8, b'\0' as i8]).as_ptr());
            }
            'c_2852: {};
            cp_peak_bits(s, num_bits_to_read);
            let bits: uint32_t = cp_consume_bits(s, num_bits_to_read);
            bits
        }
        unsafe extern "C" fn cp_rev16(mut a: uint32_t) -> uint32_t {
            a = (a & 0xaaaa as uint32_t) >> 1 as core::ffi::c_int
                | (a & 0x5555 as uint32_t) << 1 as core::ffi::c_int;
            a = (a & 0xcccc as uint32_t) >> 2 as core::ffi::c_int
                | (a & 0x3333 as uint32_t) << 2 as core::ffi::c_int;
            a = (a & 0xf0f0 as uint32_t) >> 4 as core::ffi::c_int
                | (a & 0xf0f as uint32_t) << 4 as core::ffi::c_int;
            a = (a & 0xff00 as uint32_t) >> 8 as core::ffi::c_int
                | (a & 0xff as uint32_t) << 8 as core::ffi::c_int;
            a
        }
        unsafe extern "C" fn cp_build(
            s: *mut cp_state_t,
            tree: *mut uint32_t,
            lens: *mut uint8_t,
            sym_count: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut n: core::ffi::c_int = 0;
            let mut codes: [core::ffi::c_int; 16] = [0; 16];
            let mut first: [core::ffi::c_int; 16] = [0; 16];
            let mut counts: [core::ffi::c_int; 16] = [0 as core::ffi::c_int; 16];
            n = 0 as core::ffi::c_int;
            while n < sym_count {
                counts[*lens.offset(n as isize) as usize] += 1;
                n += 1;
            }
            first[0 as core::ffi::c_int as usize] = 0 as core::ffi::c_int;
            codes[0 as core::ffi::c_int as usize] = first[0 as core::ffi::c_int as usize];
            counts[0 as core::ffi::c_int as usize] = codes[0 as core::ffi::c_int as usize];
            n = 1 as core::ffi::c_int;
            while n <= 15 as core::ffi::c_int {
                codes[n as usize] = (codes[(n - 1 as core::ffi::c_int) as usize]
                    + counts[(n - 1 as core::ffi::c_int) as usize])
                    << 1 as core::ffi::c_int;
                first[n as usize] = first[(n - 1 as core::ffi::c_int) as usize]
                    + counts[(n - 1 as core::ffi::c_int) as usize];
                n += 1;
            }
            if !s.is_null() {
                memset(
                    ((*s).lookup).as_mut_ptr() as *mut core::ffi::c_void,
                    0 as core::ffi::c_int,
                    ::core::mem::size_of::<[uint16_t; 512]>() as size_t,
                );
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < sym_count {
                let len: core::ffi::c_int = *lens.offset(i as isize) as core::ffi::c_int;
                if len != 0 as core::ffi::c_int {
                    if len < 16 as core::ffi::c_int {
                    } else {
                        __assert_fail(b"len < 16\0" as *const u8 as
                                *const core::ffi::c_char,
                            b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                                    as *const u8 as *const core::ffi::c_char,
                            154 as core::ffi::c_uint,
                            ([b'i' as i8, b'n' as i8, b't' as i8, b' ' as i8,
                                            b'c' as i8, b'p' as i8, b'_' as i8, b'b' as i8, b'u' as i8,
                                            b'i' as i8, b'l' as i8, b'd' as i8, b'(' as i8, b'c' as i8,
                                            b'p' as i8, b'_' as i8, b's' as i8, b't' as i8, b'a' as i8,
                                            b't' as i8, b'e' as i8, b'_' as i8, b't' as i8, b' ' as i8,
                                            b'*' as i8, b',' as i8, b' ' as i8, b'u' as i8, b'i' as i8,
                                            b'n' as i8, b't' as i8, b'3' as i8, b'2' as i8, b'_' as i8,
                                            b't' as i8, b' ' as i8, b'*' as i8, b',' as i8, b' ' as i8,
                                            b'u' as i8, b'i' as i8, b'n' as i8, b't' as i8, b'8' as i8,
                                            b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                                            b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8, b')' as i8,
                                            b'\0' as i8]).as_ptr());
                    }
                    'c_3605: {};
                    let fresh5 = codes[len as usize];
                    codes[len as usize] += 1;
                    let code: uint32_t = fresh5 as uint32_t;
                    let fresh6 = first[len as usize];
                    first[len as usize] += 1;
                    let slot: uint32_t = fresh6 as uint32_t;
                    *tree.offset(slot as isize) = code << (32 as core::ffi::c_int - len)
                        | (i << 4 as core::ffi::c_int) as uint32_t
                        | len as uint32_t;
                    if !s.is_null() && len <= 9 as core::ffi::c_int {
                        let mut j: core::ffi::c_int =
                            (cp_rev16(code) >> (16 as core::ffi::c_int - len)) as core::ffi::c_int;
                        while j < (1 as core::ffi::c_int) << 9 as core::ffi::c_int {
                            (*s).lookup[j as usize] =
                                (len << 9 as core::ffi::c_int | i) as uint16_t;
                            j += (1 as core::ffi::c_int) << len;
                        }
                    }
                }
                i += 1;
            }
            let max_index: core::ffi::c_int = first[15 as core::ffi::c_int as usize];
            max_index
        }
        unsafe extern "C" fn cp_stored(s: *mut cp_state_t) -> core::ffi::c_int {
            let mut p: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            cp_read_bits(s, (*s).count & 7 as core::ffi::c_int);
            let LEN: uint16_t = cp_read_bits(s, 16 as core::ffi::c_int) as uint16_t;
            let NLEN: uint16_t = cp_read_bits(s, 16 as core::ffi::c_int) as uint16_t;
            if LEN as core::ffi::c_int
                != !(NLEN as core::ffi::c_int) as uint16_t as core::ffi::c_int
            {
                cp_error_reason =
                    b"Failed to find LEN and NLEN as complements within stored (uncompressed) stream.\0"
                            as *const u8 as *const core::ffi::c_char;
            } else if (*s).bits_left / 8 as core::ffi::c_int > LEN as core::ffi::c_int {
                cp_error_reason = b"Stored block extends beyond end of input stream.\0" as *const u8
                    as *const core::ffi::c_char;
            } else {
                p = cp_ptr(s);
                memcpy(
                    (*s).out as *mut core::ffi::c_void,
                    p as *const core::ffi::c_void,
                    LEN as size_t,
                );
                (*s).out = ((*s).out).offset(LEN as core::ffi::c_int as isize);
                return 1 as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        unsafe extern "C" fn cp_fixed(s: *mut cp_state_t) -> core::ffi::c_int {
            (*s).nlit = cp_build(
                s,
                ((*s).lit).as_mut_ptr(),
                cp_fixed_table.as_mut_ptr(),
                288 as core::ffi::c_int,
            ) as uint32_t;
            (*s).ndst = cp_build(
                std::ptr::null_mut::<cp_state_t>(),
                ((*s).dst).as_mut_ptr(),
                cp_fixed_table
                    .as_mut_ptr()
                    .offset(288 as core::ffi::c_int as isize),
                32 as core::ffi::c_int,
            ) as uint32_t;
            1 as core::ffi::c_int
        }
        unsafe extern "C" fn cp_decode(
            s: *mut cp_state_t,
            tree: *mut uint32_t,
            mut hi: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let bits: uint64_t = cp_peak_bits(s, 16 as core::ffi::c_int);
            let search: uint32_t =
                cp_rev16(bits as uint32_t) << 16 as core::ffi::c_int | 0xffff as uint32_t;
            let mut lo: core::ffi::c_int = 0 as core::ffi::c_int;
            while lo < hi {
                let guess: core::ffi::c_int = (lo + hi) >> 1 as core::ffi::c_int;
                if search < *tree.offset(guess as isize) {
                    hi = guess;
                } else {
                    lo = guess + 1 as core::ffi::c_int;
                }
            }
            let key: uint32_t = *tree.offset((lo - 1 as core::ffi::c_int) as isize);
            let len: uint32_t = (32 as uint32_t).wrapping_sub(key & 0xf as uint32_t);
            if search >> len == key >> len {
            } else {
                __assert_fail(b"(search >> len) == (key >> len)\0" as
                            *const u8 as *const core::ffi::c_char,
                    b"/home/ubuntu/Test-Corpus/Public-Tests/B02_organic/pinflate_lib/src/pinflate_lib/test_case/src/lib.c\0"
                            as *const u8 as *const core::ffi::c_char,
                    217 as core::ffi::c_uint,
                    ([b'i' as i8, b'n' as i8, b't' as i8, b' ' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b'd' as i8, b'e' as i8,
                                    b'c' as i8, b'o' as i8, b'd' as i8, b'e' as i8, b'(' as i8,
                                    b'c' as i8, b'p' as i8, b'_' as i8, b's' as i8, b't' as i8,
                                    b'a' as i8, b't' as i8, b'e' as i8, b'_' as i8, b't' as i8,
                                    b' ' as i8, b'*' as i8, b',' as i8, b' ' as i8, b'u' as i8,
                                    b'i' as i8, b'n' as i8, b't' as i8, b'3' as i8, b'2' as i8,
                                    b'_' as i8, b't' as i8, b' ' as i8, b'*' as i8, b',' as i8,
                                    b' ' as i8, b'i' as i8, b'n' as i8, b't' as i8, b')' as i8,
                                    b'\0' as i8]).as_ptr());
            }
            'c_2300: {};
            let code: core::ffi::c_int =
                cp_consume_bits(s, (key & 0xf as uint32_t) as core::ffi::c_int) as core::ffi::c_int;
            (key >> 4 as core::ffi::c_int & 0xfff as uint32_t) as core::ffi::c_int
        }
        unsafe extern "C" fn cp_dynamic(s: *mut cp_state_t) -> core::ffi::c_int {
            let mut lenlens: [uint8_t; 19] = [
                0 as core::ffi::c_int as uint8_t,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
            ];
            let nlit: core::ffi::c_int = (257 as uint32_t)
                .wrapping_add(cp_read_bits(s, 5 as core::ffi::c_int))
                as core::ffi::c_int;
            let ndst: core::ffi::c_int = (1 as uint32_t)
                .wrapping_add(cp_read_bits(s, 5 as core::ffi::c_int))
                as core::ffi::c_int;
            let nlen: core::ffi::c_int = (4 as uint32_t)
                .wrapping_add(cp_read_bits(s, 4 as core::ffi::c_int))
                as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < nlen {
                lenlens[cp_permutation_order[i as usize] as usize] =
                    cp_read_bits(s, 3 as core::ffi::c_int) as uint8_t;
                i += 1;
            }
            (*s).nlen = cp_build(
                std::ptr::null_mut::<cp_state_t>(),
                ((*s).len).as_mut_ptr(),
                lenlens.as_mut_ptr(),
                19 as core::ffi::c_int,
            ) as uint32_t;
            let mut lens: [uint8_t; 320] = [0; 320];
            let mut n: core::ffi::c_int = 0 as core::ffi::c_int;
            while n < nlit + ndst {
                let sym: core::ffi::c_int =
                    cp_decode(s, ((*s).len).as_mut_ptr(), (*s).nlen as core::ffi::c_int);
                match sym {
                    16 => {
                        let mut i_0: core::ffi::c_int = (3 as uint32_t)
                            .wrapping_add(cp_read_bits(s, 2 as core::ffi::c_int))
                            as core::ffi::c_int;
                        while i_0 != 0 {
                            lens[n as usize] = lens[(n - 1 as core::ffi::c_int) as usize];
                            i_0 -= 1;
                            n += 1;
                        }
                    }
                    17 => {
                        let mut i_1: core::ffi::c_int = (3 as uint32_t)
                            .wrapping_add(cp_read_bits(s, 3 as core::ffi::c_int))
                            as core::ffi::c_int;
                        while i_1 != 0 {
                            lens[n as usize] = 0 as uint8_t;
                            i_1 -= 1;
                            n += 1;
                        }
                    }
                    18 => {
                        let mut i_2: core::ffi::c_int = (11 as uint32_t)
                            .wrapping_add(cp_read_bits(s, 7 as core::ffi::c_int))
                            as core::ffi::c_int;
                        while i_2 != 0 {
                            lens[n as usize] = 0 as uint8_t;
                            i_2 -= 1;
                            n += 1;
                        }
                    }
                    _ => {
                        let fresh4 = n;
                        n += 1;
                        lens[fresh4 as usize] = sym as uint8_t;
                    }
                }
            }
            (*s).nlit = cp_build(s, ((*s).lit).as_mut_ptr(), lens.as_mut_ptr(), nlit) as uint32_t;
            (*s).ndst = cp_build(
                std::ptr::null_mut::<cp_state_t>(),
                ((*s).dst).as_mut_ptr(),
                lens.as_mut_ptr().offset(nlit as isize),
                ndst,
            ) as uint32_t;
            1 as core::ffi::c_int
        }
        unsafe extern "C" fn cp_block(s: *mut cp_state_t) -> core::ffi::c_int {
            let current_block: u64;
            loop {
                let mut symbol: core::ffi::c_int =
                    cp_decode(s, ((*s).lit).as_mut_ptr(), (*s).nlit as core::ffi::c_int);
                if symbol < 256 as core::ffi::c_int {
                    if ((*s).out).offset(1 as core::ffi::c_int as isize) > (*s).out_end {
                        cp_error_reason =
                            b"Attempted to overwrite out buffer while outputting a symbol.\0"
                                as *const u8
                                as *const core::ffi::c_char;
                        current_block = 10862015606883543423;
                        break;
                    } else {
                        *(*s).out = symbol as core::ffi::c_char;
                        (*s).out = ((*s).out).offset(1 as core::ffi::c_int as isize);
                    }
                } else {
                    if symbol <= 256 as core::ffi::c_int {
                        current_block = 17788412896529399552;
                        break;
                    }
                    symbol -= 257 as core::ffi::c_int;
                    let mut length: core::ffi::c_int =
                        (cp_read_bits(s, cp_len_extra_bits[symbol as usize] as core::ffi::c_int))
                            .wrapping_add(cp_len_base[symbol as usize])
                            as core::ffi::c_int;
                    let distance_symbol: core::ffi::c_int =
                        cp_decode(s, ((*s).dst).as_mut_ptr(), (*s).ndst as core::ffi::c_int);
                    let backwards_distance: core::ffi::c_int = (cp_read_bits(
                        s,
                        cp_dist_extra_bits[distance_symbol as usize] as core::ffi::c_int,
                    ))
                    .wrapping_add(cp_dist_base[distance_symbol as usize])
                        as core::ffi::c_int;
                    if ((*s).out).offset(-(backwards_distance as isize)) < (*s).begin {
                        cp_error_reason =
                            b"Attempted to write before out buffer (invalid backwards distance).\0"
                                as *const u8
                                as *const core::ffi::c_char;
                        current_block = 10862015606883543423;
                        break;
                    } else if ((*s).out).offset(length as isize) > (*s).out_end {
                        cp_error_reason =
                            b"Attempted to overwrite out buffer while outputting a string.\0"
                                as *const u8
                                as *const core::ffi::c_char;
                        current_block = 10862015606883543423;
                        break;
                    } else {
                        let mut src: *mut core::ffi::c_char =
                            ((*s).out).offset(-(backwards_distance as isize));
                        let mut dst: *mut core::ffi::c_char = (*s).out;
                        (*s).out = ((*s).out).offset(length as isize);
                        match backwards_distance {
                            1 => {
                                memset(
                                    dst as *mut core::ffi::c_void,
                                    *src as core::ffi::c_int,
                                    length as size_t,
                                );
                            }
                            _ => loop {
                                let fresh0 = length;
                                length -= 1;
                                if fresh0 == 0 {
                                    break;
                                }
                                let fresh1 = *src;
                                src = src.offset(1);
                                *dst = fresh1;
                                let fresh2 = *dst;
                                dst = dst.offset(1);
                            },
                        }
                    }
                }
            }
            match current_block {
                17788412896529399552 => 1 as core::ffi::c_int,
                _ => 0 as core::ffi::c_int,
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn pinflate(
            in_0: *mut core::ffi::c_void,
            in_bytes: core::ffi::c_int,
            out: *mut core::ffi::c_void,
            out_bytes: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let current_block: u64;
            let s: *mut cp_state_t =
                calloc(1 as size_t, ::core::mem::size_of::<cp_state_t>() as size_t)
                    as *mut cp_state_t;
            (*s).bits = 0 as uint64_t;
            (*s).count = 0 as core::ffi::c_int;
            (*s).word_index = 0 as core::ffi::c_int;
            (*s).bits_left = in_bytes * 8 as core::ffi::c_int;
            let first_bytes: core::ffi::c_int =
                ((in_0 as size_t).wrapping_add(3 as size_t) & !(3 as core::ffi::c_int) as size_t)
                    .wrapping_sub(in_0 as size_t) as core::ffi::c_int;
            (*s).words =
                (in_0 as *mut core::ffi::c_char).offset(first_bytes as isize) as *mut uint32_t;
            (*s).word_count = (in_bytes - first_bytes) / 4 as core::ffi::c_int;
            let last_bytes: core::ffi::c_int = (in_bytes - first_bytes) & 3 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < first_bytes {
                (*s).bits = ((*s).bits as core::ffi::c_ulong
                    | ((*(in_0 as *mut uint8_t).offset(i as isize) as uint64_t)
                        << (i * 8 as core::ffi::c_int)) as core::ffi::c_ulong)
                    as uint64_t;
                i += 1;
            }
            (*s).final_word_available = if last_bytes != 0 {
                1 as core::ffi::c_int
            } else {
                0 as core::ffi::c_int
            };
            (*s).final_word = 0 as uint32_t;
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < last_bytes {
                (*s).final_word = ((*s).final_word as core::ffi::c_uint
                    | ((*(in_0 as *mut uint8_t).offset((in_bytes - last_bytes + i_0) as isize)
                        as core::ffi::c_int)
                        << (i_0 * 8 as core::ffi::c_int))
                        as core::ffi::c_uint) as uint32_t;
                i_0 += 1;
            }
            (*s).count = first_bytes * 8 as core::ffi::c_int;
            (*s).out = out as *mut core::ffi::c_char;
            (*s).out_end = ((*s).out).offset(out_bytes as isize);
            (*s).begin = out as *mut core::ffi::c_char;
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut bfinal: core::ffi::c_int = 0;
            loop {
                bfinal = cp_read_bits(s, 1 as core::ffi::c_int) as core::ffi::c_int;
                let btype: core::ffi::c_int =
                    cp_read_bits(s, 2 as core::ffi::c_int) as core::ffi::c_int;
                match btype {
                    0 => {
                        if cp_stored(s) == 0 {
                            current_block = 5270165255580589405;
                            break;
                        }
                    }
                    1 => {
                        cp_fixed(s);
                        if cp_block(s) == 0 {
                            current_block = 5270165255580589405;
                            break;
                        }
                    }
                    2 => {
                        cp_dynamic(s);
                        if cp_block(s) == 0 {
                            current_block = 5270165255580589405;
                            break;
                        }
                    }
                    3 => {
                        cp_error_reason = b"Detected unknown block type within input stream.\0"
                            as *const u8
                            as *const core::ffi::c_char;
                        current_block = 5270165255580589405;
                        break;
                    }
                    _ => {}
                }
                count += 1;
                if bfinal != 0 {
                    current_block = 17184638872671510253;
                    break;
                }
            }
            match current_block {
                5270165255580589405 => {
                    free(s as *mut core::ffi::c_void);
                    0 as core::ffi::c_int
                }
                _ => {
                    free(s as *mut core::ffi::c_void);
                    1 as core::ffi::c_int
                }
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("pinflate_lib", SOURCE);
}
