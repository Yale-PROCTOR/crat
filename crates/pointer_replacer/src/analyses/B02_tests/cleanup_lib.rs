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
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn snprintf(
                __s: *mut core::ffi::c_char,
                __maxlen: size_t,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn strncmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
                __n: size_t,
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
        }
        pub type size_t = usize;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn cleanup(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            c: core::ffi::c_int,
            d: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let numbers: [core::ffi::c_int; 4] = [a, b, c, d];
            let mut dynamic_str: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let expected_str: *const core::ffi::c_char =
                b"VALID\0" as *const u8 as *const core::ffi::c_char;
            let input_str: *const core::ffi::c_char =
                b"VALID\0" as *const u8 as *const core::ffi::c_char;
            if {
                let __arg_2 = strlen(expected_str);
                strncmp(input_str, expected_str, __arg_2)
            } != 0 as core::ffi::c_int
            {
                printf(
                    b"Input string validation failed.\n\0" as *const u8 as *const core::ffi::c_char,
                );
            } else {
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while i < 4 as core::ffi::c_int {
                    let current_block_5: u64;
                    match numbers[i as usize] {
                        10 => {
                            result += 10 as core::ffi::c_int;
                            current_block_5 = 13053408596401462044;
                        }
                        20 => {
                            current_block_5 = 13053408596401462044;
                        }
                        30 => {
                            result += 30 as core::ffi::c_int;
                            current_block_5 = 186573557016350645;
                        }
                        40 => {
                            current_block_5 = 186573557016350645;
                        }
                        _ => {
                            result += numbers[i as usize];
                            current_block_5 = 1841672684692190573;
                        }
                    }
                    match current_block_5 {
                        13053408596401462044 => {
                            result += 20 as core::ffi::c_int;
                        }
                        186573557016350645 => {
                            result += 40 as core::ffi::c_int;
                        }
                        _ => {}
                    }
                    i += 1;
                }
                dynamic_str = malloc(
                    (50 as size_t)
                        .wrapping_mul(::core::mem::size_of::<core::ffi::c_char>() as size_t),
                ) as *mut core::ffi::c_char;
                if dynamic_str.is_null() {
                    printf(
                        b"Memory allocation failed.\n\0" as *const u8 as *const core::ffi::c_char,
                    );
                } else {
                    snprintf(
                        dynamic_str,
                        50 as size_t,
                        b"Processed numbers: %s\0" as *const u8 as *const core::ffi::c_char,
                        b"numbers\0" as *const u8 as *const core::ffi::c_char,
                    );
                    printf(
                        b"%s\n\0" as *const u8 as *const core::ffi::c_char,
                        dynamic_str,
                    );
                }
            }
            cleanup_resources(dynamic_str);
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_result(
            label: *const core::ffi::c_char,
            result: core::ffi::c_int,
        ) {
            printf(
                b"%s: %d\n\0" as *const u8 as *const core::ffi::c_char,
                label,
                result,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cleanup_resources(mut dynamic_str: *mut core::ffi::c_char) {
            if !dynamic_str.is_null() {
                free(dynamic_str as *mut core::ffi::c_void);
                dynamic_str = std::ptr::null_mut::<core::ffi::c_char>();
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("cleanup_lib", SOURCE, &["cleanup#dynamic_str"], &[]);
}
