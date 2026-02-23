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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct Result_0 {
            pub value: core::ffi::c_int,
            pub operation: [core::ffi::c_char; 32],
            pub permissions: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Result_0 {}
        #[automatically_derived]
        impl ::core::clone::Clone for Result_0 {
            #[inline]
            fn clone(&self) -> Result_0 {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const READ_PERM: core::ffi::c_int = 0o400 as core::ffi::c_int;
        pub const WRITE_PERM: core::ffi::c_int = 0o200 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn create_result_string(
            op: *const core::ffi::c_char,
            val: core::ffi::c_int,
        ) -> *mut core::ffi::c_char {
            let str: *mut core::ffi::c_char = malloc(
                (64 as size_t).wrapping_mul(::core::mem::size_of::<core::ffi::c_char>() as size_t),
            ) as *mut core::ffi::c_char;
            if str.is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            snprintf(
                str,
                64 as size_t,
                b"Operation: %s, Value: %d\0" as *const u8 as *const core::ffi::c_char,
                op,
                val,
            );
            str
        }
        #[no_mangle]
        pub unsafe extern "C" fn check_permissions(
            perms: core::ffi::c_int,
            required: core::ffi::c_int,
        ) -> core::ffi::c_int {
            (perms & required == required) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn safe_add(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            perms: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if check_permissions(perms, READ_PERM | WRITE_PERM) == 0 {
                printf(
                    b"Insufficient permissions for addition\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return 0 as core::ffi::c_int;
            }
            a + b
        }
        #[no_mangle]
        pub unsafe extern "C" fn multiply_with_log(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            log_msg: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            *log_msg = create_result_string(
                b"multiply\0" as *const u8 as *const core::ffi::c_char,
                a * b,
            );
            if (*log_msg).is_null() {
                return 0 as core::ffi::c_int;
            }
            a * b
        }
        #[no_mangle]
        pub unsafe extern "C" fn copy_and_sum(
            src: *mut core::ffi::c_int,
            count: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if src.is_null() {
                printf(b"Source pointer is NULL\n\0" as *const u8 as *const core::ffi::c_char);
                return -(1 as core::ffi::c_int);
            }
            let dest: *mut core::ffi::c_int = malloc(
                (count as size_t)
                    .wrapping_mul(::core::mem::size_of::<core::ffi::c_int>() as size_t),
            ) as *mut core::ffi::c_int;
            if dest.is_null() {
                printf(b"Memory allocation failed\n\0" as *const u8 as *const core::ffi::c_char);
                return -(1 as core::ffi::c_int);
            }
            memcpy(
                dest as *mut core::ffi::c_void,
                src as *const core::ffi::c_void,
                (count as size_t)
                    .wrapping_mul(::core::mem::size_of::<core::ffi::c_int>() as size_t),
            );
            let mut sum: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < count {
                sum += *dest.offset(i as isize);
                i += 1;
            }
            free(dest as *mut core::ffi::c_void);
            sum
        }
        #[no_mangle]
        pub unsafe extern "C" fn compare_operations(
            op1: *const core::ffi::c_char,
            op2: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if op1.is_null() || op2.is_null() {
                printf(
                    b"One or both operation strings are NULL\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            strcmp(op1, op2)
        }
        #[no_mangle]
        pub unsafe extern "C" fn complexmode(
            mode: core::ffi::c_int,
            value1: core::ffi::c_int,
            value2: core::ffi::c_int,
            value3: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut log_message: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let permissions: core::ffi::c_int = 0o644 as core::ffi::c_int;
            let res_tracker: *mut Result_0 =
                malloc(::core::mem::size_of::<Result_0>() as size_t) as *mut Result_0;
            if res_tracker.is_null() {
                printf(
                    b"Failed to allocate result tracker\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            (*res_tracker).value = 0 as core::ffi::c_int;
            (*res_tracker).permissions = permissions;
            strcpy(
                ((*res_tracker).operation).as_mut_ptr(),
                b"none\0" as *const u8 as *const core::ffi::c_char,
            );
            match mode {
                1 => {
                    strcpy(
                        ((*res_tracker).operation).as_mut_ptr(),
                        b"addition\0" as *const u8 as *const core::ffi::c_char,
                    );
                    result = safe_add(value1, value2, permissions);
                    (*res_tracker).value = result;
                    printf(b"Mode 1: Addition\n\0" as *const u8 as *const core::ffi::c_char);
                    printf(
                        b"Result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        result,
                    );
                }
                2 => {
                    strcpy(
                        ((*res_tracker).operation).as_mut_ptr(),
                        b"multiplication\0" as *const u8 as *const core::ffi::c_char,
                    );
                    result = multiply_with_log(value1, value2, &mut log_message);
                    (*res_tracker).value = result;
                    if log_message.is_null()
                        || strcmp(log_message, b"\0" as *const u8 as *const core::ffi::c_char)
                            == 0 as core::ffi::c_int
                    {
                        printf(
                            b"Log message creation failed\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                    } else {
                        printf(
                            b"Mode 2: %s\n\0" as *const u8 as *const core::ffi::c_char,
                            log_message,
                        );
                        free(log_message as *mut core::ffi::c_void);
                    }
                }
                3 => {
                    strcpy(
                        ((*res_tracker).operation).as_mut_ptr(),
                        b"array_sum\0" as *const u8 as *const core::ffi::c_char,
                    );
                    let mut values: [core::ffi::c_int; 3] = [value1, value2, value3];
                    result = copy_and_sum(values.as_mut_ptr(), 3 as core::ffi::c_int);
                    (*res_tracker).value = result;
                    printf(b"Mode 3: Array Sum\n\0" as *const u8 as *const core::ffi::c_char);
                    printf(
                        b"Result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        result,
                    );
                }
                4 => {
                    strcpy(
                        ((*res_tracker).operation).as_mut_ptr(),
                        b"complex\0" as *const u8 as *const core::ffi::c_char,
                    );
                    if check_permissions(permissions, 0o100 as core::ffi::c_int) != 0 {
                        result = value1 * value2 + value3;
                    } else {
                        result = value1 + value2 + value3;
                    }
                    (*res_tracker).value = result;
                    printf(
                        b"Mode 4: Complex Calculation\n\0" as *const u8 as *const core::ffi::c_char,
                    );
                    printf(
                        b"Result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        result,
                    );
                }
                _ => {
                    printf(b"Invalid mode\n\0" as *const u8 as *const core::ffi::c_char);
                    result = -(1 as core::ffi::c_int);
                }
            }
            if strcmp(
                ((*res_tracker).operation).as_ptr(),
                b"none\0" as *const u8 as *const core::ffi::c_char,
            ) != 0 as core::ffi::c_int
            {
                printf(
                    b"Operation performed: %s\n\0" as *const u8 as *const core::ffi::c_char,
                    ((*res_tracker).operation).as_ptr(),
                );
            }
            free(res_tracker as *mut core::ffi::c_void);
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("complexmode_lib", SOURCE, &["dest", "res_tracker"], &[]);
}
