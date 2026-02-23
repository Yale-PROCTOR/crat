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
            fn sprintf(
                __s: *mut core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn memchr(
                __s: *const core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        pub type operation_func =
            Option<unsafe extern "C" fn(core::ffi::c_int, core::ffi::c_int) -> core::ffi::c_int>;
        static mut accumulator: core::ffi::c_int = 0 as core::ffi::c_int;
        static mut multiplier: core::ffi::c_int = 1 as core::ffi::c_int;
        static mut operation_count: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn add_to_accumulator(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            accumulator += a + b;
            operation_count += 1;
            accumulator
        }
        #[no_mangle]
        pub unsafe extern "C" fn multiply_with_multiplier(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            multiplier *= a * b;
            operation_count += 1;
            multiplier
        }
        #[no_mangle]
        pub unsafe extern "C" fn subtract_from_accumulator(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            accumulator -= a - b;
            operation_count += 1;
            accumulator
        }
        #[no_mangle]
        pub unsafe extern "C" fn divide_multiplier(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if b != 0 as core::ffi::c_int {
                multiplier /= b;
            }
            operation_count += 1;
            multiplier
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_octal_string(
            dest: *mut core::ffi::c_char,
            octal_val: core::ffi::c_int,
        ) {
            let mut buffer: [core::ffi::c_char; 50] = [0; 50];
            sprintf(
                buffer.as_mut_ptr(),
                b"Octal: 0%o, Decimal: %d\0" as *const u8 as *const core::ffi::c_char,
                octal_val,
                octal_val,
            );
            strcpy(dest, buffer.as_ptr());
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_and_replace_char(
            str: *mut core::ffi::c_char,
            search_char: core::ffi::c_int,
        ) {
            let found: *mut core::ffi::c_char =
                memchr(str as *const core::ffi::c_void, search_char, strlen(str))
                    as *mut core::ffi::c_char;
            if !found.is_null() {
                *found = 'X' as i32 as core::ffi::c_char;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn validate_and_normalize(
            value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let is_nonzero: core::ffi::c_int = (value != 0) as core::ffi::c_int;
            let is_zero: core::ffi::c_int = (value == 0) as core::ffi::c_int;
            let lower_threshold: core::ffi::c_int = 0o100 as core::ffi::c_int;
            let upper_threshold: core::ffi::c_int = 0o777 as core::ffi::c_int;
            if is_nonzero != 0 && value > 0 as core::ffi::c_int {
                if value < lower_threshold {
                    return lower_threshold;
                } else if value > upper_threshold {
                    return upper_threshold;
                }
            }
            value
        }
        static mut operations: [operation_func; 4] = unsafe {
            [
                Some(
                    add_to_accumulator
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                Some(
                    multiply_with_multiplier
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                Some(
                    subtract_from_accumulator
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                Some(
                    divide_multiplier
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
            ]
        };
        #[no_mangle]
        pub unsafe extern "C" fn findrep(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let p1_valid: core::ffi::c_int = (param1 != 0) as core::ffi::c_int;
            let p2_valid: core::ffi::c_int = (param2 != 0) as core::ffi::c_int;
            let p3_valid: core::ffi::c_int = (param3 != 0) as core::ffi::c_int;
            let p4_valid: core::ffi::c_int = (param4 != 0) as core::ffi::c_int;
            let active_params: core::ffi::c_int = p1_valid + p2_valid + p3_valid + p4_valid;
            let mode_add: core::ffi::c_int = 0o1 as core::ffi::c_int;
            let mode_multiply: core::ffi::c_int = 0o2 as core::ffi::c_int;
            let mode_subtract: core::ffi::c_int = 0o3 as core::ffi::c_int;
            let mode_divide: core::ffi::c_int = 0o4 as core::ffi::c_int;
            let normalized_p1: core::ffi::c_int = validate_and_normalize(param1);
            let normalized_p2: core::ffi::c_int = validate_and_normalize(param2);
            let normalized_p3: core::ffi::c_int = validate_and_normalize(param3);
            let normalized_p4: core::ffi::c_int = validate_and_normalize(param4);
            let mut message: [core::ffi::c_char; 100] = [0; 100];
            let mut search_buffer: [core::ffi::c_char; 100] = [0; 100];
            process_octal_string(message.as_mut_ptr(), 0o123 as core::ffi::c_int);
            strcpy(
                search_buffer.as_mut_ptr(),
                b"Function pointer example with static vars\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let found_char: *mut core::ffi::c_char = memchr(
                search_buffer.as_mut_ptr() as *const core::ffi::c_void,
                'p' as i32,
                strlen(search_buffer.as_ptr()),
            ) as *mut core::ffi::c_char;
            if !found_char.is_null() {
                result += found_char.offset_from(search_buffer.as_ptr()) as core::ffi::c_long
                    as core::ffi::c_int;
            }
            let mut selected_op: operation_func = None;
            if active_params >= mode_add {
                selected_op = operations[0 as core::ffi::c_int as usize];
                result +=
                    selected_op.expect("non-null function pointer")(normalized_p1, normalized_p2);
            }
            if active_params >= mode_multiply {
                selected_op = operations[1 as core::ffi::c_int as usize];
                result +=
                    selected_op.expect("non-null function pointer")(normalized_p3, normalized_p4);
            }
            if accumulator > 0o150 as core::ffi::c_int {
                selected_op = operations[2 as core::ffi::c_int as usize];
                let subtract_result: core::ffi::c_int =
                    selected_op.expect("non-null function pointer")(normalized_p1, normalized_p3);
                result += subtract_result;
            }
            find_and_replace_char(message.as_mut_ptr(), 'O' as i32);
            let mut final_message: [core::ffi::c_char; 100] = [0; 100];
            strcpy(final_message.as_mut_ptr(), message.as_ptr());
            let has_accumulator: core::ffi::c_int = (accumulator != 0) as core::ffi::c_int;
            let has_multiplier: core::ffi::c_int = (multiplier != 0) as core::ffi::c_int;
            let both_active: core::ffi::c_int =
                (has_accumulator != 0 && has_multiplier != 0) as core::ffi::c_int;
            if both_active != 0 {
                result += accumulator + multiplier;
            }
            if multiplier > 0o100 as core::ffi::c_int {
                selected_op = operations[3 as core::ffi::c_int as usize];
                selected_op.expect("non-null function pointer")(multiplier, 2 as core::ffi::c_int);
            }
            result += operation_count * 0o10 as core::ffi::c_int;
            let result_exists: core::ffi::c_int = (result != 0) as core::ffi::c_int;
            if result_exists == 0 {
                result = 0o777 as core::ffi::c_int;
            }
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("findrep_lib", SOURCE, &[], &[]);
}
