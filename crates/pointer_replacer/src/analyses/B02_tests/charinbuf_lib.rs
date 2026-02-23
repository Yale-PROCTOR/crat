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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
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
            Option<unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int>;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        static mut counter: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn increment_counter(value: core::ffi::c_int) -> core::ffi::c_int {
            counter += value;
            counter
        }
        pub const UINT16_MAX: core::ffi::c_int = 65535 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn decrement_counter(value: core::ffi::c_int) -> core::ffi::c_int {
            counter -= value;
            counter
        }
        #[no_mangle]
        pub unsafe extern "C" fn multiply_counter(value: core::ffi::c_int) -> core::ffi::c_int {
            counter *= value;
            counter
        }
        #[no_mangle]
        pub unsafe extern "C" fn reset_counter(value: core::ffi::c_int) -> core::ffi::c_int {
            counter = value;
            counter
        }
        #[no_mangle]
        pub unsafe extern "C" fn is_string_empty(
            str: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if str.is_null() {
                return 1 as core::ffi::c_int;
            }
            if *str != 0 {
                return 0 as core::ffi::c_int;
            }
            1 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_char_in_buffer(
            buffer: *const core::ffi::c_char,
            size: size_t,
            target: core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            if buffer.is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            memchr(
                buffer as *const core::ffi::c_void,
                target as core::ffi::c_int,
                size,
            ) as *mut core::ffi::c_char
        }
        #[no_mangle]
        pub unsafe extern "C" fn create_buffer(
            initial: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            if initial.is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            let len: size_t = strlen(initial);
            let buffer: *mut core::ffi::c_char =
                malloc(len.wrapping_add(1 as size_t)) as *mut core::ffi::c_char;
            if !buffer.is_null() {
                strcpy(buffer, initial);
            }
            buffer
        }
        #[no_mangle]
        pub unsafe extern "C" fn validate_uint16_range(
            value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if value < 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            if value > UINT16_MAX {
                return 0 as core::ffi::c_int;
            }
            1 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn apply_operation(
            op: operation_func,
            value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if op.is_none() {
                return -(1 as core::ffi::c_int);
            }
            op.expect("non-null function pointer")(value)
        }
        #[no_mangle]
        pub unsafe extern "C" fn charinbuf(
            mode: core::ffi::c_int,
            value: core::ffi::c_int,
            opt1: core::ffi::c_int,
            opt2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut buffer: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut found_pos: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let test_string: *const core::ffi::c_char =
                b"\0" as *const u8 as *const core::ffi::c_char;
            let non_empty_string: *const core::ffi::c_char =
                b"Hello, World!\0" as *const u8 as *const core::ffi::c_char;
            let mut current_op: operation_func = None;
            counter = 0 as core::ffi::c_int;
            match mode {
                0 => {
                    printf(
                        b"Mode 0: UINT16_MAX validation\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    printf(
                        b"Checking if value %d is within uint16_t range...\n\0" as *const u8
                            as *const core::ffi::c_char,
                        value,
                    );
                    if validate_uint16_range(value) != 0 {
                        printf(
                            b"Value %d is valid (0 <= value <= %u)\n\0" as *const u8
                                as *const core::ffi::c_char,
                            value,
                            UINT16_MAX,
                        );
                        result = value;
                    } else {
                        printf(
                            b"Value %d is out of range for uint16_t\n\0" as *const u8
                                as *const core::ffi::c_char,
                            value,
                        );
                        result = -(1 as core::ffi::c_int);
                    }
                    printf(
                        b"UINT16_MAX constant value: %u\n\0" as *const u8
                            as *const core::ffi::c_char,
                        UINT16_MAX,
                    );
                }
                1 => {
                    printf(
                        b"Mode 1: String empty check by dereference\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    if is_string_empty(test_string) != 0 {
                        printf(
                            b"Test string is empty (checked with *string)\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result = 0 as core::ffi::c_int;
                    } else {
                        printf(
                            b"Test string is not empty\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result = 1 as core::ffi::c_int;
                    }
                    if is_string_empty(non_empty_string) != 0 {
                        printf(
                            b"Non-empty string check failed!\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                    } else {
                        printf(
                            b"Non-empty string correctly identified\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result += 10 as core::ffi::c_int;
                    }
                }
                2 => {
                    printf(
                        b"Mode 2: Dynamic memory allocation and free\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    buffer = create_buffer(
                        b"Testing malloc and free\0" as *const u8 as *const core::ffi::c_char,
                    );
                    if !buffer.is_null() {
                        printf(
                            b"Buffer allocated: '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                            buffer,
                        );
                        printf(
                            b"Buffer length: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                            strlen(buffer),
                        );
                        result = strlen(buffer) as core::ffi::c_int;
                        free(buffer as *mut core::ffi::c_void);
                        printf(
                            b"Buffer freed successfully\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        buffer = std::ptr::null_mut::<core::ffi::c_char>();
                    } else {
                        printf(
                            b"Failed to allocate buffer\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result = -(1 as core::ffi::c_int);
                    }
                }
                3 => {
                    printf(
                        b"Mode 3: Function pointers with static counter\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    current_op = Some(
                        reset_counter as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int,
                    ) as operation_func;
                    result = apply_operation(current_op, value);
                    printf(
                        b"Counter reset to: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        result,
                    );
                    current_op = Some(
                        increment_counter
                            as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int,
                    ) as operation_func;
                    result = apply_operation(current_op, opt1);
                    printf(
                        b"Counter after increment by %d: %d\n\0" as *const u8
                            as *const core::ffi::c_char,
                        opt1,
                        result,
                    );
                    current_op = Some(
                        multiply_counter
                            as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int,
                    ) as operation_func;
                    result = apply_operation(current_op, opt2);
                    printf(
                        b"Counter after multiply by %d: %d\n\0" as *const u8
                            as *const core::ffi::c_char,
                        opt2,
                        result,
                    );
                    current_op = Some(
                        decrement_counter
                            as unsafe extern "C" fn(core::ffi::c_int) -> core::ffi::c_int,
                    ) as operation_func;
                    result = apply_operation(current_op, 5 as core::ffi::c_int);
                    printf(
                        b"Counter after decrement by 5: %d\n\0" as *const u8
                            as *const core::ffi::c_char,
                        result,
                    );
                    printf(
                        b"Final static counter value: %d\n\0" as *const u8
                            as *const core::ffi::c_char,
                        counter,
                    );
                }
                4 => {
                    printf(
                        b"Mode 4: Using memchr to find character\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    buffer = create_buffer(
                        b"Search for character X in this buffer\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    if !buffer.is_null() {
                        let buf_size: size_t = strlen(buffer);
                        let search_char: core::ffi::c_char = 'X' as i32 as core::ffi::c_char;
                        printf(
                            b"Searching for '%c' in: '%s'\n\0" as *const u8
                                as *const core::ffi::c_char,
                            search_char as core::ffi::c_int,
                            buffer,
                        );
                        found_pos = find_char_in_buffer(buffer, buf_size, search_char);
                        if !found_pos.is_null() {
                            result = found_pos.offset_from(buffer) as core::ffi::c_long
                                as core::ffi::c_int;
                            printf(
                                b"Found '%c' at position: %d\n\0" as *const u8
                                    as *const core::ffi::c_char,
                                search_char as core::ffi::c_int,
                                result,
                            );
                        } else {
                            printf(
                                b"Character '%c' not found\n\0" as *const u8
                                    as *const core::ffi::c_char,
                                search_char as core::ffi::c_int,
                            );
                            result = -(1 as core::ffi::c_int);
                        }
                        free(buffer as *mut core::ffi::c_void);
                        buffer = std::ptr::null_mut::<core::ffi::c_char>();
                    }
                }
                _ => {
                    printf(
                        b"Invalid mode: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        mode,
                    );
                    result = -(1 as core::ffi::c_int);
                }
            }
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("charinbuf_lib", SOURCE, &["create_buffer#buffer"], &[]);
}
