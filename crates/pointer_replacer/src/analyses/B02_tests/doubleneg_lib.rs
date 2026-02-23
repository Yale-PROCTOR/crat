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
            fn memchr(
                __s: *const core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn pow(__x: core::ffi::c_double, __y: core::ffi::c_double) -> core::ffi::c_double;
        }
        pub type size_t = usize;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn convert_double_to_int(
            value: core::ffi::c_double,
        ) -> core::ffi::c_int {
            value as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_value_in_buffer(
            buffer: *const core::ffi::c_char,
            size: size_t,
            search_val: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let target: core::ffi::c_char = search_val as core::ffi::c_char;
            let result: *mut core::ffi::c_void = memchr(
                buffer as *const core::ffi::c_void,
                target as core::ffi::c_int,
                size,
            );
            if !result.is_null() {
                return (result as *mut core::ffi::c_char).offset_from(buffer) as core::ffi::c_long
                    as core::ffi::c_int;
            }
            -(1 as core::ffi::c_int)
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_negation(var1: core::ffi::c_int) -> core::ffi::c_int {
            let mut var2: core::ffi::c_int = 0;
            var2 = (var1 != 0) as core::ffi::c_int;
            var2
        }
        #[no_mangle]
        pub unsafe extern "C" fn create_numeric_buffer(
            buffer: *mut core::ffi::c_char,
            size: core::ffi::c_int,
            seed: core::ffi::c_int,
        ) {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < size {
                *buffer.offset(i as isize) = ((seed + i * 7 as core::ffi::c_int)
                    % 256 as core::ffi::c_int)
                    as core::ffi::c_char;
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn calculate_with_doubles(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            c: core::ffi::c_int,
        ) -> core::ffi::c_double {
            let mut result: core::ffi::c_double = 0.0f64;
            if b != 0 as core::ffi::c_int {
                result = a as core::ffi::c_double / b as core::ffi::c_double;
            }
            result *= pow(10.0f64, (c % 10 as core::ffi::c_int) as core::ffi::c_double);
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn doubleneg(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            let mut i: core::ffi::c_int = 0;
            printf(
                b"=== Starting foo() execution ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(
                b"Parameters: %d, %d, %d, %d\n\0" as *const u8 as *const core::ffi::c_char,
                param1,
                param2,
                param3,
                param4,
            );
            printf(b"\n--- Integer Negation Test ---\n\0" as *const u8 as *const core::ffi::c_char);
            let negation_test: core::ffi::c_int = param1;
            let negation_result: core::ffi::c_int = (negation_test != 0) as core::ffi::c_int;
            printf(
                b"Original value: %d\n\0" as *const u8 as *const core::ffi::c_char,
                negation_test,
            );
            printf(
                b"After !!negation: %d\n\0" as *const u8 as *const core::ffi::c_char,
                negation_result,
            );
            result += negation_result * 10 as core::ffi::c_int;
            let neg_p2: core::ffi::c_int = (param2 != 0) as core::ffi::c_int;
            let neg_p3: core::ffi::c_int = (param3 != 0) as core::ffi::c_int;
            let neg_p4: core::ffi::c_int = (param4 != 0) as core::ffi::c_int;
            printf(
                b"Double negation results: %d, %d, %d\n\0" as *const u8 as *const core::ffi::c_char,
                neg_p2,
                neg_p3,
                neg_p4,
            );
            result += neg_p2 + neg_p3 + neg_p4;
            printf(
                b"\n--- Double to Int Conversion Test ---\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let large_double: core::ffi::c_double = calculate_with_doubles(param1, param2, param3);
            printf(
                b"Calculated double value: %e\n\0" as *const u8 as *const core::ffi::c_char,
                large_double,
            );
            let converted_int: core::ffi::c_int = convert_double_to_int(large_double);
            printf(
                b"Converted to int (may be UB): %d\n\0" as *const u8 as *const core::ffi::c_char,
                converted_int,
            );
            let negative_large: core::ffi::c_double =
                -pow(2.0f64, 40 as core::ffi::c_int as core::ffi::c_double);
            printf(
                b"Very large negative double: %e\n\0" as *const u8 as *const core::ffi::c_char,
                negative_large,
            );
            let converted_neg: core::ffi::c_int = convert_double_to_int(negative_large);
            printf(
                b"Converted to int (UB likely): %d\n\0" as *const u8 as *const core::ffi::c_char,
                converted_neg,
            );
            result +=
                converted_int % 1000 as core::ffi::c_int + converted_neg % 1000 as core::ffi::c_int;
            printf(b"\n--- Memchr Search Test ---\n\0" as *const u8 as *const core::ffi::c_char);
            create_numeric_buffer(buffer.as_mut_ptr(), 256 as core::ffi::c_int, param1);
            let search_values: [core::ffi::c_int; 4] = [
                param2 % 256 as core::ffi::c_int,
                param3 % 256 as core::ffi::c_int,
                param4 % 256 as core::ffi::c_int,
                42 as core::ffi::c_int,
            ];
            let num_searches: core::ffi::c_int = ::core::mem::size_of::<[core::ffi::c_int; 4]>()
                .wrapping_div(::core::mem::size_of::<core::ffi::c_int>())
                as core::ffi::c_int;
            printf(b"Searching buffer for values...\n\0" as *const u8 as *const core::ffi::c_char);
            i = 0 as core::ffi::c_int;
            while i < num_searches {
                let pos: core::ffi::c_int =
                    find_value_in_buffer(buffer.as_ptr(), 256 as size_t, search_values[i as usize]);
                if pos >= 0 as core::ffi::c_int {
                    printf(
                        b"Found value %d at position %d\n\0" as *const u8
                            as *const core::ffi::c_char,
                        search_values[i as usize],
                        pos,
                    );
                    result += pos;
                } else {
                    printf(
                        b"Value %d not found\n\0" as *const u8 as *const core::ffi::c_char,
                        search_values[i as usize],
                    );
                }
                i += 1;
            }
            let direct_search: *mut core::ffi::c_char = memchr(
                buffer.as_mut_ptr() as *const core::ffi::c_void,
                100 as core::ffi::c_int,
                256 as size_t,
            ) as *mut core::ffi::c_char;
            if !direct_search.is_null() {
                printf(
                    b"Direct memchr found byte 100 at offset: %ld\n\0" as *const u8
                        as *const core::ffi::c_char,
                    direct_search.offset_from(buffer.as_ptr()) as core::ffi::c_long,
                );
                result += direct_search.offset_from(buffer.as_ptr()) as core::ffi::c_long
                    as core::ffi::c_int;
            }
            printf(b"\n--- Combined Feature Test ---\n\0" as *const u8 as *const core::ffi::c_char);
            i = 0 as core::ffi::c_int;
            while i < 10 as core::ffi::c_int {
                let search_byte: core::ffi::c_int = (param1 + i * param2) % 256 as core::ffi::c_int;
                let found: *mut core::ffi::c_void = memchr(
                    buffer.as_mut_ptr() as *const core::ffi::c_void,
                    search_byte,
                    256 as size_t,
                );
                let found_flag: core::ffi::c_int = !found.is_null() as core::ffi::c_int;
                printf(
                    b"Search %d: byte=%d, found=%d\n\0" as *const u8 as *const core::ffi::c_char,
                    i,
                    search_byte,
                    found_flag,
                );
                result += found_flag;
                i += 1;
            }
            let infinity_val: core::ffi::c_double = ::core::f32::INFINITY as core::ffi::c_double;
            let nan_val: core::ffi::c_double = ::core::f32::NAN as core::ffi::c_double;
            printf(b"\n--- Special Double Values ---\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"Converting INFINITY to int: \0" as *const u8 as *const core::ffi::c_char);
            let inf_as_int: core::ffi::c_int = convert_double_to_int(infinity_val);
            printf(
                b"%d (undefined behavior)\n\0" as *const u8 as *const core::ffi::c_char,
                inf_as_int,
            );
            printf(b"Converting NAN to int: \0" as *const u8 as *const core::ffi::c_char);
            let nan_as_int: core::ffi::c_int = convert_double_to_int(nan_val);
            printf(
                b"%d (undefined behavior)\n\0" as *const u8 as *const core::ffi::c_char,
                nan_as_int,
            );
            printf(b"\n=== Final Result ===\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"Accumulated result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                result,
            );
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("doubleneg_lib", SOURCE, &[], &[]);
}
