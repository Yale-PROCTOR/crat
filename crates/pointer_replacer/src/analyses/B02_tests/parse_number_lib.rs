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
            fn strtod(
                __nptr: *const core::ffi::c_char,
                __endptr: *mut *mut core::ffi::c_char,
            ) -> core::ffi::c_double;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
        }
        pub type size_t = usize;
        pub type cJSON_bool = core::ffi::c_int;
        #[repr(C)]
        pub struct parse_buffer {
            pub content: *const core::ffi::c_uchar,
            pub length: size_t,
            pub offset: size_t,
            pub depth: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for parse_buffer {}
        #[automatically_derived]
        impl ::core::clone::Clone for parse_buffer {
            #[inline]
            fn clone(&self) -> parse_buffer {
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_uchar>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct cJSON {
            pub type_0: core::ffi::c_int,
            pub valueint: core::ffi::c_int,
            pub valuedouble: core::ffi::c_double,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for cJSON {}
        #[automatically_derived]
        impl ::core::clone::Clone for cJSON {
            #[inline]
            fn clone(&self) -> cJSON {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const true_0: cJSON_bool = 1 as core::ffi::c_int;
        pub const false_0: cJSON_bool = 0 as core::ffi::c_int;
        pub const INT_MIN: core::ffi::c_int = -__INT_MAX__ - 1 as core::ffi::c_int;
        pub const INT_MAX: core::ffi::c_int = __INT_MAX__;
        pub const cJSON_Number: core::ffi::c_int = (1 as core::ffi::c_int) << 3 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn parse_number(
            item: *mut cJSON,
            input_buffer: *mut parse_buffer,
        ) -> cJSON_bool {
            let mut number: core::ffi::c_double = 0 as core::ffi::c_int as core::ffi::c_double;
            let mut after_end: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut number_c_string: *mut core::ffi::c_uchar =
                std::ptr::null_mut::<core::ffi::c_uchar>();
            let decimal_point: core::ffi::c_uchar = '.' as i32 as core::ffi::c_uchar;
            let mut i: size_t = 0 as size_t;
            let mut number_string_length: size_t = 0 as size_t;
            let mut has_decimal_point: cJSON_bool = false_0;
            if input_buffer.is_null() || ((*input_buffer).content).is_null() {
                return false_0;
            }
            i = 0 as size_t;
            while !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(i) < (*input_buffer).length
            {
                match *((*input_buffer).content).add((*input_buffer).offset).add(i)
                    as core::ffi::c_int
                {
                    48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 43 | 45 | 101 | 69 => {
                        number_string_length = number_string_length.wrapping_add(1);
                    }
                    46 => {
                        number_string_length = number_string_length.wrapping_add(1);
                        has_decimal_point = true_0;
                    }
                    _ => {
                        break;
                    }
                }
                i = i.wrapping_add(1);
            }
            number_c_string =
                malloc(number_string_length.wrapping_add(1 as size_t)) as *mut core::ffi::c_uchar;
            if number_c_string.is_null() {
                return false_0;
            }
            memcpy(
                number_c_string as *mut core::ffi::c_void,
                ((*input_buffer).content).add((*input_buffer).offset) as *const core::ffi::c_void,
                number_string_length,
            );
            *number_c_string.add(number_string_length) = '\0' as i32 as core::ffi::c_uchar;
            if has_decimal_point != 0 {
                i = 0 as size_t;
                while i < number_string_length {
                    if *number_c_string.add(i) as core::ffi::c_int == '.' as i32 {
                        *number_c_string.add(i) = decimal_point;
                    }
                    i = i.wrapping_add(1);
                }
            }
            number = strtod(
                number_c_string as *const core::ffi::c_char,
                &mut after_end as *mut *mut core::ffi::c_uchar as *mut *mut core::ffi::c_char,
            );
            if number_c_string == after_end {
                free(number_c_string as *mut core::ffi::c_void);
                return false_0;
            }
            (*item).valuedouble = number;
            if number >= INT_MAX as core::ffi::c_double {
                (*item).valueint = INT_MAX;
            } else if number <= INT_MIN as core::ffi::c_double {
                (*item).valueint = INT_MIN;
            } else {
                (*item).valueint = number as core::ffi::c_int;
            }
            (*item).type_0 = cJSON_Number;
            (*input_buffer).offset =
                ((*input_buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(after_end.offset_from(number_c_string) as core::ffi::c_long
                        as size_t as core::ffi::c_ulong) as size_t as size_t;
            free(number_c_string as *mut core::ffi::c_void);
            true_0
        }
        pub const __INT_MAX__: core::ffi::c_int = 2147483647 as core::ffi::c_int;
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("parse_number_lib", SOURCE);
}
