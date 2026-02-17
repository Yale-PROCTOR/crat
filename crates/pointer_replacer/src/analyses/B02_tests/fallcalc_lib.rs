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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct DataPoint {
            pub value: core::ffi::c_int,
            pub coefficient: core::ffi::c_double,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for DataPoint {}
        #[automatically_derived]
        impl ::core::clone::Clone for DataPoint {
            #[inline]
            fn clone(&self) -> DataPoint {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const OCTAL_MASK_1: core::ffi::c_int = 0o777 as core::ffi::c_int;
        pub const OCTAL_MASK_2: core::ffi::c_int = 0o100 as core::ffi::c_int;
        pub const OCTAL_FLAG: core::ffi::c_int = 0o200 as core::ffi::c_int;
        pub const OCTAL_BASE: core::ffi::c_int = 0o10 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn safe_double_to_int(d: core::ffi::c_double) -> core::ffi::c_int {
            if d.is_nan() as i32 != 0 {
                return 0 as core::ffi::c_int;
            }
            if if d.is_infinite() {
                if d.is_sign_positive() {
                    1
                } else {
                    -1
                }
            } else {
                0
            } != 0
            {
                return if d > 0 as core::ffi::c_int as core::ffi::c_double {
                    INT_MAX
                } else {
                    INT_MIN
                };
            }
            if d >= INT_MAX as core::ffi::c_double {
                return INT_MAX;
            }
            if d <= INT_MIN as core::ffi::c_double {
                return INT_MIN;
            }
            d as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_array_reverse(
            mut end: *mut core::ffi::c_int,
            count: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut sum: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < count {
                sum += *end;
                end = end.offset(-1);
                i += 1;
            }
            sum
        }
        #[no_mangle]
        pub unsafe extern "C" fn switch_fallthrough_calculator(
            mut value: core::ffi::c_int,
            operation: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut current_block_5: u64;
            match operation {
                0 => {
                    value *= OCTAL_BASE;
                    current_block_5 = 9562291966642929348;
                }
                1 => {
                    current_block_5 = 9562291966642929348;
                }
                2 => {
                    current_block_5 = 8400788723583891100;
                }
                3 => {
                    value *= 3 as core::ffi::c_int;
                    current_block_5 = 3137761655869617204;
                }
                4 => {
                    current_block_5 = 3137761655869617204;
                }
                _ => {
                    value = 0 as core::ffi::c_int;
                    current_block_5 = 14523784380283086299;
                }
            }
            match current_block_5 {
                9562291966642929348 => {
                    value += OCTAL_FLAG;
                    current_block_5 = 8400788723583891100;
                }
                3137761655869617204 => {
                    value += OCTAL_MASK_2;
                    current_block_5 = 14523784380283086299;
                }
                _ => {}
            }
            if current_block_5 == 8400788723583891100 {
                value &= OCTAL_MASK_1;
            }
            value
        }
        #[no_mangle]
        pub unsafe extern "C" fn allocate_and_compute(
            size: core::ffi::c_int,
            multiplier: core::ffi::c_double,
        ) -> core::ffi::c_int {
            let points: *mut DataPoint = malloc(
                (size as size_t).wrapping_mul(::core::mem::size_of::<DataPoint>() as size_t),
            ) as *mut DataPoint;
            if points.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < size {
                (*points.offset(i as isize)).value = i * OCTAL_BASE;
                (*points.offset(i as isize)).coefficient = i as core::ffi::c_double * multiplier;
                i += 1;
            }
            let mut sum: core::ffi::c_double = 0.0f64;
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < size {
                sum += (*points.offset(i_0 as isize)).value as core::ffi::c_double
                    * (*points.offset(i_0 as isize)).coefficient;
                i_0 += 1;
            }
            let result: core::ffi::c_int = safe_double_to_int(sum);
            free(points as *mut core::ffi::c_void);
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn foreach_sum(
            array: *mut core::ffi::c_int,
            count: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut total: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut element: core::ffi::c_int = 0;
            let mut keep: core::ffi::c_int = 1 as core::ffi::c_int;
            let mut idx: core::ffi::c_int = 0 as core::ffi::c_int;
            while keep != 0 && idx < count {
                element = *array.offset(idx as isize);
                while keep != 0 {
                    total += element;
                    keep = (keep == 0) as core::ffi::c_int;
                }
                keep = (keep == 0) as core::ffi::c_int;
                idx += 1;
            }
            total
        }
        #[no_mangle]
        pub unsafe extern "C" fn fallcalc(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let base_value: core::ffi::c_int = param1 * OCTAL_MASK_2 + param2;
            let array_size: core::ffi::c_int = 5 as core::ffi::c_int;
            let data_array: *mut core::ffi::c_int = malloc(
                (array_size as size_t)
                    .wrapping_mul(::core::mem::size_of::<core::ffi::c_int>() as size_t),
            ) as *mut core::ffi::c_int;
            if data_array.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < array_size {
                *data_array.offset(i as isize) = (i + 1 as core::ffi::c_int) * OCTAL_BASE + param1;
                i += 1;
            }
            let foreach_result: core::ffi::c_int = foreach_sum(data_array, array_size);
            let last_element: *mut core::ffi::c_int = data_array
                .offset(array_size as isize)
                .offset(-(1 as core::ffi::c_int as isize));
            let reverse_sum: core::ffi::c_int = process_array_reverse(last_element, array_size);
            let switch_result: core::ffi::c_int =
                switch_fallthrough_calculator(param2, param3 % 5 as core::ffi::c_int);
            let floating_calc: core::ffi::c_double = param1 as core::ffi::c_double * 3.7f64
                + param2 as core::ffi::c_double * 2.3f64
                - param3 as core::ffi::c_double * 0.5f64;
            let converted: core::ffi::c_int = safe_double_to_int(floating_calc);
            let alloc_result: core::ffi::c_int = allocate_and_compute(
                param4 % 10 as core::ffi::c_int + 1 as core::ffi::c_int,
                1.5f64,
            );
            result = base_value
                + foreach_result
                + reverse_sum
                + switch_result
                + converted
                + alloc_result;
            if param3 > OCTAL_FLAG {
                result |= OCTAL_FLAG;
            }
            free(data_array as *mut core::ffi::c_void);
            result &= OCTAL_MASK_1;
            result
        }
        pub const INT_MAX: core::ffi::c_int = __INT_MAX__;
        pub const INT_MIN: core::ffi::c_int = -__INT_MAX__ - 1 as core::ffi::c_int;
        pub const __INT_MAX__: core::ffi::c_int = 2147483647 as core::ffi::c_int;
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("fallcalc_lib", SOURCE);
}
