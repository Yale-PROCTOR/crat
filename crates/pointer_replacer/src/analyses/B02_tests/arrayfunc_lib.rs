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
        pub type operation_func = Option<
            unsafe extern "C" fn(
                core::ffi::c_int,
                core::ffi::c_int,
                core::ffi::c_int,
                core::ffi::c_int,
            ) -> core::ffi::c_int,
        >;
        #[repr(C)]
        pub struct Result_0 {
            pub value: core::ffi::c_int,
            pub scaled: core::ffi::c_double,
            pub rank: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Result_0 {}
        #[automatically_derived]
        impl ::core::clone::Clone for Result_0 {
            #[inline]
            fn clone(&self) -> Result_0 {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct ResultArray {
            pub data: [Result_0; 10],
            pub count: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ResultArray {}
        #[automatically_derived]
        impl ::core::clone::Clone for ResultArray {
            #[inline]
            fn clone(&self) -> ResultArray {
                let _: ::core::clone::AssertParamIsClone<[Result_0; 10]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const INT32_MIN: core::ffi::c_int =
            -(2147483647 as core::ffi::c_int) - 1 as core::ffi::c_int;
        pub const INT32_MAX: core::ffi::c_int = 2147483647 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn add_operation(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a + b
        }
        #[no_mangle]
        pub unsafe extern "C" fn multiply_operation(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a * b
        }
        #[no_mangle]
        pub unsafe extern "C" fn subtract_operation(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a - b
        }
        #[no_mangle]
        pub unsafe extern "C" fn modulo_operation(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            unused1: core::ffi::c_int,
            unused2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if b == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            a % b
        }
        #[no_mangle]
        pub unsafe extern "C" fn safe_double_to_int(d: core::ffi::c_double) -> core::ffi::c_int {
            if d >= INT32_MAX as core::ffi::c_double {
                return INT32_MAX;
            }
            if d <= INT32_MIN as core::ffi::c_double {
                return INT32_MIN;
            }
            if d != d {
                return 0 as core::ffi::c_int;
            }
            d as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn compute_scaled_value(
            base: core::ffi::c_int,
            scale_factor: core::ffi::c_double,
        ) -> core::ffi::c_int {
            let scaled: core::ffi::c_double = base as core::ffi::c_double * scale_factor;
            safe_double_to_int(scaled)
        }
        #[no_mangle]
        pub unsafe extern "C" fn compare_results_in_array(
            arr: *mut ResultArray,
            idx1: core::ffi::c_int,
            idx2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if idx1 >= (*arr).count || idx2 >= (*arr).count {
                return 0 as core::ffi::c_int;
            }
            let ptr1: *mut Result_0 =
                &mut *((*arr).data).as_mut_ptr().offset(idx1 as isize) as *mut Result_0;
            let ptr2: *mut Result_0 =
                &mut *((*arr).data).as_mut_ptr().offset(idx2 as isize) as *mut Result_0;
            if ptr1 < ptr2 {
                return -(1 as core::ffi::c_int);
            } else if ptr1 > ptr2 {
                return 1 as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn init_result_array(
            arr: *mut ResultArray,
            values: *mut core::ffi::c_int,
            count: core::ffi::c_int,
        ) {
            (*arr).count = if count < 10 as core::ffi::c_int {
                count
            } else {
                10 as core::ffi::c_int
            };
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*arr).count {
                (*arr).data[i as usize] = {
                    Result_0 {
                        value: *values.offset(i as isize),
                        scaled: *values.offset(i as isize) as core::ffi::c_double * 1.5f64,
                        rank: i,
                    }
                };
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_with_foreach(
            arr: *mut ResultArray,
            op: operation_func,
        ) -> core::ffi::c_int {
            let mut total: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut item: *mut Result_0 = std::ptr::null_mut::<Result_0>();
            let mut keep: core::ffi::c_int = 1 as core::ffi::c_int;
            let mut count_iter: core::ffi::c_int = 0 as core::ffi::c_int;
            let size: core::ffi::c_int = (*arr).count;
            while keep != 0 && count_iter != size {
                item = ((*arr).data).as_mut_ptr().offset(count_iter as isize);
                while keep != 0 {
                    let result: core::ffi::c_int = op.expect("non-null function pointer")(
                        (*item).value,
                        (*item).rank,
                        0 as core::ffi::c_int,
                        0 as core::ffi::c_int,
                    );
                    total += result;
                    let temp: core::ffi::c_double = result as core::ffi::c_double * 0.75f64;
                    (*item).scaled = temp;
                    (*item).value = safe_double_to_int(temp);
                    keep = (keep == 0) as core::ffi::c_int;
                }
                keep = (keep == 0) as core::ffi::c_int;
                count_iter += 1;
            }
            total
        }
        #[no_mangle]
        pub unsafe extern "C" fn compute_weighted_sum(arr: *mut ResultArray) -> core::ffi::c_int {
            let mut sum: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*arr).count {
                let current: *mut Result_0 =
                    &mut *((*arr).data).as_mut_ptr().offset(i as isize) as *mut Result_0;
                let base: *mut Result_0 = &mut *((*arr).data)
                    .as_mut_ptr()
                    .offset(0 as core::ffi::c_int as isize)
                    as *mut Result_0;
                let weight: core::ffi::c_int = if current > base {
                    current.offset_from(base) as core::ffi::c_long as core::ffi::c_int
                } else {
                    1 as core::ffi::c_int
                };
                let weighted: core::ffi::c_double = (*current).value as core::ffi::c_double
                    * weight as core::ffi::c_double
                    * 0.8f64;
                sum += safe_double_to_int(weighted);
                i += 1;
            }
            sum
        }
        #[no_mangle]
        pub unsafe extern "C" fn arrayfunc(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let operations: [operation_func; 4] = [
                Some(
                    add_operation
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                Some(
                    multiply_operation
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                Some(
                    subtract_operation
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
                Some(
                    modulo_operation
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ),
            ];
            let mut values: [core::ffi::c_int; 8] = [
                param1,
                param2,
                param3,
                param4,
                param1 + param2,
                param2 - param3,
                param3 * 2 as core::ffi::c_int,
                param4 / 2 as core::ffi::c_int + 1 as core::ffi::c_int,
            ];
            let mut arr: ResultArray = {
                ResultArray {
                    data: [Result_0 {
                        value: 0,
                        scaled: 0.,
                        rank: 0,
                    }; 10],
                    count: 0 as core::ffi::c_int,
                }
            };
            init_result_array(&mut arr, values.as_mut_ptr(), 8 as core::ffi::c_int);
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < 4 as core::ffi::c_int {
                result += process_with_foreach(&mut arr, operations[i as usize]);
                i += 1;
            }
            result += compute_weighted_sum(&mut arr);
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < arr.count - 1 as core::ffi::c_int {
                let cmp: core::ffi::c_int =
                    compare_results_in_array(&mut arr, i_0, i_0 + 1 as core::ffi::c_int);
                result += cmp;
                i_0 += 1;
            }
            let final_scale: core::ffi::c_double = result as core::ffi::c_double * 0.333f64;
            result = safe_double_to_int(final_scale);
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("arrayfunc_lib", SOURCE, &[], &[]);
}
