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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn memmove(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct DataBlock {
            pub values: [core::ffi::c_int; 4],
            pub count: core::ffi::c_int,
            pub label: *mut core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for DataBlock {}
        #[automatically_derived]
        impl ::core::clone::Clone for DataBlock {
            #[inline]
            fn clone(&self) -> DataBlock {
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_int; 4]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn shift_array(
            arr: *mut core::ffi::c_int,
            size: core::ffi::c_int,
            positions: core::ffi::c_int,
        ) {
            if positions > 0 as core::ffi::c_int && positions < size {
                memmove(
                    arr.offset(positions as isize) as *mut core::ffi::c_void,
                    arr as *const core::ffi::c_void,
                    ((size - positions) as size_t)
                        .wrapping_mul(::core::mem::size_of::<core::ffi::c_int>() as size_t),
                );
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while i < positions {
                    *arr.offset(i as isize) = 0 as core::ffi::c_int;
                    i += 1;
                }
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_string(str: *const core::ffi::c_char) -> core::ffi::c_int {
            if *str != 0 {
                return strlen(str) as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn apply_bitmask(
            value: core::ffi::c_int,
            operation: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mask1: core::ffi::c_int = 0o360 as core::ffi::c_int;
            let mask2: core::ffi::c_int = 0o17 as core::ffi::c_int;
            let mask3: core::ffi::c_int = 0o252 as core::ffi::c_int;
            let mask4: core::ffi::c_int = 0o125 as core::ffi::c_int;
            match operation {
                0 => value & mask1,
                1 => value & mask2,
                2 => value | mask3,
                3 => value ^ mask4,
                _ => value,
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn init_matrix(matrix: *mut [core::ffi::c_int; 4]) {
            let temp: [[core::ffi::c_int; 4]; 3] = [
                [
                    1 as core::ffi::c_int,
                    2 as core::ffi::c_int,
                    3 as core::ffi::c_int,
                    4 as core::ffi::c_int,
                ],
                [
                    5 as core::ffi::c_int,
                    6 as core::ffi::c_int,
                    7 as core::ffi::c_int,
                    8 as core::ffi::c_int,
                ],
                [
                    9 as core::ffi::c_int,
                    10 as core::ffi::c_int,
                    11 as core::ffi::c_int,
                    12 as core::ffi::c_int,
                ],
            ];
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < 3 as core::ffi::c_int {
                let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                while j < 4 as core::ffi::c_int {
                    (*matrix.offset(i as isize))[j as usize] = temp[i as usize][j as usize];
                    j += 1;
                }
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn compare_allocations(
            val1: core::ffi::c_int,
            val2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let ptr1: *mut core::ffi::c_int =
                malloc(::core::mem::size_of::<core::ffi::c_int>() as size_t)
                    as *mut core::ffi::c_int;
            let ptr2: *mut core::ffi::c_int =
                malloc(::core::mem::size_of::<core::ffi::c_int>() as size_t)
                    as *mut core::ffi::c_int;
            let mut uninit_ptr: *mut core::ffi::c_int = std::ptr::null_mut::<core::ffi::c_int>();
            if ptr1.is_null() || ptr2.is_null() {
                free(ptr1 as *mut core::ffi::c_void);
                free(ptr2 as *mut core::ffi::c_void);
                return -(1 as core::ffi::c_int);
            }
            *ptr1 = val1;
            *ptr2 = val2;
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            if ptr1 < ptr2 {
                result = 1 as core::ffi::c_int;
            } else if ptr1 > ptr2 {
                result = 2 as core::ffi::c_int;
            } else {
                result = 3 as core::ffi::c_int;
            }
            uninit_ptr = ptr1;
            result += if *uninit_ptr > 0 as core::ffi::c_int {
                10 as core::ffi::c_int
            } else {
                0 as core::ffi::c_int
            };
            free(ptr1 as *mut core::ffi::c_void);
            free(ptr2 as *mut core::ffi::c_void);
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn arity4(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut block: DataBlock = {
                DataBlock {
                    values: [param1, param2, param3, param4],
                    count: 4 as core::ffi::c_int,
                    label: std::ptr::null_mut::<core::ffi::c_char>(),
                }
            };
            let test_str: [core::ffi::c_char; 6] = [
                b'H' as i8,
                b'e' as i8,
                b'l' as i8,
                b'l' as i8,
                b'o' as i8,
                b'\0' as i8,
            ];
            let empty_str: [core::ffi::c_char; 1] = [b'\0' as i8];
            let len1: core::ffi::c_int = process_string(test_str.as_ptr());
            let len2: core::ffi::c_int = process_string(empty_str.as_ptr());
            result += len1 + len2;
            shift_array(
                (block.values).as_mut_ptr(),
                4 as core::ffi::c_int,
                1 as core::ffi::c_int,
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < block.count {
                result += block.values[i as usize];
                i += 1;
            }
            result = apply_bitmask(result, param1 % 4 as core::ffi::c_int);
            let mut matrix: [[core::ffi::c_int; 4]; 3] = [[0; 4]; 3];
            init_matrix(matrix.as_mut_ptr());
            result += matrix[0 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize]
                + matrix[2 as core::ffi::c_int as usize][3 as core::ffi::c_int as usize];
            let alloc_result: core::ffi::c_int = compare_allocations(param1, param2);
            result += alloc_result;
            if param3 != 0 as core::ffi::c_int {
                result = result * param3 / 100 as core::ffi::c_int;
            }
            if param4 != 0 as core::ffi::c_int {
                result += param4;
            }
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn arity2(
            p1: core::ffi::c_int,
            p2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            arity4(p1, p2, 0 as core::ffi::c_int, 0 as core::ffi::c_int)
        }
        #[no_mangle]
        pub unsafe extern "C" fn arity3(
            p1: core::ffi::c_int,
            p2: core::ffi::c_int,
            p3: core::ffi::c_int,
        ) -> core::ffi::c_int {
            arity4(p1, p2, p3, 0 as core::ffi::c_int)
        }
        #[no_mangle]
        pub unsafe extern "C" fn arity(
            len: core::ffi::c_uchar,
            params: *mut core::ffi::c_int,
        ) -> core::ffi::c_int {
            if (len as core::ffi::c_int) < 2 as core::ffi::c_int {
                -(1 as core::ffi::c_int)
            } else if len as core::ffi::c_int == 2 as core::ffi::c_int {
                arity2(
                    *params.offset(0 as core::ffi::c_int as isize),
                    *params.offset(1 as core::ffi::c_int as isize),
                )
            } else if len as core::ffi::c_int == 3 as core::ffi::c_int {
                arity3(
                    *params.offset(0 as core::ffi::c_int as isize),
                    *params.offset(1 as core::ffi::c_int as isize),
                    *params.offset(2 as core::ffi::c_int as isize),
                )
            } else {
                arity4(
                    *params.offset(0 as core::ffi::c_int as isize),
                    *params.offset(1 as core::ffi::c_int as isize),
                    *params.offset(2 as core::ffi::c_int as isize),
                    *params.offset(3 as core::ffi::c_int as isize),
                )
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("arity_lib", SOURCE, &["ptr1", "ptr2"], &[]);
}
