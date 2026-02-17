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
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn sqrt(__x: core::ffi::c_double) -> core::ffi::c_double;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct DataBlock {
            pub id: core::ffi::c_int,
            pub value: core::ffi::c_double,
            pub label: [core::ffi::c_char; 20],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for DataBlock {}
        #[automatically_derived]
        impl ::core::clone::Clone for DataBlock {
            #[inline]
            fn clone(&self) -> DataBlock {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 20]>;
                *self
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn safe_double_to_int(d: core::ffi::c_double) -> core::ffi::c_int {
            if d > INT_MAX as core::ffi::c_double {
                INT_MAX
            } else if d < INT_MIN as core::ffi::c_double {
                INT_MIN
            } else if d.is_nan() as i32 != 0 {
                0 as core::ffi::c_int
            } else {
                d as core::ffi::c_int
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_with_fallthrough(
            code: core::ffi::c_int,
            mut base_value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut current_block_6: u64;
            match code {
                5 => {
                    base_value += 50 as core::ffi::c_int;
                    current_block_6 = 111797835255413507;
                }
                4 => {
                    current_block_6 = 111797835255413507;
                }
                3 => {
                    current_block_6 = 14107434098666203977;
                }
                2 => {
                    current_block_6 = 8373454275325829900;
                }
                1 => {
                    current_block_6 = 4866863597419105774;
                }
                0 => {
                    base_value = 0 as core::ffi::c_int;
                    current_block_6 = 3276175668257526147;
                }
                _ => {
                    base_value = -(1 as core::ffi::c_int);
                    current_block_6 = 3276175668257526147;
                }
            }
            if current_block_6 == 111797835255413507 {
                base_value += 40 as core::ffi::c_int;
                current_block_6 = 14107434098666203977;
            }
            if current_block_6 == 14107434098666203977 {
                base_value += 30 as core::ffi::c_int;
                current_block_6 = 8373454275325829900;
            }
            if current_block_6 == 8373454275325829900 {
                base_value += 20 as core::ffi::c_int;
                current_block_6 = 4866863597419105774;
            }
            if current_block_6 == 4866863597419105774 {
                base_value += 10 as core::ffi::c_int;
            }
            base_value
        }
        #[no_mangle]
        pub unsafe extern "C" fn copy_data_block(dest: *mut DataBlock, src: *const DataBlock) {
            memcpy(
                dest as *mut core::ffi::c_void,
                src as *const core::ffi::c_void,
                ::core::mem::size_of::<DataBlock>() as size_t,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn handle_pointer_operations(
            value: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut ptr: *mut core::ffi::c_int = std::ptr::null_mut::<core::ffi::c_int>();
            let mut local_value: core::ffi::c_int = value * 2 as core::ffi::c_int;
            ptr = &mut local_value;
            let result: core::ffi::c_int = *ptr + 100 as core::ffi::c_int;
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn overunder(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            c: core::ffi::c_int,
            d: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut total: core::ffi::c_int = 0 as core::ffi::c_int;
            let result_1: core::ffi::c_int = a;
            let result_2: core::ffi::c_int = b;
            let result_3: core::ffi::c_int = c;
            let result_4: core::ffi::c_int = d;
            printf(
                b"result_1 = %d\n\0" as *const u8 as *const core::ffi::c_char,
                result_1,
            );
            printf(
                b"result_2 = %d\n\0" as *const u8 as *const core::ffi::c_char,
                result_2,
            );
            let temp1: core::ffi::c_double = a as core::ffi::c_double * 1.5f64;
            let temp2: core::ffi::c_double = b as core::ffi::c_double * 2.7f64;
            let temp3: core::ffi::c_double = c as core::ffi::c_double / 3.3f64;
            let temp4: core::ffi::c_double = sqrt((d * d + a * a) as core::ffi::c_double);
            let conv1: core::ffi::c_int = safe_double_to_int(temp1);
            let conv2: core::ffi::c_int = safe_double_to_int(temp2);
            let conv3: core::ffi::c_int = safe_double_to_int(temp3);
            let conv4: core::ffi::c_int = safe_double_to_int(temp4);
            printf(
                b"Converted values: %d, %d, %d, %d\n\0" as *const u8 as *const core::ffi::c_char,
                conv1,
                conv2,
                conv3,
                conv4,
            );
            let switch_result: core::ffi::c_int =
                process_with_fallthrough(a % 6 as core::ffi::c_int, b);
            printf(
                b"Switch fall-through result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                switch_result,
            );
            let mut source_block: DataBlock = DataBlock {
                id: 0,
                value: 0.,
                label: [0; 20],
            };
            source_block.id = a;
            source_block.value = temp1;
            strncpy(
                (source_block.label).as_mut_ptr(),
                b"Source\0" as *const u8 as *const core::ffi::c_char,
                (::core::mem::size_of::<[core::ffi::c_char; 20]>() as size_t)
                    .wrapping_sub(1 as size_t),
            );
            source_block.label
                [::core::mem::size_of::<[core::ffi::c_char; 20]>().wrapping_sub(1_usize)] =
                '\0' as i32 as core::ffi::c_char;
            let mut dest_block: DataBlock = DataBlock {
                id: 0,
                value: 0.,
                label: [0; 20],
            };
            copy_data_block(&mut dest_block, &mut source_block);
            printf(
                b"Copied block: id=%d, value=%.2f, label=%s\n\0" as *const u8
                    as *const core::ffi::c_char,
                dest_block.id,
                dest_block.value,
                (dest_block.label).as_ptr(),
            );
            let ptr_result: core::ffi::c_int = handle_pointer_operations(c);
            printf(
                b"Pointer operation result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                ptr_result,
            );
            total = conv1 + conv2 + conv3 + conv4 + switch_result + ptr_result;
            total += dest_block.id;
            let overflow_test: core::ffi::c_double = 1e15f64;
            let safe_conv: core::ffi::c_int = safe_double_to_int(overflow_test);
            printf(
                b"Overflow protected conversion: %d\n\0" as *const u8 as *const core::ffi::c_char,
                safe_conv,
            );
            let underflow_test: core::ffi::c_double = -1e15f64;
            let safe_conv2: core::ffi::c_int = safe_double_to_int(underflow_test);
            printf(
                b"Underflow protected conversion: %d\n\0" as *const u8 as *const core::ffi::c_char,
                safe_conv2,
            );
            let mut array1: [core::ffi::c_int; 5] = [a, b, c, d, a + b];
            let mut array2: [core::ffi::c_int; 5] = [0; 5];
            memcpy(
                array2.as_mut_ptr() as *mut core::ffi::c_void,
                array1.as_mut_ptr() as *const core::ffi::c_void,
                ::core::mem::size_of::<[core::ffi::c_int; 5]>() as size_t,
            );
            printf(b"Array copied via memcpy: \0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < 5 as core::ffi::c_int {
                printf(
                    b"%d \0" as *const u8 as *const core::ffi::c_char,
                    array2[i as usize],
                );
                total += array2[i as usize];
                i += 1;
            }
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            total
        }
        pub const INT_MAX: core::ffi::c_int = __INT_MAX__;
        pub const INT_MIN: core::ffi::c_int = -__INT_MAX__ - 1 as core::ffi::c_int;
        pub const __INT_MAX__: core::ffi::c_int = 2147483647 as core::ffi::c_int;
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("overunder_lib", SOURCE);
}
