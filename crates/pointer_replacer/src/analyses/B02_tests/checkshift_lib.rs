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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct ComputeState {
            pub accumulator: core::ffi::c_int,
            pub operation_count: core::ffi::c_int,
            pub checksum: core::ffi::c_uint,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ComputeState {}
        #[automatically_derived]
        impl ::core::clone::Clone for ComputeState {
            #[inline]
            fn clone(&self) -> ComputeState {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_uint>;
                *self
            }
        }
        pub type operation_func =
            Option<unsafe extern "C" fn(core::ffi::c_int, core::ffi::c_int) -> core::ffi::c_int>;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAGIC_NUMBER: core::ffi::c_uint = 0xdeadbeef as core::ffi::c_uint;
        pub const MASK_LOWER: core::ffi::c_int = 0xffff as core::ffi::c_int;
        static mut static_multiplier: core::ffi::c_int = 3 as core::ffi::c_int;
        static mut static_addend: core::ffi::c_int = 100 as core::ffi::c_int;
        static mut static_shift_amount: core::ffi::c_int = 2 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn multiply_with_static(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a * b * static_multiplier
        }
        #[no_mangle]
        pub unsafe extern "C" fn add_with_static(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a + b + static_addend
        }
        #[no_mangle]
        pub unsafe extern "C" fn xor_operation(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a ^ b ^ 0xabcd as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn shift_with_static(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
        ) -> core::ffi::c_int {
            a << static_shift_amount | b >> static_shift_amount
        }
        #[no_mangle]
        pub unsafe extern "C" fn get_operation(opcode: core::ffi::c_int) -> operation_func {
            static mut ops: [operation_func; 4] = [None, None, None, None];
            if (ops[0 as core::ffi::c_int as usize]).is_none() {
                ops[0 as core::ffi::c_int as usize] = Some(
                    multiply_with_static
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ) as operation_func;
                ops[1 as core::ffi::c_int as usize] = Some(
                    add_with_static
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ) as operation_func;
                ops[2 as core::ffi::c_int as usize] = Some(
                    xor_operation
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ) as operation_func;
                ops[3 as core::ffi::c_int as usize] = Some(
                    shift_with_static
                        as unsafe extern "C" fn(
                            core::ffi::c_int,
                            core::ffi::c_int,
                        ) -> core::ffi::c_int,
                ) as operation_func;
            }
            if opcode >= 0 as core::ffi::c_int && opcode < 4 as core::ffi::c_int {
                return ops[opcode as usize];
            }
            None
        }
        #[no_mangle]
        pub unsafe extern "C" fn execute_operation(
            func: operation_func,
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            op_name: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if func.is_none() {
                printf(
                    b"Error: Operation function pointer is NULL for %s\n\0" as *const u8
                        as *const core::ffi::c_char,
                    op_name,
                );
                return 0 as core::ffi::c_int;
            }
            printf(
                b"Variable a = %d\n\0" as *const u8 as *const core::ffi::c_char,
                a,
            );
            printf(
                b"Variable b = %d\n\0" as *const u8 as *const core::ffi::c_char,
                b,
            );
            let result: core::ffi::c_int = func.expect("non-null function pointer")(a, b);
            printf(
                b"Result of %s: %d\n\0" as *const u8 as *const core::ffi::c_char,
                op_name,
                result,
            );
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn compute_checksum(
            values: *mut core::ffi::c_int,
            count: core::ffi::c_int,
        ) -> core::ffi::c_uint {
            let mut checksum: core::ffi::c_uint = 0 as core::ffi::c_uint;
            let mut buffer: [core::ffi::c_uchar; 16] = [0; 16];
            if !values.is_null() && count > 0 as core::ffi::c_int {
                let copy_count: core::ffi::c_int = if count > 4 as core::ffi::c_int {
                    4 as core::ffi::c_int
                } else {
                    count
                };
                memcpy(
                    buffer.as_mut_ptr() as *mut core::ffi::c_void,
                    values as *const core::ffi::c_void,
                    (::core::mem::size_of::<core::ffi::c_int>() as size_t)
                        .wrapping_mul(copy_count as size_t),
                );
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while (i as usize)
                    < ::core::mem::size_of::<core::ffi::c_int>().wrapping_mul(copy_count as usize)
                {
                    checksum =
                        checksum << 1 as core::ffi::c_int ^ buffer[i as usize] as core::ffi::c_uint;
                    i += 1;
                }
                checksum ^= MAGIC_NUMBER;
            }
            checksum & MASK_LOWER as core::ffi::c_uint
        }
        #[no_mangle]
        pub unsafe extern "C" fn init_state(
            state: *mut ComputeState,
            initial_value: core::ffi::c_int,
        ) {
            if state.is_null() {
                printf(
                    b"Error: state pointer is NULL in init_state\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            let mut template: ComputeState = {
                ComputeState {
                    accumulator: initial_value,
                    operation_count: 0 as core::ffi::c_int,
                    checksum: 0 as core::ffi::c_uint,
                }
            };
            memcpy(
                state as *mut core::ffi::c_void,
                &mut template as *mut ComputeState as *const core::ffi::c_void,
                ::core::mem::size_of::<ComputeState>() as size_t,
            );
            printf(
                b"State initialized with accumulator = %d\n\0" as *const u8
                    as *const core::ffi::c_char,
                (*state).accumulator,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn apply_operation(
            state: *mut ComputeState,
            value: core::ffi::c_int,
            func: operation_func,
        ) {
            if state.is_null() {
                printf(
                    b"Error: state pointer is NULL in apply_operation\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            if func.is_none() {
                printf(
                    b"Error: operation function pointer is NULL in apply_operation\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            (*state).accumulator =
                func.expect("non-null function pointer")((*state).accumulator, value);
            (*state).operation_count += 1;
        }
        #[no_mangle]
        pub unsafe extern "C" fn checkshift(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            printf(b"\n=== Starting foo function ===\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"Parameters: %d, %d, %d, %d\n\0" as *const u8 as *const core::ffi::c_char,
                param1,
                param2,
                param3,
                param4,
            );
            let mut state: *mut ComputeState =
                malloc(::core::mem::size_of::<ComputeState>() as size_t) as *mut ComputeState;
            if state.is_null() {
                printf(
                    b"Error: Failed to allocate memory for state\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            init_state(state, param1);
            let mut params: [core::ffi::c_int; 4] = [param1, param2, param3, param4];
            let mult_op: operation_func = get_operation(0 as core::ffi::c_int);
            let add_op: operation_func = get_operation(1 as core::ffi::c_int);
            let xor_op: operation_func = get_operation(2 as core::ffi::c_int);
            let shift_op: operation_func = get_operation(3 as core::ffi::c_int);
            printf(b"\n--- Operation 1: Multiply ---\n\0" as *const u8 as *const core::ffi::c_char);
            apply_operation(state, param2, mult_op);
            printf(b"\n--- Operation 2: Add ---\n\0" as *const u8 as *const core::ffi::c_char);
            apply_operation(state, param3, add_op);
            printf(b"\n--- Operation 3: XOR ---\n\0" as *const u8 as *const core::ffi::c_char);
            let xor_result: core::ffi::c_int = execute_operation(
                xor_op,
                (*state).accumulator,
                param4,
                b"XOR\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(b"\n--- Operation 4: Shift ---\n\0" as *const u8 as *const core::ffi::c_char);
            let shift_result: core::ffi::c_int = execute_operation(
                shift_op,
                xor_result,
                param2,
                b"SHIFT\0" as *const u8 as *const core::ffi::c_char,
            );
            (*state).checksum = compute_checksum(params.as_mut_ptr(), 4 as core::ffi::c_int);
            printf(
                b"\nComputed checksum: 0x%04X\n\0" as *const u8 as *const core::ffi::c_char,
                (*state).checksum,
            );
            let final_result: core::ffi::c_int =
                (((*state).accumulator + shift_result) as core::ffi::c_uint ^ (*state).checksum)
                    as core::ffi::c_int;
            printf(
                b"\nFinal accumulator: %d\n\0" as *const u8 as *const core::ffi::c_char,
                (*state).accumulator,
            );
            printf(
                b"Operation count: %d\n\0" as *const u8 as *const core::ffi::c_char,
                (*state).operation_count,
            );
            printf(
                b"Final result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                final_result,
            );
            free(state as *mut core::ffi::c_void);
            state = std::ptr::null_mut::<ComputeState>();
            printf(b"=== Ending foo function ===\n\n\0" as *const u8 as *const core::ffi::c_char);
            final_result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("checkshift_lib", SOURCE);
}
