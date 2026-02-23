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
            fn sprintf(
                __s: *mut core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn realloc(__ptr: *mut core::ffi::c_void, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct StringBuffer {
            pub data: *mut core::ffi::c_char,
            pub capacity: core::ffi::c_int,
            pub length: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for StringBuffer {}
        #[automatically_derived]
        impl ::core::clone::Clone for StringBuffer {
            #[inline]
            fn clone(&self) -> StringBuffer {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn create_buffer(
            initial_capacity: core::ffi::c_int,
        ) -> *mut StringBuffer {
            let buffer: *mut StringBuffer =
                malloc(::core::mem::size_of::<StringBuffer>() as size_t) as *mut StringBuffer;
            if buffer.is_null() {
                return std::ptr::null_mut::<StringBuffer>();
            }
            (*buffer).data = malloc(initial_capacity as size_t) as *mut core::ffi::c_char;
            if ((*buffer).data).is_null() {
                free(buffer as *mut core::ffi::c_void);
                return std::ptr::null_mut::<StringBuffer>();
            }
            (*buffer).capacity = initial_capacity;
            (*buffer).length = 0 as core::ffi::c_int;
            *((*buffer).data).offset(0 as core::ffi::c_int as isize) =
                '\0' as i32 as core::ffi::c_char;
            buffer
        }
        #[no_mangle]
        pub unsafe extern "C" fn append_to_buffer(
            buffer: *mut StringBuffer,
            str: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            let str_len: core::ffi::c_int = strlen(str) as core::ffi::c_int;
            let required_capacity: core::ffi::c_int =
                (*buffer).length + str_len + 1 as core::ffi::c_int;
            if required_capacity > (*buffer).capacity {
                let new_capacity: core::ffi::c_int = required_capacity * 2 as core::ffi::c_int;
                let new_data: *mut core::ffi::c_char = realloc(
                    (*buffer).data as *mut core::ffi::c_void,
                    new_capacity as size_t,
                ) as *mut core::ffi::c_char;
                if new_data.is_null() {
                    return -(1 as core::ffi::c_int);
                }
                (*buffer).data = new_data;
                (*buffer).capacity = new_capacity;
            }
            strcpy(((*buffer).data).offset((*buffer).length as isize), str);
            (*buffer).length += str_len;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn destroy_buffer(buffer: *mut StringBuffer) {
            if !buffer.is_null() {
                if !((*buffer).data).is_null() {
                    free((*buffer).data as *mut core::ffi::c_void);
                }
                free(buffer as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn get_operation_name(
            op_code: core::ffi::c_int,
        ) -> *const core::ffi::c_char {
            match op_code {
                0 => b"add\0" as *const u8 as *const core::ffi::c_char,
                1 => b"subtract\0" as *const u8 as *const core::ffi::c_char,
                2 => b"multiply\0" as *const u8 as *const core::ffi::c_char,
                3 => b"divide\0" as *const u8 as *const core::ffi::c_char,
                _ => b"unknown\0" as *const u8 as *const core::ffi::c_char,
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn perform_operation(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            operation: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if strcmp(operation, b"add\0" as *const u8 as *const core::ffi::c_char)
                == 0 as core::ffi::c_int
            {
                return a + b;
            } else if strcmp(
                operation,
                b"subtract\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                return a - b;
            } else if strcmp(
                operation,
                b"multiply\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                return a * b;
            } else if strcmp(
                operation,
                b"divide\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                if b != 0 as core::ffi::c_int {
                    return a / b;
                }
                return 0 as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffapp(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let log_buffer: *mut StringBuffer = create_buffer(32 as core::ffi::c_int);
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut temp: [core::ffi::c_char; 64] = [0; 64];
            (*log_buffer).length = 0 as core::ffi::c_int;
            sprintf(
                temp.as_mut_ptr(),
                b"Starting computation with %d parameters\n\0" as *const u8
                    as *const core::ffi::c_char,
                4 as core::ffi::c_int,
            );
            append_to_buffer(log_buffer, temp.as_ptr());
            let op1: *const core::ffi::c_char = get_operation_name(param1 % 4 as core::ffi::c_int);
            sprintf(
                temp.as_mut_ptr(),
                b"Operation 1: %s(%d, %d)\n\0" as *const u8 as *const core::ffi::c_char,
                op1,
                param1,
                param2,
            );
            append_to_buffer(log_buffer, temp.as_ptr());
            let intermediate1: core::ffi::c_int = perform_operation(param1, param2, op1);
            result += intermediate1;
            let op2: *const core::ffi::c_char = get_operation_name(param3 % 4 as core::ffi::c_int);
            sprintf(
                temp.as_mut_ptr(),
                b"Operation 2: %s(%d, %d)\n\0" as *const u8 as *const core::ffi::c_char,
                op2,
                param3,
                param4,
            );
            append_to_buffer(log_buffer, temp.as_ptr());
            let intermediate2: core::ffi::c_int = perform_operation(param3, param4, op2);
            result += intermediate2;
            let op3: *const core::ffi::c_char =
                b"multiply\0" as *const u8 as *const core::ffi::c_char;
            sprintf(
                temp.as_mut_ptr(),
                b"Operation 3: %s(%d, %d)\n\0" as *const u8 as *const core::ffi::c_char,
                op3,
                intermediate1,
                intermediate2,
            );
            append_to_buffer(log_buffer, temp.as_ptr());
            let intermediate3: core::ffi::c_int =
                perform_operation(intermediate1, intermediate2, op3);
            if intermediate3 != 0 as core::ffi::c_int {
                result /= intermediate3;
            } else {
                result = param1 + param2 + param3 + param4;
            }
            sprintf(
                temp.as_mut_ptr(),
                b"Final result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                result,
            );
            append_to_buffer(log_buffer, temp.as_ptr());
            printf(
                b"Computation Log:\n%s\n\0" as *const u8 as *const core::ffi::c_char,
                (*log_buffer).data,
            );
            destroy_buffer(log_buffer);
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("buffapp_lib", SOURCE, &["create_buffer#buffer"], &[]);
}
