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
            fn snprintf(
                __s: *mut core::ffi::c_char,
                __maxlen: size_t,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn strncmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
                __n: size_t,
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub union C2RustUnnamed {
            pub i: core::ffi::c_int,
            pub f: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for C2RustUnnamed {}
        #[automatically_derived]
        impl ::core::clone::Clone for C2RustUnnamed {
            #[inline]
            fn clone(&self) -> C2RustUnnamed {
                let _: ::core::clone::AssertParamIsCopy<Self>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        unsafe extern "C" fn memchra(
            str: *const core::ffi::c_char,
            c: core::ffi::c_int,
            n: size_t,
        ) -> core::ffi::c_int {
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: size_t = 0 as size_t;
            while i < n {
                if *str.add(i) as core::ffi::c_int == c as core::ffi::c_char as core::ffi::c_int {
                    count += 1;
                }
                i = i.wrapping_add(1);
            }
            count
        }
        unsafe extern "C" fn process_buffer(
            buffer: *mut core::ffi::c_char,
            len: size_t,
        ) -> core::ffi::c_int {
            if buffer.is_null() || *buffer as core::ffi::c_int == '\0' as i32 {
                return -(1 as core::ffi::c_int);
            }
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: *mut core::ffi::c_char = buffer;
            while i < buffer.add(len) && *i as core::ffi::c_int != '\0' as i32 {
                result += *i as core::ffi::c_int;
                i = i.offset(1);
            }
            result
        }
        unsafe extern "C" fn int_to_float_bits(value: core::ffi::c_int) -> core::ffi::c_float {
            let mut converter: C2RustUnnamed = C2RustUnnamed { i: 0 };
            converter.i = value;
            converter.f
        }
        unsafe extern "C" fn process_strings(
            strings: *mut *mut core::ffi::c_char,
            count: core::ffi::c_int,
            target: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if strings.is_null() || count <= 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            let mut matches: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: *mut *mut core::ffi::c_char = strings;
            while i < strings.offset(count as isize) {
                if !((*i).is_null() || **i as core::ffi::c_int == '\0' as i32) && {
                    let __arg_2 = strlen(target);
                    strncmp(*i, target, __arg_2)
                } == 0
                    as core::ffi::c_int
                {
                    matches += 1;
                }
                i = i.offset(1);
            }
            matches
        }
        unsafe extern "C" fn safe_sum_array(
            arr: *mut core::ffi::c_int,
            size: size_t,
        ) -> core::ffi::c_int {
            if arr.is_null() || size == 0 as size_t {
                return 0 as core::ffi::c_int;
            }
            let mut sum: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: *mut core::ffi::c_int = arr;
            while i < arr.add(size) {
                sum += *i;
                i = i.offset(1);
            }
            sum
        }
        unsafe extern "C" fn interpret_as_int(
            bytes: *mut core::ffi::c_uchar,
            len: size_t,
        ) -> core::ffi::c_int {
            if bytes.is_null() || len < ::core::mem::size_of::<core::ffi::c_int>() {
                return 0 as core::ffi::c_int;
            }
            let int_ptr: *mut core::ffi::c_int = bytes as *mut core::ffi::c_int;
            *int_ptr
        }
        unsafe extern "C" fn count_occurrences(
            text: *const core::ffi::c_char,
            ch: core::ffi::c_char,
        ) -> core::ffi::c_int {
            if text.is_null() || *text as core::ffi::c_int == '\0' as i32 {
                return 0 as core::ffi::c_int;
            }
            let len: size_t = strlen(text);
            memchra(text, ch as core::ffi::c_int, len)
        }
        unsafe extern "C" fn complex_iteration(
            data: *mut core::ffi::c_int,
            count: size_t,
        ) -> core::ffi::c_int {
            if data.is_null() || count == 0 as size_t {
                return -(1 as core::ffi::c_int);
            }
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: *mut core::ffi::c_int = data;
            while i < data.add(count) {
                let u: core::ffi::c_uint = *i as core::ffi::c_uint;
                result ^= (u & 0xff as core::ffi::c_uint) as core::ffi::c_int;
                i = i.offset(1);
            }
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn memchra2(
            a: core::ffi::c_int,
            b: core::ffi::c_int,
            c: core::ffi::c_int,
            d: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut buffer: [core::ffi::c_char; 64] = [0; 64];
            snprintf(
                buffer.as_mut_ptr(),
                ::core::mem::size_of::<[core::ffi::c_char; 64]>() as size_t,
                b"test%d-%d-%d-%d\0" as *const u8 as *const core::ffi::c_char,
                a,
                b,
                c,
                d,
            );
            let dash_count: core::ffi::c_int =
                count_occurrences(buffer.as_ptr(), '-' as i32 as core::ffi::c_char);
            result += dash_count * 10 as core::ffi::c_int;
            let mut values: [core::ffi::c_int; 4] = [a, b, c, d];
            let sum: core::ffi::c_int = safe_sum_array(values.as_mut_ptr(), 4 as size_t);
            result += sum;
            let mut test_strings: [*mut core::ffi::c_char; 4] = [
                b"test1\0" as *const u8 as *const core::ffi::c_char as *mut core::ffi::c_char,
                b"test2\0" as *const u8 as *const core::ffi::c_char as *mut core::ffi::c_char,
                b"testing\0" as *const u8 as *const core::ffi::c_char as *mut core::ffi::c_char,
                b"other\0" as *const u8 as *const core::ffi::c_char as *mut core::ffi::c_char,
            ];
            let matches: core::ffi::c_int = process_strings(
                test_strings.as_mut_ptr(),
                4 as core::ffi::c_int,
                b"test\0" as *const u8 as *const core::ffi::c_char,
            );
            result += matches * 5 as core::ffi::c_int;
            let f: core::ffi::c_float = int_to_float_bits(a);
            if f > 0.0f32 && f < 1000.0f32 {
                result += f as core::ffi::c_int;
            }
            let buf_sum: core::ffi::c_int =
                process_buffer(buffer.as_mut_ptr(), strlen(buffer.as_ptr()));
            if buf_sum > 0 as core::ffi::c_int {
                result += buf_sum % 256 as core::ffi::c_int;
            }
            let mut bytes: [core::ffi::c_uchar; 4] = [0; 4];
            bytes[0 as core::ffi::c_int as usize] =
                (b & 0xff as core::ffi::c_int) as core::ffi::c_uchar;
            bytes[1 as core::ffi::c_int as usize] =
                (c & 0xff as core::ffi::c_int) as core::ffi::c_uchar;
            bytes[2 as core::ffi::c_int as usize] =
                (d & 0xff as core::ffi::c_int) as core::ffi::c_uchar;
            bytes[3 as core::ffi::c_int as usize] = 0 as core::ffi::c_uchar;
            let interpreted: core::ffi::c_int = interpret_as_int(bytes.as_mut_ptr(), 4 as size_t);
            result ^= interpreted;
            let complex_result: core::ffi::c_int =
                complex_iteration(values.as_mut_ptr(), 4 as size_t);
            result += complex_result;
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("memchra2_lib", SOURCE, &[], &[]);
}
