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
        pub type size_t = usize;
        pub type __uint32_t = u32;
        pub type uint32_t = __uint32_t;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const true_0: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const false_0: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn process_decisions(
            decision_string: *mut core::ffi::c_char,
            length: size_t,
            operation: core::ffi::c_int,
            param: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if decision_string.is_null() || length == 0 as size_t {
                return -(1 as core::ffi::c_int);
            }
            match operation {
                0 => {
                    if length < 3 as size_t {
                        return -(2 as core::ffi::c_int);
                    }
                    let read: bool =
                        parse_bool(*decision_string.offset(0 as core::ffi::c_int as isize));
                    let write: bool =
                        parse_bool(*decision_string.offset(1 as core::ffi::c_int as isize));
                    let execute: bool =
                        parse_bool(*decision_string.offset(2 as core::ffi::c_int as isize));
                    apply_permissions(read, write, execute)
                }
                1 => {
                    if length < 3 as size_t {
                        return -(2 as core::ffi::c_int);
                    }
                    let cond1: bool =
                        parse_bool(*decision_string.offset(0 as core::ffi::c_int as isize));
                    let cond2: bool =
                        parse_bool(*decision_string.offset(1 as core::ffi::c_int as isize));
                    let cond3: bool =
                        parse_bool(*decision_string.offset(2 as core::ffi::c_int as isize));
                    evaluate_conditions(cond1, cond2, cond3, param)
                }
                2 => {
                    let mut decisions: [bool; 32] = [false; 32];
                    let count: size_t = if length < 32 as size_t {
                        length
                    } else {
                        32 as size_t
                    };
                    let mut i: size_t = 0 as size_t;
                    while i < count {
                        decisions[i as usize] = parse_bool(*decision_string.add(i));
                        i = i.wrapping_add(1);
                    }
                    configure_flags(decisions.as_mut_ptr(), count)
                }
                3 => validate_sequence(decision_string, length),
                _ => -(3 as core::ffi::c_int),
            }
        }
        unsafe extern "C" fn parse_bool(c: core::ffi::c_char) -> bool {
            if c as core::ffi::c_int == 'y' as i32 || c as core::ffi::c_int == 'Y' as i32 {
                return true_0 != 0;
            } else if c as core::ffi::c_int == 'n' as i32 || c as core::ffi::c_int == 'N' as i32 {
                return false_0 != 0;
            }
            false_0 != 0
        }
        unsafe extern "C" fn apply_permissions(
            read: bool,
            write: bool,
            execute: bool,
        ) -> core::ffi::c_int {
            let mut permission_value: core::ffi::c_int = 0 as core::ffi::c_int;
            if read {
                permission_value += 4 as core::ffi::c_int;
            }
            if write {
                permission_value += 2 as core::ffi::c_int;
            }
            if execute {
                permission_value += 1 as core::ffi::c_int;
            }
            if read as core::ffi::c_int != 0
                && write as core::ffi::c_int != 0
                && execute as core::ffi::c_int != 0
            {
                return 100 as core::ffi::c_int + permission_value;
            } else if read as core::ffi::c_int != 0 && write as core::ffi::c_int != 0 {
                if permission_value == 6 as core::ffi::c_int {
                    return 50 as core::ffi::c_int + permission_value;
                }
            } else if read as core::ffi::c_int != 0 && execute as core::ffi::c_int != 0 {
                return 30 as core::ffi::c_int + permission_value;
            } else if write as core::ffi::c_int != 0 && execute as core::ffi::c_int != 0 {
                return 20 as core::ffi::c_int + permission_value;
            } else if read {
                return 10 as core::ffi::c_int + permission_value;
            } else if write {
                return -(10 as core::ffi::c_int);
            } else if execute {
                return -(20 as core::ffi::c_int);
            }
            0 as core::ffi::c_int
        }
        unsafe extern "C" fn evaluate_conditions(
            cond1: bool,
            cond2: bool,
            cond3: bool,
            logic_op: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: bool = false;
            match logic_op {
                0 => {
                    result = cond1 as core::ffi::c_int != 0
                        && cond2 as core::ffi::c_int != 0
                        && cond3 as core::ffi::c_int != 0;
                    if result {
                        100 as core::ffi::c_int
                    } else {
                        if cond1 as core::ffi::c_int != 0 && cond2 as core::ffi::c_int != 0 {
                            return 50 as core::ffi::c_int;
                        }
                        if cond1 as core::ffi::c_int != 0 && cond3 as core::ffi::c_int != 0 {
                            return 51 as core::ffi::c_int;
                        }
                        if cond2 as core::ffi::c_int != 0 && cond3 as core::ffi::c_int != 0 {
                            return 52 as core::ffi::c_int;
                        }
                        if cond1 {
                            return 10 as core::ffi::c_int;
                        }
                        if cond2 {
                            return 11 as core::ffi::c_int;
                        }
                        if cond3 {
                            return 12 as core::ffi::c_int;
                        }
                        0 as core::ffi::c_int
                    }
                }
                1 => {
                    result = cond1 as core::ffi::c_int != 0
                        || cond2 as core::ffi::c_int != 0
                        || cond3 as core::ffi::c_int != 0;
                    if result {
                        let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
                        if cond1 {
                            count += 1;
                        }
                        if cond2 {
                            count += 1;
                        }
                        if cond3 {
                            count += 1;
                        }
                        return 100 as core::ffi::c_int + count;
                    }
                    0 as core::ffi::c_int
                }
                2 => {
                    result = cond1 as core::ffi::c_int
                        ^ cond2 as core::ffi::c_int
                        ^ cond3 as core::ffi::c_int
                        != 0;
                    if result {
                        if cond1 as core::ffi::c_int != 0 && !cond2 && !cond3 {
                            return 1 as core::ffi::c_int;
                        }
                        if !cond1 && cond2 as core::ffi::c_int != 0 && !cond3 {
                            return 2 as core::ffi::c_int;
                        }
                        if !cond1 && !cond2 && cond3 as core::ffi::c_int != 0 {
                            return 3 as core::ffi::c_int;
                        }
                        if cond1 as core::ffi::c_int != 0
                            && cond2 as core::ffi::c_int != 0
                            && cond3 as core::ffi::c_int != 0
                        {
                            return 7 as core::ffi::c_int;
                        }
                        return 90 as core::ffi::c_int;
                    }
                    0 as core::ffi::c_int
                }
                3 => {
                    result = !(cond1 as core::ffi::c_int != 0
                        && cond2 as core::ffi::c_int != 0
                        && cond3 as core::ffi::c_int != 0);
                    if result {
                        if !cond1 && !cond2 && !cond3 {
                            return 200 as core::ffi::c_int;
                        }
                        if !cond1 {
                            return 150 as core::ffi::c_int;
                        }
                        if !cond2 {
                            return 151 as core::ffi::c_int;
                        }
                        if !cond3 {
                            return 152 as core::ffi::c_int;
                        }
                        return 100 as core::ffi::c_int;
                    }
                    0 as core::ffi::c_int
                }
                _ => -(1 as core::ffi::c_int),
            }
        }
        unsafe extern "C" fn configure_flags(
            decisions: *mut bool,
            count: size_t,
        ) -> core::ffi::c_int {
            let mut flags: uint32_t = 0 as uint32_t;
            let mut special_count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: size_t = 0 as size_t;
            while i < count && i < 32 as size_t {
                if *decisions.add(i) {
                    flags =
                        (flags as core::ffi::c_uint | (1 as core::ffi::c_uint) << i) as uint32_t;
                    special_count += 1;
                }
                i = i.wrapping_add(1);
            }
            if special_count == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            } else if special_count as size_t == count {
                return 1000 as core::ffi::c_int + count as core::ffi::c_int;
            } else if special_count == 1 as core::ffi::c_int {
                let mut i_0: size_t = 0 as size_t;
                while i_0 < count {
                    if *decisions.add(i_0) {
                        return 100 as core::ffi::c_int + i_0 as core::ffi::c_int;
                    }
                    i_0 = i_0.wrapping_add(1);
                }
            } else if special_count as size_t == count.wrapping_sub(1 as size_t) {
                let mut i_1: size_t = 0 as size_t;
                while i_1 < count {
                    if !*decisions.add(i_1) {
                        return 200 as core::ffi::c_int + i_1 as core::ffi::c_int;
                    }
                    i_1 = i_1.wrapping_add(1);
                }
            }
            let mut alternating: bool = true_0 != 0;
            let mut i_2: size_t = 1 as size_t;
            while i_2 < count {
                if *decisions.add(i_2) as core::ffi::c_int
                    == *decisions.add(i_2.wrapping_sub(1 as size_t)) as core::ffi::c_int
                {
                    alternating = false_0 != 0;
                    break;
                } else {
                    i_2 = i_2.wrapping_add(1);
                }
            }
            if alternating {
                return 500 as core::ffi::c_int + special_count;
            }
            let mut max_consecutive: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut current_consecutive: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i_3: size_t = 0 as size_t;
            while i_3 < count {
                if *decisions.add(i_3) {
                    current_consecutive += 1;
                    if current_consecutive > max_consecutive {
                        max_consecutive = current_consecutive;
                    }
                } else {
                    current_consecutive = 0 as core::ffi::c_int;
                }
                i_3 = i_3.wrapping_add(1);
            }
            if max_consecutive >= 3 as core::ffi::c_int {
                return 300 as core::ffi::c_int + max_consecutive;
            }
            special_count
        }
        unsafe extern "C" fn validate_sequence(
            sequence: *mut core::ffi::c_char,
            len: size_t,
        ) -> core::ffi::c_int {
            if len == 0 as size_t {
                return 0 as core::ffi::c_int;
            }
            let bools: *mut bool = sequence as *mut bool;
            let mut i: size_t = 0 as size_t;
            while i < len {
                let val: bool = parse_bool(*sequence.add(i));
                *bools.add(i) = val;
                i = i.wrapping_add(1);
            }
            if !*bools.offset(0 as core::ffi::c_int as isize) {
                return -(10 as core::ffi::c_int);
            }
            if len > 1 as size_t
                && *bools.add(len.wrapping_sub(1 as size_t)) as core::ffi::c_int != 0
            {
                return -(11 as core::ffi::c_int);
            }
            let mut consecutive: core::ffi::c_int = 1 as core::ffi::c_int;
            let mut i_0: size_t = 1 as size_t;
            while i_0 < len {
                if *bools.add(i_0) as core::ffi::c_int
                    == *bools.add(i_0.wrapping_sub(1 as size_t)) as core::ffi::c_int
                {
                    consecutive += 1;
                    if consecutive > 3 as core::ffi::c_int {
                        return -(12 as core::ffi::c_int);
                    }
                } else {
                    consecutive = 1 as core::ffi::c_int;
                }
                i_0 = i_0.wrapping_add(1);
            }
            let mut transitions: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i_1: size_t = 1 as size_t;
            while i_1 < len {
                if *bools.add(i_1) as core::ffi::c_int
                    != *bools.add(i_1.wrapping_sub(1 as size_t)) as core::ffi::c_int
                {
                    transitions += 1;
                }
                i_1 = i_1.wrapping_add(1);
            }
            if len <= 3 as size_t {
                if transitions == 0 as core::ffi::c_int {
                    return 1 as core::ffi::c_int;
                }
                if transitions as size_t == len.wrapping_sub(1 as size_t) {
                    return 2 as core::ffi::c_int;
                }
                10 as core::ffi::c_int + transitions
            } else if len <= 10 as size_t {
                if (transitions as size_t) < len.wrapping_div(3 as size_t) {
                    return 20 as core::ffi::c_int;
                }
                if transitions as size_t > len.wrapping_div(2 as size_t) {
                    return 30 as core::ffi::c_int;
                }
                25 as core::ffi::c_int
            } else {
                if transitions < 3 as core::ffi::c_int {
                    return 40 as core::ffi::c_int;
                }
                if transitions as size_t > len.wrapping_sub(3 as size_t) {
                    return 50 as core::ffi::c_int;
                }
                45 as core::ffi::c_int
            }
        }
    }
    pub mod main {
        use crate::src::lib::process_decisions;
        use crate::src::lib::size_t;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stdin: *mut FILE;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        #[repr(C)]
        pub struct _IO_FILE {
            pub _flags: core::ffi::c_int,
            pub _IO_read_ptr: *mut core::ffi::c_char,
            pub _IO_read_end: *mut core::ffi::c_char,
            pub _IO_read_base: *mut core::ffi::c_char,
            pub _IO_write_base: *mut core::ffi::c_char,
            pub _IO_write_ptr: *mut core::ffi::c_char,
            pub _IO_write_end: *mut core::ffi::c_char,
            pub _IO_buf_base: *mut core::ffi::c_char,
            pub _IO_buf_end: *mut core::ffi::c_char,
            pub _IO_save_base: *mut core::ffi::c_char,
            pub _IO_backup_base: *mut core::ffi::c_char,
            pub _IO_save_end: *mut core::ffi::c_char,
            pub _markers: *mut _IO_marker,
            pub _chain: *mut _IO_FILE,
            pub _fileno: core::ffi::c_int,
            pub _flags2: core::ffi::c_int,
            pub _old_offset: __off_t,
            pub _cur_column: core::ffi::c_ushort,
            pub _vtable_offset: core::ffi::c_schar,
            pub _shortbuf: [core::ffi::c_char; 1],
            pub _lock: *mut core::ffi::c_void,
            pub _offset: __off64_t,
            pub _codecvt: *mut _IO_codecvt,
            pub _wide_data: *mut _IO_wide_data,
            pub _freeres_list: *mut _IO_FILE,
            pub _freeres_buf: *mut core::ffi::c_void,
            pub __pad5: size_t,
            pub _mode: core::ffi::c_int,
            pub _unused2: [core::ffi::c_char; 20],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for _IO_FILE {}
        #[automatically_derived]
        impl ::core::clone::Clone for _IO_FILE {
            #[inline]
            fn clone(&self) -> _IO_FILE {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_marker>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<__off_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_ushort>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_schar>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 1]>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<__off64_t>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_codecvt>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_wide_data>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 20]>;
                *self
            }
        }
        pub type _IO_lock_t = ();
        pub type FILE = _IO_FILE;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_INPUT_SIZE: core::ffi::c_int = 1024 as core::ffi::c_int;
        unsafe fn main_0() -> core::ffi::c_int {
            let mut input_buffer: [core::ffi::c_char; 1024] = [0; 1024];
            let mut operation: core::ffi::c_int = 0;
            let mut param: core::ffi::c_int = 0;
            let mut result: core::ffi::c_int = 0;
            if (fgets(input_buffer.as_mut_ptr(), MAX_INPUT_SIZE, stdin)).is_null() {
                fprintf(
                    stderr,
                    b"Error reading operation\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            operation = atoi(input_buffer.as_ptr());
            if (fgets(input_buffer.as_mut_ptr(), MAX_INPUT_SIZE, stdin)).is_null() {
                fprintf(
                    stderr,
                    b"Error reading parameter\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            param = atoi(input_buffer.as_ptr());
            if (fgets(input_buffer.as_mut_ptr(), MAX_INPUT_SIZE, stdin)).is_null() {
                fprintf(
                    stderr,
                    b"Error reading decision string\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            let mut len: size_t = strlen(input_buffer.as_ptr());
            if len > 0 as size_t
                && input_buffer[len.wrapping_sub(1 as size_t) as usize] as core::ffi::c_int
                    == '\n' as i32
            {
                input_buffer[len.wrapping_sub(1 as size_t) as usize] =
                    '\0' as i32 as core::ffi::c_char;
                len = len.wrapping_sub(1);
            }
            result = process_decisions(input_buffer.as_mut_ptr(), len, operation, param);
            printf(b"%d\n\0" as *const u8 as *const core::ffi::c_char, result);
            0 as core::ffi::c_int
        }
        pub fn main() {
            unsafe { ::std::process::exit(main_0() as i32) }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("char-to-bool", SOURCE, &[], &[]);
}
