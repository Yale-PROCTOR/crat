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
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strncat(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn strncmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
                __n: size_t,
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn snprintf(
                __s: *mut core::ffi::c_char,
                __maxlen: size_t,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
        }
        pub type size_t = usize;
        pub type __uint32_t = u32;
        pub type uint32_t = __uint32_t;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn process_strings(
            input: *mut core::ffi::c_char,
            input_len: size_t,
            reference: *const core::ffi::c_char,
            ref_len: size_t,
            operation: core::ffi::c_int,
            flags: uint32_t,
        ) -> core::ffi::c_int {
            if input.is_null() {
                return -(1 as core::ffi::c_int);
            }
            match operation {
                0 => {
                    if reference.is_null() {
                        return -(2 as core::ffi::c_int);
                    }
                    validate_token(input, reference)
                }
                1 => {
                    let mut commands: [*const core::ffi::c_char; 5] = [
                        b"START\0" as *const u8 as *const core::ffi::c_char,
                        b"STOP\0" as *const u8 as *const core::ffi::c_char,
                        b"PAUSE\0" as *const u8 as *const core::ffi::c_char,
                        b"RESUME\0" as *const u8 as *const core::ffi::c_char,
                        b"RESET\0" as *const u8 as *const core::ffi::c_char,
                    ];
                    parse_command(
                        input,
                        input_len,
                        commands.as_mut_ptr(),
                        5 as core::ffi::c_int,
                    )
                }
                2 => {
                    if reference.is_null() {
                        return -(2 as core::ffi::c_int);
                    }
                    let exact: core::ffi::c_int = (flags & 0x1 as uint32_t) as core::ffi::c_int;
                    compare_prefix(input, reference, exact)
                }
                3 => {
                    let delim: core::ffi::c_char = (if !reference.is_null() && ref_len > 0 as size_t
                    {
                        *reference.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    } else {
                        ':' as i32
                    }) as core::ffi::c_char;
                    find_delimiter(input, input_len, delim)
                }
                4 => {
                    if reference.is_null() {
                        return -(2 as core::ffi::c_int);
                    }
                    let case_sens: core::ffi::c_int = (flags & 0x2 as uint32_t) as core::ffi::c_int;
                    match_pattern(input, reference, case_sens)
                }
                _ => -(3 as core::ffi::c_int),
            }
        }
        unsafe extern "C" fn validate_token(
            token: *const core::ffi::c_char,
            expected: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if strcmp(token, expected) == 0 as core::ffi::c_int {
                return 1 as core::ffi::c_int;
            }
            if strcmp(token, b"VALID\0" as *const u8 as *const core::ffi::c_char)
                == 0 as core::ffi::c_int
                || strcmp(token, b"OK\0" as *const u8 as *const core::ffi::c_char)
                    == 0 as core::ffi::c_int
            {
                return 1 as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        unsafe extern "C" fn parse_command(
            buffer: *mut core::ffi::c_char,
            buf_size: size_t,
            cmd_list: *mut *const core::ffi::c_char,
            list_size: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < list_size {
                let cmd_len: size_t = strlen(*cmd_list.offset(i as isize));
                if buf_size >= cmd_len
                    && strncmp(buffer, *cmd_list.offset(i as isize), cmd_len)
                        == 0 as core::ffi::c_int
                    && (*buffer.add(cmd_len) as core::ffi::c_int == '\0' as i32
                        || *buffer.add(cmd_len) as core::ffi::c_int == ' ' as i32)
                {
                    return i;
                }
                if strcmp(buffer, *cmd_list.offset(i as isize)) == 0 as core::ffi::c_int {
                    return i;
                }
                i += 1;
            }
            if strcmp(buffer, b"ADMIN\0" as *const u8 as *const core::ffi::c_char)
                == 0 as core::ffi::c_int
            {
                return 99 as core::ffi::c_int;
            }
            -(1 as core::ffi::c_int)
        }
        unsafe extern "C" fn compare_prefix(
            str: *const core::ffi::c_char,
            prefix: *const core::ffi::c_char,
            exact_match: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let prefix_len: size_t = strlen(prefix);
            if exact_match != 0 {
                if strcmp(str, prefix) == 0 as core::ffi::c_int {
                    return 1 as core::ffi::c_int;
                }
                let variations: [[core::ffi::c_char; 32]; 5] = [
                    [
                        b'_' as i8,
                        b'v' as i8,
                        b'1' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                    ],
                    [
                        b'_' as i8,
                        b'v' as i8,
                        b'2' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                    ],
                    [
                        b'_' as i8,
                        b'o' as i8,
                        b'l' as i8,
                        b'd' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                    ],
                    [
                        b'_' as i8,
                        b'n' as i8,
                        b'e' as i8,
                        b'w' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                    ],
                    [
                        b'_' as i8,
                        b't' as i8,
                        b'm' as i8,
                        b'p' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                    ],
                ];
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while i < 5 as core::ffi::c_int {
                    let mut expected: [core::ffi::c_char; 64] = [0; 64];
                    strncpy(expected.as_mut_ptr(), prefix, 63 as size_t);
                    expected[63 as core::ffi::c_int as usize] = '\0' as i32 as core::ffi::c_char;
                    strncat(
                        expected.as_mut_ptr(),
                        (variations[i as usize]).as_ptr(),
                        (63 as size_t).wrapping_sub(strlen(expected.as_ptr())),
                    );
                    if strcmp(str, expected.as_ptr()) == 0 as core::ffi::c_int {
                        return 2 as core::ffi::c_int + i;
                    }
                    i += 1;
                }
                0 as core::ffi::c_int
            } else {
                if strncmp(str, prefix, prefix_len) == 0 as core::ffi::c_int {
                    return 1 as core::ffi::c_int;
                }
                0 as core::ffi::c_int
            }
        }
        unsafe extern "C" fn find_delimiter(
            data: *const core::ffi::c_char,
            len: size_t,
            delim: core::ffi::c_char,
        ) -> core::ffi::c_int {
            if len == 0 as size_t {
                return -(1 as core::ffi::c_int);
            }
            let mut i: size_t = 0 as size_t;
            while i < len {
                if *data.add(i) as core::ffi::c_int == delim as core::ffi::c_int {
                    return i as core::ffi::c_int;
                }
                if *data.add(i) as core::ffi::c_int == '\0' as i32 {
                    break;
                }
                i = i.wrapping_add(1);
            }
            if delim as core::ffi::c_int == '|' as i32
                && strcmp(data, b"NONE\0" as *const u8 as *const core::ffi::c_char)
                    == 0 as core::ffi::c_int
            {
                return -(2 as core::ffi::c_int);
            }
            if delim as core::ffi::c_int == ':' as i32
                && strcmp(data, b"EMPTY\0" as *const u8 as *const core::ffi::c_char)
                    == 0 as core::ffi::c_int
            {
                return -(3 as core::ffi::c_int);
            }
            -(1 as core::ffi::c_int)
        }
        unsafe extern "C" fn match_pattern(
            text: *const core::ffi::c_char,
            pattern: *const core::ffi::c_char,
            case_sensitive: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if case_sensitive != 0 {
                if strcmp(text, pattern) == 0 as core::ffi::c_int {
                    return 1 as core::ffi::c_int;
                }
                let mut wildcard_patterns: [[core::ffi::c_char; 64]; 3] = [[0; 64]; 3];
                snprintf(
                    (wildcard_patterns[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                    64 as size_t,
                    b"*%s*\0" as *const u8 as *const core::ffi::c_char,
                    pattern,
                );
                snprintf(
                    (wildcard_patterns[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                    64 as size_t,
                    b"%s*\0" as *const u8 as *const core::ffi::c_char,
                    pattern,
                );
                snprintf(
                    (wildcard_patterns[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                    64 as size_t,
                    b"*%s\0" as *const u8 as *const core::ffi::c_char,
                    pattern,
                );
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while i < 3 as core::ffi::c_int {
                    if strcmp(text, (wildcard_patterns[i as usize]).as_ptr())
                        == 0 as core::ffi::c_int
                    {
                        return 2 as core::ffi::c_int + i;
                    }
                    i += 1;
                }
                let text_len: size_t = strlen(text);
                let pattern_len: size_t = strlen(pattern);
                let mut i_0: size_t = 0 as size_t;
                while i_0 <= text_len.wrapping_sub(pattern_len) {
                    if strncmp(&*text.add(i_0), pattern, pattern_len) == 0 as core::ffi::c_int {
                        return (10 as size_t).wrapping_add(i_0) as core::ffi::c_int;
                    }
                    i_0 = i_0.wrapping_add(1);
                }
            } else {
                if strcmp(text, pattern) == 0 as core::ffi::c_int {
                    return 1 as core::ffi::c_int;
                }
                let pattern_len_0: size_t = strlen(pattern);
                let text_len_0: size_t = strlen(text);
                if text_len_0 != pattern_len_0
                    && strncmp(text, pattern, pattern_len_0) == 0 as core::ffi::c_int
                {
                    return 5 as core::ffi::c_int;
                }
                if text_len_0 == pattern_len_0 {
                    let mut match_0: core::ffi::c_int = 1 as core::ffi::c_int;
                    let mut i_1: size_t = 0 as size_t;
                    while i_1 < pattern_len_0 {
                        let mut c1: core::ffi::c_char = *text.add(i_1);
                        let mut c2: core::ffi::c_char = *pattern.add(i_1);
                        if c1 as core::ffi::c_int >= 'A' as i32
                            && c1 as core::ffi::c_int <= 'Z' as i32
                        {
                            c1 = (c1 as core::ffi::c_int + 32 as core::ffi::c_int)
                                as core::ffi::c_char;
                        }
                        if c2 as core::ffi::c_int >= 'A' as i32
                            && c2 as core::ffi::c_int <= 'Z' as i32
                        {
                            c2 = (c2 as core::ffi::c_int + 32 as core::ffi::c_int)
                                as core::ffi::c_char;
                        }
                        if c1 as core::ffi::c_int != c2 as core::ffi::c_int {
                            match_0 = 0 as core::ffi::c_int;
                            break;
                        } else {
                            i_1 = i_1.wrapping_add(1);
                        }
                    }
                    if match_0 != 0 {
                        return 6 as core::ffi::c_int;
                    }
                }
            }
            0 as core::ffi::c_int
        }
    }
    pub mod main {
        use crate::src::lib::process_strings;
        use crate::src::lib::size_t;
        use crate::src::lib::uint32_t;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn scanf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
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
        pub const MAX_BUFFER_SIZE: core::ffi::c_int = 1024 as core::ffi::c_int;
        unsafe fn main_0() -> core::ffi::c_int {
            let mut operation: core::ffi::c_int = 0;
            let mut flags: uint32_t = 0;
            let mut input_len: size_t = 0;
            let mut ref_len: size_t = 0;
            let mut input_buffer: [core::ffi::c_char; 1024] = [0; 1024];
            let mut ref_buffer: [core::ffi::c_char; 1024] = [0; 1024];
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut operation as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error reading operation\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if scanf(
                b"%u\0" as *const u8 as *const core::ffi::c_char,
                &mut flags as *mut uint32_t,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error reading flags\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if scanf(
                b"%zu\0" as *const u8 as *const core::ffi::c_char,
                &mut input_len as *mut size_t,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error reading input length\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if input_len > MAX_BUFFER_SIZE as size_t {
                fprintf(
                    stderr,
                    b"Error: input length %zu exceeds maximum %d\n\0" as *const u8
                        as *const core::ffi::c_char,
                    input_len,
                    MAX_BUFFER_SIZE,
                );
                return 1 as core::ffi::c_int;
            }
            let mut i: size_t = 0 as size_t;
            while i < input_len {
                let mut byte: core::ffi::c_uint = 0;
                if scanf(
                    b"%u\0" as *const u8 as *const core::ffi::c_char,
                    &mut byte as *mut core::ffi::c_uint,
                ) != 1 as core::ffi::c_int
                {
                    fprintf(
                        stderr,
                        b"Error reading input byte %zu\n\0" as *const u8
                            as *const core::ffi::c_char,
                        i,
                    );
                    return 1 as core::ffi::c_int;
                }
                input_buffer[i as usize] = byte as core::ffi::c_char;
                i = i.wrapping_add(1);
            }
            if scanf(
                b"%zu\0" as *const u8 as *const core::ffi::c_char,
                &mut ref_len as *mut size_t,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error reading reference length\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if ref_len > MAX_BUFFER_SIZE as size_t {
                fprintf(
                    stderr,
                    b"Error: reference length %zu exceeds maximum %d\n\0" as *const u8
                        as *const core::ffi::c_char,
                    ref_len,
                    MAX_BUFFER_SIZE,
                );
                return 1 as core::ffi::c_int;
            }
            let mut i_0: size_t = 0 as size_t;
            while i_0 < ref_len {
                let mut byte_0: core::ffi::c_uint = 0;
                if scanf(
                    b"%u\0" as *const u8 as *const core::ffi::c_char,
                    &mut byte_0 as *mut core::ffi::c_uint,
                ) != 1 as core::ffi::c_int
                {
                    fprintf(
                        stderr,
                        b"Error reading reference byte %zu\n\0" as *const u8
                            as *const core::ffi::c_char,
                        i_0,
                    );
                    return 1 as core::ffi::c_int;
                }
                ref_buffer[i_0 as usize] = byte_0 as core::ffi::c_char;
                i_0 = i_0.wrapping_add(1);
            }
            let result: core::ffi::c_int = process_strings(
                input_buffer.as_mut_ptr(),
                input_len,
                ref_buffer.as_ptr(),
                ref_len,
                operation,
                flags,
            );
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
    run_ownership_case("strcpy", SOURCE);
}
