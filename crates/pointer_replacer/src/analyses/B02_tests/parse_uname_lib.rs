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
#[macro_use]
extern crate c2rust_bitfields;
pub mod src {
    pub mod lib {
        use ::c2rust_bitfields;
        extern "C" {
            pub type re_dfa_t;
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strdup(__s: *const core::ffi::c_char) -> *mut core::ffi::c_char;
            fn strstr(
                __haystack: *const core::ffi::c_char,
                __needle: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn regcomp(
                __preg: *mut regex_t,
                __pattern: *const core::ffi::c_char,
                __cflags: core::ffi::c_int,
            ) -> core::ffi::c_int;
            fn regexec(
                __preg: *const regex_t,
                __String: *const core::ffi::c_char,
                __nmatch: size_t,
                __pmatch: *mut regmatch_t,
                __eflags: core::ffi::c_int,
            ) -> core::ffi::c_int;
            fn regfree(__preg: *mut regex_t);
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn snprintf(
                __s: *mut core::ffi::c_char,
                __maxlen: size_t,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
        }
        #[repr(C)]
        pub struct os_data {
            pub os_name: *mut core::ffi::c_char,
            pub os_version: *mut core::ffi::c_char,
            pub os_major: *mut core::ffi::c_char,
            pub os_minor: *mut core::ffi::c_char,
            pub os_codename: *mut core::ffi::c_char,
            pub os_platform: *mut core::ffi::c_char,
            pub os_build: *mut core::ffi::c_char,
            pub os_uname: *mut core::ffi::c_char,
            pub os_arch: *mut core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for os_data {}
        #[automatically_derived]
        impl ::core::clone::Clone for os_data {
            #[inline]
            fn clone(&self) -> os_data {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                *self
            }
        }
        pub type size_t = usize;
        pub type regoff_t = core::ffi::c_int;
        #[repr(C)]
        pub struct regmatch_t {
            pub rm_so: regoff_t,
            pub rm_eo: regoff_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for regmatch_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for regmatch_t {
            #[inline]
            fn clone(&self) -> regmatch_t {
                let _: ::core::clone::AssertParamIsClone<regoff_t>;
                *self
            }
        }
        pub type regex_t = re_pattern_buffer;
        #[repr(C)]
        pub struct re_pattern_buffer {
            pub __buffer: *mut re_dfa_t,
            pub __allocated: __re_long_size_t,
            pub __used: __re_long_size_t,
            pub __syntax: reg_syntax_t,
            pub __fastmap: *mut core::ffi::c_char,
            pub __translate: *mut core::ffi::c_uchar,
            pub re_nsub: size_t,
            pub __can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor:
                [u8; 1],
            pub c2rust_padding: [u8; 7],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for re_pattern_buffer {}
        #[automatically_derived]
        impl ::core::clone::Clone for re_pattern_buffer {
            #[inline]
            fn clone(&self) -> re_pattern_buffer {
                let _: ::core::clone::AssertParamIsClone<*mut re_dfa_t>;
                let _: ::core::clone::AssertParamIsClone<__re_long_size_t>;
                let _: ::core::clone::AssertParamIsClone<reg_syntax_t>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_uchar>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<[u8; 1]>;
                let _: ::core::clone::AssertParamIsClone<[u8; 7]>;
                *self
            }
        }
        #[automatically_derived]
        impl re_pattern_buffer {
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set___can_be_null(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field =
                    &mut self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (0usize, 0usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn __can_be_null(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field =
                    &self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (0usize, 0usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set___regs_allocated(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field =
                    &mut self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (1usize, 2usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn __regs_allocated(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field =
                    &self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (1usize, 2usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set___fastmap_accurate(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field =
                    &mut self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (3usize, 3usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn __fastmap_accurate(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field =
                    &self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (3usize, 3usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set___no_sub(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field =
                    &mut self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (4usize, 4usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn __no_sub(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field =
                    &self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (4usize, 4usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set___not_bol(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field =
                    &mut self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (5usize, 5usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn __not_bol(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field =
                    &self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (5usize, 5usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set___not_eol(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field =
                    &mut self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (6usize, 6usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn __not_eol(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field =
                    &self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (6usize, 6usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set___newline_anchor(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field =
                    &mut self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (7usize, 7usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn __newline_anchor(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field =
                    &self.__can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor;
                let (lhs_bit, rhs_bit) = (7usize, 7usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
        }
        pub type reg_syntax_t = core::ffi::c_ulong;
        pub type __re_long_size_t = core::ffi::c_ulong;
        pub type FILE = _IO_FILE;
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
        pub type __off64_t = core::ffi::c_long;
        pub type _IO_lock_t = ();
        pub type __off_t = core::ffi::c_long;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const REG_EXTENDED: core::ffi::c_int = 1 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn get_os_arch(
            os_header: *mut core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let ARCHS: [*const core::ffi::c_char; 13] = [
                b"x86_64\0" as *const u8 as *const core::ffi::c_char,
                b"i386\0" as *const u8 as *const core::ffi::c_char,
                b"i686\0" as *const u8 as *const core::ffi::c_char,
                b"sparc\0" as *const u8 as *const core::ffi::c_char,
                b"amd64\0" as *const u8 as *const core::ffi::c_char,
                b"i86pc\0" as *const u8 as *const core::ffi::c_char,
                b"ia64\0" as *const u8 as *const core::ffi::c_char,
                b"AIX\0" as *const u8 as *const core::ffi::c_char,
                b"armv6\0" as *const u8 as *const core::ffi::c_char,
                b"armv7\0" as *const u8 as *const core::ffi::c_char,
                b"aarch64\0" as *const u8 as *const core::ffi::c_char,
                b"arm64\0" as *const u8 as *const core::ffi::c_char,
                std::ptr::null::<core::ffi::c_char>(),
            ];
            let mut os_arch: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut i: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while !(ARCHS[i as usize]).is_null() {
                if !(strstr(os_header, ARCHS[i as usize])).is_null() {
                    os_arch = strdup(ARCHS[i as usize]);
                    break;
                } else {
                    i += 1;
                }
            }
            os_arch
        }
        #[no_mangle]
        pub unsafe extern "C" fn w_regexec(
            pattern: *const core::ffi::c_char,
            string: *const core::ffi::c_char,
            nmatch: size_t,
            pmatch: *mut regmatch_t,
        ) -> core::ffi::c_int {
            let mut regex: regex_t =
                regex_t {
                    __buffer: std::ptr::null_mut::<re_dfa_t>(),
                    __allocated: 0,
                    __used: 0,
                    __syntax: 0,
                    __fastmap: std::ptr::null_mut::<core::ffi::c_char>(),
                    __translate: std::ptr::null_mut::<core::ffi::c_uchar>(),
                    re_nsub: 0,
                    __can_be_null___regs_allocated___fastmap_accurate___no_sub___not_bol___not_eol___newline_anchor: [0;
                            1],
                    c2rust_padding: [0; 7],
                };
            let mut result: core::ffi::c_int = 0;
            if !(!pattern.is_null() && !string.is_null()) {
                return 0 as core::ffi::c_int;
            }
            if regcomp(&mut regex, pattern, REG_EXTENDED) != 0 {
                fprintf(
                    stderr,
                    b"Couldn't compile regular expression '%s'\n\0" as *const u8
                        as *const core::ffi::c_char,
                    pattern,
                );
                return 0 as core::ffi::c_int;
            }
            result = regexec(
                &mut regex,
                string,
                nmatch,
                pmatch as *mut regmatch_t,
                0 as core::ffi::c_int,
            );
            regfree(&mut regex);
            (result == 0) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn parse_uname_string(
            uname: *mut core::ffi::c_char,
            osd: *mut os_data,
        ) {
            let mut str_tmp: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut match_0: [regmatch_t; 2] = [
                {
                    regmatch_t {
                        rm_so: 0 as regoff_t,
                        rm_eo: 0,
                    }
                },
                regmatch_t { rm_so: 0, rm_eo: 0 },
            ];
            let mut match_size: core::ffi::c_int = 0 as core::ffi::c_int;
            if osd.is_null() {
                return;
            }
            str_tmp = strstr(uname, b" [Ver: \0" as *const u8 as *const core::ffi::c_char);
            if !str_tmp.is_null() {
                *str_tmp = '\0' as i32 as core::ffi::c_char;
                str_tmp = str_tmp.offset(7 as core::ffi::c_int as isize);
                (*osd).os_name = strdup(uname);
                *str_tmp
                    .add(strlen(str_tmp))
                    .offset(-(1 as core::ffi::c_int as isize)) = '\0' as i32 as core::ffi::c_char;
                if w_regexec(
                    b"^([0-9]+)\\.*\0" as *const u8 as *const core::ffi::c_char,
                    str_tmp,
                    2 as size_t,
                    match_0.as_mut_ptr(),
                ) != 0
                {
                    match_size = (match_0[1 as core::ffi::c_int as usize].rm_eo
                        - match_0[1 as core::ffi::c_int as usize].rm_so)
                        as core::ffi::c_int;
                    (*osd).os_major = malloc((match_size + 1 as core::ffi::c_int) as size_t)
                        as *mut core::ffi::c_char;
                    snprintf(
                        (*osd).os_major,
                        (match_size + 1 as core::ffi::c_int) as size_t,
                        b"%.*s\0" as *const u8 as *const core::ffi::c_char,
                        match_size,
                        str_tmp.offset(match_0[1 as core::ffi::c_int as usize].rm_so as isize),
                    );
                }
                if w_regexec(
                    b"^[0-9]+\\.([0-9]+)\\.*\0" as *const u8 as *const core::ffi::c_char,
                    str_tmp,
                    2 as size_t,
                    match_0.as_mut_ptr(),
                ) != 0
                {
                    match_size = (match_0[1 as core::ffi::c_int as usize].rm_eo
                        - match_0[1 as core::ffi::c_int as usize].rm_so)
                        as core::ffi::c_int;
                    (*osd).os_minor = malloc((match_size + 1 as core::ffi::c_int) as size_t)
                        as *mut core::ffi::c_char;
                    snprintf(
                        (*osd).os_minor,
                        (match_size + 1 as core::ffi::c_int) as size_t,
                        b"%.*s\0" as *const u8 as *const core::ffi::c_char,
                        match_size,
                        str_tmp.offset(match_0[1 as core::ffi::c_int as usize].rm_so as isize),
                    );
                }
                if w_regexec(
                    b"^[0-9]+\\.[0-9]+\\.([0-9]+(\\.[0-9]+)*)\\.*\0" as *const u8
                        as *const core::ffi::c_char,
                    str_tmp,
                    2 as size_t,
                    match_0.as_mut_ptr(),
                ) != 0
                {
                    match_size = (match_0[1 as core::ffi::c_int as usize].rm_eo
                        - match_0[1 as core::ffi::c_int as usize].rm_so)
                        as core::ffi::c_int;
                    (*osd).os_build = malloc((match_size + 1 as core::ffi::c_int) as size_t)
                        as *mut core::ffi::c_char;
                    snprintf(
                        (*osd).os_build,
                        (match_size + 1 as core::ffi::c_int) as size_t,
                        b"%.*s\0" as *const u8 as *const core::ffi::c_char,
                        match_size,
                        str_tmp.offset(match_0[1 as core::ffi::c_int as usize].rm_so as isize),
                    );
                }
                (*osd).os_version = strdup(str_tmp);
                (*osd).os_platform = strdup(b"windows\0" as *const u8 as *const core::ffi::c_char);
            } else {
                str_tmp = strstr(uname, b" [\0" as *const u8 as *const core::ffi::c_char);
                if !str_tmp.is_null() {
                    *str_tmp = '\0' as i32 as core::ffi::c_char;
                    str_tmp = str_tmp.offset(2 as core::ffi::c_int as isize);
                    (*osd).os_name = strdup(str_tmp);
                    str_tmp = strstr(
                        (*osd).os_name,
                        b": \0" as *const u8 as *const core::ffi::c_char,
                    );
                    if !str_tmp.is_null() {
                        *str_tmp = '\0' as i32 as core::ffi::c_char;
                        str_tmp = str_tmp.offset(2 as core::ffi::c_int as isize);
                        (*osd).os_version = strdup(str_tmp);
                        *((*osd).os_version)
                            .add(strlen((*osd).os_version))
                            .offset(-(1 as core::ffi::c_int as isize)) =
                            '\0' as i32 as core::ffi::c_char;
                        str_tmp = strstr(
                            (*osd).os_version,
                            b" (\0" as *const u8 as *const core::ffi::c_char,
                        );
                        if !str_tmp.is_null() {
                            *str_tmp = '\0' as i32 as core::ffi::c_char;
                            str_tmp = str_tmp.offset(2 as core::ffi::c_int as isize);
                            (*osd).os_codename = strdup(str_tmp);
                            *((*osd).os_codename)
                                .add(strlen((*osd).os_codename))
                                .offset(-(1 as core::ffi::c_int as isize)) =
                                '\0' as i32 as core::ffi::c_char;
                        }
                        if w_regexec(
                            b"^([0-9]+)\\.*\0" as *const u8 as *const core::ffi::c_char,
                            (*osd).os_version,
                            2 as size_t,
                            match_0.as_mut_ptr(),
                        ) != 0
                        {
                            match_size = (match_0[1 as core::ffi::c_int as usize].rm_eo
                                - match_0[1 as core::ffi::c_int as usize].rm_so)
                                as core::ffi::c_int;
                            (*osd).os_major = malloc((match_size + 1 as core::ffi::c_int) as size_t)
                                as *mut core::ffi::c_char;
                            snprintf(
                                (*osd).os_major,
                                (match_size + 1 as core::ffi::c_int) as size_t,
                                b"%.*s\0" as *const u8 as *const core::ffi::c_char,
                                match_size,
                                ((*osd).os_version)
                                    .offset(match_0[1 as core::ffi::c_int as usize].rm_so as isize),
                            );
                        }
                        if w_regexec(
                            b"^[0-9]+\\.([0-9]+)\\.*\0" as *const u8 as *const core::ffi::c_char,
                            (*osd).os_version,
                            2 as size_t,
                            match_0.as_mut_ptr(),
                        ) != 0
                        {
                            match_size = (match_0[1 as core::ffi::c_int as usize].rm_eo
                                - match_0[1 as core::ffi::c_int as usize].rm_so)
                                as core::ffi::c_int;
                            (*osd).os_minor = malloc((match_size + 1 as core::ffi::c_int) as size_t)
                                as *mut core::ffi::c_char;
                            snprintf(
                                (*osd).os_minor,
                                (match_size + 1 as core::ffi::c_int) as size_t,
                                b"%.*s\0" as *const u8 as *const core::ffi::c_char,
                                match_size,
                                ((*osd).os_version)
                                    .offset(match_0[1 as core::ffi::c_int as usize].rm_so as isize),
                            );
                        }
                    } else {
                        *((*osd).os_name)
                            .add(strlen((*osd).os_name))
                            .offset(-(1 as core::ffi::c_int as isize)) =
                            '\0' as i32 as core::ffi::c_char;
                    }
                    str_tmp = strstr(
                        (*osd).os_name,
                        b"|\0" as *const u8 as *const core::ffi::c_char,
                    );
                    if !str_tmp.is_null() {
                        *str_tmp = '\0' as i32 as core::ffi::c_char;
                        str_tmp = str_tmp.offset(1);
                        (*osd).os_platform = strdup(str_tmp);
                    }
                }
                str_tmp = get_os_arch(uname);
                if !str_tmp.is_null() {
                    (*osd).os_arch = strdup(str_tmp);
                    free(str_tmp as *mut core::ffi::c_void);
                }
            };
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("parse_uname_lib", SOURCE);
}
