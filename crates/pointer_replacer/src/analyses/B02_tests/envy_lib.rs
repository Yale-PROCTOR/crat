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
            fn snprintf(
                __s: *mut core::ffi::c_char,
                __maxlen: size_t,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
            fn getenv(__name: *const core::ffi::c_char) -> *mut core::ffi::c_char;
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
        }
        pub type size_t = usize;
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
        #[repr(C)]
        pub struct ConfigFlags {
            pub verbose_debug_optimize_cache_enabled_log_level_reserved: [u8; 1],
            pub c2rust_padding: [u8; 3],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ConfigFlags {}
        #[automatically_derived]
        impl ::core::clone::Clone for ConfigFlags {
            #[inline]
            fn clone(&self) -> ConfigFlags {
                let _: ::core::clone::AssertParamIsClone<[u8; 1]>;
                let _: ::core::clone::AssertParamIsClone<[u8; 3]>;
                *self
            }
        }
        #[automatically_derived]
        impl ConfigFlags {
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_verbose(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (0usize, 0usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn verbose(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (0usize, 0usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_debug(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (1usize, 1usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn debug(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (1usize, 1usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_optimize(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (2usize, 2usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn optimize(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (2usize, 2usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_cache_enabled(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (3usize, 3usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn cache_enabled(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (3usize, 3usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_log_level(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (4usize, 6usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn log_level(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (4usize, 6usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_reserved(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (7usize, 7usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn reserved(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.verbose_debug_optimize_cache_enabled_log_level_reserved;
                let (lhs_bit, rhs_bit) = (7usize, 7usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
        }
        #[repr(C)]
        pub struct ProcessState {
            pub flags: ConfigFlags,
            pub base_value: core::ffi::c_int,
            pub multiplier: core::ffi::c_int,
            pub operation: core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ProcessState {}
        #[automatically_derived]
        impl ::core::clone::Clone for ProcessState {
            #[inline]
            fn clone(&self) -> ProcessState {
                let _: ::core::clone::AssertParamIsClone<ConfigFlags>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const BUFFER_SIZE: core::ffi::c_int = 256 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn parse_env_numeric(
            env_name: *const core::ffi::c_char,
            default_val: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let env_value: *mut core::ffi::c_char = getenv(env_name);
            if env_value.is_null() {
                return default_val;
            }
            let mut invalid_char: *mut core::ffi::c_char = strchr(env_value, ',' as i32);
            if !invalid_char.is_null() {
                fprintf(
                    stderr,
                    b"Warning: Invalid character in %s\n\0" as *const u8
                        as *const core::ffi::c_char,
                    env_name,
                );
                return default_val;
            }
            invalid_char = strchr(env_value, ';' as i32);
            if !invalid_char.is_null() {
                fprintf(
                    stderr,
                    b"Warning: Semicolon found in %s\n\0" as *const u8 as *const core::ffi::c_char,
                    env_name,
                );
                return default_val;
            }
            atoi(env_value)
        }
        #[no_mangle]
        pub unsafe extern "C" fn init_config_from_env(flags: *mut ConfigFlags) {
            let verbose_env: *mut core::ffi::c_char =
                getenv(b"PROG_VERBOSE\0" as *const u8 as *const core::ffi::c_char);
            let debug_env: *mut core::ffi::c_char =
                getenv(b"PROG_DEBUG\0" as *const u8 as *const core::ffi::c_char);
            let optimize_env: *mut core::ffi::c_char =
                getenv(b"PROG_OPTIMIZE\0" as *const u8 as *const core::ffi::c_char);
            (*flags).set_verbose(
                (if !verbose_env.is_null() && !(strchr(verbose_env, '1' as i32)).is_null() {
                    1 as core::ffi::c_int
                } else {
                    0 as core::ffi::c_int
                }) as core::ffi::c_uint as core::ffi::c_uint,
            );
            (*flags).set_debug(
                (if !debug_env.is_null() && !(strchr(debug_env, '1' as i32)).is_null() {
                    1 as core::ffi::c_int
                } else {
                    0 as core::ffi::c_int
                }) as core::ffi::c_uint as core::ffi::c_uint,
            );
            (*flags).set_optimize(
                (if !optimize_env.is_null() {
                    1 as core::ffi::c_int
                } else {
                    0 as core::ffi::c_int
                }) as core::ffi::c_uint as core::ffi::c_uint,
            );
            (*flags).set_cache_enabled(1 as core::ffi::c_uint as core::ffi::c_uint);
            (*flags).set_log_level(0o3 as core::ffi::c_uint as core::ffi::c_uint);
            (*flags).set_reserved(0 as core::ffi::c_uint as core::ffi::c_uint);
        }
        #[no_mangle]
        pub unsafe extern "C" fn perform_operation(
            val1: core::ffi::c_int,
            val2: core::ffi::c_int,
            flags: *mut ConfigFlags,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let operation_mode: core::ffi::c_int = 0o755 as core::ffi::c_int;
            if (*flags).optimize() != 0 {
                result = val1 + val2;
            } else {
                result =
                    val1 * (*flags).log_level() as core::ffi::c_int + val2 / 2 as core::ffi::c_int;
            }
            if (*flags).debug() != 0 {
                printf(
                    b"Debug: operation_mode = %o (octal)\n\0" as *const u8
                        as *const core::ffi::c_char,
                    operation_mode,
                );
                printf(
                    b"Debug: result before adjustment = %d\n\0" as *const u8
                        as *const core::ffi::c_char,
                    result,
                );
            }
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn apply_bit_operations(
            mut value: core::ffi::c_int,
            flags: *mut ConfigFlags,
        ) -> core::ffi::c_int {
            if (*flags).verbose() != 0 {
                value <<= 1 as core::ffi::c_int;
            }
            if (*flags).cache_enabled() != 0 {
                value |= 0xf as core::ffi::c_int;
            }
            value
        }
        #[no_mangle]
        pub unsafe extern "C" fn envy(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut state: ProcessState = ProcessState {
                flags: ConfigFlags {
                    verbose_debug_optimize_cache_enabled_log_level_reserved: [0; 1],
                    c2rust_padding: [0; 3],
                },
                base_value: 0,
                multiplier: 0,
                operation: 0,
            };
            let mut state_backup: ProcessState = ProcessState {
                flags: ConfigFlags {
                    verbose_debug_optimize_cache_enabled_log_level_reserved: [0; 1],
                    c2rust_padding: [0; 3],
                },
                base_value: 0,
                multiplier: 0,
                operation: 0,
            };
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            init_config_from_env(&mut state.flags);
            let base_offset: core::ffi::c_int = parse_env_numeric(
                b"PROG_BASE_OFFSET\0" as *const u8 as *const core::ffi::c_char,
                0o100 as core::ffi::c_int,
            );
            let multiplier: core::ffi::c_int = parse_env_numeric(
                b"PROG_MULTIPLIER\0" as *const u8 as *const core::ffi::c_char,
                0o12 as core::ffi::c_int,
            );
            if (state.flags).verbose() != 0 {
                printf(b"Verbose mode enabled\n\0" as *const u8 as *const core::ffi::c_char);
                printf(
                    b"Base offset: %d (from octal 0100)\n\0" as *const u8
                        as *const core::ffi::c_char,
                    base_offset,
                );
                printf(
                    b"Multiplier: %d (from octal 012)\n\0" as *const u8 as *const core::ffi::c_char,
                    multiplier,
                );
            }
            state.base_value = param1;
            state.multiplier = multiplier;
            state.operation = '+' as i32 as core::ffi::c_char;
            memcpy(
                &mut state_backup as *mut ProcessState as *mut core::ffi::c_void,
                &mut state as *mut ProcessState as *const core::ffi::c_void,
                ::core::mem::size_of::<ProcessState>() as size_t,
            );
            if (state.flags).debug() != 0 {
                printf(
                    b"Debug: Created state backup using memcpy\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                printf(
                    b"Debug: Backup base_value = %d\n\0" as *const u8 as *const core::ffi::c_char,
                    state_backup.base_value,
                );
            }
            result = perform_operation(param1, param2, &mut state.flags);
            if param3 != 0 as core::ffi::c_int {
                result += param3 * state.multiplier;
            }
            if param4 != 0 as core::ffi::c_int {
                result += param4 >> 2 as core::ffi::c_int;
            }
            result = apply_bit_operations(result, &mut state.flags);
            result += base_offset;
            snprintf(
                buffer.as_mut_ptr(),
                BUFFER_SIZE as size_t,
                b"Result:%d:Complete\0" as *const u8 as *const core::ffi::c_char,
                result,
            );
            let colon_pos: *mut core::ffi::c_char = strchr(buffer.as_ptr(), ':' as i32);
            if !colon_pos.is_null() {
                if (state.flags).verbose() != 0 {
                    printf(
                        b"Found colon at position: %ld\n\0" as *const u8
                            as *const core::ffi::c_char,
                        colon_pos.offset_from(buffer.as_ptr()) as core::ffi::c_long,
                    );
                }
                let second_colon: *mut core::ffi::c_char =
                    strchr(colon_pos.offset(1 as core::ffi::c_int as isize), ':' as i32);
                if !second_colon.is_null() && (state.flags).debug() as core::ffi::c_int != 0 {
                    printf(
                        b"Debug: Result string format validated\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                }
            }
            if result < 0 as core::ffi::c_int {
                memcpy(
                    &mut state as *mut ProcessState as *mut core::ffi::c_void,
                    &mut state_backup as *mut ProcessState as *const core::ffi::c_void,
                    ::core::mem::size_of::<ProcessState>() as size_t,
                );
                result = state.base_value;
                if (state.flags).verbose() != 0 {
                    printf(
                        b"Restored state from backup\n\0" as *const u8 as *const core::ffi::c_char,
                    );
                }
            }
            if (state.flags).verbose() != 0 {
                printf(
                    b"Final result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                    result,
                );
                printf(
                    b"Configuration - Debug: %d, Optimize: %d, Log Level: %d\n\0" as *const u8
                        as *const core::ffi::c_char,
                    (state.flags).debug() as core::ffi::c_int,
                    (state.flags).optimize() as core::ffi::c_int,
                    (state.flags).log_level() as core::ffi::c_int,
                );
            }
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("envy_lib", SOURCE);
}
