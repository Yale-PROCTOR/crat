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
#[macro_use]
extern crate c2rust_bitfields;
pub mod src {
    pub mod lib {
        use ::c2rust_bitfields;
        extern "C" {
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn snprintf(
                __s: *mut core::ffi::c_char,
                __maxlen: size_t,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn memchr(
                __s: *const core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct PackedFlags {
            pub flag1_flag2_flag3_counter_mode_status_reserved: [u8; 4],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for PackedFlags {}
        #[automatically_derived]
        impl ::core::clone::Clone for PackedFlags {
            #[inline]
            fn clone(&self) -> PackedFlags {
                let _: ::core::clone::AssertParamIsClone<[u8; 4]>;
                *self
            }
        }
        #[automatically_derived]
        impl PackedFlags {
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_flag1(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (0usize, 0usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn flag1(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (0usize, 0usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_flag2(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (1usize, 1usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn flag2(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (1usize, 1usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_flag3(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (2usize, 2usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn flag3(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (2usize, 2usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_counter(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (3usize, 7usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn counter(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (3usize, 7usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_mode(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (8usize, 10usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn mode(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (8usize, 10usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_status(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (11usize, 15usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn status(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (11usize, 15usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
            #[doc = r" This method allows you to write to a bitfield with a value"]
            pub fn set_reserved(&mut self, int: core::ffi::c_uint) {
                use c2rust_bitfields::FieldType;
                let field = &mut self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (16usize, 31usize);
                int.set_field(field, (lhs_bit, rhs_bit));
            }
            #[doc = r" This method allows you to read from a bitfield to a value"]
            pub fn reserved(&self) -> core::ffi::c_uint {
                use c2rust_bitfields::FieldType;
                type IntType = core::ffi::c_uint;
                let field = &self.flag1_flag2_flag3_counter_mode_status_reserved;
                let (lhs_bit, rhs_bit) = (16usize, 31usize);
                <IntType as FieldType>::get_field(field, (lhs_bit, rhs_bit))
            }
        }
        #[repr(C)]
        pub union TypeConfusion {
            pub int_val: core::ffi::c_int,
            pub float_val: core::ffi::c_float,
            pub uint_val: core::ffi::c_uint,
            pub bytes: [core::ffi::c_char; 4],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for TypeConfusion {}
        #[automatically_derived]
        impl ::core::clone::Clone for TypeConfusion {
            #[inline]
            fn clone(&self) -> TypeConfusion {
                let _: ::core::clone::AssertParamIsCopy<Self>;
                *self
            }
        }
        #[repr(C)]
        pub struct ProcessState {
            pub flags: PackedFlags,
            pub data: TypeConfusion,
            pub buffer: *mut core::ffi::c_char,
            pub capacity: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for ProcessState {}
        #[automatically_derived]
        impl ::core::clone::Clone for ProcessState {
            #[inline]
            fn clone(&self) -> ProcessState {
                let _: ::core::clone::AssertParamIsClone<PackedFlags>;
                let _: ::core::clone::AssertParamIsClone<TypeConfusion>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn create_state(
            initial_val: core::ffi::c_int,
            capacity: core::ffi::c_int,
        ) -> *mut ProcessState {
            let state: *mut ProcessState =
                malloc(::core::mem::size_of::<ProcessState>() as size_t) as *mut ProcessState;
            if state.is_null() {
                printf(
                    b"Error: Failed to allocate memory for state\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<ProcessState>();
            }
            ((*state).flags).set_flag1(1 as core::ffi::c_uint as core::ffi::c_uint);
            ((*state).flags).set_flag2(0 as core::ffi::c_uint as core::ffi::c_uint);
            ((*state).flags).set_flag3(1 as core::ffi::c_uint as core::ffi::c_uint);
            ((*state).flags).set_counter(0 as core::ffi::c_uint as core::ffi::c_uint);
            ((*state).flags).set_mode(3 as core::ffi::c_uint as core::ffi::c_uint);
            ((*state).flags).set_status(15 as core::ffi::c_uint as core::ffi::c_uint);
            ((*state).flags).set_reserved(0 as core::ffi::c_uint as core::ffi::c_uint);
            (*state).data.int_val = initial_val;
            (*state).capacity = capacity;
            (*state).buffer = malloc(capacity as size_t) as *mut core::ffi::c_char;
            if ((*state).buffer).is_null() {
                printf(
                    b"Error: Failed to allocate buffer\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                free(state as *mut core::ffi::c_void);
                return std::ptr::null_mut::<ProcessState>();
            }
            snprintf(
                (*state).buffer,
                capacity as size_t,
                b"State:%d:Mode:%d\0" as *const u8 as *const core::ffi::c_char,
                initial_val,
                ((*state).flags).mode() as core::ffi::c_int,
            );
            state
        }
        #[no_mangle]
        pub unsafe extern "C" fn destroy_state(state: *mut ProcessState) {
            if !state.is_null() {
                if !((*state).buffer).is_null() {
                    free((*state).buffer as *mut core::ffi::c_void);
                }
                free(state as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_buffer(
            state: *mut ProcessState,
            target: core::ffi::c_char,
        ) -> core::ffi::c_int {
            if state.is_null() || ((*state).buffer).is_null() {
                printf(
                    b"Error: Null pointer in process_buffer\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut ptr: *mut core::ffi::c_char = (*state).buffer;
            let mut remaining: size_t = strlen((*state).buffer);
            while remaining > 0 as size_t {
                let found: *mut core::ffi::c_char = memchr(
                    ptr as *const core::ffi::c_void,
                    target as core::ffi::c_int,
                    remaining,
                ) as *mut core::ffi::c_char;
                if found.is_null() {
                    break;
                }
                count += 1;
                printf(
                    b"Operation: memchr_found with value %d\n\0" as *const u8
                        as *const core::ffi::c_char,
                    count,
                );
                remaining = (remaining as core::ffi::c_ulong).wrapping_sub(
                    (found.offset_from(ptr) as core::ffi::c_long + 1 as core::ffi::c_long)
                        as core::ffi::c_ulong,
                ) as size_t as size_t;
                ptr = found.offset(1 as core::ffi::c_int as isize);
            }
            count
        }
        #[no_mangle]
        pub unsafe extern "C" fn update_flags(state: *mut ProcessState, param: core::ffi::c_int) {
            if state.is_null() {
                return;
            }
            {
                let __arg_0 = ((((*state).flags).counter() as core::ffi::c_int
                    + 1 as core::ffi::c_int)
                    & 0x1f as core::ffi::c_int) as core::ffi::c_uint
                    as core::ffi::c_uint;
                ((*state).flags).set_counter(__arg_0)
            };
            ((*state).flags).set_flag1(
                (param & 1 as core::ffi::c_int) as core::ffi::c_uint as core::ffi::c_uint,
            );
            ((*state).flags).set_flag2(
                ((param & 2 as core::ffi::c_int) >> 1 as core::ffi::c_int) as core::ffi::c_uint
                    as core::ffi::c_uint,
            );
            ((*state).flags).set_flag3(
                ((param & 4 as core::ffi::c_int) >> 2 as core::ffi::c_int) as core::ffi::c_uint
                    as core::ffi::c_uint,
            );
            ((*state).flags).set_mode(
                (param >> 3 as core::ffi::c_int & 0x7 as core::ffi::c_int) as core::ffi::c_uint
                    as core::ffi::c_uint,
            );
            printf(
                b"Debug: state->flags.counter = %d\n\0" as *const u8 as *const core::ffi::c_char,
                ((*state).flags).counter() as core::ffi::c_int,
            );
            printf(
                b"Bit fields - flag1:%d flag2:%d flag3:%d mode:%d\n\0" as *const u8
                    as *const core::ffi::c_char,
                ((*state).flags).flag1() as core::ffi::c_int,
                ((*state).flags).flag2() as core::ffi::c_int,
                ((*state).flags).flag3() as core::ffi::c_int,
                ((*state).flags).mode() as core::ffi::c_int,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn confuse_types(
            state: *mut ProcessState,
            operation: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if state.is_null() {
                return 0 as core::ffi::c_int;
            }
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            match operation {
                0 => {
                    (*state).data.int_val = 1078530011 as core::ffi::c_int;
                    printf(
                        b"Set as int: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        (*state).data.int_val,
                    );
                }
                1 => {
                    printf(
                        b"Read as float: %f\n\0" as *const u8 as *const core::ffi::c_char,
                        (*state).data.float_val as core::ffi::c_double,
                    );
                    result = ((*state).data.float_val
                        * 100 as core::ffi::c_int as core::ffi::c_float)
                        as core::ffi::c_int;
                }
                2 => {
                    printf(
                        b"Read as uint: %u\n\0" as *const u8 as *const core::ffi::c_char,
                        (*state).data.uint_val,
                    );
                    result =
                        ((*state).data.uint_val & 0xff as core::ffi::c_uint) as core::ffi::c_int;
                }
                3 => {
                    printf(
                        b"Read as bytes: [%d, %d, %d, %d]\n\0" as *const u8
                            as *const core::ffi::c_char,
                        (*state).data.bytes[0 as core::ffi::c_int as usize] as core::ffi::c_int,
                        (*state).data.bytes[1 as core::ffi::c_int as usize] as core::ffi::c_int,
                        (*state).data.bytes[2 as core::ffi::c_int as usize] as core::ffi::c_int,
                        (*state).data.bytes[3 as core::ffi::c_int as usize] as core::ffi::c_int,
                    );
                    result = (*state).data.bytes[0 as core::ffi::c_int as usize]
                        as core::ffi::c_int
                        + (*state).data.bytes[1 as core::ffi::c_int as usize] as core::ffi::c_int;
                }
                _ => {}
            }
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn confusion(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            printf(
                b"Debug: param1 = %d\n\0" as *const u8 as *const core::ffi::c_char,
                param1,
            );
            printf(
                b"Debug: param2 = %d\n\0" as *const u8 as *const core::ffi::c_char,
                param2,
            );
            printf(
                b"Debug: param3 = %d\n\0" as *const u8 as *const core::ffi::c_char,
                param3,
            );
            printf(
                b"Debug: param4 = %d\n\0" as *const u8 as *const core::ffi::c_char,
                param4,
            );
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let state: *mut ProcessState = create_state(param1, 128 as core::ffi::c_int);
            if state.is_null() {
                return -(1 as core::ffi::c_int);
            }
            update_flags(state, param2);
            let search_char: core::ffi::c_char =
                ('0' as i32 + param3 % 10 as core::ffi::c_int) as core::ffi::c_char;
            let found_count: core::ffi::c_int = process_buffer(state, search_char);
            result += found_count * 10 as core::ffi::c_int;
            let confusion_result: core::ffi::c_int =
                confuse_types(state, param4 % 4 as core::ffi::c_int);
            result += confusion_result;
            result += ((*state).flags).counter() as core::ffi::c_int * 5 as core::ffi::c_int;
            result += ((*state).flags).mode() as core::ffi::c_int * 3 as core::ffi::c_int;
            printf(
                b"Final result: %d\n\0" as *const u8 as *const core::ffi::c_char,
                result,
            );
            destroy_state(state);
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("confusion_lib", SOURCE, &["create_state#state"], &[]);
}
