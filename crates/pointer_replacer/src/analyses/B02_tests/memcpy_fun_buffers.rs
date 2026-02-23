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
    pub mod main {
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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
        }
        pub type size_t = usize;
        pub type __uint8_t = u8;
        pub type __uint32_t = u32;
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
        pub type uint8_t = __uint8_t;
        pub type uint32_t = __uint32_t;
        #[repr(C)]
        pub struct buffer_t {
            pub data: [uint8_t; 256],
            pub length: size_t,
            pub checksum: uint32_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for buffer_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for buffer_t {
            #[inline]
            fn clone(&self) -> buffer_t {
                let _: ::core::clone::AssertParamIsClone<[uint8_t; 256]>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<uint32_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct buffer_array_t {
            pub buffers: *mut buffer_t,
            pub count: core::ffi::c_int,
            pub capacity: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for buffer_array_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for buffer_array_t {
            #[inline]
            fn clone(&self) -> buffer_array_t {
                let _: ::core::clone::AssertParamIsClone<*mut buffer_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub type operation_t = core::ffi::c_uint;
        pub const OP_CHECKSUM: operation_t = 6;
        pub const OP_ROTATE: operation_t = 5;
        pub const OP_INTERLEAVE: operation_t = 4;
        pub const OP_SPLIT: operation_t = 3;
        pub const OP_MERGE: operation_t = 2;
        pub const OP_REVERSE: operation_t = 1;
        pub const OP_COPY: operation_t = 0;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const true_0: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const false_0: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn calculate_checksum(
            data: *const uint8_t,
            length: size_t,
        ) -> uint32_t {
            let mut sum: uint32_t = 0 as uint32_t;
            let mut i: size_t = 0 as size_t;
            while i < length {
                sum = sum << 3 as core::ffi::c_int ^ *data.add(i) as uint32_t;
                i = i.wrapping_add(1);
            }
            sum
        }
        #[no_mangle]
        pub unsafe extern "C" fn validate_buffer(buf: *const buffer_t) -> bool {
            if buf.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL buffer\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return false_0 != 0;
            }
            if (*buf).length > 256 as size_t {
                fprintf(
                    stderr,
                    b"Error: Buffer length %zu exceeds maximum 256\n\0" as *const u8
                        as *const core::ffi::c_char,
                    (*buf).length,
                );
                return false_0 != 0;
            }
            let expected: uint32_t = calculate_checksum(((*buf).data).as_ptr(), (*buf).length);
            if (*buf).checksum != expected {
                fprintf(
                    stderr,
                    b"Warning: Checksum mismatch. Expected %u, got %u\n\0" as *const u8
                        as *const core::ffi::c_char,
                    expected,
                    (*buf).checksum,
                );
            }
            true_0 != 0
        }
        #[no_mangle]
        pub unsafe extern "C" fn init_buffer_array(
            initial_capacity: core::ffi::c_int,
        ) -> *mut buffer_array_t {
            if initial_capacity <= 0 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Error: Invalid capacity %d\n\0" as *const u8 as *const core::ffi::c_char,
                    initial_capacity,
                );
                return std::ptr::null_mut::<buffer_array_t>();
            }
            let arr: *mut buffer_array_t =
                malloc(::core::mem::size_of::<buffer_array_t>() as size_t) as *mut buffer_array_t;
            if arr.is_null() {
                fprintf(
                    stderr,
                    b"Error: Failed to allocate buffer array\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<buffer_array_t>();
            }
            (*arr).buffers = malloc(
                (::core::mem::size_of::<buffer_t>() as size_t)
                    .wrapping_mul(initial_capacity as size_t),
            ) as *mut buffer_t;
            if ((*arr).buffers).is_null() {
                fprintf(
                    stderr,
                    b"Error: Failed to allocate buffer storage\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                free(arr as *mut core::ffi::c_void);
                return std::ptr::null_mut::<buffer_array_t>();
            }
            (*arr).count = 0 as core::ffi::c_int;
            (*arr).capacity = initial_capacity;
            arr
        }
        #[no_mangle]
        pub unsafe extern "C" fn free_buffer_array(arr: *mut buffer_array_t) {
            if !arr.is_null() {
                free((*arr).buffers as *mut core::ffi::c_void);
                free(arr as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_copy(
            src: *const buffer_t,
            dst: *mut buffer_t,
        ) -> core::ffi::c_int {
            if src.is_null() || dst.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL pointer in buffer_copy\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if !validate_buffer(src) {
                return -(1 as core::ffi::c_int);
            }
            memcpy(
                ((*dst).data).as_mut_ptr() as *mut core::ffi::c_void,
                ((*src).data).as_ptr() as *const core::ffi::c_void,
                (*src).length,
            );
            (*dst).length = (*src).length;
            (*dst).checksum = calculate_checksum(((*dst).data).as_ptr(), (*dst).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_reverse(buf: *mut buffer_t) -> core::ffi::c_int {
            if buf.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL buffer in reverse\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if (*buf).length == 0 as size_t {
                return 0 as core::ffi::c_int;
            }
            let mut temp: [uint8_t; 256] = [0; 256];
            memcpy(
                temp.as_mut_ptr() as *mut core::ffi::c_void,
                ((*buf).data).as_mut_ptr() as *const core::ffi::c_void,
                (*buf).length,
            );
            let mut i: size_t = 0 as size_t;
            while i < (*buf).length {
                (*buf).data[i as usize] =
                    temp[((*buf).length).wrapping_sub(1 as size_t).wrapping_sub(i) as usize];
                i = i.wrapping_add(1);
            }
            (*buf).checksum = calculate_checksum(((*buf).data).as_ptr(), (*buf).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_merge(
            src1: *const buffer_t,
            src2: *const buffer_t,
            dst: *mut buffer_t,
        ) -> core::ffi::c_int {
            if src1.is_null() || src2.is_null() || dst.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL pointer in buffer_merge\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if ((*src1).length).wrapping_add((*src2).length) > 256 as size_t {
                fprintf(
                    stderr,
                    b"Error: Merged length %zu exceeds maximum\n\0" as *const u8
                        as *const core::ffi::c_char,
                    ((*src1).length).wrapping_add((*src2).length),
                );
                return -(1 as core::ffi::c_int);
            }
            memcpy(
                ((*dst).data).as_mut_ptr() as *mut core::ffi::c_void,
                ((*src1).data).as_ptr() as *const core::ffi::c_void,
                (*src1).length,
            );
            memcpy(
                ((*dst).data).as_mut_ptr().add((*src1).length) as *mut core::ffi::c_void,
                ((*src2).data).as_ptr() as *const core::ffi::c_void,
                (*src2).length,
            );
            (*dst).length = ((*src1).length).wrapping_add((*src2).length);
            (*dst).checksum = calculate_checksum(((*dst).data).as_ptr(), (*dst).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_split(
            src: *const buffer_t,
            split_pos: size_t,
            dst1: *mut buffer_t,
            dst2: *mut buffer_t,
        ) -> core::ffi::c_int {
            if src.is_null() || dst1.is_null() || dst2.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL pointer in buffer_split\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if split_pos > (*src).length {
                fprintf(
                    stderr,
                    b"Error: Split position %zu exceeds length %zu\n\0" as *const u8
                        as *const core::ffi::c_char,
                    split_pos,
                    (*src).length,
                );
                return -(1 as core::ffi::c_int);
            }
            if split_pos > 0 as size_t {
                memcpy(
                    ((*dst1).data).as_mut_ptr() as *mut core::ffi::c_void,
                    ((*src).data).as_ptr() as *const core::ffi::c_void,
                    split_pos,
                );
            }
            (*dst1).length = split_pos;
            (*dst1).checksum = calculate_checksum(((*dst1).data).as_ptr(), (*dst1).length);
            let remaining: size_t = ((*src).length).wrapping_sub(split_pos);
            if remaining > 0 as size_t {
                memcpy(
                    ((*dst2).data).as_mut_ptr() as *mut core::ffi::c_void,
                    ((*src).data).as_ptr().add(split_pos) as *const core::ffi::c_void,
                    remaining,
                );
            }
            (*dst2).length = remaining;
            (*dst2).checksum = calculate_checksum(((*dst2).data).as_ptr(), (*dst2).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_interleave(
            src1: *const buffer_t,
            src2: *const buffer_t,
            dst: *mut buffer_t,
        ) -> core::ffi::c_int {
            if src1.is_null() || src2.is_null() || dst.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL pointer in buffer_interleave\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            let max_len: size_t = if (*src1).length > (*src2).length {
                (*src1).length
            } else {
                (*src2).length
            };
            if ((*src1).length).wrapping_add((*src2).length) > 256 as size_t {
                fprintf(
                    stderr,
                    b"Error: Interleaved length exceeds maximum\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            let mut dst_pos: size_t = 0 as size_t;
            let mut i: size_t = 0 as size_t;
            while i < max_len {
                if i < (*src1).length {
                    let fresh0 = dst_pos;
                    dst_pos = dst_pos.wrapping_add(1);
                    memcpy(
                        &mut *((*dst).data).as_mut_ptr().add(fresh0) as *mut uint8_t
                            as *mut core::ffi::c_void,
                        &*((*src1).data).as_ptr().add(i) as *const uint8_t
                            as *const core::ffi::c_void,
                        1 as size_t,
                    );
                }
                if i < (*src2).length {
                    let fresh1 = dst_pos;
                    dst_pos = dst_pos.wrapping_add(1);
                    memcpy(
                        &mut *((*dst).data).as_mut_ptr().add(fresh1) as *mut uint8_t
                            as *mut core::ffi::c_void,
                        &*((*src2).data).as_ptr().add(i) as *const uint8_t
                            as *const core::ffi::c_void,
                        1 as size_t,
                    );
                }
                i = i.wrapping_add(1);
            }
            (*dst).length = dst_pos;
            (*dst).checksum = calculate_checksum(((*dst).data).as_ptr(), (*dst).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_rotate(
            buf: *mut buffer_t,
            mut positions: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if buf.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL buffer in rotate\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if (*buf).length == 0 as size_t || positions == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            positions %= (*buf).length as core::ffi::c_int;
            if positions < 0 as core::ffi::c_int {
                positions = (positions as core::ffi::c_ulong)
                    .wrapping_add((*buf).length as core::ffi::c_ulong)
                    as core::ffi::c_int as core::ffi::c_int;
            }
            let mut temp: [uint8_t; 256] = [0; 256];
            memcpy(
                temp.as_mut_ptr() as *mut core::ffi::c_void,
                ((*buf).data).as_mut_ptr() as *const core::ffi::c_void,
                (*buf).length,
            );
            memcpy(
                ((*buf).data).as_mut_ptr() as *mut core::ffi::c_void,
                temp.as_mut_ptr().offset(positions as isize) as *const core::ffi::c_void,
                ((*buf).length).wrapping_sub(positions as size_t),
            );
            memcpy(
                ((*buf).data)
                    .as_mut_ptr()
                    .add(((*buf).length).wrapping_sub(positions as size_t))
                    as *mut core::ffi::c_void,
                temp.as_mut_ptr() as *const core::ffi::c_void,
                positions as size_t,
            );
            (*buf).checksum = calculate_checksum(((*buf).data).as_ptr(), (*buf).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_conditional_copy(
            src: *const buffer_t,
            dst: *mut buffer_t,
            pattern: uint8_t,
            copy_matching: bool,
        ) -> core::ffi::c_int {
            if src.is_null() || dst.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL pointer in conditional_copy\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            let mut dst_pos: size_t = 0 as size_t;
            let mut i: size_t = 0 as size_t;
            while i < (*src).length {
                let matches: bool =
                    (*src).data[i as usize] as core::ffi::c_int == pattern as core::ffi::c_int;
                if matches as core::ffi::c_int == copy_matching as core::ffi::c_int {
                    let fresh2 = dst_pos;
                    dst_pos = dst_pos.wrapping_add(1);
                    memcpy(
                        &mut *((*dst).data).as_mut_ptr().add(fresh2) as *mut uint8_t
                            as *mut core::ffi::c_void,
                        &*((*src).data).as_ptr().add(i) as *const uint8_t
                            as *const core::ffi::c_void,
                        1 as size_t,
                    );
                }
                i = i.wrapping_add(1);
            }
            (*dst).length = dst_pos;
            (*dst).checksum = calculate_checksum(((*dst).data).as_ptr(), (*dst).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn buffer_copy_strided(
            src: *const buffer_t,
            dst: *mut buffer_t,
            stride: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if src.is_null() || dst.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL pointer in copy_strided\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if stride <= 0 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Error: Invalid stride %d\n\0" as *const u8 as *const core::ffi::c_char,
                    stride,
                );
                return -(1 as core::ffi::c_int);
            }
            let mut dst_pos: size_t = 0 as size_t;
            let mut i: size_t = 0 as size_t;
            while i < (*src).length {
                let fresh3 = dst_pos;
                dst_pos = dst_pos.wrapping_add(1);
                memcpy(
                    &mut *((*dst).data).as_mut_ptr().add(fresh3) as *mut uint8_t
                        as *mut core::ffi::c_void,
                    &*((*src).data).as_ptr().add(i) as *const uint8_t as *const core::ffi::c_void,
                    1 as size_t,
                );
                i = (i as core::ffi::c_ulong).wrapping_add(stride as core::ffi::c_ulong) as size_t
                    as size_t;
            }
            (*dst).length = dst_pos;
            (*dst).checksum = calculate_checksum(((*dst).data).as_ptr(), (*dst).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_buffer_array(
            arr: *mut buffer_array_t,
            op: operation_t,
            param: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if arr.is_null() || (*arr).count == 0 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Error: Invalid buffer array\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            match op as core::ffi::c_uint {
                0 => {
                    let mut i: core::ffi::c_int = 1 as core::ffi::c_int;
                    while i < (*arr).count {
                        if buffer_copy(
                            &mut *((*arr).buffers).offset(0 as core::ffi::c_int as isize),
                            &mut *((*arr).buffers).offset(i as isize),
                        ) != 0 as core::ffi::c_int
                        {
                            return -(1 as core::ffi::c_int);
                        }
                        i += 1;
                    }
                }
                1 => {
                    let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i_0 < (*arr).count {
                        if buffer_reverse(&mut *((*arr).buffers).offset(i_0 as isize))
                            != 0 as core::ffi::c_int
                        {
                            return -(1 as core::ffi::c_int);
                        }
                        i_0 += 1;
                    }
                }
                2 => {
                    if (*arr).count < 2 as core::ffi::c_int {
                        fprintf(
                            stderr,
                            b"Error: Need at least 2 buffers for merge\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        return -(1 as core::ffi::c_int);
                    }
                    let mut i_1: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i_1 < (*arr).count - 1 as core::ffi::c_int {
                        let mut merged: buffer_t = buffer_t {
                            data: [0; 256],
                            length: 0,
                            checksum: 0,
                        };
                        if buffer_merge(
                            &mut *((*arr).buffers).offset(i_1 as isize),
                            &mut *((*arr).buffers).offset((i_1 + 1 as core::ffi::c_int) as isize),
                            &mut merged,
                        ) != 0 as core::ffi::c_int
                        {
                            return -(1 as core::ffi::c_int);
                        }
                        memcpy(
                            &mut *((*arr).buffers).offset(i_1 as isize) as *mut buffer_t
                                as *mut core::ffi::c_void,
                            &mut merged as *mut buffer_t as *const core::ffi::c_void,
                            ::core::mem::size_of::<buffer_t>() as size_t,
                        );
                        i_1 += 2 as core::ffi::c_int;
                    }
                }
                5 => {
                    let mut i_2: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i_2 < (*arr).count {
                        if buffer_rotate(&mut *((*arr).buffers).offset(i_2 as isize), param)
                            != 0 as core::ffi::c_int
                        {
                            return -(1 as core::ffi::c_int);
                        }
                        i_2 += 1;
                    }
                }
                6 => {
                    let mut i_3: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i_3 < (*arr).count {
                        if !validate_buffer(&mut *((*arr).buffers).offset(i_3 as isize)) {
                            return -(1 as core::ffi::c_int);
                        }
                        i_3 += 1;
                    }
                }
                _ => {
                    fprintf(
                        stderr,
                        b"Error: Unknown operation %d\n\0" as *const u8 as *const core::ffi::c_char,
                        op as core::ffi::c_uint,
                    );
                    return -(1 as core::ffi::c_int);
                }
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn read_buffer(buf: *mut buffer_t) -> core::ffi::c_int {
            if buf.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL buffer in read_buffer\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            let mut length: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut length as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error: Failed to read buffer length\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if length < 0 as core::ffi::c_int || length > 256 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Error: Invalid buffer length %d\n\0" as *const u8 as *const core::ffi::c_char,
                    length,
                );
                return -(1 as core::ffi::c_int);
            }
            (*buf).length = length as size_t;
            let mut i: size_t = 0 as size_t;
            while i < (*buf).length {
                let mut byte: core::ffi::c_int = 0;
                if scanf(
                    b"%d\0" as *const u8 as *const core::ffi::c_char,
                    &mut byte as *mut core::ffi::c_int,
                ) != 1 as core::ffi::c_int
                {
                    fprintf(
                        stderr,
                        b"Error: Failed to read byte %zu\n\0" as *const u8
                            as *const core::ffi::c_char,
                        i,
                    );
                    return -(1 as core::ffi::c_int);
                }
                (*buf).data[i as usize] = byte as uint8_t;
                i = i.wrapping_add(1);
            }
            (*buf).checksum = calculate_checksum(((*buf).data).as_ptr(), (*buf).length);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn write_buffer(buf: *const buffer_t) {
            if buf.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL buffer in write_buffer\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            printf(
                b"%zu\0" as *const u8 as *const core::ffi::c_char,
                (*buf).length,
            );
            let mut i: size_t = 0 as size_t;
            while i < (*buf).length {
                printf(
                    b" %u\0" as *const u8 as *const core::ffi::c_char,
                    (*buf).data[i as usize] as core::ffi::c_int,
                );
                i = i.wrapping_add(1);
            }
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
        }
        unsafe fn main_0(
            argc: core::ffi::c_int,
            argv: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            let mut operation: core::ffi::c_int = 0;
            let mut buffer_count: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut operation as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error: Failed to read operation\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut buffer_count as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error: Failed to read buffer count\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if buffer_count <= 0 as core::ffi::c_int || buffer_count > 100 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Error: Invalid buffer count %d\n\0" as *const u8 as *const core::ffi::c_char,
                    buffer_count,
                );
                return 1 as core::ffi::c_int;
            }
            let buffers: *mut buffer_array_t = init_buffer_array(buffer_count);
            if buffers.is_null() {
                return 1 as core::ffi::c_int;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < buffer_count {
                if read_buffer(&mut *((*buffers).buffers).offset(i as isize))
                    != 0 as core::ffi::c_int
                {
                    free_buffer_array(buffers);
                    return 1 as core::ffi::c_int;
                }
                (*buffers).count += 1;
                i += 1;
            }
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            match operation {
                0 => {
                    if buffer_count >= 2 as core::ffi::c_int {
                        let mut temp: buffer_t = buffer_t {
                            data: [0; 256],
                            length: 0,
                            checksum: 0,
                        };
                        result = buffer_copy(
                            &mut *((*buffers).buffers).offset(0 as core::ffi::c_int as isize),
                            &mut temp,
                        );
                        if result == 0 as core::ffi::c_int {
                            write_buffer(&mut temp);
                        }
                    } else {
                        fprintf(
                            stderr,
                            b"Error: Copy needs at least 2 buffers\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result = -(1 as core::ffi::c_int);
                    }
                }
                1 => {
                    let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i_0 < buffer_count {
                        result = buffer_reverse(&mut *((*buffers).buffers).offset(i_0 as isize));
                        if result != 0 as core::ffi::c_int {
                            break;
                        }
                        write_buffer(&mut *((*buffers).buffers).offset(i_0 as isize));
                        i_0 += 1;
                    }
                }
                2 => {
                    if buffer_count >= 2 as core::ffi::c_int {
                        let mut merged: buffer_t = buffer_t {
                            data: [0; 256],
                            length: 0,
                            checksum: 0,
                        };
                        result = buffer_merge(
                            &mut *((*buffers).buffers).offset(0 as core::ffi::c_int as isize),
                            &mut *((*buffers).buffers).offset(1 as core::ffi::c_int as isize),
                            &mut merged,
                        );
                        if result == 0 as core::ffi::c_int {
                            write_buffer(&mut merged);
                        }
                    } else {
                        fprintf(
                            stderr,
                            b"Error: Merge needs at least 2 buffers\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result = -(1 as core::ffi::c_int);
                    }
                }
                3 => {
                    if buffer_count >= 1 as core::ffi::c_int {
                        let mut split_pos: core::ffi::c_int = 0;
                        if scanf(
                            b"%d\0" as *const u8 as *const core::ffi::c_char,
                            &mut split_pos as *mut core::ffi::c_int,
                        ) != 1 as core::ffi::c_int
                        {
                            fprintf(
                                stderr,
                                b"Error: Failed to read split position\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            result = -(1 as core::ffi::c_int);
                        } else {
                            let mut part1: buffer_t = buffer_t {
                                data: [0; 256],
                                length: 0,
                                checksum: 0,
                            };
                            let mut part2: buffer_t = buffer_t {
                                data: [0; 256],
                                length: 0,
                                checksum: 0,
                            };
                            result = buffer_split(
                                &mut *((*buffers).buffers).offset(0 as core::ffi::c_int as isize),
                                split_pos as size_t,
                                &mut part1,
                                &mut part2,
                            );
                            if result == 0 as core::ffi::c_int {
                                write_buffer(&mut part1);
                                write_buffer(&mut part2);
                            }
                        }
                    }
                }
                4 => {
                    if buffer_count >= 2 as core::ffi::c_int {
                        let mut interleaved: buffer_t = buffer_t {
                            data: [0; 256],
                            length: 0,
                            checksum: 0,
                        };
                        result = buffer_interleave(
                            &mut *((*buffers).buffers).offset(0 as core::ffi::c_int as isize),
                            &mut *((*buffers).buffers).offset(1 as core::ffi::c_int as isize),
                            &mut interleaved,
                        );
                        if result == 0 as core::ffi::c_int {
                            write_buffer(&mut interleaved);
                        }
                    } else {
                        fprintf(
                            stderr,
                            b"Error: Interleave needs at least 2 buffers\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result = -(1 as core::ffi::c_int);
                    }
                }
                5 => {
                    let mut positions: core::ffi::c_int = 0;
                    if scanf(
                        b"%d\0" as *const u8 as *const core::ffi::c_char,
                        &mut positions as *mut core::ffi::c_int,
                    ) != 1 as core::ffi::c_int
                    {
                        fprintf(
                            stderr,
                            b"Error: Failed to read rotation amount\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        result = -(1 as core::ffi::c_int);
                    } else {
                        let mut i_1: core::ffi::c_int = 0 as core::ffi::c_int;
                        while i_1 < buffer_count {
                            result = buffer_rotate(
                                &mut *((*buffers).buffers).offset(i_1 as isize),
                                positions,
                            );
                            if result != 0 as core::ffi::c_int {
                                break;
                            }
                            write_buffer(&mut *((*buffers).buffers).offset(i_1 as isize));
                            i_1 += 1;
                        }
                    }
                }
                6 => {
                    let mut i_2: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i_2 < buffer_count {
                        printf(
                            b"%u\n\0" as *const u8 as *const core::ffi::c_char,
                            (*((*buffers).buffers).offset(i_2 as isize)).checksum,
                        );
                        i_2 += 1;
                    }
                }
                _ => {
                    fprintf(
                        stderr,
                        b"Error: Unknown operation %d\n\0" as *const u8 as *const core::ffi::c_char,
                        operation,
                    );
                    result = -(1 as core::ffi::c_int);
                }
            }
            free_buffer_array(buffers);
            if result != 0 as core::ffi::c_int {
                1 as core::ffi::c_int
            } else {
                0 as core::ffi::c_int
            }
        }
        pub fn main() {
            let mut args: Vec<*mut core::ffi::c_char> = Vec::new();
            for arg in ::std::env::args() {
                args.push(
                    (::std::ffi::CString::new(arg))
                        .expect("Failed to convert argument into CString.")
                        .into_raw(),
                );
            }
            args.push(::core::ptr::null_mut());
            unsafe {
                ::std::process::exit(main_0(
                    (args.len() - 1) as core::ffi::c_int,
                    args.as_mut_ptr() as *mut *mut core::ffi::c_char,
                ) as i32)
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates(
        "memcpy-fun-buffers",
        SOURCE,
        &["init_buffer_array#arr"],
        &[],
    );
}
