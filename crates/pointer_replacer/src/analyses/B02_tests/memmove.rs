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
            fn memmove(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
        }
        pub type size_t = usize;
        pub type __uint8_t = u8;
        pub type __uint32_t = u32;
        pub type uint8_t = __uint8_t;
        pub type uint32_t = __uint32_t;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn process_buffer(
            buffer: *mut uint8_t,
            length: size_t,
            flags: uint32_t,
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
        ) -> size_t {
            let mut new_len: size_t = length;
            if buffer.is_null() || length == 0 as size_t {
                return 0 as size_t;
            }
            if flags & 0x1 as uint32_t != 0 {
                let offset: core::ffi::c_int = param1 % length as core::ffi::c_int;
                if offset != 0 as core::ffi::c_int {
                    rotate_buffer(buffer, length, offset);
                }
            }
            if flags & 0x2 as uint32_t != 0 {
                let threshold: uint8_t =
                    (if param1 > 0 as core::ffi::c_int && param1 <= 255 as core::ffi::c_int {
                        param1 as uint8_t as core::ffi::c_int
                    } else {
                        3 as core::ffi::c_int
                    }) as uint8_t;
                new_len = compact_runs(buffer, new_len, threshold);
            }
            if flags & 0x4 as uint32_t != 0 {
                let preserve: core::ffi::c_int =
                    (param2 != 0 as core::ffi::c_int) as core::ffi::c_int;
                new_len = remove_duplicates(buffer, new_len, preserve);
            }
            if flags & 0x8 as uint32_t != 0 && new_len >= 2 as size_t {
                interleave_halves(buffer, new_len);
            }
            if flags & 0x10 as uint32_t != 0 && new_len >= 4 as size_t {
                let seg_size: size_t = if param1 > 0 as core::ffi::c_int {
                    param1 as size_t
                } else {
                    4 as size_t
                };
                if seg_size <= new_len {
                    reverse_segments(buffer, new_len, seg_size);
                }
            }
            new_len
        }
        unsafe extern "C" fn rotate_buffer(
            buf: *mut uint8_t,
            len: size_t,
            mut offset: core::ffi::c_int,
        ) {
            if len <= 1 as size_t {
                return;
            }
            offset %= len as core::ffi::c_int;
            if offset < 0 as core::ffi::c_int {
                offset = (offset as core::ffi::c_ulong).wrapping_add(len as core::ffi::c_ulong)
                    as core::ffi::c_int as core::ffi::c_int;
            }
            if offset == 0 as core::ffi::c_int {
                return;
            }
            let mut temp: [uint8_t; 256] = [0; 256];
            let chunk: size_t = (if offset < 256 as core::ffi::c_int {
                offset
            } else {
                256 as core::ffi::c_int
            }) as size_t;
            if (offset as size_t) < len.wrapping_div(2 as size_t) {
                let mut i: size_t = 0;
                i = 0 as size_t;
                while i < offset as size_t {
                    let copy_len: size_t = if (offset as size_t).wrapping_sub(i) < chunk {
                        (offset as size_t).wrapping_sub(i)
                    } else {
                        chunk
                    };
                    memmove(
                        temp.as_mut_ptr() as *mut core::ffi::c_void,
                        buf.add(i) as *const core::ffi::c_void,
                        copy_len,
                    );
                    memmove(
                        buf.add(i) as *mut core::ffi::c_void,
                        buf.offset(offset as isize) as *const core::ffi::c_void,
                        len.wrapping_sub(offset as size_t),
                    );
                    memmove(
                        buf.add(len).offset(-(offset as isize)) as *mut core::ffi::c_void,
                        temp.as_mut_ptr() as *const core::ffi::c_void,
                        copy_len,
                    );
                    i = (i as core::ffi::c_ulong).wrapping_add(chunk as core::ffi::c_ulong)
                        as size_t as size_t;
                }
            } else {
                let shift: size_t = len.wrapping_sub(offset as size_t);
                memmove(
                    temp.as_mut_ptr() as *mut core::ffi::c_void,
                    buf as *const core::ffi::c_void,
                    shift,
                );
                memmove(
                    buf as *mut core::ffi::c_void,
                    buf.add(shift) as *const core::ffi::c_void,
                    offset as size_t,
                );
                memmove(
                    buf.offset(offset as isize) as *mut core::ffi::c_void,
                    temp.as_mut_ptr() as *const core::ffi::c_void,
                    shift,
                );
            };
        }
        unsafe extern "C" fn compact_runs(
            buf: *mut uint8_t,
            mut len: size_t,
            threshold: uint8_t,
        ) -> size_t {
            let mut read: size_t = 0 as size_t;
            let mut write: size_t = 0 as size_t;
            while read < len {
                let current: uint8_t = *buf.add(read);
                let mut run_len: size_t = 1 as size_t;
                while read.wrapping_add(run_len) < len
                    && *buf.add(read.wrapping_add(run_len)) as core::ffi::c_int
                        == current as core::ffi::c_int
                {
                    run_len = run_len.wrapping_add(1);
                }
                if run_len >= threshold as size_t {
                    if run_len > 255 as size_t {
                        run_len = 255 as size_t;
                    }
                    let fresh0 = write;
                    write = write.wrapping_add(1);
                    *buf.add(fresh0) = current;
                    let fresh1 = write;
                    write = write.wrapping_add(1);
                    *buf.add(fresh1) = run_len as uint8_t;
                    if read.wrapping_add(run_len) < len {
                        let remaining: size_t = len.wrapping_sub(read.wrapping_add(run_len));
                        memmove(
                            buf.add(write) as *mut core::ffi::c_void,
                            buf.add(read).add(run_len) as *const core::ffi::c_void,
                            remaining,
                        );
                    }
                    len = write.wrapping_add(len.wrapping_sub(read.wrapping_add(run_len)));
                    read = write;
                } else {
                    if write != read {
                        memmove(
                            buf.add(write) as *mut core::ffi::c_void,
                            buf.add(read) as *const core::ffi::c_void,
                            run_len,
                        );
                    }
                    write = (write as core::ffi::c_ulong)
                        .wrapping_add(run_len as core::ffi::c_ulong)
                        as size_t as size_t;
                    read = (read as core::ffi::c_ulong).wrapping_add(run_len as core::ffi::c_ulong)
                        as size_t as size_t;
                }
            }
            len
        }
        unsafe extern "C" fn remove_duplicates(
            buf: *mut uint8_t,
            len: size_t,
            preserve_order: core::ffi::c_int,
        ) -> size_t {
            if len <= 1 as size_t {
                return len;
            }
            if preserve_order != 0 {
                let mut write: size_t = 1 as size_t;
                let mut i: size_t = 1 as size_t;
                while i < len {
                    let mut j: size_t = 0;
                    j = 0 as size_t;
                    while j < write {
                        if *buf.add(i) as core::ffi::c_int == *buf.add(j) as core::ffi::c_int {
                            break;
                        }
                        j = j.wrapping_add(1);
                    }
                    if j == write {
                        if write != i {
                            *buf.add(write) = *buf.add(i);
                        }
                        write = write.wrapping_add(1);
                    }
                    i = i.wrapping_add(1);
                }
                write
            } else {
                let mut seen: [uint8_t; 256] = [
                    0 as core::ffi::c_int as uint8_t,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                ];
                let mut write_0: size_t = 0 as size_t;
                let mut i_0: size_t = 0 as size_t;
                while i_0 < len {
                    if seen[*buf.add(i_0) as usize] == 0 {
                        seen[*buf.add(i_0) as usize] = 1 as uint8_t;
                        if write_0 != i_0 {
                            let temp: uint8_t = *buf.add(write_0);
                            *buf.add(write_0) = *buf.add(i_0);
                            *buf.add(i_0) = temp;
                        }
                        write_0 = write_0.wrapping_add(1);
                    }
                    i_0 = i_0.wrapping_add(1);
                }
                write_0
            }
        }
        unsafe extern "C" fn interleave_halves(buf: *mut uint8_t, len: size_t) {
            if len < 2 as size_t {
                return;
            }
            let half: size_t = len.wrapping_div(2 as size_t);
            let odd: size_t = len.wrapping_rem(2 as size_t);
            let mut temp: [uint8_t; 512] = [0; 512];
            if half <= 256 as size_t {
                memmove(
                    temp.as_mut_ptr() as *mut core::ffi::c_void,
                    buf as *const core::ffi::c_void,
                    half,
                );
                let mut i: size_t = 0 as size_t;
                while i < half {
                    memmove(
                        buf.add(i.wrapping_mul(2 as size_t))
                            .offset(1 as core::ffi::c_int as isize)
                            as *mut core::ffi::c_void,
                        buf.add(half).add(i) as *const core::ffi::c_void,
                        1 as size_t,
                    );
                    *buf.add(i.wrapping_mul(2 as size_t)) = temp[i as usize];
                    i = i.wrapping_add(1);
                }
                if odd != 0 {
                    *buf.add(len.wrapping_sub(1 as size_t)) = *buf.add(half);
                }
            } else {
                let mut i_0: size_t = 0 as size_t;
                while i_0 < half {
                    let src: size_t = half.wrapping_add(i_0);
                    let dst: size_t = i_0.wrapping_mul(2 as size_t).wrapping_add(1 as size_t);
                    if dst < src {
                        let val: uint8_t = *buf.add(src);
                        memmove(
                            buf.add(dst).offset(1 as core::ffi::c_int as isize)
                                as *mut core::ffi::c_void,
                            buf.add(dst) as *const core::ffi::c_void,
                            src.wrapping_sub(dst),
                        );
                        *buf.add(dst) = val;
                    }
                    i_0 = i_0.wrapping_add(1);
                }
            };
        }
        unsafe extern "C" fn reverse_segments(buf: *mut uint8_t, len: size_t, seg_size: size_t) {
            if seg_size <= 1 as size_t || len < seg_size {
                return;
            }
            let num_segments: size_t = len.wrapping_div(seg_size);
            let remainder: size_t = len.wrapping_rem(seg_size);
            let mut seg: size_t = 0 as size_t;
            while seg < num_segments {
                let base: size_t = seg.wrapping_mul(seg_size);
                let mut i: size_t = 0 as size_t;
                while i < seg_size.wrapping_div(2 as size_t) {
                    let mut temp: uint8_t = 0;
                    let left: size_t = base.wrapping_add(i);
                    let right: size_t = base
                        .wrapping_add(seg_size)
                        .wrapping_sub(1 as size_t)
                        .wrapping_sub(i);
                    temp = *buf.add(left);
                    memmove(
                        buf.add(left) as *mut core::ffi::c_void,
                        buf.add(right) as *const core::ffi::c_void,
                        1 as size_t,
                    );
                    memmove(
                        buf.add(right) as *mut core::ffi::c_void,
                        &mut temp as *mut uint8_t as *const core::ffi::c_void,
                        1 as size_t,
                    );
                    i = i.wrapping_add(1);
                }
                seg = seg.wrapping_add(1);
            }
            if remainder > 1 as size_t {
                let base_0: size_t = num_segments.wrapping_mul(seg_size);
                let mut i_0: size_t = 0 as size_t;
                while i_0 < remainder.wrapping_div(2 as size_t) {
                    let temp_0: uint8_t = *buf.add(base_0.wrapping_add(i_0));
                    *buf.add(base_0.wrapping_add(i_0)) = *buf.add(
                        base_0
                            .wrapping_add(remainder)
                            .wrapping_sub(1 as size_t)
                            .wrapping_sub(i_0),
                    );
                    *buf.add(
                        base_0
                            .wrapping_add(remainder)
                            .wrapping_sub(1 as size_t)
                            .wrapping_sub(i_0),
                    ) = temp_0;
                    i_0 = i_0.wrapping_add(1);
                }
            }
        }
    }
    pub mod main {
        use crate::src::lib::process_buffer;
        use crate::src::lib::size_t;
        use crate::src::lib::uint32_t;
        use crate::src::lib::uint8_t;
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
        unsafe fn main_0() -> core::ffi::c_int {
            let mut flags: uint32_t = 0;
            let mut param1: core::ffi::c_int = 0;
            let mut param2: core::ffi::c_int = 0;
            let mut length: size_t = 0;
            let mut buffer: [uint8_t; 256] = [0; 256];
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
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut param1 as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error reading param1\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut param2 as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error reading param2\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if scanf(
                b"%zu\0" as *const u8 as *const core::ffi::c_char,
                &mut length as *mut size_t,
            ) != 1 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error reading length\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            if length > 256 as size_t {
                fprintf(
                    stderr,
                    b"Error: length %zu exceeds maximum 256\n\0" as *const u8
                        as *const core::ffi::c_char,
                    length,
                );
                return 1 as core::ffi::c_int;
            }
            let mut i: size_t = 0 as size_t;
            while i < length {
                let mut byte: core::ffi::c_uint = 0;
                if scanf(
                    b"%u\0" as *const u8 as *const core::ffi::c_char,
                    &mut byte as *mut core::ffi::c_uint,
                ) != 1 as core::ffi::c_int
                {
                    fprintf(
                        stderr,
                        b"Error reading byte %zu\n\0" as *const u8 as *const core::ffi::c_char,
                        i,
                    );
                    return 1 as core::ffi::c_int;
                }
                buffer[i as usize] = byte as uint8_t;
                i = i.wrapping_add(1);
            }
            let new_length: size_t =
                process_buffer(buffer.as_mut_ptr(), length, flags, param1, param2);
            printf(
                b"%zu\0" as *const u8 as *const core::ffi::c_char,
                new_length,
            );
            let mut i_0: size_t = 0 as size_t;
            while i_0 < new_length {
                printf(
                    b" %u\0" as *const u8 as *const core::ffi::c_char,
                    buffer[i_0 as usize] as core::ffi::c_int,
                );
                i_0 = i_0.wrapping_add(1);
            }
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
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
    run_ownership_case_with_box_candidates("memmove", SOURCE, &[], &[]);
}
