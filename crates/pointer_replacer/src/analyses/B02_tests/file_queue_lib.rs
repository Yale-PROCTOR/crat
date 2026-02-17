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
    pub mod driver {
        use crate::src::file_queue::Init_FileQueue;
        use crate::src::file_queue::Read_FileMon;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stderr: *mut FILE;
            fn fclose(__stream: *mut FILE) -> core::ffi::c_int;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn memset(
                __s: *mut core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
        }
        pub type size_t = usize;
        pub type __dev_t = core::ffi::c_ulong;
        pub type __uid_t = core::ffi::c_uint;
        pub type __gid_t = core::ffi::c_uint;
        pub type __ino_t = core::ffi::c_ulong;
        pub type __mode_t = core::ffi::c_uint;
        pub type __nlink_t = core::ffi::c_ulong;
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        pub type __time_t = core::ffi::c_long;
        pub type __blksize_t = core::ffi::c_long;
        pub type __blkcnt_t = core::ffi::c_long;
        pub type __syscall_slong_t = core::ffi::c_long;
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
        pub type time_t = __time_t;
        #[repr(C)]
        pub struct tm {
            pub tm_sec: core::ffi::c_int,
            pub tm_min: core::ffi::c_int,
            pub tm_hour: core::ffi::c_int,
            pub tm_mday: core::ffi::c_int,
            pub tm_mon: core::ffi::c_int,
            pub tm_year: core::ffi::c_int,
            pub tm_wday: core::ffi::c_int,
            pub tm_yday: core::ffi::c_int,
            pub tm_isdst: core::ffi::c_int,
            pub tm_gmtoff: core::ffi::c_long,
            pub tm_zone: *const core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for tm {}
        #[automatically_derived]
        impl ::core::clone::Clone for tm {
            #[inline]
            fn clone(&self) -> tm {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_long>;
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
                *self
            }
        }
        #[repr(C)]
        pub struct timespec {
            pub tv_sec: __time_t,
            pub tv_nsec: __syscall_slong_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for timespec {}
        #[automatically_derived]
        impl ::core::clone::Clone for timespec {
            #[inline]
            fn clone(&self) -> timespec {
                let _: ::core::clone::AssertParamIsClone<__time_t>;
                let _: ::core::clone::AssertParamIsClone<__syscall_slong_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct stat {
            pub st_dev: __dev_t,
            pub st_ino: __ino_t,
            pub st_nlink: __nlink_t,
            pub st_mode: __mode_t,
            pub st_uid: __uid_t,
            pub st_gid: __gid_t,
            pub __pad0: core::ffi::c_int,
            pub st_rdev: __dev_t,
            pub st_size: __off_t,
            pub st_blksize: __blksize_t,
            pub st_blocks: __blkcnt_t,
            pub st_atim: timespec,
            pub st_mtim: timespec,
            pub st_ctim: timespec,
            pub __glibc_reserved: [__syscall_slong_t; 3],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for stat {}
        #[automatically_derived]
        impl ::core::clone::Clone for stat {
            #[inline]
            fn clone(&self) -> stat {
                let _: ::core::clone::AssertParamIsClone<__dev_t>;
                let _: ::core::clone::AssertParamIsClone<__ino_t>;
                let _: ::core::clone::AssertParamIsClone<__nlink_t>;
                let _: ::core::clone::AssertParamIsClone<__mode_t>;
                let _: ::core::clone::AssertParamIsClone<__uid_t>;
                let _: ::core::clone::AssertParamIsClone<__gid_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<__off_t>;
                let _: ::core::clone::AssertParamIsClone<__blksize_t>;
                let _: ::core::clone::AssertParamIsClone<__blkcnt_t>;
                let _: ::core::clone::AssertParamIsClone<timespec>;
                let _: ::core::clone::AssertParamIsClone<[__syscall_slong_t; 3]>;
                *self
            }
        }
        #[repr(C)]
        pub struct file_queue {
            pub last_change: time_t,
            pub year: core::ffi::c_int,
            pub day: core::ffi::c_int,
            pub flags: core::ffi::c_int,
            pub mon: [core::ffi::c_char; 4],
            pub file_name: [core::ffi::c_char; 257],
            pub fp: *mut FILE,
            pub f_status: stat,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for file_queue {}
        #[automatically_derived]
        impl ::core::clone::Clone for file_queue {
            #[inline]
            fn clone(&self) -> file_queue {
                let _: ::core::clone::AssertParamIsClone<time_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 4]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 257]>;
                let _: ::core::clone::AssertParamIsClone<*mut FILE>;
                let _: ::core::clone::AssertParamIsClone<stat>;
                *self
            }
        }
        #[repr(C)]
        pub struct alert_data {
            pub rule: core::ffi::c_uint,
            pub level: core::ffi::c_uint,
            pub alertid: *mut core::ffi::c_char,
            pub date: *mut core::ffi::c_char,
            pub location: *mut core::ffi::c_char,
            pub comment: *mut core::ffi::c_char,
            pub group: *mut core::ffi::c_char,
            pub srcip: *mut core::ffi::c_char,
            pub srcport: core::ffi::c_int,
            pub dstip: *mut core::ffi::c_char,
            pub dstport: core::ffi::c_int,
            pub user: *mut core::ffi::c_char,
            pub filename: *mut core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for alert_data {}
        #[automatically_derived]
        impl ::core::clone::Clone for alert_data {
            #[inline]
            fn clone(&self) -> alert_data {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_uint>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_uint>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn driver(
            day: core::ffi::c_int,
            month: core::ffi::c_int,
            year: core::ffi::c_int,
            timeout: core::ffi::c_uint,
            flags: core::ffi::c_int,
        ) -> *mut alert_data {
            let mut time: tm = {
                tm {
                    tm_sec: 0 as core::ffi::c_int,
                    tm_min: 0,
                    tm_hour: 0,
                    tm_mday: 0,
                    tm_mon: 0,
                    tm_year: 0,
                    tm_wday: 0,
                    tm_yday: 0,
                    tm_isdst: 0,
                    tm_gmtoff: 0,
                    tm_zone: std::ptr::null::<core::ffi::c_char>(),
                }
            };
            time.tm_mday = day;
            time.tm_mon = month;
            time.tm_year = year;
            let mut fq: file_queue = file_queue {
                last_change: 0,
                year: 0,
                day: 0,
                flags: 0,
                mon: [0; 4],
                file_name: [0; 257],
                fp: std::ptr::null_mut::<FILE>(),
                f_status: stat {
                    st_dev: 0,
                    st_ino: 0,
                    st_nlink: 0,
                    st_mode: 0,
                    st_uid: 0,
                    st_gid: 0,
                    __pad0: 0,
                    st_rdev: 0,
                    st_size: 0,
                    st_blksize: 0,
                    st_blocks: 0,
                    st_atim: timespec {
                        tv_sec: 0,
                        tv_nsec: 0,
                    },
                    st_mtim: timespec {
                        tv_sec: 0,
                        tv_nsec: 0,
                    },
                    st_ctim: timespec {
                        tv_sec: 0,
                        tv_nsec: 0,
                    },
                    __glibc_reserved: [0; 3],
                },
            };
            memset(
                &mut fq as *mut file_queue as *mut core::ffi::c_void,
                0 as core::ffi::c_int,
                ::core::mem::size_of::<file_queue>() as size_t,
            );
            if Init_FileQueue(&mut fq, &mut time, flags) < 0 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"File queue initialization failed\0" as *const u8 as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<alert_data>();
            }
            let al_data: *mut alert_data = Read_FileMon(&mut fq, &mut time, timeout);
            if !(fq.fp).is_null() {
                fclose(fq.fp);
            }
            al_data
        }
    }
    pub mod file_queue {
        use crate::src::driver::__time_t;
        use crate::src::driver::alert_data;
        use crate::src::driver::file_queue;
        use crate::src::driver::size_t;
        use crate::src::driver::stat;
        use crate::src::driver::time_t;
        use crate::src::driver::tm;
        use crate::src::driver::FILE;
        use crate::src::read_alert::GetAlertData;
        extern "C" {
            static mut stderr: *mut FILE;
            fn fclose(__stream: *mut FILE) -> core::ffi::c_int;
            fn fopen(
                __filename: *const core::ffi::c_char,
                __modes: *const core::ffi::c_char,
            ) -> *mut FILE;
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
            fn fseek(
                __stream: *mut FILE,
                __off: core::ffi::c_long,
                __whence: core::ffi::c_int,
            ) -> core::ffi::c_int;
            fn fileno(__stream: *mut FILE) -> core::ffi::c_int;
            fn fstat(__fd: core::ffi::c_int, __buf: *mut stat) -> core::ffi::c_int;
            fn memset(
                __s: *mut core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strerror(__errnum: core::ffi::c_int) -> *mut core::ffi::c_char;
            fn select(
                __nfds: core::ffi::c_int,
                __readfds: *mut fd_set,
                __writefds: *mut fd_set,
                __exceptfds: *mut fd_set,
                __timeout: *mut timeval,
            ) -> core::ffi::c_int;
            fn __errno_location() -> *mut core::ffi::c_int;
        }
        pub type __suseconds_t = core::ffi::c_long;
        #[repr(C)]
        pub struct timeval {
            pub tv_sec: __time_t,
            pub tv_usec: __suseconds_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for timeval {}
        #[automatically_derived]
        impl ::core::clone::Clone for timeval {
            #[inline]
            fn clone(&self) -> timeval {
                let _: ::core::clone::AssertParamIsClone<__time_t>;
                let _: ::core::clone::AssertParamIsClone<__suseconds_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct fd_set {
            pub __fds_bits: [__fd_mask; 16],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for fd_set {}
        #[automatically_derived]
        impl ::core::clone::Clone for fd_set {
            #[inline]
            fn clone(&self) -> fd_set {
                let _: ::core::clone::AssertParamIsClone<[__fd_mask; 16]>;
                *self
            }
        }
        pub type __fd_mask = core::ffi::c_long;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const SEEK_END: core::ffi::c_int = 2 as core::ffi::c_int;
        pub const MAX_FQUEUE: core::ffi::c_int = 256 as core::ffi::c_int;
        pub const FQ_TIMEOUT: core::ffi::c_int = 5 as core::ffi::c_int;
        pub const ALERTS_DAILY: [core::ffi::c_char; 11] = [
            b'a' as i8,
            b'l' as i8,
            b'e' as i8,
            b'r' as i8,
            b't' as i8,
            b's' as i8,
            b'.' as i8,
            b'l' as i8,
            b'o' as i8,
            b'g' as i8,
            b'\0' as i8,
        ];
        pub const CRALERT_READ_ALL: core::ffi::c_int = 0x4 as core::ffi::c_int;
        pub const CRALERT_FP_SET: core::ffi::c_int = 0x10 as core::ffi::c_int;
        pub const FSTAT_ERROR: [core::ffi::c_char; 72] = [
            b'(' as i8,
            b'1' as i8,
            b'1' as i8,
            b'1' as i8,
            b'8' as i8,
            b')' as i8,
            b':' as i8,
            b' ' as i8,
            b'C' as i8,
            b'o' as i8,
            b'u' as i8,
            b'l' as i8,
            b'd' as i8,
            b' ' as i8,
            b'n' as i8,
            b'o' as i8,
            b't' as i8,
            b' ' as i8,
            b'r' as i8,
            b'e' as i8,
            b't' as i8,
            b'r' as i8,
            b'i' as i8,
            b'e' as i8,
            b'v' as i8,
            b'e' as i8,
            b' ' as i8,
            b'i' as i8,
            b'n' as i8,
            b'f' as i8,
            b'o' as i8,
            b'r' as i8,
            b'm' as i8,
            b'a' as i8,
            b't' as i8,
            b'i' as i8,
            b'o' as i8,
            b'n' as i8,
            b' ' as i8,
            b'o' as i8,
            b'f' as i8,
            b' ' as i8,
            b'f' as i8,
            b'i' as i8,
            b'l' as i8,
            b'e' as i8,
            b' ' as i8,
            b'\'' as i8,
            b'%' as i8,
            b's' as i8,
            b'\'' as i8,
            b' ' as i8,
            b'd' as i8,
            b'u' as i8,
            b'e' as i8,
            b' ' as i8,
            b't' as i8,
            b'o' as i8,
            b' ' as i8,
            b'[' as i8,
            b'(' as i8,
            b'%' as i8,
            b'd' as i8,
            b')' as i8,
            b'-' as i8,
            b'(' as i8,
            b'%' as i8,
            b's' as i8,
            b')' as i8,
            b']' as i8,
            b'.' as i8,
            b'\0' as i8,
        ];
        pub const FSEEK_ERROR: [core::ffi::c_char; 64] = [
            b'(' as i8,
            b'1' as i8,
            b'1' as i8,
            b'1' as i8,
            b'6' as i8,
            b')' as i8,
            b':' as i8,
            b' ' as i8,
            b'C' as i8,
            b'o' as i8,
            b'u' as i8,
            b'l' as i8,
            b'd' as i8,
            b' ' as i8,
            b'n' as i8,
            b'o' as i8,
            b't' as i8,
            b' ' as i8,
            b's' as i8,
            b'e' as i8,
            b't' as i8,
            b' ' as i8,
            b'p' as i8,
            b'o' as i8,
            b's' as i8,
            b'i' as i8,
            b't' as i8,
            b'i' as i8,
            b'o' as i8,
            b'n' as i8,
            b' ' as i8,
            b'i' as i8,
            b'n' as i8,
            b' ' as i8,
            b'f' as i8,
            b'i' as i8,
            b'l' as i8,
            b'e' as i8,
            b' ' as i8,
            b'\'' as i8,
            b'%' as i8,
            b's' as i8,
            b'\'' as i8,
            b' ' as i8,
            b'd' as i8,
            b'u' as i8,
            b'e' as i8,
            b' ' as i8,
            b't' as i8,
            b'o' as i8,
            b' ' as i8,
            b'[' as i8,
            b'(' as i8,
            b'%' as i8,
            b'd' as i8,
            b')' as i8,
            b'-' as i8,
            b'(' as i8,
            b'%' as i8,
            b's' as i8,
            b')' as i8,
            b']' as i8,
            b'.' as i8,
            b'\0' as i8,
        ];
        #[no_mangle]
        pub unsafe extern "C" fn merror(
            err_template: *const core::ffi::c_char,
            file_name: *const core::ffi::c_char,
            err: core::ffi::c_int,
            err_msg: *const core::ffi::c_char,
        ) {
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            snprintf(
                buffer.as_mut_ptr(),
                ::core::mem::size_of::<[core::ffi::c_char; 256]>() as size_t,
                err_template,
                file_name,
                err,
                err_msg,
            );
            fprintf(
                stderr,
                b"%s\n\0" as *const u8 as *const core::ffi::c_char,
                buffer.as_ptr(),
            );
        }
        static mut s_month: [*const core::ffi::c_char; 12] = [
            b"Jan\0" as *const u8 as *const core::ffi::c_char,
            b"Feb\0" as *const u8 as *const core::ffi::c_char,
            b"Mar\0" as *const u8 as *const core::ffi::c_char,
            b"Apr\0" as *const u8 as *const core::ffi::c_char,
            b"May\0" as *const u8 as *const core::ffi::c_char,
            b"Jun\0" as *const u8 as *const core::ffi::c_char,
            b"Jul\0" as *const u8 as *const core::ffi::c_char,
            b"Aug\0" as *const u8 as *const core::ffi::c_char,
            b"Sep\0" as *const u8 as *const core::ffi::c_char,
            b"Oct\0" as *const u8 as *const core::ffi::c_char,
            b"Nov\0" as *const u8 as *const core::ffi::c_char,
            b"Dec\0" as *const u8 as *const core::ffi::c_char,
        ];
        unsafe extern "C" fn file_sleep() {
            let mut fp_timeout: timeval = timeval {
                tv_sec: 0,
                tv_usec: 0,
            };
            fp_timeout.tv_sec = FQ_TIMEOUT as __time_t;
            fp_timeout.tv_usec = 0 as __suseconds_t;
            select(
                0 as core::ffi::c_int,
                std::ptr::null_mut::<fd_set>(),
                std::ptr::null_mut::<fd_set>(),
                std::ptr::null_mut::<fd_set>(),
                &mut fp_timeout,
            );
        }
        unsafe extern "C" fn GetFile_Queue(fileq: *mut file_queue) {
            (*fileq).file_name[0 as core::ffi::c_int as usize] = '\0' as i32 as core::ffi::c_char;
            (*fileq).file_name[MAX_FQUEUE as usize] = '\0' as i32 as core::ffi::c_char;
            snprintf(
                ((*fileq).file_name).as_mut_ptr(),
                MAX_FQUEUE as size_t,
                b"%s\0" as *const u8 as *const core::ffi::c_char,
                if (*fileq).flags & CRALERT_FP_SET != 0 {
                    b"<stdin>\0" as *const u8 as *const core::ffi::c_char
                } else {
                    ALERTS_DAILY.as_ptr()
                },
            );
        }
        unsafe extern "C" fn Handle_Queue(
            fileq: *mut file_queue,
            flags: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if flags & CRALERT_FP_SET == 0 {
                if !((*fileq).fp).is_null() {
                    fclose((*fileq).fp);
                    (*fileq).fp = std::ptr::null_mut::<FILE>();
                }
                (*fileq).fp = fopen(
                    ((*fileq).file_name).as_ptr(),
                    b"r\0" as *const u8 as *const core::ffi::c_char,
                );
                if ((*fileq).fp).is_null() {
                    return 0 as core::ffi::c_int;
                }
            }
            if flags & CRALERT_READ_ALL == 0 {
                if ((*fileq).fp).is_null() {
                    return 0 as core::ffi::c_int;
                }
                if fseek((*fileq).fp, 0 as core::ffi::c_long, SEEK_END) < 0 as core::ffi::c_int {
                    merror(
                        FSEEK_ERROR.as_ptr(),
                        ((*fileq).file_name).as_ptr(),
                        *__errno_location(),
                        strerror(*__errno_location()),
                    );
                    fclose((*fileq).fp);
                    (*fileq).fp = std::ptr::null_mut::<FILE>();
                    return -(1 as core::ffi::c_int);
                }
            }
            if !((*fileq).fp).is_null()
                && fstat(fileno((*fileq).fp), &mut (*fileq).f_status) < 0 as core::ffi::c_int
            {
                merror(
                    FSTAT_ERROR.as_ptr(),
                    ((*fileq).file_name).as_ptr(),
                    *__errno_location(),
                    strerror(*__errno_location()),
                );
                fclose((*fileq).fp);
                (*fileq).fp = std::ptr::null_mut::<FILE>();
                return -(1 as core::ffi::c_int);
            }
            (*fileq).last_change = (*fileq).f_status.st_mtim.tv_sec as time_t;
            1 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn Init_FileQueue(
            fileq: *mut file_queue,
            p: *const tm,
            flags: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if flags & CRALERT_FP_SET == 0 {
                (*fileq).fp = std::ptr::null_mut::<FILE>();
            }
            (*fileq).last_change = 0 as time_t;
            (*fileq).flags = 0 as core::ffi::c_int;
            (*fileq).day = (*p).tm_mday;
            (*fileq).year = (*p).tm_year + 1900 as core::ffi::c_int;
            strncpy(
                ((*fileq).mon).as_mut_ptr(),
                s_month[(*p).tm_mon as usize],
                3 as size_t,
            );
            memset(
                ((*fileq).file_name).as_mut_ptr() as *mut core::ffi::c_void,
                '\0' as i32,
                (MAX_FQUEUE + 1 as core::ffi::c_int) as size_t,
            );
            (*fileq).flags = flags;
            GetFile_Queue(fileq);
            if Handle_Queue(fileq, (*fileq).flags) < 0 as core::ffi::c_int {
                return -(1 as core::ffi::c_int);
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn Read_FileMon(
            fileq: *mut file_queue,
            p: *const tm,
            timeout: core::ffi::c_uint,
        ) -> *mut alert_data {
            let mut i: core::ffi::c_uint = 0 as core::ffi::c_uint;
            let mut al_data: *mut alert_data = std::ptr::null_mut::<alert_data>();
            if ((*fileq).fp).is_null()
                && Handle_Queue(fileq, 0 as core::ffi::c_int) != 1 as core::ffi::c_int
            {
                file_sleep();
                return std::ptr::null_mut::<alert_data>();
            }
            if ((*fileq).fp).is_null() {
                return std::ptr::null_mut::<alert_data>();
            }
            al_data = GetAlertData((*fileq).flags, (*fileq).fp);
            if !al_data.is_null() {
                return al_data;
            }
            (*fileq).day = (*p).tm_mday;
            (*fileq).year = (*p).tm_year + 1900 as core::ffi::c_int;
            strncpy(
                ((*fileq).mon).as_mut_ptr(),
                s_month[(*p).tm_mon as usize],
                3 as size_t,
            );
            GetFile_Queue(fileq);
            if Handle_Queue(fileq, 0 as core::ffi::c_int) != 1 as core::ffi::c_int {
                file_sleep();
                return std::ptr::null_mut::<alert_data>();
            }
            while i < timeout {
                al_data = GetAlertData((*fileq).flags, (*fileq).fp);
                if !al_data.is_null() {
                    return al_data;
                }
                i = i.wrapping_add(1);
                file_sleep();
            }
            std::ptr::null_mut::<alert_data>()
        }
    }
    pub mod read_alert {
        use crate::src::driver::alert_data;
        use crate::src::driver::size_t;
        use crate::src::driver::FILE;
        extern "C" {
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn fseek(
                __stream: *mut FILE,
                __off: core::ffi::c_long,
                __whence: core::ffi::c_int,
            ) -> core::ffi::c_int;
            fn clearerr(__stream: *mut FILE);
            fn feof(__stream: *mut FILE) -> core::ffi::c_int;
            fn perror(__s: *const core::ffi::c_char);
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn realloc(__ptr: *mut core::ffi::c_void, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn exit(__status: core::ffi::c_int) -> !;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strncmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
                __n: size_t,
            ) -> core::ffi::c_int;
            fn strdup(__s: *const core::ffi::c_char) -> *mut core::ffi::c_char;
            fn strchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
            fn strrchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
            fn strstr(
                __haystack: *const core::ffi::c_char,
                __needle: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const SEEK_CUR: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const CRALERT_MAIL_SET: core::ffi::c_int = 0x1 as core::ffi::c_int;
        pub const EXIT_FAILURE: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const OS_MAXSTR: core::ffi::c_int = 1024 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn os_calloc(num: size_t, size: size_t) -> *mut core::ffi::c_void {
            let out: *mut core::ffi::c_void = calloc(num, size);
            if out.is_null() {
                fprintf(
                    stderr,
                    b"Memory allocation failed in os_calloc\0" as *const u8
                        as *const core::ffi::c_char,
                );
                exit(EXIT_FAILURE);
            }
            out
        }
        #[no_mangle]
        pub unsafe extern "C" fn os_realloc(
            ptr: *mut core::ffi::c_void,
            new_size: size_t,
        ) -> *mut core::ffi::c_void {
            let out: *mut core::ffi::c_void = realloc(ptr, new_size);
            if out.is_null() {
                fprintf(
                    stderr,
                    b"Memory allocation failed in os_realloc\0" as *const u8
                        as *const core::ffi::c_char,
                );
                exit(EXIT_FAILURE);
            }
            out
        }
        #[no_mangle]
        pub unsafe extern "C" fn os_strdup(
            str: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            if str.is_null() {
                fprintf(
                    stderr,
                    b"NULL string passed to os_strdup\0" as *const u8 as *const core::ffi::c_char,
                );
                exit(EXIT_FAILURE);
            }
            let dup: *mut core::ffi::c_char = strdup(str);
            if dup.is_null() {
                fprintf(
                    stderr,
                    b"Memory allocation failed in os_strdup\0" as *const u8
                        as *const core::ffi::c_char,
                );
                exit(EXIT_FAILURE);
            }
            dup
        }
        pub const ALERT_BEGIN: [core::ffi::c_char; 9] = [
            b'*' as i8,
            b'*' as i8,
            b' ' as i8,
            b'A' as i8,
            b'l' as i8,
            b'e' as i8,
            b'r' as i8,
            b't' as i8,
            b'\0' as i8,
        ];
        pub const ALERT_BEGIN_SZ: core::ffi::c_int = 8 as core::ffi::c_int;
        pub const RULE_BEGIN: [core::ffi::c_char; 7] = [
            b'R' as i8,
            b'u' as i8,
            b'l' as i8,
            b'e' as i8,
            b':' as i8,
            b' ' as i8,
            b'\0' as i8,
        ];
        pub const RULE_BEGIN_SZ: core::ffi::c_int = 6 as core::ffi::c_int;
        pub const SRCIP_BEGIN: [core::ffi::c_char; 9] = [
            b'S' as i8,
            b'r' as i8,
            b'c' as i8,
            b' ' as i8,
            b'I' as i8,
            b'P' as i8,
            b':' as i8,
            b' ' as i8,
            b'\0' as i8,
        ];
        pub const SRCIP_BEGIN_SZ: core::ffi::c_int = 8 as core::ffi::c_int;
        pub const SRCPORT_BEGIN: [core::ffi::c_char; 11] = [
            b'S' as i8,
            b'r' as i8,
            b'c' as i8,
            b' ' as i8,
            b'P' as i8,
            b'o' as i8,
            b'r' as i8,
            b't' as i8,
            b':' as i8,
            b' ' as i8,
            b'\0' as i8,
        ];
        pub const SRCPORT_BEGIN_SZ: core::ffi::c_int = 10 as core::ffi::c_int;
        pub const DSTIP_BEGIN: [core::ffi::c_char; 9] = [
            b'D' as i8,
            b's' as i8,
            b't' as i8,
            b' ' as i8,
            b'I' as i8,
            b'P' as i8,
            b':' as i8,
            b' ' as i8,
            b'\0' as i8,
        ];
        pub const DSTIP_BEGIN_SZ: core::ffi::c_int = 8 as core::ffi::c_int;
        pub const DSTPORT_BEGIN: [core::ffi::c_char; 11] = [
            b'D' as i8,
            b's' as i8,
            b't' as i8,
            b' ' as i8,
            b'P' as i8,
            b'o' as i8,
            b'r' as i8,
            b't' as i8,
            b':' as i8,
            b' ' as i8,
            b'\0' as i8,
        ];
        pub const DSTPORT_BEGIN_SZ: core::ffi::c_int = 10 as core::ffi::c_int;
        pub const USER_BEGIN: [core::ffi::c_char; 7] = [
            b'U' as i8,
            b's' as i8,
            b'e' as i8,
            b'r' as i8,
            b':' as i8,
            b' ' as i8,
            b'\0' as i8,
        ];
        pub const USER_BEGIN_SZ: core::ffi::c_int = 6 as core::ffi::c_int;
        pub const ALERT_MAIL: [core::ffi::c_char; 5] =
            [b'm' as i8, b'a' as i8, b'i' as i8, b'l' as i8, b'\0' as i8];
        pub const ALERT_MAIL_SZ: core::ffi::c_int = 4 as core::ffi::c_int;
        pub const LOG_LIMIT: core::ffi::c_int = 100 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn FreeAlertData(mut al_data: *mut alert_data) {
            let p: *mut *mut core::ffi::c_char = std::ptr::null_mut::<*mut core::ffi::c_char>();
            if !((*al_data).alertid).is_null() {
                free((*al_data).alertid as *mut core::ffi::c_void);
                (*al_data).alertid = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).date).is_null() {
                free((*al_data).date as *mut core::ffi::c_void);
                (*al_data).date = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).location).is_null() {
                free((*al_data).location as *mut core::ffi::c_void);
                (*al_data).location = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).comment).is_null() {
                free((*al_data).comment as *mut core::ffi::c_void);
                (*al_data).comment = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).group).is_null() {
                free((*al_data).group as *mut core::ffi::c_void);
                (*al_data).group = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).srcip).is_null() {
                free((*al_data).srcip as *mut core::ffi::c_void);
                (*al_data).srcip = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).dstip).is_null() {
                free((*al_data).dstip as *mut core::ffi::c_void);
                (*al_data).dstip = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).user).is_null() {
                free((*al_data).user as *mut core::ffi::c_void);
                (*al_data).user = std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*al_data).filename).is_null() {
                free((*al_data).filename as *mut core::ffi::c_void);
                (*al_data).filename = std::ptr::null_mut::<core::ffi::c_char>();
            }
            free(al_data as *mut core::ffi::c_void);
            al_data = std::ptr::null_mut::<alert_data>();
        }
        #[no_mangle]
        pub unsafe extern "C" fn GetAlertData(
            flag: core::ffi::c_int,
            fp: *mut FILE,
        ) -> *mut alert_data {
            let current_block: u64;
            let mut al_data: *mut alert_data = std::ptr::null_mut::<alert_data>();
            al_data = os_calloc(1 as size_t, ::core::mem::size_of::<alert_data>() as size_t)
                as *mut alert_data;
            let mut _r: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut issyscheck: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut log_size: size_t = 0 as size_t;
            let mut p: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut str: [core::ffi::c_char; 1025] = [0; 1025];
            str[OS_MAXSTR as usize] = '\0' as i32 as core::ffi::c_char;
            loop {
                if (fgets(str.as_mut_ptr(), OS_MAXSTR, fp)).is_null() {
                    current_block = 3567897568976182940;
                    break;
                }
                if strncmp(ALERT_BEGIN.as_ptr(), str.as_ptr(), ALERT_BEGIN_SZ as size_t)
                    == 0 as core::ffi::c_int
                {
                    let mut m: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
                    let mut z: size_t = 0 as size_t;
                    if _r == 2 as core::ffi::c_int {
                        if fseek(
                            fp,
                            (strlen(str.as_ptr())).wrapping_neg() as core::ffi::c_long,
                            SEEK_CUR,
                        ) == -(1 as core::ffi::c_int)
                        {
                            current_block = 13720375801346730317;
                            break;
                        }
                        return al_data;
                    } else {
                        p = str
                            .as_mut_ptr()
                            .offset(ALERT_BEGIN_SZ as isize)
                            .offset(1 as core::ffi::c_int as isize);
                        m = strstr(p, b":\0" as *const u8 as *const core::ffi::c_char);
                        if m.is_null() {
                            continue;
                        }
                        z = (strlen(p)).wrapping_sub(strlen(m));
                        (*al_data).alertid =
                            os_realloc(
                                (*al_data).alertid as *mut core::ffi::c_void,
                                z.wrapping_add(1 as size_t)
                                    .wrapping_mul(
                                        ::core::mem::size_of::<core::ffi::c_char>() as size_t
                                    ),
                            ) as *mut core::ffi::c_char;
                        strncpy((*al_data).alertid, p, z);
                        *((*al_data).alertid).add(z) = '\0' as i32 as core::ffi::c_char;
                        p = strchr(p, ' ' as i32);
                        if p.is_null() {
                            continue;
                        }
                        p = p.offset(1);
                        if flag & CRALERT_MAIL_SET != 0
                            && strncmp(ALERT_MAIL.as_ptr(), p, ALERT_MAIL_SZ as size_t)
                                != 0 as core::ffi::c_int
                        {
                            continue;
                        }
                        p = strchr(p, '-' as i32);
                        if !p.is_null() {
                            p = p.offset(1);
                            while *p as core::ffi::c_int == ' ' as i32 {
                                p = p.offset(1);
                            }
                            if !((*al_data).group).is_null() {
                                free((*al_data).group as *mut core::ffi::c_void);
                                (*al_data).group = std::ptr::null_mut::<core::ffi::c_char>();
                            }
                            (*al_data).group = os_strdup(p);
                            p = strrchr((*al_data).group, '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            if !((*al_data).group).is_null()
                                && !(strstr(
                                    (*al_data).group,
                                    b"syscheck\0" as *const u8 as *const core::ffi::c_char,
                                ))
                                .is_null()
                            {
                                issyscheck = 1 as core::ffi::c_int;
                            }
                        }
                        _r = 1 as core::ffi::c_int;
                    }
                } else {
                    if _r < 1 as core::ffi::c_int {
                        continue;
                    }
                    if _r == 1 as core::ffi::c_int {
                        p = strrchr(str.as_ptr(), '\n' as i32);
                        if !p.is_null() {
                            *p = '\0' as i32 as core::ffi::c_char;
                        }
                        p = strchr(str.as_ptr(), ':' as i32);
                        if !p.is_null() {
                            p = strchr(p, ' ' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                                p = p.offset(1);
                            } else {
                                perror(
                                    b"date of location not NULL\0" as *const u8
                                        as *const core::ffi::c_char,
                                );
                                current_block = 13720375801346730317;
                                break;
                            }
                        }
                        if !((*al_data).date).is_null()
                            || !((*al_data).location).is_null()
                            || p.is_null()
                        {
                            perror(
                                b"date or location not NULL or p is NULL\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            current_block = 13720375801346730317;
                            break;
                        } else {
                            (*al_data).date = os_strdup(str.as_ptr());
                            (*al_data).location = os_strdup(p);
                            _r = 2 as core::ffi::c_int;
                            log_size = 0 as size_t;
                        }
                    } else {
                        if _r != 2 as core::ffi::c_int {
                            continue;
                        }
                        if strncmp(RULE_BEGIN.as_ptr(), str.as_ptr(), RULE_BEGIN_SZ as size_t)
                            == 0 as core::ffi::c_int
                        {
                            p = strrchr(str.as_ptr(), '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            p = str.as_mut_ptr().offset(RULE_BEGIN_SZ as isize);
                            (*al_data).rule = atoi(p) as core::ffi::c_uint;
                            p = strchr(p, ' ' as i32);
                            if !p.is_null() {
                                p = p.offset(1);
                                p = strchr(p, ' ' as i32);
                                if !p.is_null() {
                                    p = p.offset(1);
                                }
                            }
                            if p.is_null() {
                                current_block = 13720375801346730317;
                                break;
                            }
                            (*al_data).level = atoi(p) as core::ffi::c_uint;
                            p = strchr(p, '\'' as i32);
                            if p.is_null() {
                                current_block = 13720375801346730317;
                                break;
                            }
                            p = p.offset(1);
                            if !((*al_data).comment).is_null() {
                                free((*al_data).comment as *mut core::ffi::c_void);
                                (*al_data).comment = std::ptr::null_mut::<core::ffi::c_char>();
                            }
                            (*al_data).comment = os_strdup(p);
                            p = strrchr((*al_data).comment, '\'' as i32);
                            if p.is_null() {
                                current_block = 13720375801346730317;
                                break;
                            }
                            *p = '\0' as i32 as core::ffi::c_char;
                        } else if strncmp(
                            SRCIP_BEGIN.as_ptr(),
                            str.as_ptr(),
                            SRCIP_BEGIN_SZ as size_t,
                        ) == 0 as core::ffi::c_int
                        {
                            p = strrchr(str.as_ptr(), '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            p = str.as_mut_ptr().offset(SRCIP_BEGIN_SZ as isize);
                            if !((*al_data).srcip).is_null() {
                                free((*al_data).srcip as *mut core::ffi::c_void);
                                (*al_data).srcip = std::ptr::null_mut::<core::ffi::c_char>();
                            }
                            (*al_data).srcip = os_strdup(p);
                        } else if strncmp(
                            SRCPORT_BEGIN.as_ptr(),
                            str.as_ptr(),
                            SRCPORT_BEGIN_SZ as size_t,
                        ) == 0 as core::ffi::c_int
                        {
                            p = strrchr(str.as_ptr(), '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            p = str.as_mut_ptr().offset(SRCPORT_BEGIN_SZ as isize);
                            (*al_data).srcport = atoi(p);
                        } else if strncmp(
                            DSTIP_BEGIN.as_ptr(),
                            str.as_ptr(),
                            DSTIP_BEGIN_SZ as size_t,
                        ) == 0 as core::ffi::c_int
                        {
                            p = strrchr(str.as_ptr(), '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            p = str.as_mut_ptr().offset(DSTIP_BEGIN_SZ as isize);
                            if !((*al_data).dstip).is_null() {
                                free((*al_data).dstip as *mut core::ffi::c_void);
                                (*al_data).dstip = std::ptr::null_mut::<core::ffi::c_char>();
                            }
                            (*al_data).dstip = os_strdup(p);
                        } else if strncmp(
                            DSTPORT_BEGIN.as_ptr(),
                            str.as_ptr(),
                            DSTPORT_BEGIN_SZ as size_t,
                        ) == 0 as core::ffi::c_int
                        {
                            p = strrchr(str.as_ptr(), '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            p = str.as_mut_ptr().offset(DSTPORT_BEGIN_SZ as isize);
                            (*al_data).dstport = atoi(p);
                        } else if strncmp(
                            USER_BEGIN.as_ptr(),
                            str.as_ptr(),
                            USER_BEGIN_SZ as size_t,
                        ) == 0 as core::ffi::c_int
                        {
                            p = strrchr(str.as_ptr(), '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            p = str.as_mut_ptr().offset(USER_BEGIN_SZ as isize);
                            if !((*al_data).user).is_null() {
                                free((*al_data).user as *mut core::ffi::c_void);
                                (*al_data).user = std::ptr::null_mut::<core::ffi::c_char>();
                            }
                            (*al_data).user = os_strdup(p);
                        } else if log_size < LOG_LIMIT as size_t {
                            p = strrchr(str.as_ptr(), '\n' as i32);
                            if !p.is_null() {
                                *p = '\0' as i32 as core::ffi::c_char;
                            }
                            if issyscheck == 1 as core::ffi::c_int {
                                if strncmp(
                                    str.as_ptr(),
                                    b"Integrity checksum changed for: '\0" as *const u8
                                        as *const core::ffi::c_char,
                                    33 as size_t,
                                ) == 0 as core::ffi::c_int
                                {
                                    (*al_data).filename = strdup(
                                        str.as_mut_ptr().offset(33 as core::ffi::c_int as isize),
                                    );
                                    if !((*al_data).filename).is_null() {
                                        *((*al_data).filename).add(
                                            (strlen((*al_data).filename)).wrapping_sub(1 as size_t),
                                        ) = '\0' as i32 as core::ffi::c_char;
                                    }
                                }
                                issyscheck = 0 as core::ffi::c_int;
                            }
                        }
                    }
                }
            }
            if current_block == 3567897568976182940 && feof(fp) != 0 && _r == 2 as core::ffi::c_int
            {
                return al_data;
            }
            FreeAlertData(al_data);
            clearerr(fp);
            std::ptr::null_mut::<alert_data>()
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("file_queue_lib", SOURCE);
}
