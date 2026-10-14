extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    fn atol(__nptr: *const ::core::ffi::c_char) -> ::core::ffi::c_long;
    fn abort() -> !;
    fn exit(__status: ::core::ffi::c_int) -> !;
    fn strchr(
        __s: *const ::core::ffi::c_char,
        __c: ::core::ffi::c_int,
    ) -> *mut ::core::ffi::c_char;
    fn nanosleep(
        __requested_time: *const timespec,
        __remaining: *mut timespec,
    ) -> ::core::ffi::c_int;
    fn clock_gettime(__clock_id: clockid_t, __tp: *mut timespec) -> ::core::ffi::c_int;
    static mut optarg: *mut ::core::ffi::c_char;
    fn getopt(
        ___argc: ::core::ffi::c_int,
        ___argv: *const *mut ::core::ffi::c_char,
        __shortopts: *const ::core::ffi::c_char,
    ) -> ::core::ffi::c_int;
    fn getentropy(
        __buffer: *mut ::core::ffi::c_void,
        __length: size_t,
    ) -> ::core::ffi::c_int;
    static mut stdin: *mut FILE;
    static mut stdout: *mut FILE;
    fn fflush(__stream: *mut FILE) -> ::core::ffi::c_int;
    fn setvbuf(
        __stream: *mut FILE,
        __buf: *mut ::core::ffi::c_char,
        __modes: ::core::ffi::c_int,
        __n: size_t,
    ) -> ::core::ffi::c_int;
    fn printf(__format: *const ::core::ffi::c_char, ...) -> ::core::ffi::c_int;
    fn getdelim(
        __lineptr: *mut *mut ::core::ffi::c_char,
        __n: *mut size_t,
        __delimiter: ::core::ffi::c_int,
        __stream: *mut FILE,
    ) -> __ssize_t;
    fn puts(__s: *const ::core::ffi::c_char) -> ::core::ffi::c_int;
    fn ferror(__stream: *mut FILE) -> ::core::ffi::c_int;
}
pub type __uint64_t = u64;
pub type __off_t = ::core::ffi::c_long;
pub type __off64_t = ::core::ffi::c_long;
pub type __time_t = ::core::ffi::c_long;
pub type __clockid_t = ::core::ffi::c_int;
pub type __ssize_t = ::core::ffi::c_long;
pub type __syscall_slong_t = ::core::ffi::c_long;
pub type uint64_t = __uint64_t;
pub type size_t = usize;
pub type clockid_t = __clockid_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct timespec {
    pub tv_sec: __time_t,
    pub tv_nsec: __syscall_slong_t,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct _IO_FILE {
    pub _flags: ::core::ffi::c_int,
    pub _IO_read_ptr: *mut ::core::ffi::c_char,
    pub _IO_read_end: *mut ::core::ffi::c_char,
    pub _IO_read_base: *mut ::core::ffi::c_char,
    pub _IO_write_base: *mut ::core::ffi::c_char,
    pub _IO_write_ptr: *mut ::core::ffi::c_char,
    pub _IO_write_end: *mut ::core::ffi::c_char,
    pub _IO_buf_base: *mut ::core::ffi::c_char,
    pub _IO_buf_end: *mut ::core::ffi::c_char,
    pub _IO_save_base: *mut ::core::ffi::c_char,
    pub _IO_backup_base: *mut ::core::ffi::c_char,
    pub _IO_save_end: *mut ::core::ffi::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: ::core::ffi::c_int,
    pub _flags2: ::core::ffi::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: ::core::ffi::c_ushort,
    pub _vtable_offset: ::core::ffi::c_schar,
    pub _shortbuf: [::core::ffi::c_char; 1],
    pub _lock: *mut ::core::ffi::c_void,
    pub _offset: __off64_t,
    pub _codecvt: *mut _IO_codecvt,
    pub _wide_data: *mut _IO_wide_data,
    pub _freeres_list: *mut _IO_FILE,
    pub _freeres_buf: *mut ::core::ffi::c_void,
    pub __pad5: size_t,
    pub _mode: ::core::ffi::c_int,
    pub _unused2: [::core::ffi::c_char; 20],
}
pub type _IO_lock_t = ();
pub type FILE = _IO_FILE;
pub const CLOCK_REALTIME: ::core::ffi::c_int = 0 as ::core::ffi::c_int;
pub const _IOLBF: ::core::ffi::c_int = 1 as ::core::ffi::c_int;
#[no_mangle]
pub unsafe extern "C" fn ulidgen_r(mut ulid: *mut ::core::ffi::c_char) {
    static mut b32alphabet: *const ::core::ffi::c_char = b"0123456789ABCDEFGHJKMNPQRSTVWXYZ\0"
        as *const u8 as *const ::core::ffi::c_char;
    let mut buf = ulid.offset(10 as ::core::ffi::c_int as isize);
    let mut same = 1 as ::core::ffi::c_int;
    *ulid.offset(26 as ::core::ffi::c_int as isize) = 0 as ::core::ffi::c_char;
    let mut tv = timespec { tv_sec: 0, tv_nsec: 0 };
    clock_gettime(CLOCK_REALTIME, &raw mut tv);
    let mut t: uint64_t = (tv.tv_sec as ::core::ffi::c_long * 1000 as ::core::ffi::c_long
        + tv.tv_nsec as ::core::ffi::c_long / 1000000 as ::core::ffi::c_long)
        as uint64_t;
    let mut i = 9 as ::core::ffi::c_int;
    while i >= 0 as ::core::ffi::c_int {
        if *ulid.offset(i as isize) as ::core::ffi::c_int
            != *b32alphabet.offset(t.wrapping_rem(32 as uint64_t) as isize)
                as ::core::ffi::c_int
        {
            *ulid.offset(i as isize) = *b32alphabet
                .offset(t.wrapping_rem(32 as uint64_t) as isize);
            same = 0 as ::core::ffi::c_int;
        }
        i -= 1;
        t = (t as ::core::ffi::c_ulong).wrapping_div(32 as ::core::ffi::c_ulong)
            as uint64_t as uint64_t;
    }
    if same != 0 {
        let mut i_0 = 15 as ::core::ffi::c_int;
        while i_0 >= 0 as ::core::ffi::c_int
            && *buf.offset(i_0 as isize) as ::core::ffi::c_int == 'Z' as i32
        {
            let fresh0 = i_0;
            i_0 = i_0 - 1;
            *buf.offset(fresh0 as isize) = '0' as i32 as ::core::ffi::c_char;
        }
        if i_0 < 0 as ::core::ffi::c_int {
            let mut fresh1: timespec = timespec {
                tv_sec: 0 as __time_t,
                tv_nsec: 1234567 as __syscall_slong_t,
            };
            nanosleep(&raw mut fresh1, ::core::ptr::null_mut::<timespec>());
            ulidgen_r(ulid);
            return;
        }
        let mut s = strchr(b32alphabet, *buf.offset(i_0 as isize) as ::core::ffi::c_int);
        if !s.is_null() {
            *buf.offset(i_0 as isize) = *s.offset(1 as ::core::ffi::c_int as isize);
            return;
        }
    }
    let mut rnd: [::core::ffi::c_uchar; 16] = [0; 16];
    if getentropy(
        &raw mut rnd as *mut ::core::ffi::c_uchar as *mut ::core::ffi::c_void,
        ::core::mem::size_of::<[::core::ffi::c_uchar; 16]>() as size_t,
    ) < 0 as ::core::ffi::c_int
    {
        abort();
    }
    let mut i_1 = 0 as ::core::ffi::c_int;
    while i_1 < 16 as ::core::ffi::c_int {
        *buf.offset(i_1 as isize) = *b32alphabet
            .offset(
                (rnd[i_1 as usize] as ::core::ffi::c_int % 32 as ::core::ffi::c_int)
                    as isize,
            );
        i_1 += 1;
    }
}
unsafe fn main_0(
    mut argc: ::core::ffi::c_int,
    mut argv: *mut *mut ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    let mut ulid: [::core::ffi::c_char; 27] = [
        0 as ::core::ffi::c_int as ::core::ffi::c_char,
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
    let mut c: ::core::ffi::c_int = 0;
    let mut n = 1 as ::core::ffi::c_long;
    let mut tflag = 0 as ::core::ffi::c_int;
    loop {
        c = getopt(
            argc,
            argv as *const *mut ::core::ffi::c_char,
            b"n:t\0" as *const u8 as *const ::core::ffi::c_char,
        );
        if !(c != -(1 as ::core::ffi::c_int)) {
            break;
        }
        match c {
            110 => {
                n = atol(optarg);
            }
            116 => {
                tflag = 1 as ::core::ffi::c_int;
            }
            _ => {}
        }
    }
    if tflag != 0 {
        let mut line = ::core::ptr::null_mut::<::core::ffi::c_char>();
        let mut linelen: size_t = 0 as size_t;
        setvbuf(
            stdout,
            ::core::ptr::null_mut::<::core::ffi::c_char>(),
            _IOLBF,
            0 as size_t,
        );
        while getdelim(&raw mut line, &raw mut linelen, '\n' as i32, stdin)
            != -(1 as ::core::ffi::c_int) as ::core::ffi::c_long
        {
            ulidgen_r(&raw mut ulid as *mut ::core::ffi::c_char);
            printf(
                b"%s %s\0" as *const u8 as *const ::core::ffi::c_char,
                &raw mut ulid as *mut ::core::ffi::c_char,
                line,
            );
        }
    } else {
        let mut i = 0 as ::core::ffi::c_long;
        while i < n {
            ulidgen_r(&raw mut ulid as *mut ::core::ffi::c_char);
            puts(&raw mut ulid as *mut ::core::ffi::c_char);
            i += 1;
        }
    }
    fflush(::core::ptr::null_mut::<FILE>());
    exit((ferror(stdout) != 0) as ::core::ffi::c_int);
}
pub fn main() {
    let mut args_strings: Vec<Vec<u8>> = ::std::env::args()
        .map(|arg| {
            ::std::ffi::CString::new(arg)
                .expect("Failed to convert argument into CString.")
                .into_bytes_with_nul()
        })
        .collect();
    let mut args_ptrs: Vec<*mut ::core::ffi::c_char> = args_strings
        .iter_mut()
        .map(|arg| arg.as_mut_ptr() as *mut ::core::ffi::c_char)
        .chain(::core::iter::once(::core::ptr::null_mut()))
        .collect();
    unsafe {
        ::std::process::exit(
            main_0(
                (args_ptrs.len() - 1) as ::core::ffi::c_int,
                args_ptrs.as_mut_ptr() as *mut *mut ::core::ffi::c_char,
            ) as i32,
        )
    }
}
