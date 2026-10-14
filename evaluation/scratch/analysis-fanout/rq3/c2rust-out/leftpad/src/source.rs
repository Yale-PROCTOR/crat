extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    static mut stderr: *mut FILE;
    fn fputs(__s: *const ::core::ffi::c_char, __stream: *mut FILE) -> ::core::ffi::c_int;
    fn puts(__s: *const ::core::ffi::c_char) -> ::core::ffi::c_int;
    fn strtol(
        __nptr: *const ::core::ffi::c_char,
        __endptr: *mut *mut ::core::ffi::c_char,
        __base: ::core::ffi::c_int,
    ) -> ::core::ffi::c_long;
    fn malloc(__size: size_t) -> *mut ::core::ffi::c_void;
}
pub type size_t = usize;
pub type __off_t = ::core::ffi::c_long;
pub type __off64_t = ::core::ffi::c_long;
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
pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<
    ::core::ffi::c_void,
>();
#[no_mangle]
pub unsafe extern "C" fn leftpad(
    mut str: *const ::core::ffi::c_char,
    mut padding: *const ::core::ffi::c_char,
    mut min_len: size_t,
    mut dest: *mut ::core::ffi::c_char,
    mut dest_sz: size_t,
) -> size_t {
    let mut i: size_t = 0 as size_t;
    let mut str_len: size_t = 0 as size_t;
    let mut dest_len: size_t = 0 as size_t;
    let mut npad: size_t = 0 as size_t;
    while !str.is_null() && *str.offset(str_len as isize) as ::core::ffi::c_int != 0 {
        str_len = str_len.wrapping_add(1);
    }
    if padding.is_null() || *padding.offset(0 as ::core::ffi::c_int as isize) == 0 {
        padding = b" \0" as *const u8 as *const ::core::ffi::c_char;
    }
    if str_len < min_len {
        npad = min_len.wrapping_sub(str_len);
    }
    if dest.is_null() || dest_sz == 0 {
        return str_len.wrapping_add(npad);
    }
    while dest_len < npad && dest_len < dest_sz.wrapping_sub(1 as size_t) {
        let fresh0 = i;
        i = i.wrapping_add(1);
        let fresh1 = dest_len;
        dest_len = dest_len.wrapping_add(1);
        let ref mut fresh2 = *dest.offset(fresh1 as isize);
        *fresh2 = *padding.offset(fresh0 as isize);
        if *fresh2 == 0 {
            *dest.offset(dest_len.wrapping_sub(1 as size_t) as isize) = *padding
                .offset(0 as ::core::ffi::c_int as isize);
            i = 1 as size_t;
        }
    }
    i = 0 as size_t;
    while i < str_len && dest_len < dest_sz.wrapping_sub(1 as size_t) {
        let fresh3 = dest_len;
        dest_len = dest_len.wrapping_add(1);
        *dest.offset(fresh3 as isize) = *str.offset(i as isize);
        i = i.wrapping_add(1);
    }
    *dest.offset(dest_len as isize) = '\0' as i32 as ::core::ffi::c_char;
    return dest_len;
}
unsafe fn main_0(
    mut argc: ::core::ffi::c_int,
    mut argv: *mut *mut ::core::ffi::c_char,
) -> ::core::ffi::c_int {
    let mut min_len: ::core::ffi::c_long = 0;
    let mut padding = b" \0" as *const u8 as *const ::core::ffi::c_char;
    let mut end = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut buf = ::core::ptr::null_mut::<::core::ffi::c_char>();
    let mut buf_len: size_t = 0;
    if argc == 4 as ::core::ffi::c_int {
        padding = *argv.offset(3 as ::core::ffi::c_int as isize);
    } else if argc != 3 as ::core::ffi::c_int {
        fputs(
            b"usage: leftpad string length [padding]\n\0" as *const u8
                as *const ::core::ffi::c_char,
            stderr,
        );
        return 1 as ::core::ffi::c_int;
    }
    min_len = strtol(
        *argv.offset(2 as ::core::ffi::c_int as isize),
        &raw mut end,
        10 as ::core::ffi::c_int,
    );
    if *(*argv.offset(2 as ::core::ffi::c_int as isize))
        .offset(0 as ::core::ffi::c_int as isize) == 0
        || *end.offset(0 as ::core::ffi::c_int as isize) as ::core::ffi::c_int != 0
        || min_len < 0 as ::core::ffi::c_long
    {
        fputs(
            b"leftpad: invalid length\0" as *const u8 as *const ::core::ffi::c_char,
            stderr,
        );
        return 1 as ::core::ffi::c_int;
    }
    buf_len = leftpad(
        *argv.offset(1 as ::core::ffi::c_int as isize),
        padding,
        min_len as size_t,
        ::core::ptr::null_mut::<::core::ffi::c_char>(),
        0 as size_t,
    );
    buf = malloc(buf_len) as *mut ::core::ffi::c_char;
    if buf.is_null() {
        fputs(
            b"leftpad: out of memory\0" as *const u8 as *const ::core::ffi::c_char,
            stderr,
        );
        return 1 as ::core::ffi::c_int;
    }
    leftpad(
        *argv.offset(1 as ::core::ffi::c_int as isize),
        padding,
        min_len as size_t,
        buf,
        buf_len.wrapping_add(1 as size_t),
    );
    puts(buf);
    return 0 as ::core::ffi::c_int;
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
