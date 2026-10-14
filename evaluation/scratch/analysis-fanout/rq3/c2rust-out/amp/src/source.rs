extern "C" {
    fn memcpy(
        __dest: *mut ::core::ffi::c_void,
        __src: *const ::core::ffi::c_void,
        __n: size_t,
    ) -> *mut ::core::ffi::c_void;
    fn strcmp(
        __s1: *const ::core::ffi::c_char,
        __s2: *const ::core::ffi::c_char,
    ) -> ::core::ffi::c_int;
    fn strlen(__s: *const ::core::ffi::c_char) -> size_t;
    fn malloc(__size: size_t) -> *mut ::core::ffi::c_void;
    fn __assert_fail(
        __assertion: *const ::core::ffi::c_char,
        __file: *const ::core::ffi::c_char,
        __line: ::core::ffi::c_uint,
        __function: *const ::core::ffi::c_char,
    ) -> !;
    fn printf(__format: *const ::core::ffi::c_char, ...) -> ::core::ffi::c_int;
}
pub type size_t = usize;
pub type __uint32_t = u32;
pub type uint32_t = __uint32_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct amp_t {
    pub version: ::core::ffi::c_short,
    pub argc: ::core::ffi::c_short,
    pub buf: *mut ::core::ffi::c_char,
}
pub const NULL: *mut ::core::ffi::c_void = ::core::ptr::null_mut::<
    ::core::ffi::c_void,
>();
pub const __ASSERT_FUNCTION: [::core::ffi::c_char; 11] = unsafe {
    ::core::mem::transmute::<[u8; 11], [::core::ffi::c_char; 11]>(*b"int main()\0")
};
pub const AMP_VERSION: ::core::ffi::c_int = 1 as ::core::ffi::c_int;
unsafe extern "C" fn read_u32_be(mut buf: *mut ::core::ffi::c_char) -> uint32_t {
    let mut n: uint32_t = 0 as uint32_t;
    n = (n as ::core::ffi::c_uint
        | ((*buf.offset(0 as ::core::ffi::c_int as isize) as ::core::ffi::c_int)
            << 24 as ::core::ffi::c_int) as ::core::ffi::c_uint) as uint32_t;
    n = (n as ::core::ffi::c_uint
        | ((*buf.offset(1 as ::core::ffi::c_int as isize) as ::core::ffi::c_int)
            << 16 as ::core::ffi::c_int) as ::core::ffi::c_uint) as uint32_t;
    n = (n as ::core::ffi::c_uint
        | ((*buf.offset(2 as ::core::ffi::c_int as isize) as ::core::ffi::c_int)
            << 8 as ::core::ffi::c_int) as ::core::ffi::c_uint) as uint32_t;
    n = (n as ::core::ffi::c_uint
        | *buf.offset(3 as ::core::ffi::c_int as isize) as ::core::ffi::c_uint)
        as uint32_t;
    return n;
}
unsafe extern "C" fn write_u32_be(mut buf: *mut ::core::ffi::c_char, mut n: uint32_t) {
    *buf.offset(0 as ::core::ffi::c_int as isize) = (n >> 24 as ::core::ffi::c_int
        & 0xff as uint32_t) as ::core::ffi::c_char;
    *buf.offset(1 as ::core::ffi::c_int as isize) = (n >> 16 as ::core::ffi::c_int
        & 0xff as uint32_t) as ::core::ffi::c_char;
    *buf.offset(2 as ::core::ffi::c_int as isize) = (n >> 8 as ::core::ffi::c_int
        & 0xff as uint32_t) as ::core::ffi::c_char;
    *buf.offset(3 as ::core::ffi::c_int as isize) = (n & 0xff as uint32_t)
        as ::core::ffi::c_char;
}
#[no_mangle]
pub unsafe extern "C" fn amp_decode(
    mut msg: *mut amp_t,
    mut buf: *mut ::core::ffi::c_char,
) {
    (*msg).version = (*buf.offset(0 as ::core::ffi::c_int as isize) as ::core::ffi::c_int
        >> 4 as ::core::ffi::c_int) as ::core::ffi::c_short;
    (*msg).argc = (*buf.offset(0 as ::core::ffi::c_int as isize) as ::core::ffi::c_int
        & 0xf as ::core::ffi::c_int) as ::core::ffi::c_short;
    (*msg).buf = buf.offset(1 as ::core::ffi::c_int as isize);
}
#[no_mangle]
pub unsafe extern "C" fn amp_decode_arg(
    mut msg: *mut amp_t,
) -> *mut ::core::ffi::c_char {
    let mut len = read_u32_be((*msg).buf);
    (*msg).buf = (*msg).buf.offset(4 as ::core::ffi::c_int as isize);
    let mut buf = malloc(len as size_t) as *mut ::core::ffi::c_char;
    if buf.is_null() {
        return ::core::ptr::null_mut::<::core::ffi::c_char>();
    }
    memcpy(
        buf as *mut ::core::ffi::c_void,
        (*msg).buf as *const ::core::ffi::c_void,
        len as size_t,
    );
    (*msg).buf = (*msg).buf.offset(len as isize);
    return buf;
}
#[no_mangle]
pub unsafe extern "C" fn amp_encode(
    mut argv: *mut *mut ::core::ffi::c_char,
    mut argc: ::core::ffi::c_int,
) -> *mut ::core::ffi::c_char {
    let mut len: size_t = 1 as size_t;
    let vla = argc as usize;
    let mut lens: Vec<size_t> = ::std::vec::from_elem(0, vla);
    let mut i = 0 as ::core::ffi::c_int;
    while i < argc {
        len = (len as ::core::ffi::c_ulong).wrapping_add(4 as ::core::ffi::c_ulong)
            as size_t as size_t;
        *lens.as_mut_ptr().offset(i as isize) = strlen(*argv.offset(i as isize));
        len = (len as ::core::ffi::c_ulong)
            .wrapping_add(*lens.as_mut_ptr().offset(i as isize) as ::core::ffi::c_ulong)
            as size_t as size_t;
        i += 1;
    }
    let mut buf = malloc(len) as *mut ::core::ffi::c_char;
    let mut ret = buf;
    if buf.is_null() {
        return ::core::ptr::null_mut::<::core::ffi::c_char>();
    }
    let fresh0 = buf;
    buf = buf.offset(1);
    *fresh0 = (AMP_VERSION << 4 as ::core::ffi::c_int | argc) as ::core::ffi::c_char;
    let mut i_0 = 0 as ::core::ffi::c_int;
    while i_0 < argc {
        let mut len_0: size_t = *lens.as_mut_ptr().offset(i_0 as isize);
        write_u32_be(buf, len_0 as uint32_t);
        buf = buf.offset(4 as ::core::ffi::c_int as isize);
        memcpy(
            buf as *mut ::core::ffi::c_void,
            *argv.offset(i_0 as isize) as *const ::core::ffi::c_void,
            len_0,
        );
        buf = buf.offset(len_0 as isize);
        i_0 += 1;
    }
    return ret;
}
unsafe fn main_0() -> ::core::ffi::c_int {
    let mut args: [*mut ::core::ffi::c_char; 3] = [
        b"some\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
        b"stuff\0" as *const u8 as *const ::core::ffi::c_char
            as *mut ::core::ffi::c_char,
        b"here\0" as *const u8 as *const ::core::ffi::c_char as *mut ::core::ffi::c_char,
    ];
    let mut buf = amp_encode(
        &raw mut args as *mut *mut ::core::ffi::c_char,
        3 as ::core::ffi::c_int,
    );
    let mut msg = amp_t {
        version: 0 as ::core::ffi::c_short,
        argc: 0,
        buf: ::core::ptr::null_mut::<::core::ffi::c_char>(),
    };
    amp_decode(&raw mut msg, buf);
    if 1 as ::core::ffi::c_int == msg.version as ::core::ffi::c_int {} else {
        __assert_fail(
            b"1 == msg.version\0" as *const u8 as *const ::core::ffi::c_char,
            b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
            145 as ::core::ffi::c_uint,
            __ASSERT_FUNCTION.as_ptr(),
        );
    }
    'c_2584: {
        if 1 as ::core::ffi::c_int == msg.version as ::core::ffi::c_int {} else {
            __assert_fail(
                b"1 == msg.version\0" as *const u8 as *const ::core::ffi::c_char,
                b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                145 as ::core::ffi::c_uint,
                __ASSERT_FUNCTION.as_ptr(),
            );
        }
    };
    if 3 as ::core::ffi::c_int == msg.argc as ::core::ffi::c_int {} else {
        __assert_fail(
            b"3 == msg.argc\0" as *const u8 as *const ::core::ffi::c_char,
            b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
            146 as ::core::ffi::c_uint,
            __ASSERT_FUNCTION.as_ptr(),
        );
    }
    'c_2543: {
        if 3 as ::core::ffi::c_int == msg.argc as ::core::ffi::c_int {} else {
            __assert_fail(
                b"3 == msg.argc\0" as *const u8 as *const ::core::ffi::c_char,
                b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                146 as ::core::ffi::c_uint,
                __ASSERT_FUNCTION.as_ptr(),
            );
        }
    };
    let mut i = 0 as ::core::ffi::c_int;
    while i < msg.argc as ::core::ffi::c_int {
        let mut arg = amp_decode_arg(&raw mut msg);
        match i {
            0 => {
                if 0 as ::core::ffi::c_int
                    == strcmp(b"some\0" as *const u8 as *const ::core::ffi::c_char, arg)
                {} else {
                    __assert_fail(
                        b"0 == strcmp(\"some\", arg)\0" as *const u8
                            as *const ::core::ffi::c_char,
                        b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                        153 as ::core::ffi::c_uint,
                        __ASSERT_FUNCTION.as_ptr(),
                    );
                }
                'c_2484: {
                    if 0 as ::core::ffi::c_int
                        == strcmp(
                            b"some\0" as *const u8 as *const ::core::ffi::c_char,
                            arg,
                        )
                    {} else {
                        __assert_fail(
                            b"0 == strcmp(\"some\", arg)\0" as *const u8
                                as *const ::core::ffi::c_char,
                            b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                            153 as ::core::ffi::c_uint,
                            __ASSERT_FUNCTION.as_ptr(),
                        );
                    }
                };
            }
            1 => {
                if 0 as ::core::ffi::c_int
                    == strcmp(b"stuff\0" as *const u8 as *const ::core::ffi::c_char, arg)
                {} else {
                    __assert_fail(
                        b"0 == strcmp(\"stuff\", arg)\0" as *const u8
                            as *const ::core::ffi::c_char,
                        b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                        156 as ::core::ffi::c_uint,
                        __ASSERT_FUNCTION.as_ptr(),
                    );
                }
                'c_2431: {
                    if 0 as ::core::ffi::c_int
                        == strcmp(
                            b"stuff\0" as *const u8 as *const ::core::ffi::c_char,
                            arg,
                        )
                    {} else {
                        __assert_fail(
                            b"0 == strcmp(\"stuff\", arg)\0" as *const u8
                                as *const ::core::ffi::c_char,
                            b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                            156 as ::core::ffi::c_uint,
                            __ASSERT_FUNCTION.as_ptr(),
                        );
                    }
                };
            }
            2 => {
                if 0 as ::core::ffi::c_int
                    == strcmp(b"here\0" as *const u8 as *const ::core::ffi::c_char, arg)
                {} else {
                    __assert_fail(
                        b"0 == strcmp(\"here\", arg)\0" as *const u8
                            as *const ::core::ffi::c_char,
                        b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                        159 as ::core::ffi::c_uint,
                        __ASSERT_FUNCTION.as_ptr(),
                    );
                }
                'c_2359: {
                    if 0 as ::core::ffi::c_int
                        == strcmp(
                            b"here\0" as *const u8 as *const ::core::ffi::c_char,
                            arg,
                        )
                    {} else {
                        __assert_fail(
                            b"0 == strcmp(\"here\", arg)\0" as *const u8
                                as *const ::core::ffi::c_char,
                            b"source.c\0" as *const u8 as *const ::core::ffi::c_char,
                            159 as ::core::ffi::c_uint,
                            __ASSERT_FUNCTION.as_ptr(),
                        );
                    }
                };
            }
            _ => {}
        }
        i += 1;
    }
    printf(b"ok\n\0" as *const u8 as *const ::core::ffi::c_char);
    return 0 as ::core::ffi::c_int;
}
pub fn main() {
    unsafe { ::std::process::exit(main_0() as i32) }
}
