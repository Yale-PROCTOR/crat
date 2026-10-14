extern "C" {
    pub type _IO_wide_data;
    pub type _IO_codecvt;
    pub type _IO_marker;
    static mut stderr: *mut FILE;
    fn fprintf(
        __stream: *mut FILE,
        __format: *const ::core::ffi::c_char,
        ...
    ) -> ::core::ffi::c_int;
    fn printf(__format: *const ::core::ffi::c_char, ...) -> ::core::ffi::c_int;
}
pub type size_t = usize;
pub type __uint8_t = u8;
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
pub type uint8_t = __uint8_t;
pub type u4 = uint8_t;
pub const true_0: ::core::ffi::c_int = 1 as ::core::ffi::c_int;
pub const false_0: ::core::ffi::c_int = 0 as ::core::ffi::c_int;
unsafe extern "C" fn nand(mut a: bool, mut b: bool) -> bool {
    return !(a as ::core::ffi::c_int != 0 && b as ::core::ffi::c_int != 0);
}
unsafe extern "C" fn not(mut a: bool) -> bool {
    return nand(a, true_0 != 0);
}
unsafe extern "C" fn or(mut a: bool, mut b: bool) -> bool {
    return nand(not(a), not(b));
}
unsafe extern "C" fn and(mut a: bool, mut b: bool) -> bool {
    return not(nand(a, b));
}
unsafe extern "C" fn xor(mut a: bool, mut b: bool) -> bool {
    return or(and(a, not(b)), and(not(a), b));
}
unsafe extern "C" fn add_bit(
    mut a: bool,
    mut b: bool,
    mut carry: bool,
    mut carry_result: *mut bool,
) -> bool {
    *carry_result = and(or(a, b), or(and(a, b), carry));
    return xor(xor(a, b), carry);
}
unsafe extern "C" fn half_sub(
    mut a: bool,
    mut b: bool,
    mut carry_result: *mut bool,
) -> bool {
    *carry_result = and(not(a), b);
    return xor(a, b);
}
unsafe extern "C" fn sub_bit(
    mut a: bool,
    mut b: bool,
    mut carry: bool,
    mut carry_result: *mut bool,
) -> bool {
    let mut b1: bool = false;
    let mut b2: bool = false;
    let mut result = half_sub(half_sub(a, b, &raw mut b1), carry, &raw mut b2);
    *carry_result = or(b1, b2);
    return result;
}
#[no_mangle]
pub unsafe extern "C" fn bll(mut x: bool) -> *const ::core::ffi::c_char {
    if x {
        return b"true\0" as *const u8 as *const ::core::ffi::c_char;
    }
    return b"false\0" as *const u8 as *const ::core::ffi::c_char;
}
#[no_mangle]
pub unsafe extern "C" fn print_add_bit(mut a: bool, mut b: bool, mut carry: bool) {
    printf(b"a      : %s\n\0" as *const u8 as *const ::core::ffi::c_char, bll(a));
    printf(b"b      : %s\n\0" as *const u8 as *const ::core::ffi::c_char, bll(b));
    printf(b"carry  : %s\n\0" as *const u8 as *const ::core::ffi::c_char, bll(carry));
    let mut res_carry: bool = false;
    printf(b"result :\n\0" as *const u8 as *const ::core::ffi::c_char);
    printf(
        b"  bit  : %s\n\0" as *const u8 as *const ::core::ffi::c_char,
        bll(add_bit(a, b, carry, &raw mut res_carry)),
    );
    printf(
        b"  carry: %s\n\0" as *const u8 as *const ::core::ffi::c_char,
        bll(res_carry),
    );
}
pub const U4_MAX: ::core::ffi::c_int = 0o17 as ::core::ffi::c_int;
#[no_mangle]
pub unsafe extern "C" fn add_u4(mut a: u4, mut b: u4) -> u4 {
    let mut carry = false_0 != 0;
    let mut result: u4 = 0 as u4;
    result = (result as ::core::ffi::c_int
        | (add_bit(
            a as ::core::ffi::c_int >> 0 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 0 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 0 as ::core::ffi::c_int) as u4;
    result = (result as ::core::ffi::c_int
        | (add_bit(
            a as ::core::ffi::c_int >> 1 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 1 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 1 as ::core::ffi::c_int) as u4;
    result = (result as ::core::ffi::c_int
        | (add_bit(
            a as ::core::ffi::c_int >> 2 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 2 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 2 as ::core::ffi::c_int) as u4;
    result = (result as ::core::ffi::c_int
        | (add_bit(
            a as ::core::ffi::c_int >> 3 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 3 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 3 as ::core::ffi::c_int) as u4;
    return result;
}
#[no_mangle]
pub unsafe extern "C" fn sub_u4(mut a: u4, mut b: u4) -> u4 {
    let mut carry = false_0 != 0;
    let mut result: u4 = 0 as u4;
    result = (result as ::core::ffi::c_int
        | (sub_bit(
            a as ::core::ffi::c_int >> 0 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 0 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 0 as ::core::ffi::c_int) as u4;
    result = (result as ::core::ffi::c_int
        | (sub_bit(
            a as ::core::ffi::c_int >> 1 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 1 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 1 as ::core::ffi::c_int) as u4;
    result = (result as ::core::ffi::c_int
        | (sub_bit(
            a as ::core::ffi::c_int >> 2 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 2 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 2 as ::core::ffi::c_int) as u4;
    result = (result as ::core::ffi::c_int
        | (sub_bit(
            a as ::core::ffi::c_int >> 3 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            b as ::core::ffi::c_int >> 3 as ::core::ffi::c_int
                & 0o1 as ::core::ffi::c_int != 0,
            carry,
            &raw mut carry,
        ) as u4 as ::core::ffi::c_int) << 3 as ::core::ffi::c_int) as u4;
    return result;
}
#[no_mangle]
pub unsafe extern "C" fn check_add() -> bool {
    let mut a: u4 = 0 as u4;
    while (a as ::core::ffi::c_int) < U4_MAX {
        let mut b: u4 = 0 as u4;
        while (b as ::core::ffi::c_int) < U4_MAX {
            let mut my = add_u4(a, b);
            let mut h: u4 = (a as ::core::ffi::c_int + b as ::core::ffi::c_int
                & 0o17 as ::core::ffi::c_int) as u4;
            if my as ::core::ffi::c_int != h as ::core::ffi::c_int {
                fprintf(
                    stderr,
                    b"ERROR: Add failed with %d+%d:\n\0" as *const u8
                        as *const ::core::ffi::c_char,
                    a as ::core::ffi::c_int,
                    b as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"  My  : %d\n\0" as *const u8 as *const ::core::ffi::c_char,
                    my as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"  Real: %d\n\0" as *const u8 as *const ::core::ffi::c_char,
                    my as ::core::ffi::c_int,
                );
                return false_0 != 0;
            }
            b = b.wrapping_add(1);
        }
        a = a.wrapping_add(1);
    }
    fprintf(
        stderr,
        b"Add works correctly\n\0" as *const u8 as *const ::core::ffi::c_char,
    );
    return true_0 != 0;
}
#[no_mangle]
pub unsafe extern "C" fn check_sub() -> bool {
    let mut a: u4 = 0 as u4;
    while (a as ::core::ffi::c_int) < U4_MAX {
        let mut b: u4 = 0 as u4;
        while (b as ::core::ffi::c_int) < U4_MAX {
            let mut my = sub_u4(a, b);
            let mut h: u4 = (a as ::core::ffi::c_int - b as ::core::ffi::c_int
                & 0o17 as ::core::ffi::c_int) as u4;
            if my as ::core::ffi::c_int != h as ::core::ffi::c_int {
                fprintf(
                    stderr,
                    b"ERROR: Sub failed with %d-%d:\n\0" as *const u8
                        as *const ::core::ffi::c_char,
                    a as ::core::ffi::c_int,
                    b as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"  My  : %d\n\0" as *const u8 as *const ::core::ffi::c_char,
                    my as ::core::ffi::c_int,
                );
                fprintf(
                    stderr,
                    b"  Real: %d\n\0" as *const u8 as *const ::core::ffi::c_char,
                    h as ::core::ffi::c_int,
                );
                return false_0 != 0;
            }
            b = b.wrapping_add(1);
        }
        a = a.wrapping_add(1);
    }
    fprintf(
        stderr,
        b"Sub works correctly\n\0" as *const u8 as *const ::core::ffi::c_char,
    );
    return true_0 != 0;
}
unsafe fn main_0() -> ::core::ffi::c_int {
    check_add();
    check_sub();
    return 0 as ::core::ffi::c_int;
}
pub fn main() {
    unsafe { ::std::process::exit(main_0() as i32) }
}
