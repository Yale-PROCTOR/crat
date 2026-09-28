#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
pub mod libc { pub type c_int = i32; pub type c_uint = u32; pub type c_long = i64; pub type c_ulong = u64; pub type c_char = i8; }
pub type uint8_t = u8; pub type uint16_t = u16; pub type uint32_t = u32; pub type uint64_t = u64; pub type size_t = libc::c_ulong;
#[inline(always)]
unsafe extern "C" fn NextTableBitSize(count: *const uint16_t,
    mut len: libc::c_int, mut root_bits: libc::c_int)
    -> libc::c_int {
    let mut left = (1 as libc::c_int) << len - root_bits;
    while len < 15 as libc::c_int {
        left -= *count.offset(len as isize) as libc::c_int;
        if left <= 0 as libc::c_int { break; }
        len += 1;
        left <<= 1 as libc::c_int;
    }
    return len - root_bits;
}
