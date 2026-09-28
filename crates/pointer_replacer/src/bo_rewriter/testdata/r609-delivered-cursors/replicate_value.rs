#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
pub mod libc { pub type c_int = i32; pub type c_uint = u32; pub type c_long = i64; pub type c_ulong = u64; pub type c_char = i8; pub type c_short = i16; pub use core::ffi::c_void; }
pub type uint8_t = u8; pub type uint16_t = u16; pub type uint32_t = u32; pub type uint64_t = u64; pub type size_t = libc::c_ulong;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct HuffmanCode {
    pub bits: uint8_t,
    pub value: uint16_t,
}
#[inline(always)]
unsafe extern "C" fn ReplicateValue(mut table: *mut HuffmanCode,
    mut step: libc::c_int, mut end: libc::c_int,
    mut code: HuffmanCode) {
    loop {
        end -= step;
        *table.offset(end as isize) = code;
        if !(end > 0 as libc::c_int) { break; }
    };
}
