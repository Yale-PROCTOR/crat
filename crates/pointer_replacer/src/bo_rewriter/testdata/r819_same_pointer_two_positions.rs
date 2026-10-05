#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
// R819-1 item 4: libzahl's `zmodmul → zmod(a, a, d)` shape. The same pointer is
// handed at two positions of one call, and the callee writes through one while
// it reads through the other: a proven overlap, so neither position may be a
// protected reference. `zmodpow` calls `zmod` with three distinct formals, so
// `zmod`'s formals convert unless the overlap holds them.
#[repr(C)]
pub struct Z {
    pub sign: i32,
    pub used: usize,
}
unsafe fn zmod(mut a: *mut Z, mut b: *mut Z, mut c: *mut Z) {
    (*a).sign = (*b).sign % ((*c).sign | 1);
    (*a).used = (*b).used;
}
unsafe fn zcmp(mut a: *mut Z, mut b: *mut Z) -> i32 {
    (*a).sign - (*b).sign
}
#[no_mangle]
pub unsafe extern "C" fn zmodmul(mut a: *mut Z, mut b: *mut Z, mut d: *mut Z) -> i32 {
    (*a).sign = (*b).sign;
    zmod(a, a, d);
    zcmp(b, b)
}
#[no_mangle]
pub unsafe extern "C" fn zmodpow(mut a: *mut Z, mut b: *mut Z, mut c: *mut Z) {
    zmod(a, b, c);
}
