#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
// R821-3 item 1 (wave-6o 123): the scope's certificate is by the formals'
// roots. One formal handed twice, or two places inside one formal, are one
// outside object; a formal whose address is taken may be reassigned through it.
#[repr(C)]
pub struct P {
    pub x: i32,
    pub y: i32,
}
unsafe fn two(mut a: *mut i32, mut b: *mut i32) {
    *a = *b + 1;
}
#[no_mangle]
pub unsafe extern "C" fn distinct(mut p: *mut i32, mut q: *mut i32) {
    two(p, q);
}
#[no_mangle]
pub unsafe extern "C" fn twice(mut p: *mut i32) {
    two(p, p);
}
#[no_mangle]
pub unsafe extern "C" fn fields(mut p: *mut P) {
    two(&mut (*p).x, &mut (*p).y);
}
#[no_mangle]
pub unsafe extern "C" fn address_taken(mut p: *mut i32, mut q: *mut i32) {
    let mut pp: *mut *mut i32 = &mut p;
    *pp = q;
    two(p, q);
}
