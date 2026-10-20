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
// Review of the certificate (independent review, R820-2): a place reached
// through a pointer LOADED from a formal is not inside that formal's object.
#[repr(C)]
pub struct Node {
    pub next: i32,
}
#[repr(C)]
pub struct List {
    pub head: *mut Node,
}
#[no_mangle]
pub unsafe extern "C" fn link(mut l: *mut List, mut n: *mut i32) {
    two(&mut (*(*l).head).next, n);
}
// A formal assigned inside a closure of the entry.
#[no_mangle]
pub unsafe extern "C" fn in_closure(mut p: *mut i32, mut q: *mut i32) {
    let mut f = || p = q;
    f();
    two(p, q);
}
// An entry the program calls through an extern declaration of its own symbol.
#[no_mangle]
pub unsafe extern "C" fn by_symbol(mut p: *mut i32, mut q: *mut i32) {
    two(p, q);
}
mod ffi {
    extern "C" {
        pub fn by_symbol(p: *mut i32, q: *mut i32);
    }
}
pub unsafe fn calls_by_symbol(p: *mut i32, q: *mut i32) {
    ffi::by_symbol(p, q);
}
