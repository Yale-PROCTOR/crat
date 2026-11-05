#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments, static_mut_refs)]
// R838 (relay 178 item 2): `add(G1, G2)` where `G2` may hold `G1`'s pointer:
// not shown disjoint, so both of `add`'s formals stay raw (R833-1). Control:
// `add2(x, y)` from an entry with two formals, the scope's disjoint pair.
pub static mut G1: *mut i32 = 0 as *mut i32;
pub static mut G2: *mut i32 = 0 as *mut i32;
pub unsafe fn set(mut p: *mut i32, mut q: *mut i32) {
    G1 = p;
    G2 = if q.is_null() { p } else { q };
}
unsafe fn add(mut a: *mut i32, mut b: *mut i32) {
    *a += *b;
}
pub unsafe fn undecided() {
    add(G1, G2);
}
unsafe fn add2(mut a: *mut i32, mut b: *mut i32) {
    *a += *b;
}
#[no_mangle]
pub unsafe extern "C" fn certified(mut x: *mut i32, mut y: *mut i32) {
    add2(x, y);
}
