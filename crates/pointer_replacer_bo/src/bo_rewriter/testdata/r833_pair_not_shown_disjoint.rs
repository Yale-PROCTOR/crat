#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments, static_mut_refs)]
// R833-1 (USER): controls of the pair rule. `add(G1, G2)` was meant as the
// undecided call, but the census world reads it proven disjoint (see the test).
pub static mut G1: *mut i32 = 0 as *mut i32;
pub static mut G2: *mut i32 = 0 as *mut i32;
// Both globals may hold one pointer: the proof cannot separate their pointees.
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
// Control: an entry no function calls hands two distinct formals (the scope's
// certificate proves them disjoint).
unsafe fn add2(mut a: *mut i32, mut b: *mut i32) {
    *a += *b;
}
#[no_mangle]
pub unsafe extern "C" fn certified(mut x: *mut i32, mut y: *mut i32) {
    add2(x, y);
}
// Control: both members only read.
unsafe fn sum(mut a: *mut i32, mut b: *mut i32) -> i32 {
    *a + *b
}
pub unsafe fn readers() -> i32 {
    sum(G1, G2)
}
