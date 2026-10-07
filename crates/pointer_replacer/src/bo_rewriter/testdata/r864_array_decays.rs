#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments, static_mut_refs)]
// R864-1 (b) (fan-out 081): libzahl zmul's zadd(b_low.as_mut_ptr(), b_low.as_mut_ptr(), …)
// read "proven disjoint". Two decays of one array are one object.
pub static mut SA: [i32; 4] = [0; 4];
pub static mut SB: [i32; 4] = [0; 4];
unsafe fn add(mut a: *mut i32, mut b: *mut i32) {
    *a += *b;
}
pub unsafe fn same_local() {
    let mut x: [i32; 4] = [0; 4];
    add(x.as_mut_ptr(), x.as_mut_ptr());
}
pub unsafe fn same_static() {
    add(SA.as_mut_ptr(), SA.as_mut_ptr());
}
pub unsafe fn same_local_reborrowed() {
    let mut x: [i32; 4] = [0; 4];
    add(&mut *x.as_mut_ptr(), x.as_mut_ptr());
}
pub unsafe fn distinct_locals() {
    let mut x: [i32; 4] = [0; 4];
    let mut y: [i32; 4] = [0; 4];
    add(x.as_mut_ptr(), y.as_mut_ptr());
}
pub unsafe fn distinct_statics() {
    add(SA.as_mut_ptr(), SB.as_mut_ptr());
}
pub unsafe fn decay_beside_a_pointer(mut p: *mut i32) {
    let mut x: [i32; 4] = [0; 4];
    add(x.as_mut_ptr(), p);
}
pub unsafe fn decays_through_references(mut r: &mut [i32; 4], mut s: &mut [i32; 4]) {
    add(r.as_mut_ptr(), s.as_mut_ptr());
}
pub unsafe fn offsets_of_one_local() {
    let mut x: [i32; 4] = [0; 4];
    add(x.as_mut_ptr().offset(1), x.as_mut_ptr().offset(1));
}
pub unsafe fn copies_of_one_local() {
    let mut x: [i32; 4] = [0; 4];
    let mut p = x.as_mut_ptr();
    let mut q = x.as_mut_ptr().offset(2);
    p = p.offset(1);
    add(p, q);
}
pub unsafe fn reborrowed_offsets_of_one_local() {
    let mut x: [i32; 4] = [0; 4];
    add(&mut *x.as_mut_ptr().offset(1), &mut *x.as_mut_ptr().offset(1));
}
pub unsafe fn offsets_of_two_locals() {
    let mut x: [i32; 4] = [0; 4];
    let mut y: [i32; 4] = [0; 4];
    add(x.as_mut_ptr().offset(1), y.as_mut_ptr().offset(1));
}
pub unsafe fn a_copy_also_assigned_elsewhere(mut r: *mut i32) {
    let mut x: [i32; 4] = [0; 4];
    let mut p = x.as_mut_ptr();
    p = r;
    add(p, x.as_mut_ptr());
}
pub unsafe fn integer_arithmetic_on_a_decay(mut d: usize) {
    let mut x: [i32; 4] = [0; 4];
    let mut y: [i32; 4] = [0; 4];
    add((x.as_mut_ptr() as usize).wrapping_add(d) as *mut i32, y.as_mut_ptr());
}
pub unsafe fn diamond_copies_of_one_local() {
    let mut x: [i32; 4] = [0; 4];
    let q = x.as_mut_ptr();
    let mut p = q;
    p = q;
    let r = x.as_mut_ptr();
    let mut s = r;
    s = r;
    add(p, s);
}
