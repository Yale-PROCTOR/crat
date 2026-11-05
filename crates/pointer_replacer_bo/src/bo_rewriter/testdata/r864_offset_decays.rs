#![allow(dead_code, unused_mut, non_snake_case, unused_variables, static_mut_refs)]
// R864-1 (b) beyond the top of an argument (wave-5d 145a): C `add(&x[1], &x[1])`,
// `p = x; q = x; add(p, q)`, and the reborrowed element, all of one local array.
unsafe fn add1(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
unsafe fn add2(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
unsafe fn add4(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
unsafe fn add5(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
pub unsafe fn off_local() {
    let mut x: [i32; 4] = [0; 4];
    add1(x.as_mut_ptr().offset(1), x.as_mut_ptr().offset(1));
}
pub unsafe fn copies() {
    let mut x: [i32; 4] = [0; 4];
    let mut p = x.as_mut_ptr();
    let mut q = x.as_mut_ptr();
    add2(p, q);
}
pub unsafe fn reborrow_elem() {
    let mut x: [i32; 4] = [0; 4];
    add4(&mut *x.as_mut_ptr().offset(1), &mut *x.as_mut_ptr().offset(1));
}
pub unsafe fn distinct_offsets() {
    let mut x: [i32; 4] = [0; 4];
    let mut y: [i32; 4] = [0; 4];
    add5(x.as_mut_ptr().offset(1), y.as_mut_ptr().offset(1));
}
