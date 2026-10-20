#![allow(dead_code, unused_mut, non_snake_case, unused_variables, static_mut_refs)]
// wave-5d 145c: two raw locals holding one pointer, handed to a callee that
// writes one and reads the other. C: `int *q = p; add(p, q);`.
unsafe fn add1(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
unsafe fn add2(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
unsafe fn add3(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
unsafe fn add4(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
unsafe fn add5(mut a: *mut i32, mut b: *mut i32) { *a += *b; }
pub unsafe fn copy_of_copy() {
    let mut x: [i32; 4] = [0; 4];
    let p1 = x.as_mut_ptr();
    let p2 = x.as_mut_ptr();
    let q1 = p1;
    let q2 = p2;
    add1(q1, q2);
}
pub unsafe fn copy_of_offset() {
    let mut x: [i32; 4] = [0; 4];
    let p = x.as_mut_ptr().offset(1);
    let q = p;
    add2(p, q);
}
pub unsafe fn copy_of_param(a: *mut i32, n: isize) {
    let p = a.offset(n);
    let q = p;
    add3(p, q);
}
pub unsafe fn same_raw_local_twice(a: *mut i32, n: isize) {
    let p = a.offset(n);
    add4(p, p);
}
pub unsafe fn copies_of_two_arrays() {
    let mut x: [i32; 4] = [0; 4];
    let mut y: [i32; 4] = [0; 4];
    let p = x.as_mut_ptr();
    let q = y.as_mut_ptr();
    add5(p, q);
}
