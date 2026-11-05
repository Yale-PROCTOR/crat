#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments, static_mut_refs)]
// R864-1 (a) (fan-out 081): libzahl's zsqr(a: *mut Z, b: &mut Z) called as
// zsqr(T.as_mut_ptr(), T.as_mut_ptr()) over one static array: `a` is model-Raw
// (a byte cast here), `b` converts, and the pair pass formed no pair. `b` is
// held raw beside it. (`zsqr(x, &mut *x)` is F2's already: `&mut *x` lies
// inside `x`.)
pub struct Z {
    pub used: i32,
    pub sign: i32,
}
pub static mut T: [Z; 1] = [Z { used: 0, sign: 0 }];
unsafe fn zsqr(mut a: *mut Z, mut b: *mut Z) {
    let mut used = (*b).used;
    *(a as *mut u8) = 0;
    (*a).used = used * 2;
    (*a).sign = (*b).sign;
}
pub unsafe fn caller() {
    zsqr(T.as_mut_ptr(), T.as_mut_ptr());
}
// Control: the reference side is a scalar local whose address the body takes
// only here, at a call no loop repeats: no pointer can hold it, `b` keeps its
// form. (A struct local is not read so: a field borrow also points into it.)
unsafe fn zsqr2(mut a: *mut Z, mut b: *mut i32) {
    let mut used = *b;
    *(a as *mut u8) = 0;
    (*a).used = used * 2;
}
pub unsafe fn control() {
    let mut local: i32 = 1;
    zsqr2(T.as_mut_ptr(), &mut local);
}
