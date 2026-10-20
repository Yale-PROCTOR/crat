#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments, static_mut_refs)]
// R838 (era-5c 148): A5's origin evidence reads two values loaded from memory as
// disjoint origins whatever the program stored there. `add(G1, G2)` with
// `G2 = if q.is_null() { p } else { q }`: G2 may hold G1's pointer.
pub static mut G1: *mut i32 = 0 as *mut i32;
pub static mut G2: *mut i32 = 0 as *mut i32;
pub static mut ARR1: [i32; 4] = [0; 4];
pub static mut ARR2: [i32; 4] = [0; 4];
#[repr(C)]
pub struct S {
    pub a: *mut i32,
    pub b: *mut i32,
}
pub unsafe fn set(mut p: *mut i32, mut q: *mut i32) {
    G1 = p;
    G2 = if q.is_null() { p } else { q };
}
unsafe fn add(mut a: *mut i32, mut b: *mut i32) {
    *a += *b;
}
pub unsafe fn statics() {
    add(G1, G2);
}
pub unsafe fn fields(mut s: *mut S) {
    add((*s).a, (*s).b);
}
pub unsafe fn derefs(mut p: *mut *mut i32, mut q: *mut *mut i32) {
    let mut x = *p;
    add(x, *q);
}
pub unsafe fn locals_loaded(mut p: *mut *mut i32, mut q: *mut *mut i32) {
    let mut x = *p;
    let mut y = *q;
    add(x, y);
}
// Controls: two static arrays' addresses; two locals' addresses; an entry's
// two formals.
pub unsafe fn arrays() {
    add(ARR1.as_mut_ptr(), ARR2.as_mut_ptr());
}
pub unsafe fn locals() {
    let mut l1: i32 = 0;
    let mut l2: i32 = 0;
    add(&mut l1, &mut l2);
}
#[no_mangle]
pub unsafe extern "C" fn entry(mut x: *mut i32, mut y: *mut i32) {
    add(x, y);
}
// The narrowing (wave-5d report 137 §5): a loaded pointer beside the address of
// a scalar local whose address never reaches memory keeps the proof; the same
// local stored once, handed to a callee that keeps it, or bound by `ref` does not.
unsafe fn keep(mut r: *mut i32) {
    G1 = r;
}
pub unsafe fn unescaped(mut p: *mut *mut i32) {
    let mut l: i32 = 0;
    add(*p, &mut l);
}
pub unsafe fn stored(mut p: *mut *mut i32) {
    let mut l: i32 = 0;
    *p = &mut l;
    add(*p, &mut l);
}
pub unsafe fn kept() {
    let mut l: i32 = 0;
    keep(&mut l);
    add(G1, &mut l);
}
pub unsafe fn ref_bound(mut p: *mut *mut i32) {
    let mut l: i32 = 0;
    let ref mut r = l;
    *r = 1;
    add(*p, &mut l);
}
// era-5c 148a's executed shapes: one static passed twice, a static copied into
// another, two dereferences of pointers a caller makes equal.
pub unsafe fn same_static(mut p: *mut i32) {
    G1 = p;
    add(G1, G1);
}
pub unsafe fn copied_static(mut p: *mut i32) {
    G1 = p;
    G2 = G1;
    add(G1, G2);
}
pub unsafe fn derefs_equal(mut p: *mut *mut i32, mut q: *mut *mut i32) {
    add(*p, *q);
}
pub unsafe fn derefs_equal_caller(mut x: *mut *mut i32) {
    derefs_equal(x, x);
}
// The independent review (R820-2): a loop repeats the call, and an `if let ref`
// takes the address too.
pub unsafe fn in_loop(mut p: *mut *mut i32, mut n: i32) {
    let mut l: i32 = 0;
    while n > 0 {
        add(*p, &mut l);
        n -= 1;
    }
}
pub unsafe fn if_let_ref(mut p: *mut *mut i32, mut pp: *mut *mut i32) {
    let mut l: i32 = 0;
    if let ref mut r = l {
        *pp = r;
    }
    add(*p, &mut l);
}
// Relay 180 item 4: a callee that may keep the address it receives.
unsafe fn keepadd(mut a: *mut i32, mut b: *mut i32) {
    G1 = b;
    *a += *b;
}
pub unsafe fn kept_once(mut p: *mut *mut i32) {
    let mut l: i32 = 0;
    keepadd(*p, &mut l);
}
