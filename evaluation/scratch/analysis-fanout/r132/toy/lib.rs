//! r132 toy (relay 132): every kind, destination, exclusion and null-dominance case of the site counter.
//! Each expected site sits on a line tagged `// SITE:<tag>`; the expected rows are in expected.tsv (written before any
//! run). A line without a tag must produce no row: `n01_rawonly` and `n02_safe` produce none. The cases from t42 on
//! were added by the 10-10 review fixes (DESIGN.md §11), with their expected rows, before any run.
#![allow(dead_code, unused_variables, unused_mut, unused_unsafe, unused_assignments, non_camel_case_types)]
use std::ptr;

pub struct S {
    pub x: i32,
    pub q: *mut i32,
}
pub struct Holder<'a> {
    pub f: &'a mut i32,
}
pub struct BoxHolder {
    pub b: Option<Box<S>>,
}
pub struct Cur<'a> {
    base: &'a [i32],
    pos: usize,
}
pub struct QN {
    pub nw: *mut QN,
    pub v: i32,
}
pub struct Buf {
    pub vals: [i32; 4],
    pub v: Vec<i32>,
}
pub struct RS {
    pub r: &'static mut i32,
    pub b: Box<S>,
}
pub struct L {
    pub x: i32,
    pub next: *mut L,
}

extern "C" {
    fn strncmp(a: *const i8, b: *const i8, n: usize) -> i32;
    fn takes_raw(p: *mut i32);
    fn takes_rawc(p: *const i32);
}

pub fn safe_mut(r: &mut i32) {}
pub fn safe_opt(r: Option<&mut i32>) {}
pub fn safe_slice(s: &mut [i32]) {}
pub fn opaque() {}
pub unsafe fn qfree(node: Option<Box<QN>>) {}
pub unsafe fn __crat_safe_t54(b: Option<Box<S>>) -> i32 {
    match b {
        Some(b) => b.x,
        None => 0,
    }
}
macro_rules! deref_mut {
    ($p:expr) => {
        &mut *$p
    };
}

// ----- kind a: destinations

pub unsafe fn t01_decl(p: *mut i32) -> i32 {
    let r = &mut *p; // SITE:t01
    *r += 1;
    *r
}

pub unsafe fn t02_assign(p: *const i32, q: *const i32) -> i32 {
    let mut r: &i32 = &*p; // SITE:t02a
    r = &*q; // SITE:t02b
    *r
}

pub unsafe fn t03_ret<'a>(p: *mut i32) -> &'a mut i32 {
    &mut *p // SITE:t03
}

pub unsafe fn t04_call(p: *mut i32) {
    safe_mut(&mut *p); // SITE:t04
}

pub unsafe fn t05_some(p: *mut i32) {
    safe_opt(Some(&mut *p.offset(1))); // SITE:t05
}

pub unsafe fn t06_autoref(v: *mut Vec<i32>) {
    (*v).push(1); // SITE:t06
}

pub unsafe fn t07_field(h: &mut Holder<'static>, p: *mut i32) {
    h.f = &mut *p; // SITE:t07
}

pub unsafe fn t08_init(p: *mut i32) -> Holder<'static> {
    Holder { f: &mut *p } // SITE:t08
}

// ----- kind a: exclusions (the reference goes straight back to a raw pointer)

pub unsafe fn t09_excl(p: *mut i32) -> *mut i32 {
    &mut *p.offset(2) as *mut i32 // SITE:t09
}

pub unsafe fn t10_strncmp(s: *mut i8, t: *const i8) -> i32 {
    strncmp(&mut *s.offset(1), &*t, 3) // SITE:t10
}

pub unsafe fn t11_cast2(p: *mut i32) {
    takes_raw(&mut *p as *mut i32 as *mut i32); // SITE:t11
}

pub unsafe fn t12_arr(a: *mut [i32; 4]) -> *mut i32 {
    &mut *a as *mut i32 // SITE:t12
}

// ----- kind a: other destinations

pub unsafe fn t13_deref(p: *mut S) -> i32 {
    (&mut *p).x // SITE:t13
}

// ----- null dominance

pub unsafe fn t14_nd(p: *const i32) -> i32 {
    if !p.is_null() {
        let r = &*p; // SITE:t14
        return *r;
    }
    0
}

pub unsafe fn t15_early(p: *mut i32) -> Option<&'static mut i32> {
    if p.is_null() {
        return None;
    }
    p.as_mut() // SITE:t15
}

pub unsafe fn t16_unwrap(p: *const i32) -> i32 {
    *p.as_ref().unwrap() // SITE:t16
}

pub unsafe fn t17_iflet(p: *mut i32) {
    if let Some(r) = p.as_mut() { // SITE:t17
        *r = 1;
    }
}

pub unsafe fn t18_box(p: *mut S) {
    if !p.is_null() {
        drop(Box::from_raw(p)); // SITE:t18
    }
}

pub unsafe fn t19_dropped(p: *mut S) {
    let _ = Box::from_raw(p); // SITE:t19
}

pub unsafe fn t20_ne(p: *mut S) -> i32 {
    if p != ptr::null_mut() {
        let b = Box::from_raw(p); // SITE:t20
        return b.x;
    }
    0
}

pub unsafe fn t21_eq0(p: *mut S) -> i32 {
    if p == 0 as *mut S {
        return 0;
    }
    let b = Box::from_raw(p); // SITE:t21
    b.x
}

// ----- slices, NonNull

pub unsafe fn t22_slice(p: *const i32, n: usize) -> i32 {
    let s = std::slice::from_raw_parts(p, n); // SITE:t22
    s[0]
}

pub unsafe fn t23_slice_arg(p: *mut i32, n: usize) {
    safe_slice(std::slice::from_raw_parts_mut(p, n)); // SITE:t23
}

pub unsafe fn t24_nonnull(p: ptr::NonNull<i32>) -> i32 {
    *p.as_ref() // SITE:t24
}

// ----- wrappers (kind h)

pub unsafe fn mk_ref<'a>(p: *mut i32) -> &'a mut i32 {
    &mut *p // SITE:w1
}

pub unsafe fn mk_ref2<'a>(p: *const i32) -> &'a mut i32 {
    mk_ref(p as *mut i32) // SITE:w2
}

pub unsafe fn t25_helper(p: *mut i32) {
    safe_mut(mk_ref(p)); // SITE:t25a
    let r = mk_ref2(p); // SITE:t25b
}

impl<'a> Cur<'a> {
    pub unsafe fn from_raw(p: *const i32, n: usize) -> Cur<'a> {
        Cur { base: std::slice::from_raw_parts(p, n), pos: 0 } // SITE:w3
    }
}

pub unsafe fn t26_cursor(p: *const i32) -> usize {
    let c = Cur::from_raw(p, 3); // SITE:t26
    c.pos
}

// ----- closures, the reported extras (kind x)

pub unsafe fn t27_closure(p: *mut i32) -> i32 {
    let mut f = || unsafe { &mut *p }; // SITE:t27
    *f()
}

pub unsafe fn t28_transmute(p: *mut i32) -> &'static mut i32 {
    std::mem::transmute(p) // SITE:t28
}

pub unsafe fn t29_cstr(s: *const std::ffi::c_char) -> usize {
    let c = std::ffi::CStr::from_ptr(s); // SITE:t29
    c.to_bytes().len()
}

// ----- place shapes, null tests on a field / an offset, non-dominating tests

pub unsafe fn t30_inner(s: *mut S) -> i32 {
    if !(*s).q.is_null() {
        let r = &mut *(*s).q; // SITE:t30
        return *r;
    }
    0
}

pub unsafe fn t31_base(p: *const i32) -> i32 {
    if !p.is_null() {
        let r = &*p.offset(1); // SITE:t31
        return *r;
    }
    0
}

pub unsafe fn t32_nodom(p: *const i32, flag: bool) -> i32 {
    if flag {
        if p.is_null() {
            return 0;
        }
    }
    let r = &*p; // SITE:t32
    *r
}

pub unsafe fn t33_opt(p: *mut S) {
    if p.as_ref().is_some() { // SITE:t33a
        drop(Box::from_raw(p)); // SITE:t33b
    }
}

pub unsafe fn t34_store(pp: *mut &'static mut i32, p: *mut i32) {
    *pp = &mut *p; // SITE:t34
}

pub unsafe fn t35_fieldref(p: *mut S) -> i32 {
    let rx = &mut (*p).x; // SITE:t35
    *rx
}

pub unsafe fn t36_retsome(p: *mut i32) -> Option<&'static mut i32> {
    Some(&mut *p) // SITE:t36
}

pub unsafe fn t37_fresh(p: *mut i32) {
    let ref mut fresh0 = *p.offset(1); // SITE:t37
    *fresh0 += 1;
}

pub unsafe fn t38_letcast(p: *mut i32) -> *mut i32 {
    let r = &mut *p; // SITE:t38
    r as *mut i32
}

pub unsafe fn t40_boxfield(h: *mut BoxHolder, p: *mut S) {
    (*h).b = Some(Box::from_raw(p)); // SITE:t40
}

// ----- r132 review fixes (10-10): the method-form address idiom (excluded, method-to-raw)

pub unsafe fn t42_asmutptr(b: *mut Buf) -> *mut i32 {
    (*b).vals.as_mut_ptr() // SITE:t42
}

pub unsafe fn t43_asptr(b: *const Buf) {
    takes_rawc((*b).vals.as_ptr()); // SITE:t43
}

pub unsafe fn t44_vecptr(b: *mut Buf) -> *mut i32 {
    (*b).v.as_mut_ptr() // SITE:t44
}

pub unsafe fn t45_strptr(s: *const str) -> *const u8 {
    (*s).as_ptr() // SITE:t45
}

pub unsafe fn t46_len(b: *const Buf) -> usize {
    (*b).vals.len() // SITE:t46
}

// ----- null dominance: the remaining test forms

pub unsafe fn t50_optdiscr(p: *mut S) {
    if let Some(_) = p.as_ref() { // SITE:t50a
        drop(Box::from_raw(p)); // SITE:t50b
    }
}

pub unsafe fn t51_notstmt(p: *mut S) {
    let c = !p.is_null();
    if c {
        drop(Box::from_raw(p)); // SITE:t51
    }
}

pub unsafe fn t52_isnone(p: *mut S) -> i32 {
    if p.as_ref().is_none() { // SITE:t52a
        return 0;
    }
    let b = Box::from_raw(p); // SITE:t52b
    b.x
}

pub unsafe fn t53_ptrnull(p: *const S) -> i32 {
    if p == ptr::null() {
        return 0;
    }
    let r = &*p; // SITE:t53
    r.x
}

// our exposure wrapper's Option<Box> argument
pub unsafe fn t54_exposure(p: *mut S) -> i32 {
    __crat_safe_t54(if p.is_null() { None } else { Some(Box::from_raw(p)) }) // SITE:t54
}

// CROWN quadtree node.rs:121-133: the test and the site read the field through different accessor temporaries
pub unsafe fn t55_quad(mut node: Option<Box<QN>>) {
    if !(*node.as_deref().unwrap()).nw.is_null() {
        qfree(Some(Box::from_raw((*node.as_deref_mut().unwrap()).nw))); // SITE:t55
    }
}

// ----- the value proof: the same place, a changed value (yes-place)

pub unsafe fn t61_loop(mut p: *mut L) -> i32 {
    if p.is_null() {
        return 0;
    }
    let mut s = 0;
    loop {
        let r = &*p; // SITE:t61
        s += r.x;
        p = (*p).next;
        if p.is_null() {
            break;
        }
    }
    s
}

pub unsafe fn t62_fieldcall(s: *mut S) -> i32 {
    if !(*s).q.is_null() {
        opaque();
        let r = &*(*s).q; // SITE:t62
        return *r;
    }
    0
}

// ----- the extras, the remaining exclusion, place and destination shapes

pub unsafe fn t56_vec(p: *mut i32, n: usize) -> usize {
    let v = Vec::from_raw_parts(p, n, n); // SITE:t56a
    let r = std::rc::Rc::from_raw(p as *const i32); // SITE:t56b
    let k = v.len() + *r as usize;
    std::mem::forget(v);
    std::mem::forget(r);
    k
}

pub unsafe fn t57_subplace(p: *mut S) -> *mut i32 {
    &raw mut (&mut *p).x // SITE:t57
}

pub unsafe fn t58_rawslice(p: *const i32, n: usize) -> usize {
    let s = &*ptr::slice_from_raw_parts(p, n); // SITE:t58
    s.len()
}

pub unsafe fn t59_macro(p: *mut i32) {
    safe_mut(deref_mut!(p)); // SITE:t59
}

pub unsafe fn t60_viasafe(p: *mut RS) -> i32 {
    let a = &mut *(*p).r; // SITE:t60a
    let c = &(*p).b.x; // SITE:t60b
    *a + *c
}

pub unsafe fn t63_formal(mut r: &'static i32, p: *const i32) -> i32 {
    r = &*p; // SITE:t63
    *r
}

pub unsafe fn t64_elem(a: &mut [&'static mut i32; 2], p: *mut i32) {
    a[1] = &mut *p; // SITE:t64
}

pub unsafe fn t65_unused(p: *const i32) {
    let _ = &*p; // SITE:t65
}

pub unsafe fn t66_tuple(p: *mut i32) -> i32 {
    let t = (&mut *p, 1); // SITE:t66
    *t.0 += t.1;
    *t.0
}

pub unsafe fn t67_late(p: *mut i32) -> i32 {
    let r;
    r = &mut *p; // SITE:t67
    *r
}

// brotli's shape: a Box<[T]> built from a raw slice, wrapped in Some, bound by a let
pub unsafe fn t68_boxslice(p: *mut i32, n: usize) -> usize {
    let b = Some(Box::from_raw(ptr::slice_from_raw_parts_mut(p, n))); // SITE:t68
    let k = b.as_ref().map_or(0, |s| s.len());
    std::mem::forget(b);
    k
}

// a wrapper's other row is not the wrapping conversion (in_wrapper is per row)
pub unsafe fn w4_mixed<'a>(p: *mut i32, q: *mut i32) -> &'a mut i32 {
    safe_mut(&mut *q); // SITE:w4a
    &mut *p // SITE:w4b
}

// ----- no row expected below: raw-only operations, and reborrows of a reference / a Box (not raw)

pub unsafe fn n01_rawonly(p: *mut S) -> i32 {
    (*p).x += 1;
    let q = &raw mut (*p).x;
    *q + (*p.offset(1)).x
}

pub fn n02_safe(r: &mut i32, mut b: Box<S>) -> i32 {
    let r2 = &mut *r;
    *r2 += 1;
    let bx = &mut *b;
    bx.x += 1;
    let bf = &mut b.x;
    *bf
}
