// W6F-5 (relay 034 / R451-4): the INLINE ARRAY FIELD taken as a pointer —
// `((*s).arr).as_mut_ptr()`, `Construction::ArrayDecay`, whose type and length
// both live in the field's declared type. The market shapes are brotli's
// `BlockSplitterFinishBlock*::last_entropy` (mutable, `[f64; 2]`) and heman's
// `kmMat3Multiply::m1` (shared, `[f32; 9]`), spelled as the derived substrate
// spells them; the delivering precedent is lodepng
// `lodepng_compute_color_stats::p` (`&mut [u8]`, extent
// `sealed-contract:array-length`).
#![allow(
    dead_code,
    unused_mut,
    unused_unsafe,
    unused_assignments,
    unused_variables,
    non_camel_case_types,
    non_snake_case
)]
#[repr(C)]
pub struct Splitter {
    pub last_entropy_: [f64; 2],
    pub num_blocks_: u64,
    pub scratch_: *mut f64,
}
#[repr(C)]
pub struct Mat3 {
    pub mat: [f32; 9],
}

// The market shape, mutable: the field's ONLY mention in the function.
#[no_mangle]
pub unsafe extern "C" fn finish_block(mut self_0: *mut Splitter, mut n: u64) {
    let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();
    *last_entropy.offset(0 as isize) = *last_entropy.offset(1 as isize);
    *last_entropy.offset(1 as isize) = n as f64;
}

// The market shape, shared (heman's `mat`).
#[no_mangle]
pub unsafe extern "C" fn trace3(mut pIn: *const Mat3) -> f32 {
    let mut m = ((*pIn).mat).as_ptr();
    return *m.offset(0 as isize) + *m.offset(4 as isize) + *m.offset(8 as isize);
}

// Control 1 — a POINTER field: the length is NOT in its type, so the arm must
// not speak for it (a fabricated extent here would be the whole point of the
// build lost).
#[no_mangle]
pub unsafe extern "C" fn scratch_sum(mut self_0: *mut Splitter) -> f64 {
    let mut p = (*self_0).scratch_;
    return *p.offset(0 as isize) + *p.offset(1 as isize);
}

// Control 2 — a LOCAL array: wave-6s2's twin (W6S2-5b), not this arm. The
// receiver must be a FIELD projection.
#[no_mangle]
pub unsafe extern "C" fn local_array() -> f64 {
    let mut buf: [f64; 4] = [0.; 4];
    let mut p = buf.as_mut_ptr();
    *p.offset(0 as isize) = 1.0f64;
    return buf[0 as usize];
}

// Control 3 — the same field place is touched again while the view is live.
// Two live views of one place; the arm must hold.
#[no_mangle]
pub unsafe extern "C" fn second_touch(mut self_0: *mut Splitter) {
    let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();
    *last_entropy.offset(0 as isize) = 1.0f64;
    (*self_0).last_entropy_[1 as usize] = 2.0f64;
}

// Control 4 — the whole struct is overwritten while the view is live: the
// bytes the view owns are written through another path, so the arm must hold.
#[no_mangle]
pub unsafe extern "C" fn whole_overwrite(mut self_0: *mut Splitter, mut other: *mut Splitter) {
    let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();
    *last_entropy.offset(0 as isize) = 1.0f64;
    *self_0 = Splitter {
        last_entropy_: [0.; 2],
        num_blocks_: 0,
        scratch_: 0 as *mut f64,
    };
}

// Control 5 — a SHARED decay cast to a mutable pointer and written through.
// The cast peel would otherwise reach the arm, and admitting a `&mut [T]`
// over an `as_ptr` receiver is exactly the `&T` → `&mut T` widening R395-2
// forbids. Held.
#[no_mangle]
pub unsafe extern "C" fn widen(mut ro: *const Splitter) {
    let mut w = ((*ro).last_entropy_).as_ptr() as *mut f64;
    *w.offset(0 as isize) = 1.0f64;
}
