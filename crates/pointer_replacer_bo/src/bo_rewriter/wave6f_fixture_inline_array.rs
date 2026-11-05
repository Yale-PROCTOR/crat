// w6f-inline-array-frame
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

// Control 6 (R453) — the ROOT is handed to a callee AFTER the view is taken.
// The callee reaches the very field the view owns, which is an alias no guard
// in this body can see and no borrow relation the compiler checks — exactly
// what wave-6a's `root_is_a_reference_candidate` refusal is about. Held.
#[no_mangle]
pub unsafe extern "C" fn escape_after(mut self_0: *mut Splitter) {
    let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();
    *last_entropy.offset(0 as isize) = 1.0f64;
    observe_splitter(self_0);
}
#[no_mangle]
pub unsafe extern "C" fn observe_splitter(mut s: *mut Splitter) -> u64 {
    return (*s).num_blocks_;
}

// Control 7 (R453) — the root is handed to a callee BEFORE the view is taken
// (brotli's `StartPosQueuePush` shape: `StartPosQueueSize(self_0)` precedes
// `((*self_0).q_).as_mut_ptr()`). The view does not exist yet, so the
// refusal is ordered and this one still delivers.
#[no_mangle]
pub unsafe extern "C" fn escape_before(mut self_0: *mut Splitter) -> f64 {
    let mut n = observe_splitter(self_0);
    let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();
    *last_entropy.offset(0 as isize) = n as f64;
    return *last_entropy.offset(1 as isize);
}

// Control 8 (R453) — the decay is INSIDE a loop, and the root is handed to a
// callee earlier in the same body. Textual order is not execution order
// there: the call runs again after the view was taken on the previous
// iteration. No order, no ordered refusal — held.
#[no_mangle]
pub unsafe extern "C" fn decay_in_a_loop(mut self_0: *mut Splitter, mut n: u64) {
    let mut i = 0 as u64;
    while i < n {
        observe_splitter(self_0);
        let mut last_entropy = ((*self_0).last_entropy_).as_mut_ptr();
        *last_entropy.offset(0 as isize) = i as f64;
        i = i.wrapping_add(1);
    }
}

// The W6F-5′ split (R455-5): the same decay under a RAW root. There is no
// delivered reference to reborrow from, so the slice constructor with its
// evidence extent — and R453's guards — is the form. The frame stands the
// root's model kind in.
#[no_mangle]
pub unsafe extern "C" fn raw_root(mut self_0: *mut Splitter) -> f64 {
    let mut v = ((*self_0).last_entropy_).as_ptr();
    return *v.offset(0 as isize) + *v.offset(1 as isize);
}
