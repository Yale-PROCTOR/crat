//! brotli's `CleanupZopfliCostModel` — relay 033's (α) shape, reduced from the
//! derived substrate (`lib.rs` around 7481574: `BrotliFree(m, (*self_0)
//! .literal_costs_ as *mut libc::c_void)`), with the two structs and the
//! manager write the shape needs.
//!
//! Two classes own one interval: the callee's A5 T2-fallback wrapper owns the
//! whole call and plans a per-argument raw view at `arg1`, while the CALLER's
//! class plans a `typed-raw-temporary` at exactly that argument — the cast of
//! a field read through a root the caller delivers as `&mut`. At the batch-9
//! census this pair is 68 of brotli's 94 collision rows (18 class pairs, 34
//! intervals).
pub(super) const A5_INNER_ARGUMENT: &str = r#"#![allow(dead_code, unused_unsafe, non_snake_case, non_camel_case_types)]
pub mod libc { pub use core::ffi::c_void; pub use core::ffi::c_float; }
#[repr(C)]
pub struct MemoryManager { pub allocated: usize }
#[repr(C)]
pub struct ZopfliCostModel { pub literal_costs_: *mut libc::c_float }
pub unsafe fn BrotliFree(mut m: *mut MemoryManager, mut p: *mut libc::c_void) {
    (*m).allocated = (*m).allocated - 1;
    let _ = p;
}
pub unsafe fn CleanupZopfliCostModel(mut m: *mut MemoryManager, mut self_0: *mut ZopfliCostModel) {
    BrotliFree(m, (*self_0).literal_costs_ as *mut libc::c_void);
    (*self_0).literal_costs_ = 0 as *mut libc::c_float;
}
pub unsafe fn entry() {
    let mut mem = MemoryManager { allocated: 1 };
    let mut f = 1.0f32;
    let mut model = ZopfliCostModel { literal_costs_: &mut f };
    CleanupZopfliCostModel(&mut mem, &mut model);
}
"#;
