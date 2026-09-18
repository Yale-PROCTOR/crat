//! The counted-void raw twin keeps the original's BODY, so it keeps the
//! original's callers — and those are not always in the callee's module.
//! heman's `kmVec2Add` is called from three modules outside
//! `src::kazmath::vec2`, so a private twin failed there with
//! `E0425 … __crat_raw_kmVec2Add … exists but is inaccessible`, the verify
//! gate reverted the function, and its partition partner `kmVec2Subtract`
//! fell with it (report 027; main's probe measured the pair as −2).
const CROSS_MODULE: &str = r#"
#![allow(dead_code, unused_mut)]
pub mod inner {
    pub unsafe fn lodepng_memcpy(mut dst: *mut core::ffi::c_void,
        mut src: *const core::ffi::c_void, mut size: usize) {
        let mut i: usize = 0;
        i = 0;
        while i < size {
            *(dst as *mut i8).offset(i as isize) = *(src as *const i8).offset(i as isize);
            i = i.wrapping_add(1);
        }
    }
}
pub unsafe fn copy_pointer_storage() -> u8 {
    let data = [7u8; 8];
    let mut src: *const core::ffi::c_void = data.as_ptr() as *const core::ffi::c_void;
    let dst: *mut core::ffi::c_void = &mut src as *mut *const core::ffi::c_void as *mut core::ffi::c_void;
    inner::lodepng_memcpy(dst, src, 1);
    *(src as *const u8)
}
"#;

#[test]
fn wave6r_raw_twin_is_defined_and_reachable_from_another_module() {
    let source = super::emitted(CROSS_MODULE);
    let compact = source.replace([' ', '\n'], "");
    // The invariant is a conjunction, and BOTH halves have failed in the
    // corpus: at batch 11 the twin was defined but private (`E0425 … exists
    // but is inaccessible`), at batch 12 the reference survived with no
    // definition at all (`E0425` with no note). So: if any call names the
    // twin, the twin must be DEFINED, and defined visibly to that caller.
    let called = compact.contains("inner::__crat_raw_lodepng_memcpy(")
        || compact.contains("__crat_raw_lodepng_memcpy(");
    if !called {
        // No split at this base means no twin is owed; the emission is what
        // this witness pins, not the split decision.
        return;
    }
    assert!(
        compact.contains("fn__crat_raw_lodepng_memcpy("),
        "a call names the twin, so the twin must be defined: {source}"
    );
    assert!(
        compact.contains("pubunsafefn__crat_raw_lodepng_memcpy(")
            || compact.contains("pub(crate)unsafefn__crat_raw_lodepng_memcpy(")
            || compact.contains("pubunsafeextern\"C\"fn__crat_raw_lodepng_memcpy(")
            || compact.contains("pub(crate)unsafeextern\"C\"fn__crat_raw_lodepng_memcpy("),
        "the twin must be visible to a caller in another module: {source}"
    );
}
