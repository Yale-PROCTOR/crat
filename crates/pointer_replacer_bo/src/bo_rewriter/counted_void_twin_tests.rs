//! The raw twin across module boundaries — the corpus shape this lane kept
//! failing on, in its own file so a composition union cannot shred it line by
//! line (batch 13's dry16c lost three lines of the first fixture, which turned
//! the witness into an `Err("FatalError")` out of its own input; wave-6v 024).
//!
//! The two properties are a CONJUNCTION (wave-6r 034): the twin must keep the
//! visibility of the item it clones AND its call must be spelled absolutely.
//! Either alone leaves a corpus caller unable to name it.

use super::counted_void_tests::compact;

/// The twin's visibility, pinned as a conjunction at a CROSS-MODULE caller: if
/// any call names the twin, the twin must be DEFINED and nameable where the
/// call is. `insert_raw_twin` clones the callee's item, so the clone keeps that
/// item's own visibility — forcing it private loses the caller (batch 11's
/// `E0425 … exists but is inaccessible`) and synthesizing a `Restricted` path
/// loses the item itself on a composed frame (batch 12). Non-vacuous by
/// construction: the routed call is asserted before anything else, which the
/// lane's other twin witness (`…_reverts_with_its_callees_class`) is not on its
/// own fixture.
const TWIN_CROSS_MODULE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmQuaternion { pub x: f32, pub y: f32, pub z: f32, pub w: f32 }
pub mod inner {
    use super::kmQuaternion;
    pub unsafe fn kmQuaternionScale(mut pOut: *mut kmQuaternion, mut pIn: *const kmQuaternion, mut s: f32) {
        (*pOut).x = (*pIn).x * s;
        (*pOut).y = (*pIn).y * s;
        (*pOut).z = (*pIn).z * s;
        (*pOut).w = (*pIn).w * s;
        let _k = pIn.offset(0);
    }
}
pub unsafe fn slerp(mut q1: *const kmQuaternion, mut t: f32) -> f32 {
    let mut diff = kmQuaternion { x: 0., y: 0., z: 0., w: 0. };
    inner::kmQuaternionScale(&mut diff, q1, 2.0);
    inner::kmQuaternionScale(&mut diff, &mut diff, t);
    diff.x + diff.w
}
"#;

#[test]
fn w6v_raw_twin_is_defined_and_nameable_at_a_cross_module_caller() {
    let source = super::emit_tests::ast_emitted_source_of(TWIN_CROSS_MODULE).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("__crat_raw_kmQuaternionScale(&mutdiff,&mutdiff,t)"),
        "the aliased call routes to the twin (the witness is non-vacuous): {source}"
    );
    assert!(
        c.contains("fn__crat_raw_kmQuaternionScale("),
        "a called twin must be defined: {source}"
    );
    assert!(
        source
            .lines()
            .any(|l| l.contains("fn __crat_raw_kmQuaternionScale(") && l.contains("pub")),
        "the twin keeps the cloned item's `pub`, so the other module can name it: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// heman's real shape, and the one the corpus keeps failing on: the callee is
/// in another module and the caller IMPORTS it (`use …::kmVec2Add;`) and calls
/// it unqualified. Renaming such a call to `__crat_raw_…` leaves a name that
/// the caller's module never imported — `E0425 cannot find function … in this
/// scope`, with "exists but is inaccessible" when the twin is private and
/// without that note when it is not, which is what read as the item vanishing.
/// The twin's call must therefore be spelled so it resolves from any module.
const TWIN_IMPORTED_CALLER: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_imports)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmQuaternion { pub x: f32, pub y: f32, pub z: f32, pub w: f32 }
pub mod inner {
    use super::kmQuaternion;
    #[no_mangle]
    pub unsafe extern "C" fn kmQuaternionScale(mut pOut: *mut kmQuaternion, mut pIn: *const kmQuaternion, mut s: f32) {
        (*pOut).x = (*pIn).x * s;
        (*pOut).y = (*pIn).y * s;
        (*pOut).z = (*pIn).z * s;
        (*pOut).w = (*pIn).w * s;
        let _k = pIn.offset(0);
    }
}
pub mod caller {
    use super::kmQuaternion;
    use crate::inner::kmQuaternionScale;
    pub unsafe fn slerp(mut q1: *const kmQuaternion, mut t: f32) -> f32 {
        let mut diff = kmQuaternion { x: 0., y: 0., z: 0., w: 0. };
        kmQuaternionScale(&mut diff, q1, 2.0);
        kmQuaternionScale(&mut diff, &mut diff, t);
        diff.x + diff.w
    }
}
"#;

#[test]
fn w6v_raw_twin_call_resolves_from_an_importing_module() {
    let source = super::emit_tests::ast_emitted_source_of(TWIN_IMPORTED_CALLER).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("__crat_raw_kmQuaternionScale(&mutdiff,&mutdiff,t)"),
        "the aliased call routes to the twin (non-vacuous): {source}"
    );
    assert!(
        c.contains("fn__crat_raw_kmQuaternionScale("),
        "a called twin is defined: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "the renamed call resolves from the importing module: {source}"
    );
}
