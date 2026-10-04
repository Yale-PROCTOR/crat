//! wave-6a relay 144 (R798-3): heman's out-parameter allocator at the final
//! frame. `open_simplex_noise(seed, &mut ctx)` writes `*ctx = malloc(..)`; the
//! six callers' `ctx` is Owning, the callee's formal is Ref at its own level
//! and Raw at its pointee (`*mut *mut osn_context` decided `&mut *mut
//! osn_context`), `open_simplex_noise_free`'s formal is Owning. R641-6 (4a)
//! built the caller's Box against a raw callee formal; at the frame the
//! formal is a reference.

use super::wave6a_allocation_tests::{compact, emitted};
use crate::analyses::borrow_ownership::SlotKind;

const HEMAN_NOISE: &str = include_str!("testdata/w6a-r798-heman-noise.rs");

/// The frame's decisions for the chain (the L01^13 model of record:
/// `heman_generate_simplex_fbm::_10@d0` owning, `open_simplex_noise::_2@d0`
/// ref / `@d1` raw, `open_simplex_noise_free::_1@d0` owning).
fn at_the_frame(marker: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
    let _frame = super::test_model_override::frame_lock();
    let _serialise = super::decision::ownership_fields_native::field_form_override::LOCK
        .lock()
        .unwrap_or_else(|p| p.into_inner());
    super::test_model_override::set(
        marker,
        vec![],
        vec![
            (
                "heman_generate_simplex_fbm::ctx".to_owned(),
                SlotKind::Owning,
            ),
            ("open_simplex_noise::ctx".to_owned(), SlotKind::Ref),
            ("open_simplex_noise_free::ctx".to_owned(), SlotKind::Owning),
        ],
    );
    let out = emitted(marker, &format!("// {marker}\n{source}"));
    super::test_model_override::clear();
    out
}

/// **The RED (R798-3 item 3), from the corpus callee.** The caller's `ctx`
/// is the Box: `Option<Box<osn_context>>` from `None`, the callee's
/// reference formal handed the slot's own storage, 0 reverted.
#[test]
fn w6a_r798_heman_out_parameter_at_the_frame_is_the_callers_box() {
    let out = at_the_frame("r798-heman-noise", HEMAN_NOISE);
    let text = compact(&out.source);
    let row = out
        .artifacts
        .ownership_native
        .lines()
        .find(|l| l.starts_with("heman_generate_simplex_fbm::ctx#"))
        .unwrap_or_default()
        .to_owned();
    let context = format!("{row}\n{:#?}\n{}", out.degradations, out.source);
    assert!(row.contains("\tselected\t"), "{context}");
    assert!(
        text.contains(
            "letmutctx:::std::option::Option<::std::boxed::Box<crate::osn_context>>=None;"
        ),
        "{context}"
    );
    // The call borrows the slot's own storage for the callee's reference
    // formal; a nonzero return nulls the slot through the raw view.
    assert!(
        text.contains("open_simplex_noise(seedasint64_t,&mut*::core::ptr::from_mut(&mutctx).cast::<*mutcrate::osn_context>());if__crat_rc!=0{*::core::ptr::from_mut(&mutctx).cast::<*mutcrate::osn_context>()=::core::ptr::null_mut();}"),
        "{context}"
    );
    // The callee keeps the frame's form: a reference to a raw pointer.
    assert!(
        text.contains("pubunsafeextern\"C\"fnopen_simplex_noise(mutseed:int64_t,mutctx:&mut*mutosn_context)->libc::c_int{"),
        "{context}"
    );
    assert!(
        text.contains("open_simplex_noise2(ctx.as_deref().unwrap(),"),
        "{context}"
    );
    assert!(
        text.contains("open_simplex_noise_free((ctx.map_or(::core::ptr::null_mut(),::std::boxed::Box::into_raw)"),
        "{context}"
    );
    assert_eq!(out.reverted, 0, "{context}");
    if let Ok(dir) = std::env::var("CRAT_W6A_EMIT_DIR") {
        std::fs::write(format!("{dir}/r798-heman-noise-emitted.rs"), &out.source).unwrap();
    }
}
