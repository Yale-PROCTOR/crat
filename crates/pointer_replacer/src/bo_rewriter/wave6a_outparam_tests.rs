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

const HEMAN_NOISE_CALLERS: &str = include_str!("testdata/w6a-r800-heman-noise-callers.rs");

/// **R800-4 item 1, the census's two holds, RED from the corpus callers.**
/// The readers' formals are optional at the frame. `simplex_fbm` lends its
/// Box to them (`Call::Lend::Formal` at 54′: no arm lends a Box owner to an
/// optional reference formal); `island_noise` passes `freqs[0]` and
/// `planet_heightmap` passes `p.x` as the readers' scalar arguments
/// (`Source::UnsupportedOwnerUse`: a constant index into a local array and a
/// local struct's scalar field were not side-effect-free reads).
#[test]
fn w6a_r800_heman_out_parameter_callers_deliver_at_the_frame() {
    let out = callers_at_the_frame("r800-heman-noise-callers", HEMAN_NOISE_CALLERS);
    let rows = out
        .artifacts
        .ownership_native
        .lines()
        .filter(|l| l.contains("::ctx#"))
        .collect::<Vec<_>>()
        .join("\n");
    let context = format!("{rows}\n{:#?}\n{}", out.degradations, out.source);
    for caller in [
        "heman_generate_simplex_fbm",
        "heman_internal_generate_island_noise",
        "heman_generate_planet_heightmap",
    ] {
        let row = rows
            .lines()
            .find(|l| l.starts_with(&format!("{caller}::ctx#")))
            .unwrap_or_default();
        assert!(row.contains("\tselected\t"), "{caller}: {context}");
    }
    let text = compact(&out.source);
    assert_eq!(
        text.matches(
            "letmutctx:::std::option::Option<::std::boxed::Box<crate::osn_context>>=None;"
        )
        .count(),
        3,
        "{context}"
    );
    assert!(
        text.contains("open_simplex_noise2(ctx.as_deref(),"),
        "{context}"
    );
    assert!(
        text.contains("open_simplex_noise3(ctx.as_deref(),"),
        "{context}"
    );
    assert_eq!(out.reverted, 0, "{context}");
}

/// The three callers' emission with the frame's decisions pinned.
fn callers_at_the_frame(marker: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
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
            (
                "heman_internal_generate_island_noise::ctx".to_owned(),
                SlotKind::Owning,
            ),
            (
                "heman_generate_planet_heightmap::ctx".to_owned(),
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

/// **Control (R800-4):** an index that is not a constant (`freqs[k]`) may
/// trap between the generated borrows, so island's scalar argument is still
/// not a side-effect-free read and its owner holds; the other two deliver.
#[test]
fn w6a_r800_a_computed_index_is_not_a_pure_read() {
    let source = HEMAN_NOISE_CALLERS.replacen(
        "(u * freqs[0 as libc::c_int as usize]) as libc::c_double",
        "(u * freqs[(x % 5 as libc::c_int) as usize]) as libc::c_double",
        1,
    );
    assert_ne!(source, HEMAN_NOISE_CALLERS);
    let out = callers_at_the_frame("r800-computed-index", &source);
    let row = out
        .artifacts
        .ownership_native
        .lines()
        .find(|l| l.starts_with("heman_internal_generate_island_noise::ctx#"))
        .unwrap_or_default()
        .to_owned();
    assert!(row.contains("\tSource::UnsupportedOwnerUse\t"), "{row}");
    assert_eq!(
        compact(&out.source)
            .matches("letmutctx:::std::option::Option<::std::boxed::Box<crate::osn_context>>=None;")
            .count(),
        2,
        "{}",
        out.source
    );
}
