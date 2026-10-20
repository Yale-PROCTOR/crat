//! **Wave-6o (relay 038 / R465-5): the carrier at a computed argument view of
//! an OPTION-presented slice base.**
//!
//! lodepng `addChunk_IHDR::data` is decided `opt-slice-mut` and handed to
//! `lodepng_set32bitInt(data.offset(0), w)`, whose formal delivers `&mut [u8]`.
//! The carrier built for that argument took the base's RAW form, so it was a
//! `from_raw_parts` with a fabricated extent and no unwrap — and the Option
//! family's `call-required` check (`decision::option`, `carrier.spec.unwrap
//! .is_none()`) then held the whole class `option-evidence-held`, which is what
//! main 052 §5 read at the other end as the slice-use family's fallback.
//!
//! The base's own decision is the authority: the view is a suffix of the
//! delivered slice inside the `Some`, so the unwrap opens the base and the
//! index follows it — `&mut b.as_mut().unwrap()[e..]`, never the reverse.
use super::{
    decision::{
        Decision,
        seam::{Form, GlueCore, GlueSpec},
        slice_forms::ForwardView,
    },
    emit_tests::ast_emitted_source_of,
    verify,
};

/// The corpus shape, reduced: a nullable (`is_null`) slice-evidenced base
/// (`*data.offset(8) = _`) handed to a local callee whose formal delivers
/// `&mut [u8]` through two computed views.
const OPTIONAL_BASE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
unsafe fn set32(mut buffer: *mut u8, mut value: u32) {
    *buffer.offset(0 as isize) = (value >> 24) as u8;
    *buffer.offset(1 as isize) = (value >> 16) as u8;
    *buffer.offset(2 as isize) = (value >> 8) as u8;
    *buffer.offset(3 as isize) = value as u8;
}
pub unsafe fn write_header(mut data: *mut u8, mut w: u32, mut h: u32) -> i32 {
    if data.is_null() { return 0; }
    set32(data.offset(0 as isize), w);
    set32(data.offset(4 as isize), h);
    *data.offset(8 as isize) = 8 as u8;
    return 1;
}
"#;

/// The same program with the nullability evidence removed: the base is not
/// Option-presented, so this arm must not touch it.
const NON_OPTIONAL_BASE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
unsafe fn set32(mut buffer: *mut u8, mut value: u32) {
    *buffer.offset(0 as isize) = (value >> 24) as u8;
    *buffer.offset(1 as isize) = (value >> 16) as u8;
    *buffer.offset(2 as isize) = (value >> 8) as u8;
    *buffer.offset(3 as isize) = value as u8;
}
pub unsafe fn write_header(mut data: *mut u8, mut w: u32, mut h: u32) -> i32 {
    set32(data.offset(0 as isize), w);
    set32(data.offset(4 as isize), h);
    *data.offset(8 as isize) = 8 as u8;
    return 1;
}
"#;

/// `(decision of `write_header::data`, the carriers rooted at it)`.
fn base_and_carriers(input: &str) -> (Decision, Vec<(Form, Option<bool>, bool, String, String)>) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                subject.param_name.as_deref() == Some("data")
                    && tcx.item_name(subject.fn_did.to_def_id()).as_str() == "write_header"
            })
            .expect("the reduced base");
        let node = (subject.fn_did, subject.hir_id);
        let carriers = table
            .seams
            .edits
            .iter()
            .filter(|edit| edit.source_node == Some(node))
            .map(|edit| {
                (
                    edit.found,
                    edit.spec.unwrap,
                    edit.spec.forward_slice.is_some(),
                    edit.bridge.bridge_kind.clone(),
                    edit.replacement.clone(),
                )
            })
            .collect();
        (decision.clone(), carriers)
    })
    .expect("fixture compiler context")
}

/// **W6O-CARRIER-1.** The carrier takes the base's DECIDED form, so the
/// existing `(Slice, Opt { slice: true })` glue arm supplies the unwrap and the
/// view supplies the index — and the fabricated extent disappears with it.
#[test]
fn wave6o_optional_slice_base_opens_before_the_computed_suffix_index() {
    assert!(verify::type_checks_str(OPTIONAL_BASE));
    let (decision, carriers) = base_and_carriers(OPTIONAL_BASE);
    assert!(
        matches!(
            decision,
            Decision::Opt {
                mutable: true,
                slice: true,
                ..
            }
        ),
        "the base must stay an optional slice: {decision:?}"
    );
    assert_eq!(
        carriers.len(),
        2,
        "one carrier per computed view: {carriers:?}"
    );
    for (found, unwrap, forward, kind, replacement) in &carriers {
        assert_eq!(
            *found,
            Form::Opt {
                mutable: true,
                slice: true
            },
            "the carrier reads the base's decided form: {carriers:?}"
        );
        assert_eq!(
            *unwrap,
            Some(true),
            "the required contract opens it: {carriers:?}"
        );
        assert!(forward, "the view supplies the index: {carriers:?}");
        assert_eq!(kind, "computed-suffix-view");
        assert!(
            replacement.contains(".as_mut().unwrap())["),
            "the unwrap precedes the index: {replacement}"
        );
        assert!(
            !replacement.contains("FALLBACK_SLICE_EXTENT"),
            "the suffix carries the base's own extent: {replacement}"
        );
    }
    let output = ast_emitted_source_of(OPTIONAL_BASE).expect("native emission");
    assert!(
        output.contains("data: Option<&mut [u8]>"),
        "the base delivers its optional slice: {output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// **The control.** Without nullability evidence the base is not
/// Option-presented, and no unwrap may appear on its carriers — the existing
/// slice path owns that shape and this arm is inert.
#[test]
fn wave6o_a_base_that_is_not_option_presented_never_gains_an_unwrap() {
    assert!(verify::type_checks_str(NON_OPTIONAL_BASE));
    let (decision, carriers) = base_and_carriers(NON_OPTIONAL_BASE);
    assert!(
        !matches!(decision, Decision::Opt { .. }),
        "the control's base must not be optional: {decision:?}"
    );
    assert!(
        !carriers.is_empty(),
        "the control must still have the carriers the arm could have touched"
    );
    for (found, unwrap, _, _, replacement) in &carriers {
        assert!(
            !matches!(found, Form::Opt { .. }),
            "no optional found form: {carriers:?}"
        );
        assert_eq!(*unwrap, None, "no unwrap without an Option: {carriers:?}");
        assert!(
            !replacement.contains("unwrap()"),
            "no unwrap in the text: {replacement}"
        );
    }
}

/// A base with one view this arm cannot render: the `memcpy` argument is a
/// raw-boundary carrier, so the all-or-nothing refusal leaves every carrier of
/// this subject exactly as it was — including the `set32` one, whose Option
/// source it therefore still cannot open.
const REFUSED_BASE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
unsafe extern "C" { fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void; }
unsafe fn set32(mut buffer: *mut u8, mut value: u32) {
    *buffer.offset(0 as isize) = (value >> 24) as u8;
    *buffer.offset(1 as isize) = (value >> 16) as u8;
    *buffer.offset(2 as isize) = (value >> 8) as u8;
    *buffer.offset(3 as isize) = value as u8;
}
pub unsafe fn write_header2(mut data: *mut u8, mut src: *const u8, mut w: u32) -> i32 {
    if data.is_null() { return 0; }
    memcpy(data.offset(16 as isize) as *mut core::ffi::c_void, src as *const core::ffi::c_void, 4);
    set32(data.offset(0 as isize), w);
    *data.offset(8 as isize) = 8 as u8;
    return 1;
}
"#;

/// **W6O-CARRIER-3 (R466-8) — the caller side has its own name.** The reason a
/// `call-required` receipt is held when its carrier cannot open an optional
/// source is `carrier-cannot-open`, NOT `terminal-contract-missing`, which
/// keeps the callee-side meaning (no contract at the parameter at all —
/// `opt_w1_held_terminal_callee_cannot_license_unwrap` pins that one). The two
/// are opposite ends of one site and shared a name, so an artifact could read
/// `terminal_contract = terminal-required:<interface>` beside a drop reason of
/// `terminal-contract-missing` and look self-contradictory.
#[test]
fn wave6o_a_carrier_that_cannot_open_its_source_says_so() {
    assert!(verify::type_checks_str(REFUSED_BASE));
    let reasons = ::utils::compilation::run_compiler_on_str(REFUSED_BASE, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        table
            .option_receipts
            .iter()
            .filter(|receipt| receipt.operation == "call-required")
            .map(|receipt| {
                receipt
                    .obligation
                    .intended_terminal_reason
                    .as_ref()
                    .map_or_else(|| "<none>".to_owned(), |reason| reason.key())
            })
            .collect::<Vec<_>>()
    })
    .expect("fixture compiler context");
    // The retirement rewrites the reason and carries the original as
    // `site-cause=`, which is the form the census column shows.
    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("carrier-cannot-open")),
        "the caller-side hold names itself: {reasons:?}"
    );
    assert!(
        !reasons
            .iter()
            .any(|reason| reason.contains("terminal-contract-missing")),
        "the callee-side name is not reused here: {reasons:?}"
    );
}

/// **W6O-CARRIER-2 — the renderer's order.** An `Option` cannot be indexed, so
/// when a spec carries both the unwrap and a forward view the unwrap opens the
/// base FIRST. No spec the glue matrix returns carries both (the matrix never
/// sets a forward view), so this order is unreachable before this wave and
/// nothing existing moves.
#[test]
fn wave6o_the_unwrap_opens_the_base_before_the_view_shifts_it() {
    let mut spec = GlueSpec::core(GlueCore::Bare, true).with_unwrap(true);
    spec.forward_slice = Some(ForwardView {
        index_name: "(4 as isize) as usize".to_owned(),
        mutable: true,
        root: None,
    });
    assert_eq!(
        spec.render("data").expect("a bare view renders"),
        "(&mut (data.as_mut().unwrap())[(4 as isize) as usize..])"
    );
    let shared = {
        let mut spec = GlueSpec::core(GlueCore::Bare, false).with_unwrap(false);
        spec.forward_slice = Some(ForwardView {
            index_name: "e".to_owned(),
            mutable: false,
            root: None,
        });
        spec.render("p").expect("a shared view renders")
    };
    assert_eq!(shared, "(&(p.unwrap())[e..])");
    let without_a_view = GlueSpec::core(GlueCore::Bare, true)
        .with_unwrap(true)
        .render("data")
        .expect("the plain required unwrap still renders");
    assert_eq!(without_a_view, "data.as_mut().unwrap()");
}
