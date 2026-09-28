//! R636-1 — binn's `pint` custody rows (batch 50 `167:246` / `167:247`).
//!
//! The literal-width build delivers `binn_get_int32::pint` / `binn_get_int64::pint` as
//! `Option<&mut c_int>`. Their call `copy_int_value((*value).ptr, pint as *mut c_void, ..)`
//! is routed by the counted-void family to the raw twin, where the A5 fallback plans no
//! stamped temporary (R496-1) — so the pair family's T2 raw view of `pint` is rendered
//! INLINE, by the caller's own Option bridge, at a crate-qualified twin call. The ledger
//! receipts that view T2 at the argument; the matcher, which reads only a stamped
//! temporary at a call to the callee or its unqualified twin, reports it `Missing`.
//!
//! The spellings below are the batch-50 tree's, verbatim, reduced to one caller.

use super::{
    bridge_custody_match::*,
    bridge_custody_syntax::{self as syntax, ByteSpan},
};

const ORIGINAL: &str = "pub mod src {\npub mod binn {\n\
pub struct binn { pub ptr: *mut libc::c_void, pub type_0: libc::c_int }\n\
unsafe extern \"C\" fn copy_int_value(mut psource: *mut libc::c_void,\n    mut pdest: *mut libc::c_void, mut source_type: libc::c_int,\n    mut dest_type: libc::c_int) -> BOOL { *(pdest as *mut libc::c_int) = *(psource as *mut libc::c_int); return 1 as libc::c_int; }\n\
pub unsafe extern \"C\" fn binn_get_int32(mut value: *mut binn,\n    mut pint: *mut libc::c_int) -> BOOL {\n    if value.is_null() || pint.is_null() { return 0 as libc::c_int; }\n    return copy_int_value((*value).ptr, pint as *mut libc::c_void,\n            (*value).type_0, 0x61 as libc::c_int);\n}\n\
}\n}\n";

/// The emitted call's arg1 as the batch-50 tree spells it.
const VIEW: &str = "pint.as_deref_mut().map_or(core::ptr::null_mut::<core::ffi::c_void>(),\n                    |value|\n                        core::ptr::from_mut(value).cast::<core::ffi::c_void>())";

const TWIN_DECL: &str = "unsafe extern \"C\" fn __crat_raw_copy_int_value(mut psource: *mut libc::c_void,\n    mut pdest: *mut libc::c_void, mut source_type: libc::c_int,\n    mut dest_type: libc::c_int) -> BOOL { *(pdest as *mut libc::c_int) = *(psource as *mut libc::c_int); return 1 as libc::c_int; }\n";

fn emitted_with(callee: &str, argument: &str, twin: &str) -> String {
    format!(
        "pub mod src {{\npub mod binn {{\n\
pub struct binn {{ pub ptr: *mut libc::c_void, pub type_0: libc::c_int }}\n\
unsafe extern \"C\" fn copy_int_value(mut psource: &[u8],\n    mut pdest: *mut libc::c_void, mut source_type: libc::c_int,\n    mut dest_type: libc::c_int) -> BOOL {{ return 1 as libc::c_int; }}\n\
{twin}\
pub unsafe extern \"C\" fn binn_get_int32(mut value: Option<&binn>,\n    mut pint: Option<&mut libc::c_int>) -> BOOL {{\n    if value.is_none() || pint.is_none() {{ return 0 as libc::c_int; }}\n    return {callee}((*value.unwrap()).ptr,\n                {argument},\n                (*value.unwrap()).type_0, 0x61 as libc::c_int);\n}}\n\
}}\n}}\n"
    )
}

fn emitted() -> String {
    emitted_with(
        "crate::src::binn::__crat_raw_copy_int_value",
        VIEW,
        TWIN_DECL,
    )
}

fn expectation(kind: BridgeKind) -> BridgeExpectation {
    let lo = ORIGINAL.find("pint as *mut libc::c_void").unwrap() as u32;
    BridgeExpectation {
        identity: "167:246:local:167:pair:arg1".into(),
        kind,
        caller: "src::binn::binn_get_int32".into(),
        callee: "src::binn::copy_int_value".into(),
        anchor: SiteAnchor::Argument {
            span: ByteSpan {
                lo,
                hi: lo + "pint as *mut libc::c_void".len() as u32,
            },
            argument_index: 1,
        },
        c9_stamp: None,
        pending_source: None,
        tier: "T2".into(),
        waiver_id: Some(crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.into()),
    }
}

fn check(output: &str, rows: &[BridgeExpectation]) -> BridgeCustodyReport {
    let original = syntax::inventory_source("original.rs", ORIGINAL).unwrap();
    let emitted = syntax::inventory_source("emitted.rs", output).unwrap();
    compare(BridgeCustodyInput {
        original: &original,
        emitted: &emitted,
        original_source: ORIGINAL,
        emitted_source: output,
        expectations: rows,
        context: &BridgeCustodyContext::default(),
    })
}

/// The corpus shape: the A5 T2 view of `pint`, inline at the crate-qualified twin call,
/// is the receipt's rendering. RED at `4feea9176`: `Missing`,
/// `no-stamped-raw-view-or-matched-c9-at-original-site`, exactly as batches 50 and 51.
#[test]
fn w6b_an_inline_raw_view_at_the_twin_call_carries_the_a5_receipt() {
    let output = emitted();
    let report = check(&output, &[expectation(BridgeKind::A5SiteProofT2Fallback)]);
    assert_eq!(
        report.rows[0].status,
        ReceiptStatus::MatchedRaw,
        "{report:#?}"
    );
    assert!(report.data && report.tree_only.is_empty(), "{report:#?}");
    let call = output
        .find("crate::src::binn::__crat_raw_copy_int_value(")
        .unwrap() as u32;
    assert_eq!(
        report.rows[0].emitted_call.map(|span| span.lo),
        Some(call),
        "the row names the twin call: {report:#?}"
    );
}

fn missing(output: &str, kind: BridgeKind, why: &str) {
    let report = check(output, &[expectation(kind)]);
    assert!(
        !report.data && report.rows[0].status != ReceiptStatus::MatchedRaw,
        "{why}: {report:#?}"
    );
}

const TWIN: &str = "crate::src::binn::__crat_raw_copy_int_value";

/// At a call to the callee ITSELF the A5 fallback does plan its stamp, so an inline view
/// there is a stamp that did not render — still `Missing`.
#[test]
fn w6b_an_inline_view_at_the_callee_itself_still_owes_the_stamp() {
    missing(
        &emitted_with("crate::src::binn::copy_int_value", VIEW, TWIN_DECL),
        BridgeKind::A5SiteProofT2Fallback,
        "only the twin renders the view inline",
    );
}

/// The twin is followed only where the emitted tree declares it, in the callee's module.
#[test]
fn w6b_an_undeclared_or_foreign_twin_is_not_followed() {
    missing(
        &emitted_with(TWIN, VIEW, ""),
        BridgeKind::A5SiteProofT2Fallback,
        "no declared twin",
    );
    let elsewhere = emitted_with("crate::src::other::__crat_raw_copy_int_value", VIEW, "").replace(
        "}\n}\n",
        &format!("}}\npub mod other {{\n{TWIN_DECL}}}\n}}\n"),
    );
    missing(
        &elsewhere,
        BridgeKind::A5SiteProofT2Fallback,
        "a twin of the same name in another module is another function",
    );
}

/// The twin's formal at the position must be raw.
#[test]
fn w6b_a_twin_formal_that_is_not_raw_is_not_a_raw_view_target() {
    missing(
        &emitted_with(
            TWIN,
            VIEW,
            &TWIN_DECL.replace(
                "mut pdest: *mut libc::c_void",
                "mut pdest: &mut libc::c_int",
            ),
        ),
        BridgeKind::A5SiteProofT2Fallback,
        "a reference formal takes no raw view",
    );
}

/// The argument must be a raw VIEW of the original argument: a pointer that reads the
/// subject but views something else, a closure that projects another name, a view of a
/// shadowing binding, and the original text itself all refuse.
#[test]
fn w6b_only_a_view_of_the_original_argument_is_its_raw_view() {
    for (argument, why) in [
        (
            "pint.as_deref_mut().map_or(core::ptr::null_mut::<core::ffi::c_void>(), |value| core::ptr::null_mut())",
            "reads pint, views nothing",
        ),
        (
            "pint.as_deref_mut().map_or(core::ptr::null_mut::<core::ffi::c_void>(), |value| core::ptr::from_mut(other).cast::<core::ffi::c_void>())",
            "the closure projects another name",
        ),
        (
            "pint as *mut libc::c_void",
            "the original text is R499-1's zero-syntax site, not a view",
        ),
    ] {
        missing(
            &emitted_with(TWIN, argument, TWIN_DECL),
            BridgeKind::A5SiteProofT2Fallback,
            why,
        );
    }
    let shadowed = emitted().replace(
        "    return crate::src::binn::__crat_raw_copy_int_value(",
        "    let mut pint: Option<&mut libc::c_int> = None;\n    return crate::src::binn::__crat_raw_copy_int_value(",
    );
    missing(
        &shadowed,
        BridgeKind::A5SiteProofT2Fallback,
        "a view of a shadowing binding is not the original's",
    );
}

/// The row is the A5 fallback's: the PAIR family renders its raw view at twin calls as
/// anywhere else, so its receipt keeps asking for the stamp.
#[test]
fn w6b_a_pair_receipt_is_not_read_through_the_twin() {
    missing(
        &emitted(),
        BridgeKind::PairT2RawView,
        "PAIR stamps are not withdrawn",
    );
}

/// Two twin calls that both qualify leave the correspondence open: refuse.
#[test]
fn w6b_two_qualifying_twin_calls_are_not_one_site() {
    let twice = emitted().replace(
        "    return crate::src::binn::__crat_raw_copy_int_value(",
        &format!(
            "    crate::src::binn::__crat_raw_copy_int_value((*value.unwrap()).ptr, {VIEW}, (*value.unwrap()).type_0, 0x61 as libc::c_int);\n    return crate::src::binn::__crat_raw_copy_int_value("
        ),
    );
    missing(
        &twice,
        BridgeKind::A5SiteProofT2Fallback,
        "ambiguous twin calls",
    );
}

/// The closure form of an optional reference's view is the relation the ordinary stamp
/// needs too: the same view, stamped at a call to the callee, matches.
#[test]
fn w6b_the_closure_form_view_matches_as_a_stamped_temporary() {
    let lo = ORIGINAL.find("copy_int_value((*value).ptr").unwrap();
    let stamped = emitted_with("copy_int_value", &format!("__crat_a5_raw_{lo}_1"), "").replace(
        "    return copy_int_value(",
        &format!(
            "    let __crat_a5_raw_{lo}_1: *mut libc::c_void = {VIEW};\n    return copy_int_value("
        ),
    );
    let report = check(&stamped, &[expectation(BridgeKind::A5SiteProofT2Fallback)]);
    assert_eq!(
        report.rows[0].status,
        ReceiptStatus::MatchedRaw,
        "{report:#?}"
    );
    assert_eq!(report.rows[0].bindings.len(), 1, "{report:#?}");
}
