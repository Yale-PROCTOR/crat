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
