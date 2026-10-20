//! **wave-6a 157 (R925-1; report 157b) — a caller's binding handed whole to a
//! formal held for a pair stays held.** The pair hold (`held:pair-not-shown-disjoint`,
//! R855-1 / R864-1) is about the formal's OBJECT: at a call inside the callee its
//! pointer may overlap a raw sibling written there. The caller's binding designates
//! that object, so a "bridge" that kept it a reference and handed the formal its raw
//! view (`v` coerced, `s.as_mut_ptr()`) would have the sibling's write invalidate the
//! binding during the call — UB under Stacked Borrows (a protected formal) and Tree
//! Borrows alike on a UB-free input (157b's Miri run). `held:into-held-formal` is
//! load-bearing for R833, not a typing cascade; this control pins it.

/// The census's A5 world (`rewrite_m1_census_world`), its retention rows attested:
/// the open world's rows read `retention-attestation-absent`, which holds the
/// binding for a reason of its own and would hide a bridge.
fn census_emitted(text: &str) -> (String, Vec<(String, String)>) {
    match super::rewrite_m1_census_world(text) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            ..
        } => {
            println!("SOURCE\n{source}");
            for d in &degradations {
                println!("DEGRADED {} {} {:?}", d.subject, d.reason.key(), d.reason);
            }
            assert!(super::verify::type_checks_str(&source), "{source}");
            let reasons = degradations
                .iter()
                .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
                .collect();
            (source, reasons)
        }
        other => panic!("the fixture must emit: {other:?}"),
    }
}

fn reason_of<'a>(reasons: &'a [(String, String)], subject: &str) -> Option<&'a str> {
    reasons
        .iter()
        .find(|(s, _)| s.starts_with(subject))
        .map(|(_, r)| r.as_str())
}

/// 157b's Miri fixture (`miri-v1-main.rs`, docs `d1009e6`) as crat's input: H1's
/// pair (`pending_hold_tests::PARAMETER_CASE`: `caller::src` beside
/// `(*holder).data` at `update`, one object on both sides, the entry handing one
/// raw pointer to both) with one caller above it. `outer::v` is the object `update` writes through `data`; kept a reference
/// across `caller(holder, v)` it is invalidated by that write, and `outer` reads
/// it again after the call.
const PAIR_HELD_FORMAL_CALLER: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
        update((*holder).data, src);\n\
    }\n\
    pub unsafe fn outer(holder: *const Holder, v: *const i32) -> i32 {\n\
        let x = *v;\n\
        caller(holder, v);\n\
        x + *v\n\
    }\n\
    pub unsafe fn entry() -> i32 {\n\
        let mut value = 1;\n\
        let p: *mut i32 = &mut value;\n\
        let holder = Holder { data: p };\n\
        outer(&holder, p)\n\
    }\n";

#[test]
fn w6a_157_a_binding_handed_to_a_pair_held_formal_is_never_kept_a_reference() {
    let (source, reasons) = census_emitted(PAIR_HELD_FORMAL_CALLER);
    assert_eq!(
        reason_of(&reasons, "caller::src"),
        Some("held:pair-not-shown-disjoint"),
        "{reasons:?}"
    );
    assert!(
        matches!(
            reason_of(&reasons, "outer::v"),
            Some("held:into-held-formal" | "held:pair-not-shown-disjoint")
        ),
        "{reasons:?}"
    );
    let outer = source
        .lines()
        .find(|line| line.contains("fn outer("))
        .unwrap_or_default();
    assert!(outer.contains("v: *const i32"), "held raw: {outer}");
}
