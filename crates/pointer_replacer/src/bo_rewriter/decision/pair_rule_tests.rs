//! R833-1 (USER): the callee's side of the pair rule, on pair-site rows.

use super::{
    a5_site_proof::A5SiteProofVerdict,
    co_conversion::{PairRole, PairSiteDecision, PairTier, peers_of_unproven_raw_views},
};

const INPUT: &str = "pub unsafe fn add(a: *mut i32, b: *mut i32, c: *mut i32) { *a += *b + *c; }\npub unsafe fn caller(p: *mut i32, q: *mut i32, r: *mut i32) { add(p, q, r) }\n";

/// One call's three rows: `roles[i]` and `verdicts[i]` at argument `i`.
fn rows(
    roles: [PairRole; 3],
    verdicts: [A5SiteProofVerdict; 3],
) -> (
    Vec<PairSiteDecision>,
    Vec<(rustc_hir::def_id::LocalDefId, rustc_hir::HirId)>,
) {
    ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).expect("native decisions");
        let formal = |name: &str| {
            table
                .entries
                .iter()
                .find(|(subject, _)| subject.label == name)
                .map(|(subject, _)| (subject.fn_did, subject.hir_id))
                .unwrap_or_else(|| panic!("no {name}"))
        };
        let subjects = [formal("add::a"), formal("add::b"), formal("add::c")];
        let caller = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == "caller::p")
            .map(|(subject, _)| subject.fn_did)
            .expect("caller");
        let rows = (0..3)
            .map(|i| PairSiteDecision {
                caller,
                callee: subjects[i].0,
                argument_index: i,
                span: rustc_span::DUMMY_SP,
                call_span: rustc_span::DUMMY_SP,
                subject: subjects[i],
                source_node: None,
                target: None,
                source_shape: "bare-local",
                role: roles[i],
                tier: PairTier::None,
                verdict: verdicts[i],
                reason: "pair-proof-accepted".to_owned(),
                peer_receipts: String::new(),
                a5_fallback: None,
            })
            .collect();
        (rows, subjects.to_vec())
    })
    .expect("input type-checks")
}

/// A raw view not shown disjoint: its primary peer is held too.
#[test]
fn r833_1_the_primary_beside_an_unproven_raw_view_is_held() {
    use A5SiteProofVerdict::{Clear, Overlapping};
    let (mut rows, subjects) = rows(
        [PairRole::Primary, PairRole::RawView, PairRole::Clear],
        [Overlapping, Overlapping, Clear],
    );
    let held = peers_of_unproven_raw_views(&mut rows);
    assert_eq!(held, vec![subjects[0]]);
    assert_eq!(rows[0].role, PairRole::Blocked);
    assert_eq!(rows[0].reason, "pair-not-shown-disjoint");
    // The clear third position is not the pair's.
    assert_eq!(rows[2].role, PairRole::Clear);
}

/// Control: a call whose pair is clear holds nothing.
#[test]
fn r833_1_control_a_clear_call_holds_nothing() {
    use A5SiteProofVerdict::Clear;
    let (mut rows, _) = rows(
        [PairRole::Primary, PairRole::Clear, PairRole::Clear],
        [Clear, Clear, Clear],
    );
    assert!(peers_of_unproven_raw_views(&mut rows).is_empty());
    assert_eq!(rows[0].role, PairRole::Primary);
}
