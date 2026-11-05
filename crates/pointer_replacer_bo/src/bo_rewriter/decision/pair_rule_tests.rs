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
                unproven_peers: Vec::new(),
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
    let held = peers_of_unproven_raw_views(&mut rows, |_, _| None);
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
    assert!(peers_of_unproven_raw_views(&mut rows, |_, _| None).is_empty());
    assert_eq!(rows[0].role, PairRole::Primary);
}

/// R833-1, a peer with no row at the call (a raw view A5's fallback learned:
/// lodepng's `readChunk_PLTE(color, data, …)`, where only `data` has a row):
/// the formal the raw view's unproven proof names is held all the same.
#[test]
fn r833_1_the_peer_of_a_learned_raw_view_without_a_row_is_held() {
    use A5SiteProofVerdict::{Clear, Overlapping};
    let (rows, subjects) = rows(
        [PairRole::Clear, PairRole::RawView, PairRole::Clear],
        [Clear, Overlapping, Clear],
    );
    // Only the raw view's own row exists; it names position 0 as its peer.
    let mut rows = vec![PairSiteDecision {
        unproven_peers: vec![0],
        reason: "a5-fallback-raw-view-role".to_owned(),
        ..rows[1].clone()
    }];
    let held = peers_of_unproven_raw_views(&mut rows, |member, index| {
        Some(PairSiteDecision {
            argument_index: index,
            subject: subjects[index],
            role: PairRole::Blocked,
            tier: PairTier::Blocked,
            reason: "pair-not-shown-disjoint".to_owned(),
            ..member.clone()
        })
    });
    assert_eq!(held, vec![subjects[0]]);
    // The raw view keeps its role; the peer gets a blocked row of its own.
    assert_eq!(rows[0].role, PairRole::RawView);
    assert_eq!(rows.len(), 2);
    assert_eq!(
        (rows[1].subject, rows[1].role),
        (subjects[0], PairRole::Blocked)
    );
}

/// Control: a learned raw view whose peers are all clear names none.
#[test]
fn r833_1_control_a_learned_raw_view_with_no_unproven_peer_holds_nothing() {
    use A5SiteProofVerdict::{Clear, Overlapping};
    let (rows, subjects) = rows(
        [PairRole::Clear, PairRole::RawView, PairRole::Clear],
        [Clear, Overlapping, Clear],
    );
    let mut rows = vec![rows[1].clone()];
    let held = peers_of_unproven_raw_views(&mut rows, |member, index| {
        Some(PairSiteDecision {
            argument_index: index,
            subject: subjects[index],
            ..member.clone()
        })
    });
    assert!(held.is_empty());
    assert_eq!(rows.len(), 1);
}

/// R833-1: a blocked member not shown disjoint is raw like a raw view, so the
/// primary beside it is held (binn `copy_be32(p, &mut id as ..)`, where the raw
/// view's template is unavailable and `psource` is blocked instead).
#[test]
fn r833_1_the_primary_beside_an_unproven_blocked_member_is_held() {
    use A5SiteProofVerdict::{Clear, Overlapping};
    let (mut rows, subjects) = rows(
        [PairRole::Primary, PairRole::Blocked, PairRole::Clear],
        [Overlapping, Overlapping, Clear],
    );
    let held = peers_of_unproven_raw_views(&mut rows, |_, _| None);
    assert_eq!(held, vec![subjects[0]]);
    assert_eq!(rows[0].role, PairRole::Blocked);
}

/// The independent review's MED 3(a): one step only. `b` (a learned raw view)
/// names `a` (no row); `c`'s own row records that its proof against `a` is
/// not clear. Holding `a` makes it a raw member too, so `c` is held as well.
#[test]
fn r833_1_a_newly_held_peer_holds_its_own_unproven_partners() {
    use A5SiteProofVerdict::{Clear, Overlapping};
    let (rows, subjects) = rows(
        [PairRole::Clear, PairRole::RawView, PairRole::Clear],
        [Clear, Overlapping, Overlapping],
    );
    let mut rows = vec![
        PairSiteDecision {
            unproven_peers: vec![0],
            ..rows[1].clone()
        },
        PairSiteDecision {
            unproven_peers: vec![0],
            ..rows[2].clone()
        },
    ];
    let held = peers_of_unproven_raw_views(&mut rows, |member, index| {
        Some(PairSiteDecision {
            argument_index: index,
            subject: subjects[index],
            role: PairRole::Blocked,
            tier: PairTier::Blocked,
            reason: "pair-not-shown-disjoint".to_owned(),
            ..member.clone()
        })
    });
    assert!(
        held.contains(&subjects[0]) && held.contains(&subjects[2]) && held.len() == 2,
        "{held:?}"
    );
    assert_eq!(
        rows[1].role,
        PairRole::Blocked,
        "c is held beside the held a"
    );
}

/// MED 3(b): a row that exists is read by the raw member's proof, not skipped
/// for existing: `a`'s own row says clear, `b`'s proof against `a` does not.
#[test]
fn r833_1_an_existing_row_the_raw_member_names_is_held_whatever_its_own_role() {
    use A5SiteProofVerdict::{Clear, Overlapping};
    let (rows, subjects) = rows(
        [PairRole::Clear, PairRole::RawView, PairRole::Clear],
        [Clear, Overlapping, Clear],
    );
    let mut rows = vec![
        rows[0].clone(),
        PairSiteDecision {
            unproven_peers: vec![0],
            ..rows[1].clone()
        },
    ];
    let held = peers_of_unproven_raw_views(&mut rows, |_, _| None);
    assert_eq!(held, vec![subjects[0]]);
    assert_eq!(rows[0].role, PairRole::Blocked);
}
