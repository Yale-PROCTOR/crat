//! **The emission-loop seam, and the two killers it was blocking.**
//!
//! Phase M closed with three typed deferrals whose stated cause was the same
//! missing thing: the production withholding law lives inside `rewrite_core`'s
//! verify loop and had no unit seam, so DEFERRED-KILLER(R291-5) (*the delivery
//! partition takes the effective reverted set*) and DEFERRED-KILLER(R306-1c)
//! (*the receipts are derived against `reverted ∪ held_classes()`, closed*)
//! could be stated in prose and not in a test.
//!
//! Both are statements about one function. `effective_withheld_classes` now
//! names that law once — it used to be spelled out at three call sites, which
//! is how R306-1 happened in the first place: the receipts were derived against
//! `reverted` while the tree was emitted against `reverted ∪ held`, and nothing
//! in the types objected to the difference.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    bridge_receipt::SignatureClassId,
    decision::lifetime::ReturnOriginAtomDependencies,
    effective_withheld_classes,
    plan::{ClassFinalization, Plan, SignatureClassDisposition, SignatureClassPlan},
};

/// Four classes, each reaching the withheld set by a different route:
///
/// * `direct` — reverted outright;
/// * `held` — not ready, so `held_classes()` withholds it;
/// * `atom_owner` — owns the reverted atom;
/// * `dependent` — depends on `atom_owner` through the input-reversion closure.
///
/// A partition on the direct set alone keeps the last three, which is exactly
/// the ledger claiming deliveries the tree had already retired.
fn fixture() -> (
    Plan,
    BTreeSet<SignatureClassId>,
    BTreeSet<String>,
    [SignatureClassId; 4],
) {
    let ids = class_ids();
    let [direct, held, atom_owner, dependent] = ids;
    let mut plan = Plan::default();
    plan.class_finalization = ClassFinalization {
        classes: BTreeMap::from([
            (held, held_class(held)),
            (direct, ready_class(direct)),
            (atom_owner, ready_class(atom_owner)),
            (dependent, ready_class(dependent)),
        ]),
        collisions: Vec::new(),
    };
    plan.terminal_call_plans.return_origin_dependencies =
        ReturnOriginAtomDependencies::from_edges_for_test(
            BTreeMap::from([("atom-r".to_owned(), BTreeSet::from([atom_owner]))]),
            BTreeMap::from([(atom_owner, BTreeSet::from([dependent]))]),
        );
    (
        plan,
        BTreeSet::from([direct]),
        BTreeSet::from(["atom-r".to_owned()]),
        ids,
    )
}

/// **DEFERRED-KILLER(R291-5)** — the delivery partition takes the *effective*
/// set. Every one of the four routes must be withheld; a partition that used
/// the direct set alone would keep three of them.
#[test]
fn r291_5_the_withheld_set_is_the_effective_one_not_the_direct_one() {
    let (plan, reverted, atoms, [direct, held, atom_owner, dependent]) = fixture();
    let withheld = effective_withheld_classes(&plan, &reverted, &atoms);
    for (class, route) in [
        (direct, "reverted directly"),
        (held, "held: the class is not ready"),
        (atom_owner, "owns the reverted atom"),
        (dependent, "input-reversion closure over the atom owner"),
    ] {
        assert!(
            withheld.contains(&class),
            "{route} is not withheld: {withheld:?}"
        );
    }
    // The killer's teeth: the direct set really is strictly smaller, so this
    // test fails if the partition is ever re-pointed at `reverted`.
    assert_eq!(reverted.len(), 1);
    assert_eq!(withheld.len(), 4, "{withheld:?}");
    assert!(withheld.is_superset(&reverted) && withheld != reverted);
}

/// **DEFERRED-KILLER(R306-1c)** — the receipts are derived against the same set
/// the tree is emitted against. Stated as the property that makes that true:
/// the one law is a *pure function of the plan*, so two call sites that use it
/// cannot disagree, which is what three hand-written copies could.
#[test]
fn r306_1c_the_withholding_law_is_one_function_and_holds_the_held_classes() {
    let (plan, reverted, atoms, [_, held, ..]) = fixture();
    let once = effective_withheld_classes(&plan, &reverted, &atoms);
    let twice = effective_withheld_classes(&plan, &reverted, &atoms);
    assert_eq!(once, twice, "the law must be a pure function of the plan");
    assert!(
        once.contains(&held),
        "a held class must be withheld by the receipt-side reading too: {once:?}"
    );
    // The pre-R306-1 reading, reconstructed: `reverted` closed WITHOUT the held
    // classes. It is strictly smaller, which is the defect that shipped.
    let without_held = plan.effective_reverted_classes(&reverted, &atoms);
    assert!(
        !without_held.contains(&held),
        "the reconstruction must reproduce the defect it stands for"
    );
    assert!(once.len() > without_held.len());
}

/// With no reverted atoms the closure has no seed, so the withheld set is
/// exactly `reverted ∪ held`. This pins that the held classes are added
/// unconditionally and not as a side effect of the closure.
#[test]
fn the_held_classes_are_withheld_even_with_no_reverted_atom() {
    let (plan, reverted, _, [direct, held, ..]) = fixture();
    let withheld = effective_withheld_classes(&plan, &reverted, &BTreeSet::new());
    assert_eq!(withheld, BTreeSet::from([direct, held]), "{withheld:?}");
}

fn class_ids() -> [SignatureClassId; 4] {
    use rustc_hir::def_id::{DefIndex, LocalDefId};
    [0u32, 1, 2, 3].map(|index| {
        SignatureClassId::of(LocalDefId {
            local_def_index: DefIndex::from_u32(index),
        })
    })
}

fn class(id: SignatureClassId, disposition: SignatureClassDisposition) -> SignatureClassPlan {
    SignatureClassPlan {
        id,
        required_arms: Default::default(),
        site_keys: Vec::new(),
        edit_keys: Vec::new(),
        depends_on: Vec::new(),
        disposition,
        sites: Vec::new(),
        hold_ordinals: Vec::new(),
    }
}

fn ready_class(id: SignatureClassId) -> SignatureClassPlan {
    class(id, SignatureClassDisposition::Ready)
}

fn held_class(id: SignatureClassId) -> SignatureClassPlan {
    class(
        id,
        SignatureClassDisposition::Held(vec!["held:fixture".to_owned()]),
    )
}

// ---------------------------------------------------------------------------
// DEFERRED-KILLER(R299-2) — the producer states the render in the row.
// ---------------------------------------------------------------------------
//
// The other half of the emission-loop seam. `refresh` builds pending rows from
// a `Plan`, and R299-2's law is that a delivered pending site's row carries the
// *emitted* text — stated by the producer, keyed by the call's original span —
// rather than a hint the comparator reconstructs. The existing `r299_*` tests
// pin the comparator's side of that contract over a constructed `Export`; none
// of them exercises the producer, which is what the deferral was about.

use rustc_middle::mir::Local;
use rustc_span::{BytePos, DUMMY_SP};

use super::{
    bridge_custody_export::{Export, refresh},
    decision::{
        DeclShape, Subject, SubjectKind,
        raw_boundary::{ForeignSymbolKey, RawBoundarySiteKey},
        seam::Form,
        sibling_overlap::{
            LocalPostCallEvidence, PENDING_REASON, PendingSiblingReceipt, SiblingPotential,
            SiblingSource,
        },
    },
    plan::sibling_overlap::{EmittedCall, PendingSite},
};

const CALL_LO: u32 = 40;
const CALL_HI: u32 = 61;
const ARG_LO: u32 = 47;
const ARG_HI: u32 = 48;

fn pending_site() -> PendingSite {
    // Built with `Span::new`, not `DUMMY_SP.with_lo(..).with_hi(..)`: the
    // latter passes through a state where `hi < lo`, which `Span` normalises,
    // and the span comes back with the positions it was not given.
    let span = |lo: u32, hi: u32| {
        rustc_span::Span::new(
            BytePos(lo),
            BytePos(hi),
            rustc_span::SyntaxContext::root(),
            None,
        )
    };
    let call_span = span(CALL_LO, CALL_HI);
    let argument_span = span(ARG_LO, ARG_HI);
    PendingSite {
        site: Err("fixture-site".to_owned()),
        receipt: PendingSiblingReceipt {
            potential: SiblingPotential {
                site: RawBoundarySiteKey {
                    caller: "f".to_owned(),
                    block: 0,
                    statement_index: 0,
                    callee: ForeignSymbolKey {
                        symbol: "g".to_owned(),
                        path: "g".to_owned(),
                        abi: "C".to_owned(),
                        signature: "fn(*const i32)".to_owned(),
                        foreign: true,
                    },
                    argument_index: 0,
                    subject: "f::x#1".to_owned(),
                },
                caller: rustc_hir::def_id::CRATE_DEF_ID,
                callee: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                source: SiblingSource::Declared(subject()),
                argument_span,
                call_span,
                source_shape: "unsealed:deref",
                siblings: Vec::new(),
                local_post_call: LocalPostCallEvidence::ParameterProtected,
            },
            source_form: Form::Ref { mutable: false },
            target_form: Form::Raw,
            risky_siblings: Vec::new(),
            reason: PENDING_REASON,
            tier: "T2",
            waiver: "sibling-overlap",
        },
        emitted_call: Ok(EmittedCall {
            file: super::plan::FileKey::Virtual("lib.rs".to_owned()),
            lo: CALL_LO as usize,
            hi: CALL_HI as usize,
            edits: vec![(ARG_LO as usize, ARG_HI as usize, "y".to_owned())],
        }),
        siblings: Vec::new(),
    }
}

fn subject() -> Subject {
    Subject {
        fn_did: rustc_hir::def_id::CRATE_DEF_ID,
        local: Local::from_u32(1),
        hir_id: rustc_hir::CRATE_HIR_ID,
        param_name: Some("x".to_owned()),
        kind: SubjectKind::Param { hir_index: 0 },
        ptr_depth: 1,
        label: "f::x".to_owned(),
        ty_span: Some(DUMMY_SP),
        binding_span: DUMMY_SP,
        pointee_span: Some(DUMMY_SP),
        decl_shape: DeclShape::RawPtr,
        mutable: false,
        freed_at: None,
        len_recovered: false,
        null_init: false,
        mut_binding: false,
        ctor: None,
    }
}

fn refreshed(call_renders: BTreeMap<(u32, u32), String>) -> Export {
    let mut export = Export::default();
    refresh(
        &mut export,
        &Plan::default(),
        &BTreeSet::new(),
        &[pending_site()],
        &[],
        &[],
        &call_renders,
    );
    export
}

/// **DEFERRED-KILLER(R299-2)** — the row carries the producer's render, and it
/// is keyed by the **call** span. The argument span is present in the same
/// receipt and is deliberately a different interval, so a producer that keyed
/// on it would state nothing.
#[test]
fn r299_2_the_producer_states_the_render_keyed_by_the_call_span() {
    let export = refreshed(BTreeMap::from([(
        (CALL_LO, CALL_HI),
        "g(core::ptr::from_ref(x).cast::<c_void>())".to_owned(),
    )]));
    let row = export.pending_sites.first().expect("one pending row");
    let call = row.call.as_ref().expect("a delivered site states its call");
    assert_eq!(
        call.rendered.as_deref(),
        Some("g(core::ptr::from_ref(x).cast::<c_void>())"),
        "the row must carry the render the emitting layer stated"
    );

    // Keyed on the ARGUMENT span instead, the same producer states nothing —
    // which is what makes the call-span key load-bearing rather than incidental.
    let wrong_key = refreshed(BTreeMap::from([((ARG_LO, ARG_HI), "y".to_owned())]));
    let wrong_row = wrong_key.pending_sites.first().expect("one pending row");
    assert_eq!(
        wrong_row
            .call
            .as_ref()
            .expect("a delivered site states its call")
            .rendered,
        None,
        "a render keyed by the argument span is not this call's render"
    );
}

/// A delivered pending site with no render available states none rather than
/// reconstructing one. The comparator's job is to notice that; the producer's
/// job is not to invent it.
#[test]
fn r299_2_an_absent_render_is_stated_as_absent_not_reconstructed() {
    let export = refreshed(BTreeMap::new());
    let row = export.pending_sites.first().expect("one pending row");
    let call = row.call.as_ref().expect("a delivered site states its call");
    assert_eq!(call.rendered, None);
    // The interval and the edits are still stated: those are the producer's
    // own facts, and R287-1(b) owes them whether or not a render exists.
    assert_eq!((call.lo, call.hi), (CALL_LO as usize, CALL_HI as usize));
    assert_eq!(call.edits.len(), 1);
}

/// **R430-1 — the final-reverts artifact names EVERY owner of a withheld
/// class.** The census marks a subject reverted by its owner path, so a
/// class-mate the artifact does not name keeps a `realized` row over text the
/// tree left verbatim: on batch 9's candidate that was heman's
/// `kmRay2IntersectBox` (class-mate of `kmRay2IntersectLineSegment`, the one
/// path the artifact carried) and 24 more rows, which failed the program's
/// delivery custody by themselves.
/// R451-2(2). The three derived columns a root table needs: the SUBJECT the
/// class took with it, the ROOT that drove a `closure:partition` member, and the
/// attribution's HEAD. Without the root column heman's 63 partition reverts sit
/// on an empty compiler-diagnostics table with nothing pointing at their cause
/// (ownership-fields 037 STOP 1); without the head every reader re-derives the
/// same projection by hand.
#[test]
fn r451_2_final_reverts_carry_named_subject_partition_root_and_reason_head() {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::bo_rewriter::bridge_receipt::SignatureClassId;

    let class = SignatureClassId::of(rustc_hir::def_id::LocalDefId {
        local_def_index: rustc_hir::def_id::DefIndex::from_u32(352),
    });
    let withheld = BTreeSet::from([class]);
    let display = BTreeMap::from([(class, "src::p::member".to_owned())]);
    let named = BTreeMap::from([(class, BTreeSet::from(["src::p::member::out#3".to_owned()]))]);
    let reasons = BTreeMap::from([(
        class,
        BTreeSet::from([
            "callee-parameter-input-unavailable:class=118:arg=0..1:root-reverted".to_owned(),
        ]),
    )]);
    let receipt = crate::bo_rewriter::render_raw_boundary_final_reverts(
        &withheld,
        &BTreeSet::new(),
        &named,
        &reasons,
        &display,
        &BTreeMap::new(),
        &BTreeSet::new(),
        None,
    );
    let header = receipt.lines().next().expect("a header");
    assert_eq!(
        header,
        "kind\tidentity\tclass_id\tattribution\tnamed_subject\tpartition_root\treason_head"
    );
    let row = receipt
        .lines()
        .nth(1)
        .expect("one row")
        .split('\t')
        .collect::<Vec<_>>();
    assert_eq!(row[3], "closure:partition", "{receipt}");
    assert_eq!(row[4], "src::p::member::out#3", "{receipt}");
    assert_eq!(
        row[5], "callee-parameter-input-unavailable:class=118:arg=0..1:root-reverted",
        "the root that drove the partition member is named: {receipt}"
    );
    assert_eq!(row[6], "closure:partition", "{receipt}");

    // The head is a projection, not a second classification: the class ids and
    // site details that make a hold row unique are stripped, the cause is not.
    assert_eq!(
        crate::bo_rewriter::raw_boundary_reason_head("held:dependency-class-held:1107"),
        "dependency-class-held"
    );
    assert_eq!(
        crate::bo_rewriter::raw_boundary_reason_head(
            "held:dropped-site:seam-site-overlap:seam-site-overlap"
        ),
        "dropped-site"
    );
    assert_eq!(
        crate::bo_rewriter::raw_boundary_reason_head("verify-reverted"),
        "verify-reverted"
    );
}

#[test]
fn r430_final_reverts_name_every_owner_of_a_withheld_class() {
    use std::collections::{BTreeMap, BTreeSet};

    use crate::bo_rewriter::bridge_receipt::SignatureClassId;

    let class = SignatureClassId::of(rustc_hir::def_id::LocalDefId {
        local_def_index: rustc_hir::def_id::DefIndex::from_u32(352),
    });
    let other = SignatureClassId::of(rustc_hir::def_id::LocalDefId {
        local_def_index: rustc_hir::def_id::DefIndex::from_u32(410),
    });
    let withheld = BTreeSet::from([class]);
    let display = BTreeMap::from([
        (
            class,
            "src::kazmath::ray2::kmRay2IntersectLineSegment".to_owned(),
        ),
        (other, "src::kazmath::vec2::kmVec2Dot".to_owned()),
    ]);
    let owners = BTreeMap::from([
        (
            class,
            BTreeSet::from([
                "src::kazmath::ray2::kmRay2IntersectBox".to_owned(),
                "src::kazmath::ray2::kmRay2IntersectLineSegment".to_owned(),
            ]),
        ),
        (
            other,
            BTreeSet::from(["src::kazmath::vec2::kmVec2Dot".to_owned()]),
        ),
    ]);
    let receipt = crate::bo_rewriter::render_raw_boundary_final_reverts(
        &withheld,
        &BTreeSet::new(),
        &std::collections::BTreeMap::new(),
        &std::collections::BTreeMap::new(),
        &display,
        &owners,
        &withheld,
        None,
    );
    let rows = receipt
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 2, "{receipt}");
    assert!(
        rows.iter()
            .any(|row| row[1] == "src::kazmath::ray2::kmRay2IntersectBox"),
        "the class-mate the display path does not name must be a row: {receipt}"
    );
    assert!(
        rows.iter()
            .any(|row| row[1] == "src::kazmath::ray2::kmRay2IntersectLineSegment"),
        "{receipt}"
    );
    assert!(
        rows.iter().all(|row| row[2] == "local-def-index:352"),
        "both rows carry the withheld class's id: {receipt}"
    );
    // A class with no recorded owner keeps the display path, and an unnamed
    // one still fails closed as before.
    let bare = crate::bo_rewriter::render_raw_boundary_final_reverts(
        &withheld,
        &BTreeSet::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &display,
        &BTreeMap::new(),
        &withheld,
        None,
    );
    assert!(
        bare.contains("src::kazmath::ray2::kmRay2IntersectLineSegment"),
        "{bare}"
    );
    // This IS the defect's shape: the display-path-only rendering (the artifact
    // before R430-1) names one owner of the class and the census therefore
    // never learns that the other owner's text stayed verbatim.
    assert!(
        !bare.contains("src::kazmath::ray2::kmRay2IntersectBox"),
        "the display path alone cannot name the class-mate: {bare}"
    );
    let unknown = crate::bo_rewriter::render_raw_boundary_final_reverts(
        &withheld,
        &BTreeSet::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &withheld,
        None,
    );
    assert!(unknown.contains("<unknown-local-class>"), "{unknown}");
}

/// **Row (iv) (R471-2)** — each hold reason carries the ordinal `hold_terminal_class`
/// recorded it at, in RECORD order, and a cascade member shares the ordinal of the hold
/// that reached it.
///
/// `hold_reasons()` sorts and dedups. That is right for its readers and it destroys the
/// one fact a cascade needs: which refusal came first. R460-13's 201 `closure:partition`
/// rows bottom out on roots that this column names directly.
#[test]
fn r471_2_hold_reasons_carry_the_ordinal_they_were_recorded_at() {
    use crate::bo_rewriter::plan::SignatureClassDisposition as D;

    let mut plan = super::plan::Plan::default();
    let ids = class_ids();
    let (first, second) = (ids[0], ids[1]);
    plan.class_finalization
        .classes
        .insert(first, ready_class(first));
    plan.class_finalization
        .classes
        .insert(second, ready_class(second));

    plan.hold_terminal_class(
        first,
        crate::bo_rewriter::decision::Arm::Surface,
        "kind-a",
        "zzz-late-alphabetically".into(),
    );
    plan.hold_terminal_class(
        first,
        crate::bo_rewriter::decision::Arm::Surface,
        "kind-b",
        "aaa-early-alphabetically".into(),
    );

    let class = &plan.class_finalization.classes[&first];
    // The sorted view puts the SECOND reason first; the ordinal view does not.
    assert_eq!(
        class.hold_reasons(),
        ["aaa-early-alphabetically", "zzz-late-alphabetically"]
    );
    assert_eq!(
        class.hold_ordinals(),
        [
            (0, "zzz-late-alphabetically".to_owned()),
            (1, "aaa-early-alphabetically".to_owned()),
        ]
    );
    assert!(matches!(class.disposition, D::Held(_)));

    // The column the census reads renders in RECORD order, `reason@ordinal`, and is
    // therefore NOT the sorted `blocking_reason` text with ordinals appended.
    let rendered = class
        .hold_ordinals()
        .iter()
        .map(|(ordinal, reason)| format!("{reason}@{ordinal}"))
        .collect::<Vec<_>>()
        .join(";");
    assert_eq!(
        rendered, "zzz-late-alphabetically@0;aaa-early-alphabetically@1",
        "row (iv) renders in record order, not sorted order"
    );

    // A class held after the first two carries the NEXT ordinal, so ordinals are
    // comparable across the whole emission, not per class.
    plan.hold_terminal_class(
        second,
        crate::bo_rewriter::decision::Arm::Surface,
        "kind-c",
        "third".into(),
    );
    assert_eq!(
        plan.class_finalization.classes[&second].hold_ordinals(),
        [(2, "third".to_owned())]
    );
}
