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
