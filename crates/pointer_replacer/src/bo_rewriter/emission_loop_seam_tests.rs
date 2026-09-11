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
fn fixture() -> (Plan, BTreeSet<SignatureClassId>, BTreeSet<String>, [SignatureClassId; 4]) {
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
