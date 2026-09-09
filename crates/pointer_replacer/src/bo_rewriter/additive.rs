//! R220: family transactions retain a terminal predecessor before expansion.
//! Policies and snapshots are derived from compiler state, never a corpus ledger.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_span::Span;

use super::{bridge_receipt::SignatureClassId, decision, plan};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FamilyStage {
    Core,
    SliceConstruction,
    SliceUse,
    Option,
    Declaration,
    Return,
}

impl FamilyStage {
    pub(crate) fn previous(self) -> Option<Self> {
        match self {
            Self::Core => None,
            Self::SliceConstruction => Some(Self::Core),
            Self::SliceUse => Some(Self::SliceConstruction),
            Self::Option => Some(Self::SliceUse),
            Self::Declaration => Some(Self::Option),
            Self::Return => Some(Self::Declaration),
        }
    }

    pub(crate) fn next(self) -> Option<Self> {
        match self {
            Self::Core => Some(Self::SliceConstruction),
            Self::SliceConstruction => Some(Self::SliceUse),
            Self::SliceUse => Some(Self::Option),
            Self::Option => Some(Self::Declaration),
            Self::Declaration => Some(Self::Return),
            Self::Return => None,
        }
    }
}

pub(crate) struct FamilyPolicy {
    pub(crate) stage: FamilyStage,
    pub(crate) withdrawn: BTreeSet<(FamilyStage, SignatureClassId)>,
}

impl FamilyPolicy {
    pub(crate) fn at(stage: FamilyStage) -> Self {
        Self {
            stage,
            withdrawn: BTreeSet::new(),
        }
    }

    pub(crate) fn enabled(&self, owner: LocalDefId, family: FamilyStage) -> bool {
        // Each later stage may retry older mechanics with the newly available
        // carrier. Withdrawing that transaction restores the exact predecessor
        // profile, including its earlier withdrawals, rather than permanently
        // banning a family that a later construction/composition can support.
        let owner = SignatureClassId::of(owner);
        let mut stage = self.stage;
        while self.withdrawn.contains(&(stage, owner)) {
            let Some(previous) = stage.previous() else { return false };
            stage = previous;
        }
        family <= stage
    }
}

#[derive(Clone)]
pub(crate) struct StageSnapshot {
    pub(crate) table: decision::DecisionTable,
    pub(crate) plan: plan::Plan,
}

#[derive(Clone, Debug)]
pub(crate) struct FamilyWithdrawal {
    pub(crate) owner: SignatureClassId,
    pub(crate) cause: String,
}

/// A concrete old rendering error, tied to one binding and its actual site.
/// The ordinary production path registers none: refusal labels are not proof.
pub(crate) struct SoundnessWithdrawal {
    subject: (LocalDefId, HirId),
    null_construction: Span,
}

impl SoundnessWithdrawal {
    pub(crate) fn null_required_reference(
        tcx: rustc_middle::ty::TyCtxt<'_>,
        constructions: &decision::construction::ConstructionFacts,
        prior: &StageSnapshot,
        subject: (LocalDefId, HirId),
    ) -> Option<Self> {
        let (old, form) = prior
            .table
            .entries
            .iter()
            .find(|(s, _)| (s.fn_did, s.hir_id) == subject)?;
        let required = match form {
            decision::Decision::Ref { .. } | decision::Decision::InferredRef { .. } => true,
            decision::Decision::Slice { .. }
            | decision::Decision::Opt { .. }
            | decision::Decision::Box(_)
            | decision::Decision::Degraded(_) => false,
        };
        if !required || !old.null_init {
            return None;
        }
        let initializer = *constructions.init_hirs.get(&subject)?;
        if !decision::emitability::is_zero_literal(tcx.hir_node(initializer).expect_expr()) {
            return None;
        }
        Some(Self {
            subject,
            null_construction: *constructions.init_spans.get(&subject)?,
        })
    }
}

fn safe(decision: &decision::Decision) -> bool {
    match decision {
        decision::Decision::Ref { .. }
        | decision::Decision::InferredRef { .. }
        | decision::Decision::Slice { .. }
        | decision::Decision::Opt { .. }
        | decision::Decision::Box(_) => true,
        decision::Decision::Degraded(_) => false,
    }
}

fn applied(
    snapshot: &StageSnapshot,
    subject: &decision::Subject,
    decision: &decision::Decision,
) -> bool {
    safe(decision)
        && snapshot
            .plan
            .class_finalization
            .classes
            .get(&SignatureClassId::of(subject.fn_did))
            .is_some_and(plan::SignatureClassPlan::is_ready)
}

/// Protection uses a conservative superset of delivery: prior terminally
/// prepared safe declarations. Only the emitted-tree custody instrument counts
/// delivery; this planner never substitutes a Ready bit for that measurement.
fn losses<'a>(
    prior: &'a StageSnapshot,
    candidate: &StageSnapshot,
    soundness: &[SoundnessWithdrawal],
) -> Vec<&'a decision::Subject> {
    prior
        .table
        .entries
        .iter()
        .filter_map(|(subject, old)| {
            if !applied(prior, subject, old) {
                return None;
            }
            let key = (subject.fn_did, subject.hir_id);
            let survives = candidate
                .table
                .entries
                .iter()
                .find(|(s, _)| (s.fn_did, s.hir_id) == key)
                .is_some_and(|(s, d)| applied(candidate, s, d));
            let required_null = subject.null_init
                && match old {
                    decision::Decision::Ref { .. } | decision::Decision::InferredRef { .. } => true,
                    decision::Decision::Slice { .. }
                    | decision::Decision::Opt { .. }
                    | decision::Decision::Box(_)
                    | decision::Decision::Degraded(_) => false,
                };
            let witnessed = required_null
                && soundness
                    .iter()
                    .any(|proof| proof.subject == key && !proof.null_construction.is_dummy());
            (!survives && !witnessed).then_some(subject)
        })
        .collect()
}

pub(crate) fn preservation_error(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    soundness: &[SoundnessWithdrawal],
) -> Option<String> {
    let lost = losses(prior, candidate, soundness);
    (!lost.is_empty()).then(|| {
        format!(
            "additive-family-preservation-invariant:unrestored:{:?}",
            lost.iter()
                .map(|s| (s.fn_did.local_def_index.as_u32(), s.local.as_u32()))
                .collect::<Vec<_>>()
        )
    })
}

fn class_changed(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    owner: SignatureClassId,
) -> bool {
    let sites = |snapshot: &StageSnapshot| {
        snapshot
            .plan
            .class_finalization
            .classes
            .get(&owner)
            .map(|class| {
                class
                    .sites
                    .iter()
                    .map(|site| (site.key.clone(), site.edit_key.clone(), site.state.clone()))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    };
    sites(prior) != sites(candidate)
        || prior
            .plan
            .class_finalization
            .classes
            .get(&owner)
            .map(|c| &c.depends_on)
            != candidate
                .plan
                .class_finalization
                .classes
                .get(&owner)
                .map(|c| &c.depends_on)
        || prior
            .table
            .entries
            .iter()
            .filter(|(s, _)| s.fn_did == owner.local_def_id())
            .ne(candidate
                .table
                .entries
                .iter()
                .filter(|(s, _)| s.fn_did == owner.local_def_id()))
}

pub(crate) fn withdrawals(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    policy: &FamilyPolicy,
    soundness: &[SoundnessWithdrawal],
) -> Vec<FamilyWithdrawal> {
    use super::bridge_receipt::BridgeCalleeId;
    if policy.stage == FamilyStage::Core {
        return Vec::new();
    }
    let protected = losses(prior, candidate, soundness)
        .into_iter()
        .map(|s| SignatureClassId::of(s.fn_did))
        .collect::<BTreeSet<_>>();
    let witnessed_owners = soundness
        .iter()
        .map(|s| SignatureClassId::of(s.subject.0))
        .filter(|owner| !protected.contains(owner))
        .collect::<BTreeSet<_>>();
    let enabled = |owner: SignatureClassId| policy.enabled(owner.local_def_id(), policy.stage);
    let prior_sites = prior
        .plan
        .class_finalization
        .classes
        .values()
        .filter(|c| c.is_ready())
        .flat_map(|c| c.sites.iter())
        .filter(|s| s.edit_key != "-")
        .map(|s| s.edit_key.clone())
        .collect::<BTreeSet<_>>();
    let mut related_graph = BTreeMap::<SignatureClassId, BTreeSet<SignatureClassId>>::new();
    let mut connect = |left, right| {
        if left != right {
            related_graph.entry(left).or_default().insert(right);
            related_graph.entry(right).or_default().insert(left);
        }
    };
    for edit in &candidate.table.seams.edits {
        connect(SignatureClassId::of(edit.bridge.caller), edit.owner_class);
    }
    for &(left, right) in candidate
        .table
        .seams
        .interface_dependencies
        .iter()
        .chain(&candidate.table.seams.generated_item_dependencies)
    {
        connect(left, right);
    }
    for class in candidate.plan.class_finalization.classes.values() {
        for &dependency in &class.depends_on {
            connect(class.id, dependency);
        }
        for site in &class.sites {
            connect(class.id, SignatureClassId::of(site.key.caller));
            if let BridgeCalleeId::Local(callee) = site.key.callee {
                connect(class.id, SignatureClassId::of(callee));
            }
        }
    }
    let related_changes = |root| {
        let mut pending = vec![(root, vec![root])];
        let mut seen = BTreeSet::new();
        let mut changed = Vec::new();
        while let Some((owner, path)) = pending.pop() {
            if !seen.insert(owner) {
                continue;
            }
            if owner != root && enabled(owner) && class_changed(prior, candidate, owner) {
                changed.push((
                    owner,
                    path.iter()
                        .map(|owner| owner.order_key())
                        .collect::<Vec<_>>(),
                ));
            }
            for &next in related_graph.get(&owner).into_iter().flatten() {
                let mut next_path = path.clone();
                next_path.push(next);
                pending.push((next, next_path));
            }
        }
        changed
    };
    let mut requested = BTreeMap::<SignatureClassId, String>::new();
    // Exact predecessor edit identity (including replacement digest) establishes
    // age. Generated A5/C sites keep the stage that introduced the transaction;
    // their generic bridge-kind strings do not establish precedence.
    for collision in &candidate.plan.class_finalization.collisions {
        let old_left = prior_sites.contains(&collision.left_edit_key);
        let old_right = prior_sites.contains(&collision.right_edit_key);
        let newer = match (old_left, old_right) {
            (true, false) => Some(collision.right_class),
            (false, true) => Some(collision.left_class),
            (true, true) | (false, false) => None,
        };
        if let Some(owner) = newer.filter(|owner| enabled(*owner)) {
            requested.insert(
                owner,
                format!(
                    "newer-family-collision:{}|{}",
                    collision.left_edit_key, collision.right_edit_key
                ),
            );
        }
    }
    for (owner, class) in &candidate.plan.class_finalization.classes {
        if !enabled(*owner) || witnessed_owners.contains(owner) {
            continue;
        }
        let old = prior.plan.class_finalization.classes.get(owner);
        let new_dropped = class.sites.iter().find(|site| {
            matches!(site.state, plan::ClassSiteState::Dropped(_))
                && !old.is_some_and(|old| old.sites.contains(site))
                && site.key.bridge_kind != "missing-required-site"
        });
        if let Some(site) = new_dropped {
            requested.entry(*owner).or_insert_with(|| {
                format!(
                    "unsatisfied-family-site:{}:{:?}",
                    site.key.receipt_key(),
                    site.state
                )
            });
            continue;
        }
        let new_refusal = class.hold_reasons().iter().find(|reason| {
            !reason.starts_with("dependency-class-held:")
                && *reason != "cross-class-interval-collision"
                && !old.is_some_and(|old| old.hold_reasons().contains(reason))
        });
        if let Some(reason) = new_refusal {
            requested
                .entry(*owner)
                .or_insert_with(|| format!("unwitnessed-family-refusal:{reason}"));
        }
    }
    // A dependency casualty yields at the changed root transaction. Do not
    // disable the old dependent just because the finalizer propagated a hold.
    for owner in protected {
        let mut pending = vec![owner];
        let mut seen = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !seen.insert(current) || requested.contains_key(&current) {
                continue;
            }
            let Some(class) = candidate.plan.class_finalization.classes.get(&current) else {
                if enabled(current) {
                    requested.insert(current, "missing-prior-family-class".to_owned());
                } else {
                    for (owner, path) in related_changes(current) {
                        requested
                            .entry(owner)
                            .or_insert_with(|| format!("restore-family-interface-path:{path:?}"));
                    }
                }
                continue;
            };
            let held_dependencies = class
                .depends_on
                .iter()
                .copied()
                .filter(|dependency| {
                    candidate
                        .plan
                        .class_finalization
                        .classes
                        .get(dependency)
                        .is_some_and(|c| !c.is_ready())
                })
                .collect::<Vec<_>>();
            let new_dependency = held_dependencies.iter().find(|dependency| {
                !prior
                    .plan
                    .class_finalization
                    .classes
                    .get(&current)
                    .is_some_and(|old| old.depends_on.contains(dependency))
            });
            if let Some(dependency) = new_dependency.filter(|_| enabled(current)) {
                requested.insert(
                    current,
                    format!("new-family-dependency:{}", dependency.order_key()),
                );
                continue;
            }
            if !held_dependencies.is_empty() {
                pending.extend(held_dependencies);
                continue;
            }
            let collision_covered = candidate
                .plan
                .class_finalization
                .collisions
                .iter()
                .any(|c| {
                    (c.left_class == current && requested.contains_key(&c.right_class))
                        || (c.right_class == current && requested.contains_key(&c.left_class))
                });
            if collision_covered {
                continue;
            }
            if enabled(current) && class_changed(prior, candidate, current) {
                requested.insert(current, "restore-prior-family-disposition".to_owned());
                continue;
            }
            for (owner, path) in related_changes(current) {
                requested
                    .entry(owner)
                    .or_insert_with(|| format!("restore-family-interface-path:{path:?}"));
            }
        }
    }
    requested
        .into_iter()
        .map(|(owner, cause)| FamilyWithdrawal { owner, cause })
        .collect()
}

pub(crate) fn select_uses<T: Clone>(
    current: &rustc_hash::FxHashMap<(LocalDefId, HirId), T>,
    predecessor: &rustc_hash::FxHashMap<(LocalDefId, HirId), T>,
    policy: &FamilyPolicy,
    family: FamilyStage,
) -> rustc_hash::FxHashMap<(LocalDefId, HirId), T> {
    current
        .keys()
        .chain(predecessor.keys())
        .filter_map(|key| {
            let source = if policy.enabled(key.0, family) {
                current
            } else {
                predecessor
            };
            source.get(key).cloned().map(|value| (*key, value))
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub(crate) struct FamilyFallbackReceipt {
    pub(crate) family: String,
    pub(crate) owner_local_def_id: u32,
    pub(crate) owner_path: String,
    pub(crate) cause: String,
    pub(crate) subjects: Vec<(String, String, String)>,
}

#[derive(Default)]
pub(crate) struct RetiredReceipts {
    options: rustc_hash::FxHashMap<
        super::mechanical_receipt::MechanicalObligationKey,
        super::mechanical_receipt::OptionPresentationReceiptPlan,
    >,
    uses: rustc_hash::FxHashMap<
        super::mechanical_receipt::MechanicalObligationKey,
        super::mechanical_receipt::SliceUseReceiptPlan,
    >,
    constructions: rustc_hash::FxHashMap<
        super::mechanical_receipt::MechanicalObligationKey,
        super::mechanical_receipt::SliceConstructionReceiptPlan,
    >,
}

impl RetiredReceipts {
    pub(crate) fn capture(
        &mut self,
        prior: &StageSnapshot,
        candidate: &StageSnapshot,
        withdrawal: &FamilyWithdrawal,
        stage: FamilyStage,
    ) {
        use super::mechanical_receipt::{
            MechanicalObligationPlan, MechanicalState, MechanicalTerminalReason,
        };
        let retire = |obligation: &mut MechanicalObligationPlan| {
            if let super::mechanical_receipt::MechanicalSubjectKey::Local {
                owner, mir_local, ..
            } = obligation.planned.key.subject
            {
                if let Some((_, old)) = prior
                    .table
                    .entries
                    .iter()
                    .find(|(s, _)| s.fn_did == owner && s.local.as_u32() == mir_local)
                {
                    obligation.planned.found_form = decision::seam::form_of(old).key().to_owned();
                }
            }
            let site_cause = obligation.intended_terminal_reason.as_ref().map_or_else(
                || format!("owner-cause:{}", withdrawal.cause),
                MechanicalTerminalReason::key,
            );
            obligation.intended_terminal_state = MechanicalState::Reclassified;
            obligation.intended_terminal_reason =
                Some(MechanicalTerminalReason::EvidenceMissing(format!(
                    "additive-family-fallback:{};site-cause={site_cause}",
                    obligation.planned.prior_reason
                )));
        };
        let prior_keys = prior
            .plan
            .mechanical_receipts(&BTreeSet::new())
            .0
            .into_iter()
            .map(|event| event.key)
            .collect::<rustc_hash::FxHashSet<_>>();
        for receipt in &candidate.plan.option_receipt_plans {
            if receipt.owner_class != withdrawal.owner
                || prior_keys.contains(&receipt.obligation.planned.key)
            {
                continue;
            }
            let mut receipt = receipt.clone();
            retire(&mut receipt.obligation);
            receipt.source_form = receipt.obligation.planned.found_form.clone();
            receipt.adapter = format!("prior-family-rendering:{stage:?}");
            self.options
                .insert(receipt.obligation.planned.key.clone(), receipt);
        }
        for receipt in &candidate.plan.slice_use_receipt_plans {
            if receipt.owner_class != withdrawal.owner
                || prior_keys.contains(&receipt.obligation.planned.key)
            {
                continue;
            }
            let mut receipt = receipt.clone();
            retire(&mut receipt.obligation);
            receipt.source_form = receipt.obligation.planned.found_form.clone();
            receipt.adapter = format!("prior-family-rendering:{stage:?}");
            self.uses
                .insert(receipt.obligation.planned.key.clone(), receipt);
        }
        for receipt in &candidate.plan.slice_construction_receipt_plans {
            if receipt.owner_class != withdrawal.owner
                || prior_keys.contains(&receipt.obligation.planned.key)
            {
                continue;
            }
            let mut receipt = receipt.clone();
            retire(&mut receipt.obligation);
            self.constructions
                .insert(receipt.obligation.planned.key.clone(), receipt);
        }
    }

    pub(crate) fn append(self, table: &mut decision::DecisionTable, planned: &plan::Plan) {
        let active = planned
            .mechanical_receipts(&BTreeSet::new())
            .0
            .into_iter()
            .map(|event| event.key)
            .collect::<rustc_hash::FxHashSet<_>>();
        table.option_receipts.extend(
            self.options
                .into_iter()
                .filter_map(|(key, receipt)| (!active.contains(&key)).then_some(receipt)),
        );
        table.slice_use_receipts.extend(
            self.uses
                .into_iter()
                .filter_map(|(key, receipt)| (!active.contains(&key)).then_some(receipt)),
        );
        table.retired_slice_constructions.extend(
            self.constructions
                .into_iter()
                .filter_map(|(key, receipt)| (!active.contains(&key)).then_some(receipt)),
        );
    }
}
