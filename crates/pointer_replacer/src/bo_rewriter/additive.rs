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
    Ownership,
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
            Self::Ownership => Some(Self::Return),
        }
    }

    pub(crate) fn next(self) -> Option<Self> {
        match self {
            Self::Core => Some(Self::SliceConstruction),
            Self::SliceConstruction => Some(Self::SliceUse),
            Self::SliceUse => Some(Self::Option),
            Self::Option => Some(Self::Declaration),
            Self::Declaration => Some(Self::Return),
            Self::Return => Some(Self::Ownership),
            Self::Ownership => None,
        }
    }
}

pub(crate) type SubjectKey = (LocalDefId, HirId);

pub(crate) struct FamilyPolicy {
    pub(crate) stage: FamilyStage,
    pub(crate) withdrawn: BTreeSet<(FamilyStage, SignatureClassId)>,
    /// R397-6(a): a candidate that failed terminally is excluded at the
    /// selection input for exactly its own identity. Its owner and every
    /// sibling keep the stage, so the deterministic pipeline re-derives their
    /// prior result instead of the whole family falling back.
    /// Keyed by the binding's item-local id: the owner fixes the `HirId` owner.
    pub(crate) withdrawn_subjects: BTreeSet<(FamilyStage, SignatureClassId, u32)>,
}

impl FamilyPolicy {
    pub(crate) fn at(stage: FamilyStage) -> Self {
        Self {
            stage,
            withdrawn: BTreeSet::new(),
            withdrawn_subjects: BTreeSet::new(),
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

    /// The (owner, subject)-scoped gate: an owner-level withdrawal or this
    /// subject's own exclusion at a stage both drop the subject to that stage's
    /// predecessor profile; a sibling's exclusion never does.
    pub(crate) fn enabled_for(&self, subject: SubjectKey, family: FamilyStage) -> bool {
        let owner = SignatureClassId::of(subject.0);
        let mut stage = self.stage;
        while self.withdrawn.contains(&(stage, owner))
            || self
                .withdrawn_subjects
                .contains(&(stage, owner, subject.1.local_id.as_u32()))
        {
            let Some(previous) = stage.previous() else { return false };
            stage = previous;
        }
        family <= stage
    }

    /// Strict transaction progress counts both scopes.
    pub(crate) fn exclusions(&self) -> usize {
        self.withdrawn.len() + self.withdrawn_subjects.len()
    }
}

#[derive(Clone)]
pub(crate) struct StageSnapshot {
    pub(crate) table: decision::DecisionTable,
    pub(crate) plan: plan::Plan,
}

#[derive(Clone, Debug)]
pub(crate) struct FamilyWithdrawal {
    /// **035 clause (3).** A row the loop RECORDS and does not act on: the
    /// terminal named no participant, so there is nothing this rule may
    /// retire. It carries `interface-path-unresolved:<terminal>` and excludes
    /// nothing; the per-function verify gate bounds the residual risk of the
    /// interface it leaves standing.
    pub(crate) unresolved: bool,
    pub(crate) owner: SignatureClassId,
    pub(crate) cause: String,
    /// Empty: the owner falls back (R220). Otherwise exactly these candidates
    /// of `owner` are excluded at the selection input (R397-6(a)).
    pub(crate) subjects: Vec<HirId>,
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
            | decision::Decision::NestedSlice { .. }
            | decision::Decision::Cursor { .. }
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
        | decision::Decision::Box(_)
        | decision::Decision::NestedSlice { .. }
        | decision::Decision::Cursor { .. } => true,
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
                    | decision::Decision::NestedSlice { .. }
                    | decision::Decision::Cursor { .. }
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

/// Which owners the R220 generator would have withdrawn, before R397-6(a)
/// scopes each of them to the candidates that actually moved.
enum Anchor {
    /// The owner carries a new terminal of its own (a collision, a dropped
    /// site, an unwitnessed refusal, a new dependency, a changed disposition).
    /// The terminal sites are carried so the exclusion can be attributed to
    /// exactly the candidates they name — ALL new terminal sites of the owner,
    /// never the first alone: a call that drops one site per contracted
    /// position (wave-6v's `seam-site-overlap`) names every position, and
    /// excluding one of them would leave a live view beside a raw access.
    Direct(Vec<super::bridge_receipt::BridgeSiteKey>),
    /// A prior delivery of this owner is lost and the owner itself has no
    /// transaction left to withdraw: the cause is elsewhere in its interface
    /// component.
    Restore,
}

type RelatedGraph = BTreeMap<SignatureClassId, BTreeSet<SignatureClassId>>;

fn related_graph(candidate: &StageSnapshot) -> RelatedGraph {
    use super::bridge_receipt::BridgeCalleeId;
    let mut related_graph = RelatedGraph::new();
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
    related_graph
}

/// The candidates of `owner` at this stage: subjects whose candidate decision
/// is a safe form that differs from the predecessor's (or is new), and that are
/// not already excluded at this stage. A loss is a symptom, never a candidate.
fn moved(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    policy: &FamilyPolicy,
    owner: SignatureClassId,
) -> Vec<HirId> {
    candidate
        .table
        .entries
        .iter()
        .filter(|(subject, decision)| {
            subject.fn_did == owner.local_def_id()
                && safe(decision)
                && policy.enabled_for((subject.fn_did, subject.hir_id), policy.stage)
                && prior
                    .table
                    .entries
                    .iter()
                    .find(|(s, _)| (s.fn_did, s.hir_id) == (subject.fn_did, subject.hir_id))
                    .is_none_or(|(_, old)| old != decision)
        })
        .map(|(subject, _)| subject.hir_id)
        .collect()
}

/// The candidates of `anchor` a terminal site names: a call INTO the anchor
/// dropped or collided at `arg{N}` names the anchor's parameter `N` (wave-4's
/// `copyFileName::from` at the caller's `arg1`, while `to` at `arg0` is
/// untouched); a surface / address site names its subject outright. Empty
/// when the site names no candidate of the anchor's own.
fn named_by(
    candidate: &StageSnapshot,
    anchor: SignatureClassId,
    site: &super::bridge_receipt::BridgeSiteKey,
) -> Vec<HirId> {
    use super::bridge_receipt::BridgeCalleeId;
    let subjects = candidate
        .table
        .entries
        .iter()
        .filter(|(subject, _)| subject.fn_did == anchor.local_def_id());
    if site.callee == BridgeCalleeId::Local(anchor.local_def_id())
        && let Some(index) = site.position.strip_prefix("arg")
        && let Ok(index) = index.parse::<usize>()
    {
        return subjects
            .filter(|(subject, _)| {
                matches!(subject.kind, decision::SubjectKind::Param { hir_index } if hir_index == index)
            })
            .map(|(subject, _)| subject.hir_id)
            .collect();
    }
    if site.caller == anchor.local_def_id() && matches!(site.arm.as_str(), "surface" | "addr") {
        let named = site.position.split('@').next().unwrap_or_default();
        return subjects
            .filter(|(subject, _)| format!("{}#{}", subject.label, subject.local.as_u32()) == named)
            .map(|(subject, _)| subject.hir_id)
            .collect();
    }
    Vec::new()
}

/// **Relay 043 (wave-6o 016 STOP 1, R397-6(a)).** Is this dropped site
/// SUPERSEDED rather than unsatisfied?
///
/// wave-6s2's source-side raw view (`computed-suffix-raw-view`) carries the
/// evidence `body-local-raw-alias-schedule-unproved`, which is premised on the
/// **destination staying raw**. When the Option family then takes that
/// destination, the adapter is not a family site that failed — it is one the
/// newer family replaced, and the receipt layer drops it as
/// `slice-use-evidence-held`. Reading that drop as an unsatisfied family site
/// falls the WHOLE owner back to the predecessor's mechanics, which is how
/// wave-6o's five rows die one stage before their own arm runs (their report
/// 016 claims 3–5).
///
/// The invariant this restores is R397-6(a)'s own: a request means *a
/// candidate of mine failed and must be excluded*, never *a site of mine was
/// replaced by a later family*. Nothing here decides a form; it only stops one
/// class of drop from being counted as a failure.
///
/// The supersession predicate is the one wave-6s2's relay 010 names — **the
/// destination is typed by the Option family** — read here as: a subject of
/// this owner carries an `Opt` decision in the candidate that it did not carry
/// in the predecessor. A drop with no such move is untouched and still
/// requests, which is what keeps this an exception rather than a loosening.
fn superseded_by_an_option_destination(
    site: &plan::ClassSite,
    owner: SignatureClassId,
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
) -> bool {
    if site.key.bridge_kind != "slice-use-adapter" {
        return false;
    }
    if !matches!(
        &site.state,
        plan::ClassSiteState::Dropped(reason) if reason == "slice-use-evidence-held"
    ) {
        return false;
    }
    // Conjunct 3 (wave-6s2 013 §1): the Option VALUE planner owns an RHS edit
    // at this site's span. Without it the two renderings do not occupy one
    // span and there is nothing to supersede — which is what narrows the arm
    // from "this owner gained an `Opt`" to "this site was replaced".
    let value_edit_here = candidate
        .plan
        .class_finalization
        .classes
        .get(&owner)
        .is_some_and(|class| {
            class.sites.iter().any(|other| {
                matches!(other.state, plan::ClassSiteState::EditReady)
                    && other.key.file == site.key.file
                    && other.key.lo == site.key.lo
                    && other.key.hi == site.key.hi
                    && (other.key.bridge_kind.contains("option")
                        || other.key.bridge_kind.contains("nullable"))
            })
        });
    // Conjunct 3 is a SPAN test, so it applies to a site that has a span. A
    // dropped site with no text interval (`ClassSite::zero`) cannot be
    // span-matched and is decided by conjuncts 1 and 2 alone.
    let has_interval = site.edit_key != "-" && site.key.file != "-";
    if has_interval && !value_edit_here {
        return false;
    }
    let optional = |snapshot: &StageSnapshot| -> BTreeSet<String> {
        snapshot
            .table
            .entries
            .iter()
            .filter(|(subject, decided)| {
                // Exhaustive by the import-denylist rule: a new `Decision`
                // variant is classified here, never swept into a wildcard.
                let optional = match decided {
                    decision::Decision::Opt { .. } => true,
                    decision::Decision::Ref { .. }
                    | decision::Decision::InferredRef { .. }
                    | decision::Decision::Slice { .. }
                    | decision::Decision::NestedSlice { .. }
                    | decision::Decision::Cursor { .. }
                    | decision::Decision::Box(_)
                    | decision::Decision::Degraded(_) => false,
                };
                optional && SignatureClassId::of(subject.fn_did) == owner
            })
            .map(|(subject, _)| subject.label.clone())
            .collect()
    };
    optional(candidate)
        .difference(&optional(prior))
        .next()
        .is_some()
}

/// Is every change this class carries a site the Option family superseded?
///
/// Relay 045 §2. `class_changed` sees the superseded site as an ordinary new
/// dropped site and its derived hold, so the restore step re-requests the owner
/// one stage after the dropped-site path let it through. Both paths must ask the
/// same question.
fn only_change_is_superseded(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    owner: SignatureClassId,
) -> bool {
    let Some(class) = candidate.plan.class_finalization.classes.get(&owner) else {
        return false;
    };
    let old = prior.plan.class_finalization.classes.get(&owner);
    let new_sites = class
        .sites
        .iter()
        .filter(|site| !old.is_some_and(|old| old.sites.contains(site)))
        .collect::<Vec<_>>();
    if new_sites.is_empty() {
        return false;
    }
    if !new_sites
        .iter()
        .all(|site| superseded_by_an_option_destination(site, owner, prior, candidate))
    {
        return false;
    }
    let superseded: BTreeSet<String> = new_sites
        .iter()
        .filter_map(|site| match &site.state {
            plan::ClassSiteState::Dropped(reason) => {
                Some(format!("dropped-site:{}:{}", site.key.bridge_kind, reason))
            }
            _ => None,
        })
        .collect();
    class
        .hold_reasons()
        .iter()
        .filter(|reason| !old.is_some_and(|old| old.hold_reasons().contains(reason)))
        .all(|reason| superseded.contains(reason))
}

/// **035 clause (2) — the two absolute protections (R453-2).**
///
/// Neither is a soundness device: the exclusion re-derivation decides no form,
/// so over-retirement is a completeness cost only (report 034 §2). What
/// retirement buys is interface consistency, which is a property of sites at
/// intervals — so a candidate whose own sites do not participate in the
/// terminal cannot be making the interface inconsistent, and retiring it buys
/// nothing at all. These two classes of candidate are the measured cost of
/// retiring them anyway, and they are retirable ONLY under clause (1).
///
/// * **placed at the predecessor frame** — placement IS the statement that the
///   previous frame's interface was consistent with this candidate. A
///   neighbour's change that does not touch its interval cannot have made it
///   inconsistent (wave-6s 020: twelve placements lost at zero rule change;
///   slicecursor 030: heman's four `edt` cursor rows).
/// * **the sole candidate its owner has at this stage** — the loop's reading of
///   the instrument's owner-function-scoped `sole_blocker`: retiring it does not
///   remove an inconsistency, it removes the attribution, turning "blocked by
///   exactly one thing" into "no candidate at all" (wave-6s's 34 sole-blocker
///   rows among 114 stage-withdrawn; slicecursor 029's ten bzip2 walkers).
fn protected_from_retirement(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    policy: &FamilyPolicy,
    owner: SignatureClassId,
    hir: HirId,
) -> bool {
    let placed_at_predecessor = candidate
        .table
        .entries
        .iter()
        .find(|(subject, _)| subject.fn_did == owner.local_def_id() && subject.hir_id == hir)
        .is_some_and(|(subject, _)| {
            // `Edit::subject_id` is `identity_key(<owner path>)`, i.e.
            // `<owner>::<param>#<local>`; matching on the tail keeps this
            // independent of how the owner path is spelled at this stage.
            let tail = format!(
                "::{}#{}",
                subject.param_name.as_deref().unwrap_or("<unnamed>"),
                subject.local.as_u32()
            );
            prior
                .plan
                .by_file
                .values()
                .flatten()
                .any(|edit| edit.owner_class == Some(owner) && edit.subject_id.ends_with(&tail))
        });
    if placed_at_predecessor {
        return true;
    }
    // The instrument's `sole_blocker` is owner-function-scoped: a degraded row
    // is a sole blocker when its owner has exactly one DISTINCT degraded
    // reason. Read on the PREDECESSOR frame, that is the candidate whose
    // subject was the one thing standing between this owner and delivery; if
    // the loop retires it now, the attribution the forecast rule reads
    // (R452-2: sole-blocker ∧ stage-enabled) is gone, and the subject reads as
    // having had no candidate at all rather than one blocked thing.
    let mut reasons = BTreeSet::new();
    let mut carried_the_only_reason = false;
    for (subject, decided) in &prior.table.entries {
        if subject.fn_did != owner.local_def_id() {
            continue;
        }
        // Exhaustive by the import-denylist rule.
        match decided {
            decision::Decision::Degraded(degradation) => {
                reasons.insert(degradation.reason.key().to_owned());
                if subject.hir_id == hir {
                    carried_the_only_reason = true;
                }
            }
            decision::Decision::Ref { .. }
            | decision::Decision::InferredRef { .. }
            | decision::Decision::Opt { .. }
            | decision::Decision::Slice { .. }
            | decision::Decision::NestedSlice { .. }
            | decision::Decision::Cursor { .. }
            | decision::Decision::Box(_) => {}
        }
    }
    carried_the_only_reason && reasons.len() == 1
}

pub(crate) fn withdrawals(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    policy: &FamilyPolicy,
    soundness: &[SoundnessWithdrawal],
) -> Vec<FamilyWithdrawal> {
    if policy.stage == FamilyStage::Core {
        return Vec::new();
    }
    let related_graph = related_graph(candidate);
    let enabled = |owner: SignatureClassId| policy.enabled(owner.local_def_id(), policy.stage);
    let anchors = anchors(prior, candidate, policy, soundness, &enabled);

    // R397-6(a): resolve each anchor to the candidates that moved. A direct
    // anchor excludes its own moved candidates, narrowed to those its terminal
    // sites name; an anchor that moved nothing falls back as a whole (the R220
    // floor — its own non-decision mechanics are the cheapest thing to drop). A
    // restore anchor searches its interface component nearest-first and stops
    // at the first distance carrying a changed owner, instead of withdrawing
    // every changed owner the component can reach.
    let mut requested = BTreeMap::<SignatureClassId, (String, Vec<HirId>)>::new();
    let mut unresolved_rows = BTreeMap::<SignatureClassId, String>::new();
    let mut request = |owner: SignatureClassId, cause: String, subjects: Vec<HirId>| {
        requested.entry(owner).or_insert((cause, subjects));
    };
    let mut unresolved = |anchor: SignatureClassId, cause: String| {
        unresolved_rows.entry(anchor).or_insert(cause);
    };
    let scoped_cause = |anchor: SignatureClassId, cause: &str| {
        format!(
            "exclusion-rederivation:anchor={}:{cause}",
            anchor.order_key()
        )
    };
    for (anchor, (cause, kind)) in &anchors {
        match kind {
            Anchor::Direct(sites) => {
                let mut own = moved(prior, candidate, policy, *anchor);
                let named = sites
                    .iter()
                    .flat_map(|site| named_by(candidate, *anchor, site))
                    .collect::<Vec<_>>();
                // **035 clause (1) — participation, not proximity.** A
                // candidate is retirable at this terminal iff one of its own
                // sites is named by it. Where the terminal names participants
                // the set is exactly those; where it names none, clause (2)
                // still protects the placed and the sole candidate, and what
                // is left may yield so the round can make progress.
                if own.iter().any(|hir| named.contains(hir)) {
                    own.retain(|hir| named.contains(hir));
                } else if !sites.is_empty() {
                    // The terminal names sites and none of them is this
                    // candidate's: clause (2) keeps the placed and the sole
                    // blocker out of a retirement they do not participate in.
                    own.retain(|hir| {
                        !protected_from_retirement(prior, candidate, policy, *anchor, *hir)
                    });
                }
                // A terminal with NO sites is a refusal or a new dependency of
                // this class's own subjects, so the class IS the participant
                // and every moved candidate of it satisfies clause (1).
                if !own.is_empty() {
                    request(*anchor, scoped_cause(*anchor, cause), own);
                    continue;
                }
                // The anchor moved no decision of its own: R220's owner
                // fallback drops only its non-decision mechanics at this stage
                // (the seam / interface edges it generated) and is the cheapest
                // input change that can dissolve its terminal — tulipindicators
                // `ti_sma_start`'s new dependency on a held caller dissolves
                // this way while the caller keeps both of its slices. If the
                // loss persists, the next round treats the anchor as a restore
                // root and asks its nearest changed neighbour for the moved
                // candidate that induced the terminal (binn `binn_get_bool`).
                // **035 clause (1) at SITE granularity.** The anchor moved no
                // decision of its own, so there is no candidate to narrow — but
                // the terminal may still name a site of THIS class, and then the
                // participant is the class's own mechanics (the seam / interface
                // edge it generated). Dropping those is retiring the
                // participant, not a neighbour, and it is R220's owner fallback
                // in its justified form.
                //
                // **Clause (3)** is what happens otherwise: the terminal names
                // nothing of this class, so the loop records it and retires
                // nothing. That is the mechanism report 034 priced at 506
                // owner-scoped transactions naming 2,522 subjects.
                // A terminal with NO sites is a refusal of this class's own
                // subjects, so the class is the participant; otherwise the
                // participant is whoever owns a named site.
                let own_site = sites.is_empty()
                    || sites.iter().any(|site| {
                        site.owner_class == *anchor || site.caller == anchor.local_def_id()
                    });
                if own_site {
                    request(*anchor, cause.clone(), Vec::new());
                } else {
                    unresolved(*anchor, format!("interface-path-unresolved:{cause}"));
                }
            }
            Anchor::Restore => {
                let mut frontier = vec![(*anchor, vec![*anchor])];
                let mut seen = BTreeSet::from([*anchor]);
                let mut resolved = false;
                while !frontier.is_empty() {
                    let mut next = Vec::new();
                    let mut layer = Vec::new();
                    for (owner, path) in frontier {
                        for &neighbour in related_graph.get(&owner).into_iter().flatten() {
                            if !seen.insert(neighbour) {
                                continue;
                            }
                            let mut next_path = path.clone();
                            next_path.push(neighbour);
                            if enabled(neighbour) && class_changed(prior, candidate, neighbour) {
                                layer.push((neighbour, next_path.clone()));
                            }
                            next.push((neighbour, next_path));
                        }
                    }
                    if !layer.is_empty() {
                        for (owner, path) in layer {
                            let path = path
                                .iter()
                                .map(|owner| owner.order_key())
                                .collect::<Vec<_>>();
                            let cause = format!("restore-family-interface-path:{path:?}");
                            // **035 clauses (2)+(3), amended by measurement.**
                            // The nearest-first restore stays — report 009's
                            // binn case is a delivery only this step recovers —
                            // but it may no longer retire a candidate that was
                            // PLACED at the predecessor frame or is its
                            // owner's sole blocker. Where every candidate it
                            // can reach is protected, the loop records
                            // `interface-path-unresolved:` and retires nothing,
                            // which is the 506 owner-scoped transactions report
                            // 034 priced.
                            let subjects = moved(prior, candidate, policy, owner);
                            if subjects.is_empty() {
                                unresolved(owner, format!("interface-path-unresolved:{cause}"));
                            } else {
                                request(owner, scoped_cause(*anchor, &cause), subjects);
                            }
                        }
                        resolved = true;
                        break;
                    }
                    frontier = next;
                }
                // The component held no changed owner: the edge that would
                // have joined the root to its cause is the very site that is
                // missing (a cursor handed to a slice callee with no C bridge
                // to render leaves the callee's class held and the two classes
                // unconnected). The last resort before the whole program fails
                // `unrestored` is the program-wide layer — every enabled
                // changed owner yields, its moved candidates per subject.
                if !resolved {
                    for owner in candidate.plan.class_finalization.classes.keys() {
                        if *owner == *anchor
                            || !enabled(*owner)
                            || !class_changed(prior, candidate, *owner)
                        {
                            continue;
                        }
                        let cause =
                            format!("restore-family-unconnected-root:{}", anchor.order_key());
                        let subjects = moved(prior, candidate, policy, *owner);
                        if subjects.is_empty() {
                            unresolved(*owner, format!("interface-path-unresolved:{cause}"));
                        } else {
                            request(*owner, scoped_cause(*anchor, &cause), subjects);
                        }
                    }
                }
            }
        }
    }
    let mut out = requested
        .into_iter()
        .map(|(owner, (cause, subjects))| FamilyWithdrawal {
            unresolved: false,
            owner,
            cause,
            subjects,
        })
        .collect::<Vec<_>>();
    let retired_owners = out.iter().map(|w| w.owner).collect::<BTreeSet<_>>();
    out.extend(
        unresolved_rows
            .into_iter()
            .filter(|(owner, _)| !retired_owners.contains(owner))
            .map(|(owner, cause)| FamilyWithdrawal {
                unresolved: true,
                owner,
                cause,
                subjects: Vec::new(),
            }),
    );
    out
}

/// The R220 generator, unchanged in what it observes: which owners carry a new
/// terminal, and which prior deliveries are lost with no transaction of their
/// own left to withdraw. Scoping is `withdrawals`' job.
fn anchors(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    policy: &FamilyPolicy,
    soundness: &[SoundnessWithdrawal],
    enabled: &impl Fn(SignatureClassId) -> bool,
) -> BTreeMap<SignatureClassId, (String, Anchor)> {
    let protected = losses(prior, candidate, soundness)
        .into_iter()
        .map(|s| SignatureClassId::of(s.fn_did))
        .collect::<BTreeSet<_>>();
    let witnessed_owners = soundness
        .iter()
        .map(|s| SignatureClassId::of(s.subject.0))
        .filter(|owner| !protected.contains(owner))
        .collect::<BTreeSet<_>>();
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
    let mut requested = BTreeMap::<SignatureClassId, (String, Anchor)>::new();
    // Restore anchors are kept apart so they never count as a covering request
    // for a collision partner or a later protected owner (R220 parity).
    let mut restore = BTreeSet::<SignatureClassId>::new();
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
            let newer_edit_key = if old_left {
                &collision.right_edit_key
            } else {
                &collision.left_edit_key
            };
            let site = candidate
                .plan
                .class_finalization
                .classes
                .get(&owner)
                .and_then(|class| {
                    class
                        .sites
                        .iter()
                        .find(|site| site.edit_key == *newer_edit_key)
                })
                .map(|site| site.key.clone());
            requested.insert(
                owner,
                (
                    format!(
                        "newer-family-collision:{}|{}",
                        collision.left_edit_key, collision.right_edit_key
                    ),
                    Anchor::Direct(site.into_iter().collect()),
                ),
            );
        }
    }
    for (owner, class) in &candidate.plan.class_finalization.classes {
        if !enabled(*owner) || witnessed_owners.contains(owner) {
            continue;
        }
        let old = prior.plan.class_finalization.classes.get(owner);
        let new_dropped = class
            .sites
            .iter()
            .filter(|site| {
                matches!(site.state, plan::ClassSiteState::Dropped(_))
                    && !old.is_some_and(|old| old.sites.contains(site))
                    && site.key.bridge_kind != "missing-required-site"
                    && !superseded_by_an_option_destination(site, *owner, prior, candidate)
            })
            .collect::<Vec<_>>();
        if let Some(site) = new_dropped.first() {
            requested.entry(*owner).or_insert_with(|| {
                (
                    format!(
                        "unsatisfied-family-site:{}:{:?}",
                        site.key.receipt_key(),
                        site.state
                    ),
                    Anchor::Direct(new_dropped.iter().map(|site| site.key.clone()).collect()),
                )
            });
            continue;
        }
        // Relay 043: the same supersession, on the hold the finalizer derives
        // from that site (`plan::finalize_class_inputs` spells it
        // `dropped-site:<kind>:<reason>`). Filtering only the site list would
        // leave the refusal branch requesting for the very drop the arm has
        // just ruled superseded.
        let superseded: BTreeSet<String> = class
            .sites
            .iter()
            .filter(|site| superseded_by_an_option_destination(site, *owner, prior, candidate))
            .filter_map(|site| match &site.state {
                plan::ClassSiteState::Dropped(reason) => {
                    Some(format!("dropped-site:{}:{}", site.key.bridge_kind, reason))
                }
                _ => None,
            })
            .collect();
        // **R456-7 (wave-6o 021 claim 3), MEASURED AND NOT APPLIED.** The
        // ruling is that a composed pair the final plan accepts is not a
        // refusal at any stage. Exempting `intra-class-interval-overlap` here
        // unconditionally is NOT that rule: it also exempts the pairs the final
        // plan still holds, and report 037 measures what that costs — wave-6o's
        // own `wave6o_null_init_local_with_no_pending_row_still_receives_its_
        // declaration` stops delivering, and one wave-5c `thin_counted` row
        // moves. The stage cannot ask "does the final plan accept it?" as the
        // code stands, because the composing edit is not kinded
        // (`option-value-composed`) until after this stage runs. See report 037
        // §1 for what would make it decidable.
        let new_refusal = class.hold_reasons().iter().find(|reason| {
            !reason.starts_with("dependency-class-held:")
                && *reason != "cross-class-interval-collision"
                && !superseded.contains(*reason)
                && !old.is_some_and(|old| old.hold_reasons().contains(reason))
        });
        if let Some(reason) = new_refusal {
            requested.entry(*owner).or_insert_with(|| {
                (
                    format!("unwitnessed-family-refusal:{reason}"),
                    Anchor::Direct(Vec::new()),
                )
            });
        }
    }
    // A dependency casualty yields at the changed root transaction. Do not
    // disable the old dependent just because the finalizer propagated a hold.
    for owner in protected {
        let mut pending = vec![owner];
        let mut seen = BTreeSet::new();
        let before = (requested.len(), restore.len());
        while let Some(current) = pending.pop() {
            if !seen.insert(current) || requested.contains_key(&current) {
                continue;
            }
            let Some(class) = candidate.plan.class_finalization.classes.get(&current) else {
                if enabled(current) {
                    requested.insert(
                        current,
                        (
                            "missing-prior-family-class".to_owned(),
                            Anchor::Direct(Vec::new()),
                        ),
                    );
                } else {
                    restore.insert(current);
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
                    (
                        format!("new-family-dependency:{}", dependency.order_key()),
                        Anchor::Direct(Vec::new()),
                    ),
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
            // Relay 045 §2 (wave-6o 018 STOP 1): the supersession is evaluated
            // BEFORE the restore step, or the same owner withdraws one step
            // later for the same superseded site — which is exactly what
            // wave-6o measured once `fe931479f` removed the earlier path
            // (`…:anchor=3:restore-prior-family-disposition`). A class whose
            // only change is a superseded site has not changed for this
            // purpose.
            if enabled(current)
                && class_changed(prior, candidate, current)
                && !only_change_is_superseded(prior, candidate, current)
            {
                requested.insert(
                    current,
                    (
                        "restore-prior-family-disposition".to_owned(),
                        Anchor::Direct(Vec::new()),
                    ),
                );
                continue;
            }
            restore.insert(current);
        }
        // Mutually dependent held classes (binn `is_bool_str` ↔ `binn_get_bool`)
        // walk each other's held dependency and request nothing; the lost root
        // is then a restore anchor, not an `unrestored` failure.
        if (requested.len(), restore.len()) == before {
            restore.insert(owner);
        }
    }
    for owner in restore {
        requested
            .entry(owner)
            .or_insert(("lost-prior-delivery".to_owned(), Anchor::Restore));
    }
    requested
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
            let source = if policy.enabled_for(*key, family) {
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
    /// `owner`: the whole owner fell back to its predecessor stage (the R220
    /// transaction). `subject`: R397-6(a) — only the named candidate rows are
    /// excluded at the selection input; the owner and its siblings keep the
    /// stage.
    pub(crate) scope: String,
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
