//! **Phase 2 — plan.** Decision table in, edits-as-data out. No AST mutation.
//!
//! An edit is a value, and it carries **its own justification**: a re-route
//! carries the `LoanKey` that licenses it (§1.6 admissibility is a content
//! lookup, so the licensing loan is nameable), and a drop-form edit carries the
//! selector site that motivated it. That is what lets [`super::apply`] be
//! analysis-blind — it never has to ask *why*, because the edit says so.
//!
//! # Edits are byte-range splices
//!
//! An edit replaces a half-open byte range of the ORIGINAL source with new
//! text. Two properties follow, and both are why this representation was
//! chosen over pretty-printing a rewritten AST:
//!
//! 1. **Structure-preserving by construction.** Everything outside the edited
//!    ranges is the input, byte for byte — comments, spacing and macro shapes
//!    included. The frozen rewriter's whole-crate pretty-print is exactly the
//!    defect this avoids.
//! 2. **Insertions are the zero-width case** (`lo == hi`), so the statement
//!    insertions S3 needs for drops and moves are the same mechanism, not a
//!    second one.
//!
//! # E1 state visibility
//!
//! Reads the decision table by value. Does NOT read analyses, the export, or
//! decision internals beyond the table it was handed. Hands `apply` a plan by
//! value.
//!
//! # Status
//!
//! S1 lands the **G01 arm**: a pointer parameter's type becomes a reference
//! type. [`Justification`] is shaped against all ten goldens' expected text so
//! the breadth in S2–S3 fills arms rather than reshaping the type.

use std::{collections::BTreeMap, path::PathBuf};

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSiteKey, BridgeSitePlan,
        SignatureClassId,
    },
    decision::{Arm, Decision, DecisionTable, RequiredArmSet},
};

/// Which source file an edit belongs to.
///
/// # Why an enum rather than a `PathBuf`
///
/// The string entry point compiles through `FileName::Custom("main.rs")`, **not**
/// `FileName::Real` — so a key that could only hold a real path would reject
/// every golden. Both cases are first-class here; only [`FileKey::Real`] is
/// writable back to disk, which is the emit layer's concern, not the plan's.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FileKey {
    /// A file on disk.
    Real(PathBuf),
    /// A virtual root — the string entry point's `main.rs`.
    Virtual(String),
}

fn file_key_label(key: &FileKey) -> String {
    match key {
        FileKey::Real(path) => path.display().to_string(),
        FileKey::Virtual(name) => name.clone(),
    }
}

/// A decision that could not be turned into a placed edit.
///
/// **Counted and attributed, never silently dropped.**
///
/// # Expected zero — what is true today, stated exactly
///
/// **Measured** zero on all 20 frozen-corpus programs (S2b.1's emit run), and
/// **not asserted anywhere**: `m1_emit_corpus` reports the count into its row
/// under its measurement-only discipline, and nothing fails on a nonzero. The
/// pin is **scheduled for S2b.3**, alongside the placement-true counters that
/// give it something to be consistent with.
///
/// This doc previously read "aggregate-pinned expected-zero on the frozen
/// corpus". It was pinned nowhere. Prose asserting a check the code does not
/// have is this track's founding failure class, so the claim does not outlive
/// the slice that measured it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Unplaceable {
    pub owner_class: SignatureClassId,
    pub bridge: BridgeSitePlan,
    pub reason: &'static str,
    /// Attribution — which subject, in the artifact's own terms.
    pub detail: String,
    /// **Identity**, in the `owner_fn::param` form the driver keys emitted
    /// subjects by — which [`Self::detail`] is not: `"p (param #0)"` compares
    /// equal for the `p` of every function in the crate.
    ///
    /// Its purpose is subtraction, not display. `emitted` counts PLACEMENTS as
    /// of S2b.3, and the only way to exclude a decision that produced no edit is
    /// to name it in the same terms the emitting side names its own.
    pub subject: String,
}

/// Why an edit is licensed. **Shaped against all ten goldens; one arm live.**
///
/// The unbuilt arms are deliberate: designing the justification type against
/// every golden now means S3 adds construction sites, not a new type — and the
/// breadth hedge for the walking-skeleton cut rests on exactly that.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(
    dead_code,
    reason = "KindDecision and SeamAdapter are BOTH live; ReRoute/DropForm/\
              StoreForm are shaped against goldens g04-g08 on purpose, so the \
              slice that builds drops and moves adds construction sites rather \
              than reshaping the type. Their emptiness is MEASURED, not \
              assumed: arm 4's census counts every variant per program and the \
              corpus gate holds those three at zero."
)]
pub(crate) enum Justification {
    /// G01–G03: BO decided this slot is a reference. **Live at S1.**
    KindDecision { kind: &'static str },
    /// G06: a move re-route, licensed by a specific surviving loan. The
    /// `LoanKey` is rendered rather than held so `plan` carries no analysis
    /// type into `apply` — the import rule forbids it, and the string is the
    /// audit trail, not a lookup handle.
    ReRoute { licensing_loan: String },
    /// G04/G05/G08: a drop-form edit (§5.3 (D)), motivated by a selector site.
    DropForm { selector_site: String },
    /// **S3.6-1**: one expression of glue at a mismatched argument position.
    /// `family` is `"safe"` or `"reborrow"` — the latter carries the aliasing
    /// exposure §5a measured, so the two must stay countable apart.
    SeamAdapter {
        family: &'static str,
        /// **Whether this adapter's length was FABRICATED** (ruling
        /// 2026-08-12). Carried from `spec.len`, never re-derived by testing
        /// the replacement text for the const's name — the classifier
        /// anti-pattern this milestone retired once already.
        ///
        /// It is here rather than only in the seam census because the const
        /// item's insertion is conditioned on a fabricated adapter **surviving
        /// the revert set**, and the surviving set is a `plan` fact.
        fabricated: bool,
    },
    /// A5 C-9 snapshot temp at one retained marked call site.
    C9Mark,
    /// E2-FN structural signature emission, keyed to the finalized plan bytes.
    /// The AST pass owns node placement; this typed justification keeps the
    /// receipt vocabulary aligned with span/seam ownership.
    LifetimePlan { digest: String },
    /// **The fabricated-extent const's declaration** (marker ruling,
    /// 2026-08-15). One per crate, in the crate root file, emitted only when at
    /// least one fabricated adapter survives.
    ///
    /// It has no owning subject, and that is deliberate: keying it to one
    /// adapter's `owner_fn` would delete the const when that function reverts
    /// while other sites still name it (`E0433`, cascading), and keying it to a
    /// never-reverted sentinel would leave a dead const behind when every
    /// fabricated site reverts. It is DERIVED from the surviving edits instead,
    /// which is why it is created after the revert filter rather than before.
    FabricatedLenConst,
    /// G07/G09: a store form that must NOT drop — (N-raw)/(N-safe)/(R) — or a
    /// P-drop suppression, carrying which rule applied.
    StoreForm { form: &'static str },
}

/// One byte-range splice into the original source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Edit {
    /// Byte offset into the ORIGINAL source, inclusive.
    pub lo: usize,
    /// Byte offset into the ORIGINAL source, exclusive. `lo == hi` inserts.
    pub hi: usize,
    pub replacement: String,
    pub justification: Justification,
    /// **The subject whose rewrite JUSTIFIES this edit** — not the file the edit
    /// lands in, and not necessarily the function containing it.
    ///
    /// In M1 the two coincide: a parameter's type is rewritten inside its own
    /// declaration. **They diverge at S3**, whose call-site adaptation emits
    /// edits into CALLER files while the edit is justified by the CALLEE's
    /// subject. The verify loop reverts by JUSTIFICATION, never by geography —
    /// reverting the file or the containing function would take back edits the
    /// culprit did not cause and leave the ones it did.
    ///
    /// Direct signature-class identity. `None` is reserved for the derived
    /// crate-level fallback-extent declaration, which has no owning class.
    pub owner_class: Option<SignatureClassId>,
    /// Human-readable path for receipts only. No production decision may parse
    /// or compare this value.
    pub owner_path: String,
    /// Typed receipt identity. `None` is reserved for the derived crate-level
    /// fallback-extent declaration, which has no signature class of its own.
    pub bridge: Option<BridgeSitePlan>,
    /// Exact raw-boundary dependency group. Empty for every pre-wave edit.
    /// A group is carried, not reconstructed, so removing one atom can remove
    /// its declaration/use/seam closure while leaving an independent subject
    /// in the same function intact.
    pub atom_ids: Vec<String>,
    /// Canonical subject identity and full required-arm set captured when the
    /// edit is planned. The verifier's EditKey consumes these fields directly;
    /// it never guesses an arm from replacement text.
    pub subject_id: String,
    pub required_arms: String,
    pub edit_kind: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ClassSiteState {
    EditReady,
    ZeroSyntaxReady,
    Dropped(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClassSite {
    pub key: BridgeSiteKey,
    pub edit_key: String,
    pub state: ClassSiteState,
    pub extent: BridgeExtentKind,
    pub retention: BridgeRetentionTier,
    pub waiver_id: Option<String>,
}

impl ClassSite {
    pub(crate) fn edit(
        owner: SignatureClassId,
        caller: SignatureClassId,
        arm: Arm,
        file: &str,
        lo: u32,
        hi: u32,
        kind: &str,
    ) -> Self {
        let key = BridgeSiteKey {
            owner_class: owner,
            caller: caller.local_def_id(),
            callee: BridgeCalleeId::Local(owner.local_def_id()),
            arm: arm.key().to_owned(),
            position: format!("{lo}..{hi}"),
            file: file.to_owned(),
            lo,
            hi,
            bridge_kind: kind.to_owned(),
        };
        Self {
            edit_key: format!(
                "class={}|arm={}|interval={file}:{lo}:{hi}|kind={kind}",
                owner.order_key(),
                arm.key()
            ),
            key,
            state: ClassSiteState::EditReady,
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        }
    }

    pub(crate) fn zero(
        owner: SignatureClassId,
        caller: SignatureClassId,
        arm: Arm,
        kind: &str,
    ) -> Self {
        Self {
            key: BridgeSiteKey {
                owner_class: owner,
                caller: caller.local_def_id(),
                callee: BridgeCalleeId::Local(owner.local_def_id()),
                arm: arm.key().to_owned(),
                position: "zero-syntax".to_owned(),
                file: "-".to_owned(),
                lo: 0,
                hi: 0,
                bridge_kind: kind.to_owned(),
            },
            edit_key: "-".to_owned(),
            state: ClassSiteState::ZeroSyntaxReady,
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        }
    }

    pub(crate) fn dropped(
        owner: SignatureClassId,
        caller: SignatureClassId,
        arm: Arm,
        kind: &str,
        reason: impl Into<String>,
    ) -> Self {
        let mut site = Self::zero(owner, caller, arm, kind);
        site.state = ClassSiteState::Dropped(reason.into());
        site
    }

    fn has_text_interval(&self) -> bool {
        self.edit_key != "-" && self.key.file != "-"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SignatureClassDisposition {
    Ready,
    Held(Vec<String>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SignatureClassPlan {
    pub id: SignatureClassId,
    pub required_arms: RequiredArmSet,
    pub site_keys: Vec<BridgeSiteKey>,
    pub edit_keys: Vec<String>,
    pub depends_on: Vec<SignatureClassId>,
    pub disposition: SignatureClassDisposition,
    pub sites: Vec<ClassSite>,
}

impl SignatureClassPlan {
    pub(crate) fn is_ready(&self) -> bool {
        self.disposition == SignatureClassDisposition::Ready
    }

    pub(crate) fn hold_reasons(&self) -> &[String] {
        match &self.disposition {
            SignatureClassDisposition::Ready => &[],
            SignatureClassDisposition::Held(reasons) => reasons,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClassInput {
    pub id: SignatureClassId,
    pub required_arms: RequiredArmSet,
    pub sites: Vec<ClassSite>,
    pub depends_on: Vec<SignatureClassId>,
    pub block_reasons: Vec<String>,
}

impl ClassInput {
    pub(crate) fn new(id: SignatureClassId, required_arms: RequiredArmSet) -> Self {
        Self {
            id,
            required_arms,
            sites: Vec::new(),
            depends_on: Vec::new(),
            block_reasons: Vec::new(),
        }
    }

    pub(crate) fn with_site(mut self, site: ClassSite) -> Self {
        self.sites.push(site);
        self
    }

    pub(crate) fn blocked(mut self, reason: impl Into<String>) -> Self {
        self.block_reasons.push(reason.into());
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClassIntervalCollision {
    pub left_class: SignatureClassId,
    pub right_class: SignatureClassId,
    pub left_edit_key: String,
    pub right_edit_key: String,
    pub file: String,
    pub lo: u32,
    pub hi: u32,
    pub left_kind: String,
    pub right_kind: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ClassFinalization {
    pub classes: BTreeMap<SignatureClassId, SignatureClassPlan>,
    pub collisions: Vec<ClassIntervalCollision>,
}

impl ClassFinalization {
    pub(crate) fn applied_site_count(&self) -> usize {
        self.classes
            .values()
            .filter(|class| class.is_ready())
            .map(|class| class.sites.len())
            .sum()
    }

    pub(crate) fn live_sites<'a>(
        &'a self,
        reverted: &'a std::collections::BTreeSet<SignatureClassId>,
    ) -> impl Iterator<Item = &'a ClassSite> + 'a {
        self.classes
            .values()
            .filter(move |class| class.is_ready() && !reverted.contains(&class.id))
            .flat_map(|class| class.sites.iter())
    }
}

fn intervals_overlap(left: &ClassSite, right: &ClassSite) -> bool {
    if left.key.file != right.key.file {
        return false;
    }
    if left.key.lo == left.key.hi && right.key.lo == right.key.hi {
        return left.key.lo == right.key.lo;
    }
    left.key.lo < right.key.hi && right.key.lo < left.key.hi
}

pub(crate) fn finalize_class_inputs(inputs: Vec<ClassInput>) -> ClassFinalization {
    let mut merged = BTreeMap::<SignatureClassId, ClassInput>::new();
    for input in inputs {
        merged
            .entry(input.id)
            .and_modify(|class| {
                class.required_arms = class.required_arms.union(input.required_arms);
                class.sites.extend(input.sites.clone());
                class.depends_on.extend(input.depends_on.iter().copied());
                class.block_reasons.extend(input.block_reasons.clone());
            })
            .or_insert(input);
    }

    let all_sites = merged
        .values()
        .flat_map(|class| class.sites.iter())
        .filter(|site| site.has_text_interval())
        .cloned()
        .collect::<Vec<_>>();
    let mut collisions = Vec::new();
    for (left_index, left) in all_sites.iter().enumerate() {
        for right in &all_sites[left_index + 1..] {
            if left.key.owner_class == right.key.owner_class || !intervals_overlap(left, right) {
                continue;
            }
            let (left, right) = if left.key.owner_class <= right.key.owner_class {
                (left, right)
            } else {
                (right, left)
            };
            let lo = left.key.lo.max(right.key.lo);
            let hi = left.key.hi.min(right.key.hi);
            collisions.push(ClassIntervalCollision {
                left_class: left.key.owner_class,
                right_class: right.key.owner_class,
                left_edit_key: left.edit_key.clone(),
                right_edit_key: right.edit_key.clone(),
                file: left.key.file.clone(),
                lo,
                hi,
                left_kind: left.key.bridge_kind.clone(),
                right_kind: right.key.bridge_kind.clone(),
            });
        }
    }
    collisions.sort_by(|left, right| {
        (
            left.file.as_str(),
            left.lo,
            left.hi,
            left.left_class,
            left.right_class,
            left.left_edit_key.as_str(),
            left.right_edit_key.as_str(),
        )
            .cmp(&(
                right.file.as_str(),
                right.lo,
                right.hi,
                right.left_class,
                right.right_class,
                right.left_edit_key.as_str(),
                right.right_edit_key.as_str(),
            ))
    });

    for collision in &collisions {
        for class in [collision.left_class, collision.right_class] {
            merged
                .get_mut(&class)
                .expect("collision class came from merged inputs")
                .block_reasons
                .push("cross-class-interval-collision".to_owned());
        }
    }

    let classes = merged
        .into_iter()
        .map(|(id, mut input)| {
            let missing_arms = Arm::ALL
                .into_iter()
                .filter(|&arm| {
                    input.required_arms.contains(arm)
                        && !input.sites.iter().any(|site| site.key.arm == arm.key())
                })
                .collect::<Vec<_>>();
            for arm in missing_arms {
                let reason = format!("missing-required-arm:{}", arm.key());
                input.block_reasons.push(reason.clone());
                input.sites.push(ClassSite::dropped(
                    id,
                    id,
                    arm,
                    "missing-required-site",
                    reason,
                ));
            }
            for site in &input.sites {
                if let ClassSiteState::Dropped(reason) = &site.state {
                    input
                        .block_reasons
                        .push(format!("dropped-site:{}:{}", site.key.bridge_kind, reason));
                }
            }
            input.sites.sort_by_key(|site| site.key.receipt_key());
            input.sites.dedup_by(|left, right| left.key == right.key);
            input.depends_on.sort();
            input.depends_on.dedup();
            input.block_reasons.sort();
            input.block_reasons.dedup();
            let site_keys = input.sites.iter().map(|site| site.key.clone()).collect();
            let edit_keys = input
                .sites
                .iter()
                .map(|site| site.edit_key.clone())
                .collect();
            let disposition = if input.block_reasons.is_empty() {
                SignatureClassDisposition::Ready
            } else {
                SignatureClassDisposition::Held(input.block_reasons)
            };
            (
                id,
                SignatureClassPlan {
                    id,
                    required_arms: input.required_arms,
                    site_keys,
                    edit_keys,
                    depends_on: input.depends_on,
                    disposition,
                    sites: input.sites,
                },
            )
        })
        .collect();
    ClassFinalization {
        classes,
        collisions,
    }
}

fn arm_from_key(key: &str) -> Option<Arm> {
    Arm::ALL.into_iter().find(|arm| arm.key() == key)
}

/// Finalize the real plan into atomic signature classes and remove every edit
/// whose class is held. All inputs are rewriter-side carriers; no analysis or
/// cache key is consulted here.
pub(crate) fn finalize_signature_classes(
    planned: &mut Plan,
    table: &DecisionTable,
    pre_reverted: &rustc_hash::FxHashSet<rustc_hir::def_id::LocalDefId>,
) {
    use sha2::{Digest, Sha256};

    let mut by_class = BTreeMap::<SignatureClassId, ClassInput>::new();
    let mut degraded = BTreeMap::<SignatureClassId, Vec<String>>::new();
    for (subject, decision) in &table.entries {
        let id = SignatureClassId::of(subject.fn_did);
        let mut required = table
            .arm_requirements
            .get(&(subject.fn_did, subject.hir_id))
            .copied()
            .unwrap_or_default();
        let (emits, degraded_reason) = match decision {
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => (true, None),
            Decision::Degraded(record) => (false, Some(record.reason.key())),
        };
        if emits {
            required.insert(Arm::Surface);
        }
        if emits || !required.is_empty() {
            by_class
                .entry(id)
                .and_modify(|class| class.required_arms = class.required_arms.union(required))
                .or_insert_with(|| ClassInput::new(id, required));
        }
        if let Some(reason) = degraded_reason.filter(|_| !required.is_empty()) {
            degraded.entry(id).or_default().push(reason.to_owned());
        }
    }

    for site in &planned.preclass_sites {
        by_class
            .entry(site.key.owner_class)
            .or_insert_with(|| ClassInput::new(site.key.owner_class, RequiredArmSet::default()))
            .sites
            .push(site.clone());
    }

    for (file, edits) in &planned.by_file {
        let file = file_key_label(file);
        for edit in edits {
            let Some(owner) = edit.owner_class else {
                continue;
            };
            let Some(bridge) = edit.bridge.as_ref() else {
                by_class
                    .entry(owner)
                    .or_insert_with(|| ClassInput::new(owner, RequiredArmSet::default()))
                    .block_reasons
                    .push("missing-bridge-receipt".to_owned());
                continue;
            };
            let lo = u32::try_from(edit.lo).unwrap_or(u32::MAX);
            let hi = u32::try_from(edit.hi).unwrap_or(u32::MAX);
            let key = bridge.materialize(owner, file.clone(), lo, hi);
            let replacement_sha256 = format!("{:x}", Sha256::digest(edit.replacement.as_bytes()));
            let edit_key = format!(
                "class={}|arm={}|interval={}:{}:{}|kind={}|replacement_sha256={}",
                owner.order_key(),
                bridge.arm,
                file,
                edit.lo,
                edit.hi,
                bridge.bridge_kind,
                replacement_sha256
            );
            let required_arm = arm_from_key(&bridge.arm);
            let class = by_class
                .entry(owner)
                .or_insert_with(|| ClassInput::new(owner, RequiredArmSet::default()));
            if let Some(arm) = required_arm {
                class.required_arms.insert(arm);
            } else {
                class
                    .block_reasons
                    .push(format!("unknown-site-arm:{}", bridge.arm));
            }
            class.sites.push(ClassSite {
                key,
                edit_key,
                state: ClassSiteState::EditReady,
                extent: bridge.extent.clone(),
                retention: bridge.retention,
                waiver_id: bridge.waiver_id.clone(),
            });
        }
    }

    for (id, reasons) in degraded {
        if let Some(class) = by_class.get_mut(&id) {
            class.block_reasons.extend(
                reasons
                    .into_iter()
                    .map(|reason| format!("blocked-subject:{reason}")),
            );
        }
    }
    for &did in pre_reverted {
        let id = SignatureClassId::of(did);
        if let Some(class) = by_class.get_mut(&id) {
            class.block_reasons.push("pre-reverted-class".to_owned());
        }
    }

    for class in by_class.values_mut() {
        if class.required_arms.contains(Arm::D4)
            && !class.sites.iter().any(|site| site.key.arm == Arm::D4.key())
        {
            class.sites.push(ClassSite::zero(
                class.id,
                class.id,
                Arm::D4,
                "d4-class-membership",
            ));
        }
        if class.required_arms.contains(Arm::Surface)
            && !class
                .sites
                .iter()
                .any(|site| site.key.arm == Arm::Surface.key())
            && !class
                .block_reasons
                .iter()
                .any(|reason| reason.starts_with("blocked-subject:"))
        {
            class.sites.push(ClassSite::zero(
                class.id,
                class.id,
                Arm::Surface,
                "surface-zero-syntax",
            ));
        }
        if class.required_arms.contains(Arm::Glue)
            && !class
                .sites
                .iter()
                .any(|site| site.key.arm == Arm::Glue.key())
            && !class.sites.iter().any(|site| {
                site.key.arm == Arm::Glue.key() && matches!(site.state, ClassSiteState::Dropped(_))
            })
        {
            class.sites.push(ClassSite::zero(
                class.id,
                class.id,
                Arm::Glue,
                "glue-discharged-by-callee-class",
            ));
        }
    }

    let finalization = finalize_class_inputs(by_class.into_values().collect());
    planned.by_file.retain(|_, edits| {
        edits.retain(|edit| {
            edit.owner_class
                .is_none_or(|class| finalization.classes[&class].is_ready())
        });
        !edits.is_empty()
    });
    planned.class_finalization = finalization;
}

/// The finished plan handed to [`super::apply`], **grouped by file**.
///
/// # Why a map keyed by file
///
/// An edit's byte offsets are **file-relative**, so a flat list of edits across
/// a multi-file crate is ambiguous by construction: two edits in different files
/// can carry identical `(lo, hi)`. Keying by file makes *an edit with no file*
/// unrepresentable rather than merely tested, and `BTreeMap` keeps file
/// iteration deterministic (D19: a report whose order permutes between runs is
/// not comparable).
///
/// 10 of the 20 frozen-corpus programs carry subjects across 2–110 source files,
/// which is why the flat shape could not survive contact with the corpus.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Plan {
    pub by_file: BTreeMap<FileKey, Vec<Edit>>,
    /// Decisions that produced no placed edit, with attribution.
    pub unplaceable: Vec<Unplaceable>,
    /// **The crate ROOT file** — where a crate-level item must go, and the only
    /// place `crate::FALLBACK_SLICE_EXTENT` resolves from.
    ///
    /// Filled by the caller, which is the only party holding a `TyCtxt`; `plan`
    /// itself takes no compiler type. `None` leaves the fabricated-const
    /// insertion **fail-closed** — no root, no insertion, and the fabricated
    /// adapters that need it fail `verify` loudly rather than emitting a crate
    /// with a dangling path.
    pub root_file: Option<FileKey>,
    /// **The fabricated-extent const's TEXT, produced once by the caller.**
    ///
    /// It is carried rather than built where it is spliced because building it
    /// **parses and pretty-prints**, and both need `rustc_span` session globals
    /// — which the verify/revert loop does not have: `rewrite_core`'s `TyCtxt`
    /// closure ends before the loop's `render` calls. Producing it inside
    /// `render` panicked four corpus programs, and only the four in which a
    /// fabricated adapter survived into a loop round.
    ///
    /// So the rule is: **anything needing a compiler session is produced while
    /// one provably exists, and travels as data.** `None` fail-closes — no
    /// text, no insertion, and the adapters that name it fail `verify` loudly
    /// rather than emitting a crate with a dangling path.
    pub len_const_item: Option<String>,
    /// Sites known without a successfully placed text edit (blocked,
    /// unplaceable, or explicit zero-syntax).
    pub preclass_sites: Vec<ClassSite>,
    /// Final signature-class transaction inventory.
    pub class_finalization: ClassFinalization,
}

impl Plan {
    pub(crate) fn class_hold_reason(&self, class: SignatureClassId) -> Option<String> {
        self.class_finalization
            .classes
            .get(&class)
            .filter(|class| !class.is_ready())
            .map(|class| class.hold_reasons().join(";"))
    }

    pub(crate) fn held_classes(&self) -> std::collections::BTreeSet<SignatureClassId> {
        self.class_finalization
            .classes
            .values()
            .filter(|class| !class.is_ready())
            .map(|class| class.id)
            .collect()
    }

    pub(crate) fn bridge_events(
        &self,
        reverted: &std::collections::BTreeSet<SignatureClassId>,
    ) -> Vec<super::bridge_receipt::BridgeReceiptEvent> {
        use super::bridge_receipt::{BridgeReceiptEvent, BridgeReceiptStage, BridgeReceiptState};
        let mut events = Vec::new();
        for class in self.class_finalization.classes.values() {
            let terminal_drop = if reverted.contains(&class.id) {
                Some("class-reverted-after-verify".to_owned())
            } else if !class.is_ready() {
                Some(class.hold_reasons().join(";"))
            } else {
                None
            };
            for site in &class.sites {
                events.push(BridgeReceiptEvent {
                    site: site.key.clone(),
                    stage: BridgeReceiptStage::Plan,
                    state: BridgeReceiptState::Planned,
                    drop_reason: None,
                    extent: site.extent.clone(),
                    retention: site.retention,
                    waiver_id: site.waiver_id.clone(),
                });
                events.push(BridgeReceiptEvent {
                    site: site.key.clone(),
                    stage: BridgeReceiptStage::Terminal,
                    state: if terminal_drop.is_some() {
                        BridgeReceiptState::Dropped
                    } else {
                        BridgeReceiptState::Applied
                    },
                    drop_reason: terminal_drop.clone(),
                    extent: site.extent.clone(),
                    retention: site.retention,
                    waiver_id: site.waiver_id.clone(),
                });
            }
        }
        events
    }
}

/// Turn decisions into edits.
///
/// `source` is read only to copy the pointee's text verbatim: an emitted
/// `&mut i32` keeps the input's own `i32` rather than a re-rendered type, which
/// is what keeps generics, paths and whitespace inside the pointee intact.
/// # Why `source_of` is a per-file lookup and not one `&str`
///
/// **S3-proofing — do not "simplify" this back.** It would be tempting to invoke
/// `plan` once per file with that file's text. That works today, because every
/// edit S1 emits lands in the same file as the subject's declaration. **It
/// breaks at S3:** call-site adaptation emits edits into files *other* than the
/// declaring one, so file identity belongs to the **edit**, not to the
/// invocation. A per-file invocation would have to be unwound the moment S3
/// lands, and the unwinding would be silent — the code would still compile and
/// simply place S3's edits in the wrong file.
///
/// `reverted` names subjects the verify loop has already taken back: they are
/// skipped here rather than removed from the table, so the decision phase stays
/// the single authority on what was decided and the loop only decides what is
/// *emitted*.
///
/// # The non-placing arms, and what each one owes (S2b.2 audit)
///
/// Every path out of the loop that produces no edit is listed here, so *"which
/// arms are silent"* is answerable by reading this file rather than by
/// re-deriving it. A bare `continue` is legitimate only when some **other**
/// component already holds the attribution.
///
/// | arm | disposition |
/// |---|---|
/// | `reverted(subject)` | bare `continue` — the verify loop owns the count |
/// | decision is not `Ref` | bare `continue` — the table holds the `Degradation`, with subject, site and reason |
/// | `pointee_span` is `None` | **`Unplaceable`** — unreachable through the pipeline, so nothing else would hold it |
/// | `span_to_loc(ty_span)` errs | `Unplaceable`, reason from the locator |
/// | `span_to_loc(pointee_span)` errs | `Unplaceable`, reason from the locator |
/// | pointee file ≠ declaration file | `Unplaceable` |
/// | no source text for the file | `Unplaceable` |
/// | pointee range outside its file | `Unplaceable` |
///
/// **Counting — SETTLED AT S2b.3.** The reported `emitted` counts *placements*:
/// every `Unplaceable` recorded here is subtracted from the emitted-subject set
/// by its [`Unplaceable::subject`] identity, so a decision that produced no edit
/// is not reported as a rewrite. It was a count of *decisions* through S2b.2,
/// over-reporting by exactly the unplaceable set.
///
/// Exposure was zero across all 20 frozen programs both before and after, which
/// is why this was a derivation fix rather than a number change — and why it was
/// worth making: a counter that is right by measurement is one corpus change
/// away from being wrong, and the wrongness would present as a yield figure
/// rather than as a failure.
///
/// The count is now also **pinned**: `m1_emit_corpus` fails on a nonzero
/// `unplaceable`, fail-closed on a missing or unparseable value. The pin is
/// meaningful on FAIL rows only because `RewriteOutcome::Degraded` carries the
/// count as of S2b.3; before that it reported a constant.
///
/// **Where alias-typed subjects land today:** a parameter whose *resolved* type
/// is a pointer but whose declaration is a type alias is collected (R-A) with
/// `DeclShape::Alias`, and `decide_one` degrades it as
/// `UnsupportedDeclShape { shape: "alias" }` — a reason named for the declaration
/// shape, which is true but says nothing about what BO concluded for it. The
/// alias-specific relabel is **registered**, to ride whichever slice first makes
/// alias emission live (S3 at the earliest).
pub(crate) fn plan(
    table: &DecisionTable,
    source_of: impl Fn(&FileKey) -> Option<String>,
    span_to_loc: impl Fn(rustc_span::Span) -> Result<(FileKey, usize, usize), &'static str>,
    owner_of: impl Fn(&super::decision::Subject) -> String,
    reverted: &dyn Fn(&super::decision::Subject) -> bool,
) -> Plan {
    let mut by_file: BTreeMap<FileKey, Vec<Edit>> = BTreeMap::new();
    let mut unplaceable = Vec::new();
    let mut preclass_sites = Vec::new();
    let mut owner_arms = BTreeMap::<SignatureClassId, super::decision::RequiredArmSet>::new();
    for (subject, _) in &table.entries {
        let owner = SignatureClassId::of(subject.fn_did);
        let required = table
            .arm_requirements
            .get(&(subject.fn_did, subject.hir_id))
            .copied()
            .unwrap_or_default();
        owner_arms
            .entry(owner)
            .and_modify(|arms| *arms = arms.union(required))
            .or_insert(required);
    }

    // **S3.6-1 seam adapters, placed FIRST.**
    //
    // A seam edit lands in the CALLER's file and is justified by the CALLEE's
    // subject, which is the divergence `Edit::owner_fn`'s doc was written for —
    // and the reason the same-file guard further down does not apply to it. That
    // guard exists because a subject's pointee text is copied by byte offset, so
    // only a *use* edit may cross a file; a seam copies no pointee text, it
    // wraps an expression already present in the caller.
    //
    // Reverting the callee reverts its seams with it because every seam carries
    // the callee's direct signature-class ID. The path is receipt-only.
    for seam in &table.seams.edits {
        match span_to_loc(seam.span) {
            Ok((file, lo, hi)) => by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: seam.replacement.clone(),
                justification: Justification::SeamAdapter {
                    family: match seam.family {
                        super::decision::seam::SeamFamily::Safe => "safe",
                        super::decision::seam::SeamFamily::Reborrow => "reborrow",
                    },
                    fabricated: seam.spec.len.as_ref().is_some_and(|l| l.is_fabricated()),
                },
                owner_class: Some(seam.owner_class),
                owner_path: seam.owner_fn.clone(),
                bridge: Some(seam.bridge.clone()),
                atom_ids: seam.atom_ids.clone(),
                subject_id: format!("{}#arg{}", seam.owner_fn, seam.param_index),
                required_arms: owner_arms
                    .get(&seam.owner_class)
                    .copied()
                    .unwrap_or_default()
                    .render(),
                edit_kind: match seam.source_shape {
                    "pair-raw-view" => "pair-raw-view",
                    "address-observation" => "address-observation",
                    _ => "seam-adapter",
                },
            }),
            // A span that cannot be located is RECORDED, never dropped: a seam
            // that silently vanishes leaves the callee converted and the call
            // site raw, which is the `E0308` this whole slice exists to remove.
            Err(reason) => unplaceable.push(Unplaceable {
                owner_class: seam.owner_class,
                bridge: seam.bridge.clone(),
                reason,
                detail: format!("seam adapter for {}", seam.owner_fn),
                subject: seam.owner_fn.clone(),
            }),
        }
    }
    for body in &table.seams.body_edits {
        match span_to_loc(body.span) {
            Ok((file, lo, hi)) => by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: body.replacement.clone(),
                justification: Justification::SeamAdapter {
                    family: match body.family {
                        super::decision::seam::SeamFamily::Safe => "safe",
                        super::decision::seam::SeamFamily::Reborrow => "reborrow",
                    },
                    fabricated: false,
                },
                owner_class: Some(body.owner_class),
                owner_path: body.owner_fn.clone(),
                bridge: Some(body.bridge.clone()),
                atom_ids: Vec::new(),
                subject_id: body.destination.clone(),
                required_arms: owner_arms
                    .get(&body.owner_class)
                    .copied()
                    .unwrap_or_default()
                    .render(),
                edit_kind: "body-adapter",
            }),
            Err(reason) => unplaceable.push(Unplaceable {
                owner_class: body.owner_class,
                bridge: body.bridge.clone(),
                reason,
                detail: format!("body adapter for {}", body.destination),
                subject: body.owner_fn.clone(),
            }),
        }
    }

    for (subject, decision) in &table.entries {
        if reverted(subject) {
            continue;
        }
        let subject_atom_ids = table
            .seams
            .raw_boundary_atom_groups
            .get(&(subject.fn_did, subject.hir_id))
            .map(|atoms| atoms.iter().map(|atom| atom.id.clone()).collect::<Vec<_>>())
            .unwrap_or_default();
        // EXHAUSTIVE (S3.0, ruling 5). A `let …else` here compiled clean against
        // a third `Decision` variant and silently produced no edit AND no
        // `Unplaceable` record — measured with a variant probe before the
        // repair: the build named only `artifact::rows` and `degradations()`.
        // A `match` makes the next disposition a compile error at this site.
        let (mutable, use_edits_in, optional, fat, box_plan) = match decision {
            Decision::Ref { mutable } => (mutable, None, false, false, None),
            // The direct callee supplies this local's type. There is no local
            // declaration span to edit; the signature owner is planned by E2.
            Decision::InferredRef { .. } => continue,
            // S3.2′-2: the first disposition that is not declaration-only.
            Decision::Slice { mutable, uses } => (mutable, Some(uses), false, true, None),
            // S3.2′-3: an optional form, thin or fat. Its uses travel the same
            // channel — declaration and uses move together or not at all, which
            // `use_failure` below enforces for every form that has uses.
            Decision::Opt {
                mutable,
                slice,
                uses,
            } => (mutable, Some(uses), true, *slice, None),
            Decision::Box(plan) => (
                &false,
                None,
                plan.optional,
                matches!(plan.shape, super::decision::box_facts::BoxShape::Slice),
                Some(plan),
            ),
            // Degraded subjects produce no edit BY DESIGN — the decision phase
            // already recorded why, and re-deciding here would duplicate the
            // authority the architecture puts in one place.
            Decision::Degraded(_) => continue,
        };
        // Attribution names the universe, so a locals record does not read as a
        // parameter at position 0 — `detail` is what a human reads in an
        // `Unplaceable`, and "p (param #0)" for a local would be a false
        // statement, not merely a vague one. Identity still lives in
        // `Unplaceable::subject`; this is display.
        let attribution = || match subject.kind {
            super::decision::SubjectKind::Param { hir_index } => format!(
                "{} (param #{hir_index})",
                subject.param_name.as_deref().unwrap_or("<unnamed>")
            ),
            super::decision::SubjectKind::Local => format!(
                "{} (local {:?})",
                subject.param_name.as_deref().unwrap_or("<unnamed>"),
                subject.local
            ),
        };
        // The SAME recipe the driver builds its emitted-subject labels with.
        // Two spellings of one identity would make the subtraction silently
        // empty — the failure mode would be `emitted` staying decision-shaped
        // while looking placement-shaped.
        // S3.0′: ONE definition, in `decision`. This site used to build the key
        // by hand and the driver built the same string by hand beside it — a
        // duplicated canonicalizer whose two copies had to be edited together.
        let identity = || subject.identity_key(&owner_of(subject));
        let subject_id = identity();
        let surface_bridge = || {
            BridgeSitePlan::local(
                subject.fn_did,
                subject.fn_did,
                Arm::Surface.key(),
                subject_id.clone(),
                "surface-unplaceable",
            )
        };
        let subject_arms = table
            .arm_requirements
            .get(&(subject.fn_did, subject.hir_id))
            .copied()
            .unwrap_or_default()
            .render();
        // A bridge-admitted unannotated Box binding gets its complete type from
        // the rewritten initializer. It still needs a file anchor for its value
        // edits, but deliberately has no declaration splice. Every other form
        // retains the long-standing syntactic-pointee requirement.
        let inferred_box = box_plan.is_some_and(|plan| plan.inferred_binding);
        let (ty_file, declaration_edit) = if inferred_box {
            match span_to_loc(subject.binding_span) {
                Ok((file, _, _)) => (file, None),
                Err(reason) => {
                    unplaceable.push(Unplaceable {
                        owner_class: SignatureClassId::of(subject.fn_did),
                        bridge: surface_bridge(),
                        reason,
                        detail: attribution(),
                        subject: identity(),
                    });
                    continue;
                }
            }
        } else {
            let Some(pointee_span) = subject.pointee_span else {
                unplaceable.push(Unplaceable {
                    owner_class: SignatureClassId::of(subject.fn_did),
                    bridge: surface_bridge(),
                    reason: "Ref decision on a declaration with no pointee span",
                    detail: attribution(),
                    subject: identity(),
                });
                continue;
            };
            let Some(subject_ty_span) = subject.ty_span else {
                unplaceable.push(Unplaceable {
                    owner_class: SignatureClassId::of(subject.fn_did),
                    bridge: surface_bridge(),
                    reason: "subject has no declared type to splice",
                    detail: attribution(),
                    subject: identity(),
                });
                continue;
            };
            let (ty_file, ty_lo, ty_hi) = match span_to_loc(subject_ty_span) {
                Ok(located) => located,
                Err(reason) => {
                    unplaceable.push(Unplaceable {
                        owner_class: SignatureClassId::of(subject.fn_did),
                        bridge: surface_bridge(),
                        reason,
                        detail: attribution(),
                        subject: identity(),
                    });
                    continue;
                }
            };
            let (pointee_file, p_lo, p_hi) = match span_to_loc(pointee_span) {
                Ok(located) => located,
                Err(reason) => {
                    unplaceable.push(Unplaceable {
                        owner_class: SignatureClassId::of(subject.fn_did),
                        bridge: surface_bridge(),
                        reason,
                        detail: attribution(),
                        subject: identity(),
                    });
                    continue;
                }
            };
            if pointee_file != ty_file {
                unplaceable.push(Unplaceable {
                    owner_class: SignatureClassId::of(subject.fn_did),
                    bridge: surface_bridge(),
                    reason: "pointee text is in a different file from the declaration",
                    detail: attribution(),
                    subject: identity(),
                });
                continue;
            }
            let Some(source) = source_of(&ty_file) else {
                unplaceable.push(Unplaceable {
                    owner_class: SignatureClassId::of(subject.fn_did),
                    bridge: surface_bridge(),
                    reason: "no source text available for the declaring file",
                    detail: attribution(),
                    subject: identity(),
                });
                continue;
            };
            let Some(source_pointee) = source.get(p_lo..p_hi) else {
                unplaceable.push(Unplaceable {
                    owner_class: SignatureClassId::of(subject.fn_did),
                    bridge: surface_bridge(),
                    reason: "pointee range is outside its own file's source",
                    detail: attribution(),
                    subject: identity(),
                });
                continue;
            };
            let pointee = box_plan
                .and_then(|plan| plan.pointee_override)
                .map(super::decision::box_facts::BoxPointeeOverride::source_name)
                .unwrap_or(source_pointee);
            let base = if box_plan.is_some() {
                if fat {
                    format!("Box<[{pointee}]>")
                } else {
                    format!("Box<{pointee}>")
                }
            } else {
                match (fat, *mutable) {
                    (false, true) => format!("&mut {pointee}"),
                    (false, false) => format!("&{pointee}"),
                    (true, true) => format!("&mut [{pointee}]"),
                    (true, false) => format!("&[{pointee}]"),
                }
            };
            let replacement = if optional {
                format!("Option<{base}>")
            } else {
                base
            };
            (ty_file, Some((ty_lo, ty_hi, replacement)))
        };
        // The USE-SITE edits, placed before the declaration edit is pushed so a
        // use that cannot be located takes the whole subject with it. A subject
        // whose declaration is spliced while one use is left raw is an
        // ill-typed crate, not a partial rewrite.
        let mut use_edits = Vec::new();
        let mut use_failure = None;
        if let Some(box_plan) = box_plan {
            for edit in &box_plan.expr_edits {
                match span_to_loc(edit.span) {
                    Ok((file, lo, hi)) if file == ty_file => use_edits.push(Edit {
                        lo,
                        hi,
                        replacement: edit.replacement.clone(),
                        justification: if box_plan.fabricated_extent
                            && matches!(
                                edit.receipt,
                                "memset-zero-slice"
                                    | "realloc-atomic"
                                    | "default-fill-slice-fallback"
                            ) {
                            Justification::SeamAdapter {
                                family: "box",
                                fabricated: true,
                            }
                        } else if edit.receipt == "c-free-site-drop" {
                            Justification::DropForm {
                                selector_site: edit.receipt.to_owned(),
                            }
                        } else {
                            Justification::KindDecision { kind: "Box(expr)" }
                        },
                        owner_class: Some(SignatureClassId::of(subject.fn_did)),
                        owner_path: owner_of(subject),
                        bridge: Some(
                            BridgeSitePlan::local(
                                subject.fn_did,
                                subject.fn_did,
                                Arm::Surface.key(),
                                subject_id.clone(),
                                "box-expression",
                            )
                            .with_extent(
                                if box_plan.fabricated_extent
                                    && matches!(
                                        edit.receipt,
                                        "memset-zero-slice"
                                            | "realloc-atomic"
                                            | "default-fill-slice-fallback"
                                    )
                                {
                                    BridgeExtentKind::Fallback
                                } else {
                                    BridgeExtentKind::None
                                },
                            ),
                        ),
                        atom_ids: subject_atom_ids.clone(),
                        subject_id: subject_id.clone(),
                        required_arms: subject_arms.clone(),
                        edit_kind: "box-expression",
                    }),
                    Ok(_) => {
                        use_failure = Some("Box edit is in a different file from the declaration")
                    }
                    Err(reason) => use_failure = Some(reason),
                }
            }
            for &span in &box_plan.delete_statements {
                match span_to_loc(span) {
                    Ok((file, lo, hi)) if file == ty_file => use_edits.push(Edit {
                        lo,
                        hi,
                        replacement: String::new(),
                        justification: Justification::StoreForm {
                            form: "box-delete-initializer-store",
                        },
                        owner_class: Some(SignatureClassId::of(subject.fn_did)),
                        owner_path: owner_of(subject),
                        bridge: Some(BridgeSitePlan::local(
                            subject.fn_did,
                            subject.fn_did,
                            Arm::Surface.key(),
                            subject_id.clone(),
                            "box-delete-store",
                        )),
                        atom_ids: subject_atom_ids.clone(),
                        subject_id: subject_id.clone(),
                        required_arms: subject_arms.clone(),
                        edit_kind: "box-delete-store",
                    }),
                    Ok(_) => {
                        use_failure = Some(
                            "Box deleted statement is in a different file from the declaration",
                        )
                    }
                    Err(reason) => use_failure = Some(reason),
                }
            }
        }
        for use_edit in use_edits_in.into_iter().flatten() {
            match span_to_loc(use_edit.span) {
                Ok((file, lo, hi)) if file == ty_file => use_edits.push(Edit {
                    lo,
                    hi,
                    replacement: use_edit.replacement.clone(),
                    justification: Justification::KindDecision {
                        kind: if optional { "Opt(use)" } else { "Slice(use)" },
                    },
                    owner_class: Some(SignatureClassId::of(subject.fn_did)),
                    owner_path: owner_of(subject),
                    bridge: Some(BridgeSitePlan::local(
                        subject.fn_did,
                        subject.fn_did,
                        Arm::Surface.key(),
                        subject_id.clone(),
                        "subject-use",
                    )),
                    atom_ids: subject_atom_ids.clone(),
                    subject_id: subject_id.clone(),
                    required_arms: subject_arms.clone(),
                    edit_kind: "subject-use",
                }),
                Ok(_) => {
                    use_failure = Some("slice use is in a different file from the declaration")
                }
                Err(reason) => use_failure = Some(reason),
            }
        }
        if let Some(reason) = use_failure {
            unplaceable.push(Unplaceable {
                owner_class: SignatureClassId::of(subject.fn_did),
                bridge: surface_bridge(),
                reason,
                detail: attribution(),
                subject: identity(),
            });
            continue;
        }
        let kind = if box_plan.is_some() {
            match (optional, fat) {
                (false, false) => "Box",
                (false, true) => "BoxSlice",
                (true, false) => "OptBox",
                (true, true) => "OptBoxSlice",
            }
        } else {
            match (optional, fat, *mutable) {
                (false, false, true) => "Ref(mut)",
                (false, false, false) => "Ref(shared)",
                (false, true, true) => "Slice(mut)",
                (false, true, false) => "Slice(shared)",
                (true, false, true) => "OptRef(mut)",
                (true, false, false) => "OptRef(shared)",
                (true, true, true) => "OptSlice(mut)",
                (true, true, false) => "OptSlice(shared)",
            }
        };
        by_file
            .entry(ty_file.clone())
            .or_default()
            .extend(use_edits);
        if let Some((ty_lo, ty_hi, replacement)) = declaration_edit {
            by_file.entry(ty_file).or_default().push(Edit {
                lo: ty_lo,
                hi: ty_hi,
                replacement,
                justification: Justification::KindDecision { kind },
                owner_class: Some(SignatureClassId::of(subject.fn_did)),
                owner_path: owner_of(subject),
                bridge: Some(BridgeSitePlan::local(
                    subject.fn_did,
                    subject.fn_did,
                    Arm::Surface.key(),
                    subject_id.clone(),
                    "subject-declaration",
                )),
                atom_ids: subject_atom_ids,
                subject_id,
                required_arms: subject_arms,
                edit_kind: "subject-declaration",
            });
        }
    }
    preclass_sites.extend(unplaceable.iter().map(|site| {
        ClassSite {
            key: site
                .bridge
                .materialize(site.owner_class, "<unplaceable>".to_owned(), 0, 0),
            edit_key: "-".to_owned(),
            state: ClassSiteState::Dropped(site.reason.to_owned()),
            extent: site.bridge.extent.clone(),
            retention: site.bridge.retention,
            waiver_id: site.bridge.waiver_id.clone(),
        }
    }));
    for proof in &table.seams.overlap_proofs {
        use crate::bo_rewriter::decision::a5_site_proof::A5SiteProofVerdict;
        let owner = SignatureClassId::of(proof.callee);
        let site = match proof.verdict {
            A5SiteProofVerdict::Clear => ClassSite::zero(
                owner,
                SignatureClassId::of(proof.caller),
                Arm::Pair,
                "a5-site-proof-clear",
            ),
            A5SiteProofVerdict::Overlapping | A5SiteProofVerdict::Undeterminable => {
                ClassSite::dropped(
                    owner,
                    SignatureClassId::of(proof.caller),
                    Arm::Pair,
                    "a5-site-proof-blocked",
                    proof.reason.clone(),
                )
            }
        };
        preclass_sites.push(site);
    }
    for blocked in &table.seams.blocked {
        let arm = if blocked.block == super::decision::seam::SeamBlock::SiteOverlap {
            Arm::Pair
        } else {
            match (blocked.expected, blocked.found) {
                (Some(expected), Some(found))
                    if expected != super::decision::seam::Form::Raw
                        && found != super::decision::seam::Form::Raw =>
                {
                    Arm::Glue
                }
                _ => Arm::C,
            }
        };
        let bridge = BridgeSitePlan::local(
            blocked.caller,
            blocked.callee,
            arm.key(),
            format!("arg{}", blocked.index),
            blocked.block.key(),
        );
        let (file, lo, hi) = span_to_loc(blocked.span)
            .map(|(file, lo, hi)| {
                (
                    file_key_label(&file),
                    u32::try_from(lo).unwrap_or(u32::MAX),
                    u32::try_from(hi).unwrap_or(u32::MAX),
                )
            })
            .unwrap_or_else(|_| ("<unplaceable>".to_owned(), 0, 0));
        preclass_sites.push(ClassSite {
            key: bridge.materialize(SignatureClassId::of(blocked.callee), file, lo, hi),
            edit_key: "-".to_owned(),
            state: ClassSiteState::Dropped(blocked.block.key().to_owned()),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        });
    }
    for blocked in &table.seams.body_blocked {
        let bridge = BridgeSitePlan::local(
            blocked.owner_class.local_def_id(),
            blocked.owner_class.local_def_id(),
            Arm::Glue.key(),
            format!("body:{}", blocked.context.key()),
            blocked.block.key(),
        );
        let (file, lo, hi) = span_to_loc(blocked.span)
            .map(|(file, lo, hi)| {
                (
                    file_key_label(&file),
                    u32::try_from(lo).unwrap_or(u32::MAX),
                    u32::try_from(hi).unwrap_or(u32::MAX),
                )
            })
            .unwrap_or_else(|_| ("<unplaceable>".to_owned(), 0, 0));
        preclass_sites.push(ClassSite {
            key: bridge.materialize(blocked.owner_class, file, lo, hi),
            edit_key: "-".to_owned(),
            state: ClassSiteState::Dropped(blocked.block.key().to_owned()),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        });
    }
    for pair in &table.seams.pair_sites {
        use super::decision::co_conversion::{PairRole, PairTier};
        if pair.role == PairRole::RawView {
            continue;
        }
        let owner = SignatureClassId::of(pair.callee);
        let mut site = match pair.role {
            PairRole::Clear | PairRole::Primary => ClassSite::zero(
                owner,
                SignatureClassId::of(pair.caller),
                Arm::Pair,
                pair.role.key(),
            ),
            PairRole::Blocked => ClassSite::dropped(
                owner,
                SignatureClassId::of(pair.caller),
                Arm::Pair,
                pair.role.key(),
                pair.reason.clone(),
            ),
            PairRole::RawView => unreachable!(),
        };
        site.retention = match pair.tier {
            PairTier::T1 => BridgeRetentionTier::T1,
            PairTier::T2 => BridgeRetentionTier::T2,
            PairTier::None | PairTier::Blocked => BridgeRetentionTier::None,
        };
        site.waiver_id = (pair.tier == PairTier::T2)
            .then(|| super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned());
        preclass_sites.push(site);
    }

    Plan {
        by_file,
        unplaceable,
        // Both filled by the caller; `plan` has no `TyCtxt`, so it can ask
        // neither which file is the crate root nor the parser for an item.
        root_file: None,
        len_const_item: None,
        preclass_sites,
        class_finalization: ClassFinalization::default(),
    }
}

#[cfg(test)]
mod tests {
    use rustc_middle::mir::Local;

    use super::*;
    use crate::bo_rewriter::decision::{DeclShape, Subject};

    /// A subject the collector really does build: an alias-typed declaration
    /// whose RESOLVED type is a pointer. It carries `pointee_span: None`,
    /// because an alias hides the `*mut` and there is no pointee text to copy.
    fn alias_subject() -> Subject {
        Subject {
            fn_did: rustc_hir::def_id::CRATE_DEF_ID,
            local: Local::from_u32(1),
            hir_id: rustc_hir::CRATE_HIR_ID,
            param_name: Some("p".to_owned()),
            kind: crate::bo_rewriter::decision::SubjectKind::Param { hir_index: 0 },
            ptr_depth: 1,
            label: "f::p".to_owned(),
            ty_span: Some(rustc_span::DUMMY_SP),
            binding_span: rustc_span::DUMMY_SP,
            pointee_span: None,
            decl_shape: DeclShape::Alias,
            mutable: false,
            freed_at: None,
            len_recovered: false,
            null_init: false,
            mut_binding: false,
            ctor: None,
        }
    }

    /// **The arm-3 witness.** A `Ref` decision on a declaration with no pointee
    /// span is recorded as `Unplaceable`, not skipped.
    ///
    /// # Why the injection is data-level
    ///
    /// `decide_one` degrades every non-`RawPtr` declaration shape, so no input
    /// program can reach this arm — it is a backstop, and a backstop that
    /// cannot be exercised is indistinguishable from one that is not there.
    /// The reachability Rider 5 asks for is supplied HERE, by handing `plan` a
    /// table it could not have produced itself: `plan` is a pure function over
    /// its input, so the constructed table is the whole seam. **No `cfg` or env
    /// hook exists in shipping code for this** — phase separation is what makes
    /// the cheap route also the clean one.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* delete the
    /// `unplaceable.push(..)` in that arm and this fails on the length.
    #[test]
    fn a_ref_decision_with_no_pointee_span_is_attributed_not_skipped() {
        let table = DecisionTable {
            arm_requirements: Default::default(),
            exposure: None,
            seams: Default::default(),
            c9_marks: Vec::new(),
            lifetime_plan: Default::default(),
            entries: vec![(alias_subject(), Decision::Ref { mutable: false })],
        };

        let planned = plan(
            &table,
            |_| Some("fn f(p: PtrAlias) {}".to_owned()),
            // Doubles as an ORDERING assertion: the arm must short-circuit
            // before anything tries to locate a span, because the span it would
            // locate is the one that does not exist.
            |_: rustc_span::Span| -> Result<(FileKey, usize, usize), &'static str> {
                panic!("the missing-pointee arm must fire before any span is located")
            },
            |_| "f".to_owned(),
            &|_| false,
        );

        assert!(
            planned.by_file.is_empty(),
            "no edit can be placed without a pointee span, yet one was: {:?}",
            planned.by_file
        );
        assert_eq!(
            planned.unplaceable.len(),
            1,
            "the subject vanished with no attribution — this is the silent \
             `continue` the arm was replaced to prevent: {:?}",
            planned.unplaceable
        );
        assert_eq!(
            planned.unplaceable[0].reason,
            "Ref decision on a declaration with no pointee span"
        );
        assert!(
            planned.unplaceable[0].detail.contains("p (param #0)"),
            "the record must name WHICH subject, in the artifact's own terms: {:?}",
            planned.unplaceable[0].detail
        );
    }

    /// The same table with the same subject **decided as degraded** places
    /// nothing and records nothing — the decision table already holds that
    /// attribution, so a second record here would double-count it.
    ///
    /// Without this, the arm above could be "satisfied" by an implementation
    /// that reports every non-emitting subject as unplaceable, which would make
    /// the corpus's measured zero meaningless.
    #[test]
    fn a_degraded_subject_is_not_also_reported_unplaceable() {
        let table = DecisionTable {
            arm_requirements: Default::default(),
            exposure: None,
            seams: Default::default(),
            c9_marks: Vec::new(),
            lifetime_plan: Default::default(),
            entries: vec![(
                alias_subject(),
                Decision::Degraded(crate::bo_rewriter::decision::Degradation {
                    subject: "f::p".to_owned(),
                    site: "f.rs:1".to_owned(),
                    reason: crate::bo_rewriter::decision::DegradeReason::UnsupportedDeclShape {
                        shape: "alias",
                    },
                }),
            )],
        };

        let planned = plan(
            &table,
            |_| Some("fn f(p: PtrAlias) {}".to_owned()),
            |_: rustc_span::Span| -> Result<(FileKey, usize, usize), &'static str> {
                panic!("a degraded subject must not reach span location")
            },
            |_| "f".to_owned(),
            &|_| false,
        );

        assert!(planned.by_file.is_empty(), "{:?}", planned.by_file);
        assert!(
            planned.unplaceable.is_empty(),
            "a degradation the TABLE already attributes was recorded a second \
             time here: {:?}",
            planned.unplaceable
        );
    }
}

#[cfg(test)]
mod wave3_class_tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::bo_rewriter::{bridge_receipt::SignatureClassId, decision::RequiredArmSet};

    fn with_classes(count: usize, check: impl FnOnce(&[SignatureClassId]) + Send) {
        let source = (0..count)
            .map(|index| format!("fn class_{index}() {{}}"))
            .collect::<Vec<_>>()
            .join("\n");
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let mut ids = tcx
                .hir_body_owners()
                .map(SignatureClassId::of)
                .collect::<Vec<_>>();
            ids.sort();
            assert_eq!(ids.len(), count);
            check(&ids);
        })
        .expect("class fixture compiles");
    }

    fn arms(required: &[crate::bo_rewriter::decision::Arm]) -> RequiredArmSet {
        let mut out = RequiredArmSet::default();
        for &arm in required {
            out.insert(arm);
        }
        out
    }

    #[test]
    fn cls_w1_one_signature_and_all_adapters_revert_as_one_unit() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(3, |ids| {
            let owner = ids[0];
            let input = ClassInput::new(owner, arms(&[Arm::Surface, Arm::C, Arm::Glue]))
                .with_site(ClassSite::edit(
                    owner,
                    ids[1],
                    Arm::Surface,
                    "m.rs",
                    1,
                    2,
                    "signature",
                ))
                .with_site(ClassSite::edit(
                    owner,
                    ids[1],
                    Arm::C,
                    "m.rs",
                    10,
                    11,
                    "caller-a",
                ))
                .with_site(ClassSite::edit(
                    owner,
                    ids[2],
                    Arm::Glue,
                    "m.rs",
                    20,
                    21,
                    "caller-b",
                ));
            let finalized = finalize_class_inputs(vec![input]);
            assert!(finalized.classes[&owner].is_ready());
            assert_eq!(finalized.classes[&owner].sites.len(), 3);
            assert_eq!(finalized.live_sites(&BTreeSet::from([owner])).count(), 0);
        });
    }

    #[test]
    fn atm_w1_surface_with_missing_required_c_holds_the_whole_class() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(1, |ids| {
            let owner = ids[0];
            let input = ClassInput::new(owner, arms(&[Arm::Surface, Arm::C])).with_site(
                ClassSite::edit(owner, owner, Arm::Surface, "m.rs", 1, 2, "signature"),
            );
            let finalized = finalize_class_inputs(vec![input]);
            assert!(!finalized.classes[&owner].is_ready());
            assert_eq!(finalized.applied_site_count(), 0);
        });
    }

    #[test]
    fn atm_w2_blocked_class_applies_no_ready_d4_or_pair_site() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(1, |ids| {
            let owner = ids[0];
            let input = ClassInput::new(owner, arms(&[Arm::D4, Arm::Pair]))
                .blocked("blocked-subject")
                .with_site(ClassSite::zero(owner, owner, Arm::D4, "d4-membership"))
                .with_site(ClassSite::edit(
                    owner,
                    owner,
                    Arm::Pair,
                    "m.rs",
                    4,
                    5,
                    "pair-view",
                ));
            let finalized = finalize_class_inputs(vec![input]);
            assert!(!finalized.classes[&owner].is_ready());
            assert_eq!(finalized.applied_site_count(), 0);
        });
    }

    #[test]
    fn atm_w3_zero_syntax_site_is_terminally_applied() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(1, |ids| {
            let owner = ids[0];
            let input = ClassInput::new(owner, arms(&[Arm::C])).with_site(ClassSite::zero(
                owner,
                owner,
                Arm::C,
                "identity-coercion",
            ));
            let finalized = finalize_class_inputs(vec![input]);
            assert!(finalized.classes[&owner].is_ready());
            assert_eq!(finalized.applied_site_count(), 1);
            assert_eq!(finalized.classes[&owner].sites[0].edit_key, "-");
            let plan = Plan {
                class_finalization: finalized,
                ..Plan::default()
            };
            let events = plan.bridge_events(&BTreeSet::new());
            let summary = crate::bo_rewriter::bridge_receipt::reconcile_bridge_events(&events)
                .expect("zero-syntax plan/terminal receipt reconciles");
            assert_eq!(summary.required_sites, 1);
            assert_eq!(summary.applied_events, 1);
            assert_eq!(summary.dropped_events, 0);
        });
    }

    #[test]
    fn coll_w1_cross_class_interval_collision_holds_both_classes() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(2, |ids| {
            let left = ClassInput::new(ids[0], arms(&[Arm::Surface])).with_site(ClassSite::edit(
                ids[0],
                ids[0],
                Arm::Surface,
                "m.rs",
                10,
                20,
                "left",
            ));
            let right = ClassInput::new(ids[1], arms(&[Arm::Surface])).with_site(ClassSite::edit(
                ids[1],
                ids[1],
                Arm::Surface,
                "m.rs",
                15,
                25,
                "right",
            ));
            let finalized = finalize_class_inputs(vec![left, right]);
            assert_eq!(finalized.collisions.len(), 1);
            assert!(!finalized.classes[&ids[0]].is_ready());
            assert!(!finalized.classes[&ids[1]].is_ready());
            assert_eq!(finalized.applied_site_count(), 0);
        });
    }
}
