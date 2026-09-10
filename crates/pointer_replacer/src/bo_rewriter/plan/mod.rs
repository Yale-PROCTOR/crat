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

pub(crate) mod callee_parameter_input;
pub(crate) mod native_return;
pub(crate) mod outbound_expression;
pub(crate) mod outbound_return;
pub(crate) mod receiver_input;
pub(crate) mod sibling_overlap;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};

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

pub(crate) fn file_key_label(key: &FileKey) -> String {
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
    /// A5 proof-site T2 raw temporary consumed by a raw callee position.
    A5RawView,
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
    /// Logical atom dependencies survive even when this site has no text edit.
    pub atom_ids: Vec<String>,
    pub key: BridgeSiteKey,
    pub edit_key: String,
    pub state: ClassSiteState,
    pub expected_form: String,
    pub found_form: String,
    pub argument_kind: String,
    pub extent: BridgeExtentKind,
    pub retention: BridgeRetentionTier,
    pub waiver_id: Option<String>,
    pub unsafe_context: Option<super::mechanical_receipt::UnsafeContextPresentation>,
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
            atom_ids: Vec::new(),
            edit_key: format!(
                "class={}|arm={}|interval={file}:{lo}:{hi}|kind={kind}",
                owner.order_key(),
                arm.key()
            ),
            key,
            state: ClassSiteState::EditReady,
            expected_form: "-".to_owned(),
            found_form: "-".to_owned(),
            argument_kind: "-".to_owned(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: None,
        }
    }

    pub(crate) fn zero(
        owner: SignatureClassId,
        caller: SignatureClassId,
        arm: Arm,
        kind: &str,
    ) -> Self {
        Self {
            atom_ids: Vec::new(),
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
            expected_form: "-".to_owned(),
            found_form: "-".to_owned(),
            argument_kind: "-".to_owned(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: None,
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ClassAttributionInterval {
    pub owner_class: SignatureClassId,
    pub owner_path: String,
    pub file: FileKey,
    pub lo: usize,
    pub hi: usize,
    pub kind: &'static str,
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
    // A logical position receipt can be attached to its enclosing physical
    // call edit. The exact physical identity is produced only after that edit
    // materializes; two such receipts do not introduce two splices.
    if left.key.owner_class == right.key.owner_class
        && left.key.caller == right.key.caller
        && left.edit_key != "-"
        && !left.edit_key.is_empty()
        && left.edit_key == right.edit_key
        && ((left.key.lo <= right.key.lo && right.key.hi <= left.key.hi)
            || (right.key.lo <= left.key.lo && left.key.hi <= right.key.hi))
    {
        return false;
    }
    if left.key.lo == left.key.hi && right.key.lo == right.key.hi {
        return left.key.lo == right.key.lo;
    }
    left.key.lo < right.key.hi && right.key.lo < left.key.hi
}

/// The AST pipeline rewrites a subject use before it wraps the containing call
/// argument.  This one strict nesting is therefore composition, not a byte
/// collision.  Return `(outer, inner)` so cross-class nesting also records the
/// readiness dependency needed to keep the composition atomic.
fn nested_ast_composition(
    left: &ClassSite,
    right: &ClassSite,
) -> Option<(SignatureClassId, SignatureClassId)> {
    let strictly_contains = |outer: &ClassSite, inner: &ClassSite| {
        outer.key.file == inner.key.file
            && outer.key.lo <= inner.key.lo
            && inner.key.hi <= outer.key.hi
            && (outer.key.lo < inner.key.lo || inner.key.hi < outer.key.hi)
    };
    let contains = |outer: &ClassSite, inner: &ClassSite| {
        outer.key.file == inner.key.file
            && outer.key.lo <= inner.key.lo
            && inner.key.hi <= outer.key.hi
    };
    let composable = |outer: &ClassSite, inner: &ClassSite| {
        let bridge_over_subject = matches!(outer.key.arm.as_str(), "c" | "glue")
            && inner.key.bridge_kind == "subject-use";
        let pair_over_c = outer.key.owner_class == inner.key.owner_class
            && outer.key.arm == "pair"
            && outer.key.bridge_kind == "pair-t2-raw-view"
            && inner.key.arm == "c";
        let a5_over_inner = outer.key.owner_class == inner.key.owner_class
            && outer.key.arm == "pair"
            && outer.key.bridge_kind == "a5-site-proof-t2-fallback"
            && matches!(inner.key.arm.as_str(), "c" | "glue");
        let slice_construction_over_inner = outer.key.bridge_kind == "slice-local-construction"
            && inner.key.bridge_kind != "slice-local-construction"
            && contains(outer, inner);
        let option_value_over_inner = outer.key.bridge_kind == "option-value-composed"
            && inner.key.bridge_kind != "option-value-composed"
            && contains(outer, inner);
        // L07 (§39 addendum 272, R272-3). The five outer/inner kind pairs the
        // J'' frame measures as STRICT CONTAINMENTS, entering under exactly
        // the dependency discipline `bridge_over_subject` already uses: the
        // outer `depends_on` the inner, so reverting the inner reverts the
        // outer, and no new custody contract is introduced.
        //
        // Each closed collision unholds TWO classes, because a declined
        // containment makes both carry `cross-class-interval-collision`.
        //
        // The pairs are named exactly, never by a family predicate: an
        // unlisted outer/inner combination still collides, which is what
        // keeps this an allowlist rather than a loosened arm.
        let l07_containment = outer.key.caller == inner.key.caller
            && matches!(
                (
                    outer.key.bridge_kind.as_str(),
                    inner.key.bridge_kind.as_str()
                ),
                ("pair-t2-raw-view", "typed-raw-temporary")
                    | ("pair-copy-snapshot", "typed-raw-temporary")
                    | ("pair-t2-raw-view", "raw-cast-const")
                    | ("c-raw-reborrow-shared", "raw-cast-const")
                    | ("pair-t2-raw-view", "subject-use")
            );
        let raw_receiver_over_argument = matches!(
            outer.key.bridge_kind.as_str(),
            "return-caller-receive-raw"
                | "return-shared-option"
                | "outbound-native-return-argument"
        ) && outer.key.owner_class == inner.key.owner_class
            && outer.key.caller == inner.key.caller
            && matches!(inner.key.arm.as_str(), "c" | "glue")
            && strictly_contains(outer, inner);
        ((bridge_over_subject || pair_over_c || a5_over_inner || l07_containment)
            && strictly_contains(outer, inner))
            || slice_construction_over_inner
            || option_value_over_inner
            || raw_receiver_over_argument
    };
    if composable(left, right) {
        Some((left.key.owner_class, right.key.owner_class))
    } else if composable(right, left) {
        Some((right.key.owner_class, left.key.owner_class))
    } else {
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct A5ProofResolution {
    kind: &'static str,
    state: ClassSiteState,
    retention: BridgeRetentionTier,
    waiver_id: Option<String>,
}

fn a5_proof_resolution(fallback: &super::decision::seam::A5ProofSiteFallback) -> A5ProofResolution {
    use super::decision::seam::A5ProofSiteFallback;
    match fallback {
        A5ProofSiteFallback::Clear => A5ProofResolution {
            kind: "a5-site-proof-clear",
            state: ClassSiteState::ZeroSyntaxReady,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        },
        A5ProofSiteFallback::T2RawView { .. } => A5ProofResolution {
            kind: "a5-site-proof-t2-fallback",
            state: ClassSiteState::Dropped(
                "a5-fallback-unrenderable:carrier-not-materialized".into(),
            ),
            retention: BridgeRetentionTier::T2,
            waiver_id: Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned()),
        },
        A5ProofSiteFallback::Primary => A5ProofResolution {
            kind: "a5-site-proof-pair-primary",
            state: ClassSiteState::ZeroSyntaxReady,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        },
        A5ProofSiteFallback::Held { reason } => A5ProofResolution {
            kind: "a5-site-proof-reclassified",
            state: ClassSiteState::Dropped(reason.clone()),
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        },
    }
}

pub(crate) fn physical_edit_key(file: &FileKey, edit: &Edit) -> Option<String> {
    use sha2::{Digest, Sha256};
    let owner = edit.owner_class?;
    let bridge = edit.bridge.as_ref()?;
    Some(format!(
        "class={}|arm={}|interval={}:{}:{}|kind={}|replacement_sha256={:x}",
        owner.order_key(),
        bridge.arm,
        file_key_label(file),
        edit.lo,
        edit.hi,
        bridge.bridge_kind,
        Sha256::digest(edit.replacement.as_bytes())
    ))
}

/// Logical A5 position receipts borrow the identity of their one already
/// materialized whole-call edit. They never create another argument edit.
pub(crate) fn link_a5_fallback_carriers(
    plan: &mut Plan,
    table: &DecisionTable,
    locate: impl Fn(rustc_span::Span) -> Result<(FileKey, usize, usize), &'static str>,
) {
    use super::decision::{
        SubjectKind,
        seam::{A5ProofSiteFallback, Form},
    };
    for proof in &table.seams.overlap_proofs {
        if !matches!(proof.fallback, A5ProofSiteFallback::T2RawView { .. }) {
            continue;
        }
        let raw = table.entries.iter().find(|(subject, _)| subject.fn_did == proof.callee
            && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == proof.index))
            .is_some_and(|(_, decision)| super::decision::seam::form_of(decision) == Form::Raw);
        let mut calls = Vec::new();
        if raw {
            for call in &table.seams.a5_raw_calls {
                if call.caller == proof.caller
                    && call.callee == proof.callee
                    && call.views.iter().any(|view| {
                        Some(view.proof_site_key) == proof.proof_site_key
                            && view.argument_index == proof.index
                            && view.expected_form == Form::Raw
                            && view.adapted_expression == super::c9::A5_RAW_VALUE_PLACEHOLDER
                    })
                {
                    if let Ok((file, lo, hi)) = locate(call.call_span) {
                        calls.push((file, lo, hi, "a5-proof-site-raw-view"));
                    }
                }
            }
            for call in &table.seams.pair_raw_calls {
                if call.caller == proof.caller
                    && call.callee == proof.callee
                    && call
                        .call_span
                        .source_callsite()
                        .contains(proof.span.source_callsite())
                    && call
                        .views
                        .iter()
                        .any(|view| view.argument_index == proof.index)
                {
                    if let Ok((file, lo, hi)) = locate(call.call_span) {
                        calls.push((file, lo, hi, "pair-raw-view"));
                    }
                }
            }
        }
        let Ok((proof_file, proof_lo, proof_hi)) = locate(proof.span) else { continue };
        let sites = plan
            .preclass_sites
            .iter()
            .enumerate()
            .filter(|(_, site)| {
                site.key.bridge_kind == "a5-site-proof-t2-fallback"
                    && site.key.caller == proof.caller
                    && site.key.owner_class == SignatureClassId::of(proof.callee)
                    && site.key.position == format!("arg{}", proof.index)
                    && site.key.file == file_key_label(&proof_file)
                    && site.key.lo as usize == proof_lo
                    && site.key.hi as usize == proof_hi
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        for index in sites {
            let site = &plan.preclass_sites[index];
            let calls_ref = &calls;
            let candidates = plan
                .by_file
                .iter()
                .flat_map(|(file, edits)| {
                    edits.iter().filter_map(move |edit| {
                        let b = edit.bridge.as_ref()?;
                        (edit.owner_class == Some(site.key.owner_class)
                            && b.caller == proof.caller
                            && file_key_label(file) == site.key.file
                            && edit.lo <= site.key.lo as usize
                            && site.key.hi as usize <= edit.hi
                            && calls_ref.iter().any(|(f, lo, hi, kind)| {
                                f == file
                                    && edit.lo == *lo
                                    && edit.hi == *hi
                                    && edit.edit_kind == *kind
                            }))
                        .then(|| physical_edit_key(file, edit))
                        .flatten()
                    })
                })
                .collect::<Vec<_>>();
            let site = &mut plan.preclass_sites[index];
            site.expected_form = Form::Raw.key().into();
            if calls.len() == 1 && candidates.len() == 1 {
                site.state = ClassSiteState::EditReady;
                site.edit_key = candidates[0].clone();
            } else {
                site.state = ClassSiteState::Dropped(format!(
                    "a5-fallback-unrenderable:raw={raw};carriers={};edits={}",
                    calls.len(),
                    candidates.len()
                ));
            }
        }
    }
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
    let mut intra_class_collisions = std::collections::BTreeSet::new();
    let mut composed_dependencies = std::collections::BTreeSet::new();
    for (left_index, left) in all_sites.iter().enumerate() {
        for right in &all_sites[left_index + 1..] {
            if !intervals_overlap(left, right) {
                continue;
            }
            if let Some((outer, inner)) = nested_ast_composition(left, right) {
                if outer != inner {
                    composed_dependencies.insert((outer, inner));
                }
                continue;
            }
            if left.key.owner_class == right.key.owner_class {
                // Exact duplicate sites are normalized below. Any other pair
                // would ask the flat splicer to apply two independently
                // rendered edits to one source interval. Hold the atomic class
                // unless a future producer explicitly composes them.
                if left.key != right.key || left.edit_key != right.edit_key {
                    intra_class_collisions.insert(left.key.owner_class);
                }
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

    for (outer, inner) in composed_dependencies {
        merged
            .get_mut(&outer)
            .expect("composed outer class came from merged inputs")
            .depends_on
            .push(inner);
    }

    for class in intra_class_collisions {
        merged
            .get_mut(&class)
            .expect("intra-class collision came from merged inputs")
            .block_reasons
            .push("intra-class-interval-overlap".to_owned());
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

    let mut classes = merged
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
        .collect::<BTreeMap<_, _>>();

    // Readiness follows dependency edges, not only recovery order. In
    // particular, a surfaced caller that names a generated safe inner cannot
    // remain Ready after the defining callee class is held.
    loop {
        let newly_held = classes
            .iter()
            .filter(|(_, class)| class.is_ready())
            .filter_map(|(&id, class)| {
                class
                    .depends_on
                    .iter()
                    .copied()
                    .find(|dependency| {
                        classes
                            .get(dependency)
                            .is_some_and(|dependency| !dependency.is_ready())
                    })
                    .map(|dependency| (id, dependency))
            })
            .collect::<Vec<_>>();
        if newly_held.is_empty() {
            break;
        }
        for (id, dependency) in newly_held {
            classes
                .get_mut(&id)
                .expect("dependent class came from finalized inputs")
                .disposition = SignatureClassDisposition::Held(vec![format!(
                "dependency-class-held:{}",
                dependency.order_key()
            )]);
        }
    }
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
/// An Option receipt can hold a class only while an actual changed Option
/// subject requires its operation. A candidate for an already-raw slot is
/// additive evidence, not a new consistency requirement for its neighbors.
fn option_receipt_requires_changed_form(
    table: &DecisionTable,
    receipt: &super::mechanical_receipt::OptionPresentationReceiptPlan,
) -> bool {
    table
        .entries
        .iter()
        .find(|(subject, _)| {
            receipt.obligation.planned.key.subject
                == super::mechanical_receipt::MechanicalSubjectKey::Local {
                    owner: subject.fn_did,
                    mir_local: subject.local.as_u32(),
                    slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
                }
        })
        .is_some_and(|(_, decision)| match decision {
            Decision::Opt { .. } => true,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => false,
        })
}

/// Class-consistency preflight for the new Option family. A failed optional
/// operation requests its prior raw disposition; a changed callee interface
/// remains a load-bearing requirement and keeps the existing class hold.
pub(crate) fn additive_option_fallbacks(
    table: &DecisionTable,
    planned: &Plan,
) -> Vec<(usize, super::decision::DegradeReason)> {
    use super::mechanical_receipt::{CanonicalCallee, MechanicalState};
    let mut requests = Vec::new();
    for (index, receipt) in planned.option_receipt_plans.iter().enumerate() {
        if receipt.obligation.intended_terminal_state != MechanicalState::HeldNonmechanical
            || matches!(
                receipt.operation.as_str(),
                "excluded-cursor" | "handoff-return" | "handoff-use"
            )
            || !option_receipt_requires_changed_form(table, receipt)
        {
            continue;
        }
        let site = &receipt.obligation.planned.key.site;
        let changed_callee = match (&site.callee, site.argument_index) {
            (Some(CanonicalCallee::Local(callee)), Some(argument)) => {
                callee.as_local().is_some_and(|callee| {
                    super::terminal_parameter_form(
                        table,
                        &planned.class_finalization,
                        callee,
                        argument as usize,
                    ) != super::decision::seam::Form::Raw
                })
            }
            _ => false,
        };
        if changed_callee {
            continue;
        }
        let (subject, _) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                receipt.obligation.planned.key.subject
                    == super::mechanical_receipt::MechanicalSubjectKey::Local {
                        owner: subject.fn_did,
                        mir_local: subject.local.as_u32(),
                        slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
                    }
            })
            .expect("changed Option obligation has its subject");
        let prior_reason = if subject.null_init {
            super::decision::DegradeReason::NullInit
        } else if matches!(subject.kind, super::decision::SubjectKind::Local) {
            super::decision::DegradeReason::OptLocalConstruction
        } else {
            super::decision::DegradeReason::OptUseUnsupported
        };
        requests.push((index, prior_reason));
    }
    requests
}

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
            Decision::Degraded(record)
                if record.reason == super::decision::DegradeReason::PairRawView =>
            {
                (false, None)
            }
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
                atom_ids: edit.atom_ids.clone(),
                key,
                edit_key,
                state: ClassSiteState::EditReady,
                expected_form: bridge.expected_form.clone(),
                found_form: bridge.found_form.clone(),
                argument_kind: bridge.argument_kind.clone(),
                extent: bridge.extent.clone(),
                retention: bridge.retention,
                waiver_id: bridge.waiver_id.clone(),
                unsafe_context: bridge.unsafe_context,
            });
        }
    }

    let mut dependency_edges = table
        .seams
        .edits
        .iter()
        .map(|edit| (SignatureClassId::of(edit.bridge.caller), edit.owner_class))
        .collect::<Vec<_>>();
    dependency_edges.extend(table.seams.interface_dependencies.iter().copied());
    dependency_edges.extend(table.seams.generated_item_dependencies.iter().copied());
    dependency_edges.extend(
        planned
            .option_receipt_plans
            .iter()
            .filter(|receipt| {
                receipt.obligation.intended_terminal_state
                    != super::mechanical_receipt::MechanicalState::Reclassified
                    && matches!(
                        receipt.operation.as_str(),
                        "call-required" | "call-optional"
                    )
            })
            .flat_map(|receipt| {
                receipt
                    .obligation
                    .planned
                    .dependency_classes
                    .iter()
                    .map(move |&dependency| (receipt.owner_class, dependency))
            }),
    );
    dependency_edges.extend(table.entries.iter().filter_map(
        |(subject, decision)| match decision {
            Decision::InferredRef { callee, .. } => Some((
                SignatureClassId::of(subject.fn_did),
                SignatureClassId::of(*callee),
            )),
            Decision::Ref { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => None,
        },
    ));
    dependency_edges.extend(table.return_receivers.plans.values().map(|receiver| {
        (
            SignatureClassId::of(receiver.node.0),
            SignatureClassId::of(receiver.callee),
        )
    }));
    for (dependent, dependency) in dependency_edges {
        if dependent == dependency || !by_class.contains_key(&dependency) {
            continue;
        }
        if let Some(class) = by_class.get_mut(&dependent) {
            class.depends_on.push(dependency);
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
    planned
        .attribution_intervals
        .retain(|site| finalization.classes[&site.owner_class].is_ready());
    planned.class_finalization = finalization;
}

fn dependency_reach(
    start: SignatureClassId,
    classes: &BTreeMap<SignatureClassId, SignatureClassPlan>,
) -> std::collections::BTreeSet<SignatureClassId> {
    let mut reached = std::collections::BTreeSet::new();
    let mut pending = vec![start];
    while let Some(class) = pending.pop() {
        if !reached.insert(class) {
            continue;
        }
        if let Some(plan) = classes.get(&class) {
            pending.extend(
                plan.depends_on
                    .iter()
                    .copied()
                    .filter(|dependency| classes.contains_key(dependency)),
            );
        }
    }
    reached
}

/// Dependency SCCs in the binding recovery order: dependents before the
/// interfaces they consume, with only the local DefId index as a tie-breaker.
pub(crate) fn dependency_scc_order(
    classes: &BTreeMap<SignatureClassId, SignatureClassPlan>,
) -> Vec<Vec<SignatureClassId>> {
    let reaches = classes
        .keys()
        .copied()
        .map(|id| (id, dependency_reach(id, classes)))
        .collect::<BTreeMap<_, _>>();
    let mut unassigned = classes
        .keys()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    let mut groups = Vec::<Vec<SignatureClassId>>::new();
    while let Some(&seed) = unassigned.first() {
        let mut group = unassigned
            .iter()
            .copied()
            .filter(|candidate| {
                reaches[&seed].contains(candidate) && reaches[candidate].contains(&seed)
            })
            .collect::<Vec<_>>();
        group.sort();
        for member in &group {
            unassigned.remove(member);
        }
        groups.push(group);
    }

    let group_of = groups
        .iter()
        .enumerate()
        .flat_map(|(index, group)| group.iter().copied().map(move |id| (id, index)))
        .collect::<BTreeMap<_, _>>();
    let mut outgoing = vec![std::collections::BTreeSet::<usize>::new(); groups.len()];
    let mut indegree = vec![0usize; groups.len()];
    for (&id, class) in classes {
        let source = group_of[&id];
        for dependency in &class.depends_on {
            let Some(&target) = group_of.get(dependency) else {
                continue;
            };
            if source != target && outgoing[source].insert(target) {
                indegree[target] += 1;
            }
        }
    }
    let mut ready = groups
        .iter()
        .enumerate()
        .filter(|(index, _)| indegree[*index] == 0)
        .map(|(index, group)| (group[0], index))
        .collect::<std::collections::BTreeSet<_>>();
    let mut ordered = Vec::new();
    while let Some(&(key, index)) = ready.first() {
        ready.remove(&(key, index));
        ordered.push(groups[index].clone());
        for &target in &outgoing[index] {
            indegree[target] -= 1;
            if indegree[target] == 0 {
                ready.insert((groups[target][0], target));
            }
        }
    }
    debug_assert_eq!(ordered.iter().map(Vec::len).sum::<usize>(), classes.len());
    ordered
}

pub(crate) fn dependent_closure(
    classes: &BTreeMap<SignatureClassId, SignatureClassPlan>,
    seeds: &std::collections::BTreeSet<SignatureClassId>,
) -> std::collections::BTreeSet<SignatureClassId> {
    let mut closure = seeds.clone();
    loop {
        let before = closure.len();
        for class in classes.values() {
            if class.is_ready()
                && class
                    .depends_on
                    .iter()
                    .any(|dependency| closure.contains(dependency))
            {
                closure.insert(class.id);
            }
        }
        if closure.len() == before {
            return closure;
        }
    }
}

pub(crate) fn strict_recovery_subset(
    ready: &std::collections::BTreeSet<SignatureClassId>,
    reverted: &std::collections::BTreeSet<SignatureClassId>,
) -> bool {
    !reverted.is_empty() && reverted.is_subset(ready) && reverted.len() < ready.len()
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
    pub native_return_plans: native_return::NativeReturnPlans,
    pub outbound_expression_plans: outbound_expression::OutboundExpressionReceiptPlans,
    pub outbound_expression_sites:
        rustc_hash::FxHashMap<super::decision::raw_boundary::RawBoundarySiteKey, ClassSite>,
    pub raw_receiver_sites:
        rustc_hash::FxHashMap<super::decision::return_receiver::Node, ClassSite>,
    pub outbound_return_plans: outbound_return::OutboundReturnPlans,
    pub receiver_input_receipts: receiver_input::ReceiverReceiptMap,
    pub callee_parameter_input_receipts: callee_parameter_input::InputReceiptMap,
    pub sibling_receipt_plans: Vec<sibling_overlap::SiblingReceiptPlan>,
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
    /// Whole-call/generated-site intervals used for diagnostics that land
    /// outside an edited argument or declaration.
    pub attribution_intervals: Vec<ClassAttributionInterval>,
    /// Proof-site-owned wave-3b A5 obligations. The common and specialized
    /// ledgers are materialized from this one carrier after class finalization.
    pub a5_receipt_plans: Vec<super::mechanical_receipt::A5ProofSiteReceiptPlan>,
    /// Item-2 local-slice construction obligations, sharing one identity with
    /// the common mechanical ledger.
    pub slice_construction_receipt_plans:
        Vec<super::mechanical_receipt::SliceConstructionReceiptPlan>,
    pub slice_use_receipt_plans: Vec<super::mechanical_receipt::SliceUseReceiptPlan>,
    pub option_receipt_plans: Vec<super::mechanical_receipt::OptionPresentationReceiptPlan>,
    pub declaration_receipt_plans: Vec<super::mechanical_receipt::DeclarationShapeReceiptPlan>,
    pub unowned_a5_proof_sites: usize,
    /// A5 calls after terminal-interface validation/re-planning. The AST graft
    /// consumes this sealed plan; it never recomputes the terminal verdict.
    pub terminal_call_plans: super::decision::seam::TerminalCallPlans,
}

fn terminal_seam_site(
    seam: &super::decision::seam::SeamEdit,
    file: &FileKey,
    lo: usize,
    hi: usize,
    edit: Option<&Edit>,
) -> ClassSite {
    use sha2::{Digest, Sha256};
    let file = file_key_label(file);
    ClassSite {
        atom_ids: seam.atom_ids.clone(),
        key: seam
            .bridge
            .materialize(seam.owner_class, file.clone(), lo as u32, hi as u32),
        edit_key: edit.map_or_else(
            || "-".to_owned(),
            |edit| {
                format!(
                    "class={}|arm={}|interval={}:{}:{}|kind={}|replacement_sha256={:x}",
                    seam.owner_class.order_key(),
                    seam.bridge.arm,
                    file,
                    lo,
                    hi,
                    seam.bridge.bridge_kind,
                    Sha256::digest(edit.replacement.as_bytes()),
                )
            },
        ),
        state: if edit.is_some() {
            ClassSiteState::EditReady
        } else {
            ClassSiteState::ZeroSyntaxReady
        },
        expected_form: seam.bridge.expected_form.clone(),
        found_form: seam.bridge.found_form.clone(),
        argument_kind: seam.bridge.argument_kind.clone(),
        extent: seam.bridge.extent.clone(),
        retention: seam.bridge.retention,
        waiver_id: seam.bridge.waiver_id.clone(),
        unsafe_context: seam.bridge.unsafe_context,
    }
}

impl Plan {
    pub(crate) fn outbound_return_receipts(
        &self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Result<
        (
            Vec<super::mechanical_receipt::OutboundReturnRequirement>,
            Vec<super::mechanical_receipt::MechanicalObligationEvent>,
            Vec<super::mechanical_receipt::OutboundReturnBridgeReceiptRow>,
        ),
        String,
    > {
        let mut withheld = classes.clone();
        withheld.extend(self.held_classes());
        let effective = self.effective_reverted_classes(&withheld, atoms);
        let (mut required, mut common, mut rows) = self
            .outbound_return_plans
            .materialize(
                &self.terminal_call_plans.receiver_inputs,
                &self.terminal_call_plans.raw_receivers,
                &effective,
                atoms,
            )
            .map_err(|failures| format!("outbound-return-custody:{failures:?}"))?;
        let (native_required, native_common, native_rows) = self
            .native_return_plans
            .materialize(&self.terminal_call_plans, &effective, atoms)
            .map_err(|failures| format!("outbound-return-native-custody:{failures:?}"))?;
        required.extend(native_required);
        common.extend(native_common);
        rows.extend(native_rows);
        let (expression_required, expression_common, expression_rows) = self
            .outbound_expression_plans
            .materialize(&self.terminal_call_plans.outbound_expressions, &effective)
            .map_err(|failures| format!("outbound-expression-custody:{failures:?}"))?;
        required.extend(expression_required);
        common.extend(expression_common);
        rows.extend(expression_rows);
        Ok((required, common, rows))
    }

    pub(crate) fn validate_outbound_return_receipts(
        &self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Result<(), String> {
        let (required, common, rows) = self.outbound_return_receipts(classes, atoms)?;
        super::mechanical_receipt::reconcile_outbound_return_rows(
            &required,
            &rows,
            &common,
            &self.bridge_events_with_atoms(classes, atoms),
        )
        .map(|_| ())
    }

    pub(crate) fn validate_receiver_input_receipts(
        &self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Result<(), String> {
        let selected = self.receiver_input_receipts.selected(
            &self.terminal_call_plans.receiver_inputs,
            classes,
            atoms,
        );
        if selected.failures.is_empty() {
            return Ok(());
        }
        Err(format!(
            "return-receiver-input-custody:{}",
            selected
                .failures
                .iter()
                .map(|failure| format!(
                    "{:?}:callee={}:caller={}:hir={}:{}",
                    failure.kind,
                    failure.callee.order_key(),
                    failure.caller.order_key(),
                    failure.node.1.local_id.as_u32(),
                    failure.reason
                ))
                .collect::<Vec<_>>()
                .join(";")
        ))
    }

    fn receiver_declaration_reverted(
        &self,
        receipt: &super::mechanical_receipt::DeclarationShapeReceiptPlan,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> bool {
        use super::mechanical_receipt::{MechanicalMechanism, MechanicalSubjectKey};
        let event = &receipt.obligation.planned;
        if event.mechanism != MechanicalMechanism::DeclarationExplicitType {
            return false;
        }
        self.terminal_call_plans.receiver_inputs.plans.values().any(|input| {
            input.active(classes, atoms) && receipt.owner_class == input.selection.callee
                && matches!(event.key.subject, MechanicalSubjectKey::Local { owner, mir_local, .. }
                    if owner == input.selection.node.0 && mir_local == input.destination.as_u32())
        })
    }

    pub(crate) fn validate_callee_parameter_input_receipts(
        &self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Result<(), String> {
        let selected = self.callee_parameter_input_receipts.selected(
            &self.terminal_call_plans.callee_parameter_inputs,
            classes,
            atoms,
        );
        if selected.failures.is_empty() {
            return Ok(());
        }
        Err(format!(
            "callee-parameter-input-custody:{}",
            selected
                .failures
                .iter()
                .map(|failure| format!(
                    "{:?}:class={}:caller={}:arg={}..{}:{}",
                    failure.kind,
                    failure.target.order_key(),
                    failure.caller.order_key(),
                    failure.key.1,
                    failure.key.2,
                    failure.reason
                ))
                .collect::<Vec<_>>()
                .join(";")
        ))
    }

    pub(crate) fn effective_reverted_classes(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> BTreeSet<SignatureClassId> {
        self.terminal_call_plans
            .effective_reverted_classes(reverted, atoms)
    }

    pub(crate) fn replace_terminal_seam(
        &mut self,
        old: &super::decision::seam::SeamEdit,
        new: &super::decision::seam::SeamEdit,
        located: (FileKey, usize, usize),
    ) -> Result<(), String> {
        let (file, lo, hi) = located;
        let old_key =
            old.bridge
                .materialize(old.owner_class, file_key_label(&file), lo as u32, hi as u32);
        let Some(class) = self.class_finalization.classes.get_mut(&old.owner_class) else {
            return Err("terminal-seam-owner-missing".to_owned());
        };
        let matches = class
            .sites
            .iter()
            .enumerate()
            .filter(|(_, site)| site.key == old_key)
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(format!(
                "terminal-seam-site-cardinality:{}:{}",
                old.owner_class.order_key(),
                matches.len()
            ));
        }
        let mut removed = Vec::new();
        if let Some(edits) = self.by_file.get_mut(&file) {
            let mut index = 0;
            while index < edits.len() {
                if edits[index].lo == lo
                    && edits[index].hi == hi
                    && edits[index].owner_class == Some(old.owner_class)
                    && edits[index].bridge.as_ref() == Some(&old.bridge)
                {
                    removed.push(edits.remove(index));
                } else {
                    index += 1;
                }
            }
        }
        if removed.len() != usize::from(!old.zero_syntax) {
            return Err(format!(
                "terminal-seam-edit-cardinality:{}:{}",
                old.owner_class.order_key(),
                removed.len()
            ));
        }
        let replacement = if new.zero_syntax {
            None
        } else {
            let mut edit = removed.pop().ok_or("terminal-seam-zero-to-edit-unbuilt")?;
            edit.replacement = new.replacement.clone();
            edit.bridge = Some(new.bridge.clone());
            edit.justification = Justification::SeamAdapter {
                family: match new.family {
                    super::decision::seam::SeamFamily::Safe => "safe",
                    super::decision::seam::SeamFamily::Reborrow => "reborrow",
                },
                fabricated: new.spec.len.as_ref().is_some_and(|len| len.is_fabricated()),
            };
            Some(edit)
        };
        let site = terminal_seam_site(new, &file, lo, hi, replacement.as_ref());
        class.sites[matches[0]] = site.clone();
        class.site_keys = class.sites.iter().map(|site| site.key.clone()).collect();
        class.edit_keys = class
            .sites
            .iter()
            .filter(|site| site.edit_key != "-")
            .map(|site| site.edit_key.clone())
            .collect();
        self.preclass_sites.retain(|site| site.key != old_key);
        if let Some(edit) = replacement {
            self.by_file.entry(file).or_default().push(edit);
        } else {
            self.preclass_sites.push(site);
        }
        Ok(())
    }

    /// Hold exactly one terminally stale owner class, then apply the already
    /// declared dependency rule and remove every edit belonging to the newly
    /// held closure. This is class recovery, never a program-level failure.
    pub(crate) fn hold_terminal_a5_class(&mut self, owner: SignatureClassId, reason: String) {
        self.hold_terminal_class(owner, Arm::Pair, "a5-fallback-unrenderable", reason);
    }

    pub(crate) fn replace_terminal_a5_edit(
        &mut self,
        file: &FileKey,
        replacement: Edit,
        views: &[super::decision::seam::A5RawViewTemp],
    ) -> Result<(), String> {
        let bridge = replacement
            .bridge
            .clone()
            .ok_or("a5-fallback-unrenderable:bridge-absent")?;
        let new_key = physical_edit_key(file, &replacement)
            .ok_or("a5-fallback-unrenderable:edit-key-absent")?;
        let edits = self
            .by_file
            .get_mut(file)
            .ok_or("a5-fallback-unrenderable:materialized-file-absent")?;
        let matching = edits
            .iter()
            .enumerate()
            .filter(|(_, old)| {
                old.owner_class == replacement.owner_class
                    && old.lo == replacement.lo
                    && old.hi == replacement.hi
                    && old.edit_kind == replacement.edit_kind
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let [index] = matching.as_slice() else {
            return Err("a5-fallback-unrenderable:materialized-edit-not-unique".into());
        };
        let old_key = physical_edit_key(file, &edits[*index])
            .ok_or("a5-fallback-unrenderable:old-edit-key-absent")?;
        edits[*index] = replacement;
        let update = |site: &mut ClassSite| {
            if site.edit_key != old_key {
                return;
            }
            site.edit_key.clone_from(&new_key);
            if let Some(view) = views
                .iter()
                .find(|view| site.key.position == format!("arg{}", view.argument_index))
            {
                site.expected_form = super::decision::seam::Form::Raw.key().into();
                site.found_form = view.found_form.key().into();
                site.extent = BridgeExtentKind::None;
            } else {
                site.expected_form.clone_from(&bridge.expected_form);
                site.found_form.clone_from(&bridge.found_form);
                site.extent.clone_from(&bridge.extent);
                site.unsafe_context = bridge.unsafe_context;
            }
        };
        for site in &mut self.preclass_sites {
            update(site);
        }
        for class in self.class_finalization.classes.values_mut() {
            for site in &mut class.sites {
                update(site);
            }
            for key in &mut class.edit_keys {
                if *key == old_key {
                    key.clone_from(&new_key);
                }
            }
            class.edit_keys.sort();
            class.edit_keys.dedup();
        }
        Ok(())
    }

    pub(crate) fn hold_terminal_class(
        &mut self,
        owner: SignatureClassId,
        arm: Arm,
        bridge_kind: &'static str,
        reason: String,
    ) {
        let Some(class) = self.class_finalization.classes.get_mut(&owner) else {
            return;
        };
        let site = ClassSite::dropped(owner, owner, arm, bridge_kind, reason.clone());
        class.site_keys.push(site.key.clone());
        class.edit_keys.push(site.edit_key.clone());
        class.sites.push(site);
        class.site_keys.sort_by_key(BridgeSiteKey::receipt_key);
        class.site_keys.dedup();
        class.edit_keys.sort();
        class.edit_keys.dedup();
        class.sites.sort_by_key(|site| site.key.receipt_key());
        class.sites.dedup_by(|left, right| left.key == right.key);
        let mut reasons = class.hold_reasons().to_vec();
        reasons.push(reason);
        reasons.sort();
        reasons.dedup();
        class.disposition = SignatureClassDisposition::Held(reasons);

        loop {
            let newly_held = self
                .class_finalization
                .classes
                .iter()
                .filter(|(_, class)| class.is_ready())
                .filter_map(|(&id, class)| {
                    class
                        .depends_on
                        .iter()
                        .copied()
                        .find(|dependency| {
                            self.class_finalization
                                .classes
                                .get(dependency)
                                .is_some_and(|dependency| !dependency.is_ready())
                        })
                        .map(|dependency| (id, dependency))
                })
                .collect::<Vec<_>>();
            if newly_held.is_empty() {
                break;
            }
            for (id, dependency) in newly_held {
                self.class_finalization
                    .classes
                    .get_mut(&id)
                    .expect("dependent terminal class exists")
                    .disposition = SignatureClassDisposition::Held(vec![format!(
                    "dependency-class-held:{}",
                    dependency.order_key()
                )]);
            }
        }

        let ready = self
            .class_finalization
            .classes
            .values()
            .filter(|class| class.is_ready())
            .map(|class| class.id)
            .collect::<std::collections::BTreeSet<_>>();
        self.by_file.retain(|_, edits| {
            edits.retain(|edit| edit.owner_class.is_none_or(|class| ready.contains(&class)));
            !edits.is_empty()
        });
        self.attribution_intervals
            .retain(|site| ready.contains(&site.owner_class));
        self.terminal_call_plans
            .a5_raw_calls
            .retain(|call| ready.contains(&call.owner_class));
    }

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
        reverted: &BTreeSet<SignatureClassId>,
    ) -> Vec<super::bridge_receipt::BridgeReceiptEvent> {
        self.bridge_events_with_atoms(reverted, &BTreeSet::new())
    }

    pub(crate) fn bridge_events_with_atoms(
        &self,
        reverted: &std::collections::BTreeSet<SignatureClassId>,
        reverted_atoms: &BTreeSet<String>,
    ) -> Vec<super::bridge_receipt::BridgeReceiptEvent> {
        use super::bridge_receipt::{BridgeReceiptEvent, BridgeReceiptStage, BridgeReceiptState};
        let return_origin_reverted = self
            .terminal_call_plans
            .return_origin_dependencies
            .effective_reverted_classes(&BTreeSet::new(), reverted_atoms);
        let mut withheld = reverted.clone();
        withheld.extend(self.held_classes());
        let (reverted, input_holds) = self
            .terminal_call_plans
            .input_reversion_closure(&withheld, reverted_atoms);
        let inputs = self.callee_parameter_input_receipts.selected(
            &self.terminal_call_plans.callee_parameter_inputs,
            &reverted,
            reverted_atoms,
        );
        let receivers = self.receiver_input_receipts.selected(
            &self.terminal_call_plans.receiver_inputs,
            &reverted,
            reverted_atoms,
        );
        let atom_dropped = self
            .by_file
            .iter()
            .flat_map(|(file, edits)| {
                edits
                    .iter()
                    .filter(|edit| {
                        edit.atom_ids
                            .iter()
                            .any(|atom| reverted_atoms.contains(atom))
                    })
                    .filter_map(move |edit| physical_edit_key(file, edit))
            })
            .collect::<BTreeSet<_>>();
        let mut events = Vec::new();
        for class in self.class_finalization.classes.values() {
            let terminal_drop = if return_origin_reverted.contains(&class.id) {
                Some("return-origin-atom-reverted".to_owned())
            } else if !class.is_ready() {
                Some(class.hold_reasons().join(";"))
            } else if let Some(reasons) = input_holds.get(&class.id) {
                Some(reasons.iter().cloned().collect::<Vec<_>>().join(";"))
            } else if reverted.contains(&class.id) {
                Some("class-reverted-after-verify".to_owned())
            } else {
                None
            };
            for site in &class.sites {
                // Logical dependencies also govern sites without a text edit.
                // Receipts sharing a physical carrier share its atom fate.
                // A5/C9 carriers have no atom dependencies and stay Applied
                // with their source input rendering while their class survives.
                let terminal_drop = terminal_drop
                    .clone()
                    .or_else(|| {
                        inputs
                            .withdrawn
                            .contains(&site.key)
                            .then(|| "callee-parameter-input-selected".to_owned())
                    })
                    .or_else(|| {
                        receivers
                            .withdrawn
                            .contains(&site.key)
                            .then(|| "return-receiver-input-selected".to_owned())
                    })
                    .or_else(|| {
                        (site
                            .atom_ids
                            .iter()
                            .any(|atom| reverted_atoms.contains(atom))
                            || atom_dropped.contains(&site.edit_key))
                        .then(|| "atom-reverted-after-verify".to_owned())
                    });
                events.push(BridgeReceiptEvent {
                    site: site.key.clone(),
                    expected_form: site.expected_form.clone(),
                    found_form: site.found_form.clone(),
                    argument_kind: site.argument_kind.clone(),
                    stage: BridgeReceiptStage::Plan,
                    state: BridgeReceiptState::Planned,
                    drop_reason: None,
                    extent: site.extent.clone(),
                    retention: site.retention,
                    waiver_id: site.waiver_id.clone(),
                });
                events.push(BridgeReceiptEvent {
                    site: site.key.clone(),
                    expected_form: site.expected_form.clone(),
                    found_form: site.found_form.clone(),
                    argument_kind: site.argument_kind.clone(),
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
        events.extend(inputs.bridge_events);
        events.extend(receivers.bridge_events);
        events
    }

    pub(crate) fn unsafe_context_events(
        &self,
        reverted: &std::collections::BTreeSet<SignatureClassId>,
    ) -> Vec<super::mechanical_receipt::UnsafeContextReceiptEvent> {
        self.unsafe_context_events_with_atoms(reverted, &BTreeSet::new())
    }

    pub(crate) fn unsafe_context_events_with_atoms(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Vec<super::mechanical_receipt::UnsafeContextReceiptEvent> {
        let mut withheld = reverted.clone();
        withheld.extend(self.held_classes());
        let (effective_reverted, input_holds) = self
            .terminal_call_plans
            .input_reversion_closure(&withheld, atoms);
        let reverted = &effective_reverted;
        let inputs = self.callee_parameter_input_receipts.selected(
            &self.terminal_call_plans.callee_parameter_inputs,
            reverted,
            atoms,
        );
        let receivers = self.receiver_input_receipts.selected(
            &self.terminal_call_plans.receiver_inputs,
            reverted,
            atoms,
        );
        use super::{
            bridge_receipt::{BridgeReceiptStage, BridgeReceiptState},
            mechanical_receipt::UnsafeContextReceiptEvent,
        };

        let mut events = Vec::new();
        for class in self.class_finalization.classes.values() {
            let terminal_drop = if !class.is_ready() {
                Some(class.hold_reasons().join(";"))
            } else if let Some(reasons) = input_holds.get(&class.id) {
                Some(reasons.iter().cloned().collect::<Vec<_>>().join(";"))
            } else if reverted.contains(&class.id) {
                Some("class-reverted-after-verify".to_owned())
            } else {
                None
            };
            let disposition = if !class.is_ready() {
                "held"
            } else if reverted.contains(&class.id) {
                "reverted"
            } else {
                "ready"
            };
            for site in &class.sites {
                let Some(presentation) = site.unsafe_context else {
                    continue;
                };
                let terminal_drop = terminal_drop
                    .clone()
                    .or_else(|| {
                        inputs
                            .withdrawn
                            .contains(&site.key)
                            .then(|| "callee-parameter-input-selected".to_owned())
                    })
                    .or_else(|| {
                        receivers
                            .withdrawn
                            .contains(&site.key)
                            .then(|| "return-receiver-input-selected".to_owned())
                    })
                    .or_else(|| {
                        site.atom_ids
                            .iter()
                            .any(|atom| atoms.contains(atom))
                            .then(|| "atom-reverted-after-verify".into())
                    });
                events.push(UnsafeContextReceiptEvent {
                    site: site.key.clone(),
                    enclosing: site.key.caller,
                    presentation,
                    terminal_class_disposition: disposition.to_owned(),
                    stage: BridgeReceiptStage::Plan,
                    state: BridgeReceiptState::Planned,
                    drop_reason: None,
                });
                events.push(UnsafeContextReceiptEvent {
                    site: site.key.clone(),
                    enclosing: site.key.caller,
                    presentation,
                    terminal_class_disposition: disposition.to_owned(),
                    stage: BridgeReceiptStage::Terminal,
                    state: if terminal_drop.is_some() {
                        BridgeReceiptState::Dropped
                    } else {
                        BridgeReceiptState::Applied
                    },
                    drop_reason: terminal_drop.clone(),
                });
            }
        }
        events.extend(inputs.unsafe_context_events);
        events.extend(receivers.unsafe_context_events);
        events
    }

    pub(crate) fn mechanical_receipts(
        &self,
        reverted: &std::collections::BTreeSet<SignatureClassId>,
    ) -> (
        Vec<super::mechanical_receipt::MechanicalObligationEvent>,
        Vec<super::mechanical_receipt::A5ProofSiteFallbackReceiptRow>,
        Vec<super::mechanical_receipt::SliceConstructionReceiptRow>,
    ) {
        self.mechanical_receipts_with_atoms(reverted, &BTreeSet::new())
    }

    pub(crate) fn mechanical_receipts_with_atoms(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> (
        Vec<super::mechanical_receipt::MechanicalObligationEvent>,
        Vec<super::mechanical_receipt::A5ProofSiteFallbackReceiptRow>,
        Vec<super::mechanical_receipt::SliceConstructionReceiptRow>,
    ) {
        let effective_reverted = self.effective_reverted_classes(reverted, atoms);
        let reverted = &effective_reverted;
        let mut events = Vec::new();
        let mut a5_rows = Vec::new();
        let mut slice_rows = Vec::new();
        for argument in &self.terminal_call_plans.surface_arguments {
            let live = self
                .class_finalization
                .classes
                .get(&argument.owner_class)
                .is_some_and(SignatureClassPlan::is_ready);
            let removed = reverted.contains(&argument.owner_class)
                || argument.atom_ids.iter().any(|atom| atoms.contains(atom));
            events.extend(argument.obligation.events(live, removed));
        }
        for receipt in &self.a5_receipt_plans {
            let class_live = self
                .class_finalization
                .classes
                .get(&receipt.owner_class)
                .is_some_and(SignatureClassPlan::is_ready);
            let (pair, rows) =
                receipt.materialize(class_live, reverted.contains(&receipt.owner_class));
            events.extend(pair);
            a5_rows.extend(rows);
        }
        for receipt in &self.slice_construction_receipt_plans {
            let class_live = self
                .class_finalization
                .classes
                .get(&receipt.owner_class)
                .is_some_and(SignatureClassPlan::is_ready);
            let (pair, rows) =
                receipt.materialize(class_live, reverted.contains(&receipt.owner_class));
            events.extend(pair);
            slice_rows.extend(rows);
        }
        for receipt in &self.slice_use_receipt_plans {
            let live = self.slice_use_class_live(receipt, reverted);
            let (pair, _) = receipt.materialize(live, reverted.contains(&receipt.owner_class));
            events.extend(pair);
        }
        for receipt in &self.option_receipt_plans {
            let live = self.option_class_live(receipt, reverted);
            events.extend(
                receipt
                    .materialize(live, reverted.contains(&receipt.owner_class))
                    .0,
            );
        }
        for receipt in &self.declaration_receipt_plans {
            let live = self
                .class_finalization
                .classes
                .get(&receipt.owner_class)
                .is_some_and(SignatureClassPlan::is_ready);
            events.extend(
                receipt
                    .materialize(
                        live,
                        reverted.contains(&receipt.owner_class)
                            || self.receiver_declaration_reverted(receipt, reverted, atoms),
                    )
                    .0,
            );
        }
        (events, a5_rows, slice_rows)
    }

    pub(crate) fn declaration_receipt_rows(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
    ) -> Vec<super::mechanical_receipt::DeclarationShapeReceiptRow> {
        self.declaration_receipt_rows_with_atoms(reverted, &BTreeSet::new())
    }

    pub(crate) fn declaration_receipt_rows_with_atoms(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Vec<super::mechanical_receipt::DeclarationShapeReceiptRow> {
        let reverted = self.effective_reverted_classes(reverted, atoms);
        self.declaration_receipt_plans
            .iter()
            .flat_map(|receipt| {
                let live = self
                    .class_finalization
                    .classes
                    .get(&receipt.owner_class)
                    .is_some_and(SignatureClassPlan::is_ready);
                receipt
                    .materialize(
                        live,
                        reverted.contains(&receipt.owner_class)
                            || self.receiver_declaration_reverted(receipt, &reverted, atoms),
                    )
                    .1
            })
            .collect()
    }

    fn slice_use_class_live(
        &self,
        receipt: &super::mechanical_receipt::SliceUseReceiptPlan,
        reverted: &BTreeSet<SignatureClassId>,
    ) -> bool {
        std::iter::once(&receipt.owner_class)
            .chain(receipt.obligation.planned.dependency_classes.iter())
            .all(|owner| {
                !reverted.contains(owner)
                    && self
                        .class_finalization
                        .classes
                        .get(owner)
                        .is_some_and(SignatureClassPlan::is_ready)
            })
    }

    pub(crate) fn slice_use_receipt_rows(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
    ) -> Vec<super::mechanical_receipt::SliceUseAdapterReceiptRow> {
        self.slice_use_receipt_plans
            .iter()
            .flat_map(|receipt| {
                receipt
                    .materialize(
                        self.slice_use_class_live(receipt, reverted),
                        reverted.contains(&receipt.owner_class),
                    )
                    .1
            })
            .collect()
    }

    fn option_class_live(
        &self,
        receipt: &super::mechanical_receipt::OptionPresentationReceiptPlan,
        reverted: &BTreeSet<SignatureClassId>,
    ) -> bool {
        std::iter::once(&receipt.owner_class)
            .chain(receipt.obligation.planned.dependency_classes.iter())
            .all(|owner| {
                !reverted.contains(owner)
                    && self
                        .class_finalization
                        .classes
                        .get(owner)
                        .is_some_and(SignatureClassPlan::is_ready)
            })
    }

    pub(crate) fn option_receipt_rows(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
    ) -> Vec<super::mechanical_receipt::OptionPresentationReceiptRow> {
        self.option_receipt_plans
            .iter()
            .flat_map(|receipt| {
                receipt
                    .materialize(
                        self.option_class_live(receipt, reverted),
                        reverted.contains(&receipt.owner_class),
                    )
                    .1
            })
            .collect()
    }
}

fn declaration_lifetime<'a>(
    table: &'a DecisionTable,
    subject: &super::decision::Subject,
) -> Option<&'a str> {
    match subject.kind {
        super::decision::SubjectKind::Param { hir_index } => table
            .lifetime_plan
            .function(subject.fn_did)
            .and_then(|plan| {
                plan.lifetime_for(super::decision::lifetime::FnSignatureSlot::arg(
                    hir_index + 1,
                    0,
                    0,
                ))
            }),
        super::decision::SubjectKind::Local => None,
    }
}

fn declaration_receipts(
    table: &DecisionTable,
    owner_of: &impl Fn(&super::decision::Subject) -> String,
) -> Vec<super::mechanical_receipt::DeclarationShapeReceiptPlan> {
    use super::mechanical_receipt::*;
    table
        .entries
        .iter()
        .filter_map(|(subject, decision)| {
            if subject.decl_shape == super::decision::DeclShape::RawPtr
                && !table
                    .declaration_patterns
                    .contains_key(&(subject.fn_did, subject.hir_id))
            {
                return None;
            }
            let owner = SignatureClassId::of(subject.fn_did);
            let node = (subject.fn_did, subject.hir_id);
            let original = table
                .declaration_patterns
                .get(&node)
                .map(|pattern| pattern.input_type.clone())
                .or_else(|| {
                    table
                        .declaration_pointees
                        .get(&node)
                        .map(|pointee| pointee.original_alias.clone())
                })
                .unwrap_or_else(|| subject.decl_shape.key().to_owned());
            let pattern = table.declaration_patterns.get(&node);
            let emitted = table
                .declaration_pointees
                .get(&node)
                .map(|ty| ty.pointee.as_str())
                .or_else(|| pattern.map(|carrier| carrier.pointee.as_str()))
                .and_then(|pointee| {
                    super::decision::declaration::emitted_type(
                        decision,
                        pointee,
                        declaration_lifetime(table, subject),
                    )
                });
            let (settled, state, reason) = match decision {
                Decision::Degraded(record) => (
                    original.clone(),
                    MechanicalState::Reclassified,
                    Some(MechanicalTerminalReason::EvidenceMissing(
                        record.reason.key().to_owned(),
                    )),
                ),
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_) => match emitted {
                    Some(ty) => (ty, MechanicalState::Applied, None),
                    None => (
                        original.clone(),
                        MechanicalState::HeldNonmechanical,
                        Some(MechanicalTerminalReason::EvidenceMissing(
                            "declaration-pointee-unavailable".to_owned(),
                        )),
                    ),
                },
            };
            let initializer_kind = match subject.kind {
                super::decision::SubjectKind::Param { .. } => "parameter".to_owned(),
                super::decision::SubjectKind::Local => table
                    .slice_constructions
                    .iter()
                    .find(|construction| construction.node == node)
                    .map_or_else(
                        || {
                            subject
                                .ctor
                                .as_ref()
                                .map_or(
                                    "local-expression",
                                    super::decision::construction::Construction::key,
                                )
                                .to_owned()
                        },
                        |construction| construction.initializer_kind.to_owned(),
                    ),
            };
            let site = CanonicalSiteKey {
                owner: subject.fn_did,
                location: CanonicalLocation::Hir {
                    owner: subject.fn_did,
                    item_local_id: subject.hir_id.local_id.as_u32(),
                },
                callee: None,
                argument_index: None,
                slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
            };
            let event = MechanicalObligationEvent {
                key: MechanicalObligationKey {
                    owner_class: owner,
                    subject: MechanicalSubjectKey::Local {
                        owner: subject.fn_did,
                        mir_local: subject.local.as_u32(),
                        slot_depth: site.slot_depth,
                    },
                    site: site.clone(),
                    family: MechanicalFamily::UnsupportedDeclShape,
                },
                owner_path: owner_of(subject),
                prior_reason: format!("unsupported-decl-shape:{}", subject.decl_shape.key()),
                expected_form: settled.clone(),
                found_form: original.clone(),
                argument_kind: initializer_kind.clone(),
                source_shape: subject.decl_shape.key().to_owned(),
                required_arms: table
                    .arm_requirements
                    .get(&node)
                    .copied()
                    .unwrap_or_default()
                    .render(),
                mechanism: MechanicalMechanism::DeclarationExplicitType,
                composition_parent: None,
                dependency_classes: BTreeSet::new(),
                evidence: MechanicalEvidence {
                    extent: MechanicalExtent::None,
                    retention: MechanicalRetention::None,
                    negative_write: NegativeWriteEvidence::NotApplicable,
                    terminal_contract: TerminalContract::NotApplicable,
                    hoist: HoistSafety::NotApplicable,
                    unsafe_context: None,
                },
                stage: MechanicalStage::Plan,
                state: MechanicalState::Planned,
                terminal_reason: None,
            };
            Some(DeclarationShapeReceiptPlan {
                obligation: MechanicalObligationPlan {
                    planned: event,
                    intended_terminal_state: state,
                    intended_terminal_reason: reason,
                },
                declaration_site: site,
                original_type_form: original,
                settled_emitted_type: settled,
                initializer_kind,
                typed_temporary: pattern.map(|carrier| carrier.temporary.clone()),
                evaluation_order: HoistSafety::NotApplicable,
                owner_class: owner,
            })
        })
        .collect()
}

fn explicit_declaration_receipt(
    declaration: &super::decision::seam::ExplicitDeclarationSite,
    table: &DecisionTable,
    owner_of: &impl Fn(&super::decision::Subject) -> String,
) -> super::mechanical_receipt::DeclarationShapeReceiptPlan {
    use super::mechanical_receipt::*;
    let owner = declaration.owner_class;
    let identity = format!(
        "{}:{}",
        declaration.category,
        declaration.span.map_or_else(
            || "generated".to_owned(),
            |span| format!("{}..{}", span.lo().0, span.hi().0)
        )
    );
    let source = declaration.node.and_then(|node| {
        table
            .entries
            .iter()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
            .map(|(subject, _)| subject)
    });
    let subject = source.map_or_else(
        || MechanicalSubjectKey::Generated {
            owner: declaration.caller,
            key: identity.clone(),
            slot_depth: 0,
        },
        |subject| MechanicalSubjectKey::Local {
            owner: subject.fn_did,
            mir_local: subject.local.as_u32(),
            slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
        },
    );
    let site = CanonicalSiteKey {
        owner: declaration.caller,
        location: CanonicalLocation::Generated {
            defining_class: owner,
            key: identity.clone(),
        },
        callee: None,
        argument_index: None,
        slot_depth: 0,
    };
    let original = if declaration.category == "local" {
        "inferred-call-result"
    } else {
        "input-raw-interface"
    }
    .to_owned();
    let kind = declaration.category.to_owned();
    let temporary =
        matches!(declaration.category, "local-temp" | "return-temp").then_some(identity);
    let event = MechanicalObligationEvent {
        key: MechanicalObligationKey {
            owner_class: owner,
            subject,
            site: site.clone(),
            family: MechanicalFamily::UnsupportedDeclShape,
        },
        owner_path: source.map_or_else(|| format!("class#{}", owner.order_key()), owner_of),
        prior_reason: "declaration-explicit-type".to_owned(),
        expected_form: declaration.emitted_type.clone(),
        found_form: original.clone(),
        argument_kind: kind.clone(),
        source_shape: declaration.category.to_owned(),
        required_arms: declaration.arm.to_owned(),
        mechanism: MechanicalMechanism::DeclarationExplicitType,
        composition_parent: None,
        dependency_classes: BTreeSet::new(),
        evidence: MechanicalEvidence::default(),
        stage: MechanicalStage::Plan,
        state: MechanicalState::Planned,
        terminal_reason: None,
    };
    DeclarationShapeReceiptPlan {
        obligation: MechanicalObligationPlan {
            planned: event,
            intended_terminal_state: MechanicalState::Applied,
            intended_terminal_reason: None,
        },
        declaration_site: site,
        original_type_form: original,
        settled_emitted_type: declaration.emitted_type.clone(),
        initializer_kind: kind,
        typed_temporary: temporary,
        evaluation_order: HoistSafety::NotApplicable,
        owner_class: owner,
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
/// Alias declarations use a compiler-resolved pointee carrier sealed by the
/// declaration decision stage. Only the binding's annotation is replaced;
/// the shared typedef and every subject retaining its raw form stay unchanged.
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
    let mut raw_receiver_sites = rustc_hash::FxHashMap::default();
    let mut outbound_expression_sites = rustc_hash::FxHashMap::default();
    let callee_parameter_input_receipts = callee_parameter_input::InputReceiptMap::capture(
        &table.seams.callee_parameter_inputs,
        &table.seams,
        &span_to_loc,
    );
    for failure in callee_parameter_input_receipts.failures() {
        for owner in [failure.caller, failure.target] {
            preclass_sites.push(ClassSite::dropped(
                owner,
                failure.caller,
                Arm::C,
                "callee-parameter-input-unavailable",
                failure.reason.clone(),
            ));
        }
    }
    let mut a5_receipt_plans = Vec::new();
    let mut slice_construction_receipt_plans = table.retired_slice_constructions.clone();
    let slice_use_receipt_plans = table.slice_use_receipts.clone();
    let option_receipt_plans = table.option_receipts.clone();
    let mut declaration_receipt_plans = declaration_receipts(table, &owner_of);
    let unowned_a5_proof_sites = table
        .seams
        .overlap_proofs
        .iter()
        .filter(|proof| {
            proof.verdict != super::decision::a5_site_proof::A5SiteProofVerdict::Clear
                && proof.proof_site_key.is_none()
        })
        .count();
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

    for declaration in &table.seams.explicit_declarations {
        declaration_receipt_plans.push(explicit_declaration_receipt(declaration, table, &owner_of));
        let bridge = BridgeSitePlan {
            caller: declaration.caller,
            callee: BridgeCalleeId::Local(declaration.owner_class.local_def_id()),
            arm: declaration.arm.to_owned(),
            position: format!("{}:type={}", declaration.category, declaration.emitted_type),
            bridge_kind: "declaration-explicit-type".to_owned(),
            expected_form: "-".to_owned(),
            found_form: "-".to_owned(),
            argument_kind: declaration.category.to_owned(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: None,
        };
        if let (Some(span), Some(replacement)) = (declaration.span, &declaration.replacement) {
            match span_to_loc(span) {
                Ok((file, lo, hi)) => {
                    let subject_id = declaration
                        .node
                        .and_then(|node| {
                            table
                                .entries
                                .iter()
                                .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
                        })
                        .map(|(subject, _)| subject.identity_key(&owner_of(subject)))
                        .unwrap_or_else(|| declaration.category.to_owned());
                    by_file.entry(file).or_default().push(Edit {
                        lo,
                        hi,
                        replacement: replacement.clone(),
                        justification: Justification::SeamAdapter {
                            family: "safe",
                            fabricated: false,
                        },
                        owner_class: Some(declaration.owner_class),
                        owner_path: format!("class#{}", declaration.owner_class.order_key()),
                        bridge: Some(bridge),
                        atom_ids: Vec::new(),
                        subject_id,
                        required_arms: owner_arms
                            .get(&declaration.owner_class)
                            .copied()
                            .unwrap_or_default()
                            .render(),
                        edit_kind: "declaration-explicit-type",
                    });
                }
                Err(reason) => unplaceable.push(Unplaceable {
                    owner_class: declaration.owner_class,
                    bridge,
                    reason,
                    detail: declaration.category.to_owned(),
                    subject: declaration.category.to_owned(),
                }),
            }
            continue;
        }
        let (file, lo, hi, state) = match declaration.span {
            None => (
                "<generated>".to_owned(),
                0,
                0,
                ClassSiteState::ZeroSyntaxReady,
            ),
            Some(span) => match span_to_loc(span) {
                Ok((file, lo, hi)) => (
                    file_key_label(&file),
                    u32::try_from(lo).unwrap_or(u32::MAX),
                    u32::try_from(hi).unwrap_or(u32::MAX),
                    ClassSiteState::ZeroSyntaxReady,
                ),
                Err(reason) => (
                    "<unplaceable>".to_owned(),
                    0,
                    0,
                    ClassSiteState::Dropped(reason.to_owned()),
                ),
            },
        };
        preclass_sites.push(ClassSite {
            atom_ids: Vec::new(),
            key: bridge.materialize(declaration.owner_class, file, lo, hi),
            edit_key: "-".to_owned(),
            state,
            expected_form: bridge.expected_form.clone(),
            found_form: bridge.found_form.clone(),
            argument_kind: bridge.argument_kind.clone(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: bridge.unsafe_context,
        });
    }

    for argument in &table.seams.surface_arguments {
        let bridge = &argument.bridge;
        preclass_sites.push(ClassSite {
            atom_ids: argument.atom_ids.clone(),
            key: bridge.materialize(argument.owner_class, "<generated>".into(), 0, 0),
            edit_key: "-".into(),
            state: ClassSiteState::ZeroSyntaxReady,
            expected_form: bridge.expected_form.clone(),
            found_form: bridge.found_form.clone(),
            argument_kind: bridge.argument_kind.clone(),
            extent: bridge.extent.clone(),
            retention: bridge.retention,
            waiver_id: bridge.waiver_id.clone(),
            unsafe_context: bridge.unsafe_context,
        });
    }
    for failure in table.return_receivers.failures.values() {
        if table
            .seams
            .raw_receivers
            .plans
            .get(&failure.node)
            .is_some_and(|input| input.callee == failure.callee)
        {
            // This actual raw destination has its own required result view;
            // no prospective borrowed-receiver presentation is needed.
            continue;
        }
        let owner = SignatureClassId::of(failure.callee);
        let mut site = ClassSite::zero(
            owner,
            SignatureClassId::of(failure.node.0),
            Arm::C,
            "return-receiver-interface-unavailable",
        );
        site.key.position = format!(
            "receiver:{}:{}",
            failure.node.0.local_def_index.as_u32(),
            failure.node.1.local_id.as_u32()
        );
        site.state =
            ClassSiteState::Dropped(format!("return-receiver-interface:{:?}", failure.kind));
        preclass_sites.push(site);
    }
    for receiver in table.return_receivers.plans.values().filter(|receiver| {
        receiver.coercion == super::decision::return_receiver::ReceiverCoercion::SharedOption
            && super::decision::return_receiver::active_initializer(
                table,
                receiver.node,
                receiver.initializer_hir,
                receiver.initializer_span,
            )
            .is_some()
    }) {
        let owner = SignatureClassId::of(receiver.callee);
        let bridge = BridgeSitePlan {
            caller: receiver.node.0,
            callee: BridgeCalleeId::Local(receiver.callee),
            arm: "glue".into(),
            position: format!(
                "receiver-coercion:{}:{}:lifetime_plan={}",
                receiver.node.0.local_def_index.as_u32(),
                receiver.node.1.local_id.as_u32(),
                receiver.candidate_interface.lifetime_plan_digest
            ),
            bridge_kind: "return-shared-option".into(),
            expected_form: receiver.receiver_form.key().into(),
            found_form: receiver.candidate_interface.form.key().into(),
            argument_kind: "return-call-result".into(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: None,
        };
        match span_to_loc(receiver.initializer_span) {
            Ok((file, lo, hi)) => preclass_sites.push(ClassSite {
                atom_ids: Vec::new(),
                key: bridge.materialize(owner, file_key_label(&file), lo as u32, hi as u32),
                edit_key: "-".into(),
                state: ClassSiteState::EditReady,
                expected_form: bridge.expected_form,
                found_form: bridge.found_form,
                argument_kind: bridge.argument_kind,
                extent: bridge.extent,
                retention: bridge.retention,
                waiver_id: bridge.waiver_id,
                unsafe_context: bridge.unsafe_context,
            }),
            Err(reason) => preclass_sites.push(ClassSite::dropped(
                owner,
                SignatureClassId::of(receiver.node.0),
                Arm::Glue,
                "receiver-coercion-unlocated",
                reason,
            )),
        }
    }
    for input in table.seams.outbound_expressions.plans.values() {
        let owner = input.owner_class();
        let bridge = input.bridge();
        match span_to_loc(input.argument_span) {
            Ok((file, lo, hi)) => {
                let site = ClassSite {
                    atom_ids: Vec::new(),
                    key: bridge.materialize(owner, file_key_label(&file), lo as u32, hi as u32),
                    edit_key: "-".into(),
                    state: ClassSiteState::EditReady,
                    expected_form: bridge.expected_form,
                    found_form: bridge.found_form,
                    argument_kind: bridge.argument_kind,
                    extent: bridge.extent,
                    retention: bridge.retention,
                    waiver_id: bridge.waiver_id,
                    unsafe_context: bridge.unsafe_context,
                };
                outbound_expression_sites.insert(input.key.clone(), site.clone());
                preclass_sites.push(site);
            }
            Err(reason) => preclass_sites.push(ClassSite::dropped(
                owner,
                SignatureClassId::of(input.caller),
                Arm::C,
                "outbound-expression-site-unlocated",
                reason,
            )),
        }
    }
    for unavailable in table.seams.outbound_expressions.unavailable.values() {
        let owner = SignatureClassId::of(unavailable.source_callee);
        let mut site = ClassSite::dropped(
            owner,
            SignatureClassId::of(unavailable.caller),
            Arm::C,
            "outbound-expression-unavailable",
            unavailable.reason.alias_permission_reason().map_or_else(
                || format!("outbound-expression:{:?}", unavailable.reason),
                str::to_owned,
            ),
        );
        site.key.caller = unavailable.caller;
        site.key.callee = unavailable.sink_callee.clone();
        site.key.position = format!(
            "arg{}:expression={}",
            unavailable.key.argument_index,
            unavailable.argument_hir.local_id.as_u32()
        );
        if let Ok((file, lo, hi)) = span_to_loc(unavailable.argument_span) {
            site.key.file = file_key_label(&file);
            site.key.lo = lo as u32;
            site.key.hi = hi as u32;
        }
        preclass_sites.push(site);
    }
    for input in table.seams.raw_receivers.plans.values() {
        let owner = SignatureClassId::of(input.callee);
        let bridge = input.bridge();
        match span_to_loc(input.initializer_span) {
            Ok((file, lo, hi)) => {
                let site = ClassSite {
                    atom_ids: Vec::new(),
                    key: bridge.materialize(owner, file_key_label(&file), lo as u32, hi as u32),
                    edit_key: "-".into(),
                    state: ClassSiteState::EditReady,
                    expected_form: bridge.expected_form,
                    found_form: bridge.found_form,
                    argument_kind: bridge.argument_kind,
                    extent: bridge.extent,
                    retention: bridge.retention,
                    waiver_id: bridge.waiver_id,
                    unsafe_context: bridge.unsafe_context,
                };
                raw_receiver_sites.insert(input.node, site.clone());
                preclass_sites.push(site);
            }
            Err(reason) => preclass_sites.push(ClassSite::dropped(
                owner,
                SignatureClassId::of(input.node.0),
                Arm::C,
                "raw-receiver-site-unlocated",
                reason,
            )),
        }
    }
    for unavailable in table.seams.raw_receivers.unavailable.values() {
        let owner = SignatureClassId::of(unavailable.callee);
        let mut site = ClassSite::dropped(
            owner,
            SignatureClassId::of(unavailable.node.0),
            Arm::C,
            "raw-receiver-result-unavailable",
            format!("raw-receiver-result:{:?}", unavailable.reason),
        );
        site.key.position = format!(
            "raw-receiver:{}:{}",
            unavailable.node.0.local_def_index.as_u32(),
            unavailable.node.1.local_id.as_u32()
        );
        preclass_sites.push(site);
    }
    for failure in &table.seams.surface_argument_failures {
        let mut site = ClassSite::zero(
            failure.owner_class,
            failure.owner_class,
            Arm::Surface,
            "surface-argument-unavailable",
        );
        site.key.position = format!("generated-wrapper-arg{}", failure.parameter_index);
        site.state = ClassSiteState::Dropped(failure.reason.into());
        preclass_sites.push(site);
    }
    for site in &table.seams.zero_bridges {
        let bridge = BridgeSitePlan {
            caller: site.caller,
            callee: BridgeCalleeId::Local(site.owner_class.local_def_id()),
            arm: site.arm.to_owned(),
            position: site.position.clone(),
            bridge_kind: site.bridge_kind.to_owned(),
            expected_form: site.expected_form.to_owned(),
            found_form: site.found_form.to_owned(),
            argument_kind: site.argument_kind.to_owned(),
            extent: BridgeExtentKind::None,
            retention: site.retention,
            waiver_id: site.waiver_id.clone(),
            unsafe_context: site.unsafe_context,
        };
        let (file, lo, hi, state) = match site.span {
            None => (
                "<generated>".to_owned(),
                0,
                0,
                ClassSiteState::ZeroSyntaxReady,
            ),
            Some(span) => match span_to_loc(span) {
                Ok((file, lo, hi)) => (
                    file_key_label(&file),
                    u32::try_from(lo).unwrap_or(u32::MAX),
                    u32::try_from(hi).unwrap_or(u32::MAX),
                    ClassSiteState::ZeroSyntaxReady,
                ),
                Err(reason) => (
                    "<unplaceable>".to_owned(),
                    0,
                    0,
                    ClassSiteState::Dropped(reason.to_owned()),
                ),
            },
        };
        preclass_sites.push(ClassSite {
            atom_ids: Vec::new(),
            key: bridge.materialize(site.owner_class, file, lo, hi),
            edit_key: "-".to_owned(),
            state,
            expected_form: bridge.expected_form.clone(),
            found_form: bridge.found_form.clone(),
            argument_kind: bridge.argument_kind.clone(),
            extent: BridgeExtentKind::None,
            retention: site.retention,
            waiver_id: site.waiver_id.clone(),
            unsafe_context: bridge.unsafe_context,
        });
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
            Ok((file, lo, hi)) => {
                if seam.zero_syntax {
                    preclass_sites.push(terminal_seam_site(seam, &file, lo, hi, None));
                    continue;
                }
                by_file.entry(file).or_default().push(Edit {
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
                        "raw-op-address-observation" => "raw-op-address-observation",
                        _ => "seam-adapter",
                    },
                });
            }
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
    for storage in &table.depth2_npo_storages {
        let owner = SignatureClassId::of(storage.node.0);
        let subject_id = table
            .entries
            .iter()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == storage.node)
            .map(|(subject, _)| subject.identity_key(&owner_of(subject)))
            .unwrap_or_else(|| format!("depth2-storage:{}", storage.node.1.local_id.as_u32()));
        let mut bridge = BridgeSitePlan::local(
            storage.node.0,
            storage.node.0,
            Arm::C.key(),
            format!("storage-init:hir{}", storage.node.1.local_id.as_u32()),
            "depth2-npo-storage",
        );
        bridge.unsafe_context = storage.unsafe_context;
        match span_to_loc(storage.init_span) {
            Ok((file, lo, hi)) => by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: storage.replacement.clone(),
                justification: Justification::SeamAdapter {
                    family: "safe",
                    fabricated: false,
                },
                owner_class: Some(owner),
                owner_path: subject_id.clone(),
                bridge: Some(bridge),
                atom_ids: Vec::new(),
                subject_id,
                required_arms: owner_arms.get(&owner).copied().unwrap_or_default().render(),
                edit_kind: "depth2-npo-storage-init",
            }),
            Err(reason) => unplaceable.push(Unplaceable {
                owner_class: owner,
                bridge,
                reason,
                detail: subject_id.clone(),
                subject: subject_id,
            }),
        }
    }

    for node in &table.option_mut_bindings {
        if table
            .return_receivers
            .plans
            .get(node)
            .is_some_and(|receiver| {
                !table.return_receivers.failures.contains_key(node)
                    && table.seams.explicit_declarations.iter().any(|site| {
                        site.category == "local"
                            && site.node == Some(*node)
                            && site.owner_class == SignatureClassId::of(receiver.callee)
                            && site.emitted_type == receiver.receiver_type()
                    })
            })
        {
            // The callee-owned explicit declaration places type and binding
            // together; a caller-owned edit here would claim the same span.
            continue;
        }
        let Some((subject, decision)) = table
            .entries
            .iter()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == *node)
        else {
            continue;
        };
        match decision {
            Decision::Opt { .. } => {}
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        }
        let owner = SignatureClassId::of(subject.fn_did);
        let Some(name) = &subject.param_name else { continue };
        let bridge = BridgeSitePlan::local(
            subject.fn_did,
            subject.fn_did,
            Arm::Surface.key(),
            format!("option-binding:hir{}", subject.hir_id.local_id.as_u32()),
            "option-mut-binding",
        );
        match span_to_loc(subject.binding_span) {
            Ok((file, lo, hi)) => by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: format!("mut {name}"),
                justification: Justification::SeamAdapter {
                    family: "safe",
                    fabricated: false,
                },
                owner_class: Some(owner),
                owner_path: owner_of(subject),
                bridge: Some(bridge),
                atom_ids: Vec::new(),
                subject_id: subject.identity_key(&owner_of(subject)),
                required_arms: owner_arms.get(&owner).copied().unwrap_or_default().render(),
                edit_kind: "option-mut-binding",
            }),
            Err(reason) => unplaceable.push(Unplaceable {
                owner_class: owner,
                bridge,
                reason,
                detail: "Option binding mutability".to_owned(),
                subject: subject.identity_key(&owner_of(subject)),
            }),
        }
    }
    for receipt in &option_receipt_plans {
        if receipt.obligation.intended_terminal_state
            == super::mechanical_receipt::MechanicalState::HeldNonmechanical
            && option_receipt_requires_changed_form(table, receipt)
            && !matches!(
                receipt.operation.as_str(),
                "excluded-cursor" | "handoff-return" | "handoff-use"
            )
        {
            let subject = table
                .entries
                .iter()
                .find(|(subject, _)| {
                    receipt.obligation.planned.key.subject
                        == super::mechanical_receipt::MechanicalSubjectKey::Local {
                            owner: subject.fn_did,
                            mir_local: subject.local.as_u32(),
                            slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
                        }
                })
                .expect("Option receipt retains its subject")
                .0
                .clone();
            let bridge = BridgeSitePlan::local(
                receipt.owner_class.local_def_id(),
                receipt.owner_class.local_def_id(),
                Arm::Surface.key(),
                receipt.obligation.planned.key.site.receipt_key(),
                "option-presentation",
            )
            .with_forms(
                &receipt.target_form,
                &receipt.source_form,
                &receipt.operation,
            );
            unplaceable.push(Unplaceable {
                owner_class: receipt.owner_class,
                bridge,
                reason: "option-evidence-held",
                detail: format!("{:?}", receipt.obligation.intended_terminal_reason),
                subject: subject.identity_key(&owner_of(&subject)),
            });
        }
    }
    for receipt in &slice_use_receipt_plans {
        if receipt.obligation.intended_terminal_state
            == super::mechanical_receipt::MechanicalState::HeldNonmechanical
            && receipt.obligation.intended_terminal_reason
                != Some(super::mechanical_receipt::MechanicalTerminalReason::Cursor)
        {
            let site = &receipt.obligation.planned.key.site;
            let subject = table
                .entries
                .iter()
                .find(|(subject, _)| {
                    receipt.obligation.planned.key.subject
                        == super::mechanical_receipt::MechanicalSubjectKey::Local {
                            owner: subject.fn_did,
                            mir_local: subject.local.as_u32(),
                            slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
                        }
                })
                .expect("slice-use receipt retains its source subject")
                .0
                .clone();
            let bridge = BridgeSitePlan::local(
                receipt.owner_class.local_def_id(),
                receipt.owner_class.local_def_id(),
                Arm::Surface.key(),
                site.receipt_key(),
                "slice-use-adapter",
            )
            .with_forms(
                &receipt.target_form,
                &receipt.source_form,
                &receipt.obligation.planned.source_shape,
            );
            unplaceable.push(Unplaceable {
                owner_class: receipt.owner_class,
                bridge,
                reason: "slice-use-evidence-held",
                detail: format!("{:?}", receipt.obligation.intended_terminal_reason),
                subject: subject.identity_key(&owner_of(&subject)),
            });
        }
    }

    for construction in &table.slice_constructions {
        use super::mechanical_receipt::{
            CanonicalLocation, CanonicalSiteKey, HoistSafety, MechanicalEvidence, MechanicalFamily,
            MechanicalMechanism, MechanicalObligationEvent, MechanicalObligationKey,
            MechanicalObligationPlan, MechanicalRetention, MechanicalStage, MechanicalState,
            MechanicalSubjectKey, MechanicalTerminalReason, NegativeWriteEvidence,
            SliceConstructionReceiptPlan, TerminalContract,
        };

        let Some((subject, _)) = table
            .entries
            .iter()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == construction.node)
        else {
            continue;
        };
        let owner = SignatureClassId::of(subject.fn_did);
        let subject_id = subject.identity_key(&owner_of(subject));
        let mechanical_subject = MechanicalSubjectKey::Local {
            owner: subject.fn_did,
            mir_local: subject.local.as_u32(),
            slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
        };
        let extent = construction.length.extent();
        let bridge_extent = if extent.is_fallback() {
            BridgeExtentKind::Fallback
        } else {
            BridgeExtentKind::Evidence(construction.length.source.receipt_key())
        };
        let expected_form = if construction.mutable {
            if construction.nullable {
                "option-slice-mut"
            } else {
                "slice-mut"
            }
        } else if construction.nullable {
            "option-slice-shared"
        } else {
            "slice-shared"
        };
        let mut bridge = BridgeSitePlan::local(
            subject.fn_did,
            subject.fn_did,
            Arm::Surface.key(),
            format!("slice-init:hir{}", construction.init_hir.local_id.as_u32()),
            "slice-local-construction",
        )
        .with_extent(bridge_extent)
        .with_forms(expected_form, "raw", construction.initializer_kind);
        bridge.unsafe_context = Some(construction.unsafe_context);

        let located = span_to_loc(construction.init_span);
        let placement_failure = construction
            .hold_reason
            .clone()
            .or_else(|| located.as_ref().err().map(|reason| (*reason).to_owned()));
        if let (Some(replacement), Ok((file, lo, hi))) =
            (construction.replacement.as_ref(), located)
            && placement_failure.is_none()
        {
            by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: replacement.clone(),
                justification: Justification::SeamAdapter {
                    family: "slice-construction",
                    fabricated: extent.is_fallback(),
                },
                owner_class: Some(owner),
                owner_path: owner_of(subject),
                bridge: Some(bridge.clone()),
                atom_ids: Vec::new(),
                subject_id: subject_id.clone(),
                required_arms: owner_arms.get(&owner).copied().unwrap_or_default().render(),
                edit_kind: "slice-local-construction",
            });
        } else {
            unplaceable.push(Unplaceable {
                owner_class: owner,
                bridge: bridge.clone(),
                reason: "slice construction unavailable",
                detail: format!(
                    "{}: {}",
                    subject_id,
                    placement_failure
                        .clone()
                        .unwrap_or_else(|| "no replacement".to_owned())
                ),
                subject: subject_id.clone(),
            });
        }

        let intended_terminal_state = if placement_failure.is_some() {
            MechanicalState::HeldNonmechanical
        } else {
            MechanicalState::Applied
        };
        let intended_terminal_reason = placement_failure.clone().map(|reason| {
            if let Some(detail) = reason.strip_prefix("composition-crossing-unhoistable:") {
                MechanicalTerminalReason::CompositionCrossingUnhoistable(detail.to_owned())
            } else {
                MechanicalTerminalReason::EvidenceMissing(reason)
            }
        });
        let site = CanonicalSiteKey {
            owner: subject.fn_did,
            location: CanonicalLocation::Hir {
                owner: subject.fn_did,
                item_local_id: construction.init_hir.local_id.as_u32(),
            },
            callee: None,
            argument_index: None,
            slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
        };
        let event = MechanicalObligationEvent {
            key: MechanicalObligationKey {
                owner_class: owner,
                subject: mechanical_subject.clone(),
                site,
                family: MechanicalFamily::SliceLocalConstruction,
            },
            owner_path: owner_of(subject),
            prior_reason: "slice-local-construction".to_owned(),
            expected_form: expected_form.to_owned(),
            found_form: "raw".to_owned(),
            argument_kind: "local-initializer".to_owned(),
            source_shape: construction.initializer_kind.to_owned(),
            required_arms: owner_arms.get(&owner).copied().unwrap_or_default().render(),
            mechanism: MechanicalMechanism::SliceConstruction,
            composition_parent: None,
            dependency_classes: BTreeSet::new(),
            evidence: MechanicalEvidence {
                extent: extent.clone(),
                retention: MechanicalRetention::None,
                negative_write: NegativeWriteEvidence::NotApplicable,
                terminal_contract: TerminalContract::NotApplicable,
                hoist: HoistSafety::NotApplicable,
                unsafe_context: Some(construction.unsafe_context),
            },
            stage: MechanicalStage::Plan,
            state: MechanicalState::Planned,
            terminal_reason: None,
        };
        slice_construction_receipt_plans.push(SliceConstructionReceiptPlan {
            obligation: MechanicalObligationPlan {
                planned: event,
                intended_terminal_state,
                intended_terminal_reason,
            },
            allocation_result: mechanical_subject,
            element_type: construction.element_type.clone(),
            mutable: construction.mutable,
            nullable: construction.nullable,
            length_expression: construction.length.expression.clone(),
            length_provenance: construction.length.provenance_receipt(),
            extent,
            owner_class: owner,
        });
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
        let typed_pattern = table
            .declaration_patterns
            .contains_key(&(subject.fn_did, subject.hir_id));
        let typed_receiver = table
            .return_receivers
            .plans
            .get(&(subject.fn_did, subject.hir_id))
            .is_some_and(|receiver| {
                !table.return_receivers.failures.contains_key(&receiver.node)
                    && super::decision::seam::form_of(decision) == receiver.receiver_form
                    && table.seams.explicit_declarations.iter().any(|site| {
                        site.category == "local"
                            && site.node == Some(receiver.node)
                            && site.owner_class == SignatureClassId::of(receiver.callee)
                            && site.emitted_type == receiver.receiver_type()
                    })
            });
        let (ty_file, declaration_edit) = if inferred_box || typed_pattern || typed_receiver {
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
        } else if let Some(resolved) = table
            .declaration_pointees
            .get(&(subject.fn_did, subject.hir_id))
        {
            let located = subject
                .ty_span
                .ok_or("alias declaration has no type span")
                .and_then(&span_to_loc);
            let (file, lo, hi) = match located {
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
            let Some(replacement) = super::decision::declaration::emitted_type(
                decision,
                &resolved.pointee,
                declaration_lifetime(table, subject),
            ) else {
                unplaceable.push(Unplaceable {
                    owner_class: SignatureClassId::of(subject.fn_did),
                    bridge: surface_bridge(),
                    reason: "alias declaration has no licensed borrowed form",
                    detail: attribution(),
                    subject: identity(),
                });
                continue;
            };
            (file, Some((lo, hi, replacement)))
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
            let raw_op = use_edit.bridge_kind.starts_with("raw-op-");
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
                        if raw_op {
                            Arm::Addr.key()
                        } else {
                            Arm::Surface.key()
                        },
                        if raw_op {
                            format!("{}@{}..{}", subject_id, lo, hi)
                        } else {
                            subject_id.clone()
                        },
                        use_edit.bridge_kind,
                    )),
                    atom_ids: subject_atom_ids.clone(),
                    subject_id: subject_id.clone(),
                    required_arms: subject_arms.clone(),
                    edit_kind: use_edit.bridge_kind,
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
            atom_ids: Vec::new(),
            key: site
                .bridge
                .materialize(site.owner_class, "<unplaceable>".to_owned(), 0, 0),
            edit_key: "-".to_owned(),
            state: ClassSiteState::Dropped(site.reason.to_owned()),
            expected_form: site.bridge.expected_form.clone(),
            found_form: site.bridge.found_form.clone(),
            argument_kind: site.bridge.argument_kind.clone(),
            extent: site.bridge.extent.clone(),
            retention: site.bridge.retention,
            waiver_id: site.bridge.waiver_id.clone(),
            unsafe_context: site.bridge.unsafe_context,
        }
    }));
    if let Some(exposure) = table.exposure.as_ref() {
        for seed in exposure.static_fnptr_seeds() {
            if !matches!(
                exposure.plan(seed.function),
                super::decision::exposure::ExposureSurfacePlan::PositiveSeedShim
                    | super::decision::exposure::ExposureSurfacePlan::FnPtrRawWrapper
            ) {
                continue;
            }
            let owner = SignatureClassId::of(seed.function);
            let bridge = BridgeSitePlan::local(
                seed.owner,
                seed.function,
                Arm::Surface.key(),
                format!("static:{}", seed.location_key()),
                "surface-static-fnptr-wrapper",
            );
            let site = match span_to_loc(seed.span) {
                Ok((file, lo, hi)) => ClassSite {
                    atom_ids: Vec::new(),
                    key: bridge.materialize(
                        owner,
                        file_key_label(&file),
                        u32::try_from(lo).unwrap_or(u32::MAX),
                        u32::try_from(hi).unwrap_or(u32::MAX),
                    ),
                    edit_key: "-".to_owned(),
                    state: ClassSiteState::ZeroSyntaxReady,
                    expected_form: bridge.expected_form.clone(),
                    found_form: bridge.found_form.clone(),
                    argument_kind: bridge.argument_kind.clone(),
                    extent: BridgeExtentKind::None,
                    retention: BridgeRetentionTier::None,
                    waiver_id: None,
                    unsafe_context: None,
                },
                Err(reason) => ClassSite {
                    atom_ids: Vec::new(),
                    key: bridge.materialize(owner, "<unplaceable>".to_owned(), 0, 0),
                    edit_key: "-".to_owned(),
                    state: ClassSiteState::Dropped(reason.to_owned()),
                    expected_form: bridge.expected_form.clone(),
                    found_form: bridge.found_form.clone(),
                    argument_kind: bridge.argument_kind.clone(),
                    extent: BridgeExtentKind::None,
                    retention: BridgeRetentionTier::None,
                    waiver_id: None,
                    unsafe_context: None,
                },
            };
            preclass_sites.push(site);
        }
    }
    for proof in &table.seams.overlap_proofs {
        let owner = SignatureClassId::of(proof.callee);
        let resolution = a5_proof_resolution(&proof.fallback);
        if let Some(proof_site_key) = proof.proof_site_key
            && let Some((subject, _)) = table.entries.iter().find(|(subject, _)| {
                subject.fn_did == proof.callee
                    && matches!(
                        subject.kind,
                        super::decision::SubjectKind::Param { hir_index }
                            if hir_index == proof.index
                    )
            })
        {
            use super::mechanical_receipt::{
                A5ProofSiteReceiptPlan, CanonicalCallee, CanonicalLocation, CanonicalSiteKey,
                MechanicalEvidence, MechanicalFamily, MechanicalMechanism,
                MechanicalObligationEvent, MechanicalObligationKey, MechanicalObligationPlan,
                MechanicalRetention, MechanicalStage, MechanicalState, MechanicalSubjectKey,
                MechanicalTerminalReason, NegativeWriteEvidence,
            };

            let site = CanonicalSiteKey {
                owner: proof_site_key.caller,
                location: CanonicalLocation::Mir {
                    basic_block: proof_site_key.location.block,
                    statement_index: u32::try_from(proof_site_key.location.statement_index)
                        .unwrap_or(u32::MAX),
                    terminator: true,
                },
                callee: Some(CanonicalCallee::Local(proof_site_key.callee)),
                argument_index: Some(
                    u32::try_from(proof_site_key.argument_index).unwrap_or(u32::MAX),
                ),
                slot_depth: u32::try_from(proof_site_key.slot_depth).unwrap_or(u32::MAX),
            };
            let (intended_terminal_state, intended_terminal_reason, retention, negative_write) =
                match &proof.fallback {
                    super::decision::seam::A5ProofSiteFallback::T2RawView {
                        negative_write,
                        ..
                    } => (
                        MechanicalState::Applied,
                        None,
                        MechanicalRetention::T2 {
                            waiver_id: super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned(),
                        },
                        match negative_write {
                            Some(super::decision::raw_boundary::NegativeWriteEvidence::FosterImmutable) => {
                                NegativeWriteEvidence::FosterImmutable
                            }
                            Some(super::decision::raw_boundary::NegativeWriteEvidence::LibcReadOnly) => {
                                NegativeWriteEvidence::LibcReadOnly("local-a5".to_owned())
                            }
                            None => NegativeWriteEvidence::NotApplicable,
                        },
                    ),
                    super::decision::seam::A5ProofSiteFallback::Held { reason }
                        if reason.strip_prefix("a5-fallback-unrenderable:").unwrap_or(reason)
                            == super::decision::seam::SeamBlock::A5NegativeWriteAbsent.key() =>
                    {
                        (
                            MechanicalState::HeldNonmechanical,
                            Some(MechanicalTerminalReason::RbNegativeWriteAbsent),
                            MechanicalRetention::None,
                            NegativeWriteEvidence::Missing,
                        )
                    }
                    super::decision::seam::A5ProofSiteFallback::Held { reason }
                        if reason.strip_prefix("a5-fallback-unrenderable:").unwrap_or(reason)
                            == super::decision::seam::SeamBlock::PositiveRetention.key() =>
                    {
                        (
                            MechanicalState::HeldNonmechanical,
                            Some(MechanicalTerminalReason::PositiveRetention),
                            MechanicalRetention::PositiveRetention,
                            NegativeWriteEvidence::NotApplicable,
                        )
                    }
                    super::decision::seam::A5ProofSiteFallback::Held { reason } => (
                        MechanicalState::Reclassified,
                        Some(MechanicalTerminalReason::EvidenceMissing(reason.clone())),
                        MechanicalRetention::None,
                        NegativeWriteEvidence::NotApplicable,
                    ),
                    super::decision::seam::A5ProofSiteFallback::Clear
                    | super::decision::seam::A5ProofSiteFallback::Primary => continue,
                };
            let template = match &proof.fallback {
                super::decision::seam::A5ProofSiteFallback::T2RawView { template, .. } => {
                    template.clone()
                }
                _ => "-".to_owned(),
            };
            let mechanism = if matches!(
                &negative_write,
                NegativeWriteEvidence::FosterImmutable
                    | NegativeWriteEvidence::LibcReadOnly(_)
                    | NegativeWriteEvidence::Missing
                    | NegativeWriteEvidence::Writes
            ) {
                MechanicalMechanism::SharedRefToMutRaw
            } else {
                MechanicalMechanism::A5RawView
            };
            let event = MechanicalObligationEvent {
                key: MechanicalObligationKey {
                    owner_class: owner,
                    subject: MechanicalSubjectKey::Local {
                        owner: subject.fn_did,
                        mir_local: subject.local.as_u32(),
                        slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
                    },
                    site: site.clone(),
                    family: MechanicalFamily::A5ProofSiteFallback,
                },
                owner_path: owner_of(subject),
                prior_reason: format!("a5-site-proof-blocked:{}", proof.reason),
                expected_form: proof.expected_form.key().to_owned(),
                found_form: proof.found_form.key().to_owned(),
                argument_kind: proof.argument_shape.to_owned(),
                source_shape: proof.found_form.key().to_owned(),
                required_arms: Arm::Pair.key().to_owned(),
                mechanism,
                composition_parent: Some(format!(
                    "call:{}:{}",
                    proof_site_key.location.block, proof_site_key.location.statement_index
                )),
                dependency_classes: table
                    .seams
                    .interface_dependencies
                    .iter()
                    .filter_map(|(dependent, dependency)| {
                        (*dependent == owner).then_some(*dependency)
                    })
                    .collect(),
                evidence: MechanicalEvidence {
                    extent: super::mechanical_receipt::MechanicalExtent::None,
                    retention: retention.clone(),
                    negative_write,
                    terminal_contract: super::mechanical_receipt::TerminalContract::NotApplicable,
                    hoist: super::mechanical_receipt::HoistSafety::Place,
                    unsafe_context: None,
                },
                stage: MechanicalStage::Plan,
                state: MechanicalState::Planned,
                terminal_reason: None,
            };
            a5_receipt_plans.push(A5ProofSiteReceiptPlan {
                obligation: MechanicalObligationPlan {
                    planned: event,
                    intended_terminal_state,
                    intended_terminal_reason,
                },
                proof_site_key: site,
                verdict: proof.verdict.key().to_owned(),
                argument_shape: proof.argument_shape.to_owned(),
                settled_form: proof.found_form.key().to_owned(),
                raw_view_template: template,
                retention,
                owner_class: owner,
            });
        }
        let bridge = BridgeSitePlan::local(
            proof.caller,
            proof.callee,
            Arm::Pair.key(),
            format!("arg{}", proof.index),
            resolution.kind,
        );
        let (file, lo, hi, state) = match span_to_loc(proof.span) {
            Ok((file, lo, hi)) => (
                file_key_label(&file),
                u32::try_from(lo).unwrap_or(u32::MAX),
                u32::try_from(hi).unwrap_or(u32::MAX),
                resolution.state,
            ),
            Err(reason) => (
                "<unplaceable>".to_owned(),
                0,
                0,
                ClassSiteState::Dropped(reason.to_owned()),
            ),
        };
        preclass_sites.push(ClassSite {
            atom_ids: Vec::new(),
            key: bridge.materialize(owner, file, lo, hi),
            edit_key: "-".to_owned(),
            state,
            expected_form: proof.expected_form.key().to_owned(),
            found_form: proof.found_form.key().to_owned(),
            argument_kind: proof.argument_shape.to_owned(),
            extent: BridgeExtentKind::None,
            retention: resolution.retention,
            waiver_id: resolution.waiver_id,
            unsafe_context: None,
        });
    }
    for blocked in &table.seams.blocked {
        let arm = if blocked.source_shape == "return-seam" {
            Arm::Glue
        } else if blocked.block == super::decision::seam::SeamBlock::SiteOverlap {
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
            atom_ids: Vec::new(),
            key: bridge.materialize(SignatureClassId::of(blocked.callee), file, lo, hi),
            edit_key: "-".to_owned(),
            state: ClassSiteState::Dropped(blocked.block.key().to_owned()),
            expected_form: blocked.expected.map_or("-", |form| form.key()).to_owned(),
            found_form: blocked.found.map_or("-", |form| form.key()).to_owned(),
            argument_kind: blocked.source_shape.to_owned(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: None,
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
            atom_ids: Vec::new(),
            key: bridge.materialize(blocked.owner_class, file, lo, hi),
            edit_key: "-".to_owned(),
            state: ClassSiteState::Dropped(blocked.block.key().to_owned()),
            expected_form: blocked.expected.key().to_owned(),
            found_form: blocked.found.map_or("-", |form| form.key()).to_owned(),
            argument_kind: blocked.source_shape.to_owned(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: None,
        });
    }
    for blocked in &table.seams.raw_boundary_blocked {
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
            atom_ids: Vec::new(),
            key: blocked
                .bridge
                .materialize(blocked.owner_class, file, lo, hi),
            edit_key: "-".to_owned(),
            state: ClassSiteState::Dropped(blocked.reason.clone()),
            expected_form: blocked.bridge.expected_form.clone(),
            found_form: blocked.bridge.found_form.clone(),
            argument_kind: blocked.bridge.argument_kind.clone(),
            extent: blocked.bridge.extent.clone(),
            retention: blocked.bridge.retention,
            waiver_id: blocked.bridge.waiver_id.clone(),
            unsafe_context: blocked.bridge.unsafe_context,
        });
    }
    for pair in &table.seams.pair_sites {
        use super::decision::co_conversion::{PairRole, PairTier};
        if pair.role == PairRole::RawView {
            continue;
        }
        let owner = SignatureClassId::of(pair.callee);
        let bridge = BridgeSitePlan::local(
            pair.caller,
            pair.callee,
            Arm::Pair.key(),
            format!("arg{}:{}", pair.argument_index, pair.reason),
            match pair.role {
                PairRole::Clear => "pair-a5-clear",
                PairRole::Primary => "pair-safe-primary",
                PairRole::Blocked => "pair-blocked",
                PairRole::RawView => unreachable!(),
            },
        );
        let (file, lo, hi, state) = match span_to_loc(pair.span) {
            Ok((file, lo, hi)) => (
                file_key_label(&file),
                u32::try_from(lo).unwrap_or(u32::MAX),
                u32::try_from(hi).unwrap_or(u32::MAX),
                if pair.role == PairRole::Blocked {
                    ClassSiteState::Dropped(pair.reason.clone())
                } else {
                    ClassSiteState::ZeroSyntaxReady
                },
            ),
            Err(reason) => (
                "<unplaceable>".to_owned(),
                0,
                0,
                ClassSiteState::Dropped(reason.to_owned()),
            ),
        };
        let mut site = ClassSite {
            atom_ids: Vec::new(),
            key: bridge.materialize(owner, file, lo, hi),
            edit_key: "-".to_owned(),
            state,
            expected_form: "safe-parameter".to_owned(),
            found_form: "pair-site".to_owned(),
            argument_kind: pair.source_shape.to_owned(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
            unsafe_context: None,
        };
        site.retention = match pair.tier {
            PairTier::T2 => BridgeRetentionTier::T2,
            PairTier::None | PairTier::Blocked => BridgeRetentionTier::None,
        };
        site.waiver_id = (pair.tier == PairTier::T2)
            .then(|| super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned());
        preclass_sites.push(site);
    }

    let mut attribution_intervals = table
        .seams
        .edits
        .iter()
        .filter_map(|edit| {
            let (file, lo, hi) = span_to_loc(edit.call_span).ok()?;
            Some(ClassAttributionInterval {
                owner_class: edit.owner_class,
                owner_path: edit.owner_fn.clone(),
                file,
                lo,
                hi,
                kind: "seam-site",
            })
        })
        .collect::<Vec<_>>();
    if let Some(exposure) = table.exposure.as_ref() {
        attribution_intervals.extend(exposure.static_fnptr_seeds().iter().filter_map(|seed| {
            if !matches!(
                exposure.plan(seed.function),
                super::decision::exposure::ExposureSurfacePlan::PositiveSeedShim
                    | super::decision::exposure::ExposureSurfacePlan::FnPtrRawWrapper
            ) {
                return None;
            }
            let (file, lo, hi) = span_to_loc(seed.span).ok()?;
            let owner_path = table
                .entries
                .iter()
                .find(|(subject, _)| subject.fn_did == seed.function)
                .map(|(subject, _)| owner_of(subject))
                .unwrap_or_else(|| format!("local-def-{}", seed.function.local_def_index.as_u32()));
            Some(ClassAttributionInterval {
                owner_class: SignatureClassId::of(seed.function),
                owner_path,
                file,
                lo,
                hi,
                kind: "static-fnptr-site",
            })
        }));
    }
    attribution_intervals.extend(table.seams.interface_inventory.iter().filter_map(|site| {
        let (file, lo, hi) = span_to_loc(site.call_span).ok()?;
        Some(ClassAttributionInterval {
            owner_class: site.key.callee,
            owner_path: table
                .entries
                .iter()
                .find(|(subject, _)| subject.fn_did == site.key.callee.local_def_id())
                .map(|(subject, _)| owner_of(subject))
                .unwrap_or_else(|| format!("local-def-{}", site.key.callee.order_key())),
            file,
            lo,
            hi,
            kind: "interface-inventory-site",
        })
    }));
    attribution_intervals.sort();
    attribution_intervals.dedup();

    let receiver_input_receipts = receiver_input::ReceiverReceiptMap::capture(
        &table.seams.receiver_inputs,
        table,
        &preclass_sites,
        &by_file,
        &span_to_loc,
    );
    let outbound_return_plans = outbound_return::capture(
        table,
        &table.seams.receiver_inputs,
        &receiver_input_receipts,
        &table.seams.raw_receivers,
        &raw_receiver_sites,
        &|owner| {
            table
                .entries
                .iter()
                .find(|(subject, _)| subject.fn_did == owner)
                .map(|(subject, _)| owner_of(subject))
        },
    );

    let native_return_plans = native_return::capture(table, &span_to_loc, &|owner| {
        table
            .entries
            .iter()
            .find(|(subject, _)| subject.fn_did == owner)
            .map(|(subject, _)| owner_of(subject))
    });

    let outbound_expression_plans = outbound_expression::capture(
        table,
        &table.seams.outbound_expressions,
        &outbound_expression_sites,
        &|owner| {
            table
                .entries
                .iter()
                .find(|(subject, _)| subject.fn_did == owner)
                .map(|(subject, _)| owner_of(subject))
        },
    );

    Plan {
        native_return_plans,
        outbound_expression_plans,
        outbound_expression_sites,
        raw_receiver_sites,
        outbound_return_plans,
        receiver_input_receipts,
        callee_parameter_input_receipts,
        sibling_receipt_plans: sibling_overlap::plans(table, &span_to_loc),
        by_file,
        unplaceable,
        // Both filled by the caller; `plan` has no `TyCtxt`, so it can ask
        // neither which file is the crate root nor the parser for an item.
        root_file: None,
        len_const_item: None,
        preclass_sites,
        class_finalization: ClassFinalization::default(),
        attribution_intervals,
        a5_receipt_plans,
        slice_construction_receipt_plans,
        slice_use_receipt_plans,
        option_receipt_plans,
        declaration_receipt_plans,
        unowned_a5_proof_sites,
        terminal_call_plans: super::decision::seam::TerminalCallPlans::candidates(&table.seams),
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
            sibling_overlap_inventory: Default::default(),
            declaration_pointees: Default::default(),
            declaration_patterns: Default::default(),
            input_interfaces: Default::default(),
            arm_requirements: Default::default(),
            exposure: None,
            seams: Default::default(),
            c9_marks: Vec::new(),
            lifetime_plan: Default::default(),
            return_interfaces: Default::default(),
            return_receivers: Default::default(),
            depth2_npo_storages: Vec::new(),
            slice_constructions: Vec::new(),
            retired_slice_constructions: Vec::new(),
            slice_use_receipts: Vec::new(),
            option_receipts: Vec::new(),
            option_value_initializers: Vec::new(),
            option_mut_bindings: rustc_hash::FxHashSet::default(),
            option_composed_uses: Vec::new(),
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
            sibling_overlap_inventory: Default::default(),
            declaration_pointees: Default::default(),
            declaration_patterns: Default::default(),
            input_interfaces: Default::default(),
            arm_requirements: Default::default(),
            exposure: None,
            seams: Default::default(),
            c9_marks: Vec::new(),
            lifetime_plan: Default::default(),
            return_interfaces: Default::default(),
            return_receivers: Default::default(),
            depth2_npo_storages: Vec::new(),
            slice_constructions: Vec::new(),
            retired_slice_constructions: Vec::new(),
            slice_use_receipts: Vec::new(),
            option_receipts: Vec::new(),
            option_value_initializers: Vec::new(),
            option_mut_bindings: rustc_hash::FxHashSet::default(),
            option_composed_uses: Vec::new(),
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
    fn r231_selected_pair_atom_drops_only_its_physical_bridge_receipt() {
        with_classes(1, |ids| {
            let owner = ids[0];
            let file = FileKey::Virtual("main.rs".into());
            let mut input = ClassInput::new(owner, RequiredArmSet::default());
            let mut edits = Vec::new();
            for (lo, kind, atoms) in [
                (10, "pair-t2-raw-view", vec!["selected-pair".to_owned()]),
                (30, "a5-site-proof-t2-fallback", Vec::new()),
            ] {
                let mut site =
                    ClassSite::edit(owner, owner, Arm::Pair, "main.rs", lo, lo + 5, kind);
                let edit = Edit {
                    lo: lo as usize,
                    hi: (lo + 5) as usize,
                    replacement: "carrier".into(),
                    justification: Justification::A5RawView,
                    owner_class: Some(owner),
                    owner_path: "fixture".into(),
                    bridge: Some(BridgeSitePlan::local(
                        owner.local_def_id(),
                        owner.local_def_id(),
                        "pair",
                        "arg1",
                        kind,
                    )),
                    atom_ids: atoms,
                    subject_id: "fixture-subject".into(),
                    required_arms: "pair".into(),
                    edit_kind: kind,
                };
                site.edit_key = physical_edit_key(&file, &edit).unwrap();
                input.sites.push(site);
                edits.push(edit);
            }
            let plan = Plan {
                by_file: BTreeMap::from([(file, edits)]),
                class_finalization: finalize_class_inputs(vec![input]),
                ..Default::default()
            };
            let events = plan.bridge_events_with_atoms(
                &BTreeSet::new(),
                &BTreeSet::from(["selected-pair".into()]),
            );
            let terminal = events
                .iter()
                .filter(|event| {
                    event.stage == super::super::bridge_receipt::BridgeReceiptStage::Terminal
                })
                .collect::<Vec<_>>();
            assert_eq!(terminal.len(), 2);
            assert!(
                terminal
                    .iter()
                    .any(|event| event.site.bridge_kind == "pair-t2-raw-view"
                        && event.state
                            == super::super::bridge_receipt::BridgeReceiptState::Dropped)
            );
            assert!(terminal.iter().any(|event| event.site.bridge_kind
                == "a5-site-proof-t2-fallback"
                && event.state == super::super::bridge_receipt::BridgeReceiptState::Applied));
        });
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

    /// D2-W1 — the heman/kazmath failure shape: two edits owned by one
    /// signature class overlap before application.  The finalizer must hold
    /// the class rather than let either interval reach the flat splicer.
    #[test]
    fn d2_w1_intra_class_interval_overlap_holds_before_apply() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(1, |ids| {
            let owner = ids[0];
            let input = ClassInput::new(owner, arms(&[Arm::Surface, Arm::C]))
                .with_site(ClassSite::edit(
                    owner,
                    owner,
                    Arm::Surface,
                    "kazmath.rs",
                    42240,
                    42260,
                    "outer-signature-edit",
                ))
                .with_site(ClassSite::edit(
                    owner,
                    owner,
                    Arm::C,
                    "kazmath.rs",
                    42252,
                    42255,
                    "nested-call-edit",
                ));
            let finalized = finalize_class_inputs(vec![input]);
            let class = &finalized.classes[&owner];
            assert!(!class.is_ready());
            assert_eq!(finalized.applied_site_count(), 0);
            assert!(
                class
                    .hold_reasons()
                    .iter()
                    .any(|reason| reason == "intra-class-interval-overlap"),
                "missing typed intra-class hold: {:?}",
                class.hold_reasons()
            );
        });
    }

    #[test]
    fn r231_logical_position_and_call_share_one_physical_edit() {
        with_classes(1, |ids| {
            let owner = ids[0];
            let outer = ClassSite::edit(
                owner,
                owner,
                Arm::Pair,
                "main.rs",
                10,
                40,
                "a5-site-proof-t2-fallback",
            );
            let mut position = ClassSite::edit(
                owner,
                owner,
                Arm::Pair,
                "main.rs",
                30,
                33,
                "a5-site-proof-t2-fallback",
            );
            position.edit_key.clone_from(&outer.edit_key);
            let result = finalize_class_inputs(vec![
                ClassInput::new(owner, arms(&[Arm::Pair]))
                    .with_site(outer)
                    .with_site(position),
            ]);
            assert!(result.classes[&owner].is_ready(), "{result:#?}");
        });
    }

    #[test]
    fn r231_shared_key_does_not_license_crossing_or_other_owners() {
        with_classes(2, |ids| {
            let mut left =
                ClassSite::edit(ids[0], ids[0], Arm::Pair, "main.rs", 10, 30, "physical-a");
            let mut right =
                ClassSite::edit(ids[0], ids[0], Arm::Pair, "main.rs", 20, 40, "physical-b");
            right.edit_key.clone_from(&left.edit_key);
            assert!(intervals_overlap(&left, &right));
            left.key.hi = 50;
            right.key.owner_class = ids[1];
            assert!(intervals_overlap(&left, &right));
        });
    }

    /// D10-W1 — lil's 204/260 shape.  A call-level C bridge owns an outer AST
    /// node while a subject-use rewrite owns a strict descendant.  The AST
    /// pipeline applies the descendant first and then moves that rewritten
    /// subtree into the bridge, so finalization must not classify the nesting
    /// as a flat-splice collision.  A true crossing remains held.
    #[test]
    fn d10_w1_nested_c_bridge_composes_but_crossing_intervals_hold() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(4, |ids| {
            let outer = ClassInput::new(ids[0], arms(&[Arm::C])).with_site(ClassSite::edit(
                ids[0],
                ids[0],
                Arm::C,
                "lil.rs",
                200,
                260,
                "c-raw-option-slice",
            ));
            let inner = ClassInput::new(ids[1], arms(&[Arm::Surface])).with_site(ClassSite::edit(
                ids[1],
                ids[1],
                Arm::Surface,
                "lil.rs",
                220,
                230,
                "subject-use",
            ));
            let crossing_outer =
                ClassInput::new(ids[2], arms(&[Arm::Glue])).with_site(ClassSite::edit(
                    ids[2],
                    ids[2],
                    Arm::Glue,
                    "lil.rs",
                    300,
                    330,
                    "nullable-required-unwrap",
                ));
            let crossing_inner =
                ClassInput::new(ids[3], arms(&[Arm::Surface])).with_site(ClassSite::edit(
                    ids[3],
                    ids[3],
                    Arm::Surface,
                    "lil.rs",
                    320,
                    340,
                    "subject-use",
                ));
            let finalized =
                finalize_class_inputs(vec![outer, inner, crossing_outer, crossing_inner]);
            assert!(
                finalized.classes[&ids[0]].is_ready(),
                "strict inner-first composition was held: {:?}",
                finalized.classes[&ids[0]].hold_reasons()
            );
            assert!(finalized.classes[&ids[1]].is_ready());
            assert!(finalized.classes[&ids[0]].depends_on.contains(&ids[1]));
            assert!(
                !finalized.classes[&ids[2]].is_ready() && !finalized.classes[&ids[3]].is_ready(),
                "a true crossing reached application"
            );
        });
    }

    /// D11-W1 — buffer's measured interval shape.  PAIR owns the outer call
    /// and first walks its children, so the C bridge on the safe-primary
    /// operand is applied before PAIR substitutes the peer raw-view temp.  The
    /// strict nesting is one structural composition; a true PAIR/C crossing is
    /// still a collision.
    #[test]
    fn d11_w1_pair_outer_composes_the_c_primary_operand_only() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(2, |ids| {
            let composed = ClassInput::new(ids[0], arms(&[Arm::C, Arm::Pair]))
                .with_site(ClassSite::edit(
                    ids[0],
                    ids[0],
                    Arm::C,
                    "buffer.rs",
                    21017,
                    21020,
                    "c-raw-reborrow-mut",
                ))
                .with_site(ClassSite::edit(
                    ids[0],
                    ids[0],
                    Arm::Pair,
                    "buffer.rs",
                    21003,
                    21093,
                    "pair-t2-raw-view",
                ));
            let crossing = ClassInput::new(ids[1], arms(&[Arm::C, Arm::Pair]))
                .with_site(ClassSite::edit(
                    ids[1],
                    ids[1],
                    Arm::C,
                    "buffer.rs",
                    300,
                    340,
                    "c-raw-reborrow-mut",
                ))
                .with_site(ClassSite::edit(
                    ids[1],
                    ids[1],
                    Arm::Pair,
                    "buffer.rs",
                    320,
                    360,
                    "pair-t2-raw-view",
                ));
            let finalized = finalize_class_inputs(vec![composed, crossing]);
            assert!(
                finalized.classes[&ids[0]].is_ready(),
                "PAIR/C nesting was held: {:?}",
                finalized.classes[&ids[0]].hold_reasons()
            );
            assert!(!finalized.classes[&ids[1]].is_ready());
        });
    }

    /// D14-W1 — a non-clear A5 proof is not itself a hold once PAIR has
    /// selected a receipted T2 raw view. R231 requires an actual linked
    /// carrier before this logical receipt is ready; the waiver remains exact.
    #[test]
    fn d14_w1_a5_block_falls_through_to_the_pair_t2_receipt() {
        use crate::bo_rewriter::decision::seam::A5ProofSiteFallback;
        let resolved = a5_proof_resolution(&A5ProofSiteFallback::T2RawView {
            template: "slice-mut-to-raw-mut->from-raw-parts-mut".to_owned(),
            negative_write: None,
        });
        assert_eq!(resolved.kind, "a5-site-proof-t2-fallback");
        assert_eq!(
            resolved.state,
            ClassSiteState::Dropped("a5-fallback-unrenderable:carrier-not-materialized".into())
        );
        assert_eq!(resolved.retention, BridgeRetentionTier::T2);
        assert_eq!(
            resolved.waiver_id.as_deref(),
            Some(super::super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
        );

        let blocked = a5_proof_resolution(&A5ProofSiteFallback::Held {
            reason: "pair-positive-retention".to_owned(),
        });
        assert_eq!(blocked.kind, "a5-site-proof-reclassified");
        assert!(matches!(blocked.state, ClassSiteState::Dropped(_)));
        assert_eq!(blocked.retention, BridgeRetentionTier::None);
        assert!(blocked.waiver_id.is_none());
    }

    #[test]
    fn cls_w4_dependency_order_is_dependents_first_not_local_index_order() {
        with_classes(3, |ids| {
            let mut dependent = ClassInput::new(ids[2], RequiredArmSet::default());
            dependent.depends_on.push(ids[0]);
            let finalized = finalize_class_inputs(vec![
                ClassInput::new(ids[0], RequiredArmSet::default()),
                ClassInput::new(ids[1], RequiredArmSet::default()),
                dependent,
            ]);
            let groups = dependency_scc_order(&finalized.classes);
            let flattened = groups.into_iter().flatten().collect::<Vec<_>>();
            let dependent_at = flattened.iter().position(|id| *id == ids[2]).unwrap();
            let dependency_at = flattened.iter().position(|id| *id == ids[0]).unwrap();
            assert!(dependent_at < dependency_at, "dependency order was lexical");
        });
    }

    /// L07 (§39 addendum 272, R272-3) — the five kind pairs, each through the
    /// three states the ruling requires.
    ///
    /// **State 1, both applied.** The containment is a composition, not a
    /// collision: both classes stay ready and the outer records the inner as a
    /// dependency.
    ///
    /// **State 2, inner reverted.** `dependent_closure` carries the revert
    /// UPWARD along that dependency, so the outer goes with it. This is the
    /// property that makes cross-class composition safe against revert
    /// atomicity: the inner can never be withdrawn while the outer that wraps
    /// it stays applied.
    ///
    /// **State 3, outer reverted with the inner applied.** The closure is
    /// directional, so the inner survives — and it re-renders correctly
    /// because `round_files` emits through
    /// `ast_transform::ast_emitted_files_from`, an AST re-render from the
    /// ready-class set, not a text splice. There is no half-composed text
    /// region to leave behind: the inner rewrite applies to its own AST node
    /// and the outer simply does not wrap it. (`apply::apply`'s
    /// overlapping-edit rollback belongs to the span layer, which is not the
    /// emission path here.)
    #[test]
    fn l07_five_kind_pairs_compose_and_revert_inner_first() {
        use crate::bo_rewriter::decision::Arm;
        const PAIRS: [(Arm, &str, Arm, &str); 5] = [
            (Arm::Pair, "pair-t2-raw-view", Arm::C, "typed-raw-temporary"),
            (
                Arm::Pair,
                "pair-copy-snapshot",
                Arm::C,
                "typed-raw-temporary",
            ),
            (Arm::Pair, "pair-t2-raw-view", Arm::C, "raw-cast-const"),
            (Arm::C, "c-raw-reborrow-shared", Arm::C, "raw-cast-const"),
            (Arm::Pair, "pair-t2-raw-view", Arm::Surface, "subject-use"),
        ];
        for (outer_arm, outer_kind, inner_arm, inner_kind) in PAIRS {
            with_classes(2, |ids| {
                let outer = ClassInput::new(ids[0], arms(&[outer_arm])).with_site(ClassSite::edit(
                    ids[0], ids[1], outer_arm, "j.rs", 1000, 1080, outer_kind,
                ));
                let inner = ClassInput::new(ids[1], arms(&[inner_arm])).with_site(ClassSite::edit(
                    ids[1], ids[1], inner_arm, "j.rs", 1020, 1040, inner_kind,
                ));
                let finalized = finalize_class_inputs(vec![outer, inner]);

                // State 1.
                assert!(
                    finalized.classes[&ids[0]].is_ready(),
                    "{outer_kind} over {inner_kind}: outer held {:?}",
                    finalized.classes[&ids[0]].hold_reasons()
                );
                assert!(
                    finalized.classes[&ids[1]].is_ready(),
                    "{outer_kind} over {inner_kind}: inner held {:?}",
                    finalized.classes[&ids[1]].hold_reasons()
                );
                assert!(
                    finalized.classes[&ids[0]].depends_on.contains(&ids[1]),
                    "{outer_kind} over {inner_kind}: composed without its dependency"
                );
                assert!(
                    finalized.collisions.is_empty(),
                    "{outer_kind} over {inner_kind}: still a collision"
                );

                // State 2.
                let inner_reverted =
                    dependent_closure(&finalized.classes, &BTreeSet::from([ids[1]]));
                assert!(
                    inner_reverted.contains(&ids[0]),
                    "{outer_kind} over {inner_kind}: the outer survived its inner's revert"
                );

                // State 3.
                let outer_reverted =
                    dependent_closure(&finalized.classes, &BTreeSet::from([ids[0]]));
                assert!(
                    !outer_reverted.contains(&ids[1]),
                    "{outer_kind} over {inner_kind}: reverting the outer took the inner with it"
                );
            });
        }
    }

    /// The allowlist stays an allowlist. An outer/inner kind combination that
    /// is not one of the five still collides, and both classes still hold —
    /// which is exactly the cost L07 is paying down for the five it names.
    #[test]
    fn l07_unlisted_kind_pair_still_collides() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(2, |ids| {
            let outer = ClassInput::new(ids[0], arms(&[Arm::Pair])).with_site(ClassSite::edit(
                ids[0],
                ids[1],
                Arm::Pair,
                "j.rs",
                1000,
                1080,
                "pair-t2-raw-view",
            ));
            let inner = ClassInput::new(ids[1], arms(&[Arm::C])).with_site(ClassSite::edit(
                ids[1],
                ids[1],
                Arm::C,
                "j.rs",
                1020,
                1040,
                "slice-to-raw-const",
            ));
            let finalized = finalize_class_inputs(vec![outer, inner]);
            assert_eq!(finalized.collisions.len(), 1);
            assert!(!finalized.classes[&ids[0]].is_ready());
            assert!(!finalized.classes[&ids[1]].is_ready());
        });
    }

    /// A true crossing of a LISTED pair is still a collision. Composition is
    /// about strict containment; two intervals that merely overlap have no
    /// inner-first order to render in.
    #[test]
    fn l07_listed_kinds_that_cross_are_still_held() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(2, |ids| {
            let outer = ClassInput::new(ids[0], arms(&[Arm::Pair])).with_site(ClassSite::edit(
                ids[0],
                ids[1],
                Arm::Pair,
                "j.rs",
                1000,
                1050,
                "pair-t2-raw-view",
            ));
            let inner = ClassInput::new(ids[1], arms(&[Arm::C])).with_site(ClassSite::edit(
                ids[1],
                ids[1],
                Arm::C,
                "j.rs",
                1040,
                1090,
                "typed-raw-temporary",
            ));
            let finalized = finalize_class_inputs(vec![outer, inner]);
            assert_eq!(finalized.collisions.len(), 1, "a crossing composed");
            assert!(!finalized.classes[&ids[0]].is_ready());
            assert!(!finalized.classes[&ids[1]].is_ready());
        });
    }

    /// The two edits must live in ONE function body. A same-file containment
    /// across two different callers is a byte coincidence, not a nesting.
    #[test]
    fn l07_containment_across_two_callers_is_not_a_composition() {
        use crate::bo_rewriter::decision::Arm;
        with_classes(3, |ids| {
            let outer = ClassInput::new(ids[0], arms(&[Arm::Pair])).with_site(ClassSite::edit(
                ids[0],
                ids[1],
                Arm::Pair,
                "j.rs",
                1000,
                1080,
                "pair-t2-raw-view",
            ));
            let inner = ClassInput::new(ids[2], arms(&[Arm::C])).with_site(ClassSite::edit(
                ids[2],
                ids[2],
                Arm::C,
                "j.rs",
                1020,
                1040,
                "typed-raw-temporary",
            ));
            let finalized = finalize_class_inputs(vec![outer, inner]);
            assert_eq!(finalized.collisions.len(), 1, "two callers composed");
        });
    }

    #[test]
    fn cls_w6_revert_all_is_never_a_successful_recovery() {
        with_classes(3, |ids| {
            let ready = ids.iter().copied().collect::<BTreeSet<_>>();
            assert!(strict_recovery_subset(&ready, &BTreeSet::from([ids[0]])));
            assert!(!strict_recovery_subset(&ready, &ready));
        });
    }
}
