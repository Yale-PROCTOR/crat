//! R365 source-bound owning-local candidates. No allocation epoch is fabricated.
//! Candidates enter a final additive stage; terminal interfaces are checked again
//! against its completed class plan before the stage can survive.
use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Decision, DecisionTable, SubjectKind,
    a5_site_proof::{A5SeamProofIndex, A5SiteProofVerdict},
    box_facts::{BoxExprEdit, BoxPlan, BoxPlanFailure, BoxShape},
    construction::ConstructionFacts,
    ownership_fields_effects::NativeEffects,
    ownership_fields_formal::{self as formal, NativeFormal},
    ownership_fields_hook::Hold,
    ownership_fields_source::{self as source, SourceCallKey, SourceHold, SourcePlan},
    raw_boundary::{RawBoundarySiteFacts, RetentionSummaries, RetentionVerdict},
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::{
        ownership_fields::{
            free_sites::plan_frees,
            lend::{FormalForm, LendHold},
        },
        plan::ClassFinalization,
    },
    utils::rustc::RustProgram,
};

type Node = (LocalDefId, HirId);

#[derive(Clone, Debug)]
pub(crate) enum NativeHold {
    Source(SourceHold),
    Call(Hold),
    Missing(&'static str),
    Identity,
    Peer(&'static str),
    FinalInterface,
}

#[derive(Clone, Debug)]
struct Bundle {
    plan: BoxPlan,
    source_elements: Option<u64>,
    formals: Vec<NativeFormal>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Candidates {
    bundles: FxHashMap<Node, Bundle>,
    pub(crate) holds: FxHashMap<Node, NativeHold>,
    /// Owners whose bundle was re-derived once at the ownership stage after
    /// a callee's interface class was restored beneath the return-stage proof.
    refreshed: FxHashSet<Node>,
    /// Observation only: the primary diagnosis before the native stage.
    /// Kept apart from native holds and final decisions, including on success.
    primary: FxHashMap<Node, (String, String)>,
}

pub(crate) struct Inputs<'a, 'tcx> {
    pub(crate) program: &'a RustProgram<'tcx>,
    pub(crate) slots: &'a CrateSlots,
    pub(crate) model: &'a FxHashMap<SlotRef, SlotKind>,
    pub(crate) constructions: &'a ConstructionFacts,
    pub(crate) sites: &'a RawBoundarySiteFacts,
    pub(crate) retention: &'a RetentionSummaries,
    pub(crate) a5: &'a A5SeamProofIndex,
}

impl Candidates {
    /// The bound belongs to this exact selected native plan, not its display
    /// receipt or another owner with a coincidentally equal allocation size.
    pub(crate) fn selected_slice_elements(&self, node: Node, selected: &BoxPlan) -> Option<u64> {
        let bundle = self.bundles.get(&node)?;
        (bundle.plan == *selected
            && selected.shape == BoxShape::Slice
            && !selected.optional
            && !selected.fabricated_extent)
            .then_some(bundle.source_elements)
            .flatten()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.bundles.is_empty()
    }

    /// Append-only observation of the already-computed candidate family.
    /// This must run even when there are no successful native bundles.
    pub(crate) fn audit(
        &self,
        tcx: rustc_middle::ty::TyCtxt<'_>,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
        table: &DecisionTable,
    ) -> String {
        let clean = |text: &str| text.replace(['\t', '\r', '\n'], " ");
        let mut rows = Vec::new();
        for (subject, decision) in &table.entries {
            if !outer_owning(slots, model, subject) {
                continue;
            }
            let node = (subject.fn_did, subject.hir_id);
            let owner = tcx.def_path_str(subject.fn_did.to_def_id());
            let key = subject.identity_key(&owner);
            let primary = self
                .primary
                .get(&node)
                .cloned()
                .unwrap_or_else(|| primary_diagnosis(decision));
            let final_form = match decision {
                Decision::Box(_) => "box",
                Decision::Degraded(_) => "degraded",
                Decision::Ref { .. } => "ref",
                Decision::InferredRef { .. } => "inferred-ref",
                Decision::Slice { .. } => "slice",
                Decision::NestedSlice { .. } => "nested-slice",
                Decision::Cursor { .. } => "cursor",
                Decision::Opt { .. } => "optional",
            };
            let (considered, status, kind, detail) = if let Some(bundle) = self.bundles.get(&node) {
                let selected = match decision {
                    Decision::Box(plan) => plan == &bundle.plan,
                    Decision::Degraded(_)
                    | Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::NestedSlice { .. }
                    | Decision::Cursor { .. }
                    | Decision::Opt { .. } => false,
                };
                if selected {
                    (true, "selected", "-", "-".to_owned())
                } else {
                    (
                        true,
                        "not-selected",
                        "CandidateNotSelected",
                        "final decision does not carry the exact native candidate plan".to_owned(),
                    )
                }
            } else if let Some(hold) = self.holds.get(&node) {
                (true, "held", native_hold_kind(hold), format!("{hold:?}"))
            } else {
                let kind = match subject.kind {
                    SubjectKind::Param { .. } => "ParameterNotAttempted",
                    SubjectKind::Local if subject.ptr_depth != 1 => "DepthNotAttempted",
                    SubjectKind::Local => "OutsideNativeCandidateScope",
                };
                (
                    false,
                    "unattempted",
                    kind,
                    "no native candidate or native rejection was produced for this subject"
                        .to_owned(),
                )
            };
            let row = format!(
                "{}\t{}\t{}\t{}\t{}\towning\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                clean(&key),
                clean(&owner),
                subject.local.as_u32(),
                matches!(subject.kind, SubjectKind::Param { .. }),
                subject.ptr_depth,
                final_form,
                considered,
                status,
                kind,
                clean(&detail),
                clean(&primary.0),
                clean(&primary.1),
            );
            rows.push((key, row));
        }
        // Sorting is presentation only. Duplicate identities remain visible to
        // the census join instead of being overwritten by a map insertion.
        rows.sort_by(|left, right| left.0.cmp(&right.0));
        let mut output = "subject_key\towner_fn\tmir_local\tis_param\tptr_depth\tmodel_kind\tfinal_decision\tconsidered\tnative_status\tnative_hold_kind\tnative_hold_detail\tprimary_reason\tprimary_detail\n".to_owned();
        for (_, row) in rows {
            output.push_str(&row);
        }
        output
    }

    pub(crate) fn derive(
        inputs: &Inputs<'_, '_>,
        table: &DecisionTable,
        classes: &ClassFinalization,
    ) -> Self {
        let effects = NativeEffects::derive(inputs.program);
        let mut result = Self::default();
        for (subject, decision) in &table.entries {
            if outer_owning(inputs.slots, inputs.model, subject) {
                result.primary.insert(
                    (subject.fn_did, subject.hir_id),
                    primary_diagnosis(decision),
                );
            }
            if subject.kind != SubjectKind::Local {
                continue;
            }
            let degraded = match decision {
                Decision::Degraded(degraded) => degraded,
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. }
                | Decision::Opt { .. }
                | Decision::Box(_) => continue,
            };
            // Locals the prior path held on their caller (F01), on an
            // aggregate initializer (F04), or on pointer depth (F03: an array
            // of raw pointers whose outer owner is the subject and whose
            // elements stay raw) are native candidates.
            match &degraded.reason {
                super::DegradeReason::BoxFailure {
                    failure: BoxPlanFailure::NativeEvidenceHeld { prior_key, .. },
                } if matches!(
                    *prior_key,
                    "box-param-caller-unknown" | "box-initializer-unsupported"
                ) => {}
                // The source permit decides which depth it admits.
                super::DegradeReason::BoxFailure {
                    failure: BoxPlanFailure::PointerDepth,
                } => {}
                // The prior path knows no active endpoint (R415: a local
                // stored into another object's field is one — the transfer).
                super::DegradeReason::BoxFailure {
                    failure: BoxPlanFailure::EndpointInactive,
                } => {}
                _ => continue,
            }
            let Some(slot) = inputs
                .slots
                .fn_local_slots
                .get(&subject.fn_did)
                .and_then(|u| u.slot_for_local_depth(subject.local, 0))
            else {
                continue;
            };
            if inputs.model.get(&SlotRef::Local(subject.fn_did, slot)) != Some(&SlotKind::Owning) {
                continue;
            }
            let node = (subject.fn_did, subject.hir_id);
            let bundle = source::derive(inputs.program, subject, inputs.constructions)
                .map_err(NativeHold::Source)
                .and_then(|source| {
                    derive_bundle(inputs, table, classes, &effects, subject, &source, false)
                });
            match bundle {
                Ok(bundle) => {
                    result.bundles.insert(node, bundle);
                }
                Err(hold) => {
                    result.holds.insert(node, hold);
                }
            }
        }
        result
    }

    /// This supplies only candidate rendering to the replayed suffix. The
    /// unchanged model owns the kind, and the final stage checks interfaces.
    pub(crate) fn plan(&self, node: Node) -> Option<&BoxPlan> {
        self.bundles.get(&node).map(|bundle| &bundle.plan)
    }

    /// The ownership stage's recheck. A formal proof taken at the return
    /// stage can be stale here when a callee's interface class was restored
    /// (its formal is raw again): the bundle is re-derived ONCE against the
    /// current table and classes — the lend bridge changes text, nothing else
    /// — and the stage re-runs with the refreshed plan; a bundle that cannot
    /// be re-derived invalidates its owner exactly as before.
    pub(crate) fn refresh_or_invalidate(
        &mut self,
        inputs: &Inputs<'_, '_>,
        table: &DecisionTable,
        classes: &ClassFinalization,
    ) -> (FxHashSet<LocalDefId>, bool) {
        let effects = NativeEffects::derive(inputs.program);
        let mut refreshed = false;
        let stale: Vec<Node> = self
            .invalid_owner_nodes(inputs, table, classes)
            .into_iter()
            .filter(|node| !self.refreshed.contains(node))
            .collect();
        for node in stale {
            let Some((subject, _)) = table
                .entries
                .iter()
                .find(|(s, _)| (s.fn_did, s.hir_id) == node)
            else {
                continue;
            };
            let bundle = source::derive(inputs.program, subject, inputs.constructions)
                .map_err(NativeHold::Source)
                .and_then(|source| {
                    derive_bundle(inputs, table, classes, &effects, subject, &source, true)
                });
            self.refreshed.insert(node);
            match bundle {
                Ok(bundle) => {
                    self.bundles.insert(node, bundle);
                    refreshed = true;
                }
                Err(hold) => {
                    self.bundles.remove(&node);
                    self.holds.insert(node, hold);
                }
            }
        }
        (self.invalid_owners(inputs, table, classes), refreshed)
    }

    fn invalid_owner_nodes(
        &self,
        inputs: &Inputs<'_, '_>,
        table: &DecisionTable,
        classes: &ClassFinalization,
    ) -> Vec<Node> {
        let mut invalid = Vec::new();
        for (&node, bundle) in &self.bundles {
            if !table.entries.iter().any(|(s, d)| {
                let selected = match d {
                    Decision::Box(plan) => plan == &bundle.plan,
                    Decision::Degraded(_)
                    | Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::NestedSlice { .. }
                    | Decision::Cursor { .. }
                    | Decision::Opt { .. } => false,
                };
                (s.fn_did, s.hir_id) == node && selected
            }) {
                continue;
            }
            if bundle.formals.iter().any(|proof| {
                let (callee, argument) = proof.identity();
                formal::resolve(
                    inputs.program.tcx,
                    inputs.slots,
                    inputs.model,
                    table,
                    classes,
                    callee,
                    argument,
                )
                .map_or(true, |current| current != *proof)
                    || (proof.terminal() == super::seam::Form::Raw
                        && !stable_raw_formal(table, callee, argument))
            }) {
                invalid.push(node);
            }
        }
        invalid
    }

    pub(crate) fn invalid_owners(
        &self,
        inputs: &Inputs<'_, '_>,
        table: &DecisionTable,
        classes: &ClassFinalization,
    ) -> FxHashSet<LocalDefId> {
        let mut invalid = FxHashSet::default();
        for (&node, bundle) in &self.bundles {
            if !table.entries.iter().any(|(s, d)| {
                let selected = match d {
                    Decision::Box(plan) => plan == &bundle.plan,
                    Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::NestedSlice { .. }
                    | Decision::Cursor { .. }
                    | Decision::Opt { .. }
                    | Decision::Degraded(_) => false,
                };
                (s.fn_did, s.hir_id) == node && selected
            }) {
                continue;
            }
            for proof in &bundle.formals {
                let (callee, argument) = proof.identity();
                if formal::resolve(
                    inputs.program.tcx,
                    inputs.slots,
                    inputs.model,
                    table,
                    classes,
                    callee,
                    argument,
                )
                .map_or(true, |current| current != *proof)
                    || (proof.terminal() == super::seam::Form::Raw
                        && !stable_raw_formal(table, callee, argument)
                        && !self.refreshed.contains(&node))
                {
                    invalid.insert(node.0);
                }
            }
        }
        invalid
    }
}

/// `span` lies inside the initializer of a `let` whose binding the table
/// decided a slice-family form (a slice, cursor, nested slice or option) —
/// the construction that family renders over the initializer's source text.
fn under_slice_construction(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    table: &DecisionTable,
    owner: LocalDefId,
    span: rustc_span::Span,
) -> bool {
    table.entries.iter().any(|(subject, decision)| {
        if subject.fn_did != owner {
            return false;
        }
        let constructed = match decision {
            Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. } => true,
            Decision::Box(_)
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Degraded(_) => false,
        };
        if !constructed {
            return false;
        }
        let rustc_hir::Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else {
            return false;
        };
        local
            .init
            .is_some_and(|init| init.span.contains(span) && init.span != span)
    })
}

/// The argument spans a selected native Box plan renders itself (a lend or a
/// transfer, through the owner or one of its views). The seam plans no call
/// glue at these positions.
pub(crate) fn owned_argument_spans<'a>(
    entries: impl Iterator<Item = &'a (super::Subject, Decision)>,
) -> FxHashSet<(LocalDefId, rustc_span::Span)> {
    let mut spans = FxHashSet::default();
    for (subject, decision) in entries {
        let plan = match decision {
            Decision::Box(plan) => plan,
            Decision::Degraded(_)
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. } => continue,
        };
        for edit in &plan.expr_edits {
            if matches!(
                edit.receipt,
                "native-box-lend-t1" | "native-box-transfer-to-c-free"
            ) {
                spans.insert((subject.fn_did, edit.span));
            }
        }
    }
    spans
}

fn outer_owning(
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    subject: &super::Subject,
) -> bool {
    slots
        .fn_local_slots
        .get(&subject.fn_did)
        .and_then(|universe| universe.slot_for_local_depth(subject.local, 0))
        .is_some_and(|slot| {
            model.get(&SlotRef::Local(subject.fn_did, slot)) == Some(&SlotKind::Owning)
        })
}

fn primary_diagnosis(decision: &Decision) -> (String, String) {
    match decision {
        Decision::Degraded(record) => (record.reason.key().to_owned(), record.reason.detail()),
        Decision::Box(_)
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Opt { .. } => ("-".to_owned(), "-".to_owned()),
    }
}

fn native_hold_kind(hold: &NativeHold) -> &'static str {
    use super::ownership_fields_effects::EffectsHold;
    match hold {
        NativeHold::Source(source) => match source {
            SourceHold::Missing(_) => "Source::Missing",
            SourceHold::Identity => "Source::Identity",
            SourceHold::ConstructorIdentity => "Source::ConstructorIdentity",
            SourceHold::ConstructorShape => "Source::ConstructorShape",
            SourceHold::UnsupportedOwnerUse => "Source::UnsupportedOwnerUse",
            SourceHold::FreeIdentity => "Source::FreeIdentity",
            SourceHold::NormalExitCoverage => "Source::NormalExitCoverage",
            SourceHold::UnsupportedControlFlow => "Source::UnsupportedControlFlow",
            SourceHold::Duplicate(_) => "Source::Duplicate",
            SourceHold::Unexpected(_) => "Source::Unexpected",
            SourceHold::Absent(_) => "Source::Absent",
        },
        NativeHold::Call(Hold::NativeEffects(effects)) => match effects {
            EffectsHold::MissingFunction(_) => "Call::NativeEffects::MissingFunction",
            EffectsHold::Parameter { .. } => "Call::NativeEffects::Parameter",
            EffectsHold::Retirement(_) => "Call::NativeEffects::Retirement",
            EffectsHold::Opaque(_) => "Call::NativeEffects::Opaque",
            EffectsHold::Cycle(_) => "Call::NativeEffects::Cycle",
            EffectsHold::Escape(_) => "Call::NativeEffects::Escape",
        },
        NativeHold::Call(Hold::Lend(lend)) => match lend {
            LendHold::Missing(_) => "Call::Lend::Missing",
            LendHold::Inventory => "Call::Lend::Inventory",
            LendHold::Grant => "Call::Lend::Grant",
            LendHold::Identity => "Call::Lend::Identity",
            LendHold::OwningCallee => "Call::Lend::OwningCallee",
            LendHold::ConsumingCallee => "Call::Lend::ConsumingCallee",
            LendHold::Formal => "Call::Lend::Formal",
            LendHold::MoveInsteadOfLend => "Call::Lend::MoveInsteadOfLend",
            LendHold::Retention => "Call::Lend::Retention",
            LendHold::Span => "Call::Lend::Span",
            LendHold::LiveReference => "Call::Lend::LiveReference",
            LendHold::Protector => "Call::Lend::Protector",
            LendHold::PeerAlias => "Call::Lend::PeerAlias",
            LendHold::TargetDisagreement => "Call::Lend::TargetDisagreement",
        },
        NativeHold::Call(Hold::Missing(_)) => "Call::Missing",
        NativeHold::Call(Hold::Identity) => "Call::Identity",
        NativeHold::Call(Hold::Construction) => "Call::Construction",
        NativeHold::Call(Hold::Projection) => "Call::Projection",
        NativeHold::Call(Hold::RecursiveSuppression) => "Call::RecursiveSuppression",
        NativeHold::Call(Hold::Free(_)) => "Call::Free",
        NativeHold::Call(Hold::Close(_)) => "Call::Close",
        NativeHold::Missing(_) => "Missing",
        NativeHold::Identity => "Identity",
        NativeHold::Peer(_) => "Peer",
        NativeHold::FinalInterface => "FinalInterface",
    }
}

/// This tranche does not convert formals. Its raw interface survives both a
/// ready class and restoration of that class, so later verification recovery
/// cannot change the argument expansion into a Box transfer or reference.
fn stable_raw_formal(table: &DecisionTable, callee: LocalDefId, argument: usize) -> bool {
    table.entries.iter().any(|(subject, decision)| {
        let degraded = match decision {
            Decision::Degraded(_) => true,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => false,
        };
        subject.fn_did == callee
            && matches!(subject.kind, SubjectKind::Param{hir_index} if hir_index==argument)
            && degraded
    }) && table
        .input_interfaces
        .parameter_forms
        .get(&(callee, argument))
        == Some(&super::seam::Form::Raw)
}

/// Pinned Linux System-allocation / libc-free contract. The complete current
/// crate graph must contain no user global allocator, including dependencies.
/// Numeric nonempty payloads avoid the dangling zero-layout sentinel.
pub(crate) fn c_free_allocator_compatible(tcx: rustc_middle::ty::TyCtxt<'_>) -> bool {
    tcx.sess.target.os == "linux"
        && !tcx.has_global_allocator(rustc_span::def_id::LOCAL_CRATE)
        && tcx.crates(()).iter().all(|c| !tcx.has_global_allocator(*c))
        && tcx
            .crates(())
            .iter()
            .any(|c| tcx.crate_name(*c).as_str() == "std")
}
pub(crate) fn raw_lend_argument(
    shape: BoxShape,
    name: &str,
    element: &str,
    target: &str,
) -> String {
    let value = match shape {
        BoxShape::Sized => format!("::core::ptr::from_mut(&mut *({name}))"),
        BoxShape::Slice => format!("<[_]>::as_mut_ptr(&mut *({name}))"),
    };
    if target == format!("*mut {element}") {
        value
    } else {
        format!("({value} as {target})")
    }
}

const DECLARATION_TYPE_RECEIPT: &str = "native-box-declaration-type";
const VIEW_ALIAS_TYPE_RECEIPT: &str = "native-box-view-alias-type";

/// R402-2(a): register the explicit declaration type of every native Box
/// owner as a `local` explicit-declaration site, so both emission paths
/// annotate the binding (`let mut p: ::std::boxed::Box<[T]> = …`).
pub(crate) fn complete_declarations(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    table: &super::DecisionTable,
    plan: &mut super::seam::SeamPlan,
) {
    for (subject, decision) in &table.entries {
        let box_plan = match decision {
            Decision::Box(plan) => plan,
            Decision::Degraded(_)
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. } => continue,
        };
        let Some(emitted_type) = box_plan
            .receipts
            .iter()
            .find_map(|receipt| receipt.strip_prefix(DECLARATION_TYPE_RECEIPT))
            .map(str::trim)
        else {
            continue;
        };
        let node = (subject.fn_did, subject.hir_id);
        // A declaration's text edit: inserted after the pattern, or REPLACING
        // the source's own annotation when the binding carries one.
        let mut declarations = vec![(
            node,
            subject.ty_span.map_or(
                (
                    subject.binding_span.shrink_to_hi(),
                    format!(": {emitted_type}"),
                ),
                |annotation| (annotation, emitted_type.to_owned()),
            ),
            emitted_type.to_owned(),
        )];
        // The owner's view aliases: `let mut a = root.offset(e)` becomes
        // `let mut a: &mut [T] = &mut (*root)[(e) as usize..]`.
        for receipt in &box_plan.receipts {
            let Some(rest) = receipt.strip_prefix(VIEW_ALIAS_TYPE_RECEIPT) else { continue };
            let mut parts = rest.trim().splitn(2, ' ');
            let (Some(local_id), Some(ty)) = (parts.next(), parts.next()) else { continue };
            let Ok(local_id) = local_id.parse::<u32>() else { continue };
            let alias = rustc_hir::HirId {
                owner: subject.hir_id.owner,
                local_id: rustc_hir::ItemLocalId::from_u32(local_id),
            };
            let span = tcx.hir_span(alias);
            declarations.push((
                (subject.fn_did, alias),
                (span.shrink_to_hi(), format!(": {ty}")),
                ty.to_owned(),
            ));
        }
        for (node, (span, replacement), emitted_type) in declarations {
            if plan
                .explicit_declarations
                .iter()
                .any(|site| site.node == Some(node) && site.category == "local")
            {
                continue;
            }
            plan.explicit_declarations
                .push(super::seam::ExplicitDeclarationSite {
                    owner_class: crate::bo_rewriter::bridge_receipt::SignatureClassId::of(
                        subject.fn_did,
                    ),
                    caller: subject.fn_did,
                    node: Some(node),
                    span: Some(span),
                    category: "local",
                    replacement: Some(replacement),
                    emitted_type,
                    arm: "surface",
                });
        }
    }
}

/// R402-2(b): a `Box` decision the emission stage withdrew — its owner's
/// signature class held, or its edits unplaceable — is reported DEGRADED with
/// the withdrawal reason and never expected or counted delivered. Any other
/// decision is left to the seed writer's own accounting.
pub(crate) fn withdrawn_box_reason(
    decision: &Decision,
    emission_plan: &crate::bo_rewriter::plan::Plan,
    owner_class: crate::bo_rewriter::bridge_receipt::SignatureClassId,
    unplaced_reason: Option<&'static str>,
) -> Option<String> {
    match decision {
        Decision::Box(_) => {}
        Decision::Degraded(_)
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Opt { .. } => return None,
    }
    if let Some(reason) = unplaced_reason {
        return Some(format!("unplaceable:{reason}"));
    }
    emission_plan
        .class_hold_reason(owner_class)
        .map(|reason| format!("signature-class-held:{reason}"))
}

/// The peer argument's MIR local is outside the derivation closure of the
/// subject's allocation result, so it cannot point into the fresh object;
/// an escaped allocation (stored into memory) proves nothing.
fn fresh_allocation_peer_disjoint(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    subject: &super::Subject,
    source: &SourcePlan,
    key: SourceCallKey,
    peer_index: usize,
) -> Result<String, &'static str> {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(subject.fn_did)
        .borrow();
    let start = rustc_middle::mir::Local::from_u32(source.allocation_local());
    let (closure, escape) = super::ownership_fields_effects::derivation_closure(
        tcx,
        &body,
        subject.fn_did.local_def_index.as_u32(),
        start,
    );
    if escape.is_some() || !closure.contains(&subject.local) {
        return Err("fresh-allocation-escapes");
    }
    let data = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_u32(key.block)];
    let rustc_middle::mir::TerminatorKind::Call { args, .. } = &data.terminator().kind else {
        return Err("peer-site-not-a-call");
    };
    let peer =
        args.get(peer_index)
            .and_then(|arg| match &arg.node {
                rustc_middle::mir::Operand::Copy(place)
                | rustc_middle::mir::Operand::Move(place) => place.as_local(),
                rustc_middle::mir::Operand::Constant(_) => None,
            })
            .ok_or("peer-operand-not-a-local")?;
    if closure.contains(&peer) {
        return Err("peer-derived-from-subject");
    }
    Ok(format!(
        "subject_local={} allocation_local={} peer_local={} closure={:?}",
        subject.local.as_u32(),
        start.as_u32(),
        peer.as_u32(),
        closure.iter().map(|l| l.as_u32()).collect::<Vec<_>>()
    ))
}

fn derive_bundle(
    inputs: &Inputs<'_, '_>,
    table: &DecisionTable,
    classes: &ClassFinalization,
    effects: &NativeEffects<'_>,
    subject: &super::Subject,
    source: &SourcePlan,
    final_stage: bool,
) -> Result<Bundle, NativeHold> {
    // At the ownership stage (the last), a callee class that is not ready
    // keeps its raw signature in the emitted program: a raw formal is final.
    let raw_is_final = |callee: LocalDefId, argument: usize| {
        stable_raw_formal(table, callee, argument)
            || (final_stage
                && !classes
                    .classes
                    .get(&crate::bo_rewriter::bridge_receipt::SignatureClassId::of(
                        callee,
                    ))
                    .is_some_and(crate::bo_rewriter::plan::SignatureClassPlan::is_ready))
    };
    let tcx = inputs.program.tcx;
    let name = subject.param_name.as_ref().ok_or(NativeHold::Identity)?;
    // R431: an owner MOVED OUT of another object's field (`let mut x =
    // (*y).left;`) has no constructor of its own — the load is the FIELD
    // family's to render (wave-6f's `take()` out of an owning field). Until a
    // field transaction owns that field, typing this local `Box<T>` would
    // leave the container's raw copy pointing into memory this Box closes:
    // the shape holds fail-closed. (The composition lifts the hold for a
    // field wave-6f's transaction owns; see the R431 predicate patch.)
    // R431 on the composition: the load is an acquisition only where a field
    // transaction OWNS the field it came out of; their transaction renders the
    // move (`take()`), this producer types the local and closes it.
    let field_load = source.load_field();
    if let Some((struct_did, field_index)) = field_load
        && !table.field_transactions.applied.iter().any(|transaction| {
            transaction.owning
                && transaction.key.struct_did.to_def_id() == struct_did
                && transaction.key.field_index == field_index
        })
    {
        return Err(NativeHold::Missing("native-field-load-field-not-owned"));
    }
    let mut edits = if field_load.is_some() {
        // The initializer is the field family's; this producer contributes the
        // type, the close and the receipts, and no constructor edit.
        Vec::new()
    } else {
        vec![source.constructor().clone()]
    };
    // R402-2(a): every delivered declaration carries its explicit type. The
    // type is registered as an explicit local declaration site (the same
    // channel wave-6k's construction values use), which the text path splices
    // after the pattern — or over the source's own annotation (`let v: *mut T
    // = …`, bzip2's spelling) — and the AST path places as `local.ty`,
    // replacing an annotation (R419-1/3).
    let payload = match source.shape() {
        BoxShape::Sized => source.element_spelling().to_owned(),
        BoxShape::Slice => format!("[{}]", source.element_spelling()),
    };
    // R423: a view alias the table decides for ANOTHER family (a slice or
    // cursor over the same accesses) owns its own use edits; rendering mine
    // too would claim one interval twice (`intra-class-interval-overlap`).
    // The alias is only this producer's while no other family took it.
    if source.view_aliases().iter().any(|alias| {
        table.entries.iter().any(|(candidate, decision)| {
            let decided = match decision {
                Decision::Box(_)
                | Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. }
                | Decision::Opt { .. } => true,
                Decision::Degraded(_) => false,
            };
            candidate.fn_did == subject.fn_did && candidate.hir_id == alias.hir_id && decided
        })
    }) {
        return Err(NativeHold::Missing("native-view-alias-family-owned"));
    }
    edits.extend_from_slice(source.scalar_edits());
    // R412-2: an owner access that is the BASE of another family's slice
    // construction (`let mut src = ((**elevations.offset(i)).data).offset(…)`
    // with `src` decided a slice or cursor) sits inside that family's
    // initializer replacement, which is rendered from the source text — the
    // access edit would be lost and `.offset` kept on the Box. Until the
    // nested-edit composition applies the inner edit first (wave-6l's), the
    // owner holds, typed.
    if source
        .scalar_edits()
        .iter()
        .any(|edit| under_slice_construction(tcx, table, subject.fn_did, edit.span))
    {
        return Err(NativeHold::Missing(
            "native-access-under-slice-construction",
        ));
    }
    for alias in source.view_aliases() {
        if source.shape() != BoxShape::Slice {
            return Err(NativeHold::Missing("native-view-alias-shape"));
        }
        edits.push(BoxExprEdit {
            span: alias.initializer_span,
            replacement: format!("&mut (*({name}))[({}) as usize..]", alias.start),
            receipt: "native-box-view-alias",
        });
        edits.extend_from_slice(&alias.access_edits);
    }
    let mut receipts = vec![format!(
        "native-owning-source owner={} local={} generation=Missing source-root={:?}",
        subject.fn_did.local_def_index.as_u32(),
        subject.local.as_u32(),
        subject.hir_id
    )];
    receipts.push(format!(
        "{DECLARATION_TYPE_RECEIPT} ::std::boxed::Box<{payload}>"
    ));
    for alias in source.view_aliases() {
        receipts.push(format!(
            "{VIEW_ALIAS_TYPE_RECEIPT} {} &mut [{}]",
            alias.hir_id.local_id.as_u32(),
            source.element_spelling()
        ));
        receipts.push(format!(
            "native-box-view-alias alias={} start=({}) accesses={} runtime-checked=slice-start-and-index(R394-1) owner-untouched-while-live=borrow-checker",
            alias.spelling,
            alias.start,
            alias.access_edits.len()
        ));
    }
    receipts.push(format!("native-box-slice-uses count={} element={} length-unchanged=closed-root-uses source-aliases={:?} indexing=delivered-slice-walker",source.count(),source.element(),source.mir_aliases()));
    receipts.push(format!("native-generated-unwind-permit operations=allocation-helpers-and-slice-bounds-checks all-roots=fresh-local-closed-uses-and-verified-T1 payload={}/nonrecursive; actual-waiver-sites=emitted-MIR-ledger",source.element()));
    let mut formals = Vec::new();
    let mut checked_calls = BTreeSet::<SourceCallKey>::new();
    for obligation in source.calls() {
        let callee = obligation
            .callee()
            .as_local()
            .ok_or(NativeHold::Missing("native-local-callee"))?;
        let argument = obligation.argument();
        let key = obligation.key();
        // The lent local is the owner or one of its view aliases; the
        // raw-boundary site is keyed by that local's own binding.
        let lent = obligation.lent();
        let name: &str = &lent.spelling;
        let lent_node = (subject.fn_did, lent.hir_id);
        let matching: Vec<_> = inputs
            .sites
            .sites
            .iter()
            .filter(|site| {
                site.node == Some(lent_node)
                    && site.callee_local == Some(callee)
                    && site.key.block == key.block
                    && site.key.statement_index as usize == key.statement
                    && site.key.argument_index == argument
                    && site.source_span.source_callsite()
                        == obligation.argument_span().source_callsite()
            })
            .collect();
        let [site] = matching.as_slice() else {
            return Err(NativeHold::Missing("native-lend-source-join"));
        };
        if site.callee_may_yield_pointer && obligation.deallocator_events().is_none() {
            return Err(NativeHold::Missing("native-pointer-yield"));
        }
        let emitted = formal::resolve(
            tcx,
            inputs.slots,
            inputs.model,
            table,
            classes,
            callee,
            argument,
        )
        .map_err(NativeHold::Call)?;
        let consumes = obligation.deallocator_events().is_some();
        if consumes && lent.is_view_alias {
            // A view never transfers ownership; only the owner does.
            return Err(NativeHold::Call(Hold::Lend(LendHold::MoveInsteadOfLend)));
        }
        let lend_expression = if consumes {
            if !source.nonempty() {
                return Err(NativeHold::Missing("native-transfer-nonempty"));
            }
            if !c_free_allocator_compatible(tcx) {
                return Err(NativeHold::Missing("native-transfer-allocator-contract"));
            }
            receipts.push("native-transfer-allocator=linux-System;global-allocators=none;nonempty=numeric-layout".into());
            if emitted.terminal() != super::seam::Form::Raw || !raw_is_final(callee, argument) {
                return Err(NativeHold::FinalInterface);
            }
            let proof =
                super::ownership_fields_deallocator::derive(inputs.program, callee, argument)
                    .map_err(|_| NativeHold::Missing("native-deallocator-summary"))?;
            if !proof.matches(inputs.program, callee, argument)
                || Some(proof.events()) != obligation.deallocator_events()
            {
                return Err(NativeHold::Identity);
            }
            receipts.push(format!("native-box-transfer {:?} callee={} argument={argument} original-C-free-events={:?} caller-after=dead",key,tcx.def_path_str(callee.to_def_id()),proof.events()));
            format!(
                "(::std::boxed::Box::into_raw({name}) as {})",
                obligation.raw_argument_type()
            )
        } else {
            let nonconsuming_scope =
                formal::require_nonconsuming(effects, &emitted).map_err(NativeHold::Call)?;
            receipts.push(format!(
                "native-nonconsuming-proof {:?} arg={argument} scope={nonconsuming_scope}",
                key
            ));
            let retention_scope = match inputs.retention.get(callee, argument) {
                Some(RetentionVerdict::NoRetain { certificate }) => {
                    inputs
                        .retention
                        .verify_certificate(callee, argument, certificate)
                        .map_err(|_| NativeHold::Call(Hold::Lend(LendHold::Retention)))?;
                    "raw-boundary-t1-certificate"
                }
                // T1's frontier stops at core pointer arithmetic on the formal;
                // the native trace follows the derived pointer instead.
                _ => effects
                    .certify_no_retention(callee, argument)
                    .map_err(|_| NativeHold::Call(Hold::Lend(LendHold::Retention)))?
                    .scope(),
            };
            receipts.push(format!(
                "native-noretention-proof {:?} arg={argument} scope={retention_scope}",
                key
            ));
            match (source.shape(), emitted.emitted(), emitted.terminal()) {
                (BoxShape::Slice, FormalForm::MutableRaw, super::seam::Form::Raw)
                    if raw_is_final(callee, argument) =>
                {
                    raw_lend_argument(
                        source.shape(),
                        name,
                        source.element(),
                        obligation.raw_argument_type(),
                    )
                }
                (BoxShape::Sized, FormalForm::MutableRaw, super::seam::Form::Raw)
                    if raw_is_final(callee, argument) =>
                {
                    raw_lend_argument(
                        source.shape(),
                        name,
                        source.element(),
                        obligation.raw_argument_type(),
                    )
                }
                (
                    BoxShape::Slice,
                    FormalForm::MutableReference,
                    super::seam::Form::Slice { mutable: true },
                )
                | (
                    BoxShape::Sized,
                    FormalForm::MutableReference,
                    super::seam::Form::Ref { mutable: true },
                )
                | (
                    BoxShape::Slice,
                    FormalForm::MutableReference,
                    super::seam::Form::Cursor { mutable: true },
                ) => format!("&mut *({name})"),
                // A thin formal over a slice owner: the callee decided a
                // reference to ONE element (its uses are direct derefs), so
                // the lend is the first element, never a widened slice.
                (
                    BoxShape::Slice,
                    FormalForm::MutableReference,
                    super::seam::Form::Ref { mutable: true },
                ) => format!("&mut (*({name}))[0]"),
                (
                    BoxShape::Slice,
                    FormalForm::SharedReference,
                    super::seam::Form::Slice { mutable: false },
                )
                | (
                    BoxShape::Sized,
                    FormalForm::SharedReference,
                    super::seam::Form::Ref { mutable: false },
                ) => format!("&*({name})"),
                (
                    BoxShape::Slice,
                    FormalForm::SharedReference,
                    super::seam::Form::Ref { mutable: false },
                ) => format!("&(*({name}))[0]"),
                _ => return Err(NativeHold::FinalInterface),
            }
        };
        let sig = tcx.fn_sig(callee.to_def_id()).skip_binder().skip_binder();
        // The source permit accounts for every nonpointer operand separately.
        // Only literal/local/cast scalar reads commute with the peer borrows.
        let pointer_indices: BTreeSet<_> = sig
            .inputs()
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| ty.is_raw_ptr().then_some(index))
            .collect();
        let scalar_indices: BTreeSet<_> = (0..sig.inputs().len())
            .filter(|index| !pointer_indices.contains(index))
            .collect();
        if (!sig.output().is_unit()
            && !matches!(
                sig.output().kind(),
                rustc_middle::ty::TyKind::Int(_)
                    | rustc_middle::ty::TyKind::Uint(_)
                    | rustc_middle::ty::TyKind::Float(_)
                    | rustc_middle::ty::TyKind::Bool
            ))
            || &scalar_indices != obligation.scalar_arguments()
            || scalar_indices.iter().any(|index| {
                !matches!(
                    sig.inputs()[*index].kind(),
                    rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Float(_)
                        | rustc_middle::ty::TyKind::Bool
                )
            })
        {
            return Err(NativeHold::Missing("native-complete-pointer-call-shape"));
        }
        // E5C-3 (era-5c 002 claim 4): the lend/transfer invalidates no read
        // in the argument list — the scalar operands are literals, scalar
        // locals, casts and arithmetic over them, never a read through the
        // owner or one of its views — so no hoist is owed at this site.
        receipts.push(format!("native-box-call-scalar-evaluation {key:?} arguments={scalar_indices:?} effect-free=literal-local-cast reads-through-owner=none hoist=not-owed"));
        let peers: Vec<_> = inputs
            .sites
            .sites
            .iter()
            .filter(|peer| {
                peer.callee_local == Some(callee)
                    && peer.key.caller == site.key.caller
                    && peer.key.block == site.key.block
                    && peer.key.statement_index == site.key.statement_index
            })
            .collect();
        let indices: BTreeSet<_> = peers.iter().map(|p| p.key.argument_index).collect();
        if indices != pointer_indices
            || peers.len() != indices.len()
            || peers
                .iter()
                .any(|p| p.call_span != site.call_span || p.node.is_none())
        {
            return Err(NativeHold::Missing("native-peer-inventory"));
        }
        for peer in peers.iter().filter(|p| p.key.argument_index != argument) {
            let proof = inputs.a5.lookup(
                subject.fn_did.local_def_index.as_u32(),
                callee.local_def_index.as_u32(),
                argument,
                peer.key.argument_index,
                site.source_span,
                peer.source_span,
            );
            if proof.verdict != A5SiteProofVerdict::Clear {
                // A fresh allocation whose pointer never escapes (the source
                // permit) is disjoint from every peer not derived from it.
                let disjoint = fresh_allocation_peer_disjoint(
                    tcx,
                    subject,
                    source,
                    key,
                    peer.key.argument_index,
                )
                .map_err(|_| NativeHold::Peer(proof.reason))?;
                receipts.push(format!(
                    "native-box-pair {:?} peer={} disjoint=fresh-allocation-derivation-closure({disjoint}) a5={}",
                    key, peer.key.argument_index, proof.reason
                ));
                continue;
            }
            for a in [argument, peer.key.argument_index] {
                let Some(proof_key) = proof.site_key(a) else {
                    return Err(NativeHold::Peer("missing-exact-site"));
                };
                if proof_key.caller != subject.fn_did
                    || proof_key.callee != callee.to_def_id()
                    || proof_key.location.block != key.block
                    || proof_key.location.statement_index != key.statement
                    || proof_key.slot_depth != 0
                {
                    return Err(NativeHold::Peer("mismatched-exact-site"));
                }
            }
            receipts.push(format!(
                "native-box-pair {:?} {}",
                key,
                proof.receipt(argument, peer.key.argument_index)
            ));
        }
        edits.push(BoxExprEdit {
            span: obligation.argument_span(),
            // Select the inherent slice operation directly; a source trait
            // method on Box must not capture the generated view operation.
            replacement: lend_expression,
            receipt: if consumes {
                "native-box-transfer-to-c-free"
            } else {
                "native-box-lend-t1"
            },
        });
        if !consumes {
            receipts.push(format!("native-box-lend {:?} arg={argument} formal_model={:?} emitted={} T1=verified nonconsuming=verified interval=argument-list-through-return protector=call source-reference-inventory=complete",key,emitted.model_kind(),emitted.terminal().key()));
        }
        checked_calls.insert(key);
        formals.push(emitted);
    }
    // SourcePlan proves a fresh numeric root per allocation occurrence, no source aliases/escaping storage,
    // no reference-taking or rebinding, and all normal paths through its exact
    // C free or proven consuming call. Kept-owner calls are separately proved
    // nonretaining and nonconsuming; transfer calls keep their original callee free. That completes the all-roots account for extra unwinding
    // closes of this scalar root; it is not inferred from an empty loan set.
    for at in source.unwind_obligations() {
        receipts.push(format!("native-unwind-close-permit source-call={at:?} all-roots=fresh-local-closed-uses-and-verified-T1 payload={}/nonrecursive; actual-waiver-sites=emitted-MIR-ledger",source.element()));
    }
    if let Some(span) = source.return_transfer() {
        // Ownership leaves as a raw pointer exactly as in C; the caller's C
        // free is untouched, so the allocation must be C-free compatible.
        if !source.nonempty() {
            return Err(NativeHold::Missing("native-transfer-nonempty"));
        }
        if !c_free_allocator_compatible(tcx) {
            return Err(NativeHold::Missing("native-transfer-allocator-contract"));
        }
        receipts.push(format!("native-box-transfer-at-return span={span:?} allocator=linux-System;global-allocators=none;nonempty=numeric-layout caller-free=unchanged"));
        edits.push(BoxExprEdit {
            span,
            replacement: format!("::std::boxed::Box::into_raw({name})"),
            receipt: "native-box-transfer-at-return",
        });
    }
    if let Some(span) = source.store_transfer() {
        // The owner leaves into another object's field as a raw pointer,
        // exactly as at a return transfer: that object's C free is untouched,
        // so the allocation must be C-free compatible. A slice's count that
        // is not proved nonempty is guarded: an empty boxed slice hands the
        // field a null pointer — one of `malloc(0)`'s legal results, which
        // the C free accepts — never a dangling sentinel.
        if !c_free_allocator_compatible(tcx) {
            return Err(NativeHold::Missing("native-transfer-allocator-contract"));
        }
        let raw = match source.shape() {
            BoxShape::Sized => format!("::std::boxed::Box::into_raw({name})"),
            BoxShape::Slice => format!(
                "(::std::boxed::Box::into_raw({name}) as *mut {})",
                source.element_spelling()
            ),
        };
        let (replacement, nonempty) = if source.nonempty() {
            (raw, "numeric-layout")
        } else {
            // The Box is consumed on every path (no drop anywhere); the
            // empty case reads the raw slice pointer's length.
            (
                format!(
                    "({{ let __crat_raw = ::std::boxed::Box::into_raw({name}); if __crat_raw.len() == 0 {{ ::core::ptr::null_mut() }} else {{ __crat_raw as *mut {} }} }})",
                    source.element_spelling()
                ),
                "guarded-null-for-empty",
            )
        };
        // R416-12: a field a field transaction OWNS (wave-6f's
        // `Option<Box<T>>`) takes the moved Box as its store (`Some(owner)`,
        // rendered by that transaction from this Box decision); the raw
        // transfer is rendered only into a field that stays raw.
        let owned_field = source
            .store_field()
            .is_some_and(|(struct_did, field_index)| {
                table.field_transactions.applied.iter().any(|transaction| {
                    transaction.owning
                        && transaction.key.struct_did.to_def_id() == struct_did
                        && transaction.key.field_index == field_index
                })
            });
        if owned_field {
            receipts.push(format!("native-box-transfer-to-owning-field span={span:?} store=field-transaction(Some(owner)) nonempty={nonempty}"));
        } else {
            receipts.push(format!("native-box-transfer-at-store span={span:?} allocator=linux-System;global-allocators=none;nonempty={nonempty} field-free=unchanged"));
            edits.push(BoxExprEdit {
                span,
                replacement,
                receipt: "native-box-transfer-at-store",
            });
        }
    }
    let required: BTreeSet<_> = source.frees().iter().map(|site| site.key()).collect();
    let frees = plan_frees(&required, source.frees()).map_err(NativeHold::Source)?;
    if frees.len() != source.frees().len() {
        return Err(NativeHold::Identity);
    }
    for (key, edit) in frees {
        let source_free = source
            .frees()
            .iter()
            .find(|site| site.key() == key)
            .ok_or(NativeHold::Identity)?;
        receipts.push(format!(
            "box-free-source-identity {key:?} callee={} span={:?} generation=Missing",
            tcx.def_path_str(source_free.callee()),
            source_free.span(),
        ));
        edits.push(edit);
    }
    let mut spans = BTreeSet::new();
    if edits
        .iter()
        .any(|e| !spans.insert((e.span.lo().0, e.span.hi().0)))
    {
        return Err(NativeHold::Identity);
    }
    let transfer_keys = source
        .calls()
        .iter()
        .filter(|c| c.deallocator_events().is_some())
        .map(|c| c.key())
        .collect::<BTreeSet<_>>();
    receipts.push(format!("native-box-continuations calls={checked_calls:?} free_keys={required:?} transfer_keys={transfer_keys:?} scope-exit=closed-by-explicit-source-sink"));
    Ok(Bundle {
        source_elements: source.count().parse::<u64>().ok(),
        plan: BoxPlan {
            shape: source.shape(),
            optional: false,
            expr_edits: edits,
            delete_statements: Vec::new(),
            receipts,
            fabricated_extent: false,
            pointee_override: None,
            // The plan's own declaration edit spells the Box type (annotated
            // bindings have their declared type replaced in place), so the
            // AST planner must place no declaration splice of its own.
            inferred_binding: true,
            overwrite_spans: Vec::new(),
            retained_sink: true,
            implicit_scope_close: false,
        },
        formals,
    })
}

#[cfg(test)]
mod audit_tests {
    use super::*;
    use crate::bo_rewriter as bo;

    fn rows(text: &str) -> Vec<Vec<&str>> {
        text.lines()
            .skip(1)
            .map(|line| line.split('\t').collect())
            .collect()
    }

    #[test]
    fn native_audit_covers_admitted_owners_and_unattempted_parameters() {
        let source =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);");
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            // Audit-only retained snapshots of actual native plans. These do
            // not authorize a plan or change the compiler/solver result.
            let mut candidates = Candidates::default();
            for (subject, decision) in &table.entries {
                if let Decision::Box(plan) = decision {
                    candidates.bundles.insert(
                        (subject.fn_did, subject.hir_id),
                        Bundle {
                            source_elements: None,
                            plan: plan.clone(),
                            formals: vec![],
                        },
                    );
                }
            }
            assert_eq!(
                candidates.bundles.len(),
                2,
                "both owners admitted by real native pipeline"
            );
            let audit = candidates.audit(tcx, &ctx.slots, &ctx.model, &table);
            let data = rows(&audit);
            assert_eq!(
                data.len(),
                4,
                "both actual caller owners and both Owning formals"
            );
            let keys: BTreeSet<_> = data.iter().map(|row| row[0]).collect();
            assert_eq!(keys.len(), 4);
            assert!(data.iter().all(|row| row.len() == 13 && row[5] == "owning"));
            assert_eq!(
                data.iter()
                    .filter(|row| row[7] == "true" && row[8] == "selected" && row[6] == "box")
                    .count(),
                2
            );
            assert_eq!(
                data.iter()
                    .filter(|row| row[3] == "true"
                        && row[7] == "false"
                        && row[8] == "unattempted"
                        && row[9] == "ParameterNotAttempted")
                    .count(),
                2
            );
            // A candidate's name is not enough: one changed plan is no longer
            // the exact selected native candidate, with model/table unchanged.
            let bundle = candidates.bundles.values_mut().next().unwrap();
            bundle
                .plan
                .receipts
                .push("audit-test-stale-plan".to_owned());
            let changed = candidates.audit(tcx, &ctx.slots, &ctx.model, &table);
            assert_eq!(
                rows(&changed)
                    .iter()
                    .filter(|row| row[8] == "not-selected")
                    .count(),
                1
            );
        })
        .unwrap();
    }

    #[test]
    fn native_audit_keeps_typed_source_hold_beside_primary_reason() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt",
            "let a=pl1.offset(1); let b=pl2.offset(1); *a=*b; edt(pl1,pl2);",
        );
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let program = bo::collect_program(tcx);
            let candidates = Candidates::derive(
                &Inputs {
                    program: &program,
                    slots: &ctx.slots,
                    model: &ctx.model,
                    constructions: &ctx.constructions,
                    sites: &ctx.raw_boundary_sites,
                    retention: &ctx.retention,
                    a5: &ctx.a5_site_proofs,
                },
                &table,
                &ClassFinalization::default(),
            );
            assert_eq!(candidates.holds.len(), 2, "actual unsupported cursor uses");
            let audit = candidates.audit(tcx, &ctx.slots, &ctx.model, &table);
            let data = rows(&audit);
            assert_eq!(data.len(), 4);
            let held: Vec<_> = data.iter().filter(|row| row[8] == "held").collect();
            assert_eq!(held.len(), 2);
            assert!(held.iter().all(|row| row[7] == "true"
                && row[9] == "Source::UnsupportedOwnerUse"
                && row[10].contains("UnsupportedOwnerUse")
                && row[11] == "box-param-caller-unknown"));
        })
        .unwrap();
    }

    #[test]
    fn r376_synthetic_terminal_slice_renders_lend_and_recovery_invalidates_owner() {
        use crate::bo_rewriter::bridge_receipt::SignatureClassId;

        let input =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);");
        let carrier = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
            let (mut table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let original_model = ctx.model.clone();
            let program = bo::collect_program(tcx);
            let callee = *program
                .functions
                .iter()
                .find(|id| tcx.def_path_str(id.to_def_id()) == "edt")
                .unwrap();
            let mut classes =
                bo::prepare_plan_files(tcx, &table, &FxHashSet::default(), &ctx.retained_c9_plans)
                    .unwrap()
                    .plan
                    .class_finalization;
            // Mechanical terminal-class snapshot only: source identities,
            // ownership model, native effects, T1 and A5 remain real. These
            // inserted Slice decisions are not native slice grants.
            let mut changed = 0;
            for (subject, decision) in &mut table.entries {
                if subject.fn_did == callee && matches!(subject.kind, SubjectKind::Param { .. }) {
                    *decision = Decision::Slice {
                        mutable: true,
                        uses: Vec::new(),
                    };
                    changed += 1;
                }
            }
            assert_eq!(changed, 2);
            let id = SignatureClassId::of(callee);
            classes.classes.insert(
                id,
                bo::plan::SignatureClassPlan {
                    id,
                    required_arms: Default::default(),
                    site_keys: Vec::new(),
                    edit_keys: Vec::new(),
                    depends_on: Vec::new(),
                    disposition: bo::plan::SignatureClassDisposition::Ready,
                    sites: Vec::new(),
                },
            );
            let inputs = Inputs {
                program: &program,
                slots: &ctx.slots,
                model: &ctx.model,
                constructions: &ctx.constructions,
                sites: &ctx.raw_boundary_sites,
                retention: &ctx.retention,
                a5: &ctx.a5_site_proofs,
            };
            let effects = NativeEffects::derive(&program);
            let mut candidates = Candidates::default();
            let mut arguments = std::collections::BTreeMap::new();
            let mut owners = FxHashSet::default();
            for (subject, _) in &table.entries {
                let Some(name @ ("pl1" | "pl2")) = subject.param_name.as_deref() else {
                    continue;
                };
                assert!(outer_owning(&ctx.slots, &ctx.model, subject));
                let source = source::derive(&program, subject, &ctx.constructions).unwrap();
                let bundle =
                    derive_bundle(&inputs, &table, &classes, &effects, subject, &source, false)
                        .unwrap();
                assert_eq!(bundle.formals.len(), 1);
                assert_eq!(bundle.formals[0].emitted(), FormalForm::MutableReference);
                assert_eq!(
                    bundle.formals[0].terminal(),
                    super::super::seam::Form::Slice { mutable: true }
                );
                let edits: Vec<_> = bundle
                    .plan
                    .expr_edits
                    .iter()
                    .filter(|edit| edit.receipt == "native-box-lend-t1")
                    .collect();
                assert_eq!(edits.len(), 1);
                assert_eq!(edits[0].replacement, format!("&mut *({name})"));
                arguments.insert(name.to_owned(), edits[0].replacement.clone());
                owners.insert(subject.fn_did);
                candidates
                    .bundles
                    .insert((subject.fn_did, subject.hir_id), bundle);
            }
            assert_eq!(candidates.bundles.len(), 2);
            for (subject, decision) in &mut table.entries {
                if let Some(bundle) = candidates.bundles.get(&(subject.fn_did, subject.hir_id)) {
                    *decision = Decision::Box(bundle.plan.clone());
                }
            }
            assert!(
                candidates
                    .invalid_owners(&inputs, &table, &classes)
                    .is_empty()
            );
            classes.classes.get_mut(&id).unwrap().disposition =
                bo::plan::SignatureClassDisposition::Held(vec!["synthetic-slice-recovery".into()]);
            assert_eq!(candidates.invalid_owners(&inputs, &table, &classes), owners);
            for bundle in candidates.bundles.values() {
                let proof = &bundle.formals[0];
                let (callee, argument) = proof.identity();
                let recovered = formal::resolve(
                    tcx, &ctx.slots, &ctx.model, &table, &classes, callee, argument,
                )
                .unwrap();
                assert_eq!(recovered.terminal(), super::super::seam::Form::Raw);
                assert_ne!(&recovered, proof);
            }
            assert_eq!(ctx.model, original_model);
            format!(
                "fn edt(input: &mut [f32], output: &mut [f32]) {{ output[0] = input[0]; }}\n\
                 fn main() {{ let mut pl1: Box<[f32]> = vec![1.0; 2].into_boxed_slice();\n\
                 let mut pl2: Box<[f32]> = vec![0.0; 2].into_boxed_slice();\n\
                 edt({}, {}); drop(pl1); drop(pl2); }}",
                arguments["pl1"], arguments["pl2"],
            )
        })
        .unwrap();
        assert!(bo::verify::type_checks_str(&carrier));
    }
}
