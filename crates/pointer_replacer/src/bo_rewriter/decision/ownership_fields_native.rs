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
    formals: Vec<NativeFormal>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Candidates {
    bundles: FxHashMap<Node, Bundle>,
    pub(crate) holds: FxHashMap<Node, NativeHold>,
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
                | Decision::Cursor { .. }
                | Decision::Opt { .. }
                | Decision::Box(_) => continue,
            };
            let super::DegradeReason::BoxFailure {
                failure: BoxPlanFailure::NativeEvidenceHeld { prior_key, .. },
            } = &degraded.reason
            else {
                continue;
            };
            if *prior_key != "box-param-caller-unknown" {
                continue;
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
                    derive_bundle(inputs, table, classes, &effects, subject, &source)
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
                        && !stable_raw_formal(table, callee, argument))
                {
                    invalid.insert(node.0);
                }
            }
        }
        invalid
    }
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

fn derive_bundle(
    inputs: &Inputs<'_, '_>,
    table: &DecisionTable,
    classes: &ClassFinalization,
    effects: &NativeEffects<'_>,
    subject: &super::Subject,
    source: &SourcePlan,
) -> Result<Bundle, NativeHold> {
    if source.calls().is_empty() {
        return Err(NativeHold::Missing("native-lend-call-inventory"));
    }
    let tcx = inputs.program.tcx;
    let name = subject.param_name.as_ref().ok_or(NativeHold::Identity)?;
    let mut edits = vec![source.constructor().clone()];
    edits.extend_from_slice(source.scalar_edits());
    let mut receipts = vec![format!(
        "native-owning-source owner={} local={} generation=Missing source-root={:?}",
        subject.fn_did.local_def_index.as_u32(),
        subject.local.as_u32(),
        subject.hir_id
    )];
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
        let matching: Vec<_> = inputs
            .sites
            .sites
            .iter()
            .filter(|site| {
                site.node == Some((subject.fn_did, subject.hir_id))
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
        if site.callee_may_yield_pointer {
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
        let lend_expression = match (emitted.emitted(), emitted.terminal()) {
            (FormalForm::MutableRaw, super::seam::Form::Raw)
                if stable_raw_formal(table, callee, argument) =>
            {
                format!("<[_]>::as_mut_ptr(&mut *({name}))")
            }
            (FormalForm::MutableReference, super::seam::Form::Slice { mutable: true }) => {
                format!("&mut *({name})")
            }
            _ => return Err(NativeHold::FinalInterface),
        };
        formal::require_nonconsuming(effects, &emitted).map_err(NativeHold::Call)?;
        let Some(RetentionVerdict::NoRetain { certificate }) =
            inputs.retention.get(callee, argument)
        else {
            return Err(NativeHold::Call(Hold::Lend(LendHold::Retention)));
        };
        inputs
            .retention
            .verify_certificate(callee, argument, certificate)
            .map_err(|_| NativeHold::Call(Hold::Lend(LendHold::Retention)))?;
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
        if !sig.output().is_unit()
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
        receipts.push(format!("native-box-call-scalar-evaluation {key:?} arguments={scalar_indices:?} effect-free=literal-local-cast"));
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
                return Err(NativeHold::Peer(proof.reason));
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
            receipt: "native-box-lend-t1",
        });
        receipts.push(format!("native-box-lend {:?} arg={argument} formal_model={:?} emitted={} T1=verified nonconsuming=verified interval=argument-list-through-return protector=call source-reference-inventory=complete",key,emitted.model_kind(),emitted.terminal().key()));
        checked_calls.insert(key);
        formals.push(emitted);
    }
    // SourcePlan proves a fresh numeric root per allocation occurrence, no source aliases/escaping storage,
    // no reference-taking or rebinding, and all normal paths through its exact
    // C free. Each owner-using call above is separately proved nonretaining and
    // nonconsuming. That completes the all-roots account for extra unwinding
    // closes of this scalar root; it is not inferred from an empty loan set.
    for at in source.unwind_obligations() {
        receipts.push(format!("native-unwind-close-permit source-call={at:?} all-roots=fresh-local-closed-uses-and-verified-T1 payload={}/nonrecursive; actual-waiver-sites=emitted-MIR-ledger",source.element()));
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
    receipts.push(format!("native-box-continuations calls={checked_calls:?} free_keys={required:?} scope-exit=exact-C-free"));
    Ok(Bundle {
        plan: BoxPlan {
            shape: BoxShape::Slice,
            optional: false,
            expr_edits: edits,
            delete_statements: Vec::new(),
            receipts,
            fabricated_extent: false,
            pointee_override: None,
            inferred_binding: subject.ty_span.is_none(),
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
                    derive_bundle(&inputs, &table, &classes, &effects, subject, &source).unwrap();
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
