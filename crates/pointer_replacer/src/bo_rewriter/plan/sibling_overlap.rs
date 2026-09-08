//! Terminal R233 stamping, independent of class edits and holds.

use std::collections::BTreeSet;

use rustc_span::Span;

use super::super::{
    bridge_receipt::{BridgeCalleeId, BridgeSiteKey, SignatureClassId},
    decision::{
        DecisionTable, SubjectKind,
        seam::Form,
        sibling_overlap::{
            self, CoverageGapReceipt, PendingSiblingReceipt, SiblingPotential,
            SourceBridgeCoverage, SourceBridgeEvidence, TerminalSiteState,
        },
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PendingSite {
    pub site: Result<BridgeSiteKey, String>,
    pub receipt: PendingSiblingReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Endpoint {
    class: Option<SignatureClassId>,
    input: Form,
    placed: Option<Form>,
    atoms: Vec<String>,
}

impl Endpoint {
    fn live(
        &self,
        plan: &super::Plan,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> bool {
        self.atoms.iter().all(|atom| !atoms.contains(atom))
            && self.class.is_some_and(|class| {
                !reverted.contains(&class)
                    && plan
                        .class_finalization
                        .classes
                        .get(&class)
                        .is_some_and(super::SignatureClassPlan::is_ready)
            })
    }

    fn form(
        &self,
        plan: &super::Plan,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Form {
        super::super::terminal_interface_form(
            self.input,
            self.placed,
            self.live(plan, reverted, atoms),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SiblingReceiptPlan {
    potential: SiblingPotential,
    evidence: SourceBridgeEvidence,
    site: Result<BridgeSiteKey, String>,
    source: Endpoint,
    target: Endpoint,
}

pub(crate) fn plans(
    table: &DecisionTable,
    locate: &impl Fn(Span) -> Result<(super::FileKey, usize, usize), &'static str>,
) -> Vec<SiblingReceiptPlan> {
    table.sibling_overlap_inventory.coverage.iter().map(|coverage| {
        let potential = &coverage.potential;
        let source_key = (potential.source.fn_did, potential.source.hir_id);
        let source = Endpoint {
            class: Some(SignatureClassId::of(potential.caller)),
            atoms: table.seams.raw_boundary_atom_groups.get(&source_key).into_iter().flatten().map(|atom| atom.id.clone()).collect(),
            input: table.input_interfaces.subject_forms.get(&source_key).copied().unwrap_or(Form::Raw),
            placed: table.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == source_key)
                .and_then(|(_, choice)| super::super::terminal_application(choice, true))
                .map(super::super::decision::seam::form_of),
        };
        let target = potential.callee.as_local().map(|callee| Endpoint {
            class: Some(SignatureClassId::of(callee)),
            atoms: table.entries.iter().find(|(subject, _)| subject.fn_did == callee
                && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == potential.site.argument_index))
                .and_then(|(subject, _)| table.seams.raw_boundary_atom_groups.get(&(subject.fn_did, subject.hir_id)))
                .into_iter().flatten().map(|atom| atom.id.clone()).collect(),
            input: table.input_interfaces.parameter_forms.get(&(callee, potential.site.argument_index))
                .copied().unwrap_or(Form::Raw),
            placed: table.entries.iter().find(|(subject, _)| subject.fn_did == callee
                && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == potential.site.argument_index))
                .and_then(|(_, choice)| super::super::terminal_application(choice, true))
                .map(super::super::decision::seam::form_of),
        }).unwrap_or(Endpoint { class: None, input: Form::Raw, placed: None, atoms: Vec::new() });
        let site = locate(potential.argument_span).map(|(file, lo, hi)| BridgeSiteKey {
            owner_class: SignatureClassId::of(potential.caller), caller: potential.caller,
            callee: potential.callee.as_local().map(BridgeCalleeId::Local)
                .unwrap_or_else(|| BridgeCalleeId::Foreign(potential.site.callee.path.clone())),
            arm: "sibling-overlap".into(), position: format!("arg{}", potential.site.argument_index),
            file: super::file_key_label(&file), lo: lo as u32, hi: hi as u32,
            bridge_kind: sibling_overlap::PENDING_REASON.into(),
        }).map_err(|why| format!("pending-sibling-site-unmapped:{}:{why}", super::super::decision::raw_boundary::site_atom_id(&potential.site)));
        SiblingReceiptPlan { potential: potential.clone(), evidence: coverage.evidence.clone(), site, source, target }
    }).collect()
}

impl super::Plan {
    pub(crate) fn pending_sibling_receipts(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
    ) -> Vec<PendingSite> {
        self.pending_sibling_receipts_with_atoms(reverted, &BTreeSet::new())
    }

    pub(crate) fn pending_sibling_receipts_with_atoms(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Vec<PendingSite> {
        self.sibling_receipt_plans
            .iter()
            .filter(|row| {
                matches!(
                    row.evidence,
                    SourceBridgeEvidence::WholeSubject
                        | SourceBridgeEvidence::ProjectedReferent { .. }
                        | SourceBridgeEvidence::TypedView { .. }
                )
            })
            .flat_map(|row| {
                sibling_overlap::select_pending(std::slice::from_ref(&row.potential), |_| {
                    TerminalSiteState {
                        source_form: row.source.form(self, reverted, atoms),
                        target_form: row.target.form(self, reverted, atoms),
                        source_delivered: row.source.placed.is_some()
                            && row.source.live(self, reverted, atoms),
                    }
                })
                .into_iter()
                .map(|receipt| PendingSite {
                    site: row.site.clone(),
                    receipt,
                })
            })
            .collect()
    }
}

impl super::Plan {
    pub(crate) fn sibling_coverage_gaps(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
    ) -> Vec<CoverageGapReceipt> {
        self.sibling_coverage_gaps_with_atoms(reverted, &BTreeSet::new())
    }

    pub(crate) fn sibling_coverage_gaps_with_atoms(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Vec<CoverageGapReceipt> {
        self.sibling_receipt_plans
            .iter()
            .flat_map(|row| {
                let coverage = SourceBridgeCoverage {
                    potential: row.potential.clone(),
                    evidence: row.evidence.clone(),
                };
                sibling_overlap::select_coverage_gaps(std::slice::from_ref(&coverage), |_| {
                    TerminalSiteState {
                        source_form: row.source.form(self, reverted, atoms),
                        target_form: row.target.form(self, reverted, atoms),
                        source_delivered: row.source.placed.is_some()
                            && row.source.live(self, reverted, atoms),
                    }
                })
            })
            .collect()
    }
}
