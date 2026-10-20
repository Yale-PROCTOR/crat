//! Terminal R233 stamping, independent of class edits and holds.

use std::collections::BTreeSet;

use rustc_span::Span;

use super::super::{
    bridge_receipt::{BridgeCalleeId, BridgeSiteKey, SignatureClassId},
    decision::{
        DecisionTable, SubjectKind,
        seam::Form,
        sibling_overlap::{
            self, CoverageGapReceipt, PendingSiblingReceipt, SiblingPotential, SiblingSource,
            SourceBridgeCoverage, SourceBridgeEvidence, TerminalSiteState,
        },
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PendingSite {
    pub site: Result<BridgeSiteKey, String>,
    pub receipt: PendingSiblingReceipt,
    /// **R287-1(b) — what the tree carries at this call.**
    ///
    /// A pending site is a DELIVERED site, so its ledger row owes the emitted
    /// call, not a hint from which the comparator might reconstruct one. The
    /// producer states the call's original interval and every edit it planned
    /// inside that interval; applying the second to the first is the emitted
    /// text, exactly.
    ///
    /// This is what replaces `pending-call-correspondence-not-unique`. The old
    /// matcher searched the emitted tree for the *unique* structurally
    /// corresponding call and failed whenever an owner had two — a uniqueness
    /// requirement that was never the property custody needs. With the text
    /// stated, two identical calls stop being a failure, because either one
    /// satisfies custody.
    pub emitted_call: Result<EmittedCall, String>,
    /// R287-1(c) — one entry per pointer sibling argument, no gaps.
    pub siblings: Vec<SiblingDisposition>,
}

/// The original call interval plus the edits planned inside it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EmittedCall {
    pub file: super::FileKey,
    pub lo: usize,
    pub hi: usize,
    /// Sorted, non-overlapping, file-relative. Rendering is
    /// [`EmittedCall::render`].
    pub edits: Vec<(usize, usize, String)>,
}

/// What the plan did with one sibling argument of a pending call.
///
/// Every pointer sibling gets one of these. "No row" is not a disposition —
/// that is the `sibling-audit:incomplete-row` defect R287-1 classifies as
/// producer-side, and the comparator must never be taught to accept it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SiblingDisposition {
    /// An edit under a ready class rewrites this argument; the string is that
    /// edit's custody identity.
    Bridged {
        argument_index: usize,
        custody_identity: String,
    },
    /// The subject behind this argument is refused, with its typed reason —
    /// `held:thin-extent` and its kin.
    Held {
        argument_index: usize,
        reason: String,
    },
    /// No edit and no refusal: the original text stands.
    RawUnchanged { argument_index: usize },
}

impl SiblingDisposition {
    pub(crate) fn argument_index(&self) -> usize {
        match self {
            Self::Bridged { argument_index, .. }
            | Self::Held { argument_index, .. }
            | Self::RawUnchanged { argument_index } => *argument_index,
        }
    }

    pub(crate) fn key(&self) -> &'static str {
        match self {
            Self::Bridged { .. } => "bridged",
            Self::Held { .. } => "held",
            Self::RawUnchanged { .. } => "raw-unchanged",
        }
    }
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
    /// R287-1(b): the call's own interval, located at plan time beside the
    /// argument interval `site` already carries.
    call: Result<(super::FileKey, usize, usize), String>,
    /// R287-1(c): each sibling's argument interval, located at the same time
    /// and by the same closure. `None` is missing capture, carried as such.
    sibling_spans: Vec<(usize, Option<(super::FileKey, usize, usize)>)>,
}

pub(crate) fn plans(
    table: &DecisionTable,
    locate: &impl Fn(Span) -> Result<(super::FileKey, usize, usize), &'static str>,
) -> Vec<SiblingReceiptPlan> {
    table.sibling_overlap_inventory.coverage.iter().map(|coverage| {
        let potential = &coverage.potential;
        let source = match &potential.source {
            SiblingSource::Declared(subject) => {
                let source_key = (subject.fn_did, subject.hir_id);
                Endpoint {
                    class: Some(SignatureClassId::of(potential.caller)),
                    atoms: table.seams.raw_boundary_atom_groups.get(&source_key).into_iter().flatten().map(|atom| atom.id.clone()).collect(),
                    input: table.input_interfaces.subject_forms.get(&source_key).copied().unwrap_or(Form::Raw),
                    placed: table.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == source_key)
                        .and_then(|(_, choice)| super::super::terminal_application(choice, true))
                        .map(super::super::decision::seam::form_of),
                }
            }
            SiblingSource::NativeReturnExpression { source_callee, source_interface, .. } => Endpoint {
                class: Some(SignatureClassId::of(*source_callee)),
                // Return-origin atom closure has already normalized classes.
                atoms: Vec::new(),
                input: Form::Raw,
                placed: Some(source_interface.form),
            },
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
            owner_class: potential.source.owner_class(), caller: potential.caller,
            callee: potential.callee.as_local().map(BridgeCalleeId::Local)
                .unwrap_or_else(|| BridgeCalleeId::Foreign(potential.site.callee.path.clone())),
            arm: "sibling-overlap".into(), position: format!("arg{}", potential.site.argument_index),
            file: super::file_key_label(&file), lo: lo as u32, hi: hi as u32,
            bridge_kind: sibling_overlap::PENDING_REASON.into(),
        }).map_err(|why| format!("pending-sibling-site-unmapped:{}:{why}", super::super::decision::raw_boundary::site_atom_id(&potential.site)));
        let call = locate(potential.call_span).map_err(|why| format!("pending-sibling-call-unmapped:{}:{why}", super::super::decision::raw_boundary::site_atom_id(&potential.site)));
        let sibling_spans = potential.siblings.iter().map(|sibling| {
            (sibling.argument_index, sibling.argument_span.and_then(|span| locate(span).ok()))
        }).collect();
        SiblingReceiptPlan { potential: potential.clone(), evidence: coverage.evidence.clone(), site, source, target, call, sibling_spans }
    }).collect()
}

impl super::Plan {
    pub(crate) fn sibling_audit_rows_with_atoms(
        &self,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Vec<super::super::sibling_audit::Row> {
        let reverted = self.effective_reverted_classes(reverted, atoms);
        let inputs = self
            .sibling_receipt_plans
            .iter()
            .map(|row| super::super::sibling_audit::Input {
                site: row.site.clone(),
                potential: row.potential.clone(),
                source_evidence: row.evidence.clone(),
                terminal: TerminalSiteState {
                    source_form: row.source.form(self, &reverted, atoms),
                    target_form: row.target.form(self, &reverted, atoms),
                    source_delivered: row.source.placed.is_some()
                        && row.source.live(self, &reverted, atoms),
                },
            })
            .collect::<Vec<_>>();
        super::super::sibling_audit::audit(&inputs)
    }

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
        let effective_reverted = self.effective_reverted_classes(reverted, atoms);
        let reverted = &effective_reverted;
        self.sibling_receipt_plans
            .iter()
            .filter(|row| {
                matches!(
                    row.evidence,
                    SourceBridgeEvidence::WholeSubject
                        | SourceBridgeEvidence::ProjectedReferent { .. }
                        | SourceBridgeEvidence::TypedView { .. }
                        | SourceBridgeEvidence::NativeReturnExpression { .. }
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
                    emitted_call: self.emitted_call_of(row, reverted, atoms),
                    siblings: self.sibling_dispositions_of(row, reverted, atoms),
                    receipt,
                })
            })
            .collect()
    }
}

impl super::Plan {
    /// R287-1(b): the call's interval plus every planned edit inside it, from
    /// the classes that are actually ready at this revert state.
    ///
    /// Only edits under a live class are recorded, because a reverted class's
    /// edit is not in the tree — the same filter `by_file` applies at
    /// finalization, applied here at the same revert state the receipt is
    /// computed for.
    fn emitted_call_of(
        &self,
        row: &SiblingReceiptPlan,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Result<EmittedCall, String> {
        // A native-return-expression source hoists its carrier into a
        // statement BEFORE the call, so the call's emitted text is not stated
        // by the edits inside the call interval. That shape already has its
        // own custody arm (`PendingSourceShape::NativeReturnExpression`), and
        // R287-1 leaves existing arms alone, so this row claims no call text
        // for it — only the sibling dispositions, which it does own.
        if !matches!(row.potential.source, SiblingSource::Declared(_)) {
            return Err(format!(
                "pending-sibling-call-not-claimed:native-return-expression:{}",
                super::super::decision::raw_boundary::site_atom_id(&row.potential.site)
            ));
        }
        let (file, lo, hi) = row.call.clone()?;
        let mut edits = self
            .by_file
            .get(&file)
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .filter(|edit| lo <= edit.lo && edit.hi <= hi)
            .filter(|edit| {
                edit.owner_class.is_none_or(|class| {
                    !reverted.contains(&class)
                        && self
                            .class_finalization
                            .classes
                            .get(&class)
                            .is_some_and(super::SignatureClassPlan::is_ready)
                })
            })
            .filter(|edit| edit.atom_ids.iter().all(|atom| !atoms.contains(atom)))
            .map(|edit| (edit.lo, edit.hi, edit.replacement.clone()))
            .collect::<Vec<_>>();
        // Sorted outermost-first at each position: a composed nested pair
        // (L07) legitimately puts an inner edit inside an outer one, and the
        // renderer splices them the way the AST layer does. A true crossing is
        // not sorted away here — the renderer rejects it.
        edits.sort_by_key(|(lo, hi, _)| (*lo, std::cmp::Reverse(*hi)));
        Ok(EmittedCall {
            file,
            lo,
            hi,
            edits,
        })
    }

    /// R287-1(c): one disposition per pointer sibling, never a gap.
    fn sibling_dispositions_of(
        &self,
        row: &SiblingReceiptPlan,
        reverted: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Vec<SiblingDisposition> {
        let Ok((file, _, _)) = row.call.clone() else {
            return Vec::new();
        };
        let mut out = row
            .potential
            .siblings
            .iter()
            .map(|sibling| {
                let index = sibling.argument_index;
                let span = row
                    .sibling_spans
                    .iter()
                    .find(|(candidate, _)| *candidate == index)
                    .and_then(|(_, located)| located.as_ref())
                    .filter(|(sibling_file, _, _)| *sibling_file == file)
                    .map(|(_, lo, hi)| (*lo, *hi));
                let edit = self
                    .by_file
                    .get(&file)
                    .map_or(&[][..], Vec::as_slice)
                    .iter()
                    .filter(|edit| {
                        edit.owner_class.is_none_or(|class| {
                            !reverted.contains(&class)
                                && self
                                    .class_finalization
                                    .classes
                                    .get(&class)
                                    .is_some_and(super::SignatureClassPlan::is_ready)
                        })
                    })
                    .filter(|edit| edit.atom_ids.iter().all(|atom| !atoms.contains(atom)))
                    .find(|edit| span.is_some_and(|(lo, hi)| lo <= edit.lo && edit.hi <= hi));
                if let Some(edit) = edit {
                    return SiblingDisposition::Bridged {
                        argument_index: index,
                        custody_identity: edit.bridge.as_ref().map_or_else(
                            || format!("edit:{}:{}", edit.lo, edit.hi),
                            |bridge| format!("{}:{}", bridge.arm, bridge.position),
                        ),
                    };
                }
                // A refusal is recorded by the plan as a DROPPED class site
                // over the same interval, carrying its typed reason. That is
                // the plan's own statement of the hold, so the disposition is
                // read from it rather than re-derived.
                let label = super::file_key_label(&file);
                let held = self
                    .class_finalization
                    .classes
                    .values()
                    .flat_map(|class| class.sites.iter())
                    .filter(|class_site| class_site.key.file == label)
                    .find_map(|class_site| match (&class_site.state, span) {
                        (super::ClassSiteState::Dropped(reason), Some((lo, hi)))
                            if lo as u32 <= class_site.key.lo && class_site.key.hi <= hi as u32 =>
                        {
                            Some(reason.clone())
                        }
                        _ => None,
                    });
                match held {
                    Some(reason) => SiblingDisposition::Held {
                        argument_index: index,
                        reason,
                    },
                    None => SiblingDisposition::RawUnchanged {
                        argument_index: index,
                    },
                }
            })
            .collect::<Vec<_>>();
        out.sort_by_key(SiblingDisposition::argument_index);
        out.dedup_by_key(|disposition| disposition.argument_index());
        out
    }

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
        let effective_reverted = self.effective_reverted_classes(reverted, atoms);
        let reverted = &effective_reverted;
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
