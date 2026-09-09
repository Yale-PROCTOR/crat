//! Owned predicate-input receipts for every R233 coverage record, including
//! nonpending sites. This report neither selects bridges nor changes holds.

use serde::{Deserialize, Serialize};

use super::{
    bridge_receipt::{BridgeCalleeId, BridgeSiteKey},
    decision::{
        a5_site_proof::{A5ProofSiteKey, A5SiteProofVerdict},
        seam::Form,
        sibling_overlap::{
            self, LocalPostCallEvidence, SiblingAccess, SiblingPotential, SiblingSource,
            SourceBridgeCoverage, SourceBridgeEvidence, TerminalSiteState,
        },
    },
};

#[derive(Clone, Debug)]
pub(crate) struct Input {
    pub(crate) site: Result<BridgeSiteKey, String>,
    pub(crate) potential: SiblingPotential,
    pub(crate) source_evidence: SourceBridgeEvidence,
    pub(crate) terminal: TerminalSiteState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ProofSite {
    pub(crate) caller: u32,
    pub(crate) block: u32,
    pub(crate) statement_index: usize,
    pub(crate) callee_crate: u32,
    pub(crate) callee_definition: u32,
    pub(crate) argument_index: usize,
    pub(crate) slot_depth: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum A5Outcome {
    Clear,
    Overlapping,
    Undeterminable,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct A5Audit {
    pub(crate) outcome: A5Outcome,
    pub(crate) reason: String,
    pub(crate) family: String,
    pub(crate) location: Option<(u32, usize)>,
    pub(crate) left_site: Option<ProofSite>,
    pub(crate) right_site: Option<ProofSite>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum Access {
    Foster {
        local: u32,
        mutable: bool,
        defaulted: bool,
    },
    Contract {
        access: String,
        provenance: String,
    },
    Unknown {
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Sibling {
    pub(crate) argument_index: usize,
    pub(crate) argument_shape: Option<String>,
    /// Mandatory: a captured Undeterminable is not absent proof data.
    pub(crate) proof: A5Audit,
    pub(crate) access: Access,
    pub(crate) risky: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum PostCall {
    ParameterProtected,
    ParameterOrigin { parameters: Vec<usize> },
    Live { locals: Vec<u32> },
    DeadUnprotected { checked_locals: Vec<u32> },
    Unknown { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum SourceEvidence {
    WholeSubject,
    ProjectedReferent {
        hir_owner: u32,
        hir_local: u32,
    },
    TypedView {
        hir_owner: u32,
        hir_local: u32,
        method_crate: u32,
        method_definition: u32,
    },
    NativeReturnExpression {
        hir_owner: u32,
        hir_local: u32,
    },
    RawFieldValue,
    BindingStorage,
    UnknownShape {
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum SubjectKind {
    Parameter { hir_index: usize },
    Local,
    NativeReturnExpression,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct NativeReturnSource {
    pub(crate) source_owner: u32,
    pub(crate) source_form: String,
    pub(crate) pointee: String,
    pub(crate) lifetime: String,
    pub(crate) lifetime_plan_digest: String,
    pub(crate) temporary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Source {
    pub(crate) identity: String,
    pub(crate) label: String,
    pub(crate) kind: SubjectKind,
    /// Some retains the declared-row numeric JSON representation. A missing
    /// expression operand is explicit None, never an invented local zero.
    pub(crate) mir_local: Option<u32>,
    pub(crate) hir_owner: u32,
    pub(crate) hir_local: u32,
    pub(crate) argument_shape: String,
    pub(crate) evidence: SourceEvidence,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) native_return: Option<NativeReturnSource>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Terminal {
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) source_delivered: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Outcome {
    SourceNotDelivered,
    SourceRaw,
    TargetSafe,
    RawFieldValue,
    BindingStorage,
    DeadUnprotected,
    NoRiskySibling,
    PendingWaiver,
    CoverageGap,
    IncompleteCapture,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Row {
    pub(crate) coverage_id: String,
    pub(crate) receipt_key: Option<String>,
    pub(crate) file: Option<String>,
    pub(crate) argument_span: Option<(u32, u32)>,
    pub(crate) call_global_span: (u32, u32),
    pub(crate) caller: String,
    pub(crate) callee: String,
    pub(crate) block: u32,
    pub(crate) statement_index: usize,
    pub(crate) argument_index: usize,
    pub(crate) source: Source,
    pub(crate) siblings: Vec<Sibling>,
    pub(crate) post_call: PostCall,
    pub(crate) terminal: Terminal,
    pub(crate) outcome: Outcome,
    pub(crate) data: bool,
    pub(crate) issues: Vec<String>,
}

fn proof_site(site: A5ProofSiteKey) -> ProofSite {
    ProofSite {
        caller: site.caller.local_def_index.as_u32(),
        block: site.location.block,
        statement_index: site.location.statement_index,
        callee_crate: site.callee.krate.as_u32(),
        callee_definition: site.callee.index.as_u32(),
        argument_index: site.argument_index,
        slot_depth: site.slot_depth,
    }
}

fn source_evidence(evidence: &SourceBridgeEvidence) -> SourceEvidence {
    match evidence {
        SourceBridgeEvidence::WholeSubject => SourceEvidence::WholeSubject,
        SourceBridgeEvidence::ProjectedReferent { use_hir_id } => {
            SourceEvidence::ProjectedReferent {
                hir_owner: use_hir_id.owner.def_id.local_def_index.as_u32(),
                hir_local: use_hir_id.local_id.as_u32(),
            }
        }
        SourceBridgeEvidence::TypedView { use_hir_id, method } => SourceEvidence::TypedView {
            hir_owner: use_hir_id.owner.def_id.local_def_index.as_u32(),
            hir_local: use_hir_id.local_id.as_u32(),
            method_crate: method.krate.as_u32(),
            method_definition: method.index.as_u32(),
        },
        SourceBridgeEvidence::NativeReturnExpression { use_hir_id } => {
            SourceEvidence::NativeReturnExpression {
                hir_owner: use_hir_id.owner.def_id.local_def_index.as_u32(),
                hir_local: use_hir_id.local_id.as_u32(),
            }
        }
        SourceBridgeEvidence::RawFieldValue => SourceEvidence::RawFieldValue,
        SourceBridgeEvidence::BindingStorage => SourceEvidence::BindingStorage,
        SourceBridgeEvidence::UnknownShape(reason) => SourceEvidence::UnknownShape {
            reason: (*reason).into(),
        },
    }
}

fn outcome(input: &Input) -> Outcome {
    let potential = &input.potential;
    let represented_source = matches!(
        input.source_evidence,
        SourceBridgeEvidence::WholeSubject
            | SourceBridgeEvidence::ProjectedReferent { .. }
            | SourceBridgeEvidence::TypedView { .. }
            | SourceBridgeEvidence::NativeReturnExpression { .. }
    );
    if represented_source
        && !sibling_overlap::select_pending(std::slice::from_ref(potential), |_| input.terminal)
            .is_empty()
    {
        return Outcome::PendingWaiver;
    }
    let coverage = SourceBridgeCoverage {
        potential: potential.clone(),
        evidence: input.source_evidence.clone(),
    };
    if !sibling_overlap::select_coverage_gaps(&[coverage], |_| input.terminal).is_empty() {
        return Outcome::CoverageGap;
    }
    if !input.terminal.source_delivered {
        return Outcome::SourceNotDelivered;
    }
    if input.terminal.source_form == Form::Raw {
        return Outcome::SourceRaw;
    }
    if input.terminal.target_form != Form::Raw {
        return Outcome::TargetSafe;
    }
    match input.source_evidence {
        SourceBridgeEvidence::RawFieldValue => return Outcome::RawFieldValue,
        SourceBridgeEvidence::BindingStorage => return Outcome::BindingStorage,
        SourceBridgeEvidence::WholeSubject
        | SourceBridgeEvidence::ProjectedReferent { .. }
        | SourceBridgeEvidence::TypedView { .. }
        | SourceBridgeEvidence::NativeReturnExpression { .. }
        | SourceBridgeEvidence::UnknownShape(_) => {}
    }
    if matches!(
        potential.local_post_call,
        LocalPostCallEvidence::DeadUnprotected { .. }
    ) {
        Outcome::DeadUnprotected
    } else {
        Outcome::NoRiskySibling
    }
}

pub(crate) fn audit(inputs: &[Input]) -> Vec<Row> {
    let mut counts = std::collections::BTreeMap::<String, usize>::new();
    for input in inputs {
        *counts
            .entry(super::decision::raw_boundary::site_atom_id(
                &input.potential.site,
            ))
            .or_default() += 1;
    }
    inputs
        .iter()
        .map(|input| {
            let potential = &input.potential;
            let coverage_id = super::decision::raw_boundary::site_atom_id(&potential.site);
            let mut issues = Vec::new();
            if counts[&coverage_id] != 1 {
                issues.push(format!("sibling-audit:duplicate-coverage-id:{coverage_id}"));
            }
            let (receipt_key, file, argument_span) = match &input.site {
                Ok(site) => {
                    let callee_matches = match &site.callee {
                        BridgeCalleeId::Local(callee) => {
                            potential.callee.as_local() == Some(*callee)
                        }
                        BridgeCalleeId::Foreign(callee) => *callee == potential.site.callee.path,
                    };
                    if site.caller != potential.caller
                        || site.owner_class != potential.source.owner_class()
                        || potential.source.caller() != potential.caller
                        || !callee_matches
                        || site.position != format!("arg{}", potential.site.argument_index)
                        || site.hi <= site.lo
                    {
                        issues.push(format!("sibling-audit:site-mapping-mismatch:{coverage_id}"));
                    }
                    (
                        Some(site.receipt_key()),
                        Some(site.file.clone()),
                        Some((site.lo, site.hi)),
                    )
                }
                Err(error) => {
                    issues.push(format!("sibling-audit:site-mapping:{coverage_id}:{error}"));
                    (None, None, None)
                }
            };
            let siblings = potential
                .siblings
                .iter()
                .map(|sibling| {
                    if sibling.argument_shape.is_none() {
                        issues.push(format!(
                            "sibling-audit:argument-shape-missing:{coverage_id}:arg{}",
                            sibling.argument_index
                        ));
                    }
                    Sibling {
                        argument_index: sibling.argument_index,
                        argument_shape: sibling.argument_shape.map(str::to_owned),
                        proof: A5Audit {
                            outcome: match sibling.proof.verdict {
                                A5SiteProofVerdict::Clear => A5Outcome::Clear,
                                A5SiteProofVerdict::Overlapping => A5Outcome::Overlapping,
                                A5SiteProofVerdict::Undeterminable => A5Outcome::Undeterminable,
                            },
                            reason: sibling.proof.reason.into(),
                            family: sibling.proof.family.into(),
                            location: sibling
                                .proof
                                .location
                                .map(|location| (location.block, location.statement_index)),
                            left_site: sibling.proof.left_site.map(proof_site),
                            right_site: sibling.proof.right_site.map(proof_site),
                        },
                        access: match sibling.access {
                            SiblingAccess::Foster {
                                local,
                                mutable,
                                defaulted,
                            } => Access::Foster {
                                local: local.as_u32(),
                                mutable,
                                defaulted,
                            },
                            SiblingAccess::Contract { access, provenance } => Access::Contract {
                                access: access.key().into(),
                                provenance: provenance.into(),
                            },
                            SiblingAccess::Unknown(reason) => Access::Unknown {
                                reason: reason.into(),
                            },
                        },
                        risky: sibling_overlap::risky_sibling(sibling),
                    }
                })
                .collect();
            let post_call = match &potential.local_post_call {
                LocalPostCallEvidence::ParameterProtected => PostCall::ParameterProtected,
                LocalPostCallEvidence::ParameterOrigin { parameters } => {
                    PostCall::ParameterOrigin {
                        parameters: parameters.clone(),
                    }
                }
                LocalPostCallEvidence::Live { locals } => PostCall::Live {
                    locals: locals.iter().map(|local| local.as_u32()).collect(),
                },
                LocalPostCallEvidence::DeadUnprotected { checked_locals } => {
                    PostCall::DeadUnprotected {
                        checked_locals: checked_locals.iter().map(|local| local.as_u32()).collect(),
                    }
                }
                LocalPostCallEvidence::Unknown(reason) => PostCall::Unknown {
                    reason: (*reason).into(),
                },
            };
            let outcome = if issues.is_empty() {
                outcome(input)
            } else {
                Outcome::IncompleteCapture
            };
            if outcome == Outcome::CoverageGap {
                issues.push(format!(
                    "sibling-audit:source-custody-unresolved:{coverage_id}"
                ));
            }
            let source = &potential.source;
            let (kind, native_return) = match source {
                SiblingSource::Declared(subject) => (
                    match subject.kind {
                        super::decision::SubjectKind::Param { hir_index } => {
                            SubjectKind::Parameter { hir_index }
                        }
                        super::decision::SubjectKind::Local => SubjectKind::Local,
                    },
                    None,
                ),
                SiblingSource::NativeReturnExpression {
                    source_callee,
                    source_interface,
                    temporary,
                    ..
                } => (
                    SubjectKind::NativeReturnExpression,
                    Some(NativeReturnSource {
                        source_owner: source_callee.local_def_index.as_u32(),
                        source_form: source_interface.form.key().into(),
                        pointee: source_interface.pointee.clone(),
                        lifetime: source_interface.lifetime.clone(),
                        lifetime_plan_digest: source_interface.lifetime_plan_digest.clone(),
                        temporary: temporary.clone(),
                    }),
                ),
            };
            let mut row = Row {
                coverage_id,
                receipt_key,
                file,
                argument_span,
                call_global_span: (potential.call_span.lo().0, potential.call_span.hi().0),
                caller: potential.site.caller.clone(),
                callee: potential.site.callee.path.clone(),
                block: potential.site.block,
                statement_index: potential.site.statement_index as usize,
                argument_index: potential.site.argument_index,
                source: Source {
                    identity: source.identity_key(&potential.site.caller),
                    label: source.label(),
                    kind,
                    mir_local: source.mir_local().map(|local| local.as_u32()),
                    hir_owner: source.hir_id().owner.def_id.local_def_index.as_u32(),
                    hir_local: source.hir_id().local_id.as_u32(),
                    argument_shape: potential.source_shape.into(),
                    evidence: source_evidence(&input.source_evidence),
                    native_return,
                },
                siblings,
                post_call,
                terminal: Terminal {
                    source_form: input.terminal.source_form.key().into(),
                    target_form: input.terminal.target_form.key().into(),
                    source_delivered: input.terminal.source_delivered,
                },
                outcome,
                data: issues.is_empty(),
                issues,
            };
            let source_issues = source_integrity_issues(&row);
            if !source_issues.is_empty() {
                row.issues.extend(source_issues);
                row.outcome = Outcome::IncompleteCapture;
                row.data = false;
            }
            row
        })
        .collect()
}

/// Replay rechecks the owned source descriptor rather than trusting a saved
/// successful row. This validates identity/evidence custody, not alias policy.
pub(crate) fn source_integrity_issues(row: &Row) -> Vec<String> {
    let source = &row.source;
    let mut issues = Vec::new();
    let native = matches!(source.kind, SubjectKind::NativeReturnExpression);
    if !native {
        if source.mir_local.is_none()
            || source.native_return.is_some()
            || matches!(
                source.evidence,
                SourceEvidence::NativeReturnExpression { .. }
            )
        {
            issues.push(format!(
                "sibling-audit:declared-source-descriptor:{}",
                row.coverage_id
            ));
        }
        return issues;
    }
    let Some(proof) = &source.native_return else {
        return vec![format!(
            "sibling-audit:native-source-proof-missing:{}",
            row.coverage_id
        )];
    };
    if source.identity != format!("{}::<outbound-expression:{}>", row.caller, source.hir_local)
        || source.label != format!("outbound-expression:{}", source.hir_local)
        || !matches!(source.evidence, SourceEvidence::NativeReturnExpression { hir_owner, hir_local }
            if hir_owner == source.hir_owner && hir_local == source.hir_local)
        || !matches!(
            proof.source_form.as_str(),
            "ref-mut"
                | "ref-shared"
                | "slice-mut"
                | "slice-shared"
                | "opt-ref-mut"
                | "opt-ref-shared"
                | "opt-slice-mut"
                | "opt-slice-shared"
        )
        || proof.pointee.is_empty()
        || proof.lifetime.is_empty()
        || proof.lifetime_plan_digest.is_empty()
        || proof.temporary.is_empty()
        || (row.terminal.source_delivered && row.terminal.source_form != proof.source_form)
    {
        issues.push(format!(
            "sibling-audit:native-source-descriptor:{}",
            row.coverage_id
        ));
    }
    if source.mir_local.is_none()
        && !matches!(&row.post_call, PostCall::Unknown { reason } if !reason.is_empty())
    {
        issues.push(format!(
            "sibling-audit:native-source-mir-evidence-missing:{}",
            row.coverage_id
        ));
    }
    issues
}
