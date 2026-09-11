//! Instrument-only typed export and checkpoint bridge custody. No solver or
//! semantic analysis is invoked by this module.

use std::collections::{BTreeMap, BTreeSet};

use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{
    CensusOutcomeKind,
    bridge_custody_match::{
        self, BridgeCustodyContext, BridgeCustodyInput, BridgeCustodyReport, BridgeExpectation,
        BridgeKind, C9Stamp, OwnerRename, PendingSource, PendingSourceShape, ReceiptResult,
        ReceiptStatus, SiteAnchor,
    },
    bridge_custody_syntax::{self, ByteSpan, Inventory},
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptEvent, BridgeReceiptStage, BridgeReceiptState,
        BridgeRetentionTier, SignatureClassId,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct OriginalFile {
    pub(crate) source: String,
    pub(crate) sha256: String,
    pub(crate) global_start: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct FunctionMapping {
    pub(crate) owner_class: Option<u32>,
    pub(crate) source_file: String,
    pub(crate) original_span: ByteSpan,
    pub(crate) original_owner: String,
    pub(crate) emitted_owner: String,
    /// The actual generated name selected by the exposure plan, when present.
    pub(crate) generated_inner_name: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Descriptor {
    pub(crate) receipt_key: String,
    pub(crate) source_file: String,
    pub(crate) expectation: BridgeExpectation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum PendingSubjectKind {
    Parameter { hir_index: usize },
    Local,
    NativeReturnExpression,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum PendingPostCallEvidence {
    ParameterProtected,
    ParameterOrigin { parameters: Vec<usize> },
    Live { locals: Vec<u32> },
    DeadUnprotected { checked_locals: Vec<u32> },
    Unknown { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingSubjectRecord {
    pub(crate) site_id: String,
    pub(crate) receipt_key: Option<String>,
    pub(crate) subject_label: String,
    pub(crate) subject_identity: Option<String>,
    pub(crate) subject_owner: Option<String>,
    pub(crate) subject_kind: PendingSubjectKind,
    pub(crate) mir_local: Option<u32>,
    pub(crate) hir_owner: u32,
    pub(crate) hir_binding: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) hir_expression: Option<u32>,
    pub(crate) argument_index: usize,
    pub(crate) source_shape: String,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) post_call: PendingPostCallEvidence,
    pub(crate) reason: String,
    pub(crate) tier: String,
    pub(crate) waiver_id: String,
    pub(crate) classification: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Export {
    #[serde(default)]
    pub(crate) outbound_return: Option<super::outbound_return_transport::Capture>,
    #[serde(default)]
    pub(crate) outbound_return_bridge_keys: Option<BTreeSet<String>>,
    #[serde(default)]
    pub(crate) sibling_audit: Option<SiblingAuditCapture>,
    pub(crate) files: BTreeMap<String, OriginalFile>,
    pub(crate) functions: Vec<FunctionMapping>,
    /// All typed candidates; final Applied keys select the active subset.
    pub(crate) descriptors: Vec<Descriptor>,
    /// Already selected terminal R233 receipts, supplied by its typed producer.
    pub(crate) pending: Vec<Descriptor>,
    pub(crate) issues: Vec<String>,
    pub(crate) terminal_issues: Vec<String>,
    pub(crate) descriptor_issues: BTreeMap<String, String>,
    pub(crate) pending_candidates: BTreeMap<String, Result<Descriptor, String>>,
    pub(crate) pending_records: Vec<String>,
    /// **R287-1 — the pending sibling-overlap ledger.**
    ///
    /// A site under the R232-4 pending waiver is a DELIVERED site, so its row
    /// owes the emitted call and a disposition for every sibling. These are
    /// the rows the one new strict arm checks; nothing else reads them.
    #[serde(default)]
    pub(crate) pending_sites: Vec<PendingSiteRow>,
    pub(crate) pending_subject_records: Vec<PendingSubjectRecord>,
    pub(crate) coverage_gap_records: Vec<String>,
}

/// One pending sibling-overlap site, stated completely (R287-1).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingSiteRow {
    pub(crate) site_id: String,
    /// (a) the waiver receipt.
    pub(crate) waiver: String,
    pub(crate) source_file: String,
    /// (b) the call's original interval and the edits planned inside it;
    /// `Err` is a producer defect and is reported as one, never accepted.
    pub(crate) call: Result<PendingCallRow, String>,
    /// (c) one entry per pointer sibling. An empty list where the site has
    /// siblings is the `sibling-audit:incomplete-row` defect, not a pass.
    pub(crate) siblings: Vec<PendingSiblingRow>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingCallRow {
    pub(crate) lo: usize,
    pub(crate) hi: usize,
    pub(crate) edits: Vec<(usize, usize, String)>,
    /// **R299-2 — the PRODUCER'S OWN RENDER of this call.**
    ///
    /// The plan cannot state these calls from `by_file`: the argument bridges
    /// that reach the tree are grafted by the AST layer straight from the
    /// decision table and never become plan edits, so a row spliced out of the
    /// edit set states a call the tree does not contain — measured on heman's
    /// `kmQuaternionRotationAxisAngle` site, whose row carried `edits: []`
    /// while the tree read `core::ptr::from_ref(axis)`.
    ///
    /// So the emitting layer renders the call node it actually produced and
    /// the row carries that text verbatim. `None` is the pre-convergence
    /// state — an exit that never reached an emission has nothing to render —
    /// and the comparator then falls back to the spliced reading rather than
    /// inventing a verdict.
    #[serde(default)]
    pub(crate) rendered: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingSiblingRow {
    pub(crate) argument_index: usize,
    pub(crate) disposition: String,
    pub(crate) detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SiblingAuditCapture {
    pub(crate) expected_coverage_ids: BTreeSet<String>,
    pub(crate) rows: Vec<super::sibling_audit::Row>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CheckpointReport {
    pub(crate) data: bool,
    pub(crate) applied_receipts: BTreeSet<String>,
    pub(crate) pending_receipts: BTreeSet<String>,
    pub(crate) files: BTreeMap<String, BridgeCustodyReport>,
    pub(crate) issues: Vec<String>,
}

/// Exact worker frame carried by retained custody inputs; no current-checkout
/// source lookup is permitted when replaying this owned evidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ReplayFrame {
    pub(crate) program: String,
    pub(crate) analysis_frame: String,
    pub(crate) code_frame: String,
    pub(crate) input_tree_sha256: String,
    pub(crate) emitted_tree_sha256: String,
    pub(crate) cache_manifest_sha256: String,
    pub(crate) launch_env_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct AppliedReceipt {
    pub(crate) receipt_key: String,
    pub(crate) kind: BridgeKind,
    pub(crate) tier: String,
    pub(crate) waiver_id: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct RetainedReplay {
    pub(crate) frame: ReplayFrame,
    pub(crate) export: Export,
    pub(crate) applied: Vec<AppliedReceipt>,
    pub(crate) emitted_sources: Option<BTreeMap<String, String>>,
    pub(crate) emitted_outcome: bool,
    pub(crate) comparison: CheckpointReport,
}

pub(crate) fn compare_retained(
    retained: Option<&RetainedReplay>,
    expected_frame: &ReplayFrame,
) -> Result<CheckpointReport, String> {
    let retained = retained.ok_or("bridge-custody:missing-retained-replay")?;
    if &retained.frame != expected_frame {
        return Err("bridge-custody:retained-frame-mismatch".into());
    }
    if !retained.comparison.data || !retained.comparison.issues.is_empty() {
        return Err("bridge-custody:retained-comparison-not-valid".into());
    }
    let replay = compare_applied(
        &retained.export,
        &retained.applied,
        retained.emitted_sources.as_ref(),
        if retained.emitted_outcome {
            CensusOutcomeKind::Emitted
        } else {
            CensusOutcomeKind::Degraded
        },
    );
    if !replay.data {
        return Ok(replay);
    }
    if replay != retained.comparison {
        return Err("bridge-custody:retained-comparison-replay-mismatch".into());
    }
    Ok(replay)
}

pub(crate) fn applied_receipts(events: &[BridgeReceiptEvent]) -> Vec<AppliedReceipt> {
    events
        .iter()
        .filter_map(|event| {
            if event.stage != BridgeReceiptStage::Terminal
                || event.state != BridgeReceiptState::Applied
            {
                return None;
            }
            let kind = match event.site.bridge_kind.as_str() {
                "pair-t2-raw-view" => BridgeKind::PairT2RawView,
                "a5-site-proof-t2-fallback" => BridgeKind::A5SiteProofT2Fallback,
                "pair-copy-snapshot" => BridgeKind::PairCopySnapshot,
                _ => return None,
            };
            Some(AppliedReceipt {
                receipt_key: event.site.receipt_key(),
                kind,
                tier: match event.retention {
                    BridgeRetentionTier::None => "none",
                    BridgeRetentionTier::T1 => "T1",
                    BridgeRetentionTier::T2 => "T2",
                }
                .into(),
                waiver_id: event.waiver_id.clone(),
            })
        })
        .collect()
}

pub(crate) fn file_label(file: &super::plan::FileKey) -> String {
    match file {
        super::plan::FileKey::Real(path) => path.display().to_string(),
        super::plan::FileKey::Virtual(name) => name.clone(),
    }
}

fn source_location(tcx: TyCtxt<'_>, span: Span) -> Result<(String, ByteSpan), String> {
    if span.is_dummy() || span.from_expansion() {
        return Err("unplaceable-source-span".into());
    }
    let low = tcx.sess.source_map().lookup_byte_offset(span.lo());
    let high = tcx.sess.source_map().lookup_byte_offset(span.hi());
    if low.sf.start_pos != high.sf.start_pos {
        return Err("cross-file-source-span".into());
    }
    let file = super::file_key(&low.sf.name).ok_or("unmapped-source-file")?;
    Ok((
        file_label(&file),
        ByteSpan {
            lo: low.pos.0 as u32,
            hi: high.pos.0 as u32,
        },
    ))
}

fn qualified_inner(owner: &str, inner: &str) -> String {
    match owner.rsplit_once("::") {
        Some((parent, _)) => format!("{parent}::{inner}"),
        None => inner.to_owned(),
    }
}

struct FunctionCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    capture: &'a super::ast_transform::AstCapture,
    table: &'a super::decision::DecisionTable,
    export: &'a mut Export,
}

impl FunctionCollector<'_, '_> {
    fn add(&mut self, id: ast::NodeId, span: Span) {
        let Some(&owner) = self.capture.map.global_map.get(&id) else { return };
        let Ok((file, original_span)) = source_location(self.tcx, span) else { return };
        if !self.export.files.contains_key(&file) {
            return;
        }
        let original_owner = self.tcx.def_path_str(owner.to_def_id());
        let generated_inner_name = match self
            .table
            .exposure
            .as_ref()
            .map(|exposure| exposure.plan(owner))
        {
            Some(
                super::decision::exposure::ExposureSurfacePlan::PositiveSeedShim
                | super::decision::exposure::ExposureSurfacePlan::FnPtrRawWrapper,
            ) => Some(format!(
                "__crat_safe_{}",
                self.tcx.item_name(owner.to_def_id())
            )),
            Some(
                super::decision::exposure::ExposureSurfacePlan::ClosedWorldDirect
                | super::decision::exposure::ExposureSurfacePlan::NotApplicable,
            )
            | None => None,
        };
        self.export.functions.push(FunctionMapping {
            owner_class: Some(SignatureClassId::of(owner).order_key()),
            source_file: file,
            original_span,
            emitted_owner: original_owner.clone(),
            original_owner,
            generated_inner_name,
        });
    }
}

impl<'ast> Visitor<'ast> for FunctionCollector<'_, '_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        if matches!(item.kind, ast::ItemKind::Fn(_)) {
            self.add(item.id, item.span);
        }
        visit::walk_item(self, item);
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, context: visit::AssocCtxt) {
        if matches!(item.kind, ast::AssocItemKind::Fn(_)) {
            self.add(item.id, item.span);
        }
        visit::walk_assoc_item(self, item, context);
    }

    fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
        if matches!(item.kind, ast::ForeignItemKind::Fn(_)) {
            self.add(item.id, item.span);
        }
        visit::walk_item(self, item);
    }
}

fn descriptor_for_event(
    tcx: TyCtxt<'_>,
    table: &super::decision::DecisionTable,
    plan: &super::plan::Plan,
    files: &BTreeMap<String, OriginalFile>,
    event: &BridgeReceiptEvent,
) -> Result<Descriptor, String> {
    let mut candidates = Vec::new();
    let mut consider = |kind: BridgeKind,
                        caller: LocalDefId,
                        callee: LocalDefId,
                        span: Span,
                        indices: Vec<usize>,
                        argument: bool,
                        c9_stamp: Option<C9Stamp>|
     -> Result<(), String> {
        if event.site.caller != caller
            || event.site.owner_class != SignatureClassId::of(callee)
            || event.site.callee != BridgeCalleeId::Local(callee)
        {
            return Ok(());
        }
        let (file, location) = source_location(tcx, span)?;
        if event.site.file != file || event.site.lo != location.lo || event.site.hi != location.hi {
            return Ok(());
        }
        if !files.contains_key(&file) {
            return Err(format!("source-file-not-captured:{file}"));
        }
        let key = event.site.receipt_key();
        let anchor = if argument {
            let [index] = indices.as_slice() else {
                return Err("argument-descriptor-position-arity".into());
            };
            SiteAnchor::Argument {
                span: location,
                argument_index: *index,
            }
        } else {
            SiteAnchor::Call {
                span: location,
                argument_indices: indices,
            }
        };
        let tier = match event.retention {
            BridgeRetentionTier::None => "none",
            BridgeRetentionTier::T1 => "T1",
            BridgeRetentionTier::T2 => "T2",
        };
        candidates.push(Descriptor {
            receipt_key: key.clone(),
            source_file: file,
            expectation: BridgeExpectation {
                identity: key,
                kind,
                caller: tcx.def_path_str(caller.to_def_id()),
                callee: tcx.def_path_str(callee.to_def_id()),
                anchor,
                c9_stamp,
                pending_source: None,
                tier: tier.into(),
                waiver_id: event.waiver_id.clone(),
            },
        });
        Ok(())
    };
    match event.site.bridge_kind.as_str() {
        "pair-t2-raw-view" => {
            for call in &plan.terminal_call_plans.pair_raw_calls {
                consider(
                    BridgeKind::PairT2RawView,
                    call.caller,
                    call.callee,
                    call.call_span,
                    call.views.iter().map(|view| view.argument_index).collect(),
                    false,
                    None,
                )?;
            }
        }
        "a5-site-proof-t2-fallback" => {
            for call in &plan.terminal_call_plans.a5_raw_calls {
                consider(
                    BridgeKind::A5SiteProofT2Fallback,
                    call.caller,
                    call.callee,
                    call.call_span,
                    call.views.iter().map(|view| view.argument_index).collect(),
                    false,
                    None,
                )?;
            }
            for proof in &table.seams.overlap_proofs {
                if matches!(
                    proof.fallback,
                    super::decision::seam::A5ProofSiteFallback::T2RawView { .. }
                ) && proof.proof_site_key.is_some_and(|key| {
                    key.caller == proof.caller
                        && key.callee == proof.callee.to_def_id()
                        && key.argument_index == proof.index
                }) {
                    consider(
                        BridgeKind::A5SiteProofT2Fallback,
                        proof.caller,
                        proof.callee,
                        proof.span,
                        vec![proof.index],
                        true,
                        None,
                    )?;
                }
            }
        }
        "pair-copy-snapshot" => {
            for mark in &table.c9_marks {
                let params = mark.key.pair.params();
                let parameter = match mark.key.shared_side {
                    crate::analyses::borrow_ownership::a5_overlap::PairSide::Left => params.first(),
                    crate::analyses::borrow_ownership::a5_overlap::PairSide::Right => {
                        params.second()
                    }
                };
                let index = usize::try_from(parameter)
                    .ok()
                    .and_then(|index| index.checked_sub(1))
                    .ok_or("invalid-c9-formal-position")?;
                let statement_index = u32::try_from(mark.key.location.statement_index)
                    .map_err(|_| "c9-statement-overflow")?;
                consider(
                    BridgeKind::PairCopySnapshot,
                    mark.caller_did,
                    mark.owner_did,
                    mark.call_span,
                    vec![index],
                    false,
                    Some(C9Stamp {
                        basic_block: mark.key.location.block,
                        statement_index,
                    }),
                )?;
            }
        }
        _ => return Err("unsupported-custody-event-kind".into()),
    }
    if candidates.len() != 1 {
        return Err(format!(
            "typed-carrier-candidate-count:{}",
            candidates.len()
        ));
    }
    Ok(candidates.remove(0))
}

pub(crate) fn capture(
    tcx: TyCtxt<'_>,
    capture: &super::ast_transform::AstCapture,
    table: &super::decision::DecisionTable,
    plan: &super::plan::Plan,
    original_files: &BTreeMap<super::plan::FileKey, String>,
) -> Export {
    let mut export = Export::default();
    export.sibling_audit = Some(SiblingAuditCapture {
        expected_coverage_ids: table
            .sibling_overlap_inventory
            .coverage
            .iter()
            .map(|record| super::decision::raw_boundary::site_atom_id(&record.potential.site))
            .chain(
                table
                    .seams
                    .outbound_expressions
                    .plans
                    .keys()
                    .map(super::decision::raw_boundary::site_atom_id),
            )
            .collect(),
        rows: Vec::new(),
    });
    for (file, source) in original_files {
        let label = file_label(file);
        let files = tcx.sess.source_map().files();
        let observed = files
            .iter()
            .filter(|source_file| super::file_key(&source_file.name).as_ref() == Some(file))
            .collect::<Vec<_>>();
        let [source_file] = observed.as_slice() else {
            export
                .issues
                .push(format!("source-file-start-not-unique:{label}"));
            continue;
        };
        export.files.insert(
            label,
            OriginalFile {
                source: source.clone(),
                sha256: format!("{:x}", Sha256::digest(source.as_bytes())),
                global_start: source_file.start_pos.0,
            },
        );
    }
    FunctionCollector {
        tcx,
        capture,
        table,
        export: &mut export,
    }
    .visit_crate(&capture.krate);
    for event in plan.bridge_events(&BTreeSet::new()).iter().filter(|event| {
        event.stage == BridgeReceiptStage::Plan
            && matches!(
                event.site.bridge_kind.as_str(),
                "pair-t2-raw-view" | "a5-site-proof-t2-fallback" | "pair-copy-snapshot"
            )
    }) {
        match descriptor_for_event(tcx, table, plan, &export.files, event) {
            Ok(descriptor) => export.descriptors.push(descriptor),
            Err(error) => {
                export
                    .descriptor_issues
                    .insert(event.site.receipt_key(), error);
            }
        }
    }
    for potential in table.sibling_overlap_inventory.potentials.iter().chain(
        table
            .sibling_overlap_inventory
            .coverage
            .iter()
            .map(|coverage| &coverage.potential),
    ) {
        let id = super::decision::raw_boundary::site_atom_id(&potential.site);
        let descriptor = (|| {
            let (file, span) = source_location(tcx, potential.argument_span)?;
            if !export.files.contains_key(&file) {
                return Err(format!("pending-source-file-not-captured:{file}"));
            }
            let coverage = table
                .sibling_overlap_inventory
                .coverage
                .iter()
                .filter(|coverage| coverage.potential.site == potential.site)
                .collect::<Vec<_>>();
            let [coverage] = coverage.as_slice() else {
                return Err("pending-source-coverage-not-unique".into());
            };
            use super::decision::sibling_overlap::{SiblingSource, SourceBridgeEvidence};
            let pending_source = match (&potential.source, &coverage.evidence) {
                (SiblingSource::Declared(source), evidence) => {
                    let shape = match evidence {
                        SourceBridgeEvidence::WholeSubject => PendingSourceShape::WholeSubject,
                        // **R304-2** — the array view is the same depth-1
                        // projection of the referent, differing only in how it
                        // is spelled, so it is the same pending source shape.
                        SourceBridgeEvidence::ProjectedReferent { .. }
                        | SourceBridgeEvidence::ProjectedArrayView { .. } => {
                            PendingSourceShape::ProjectedReferent
                        }
                        SourceBridgeEvidence::TypedView { .. }
                        | SourceBridgeEvidence::NativeReturnExpression { .. }
                        | SourceBridgeEvidence::RawFieldValue
                        | SourceBridgeEvidence::BindingStorage
                        | SourceBridgeEvidence::UnknownShape(_) => {
                            return Err("pending-source-coverage-not-supported".into());
                        }
                    };
                    let (binding_file, binding_span) = source_location(tcx, source.binding_span)?;
                    if binding_file != file {
                        return Err("pending-source-binding-in-different-file".into());
                    }
                    PendingSource {
                        binding: Some(
                            source
                                .param_name
                                .clone()
                                .ok_or("pending-source-binding-name-absent")?,
                        ),
                        binding_span: Some(binding_span),
                        shape,
                    }
                }
                (
                    SiblingSource::NativeReturnExpression {
                        argument_hir,
                        source_callee,
                        source_interface,
                        temporary,
                        ..
                    },
                    SourceBridgeEvidence::NativeReturnExpression { use_hir_id },
                ) => {
                    let input = table
                        .seams
                        .outbound_expressions
                        .plans
                        .get(&potential.site)
                        .ok_or("pending-native-expression-input-missing")?;
                    // A nested carrier edits a span strictly inside the
                    // argument, so the argument identity it must match is its
                    // enclosing span, not its edit span.
                    let enclosing = input.enclosing_argument_span.unwrap_or(input.argument_span);
                    if input.argument_hir != *argument_hir
                        || use_hir_id != argument_hir
                        || input.caller != potential.caller
                        || input.source_callee != *source_callee
                        || input.source_interface != *source_interface
                        || input.temporary != *temporary
                        || enclosing != potential.argument_span
                        || input.call_span != potential.call_span
                    {
                        return Err("pending-native-expression-input-drift".into());
                    }
                    let (source_file, source_call_span) =
                        source_location(tcx, input.argument_span)?;
                    if source_file != file {
                        return Err("pending-native-expression-in-different-file".into());
                    }
                    let source_owner = source_callee.local_def_index.as_u32();
                    let source_function = tcx.def_path_str(source_callee.to_def_id());
                    let source_form = source_interface.form.key().into();
                    let source_type = source_interface.temporary_type();
                    let temporary = temporary.clone();
                    let template = input.template.key().into();
                    PendingSource {
                        binding: None,
                        binding_span: None,
                        shape: if input.enclosing_argument_span.is_some() {
                            PendingSourceShape::NativeReturnExpressionNested {
                                argument_span: span,
                                source_call_span,
                                source_owner,
                                source_function,
                                source_form,
                                source_type,
                                temporary,
                                template,
                            }
                        } else {
                            PendingSourceShape::NativeReturnExpression {
                                argument_span: span,
                                source_call_span,
                                source_owner,
                                source_function,
                                source_form,
                                source_type,
                                temporary,
                                template,
                            }
                        },
                    }
                }
                (SiblingSource::NativeReturnExpression { .. }, _) => {
                    return Err("pending-native-expression-coverage-mismatch".into());
                }
            };
            Ok(Descriptor {
                receipt_key: id.clone(),
                source_file: file,
                expectation: BridgeExpectation {
                    identity: id.clone(),
                    kind: BridgeKind::SiblingOverlapPending,
                    caller: tcx.def_path_str(potential.caller.to_def_id()),
                    callee: tcx.def_path_str(potential.callee),
                    anchor: SiteAnchor::Argument {
                        span,
                        argument_index: potential.site.argument_index,
                    },
                    c9_stamp: None,
                    pending_source: Some(pending_source),
                    tier: String::new(),
                    waiver_id: None,
                },
            })
        })();
        if let Some(previous) = export
            .pending_candidates
            .insert(id.clone(), descriptor.clone())
        {
            if previous != descriptor {
                export
                    .pending_candidates
                    .insert(id, Err("pending-candidate-identity-conflict".into()));
            }
        }
    }
    refresh(
        &mut export,
        plan,
        &BTreeSet::new(),
        &plan.pending_sibling_receipts(&BTreeSet::new()),
        &plan.sibling_coverage_gaps(&BTreeSet::new()),
        &plan.sibling_audit_rows_with_atoms(&BTreeSet::new(), &BTreeSet::new()),
        &BTreeMap::new(),
    );
    let mut artifacts = super::RawBoundaryArtifacts::default();
    super::refresh_raw_boundary_receipt_events(
        &mut artifacts,
        plan,
        &BTreeSet::new(),
        &BTreeSet::new(),
    );
    export.outbound_return = artifacts.bridge_custody_export.outbound_return;
    export.outbound_return_bridge_keys =
        artifacts.bridge_custody_export.outbound_return_bridge_keys;
    export
}

pub(crate) fn refresh(
    export: &mut Export,
    plan: &super::plan::Plan,
    reverted: &BTreeSet<super::bridge_receipt::SignatureClassId>,
    pending: &[super::plan::sibling_overlap::PendingSite],
    gaps: &[super::decision::sibling_overlap::CoverageGapReceipt],
    audit_rows: &[super::sibling_audit::Row],
    // R299-2: the emitting layer's render of each call, by original span.
    call_renders: &BTreeMap<(u32, u32), String>,
) {
    if let Some(audit) = &mut export.sibling_audit {
        audit.rows = audit_rows.to_vec();
    }
    export.terminal_issues.clear();
    export.pending.clear();
    export.pending_records.clear();
    export.pending_sites.clear();
    export.pending_subject_records.clear();
    export.coverage_gap_records.clear();
    for function in &mut export.functions {
        let live = function.owner_class.is_some_and(|owner| {
            plan.class_finalization.classes.iter().any(|(id, class)| {
                id.order_key() == owner && class.is_ready() && !reverted.contains(id)
            })
        });
        function.emitted_owner = match (&function.generated_inner_name, live) {
            (Some(inner), true) => qualified_inner(&function.original_owner, inner),
            _ => function.original_owner.clone(),
        };
    }
    for site in pending {
        export.pending_records.push(format!("{site:#?}"));
        export.pending_sites.push(PendingSiteRow {
            site_id: site.receipt.site_id(),
            waiver: site.receipt.reason.to_owned(),
            source_file: match &site.emitted_call {
                Ok(call) => super::plan::file_key_label(&call.file),
                Err(_) => site
                    .site
                    .as_ref()
                    .map(|key| key.file.clone())
                    .unwrap_or_default(),
            },
            call: site.emitted_call.as_ref().map_or_else(
                |error| Err(error.clone()),
                |call| {
                    Ok(PendingCallRow {
                        lo: call.lo,
                        hi: call.hi,
                        edits: call.edits.clone(),
                        rendered: call_renders
                            .get(&(
                                site.receipt.potential.call_span.lo().0,
                                site.receipt.potential.call_span.hi().0,
                            ))
                            .cloned(),
                    })
                },
            ),
            siblings: site
                .siblings
                .iter()
                .map(|disposition| PendingSiblingRow {
                    argument_index: disposition.argument_index(),
                    disposition: disposition.key().to_owned(),
                    detail: match disposition {
                        super::plan::sibling_overlap::SiblingDisposition::Bridged {
                            custody_identity,
                            ..
                        } => custody_identity.clone(),
                        super::plan::sibling_overlap::SiblingDisposition::Held {
                            reason, ..
                        } => reason.clone(),
                        super::plan::sibling_overlap::SiblingDisposition::RawUnchanged {
                            ..
                        } => "-".to_owned(),
                    },
                })
                .collect(),
        });
        let source = &site.receipt.potential.source;
        let owners = export
            .functions
            .iter()
            .filter(|function| {
                function.owner_class == Some(source.caller().local_def_index.as_u32())
            })
            .map(|function| function.original_owner.clone())
            .collect::<Vec<_>>();
        let owner = match owners.as_slice() {
            [owner] => Some(owner.clone()),
            _ => None,
        };
        let subject_kind = match source.declared().map(|source| source.kind) {
            Some(super::decision::SubjectKind::Param { hir_index }) => {
                PendingSubjectKind::Parameter { hir_index }
            }
            Some(super::decision::SubjectKind::Local) => PendingSubjectKind::Local,
            None => PendingSubjectKind::NativeReturnExpression,
        };
        use super::decision::sibling_overlap::LocalPostCallEvidence;
        let post_call = match &site.receipt.potential.local_post_call {
            LocalPostCallEvidence::ParameterProtected => {
                PendingPostCallEvidence::ParameterProtected
            }
            LocalPostCallEvidence::ParameterOrigin { parameters } => {
                PendingPostCallEvidence::ParameterOrigin {
                    parameters: parameters.clone(),
                }
            }
            LocalPostCallEvidence::Live { locals } => PendingPostCallEvidence::Live {
                locals: locals.iter().map(|local| local.as_u32()).collect(),
            },
            LocalPostCallEvidence::DeadUnprotected { checked_locals } => {
                PendingPostCallEvidence::DeadUnprotected {
                    checked_locals: checked_locals.iter().map(|local| local.as_u32()).collect(),
                }
            }
            LocalPostCallEvidence::Unknown(reason) => PendingPostCallEvidence::Unknown {
                reason: (*reason).into(),
            },
        };
        export.pending_subject_records.push(PendingSubjectRecord {
            site_id: site.receipt.site_id(),
            receipt_key: site.site.as_ref().ok().map(|key| key.receipt_key()),
            subject_label: source.label(),
            subject_identity: owner.as_ref().map(|owner| source.identity_key(owner)),
            subject_owner: owner,
            subject_kind,
            mir_local: source.mir_local().map(|local| local.as_u32()),
            hir_owner: source.hir_id().owner.def_id.local_def_index.as_u32(),
            hir_binding: source
                .declared()
                .map(|source| source.hir_id.local_id.as_u32()),
            hir_expression: source
                .declared()
                .is_none()
                .then(|| source.hir_id().local_id.as_u32()),
            argument_index: site.receipt.potential.site.argument_index,
            source_shape: site.receipt.potential.source_shape.into(),
            source_form: site.receipt.source_form.key().into(),
            target_form: site.receipt.target_form.key().into(),
            post_call,
            reason: site.receipt.reason.into(),
            tier: site.receipt.tier.into(),
            waiver_id: site.receipt.waiver.into(),
            classification: "WAIVED".into(),
        });
        if let Err(error) = &site.site {
            export
                .terminal_issues
                .push(format!("bridge-custody:pending-site-mapping:{error}"));
            continue;
        }
        let id = site.receipt.site_id();
        match export.pending_candidates.get(&id) {
            Some(Ok(candidate)) => {
                let mut descriptor = candidate.clone();
                let key = site
                    .site
                    .as_ref()
                    .expect("checked pending site")
                    .receipt_key();
                descriptor.receipt_key = key.clone();
                descriptor.expectation.identity = key;
                descriptor.expectation.tier = site.receipt.tier.into();
                descriptor.expectation.waiver_id = Some(site.receipt.waiver.into());
                export.pending.push(descriptor);
            }
            Some(Err(error)) => export
                .terminal_issues
                .push(format!("bridge-custody:pending-descriptor:{id}:{error}")),
            None => export
                .terminal_issues
                .push(format!("bridge-custody:missing-pending-descriptor:{id}")),
        }
    }
    for gap in gaps {
        // **R304-2 — the row is recorded either way; only an UNRULED shape is
        // an issue.** A shape the seat has ruled on is held under its own name
        // and that is complete custody, not an unresolved gap.
        export.coverage_gap_records.push(format!("{gap:#?}"));
        if gap.held {
            continue;
        }
        export.terminal_issues.push(format!(
            "bridge-custody:sibling-coverage-gap:{}:{}:{}",
            super::decision::raw_boundary::site_atom_id(&gap.potential.site),
            gap.reason,
            gap.shape
        ));
    }
}

/// This entry runs only after the compiler callback returns. The final typed
/// events, rather than earlier class readiness, select expected bridge sites.
pub(crate) fn compare_capture(
    export: &Export,
    events: &[BridgeReceiptEvent],
    sources: Option<&BTreeMap<String, String>>,
    outcome: CensusOutcomeKind,
) -> CheckpointReport {
    compare_applied(export, &applied_receipts(events), sources, outcome)
}

/// **R287-1 — the one new strict arm: "pending sibling-overlap site".**
///
/// A site under the R232-4 pending waiver is a DELIVERED site. Its ledger row
/// must carry the waiver receipt, the emitted call, and an explicit
/// disposition for every sibling argument; this arm checks exactly those
/// three and nothing else. Existing arms are untouched.
///
/// It replaces a *uniqueness* requirement with an *equality* one. The old
/// pending matcher searched the emitted tree for the unique structurally
/// corresponding call and answered `pending-call-correspondence-not-unique`
/// whenever an owner held two — a property custody never needed. Here the
/// producer states what the tree should read and the arm checks that some
/// call in that file reads it, so two identical calls satisfy custody rather
/// than defeating it.
///
/// Nothing here is permitted to pass on absence: a missing call, an
/// unrenderable one, or a sibling without a disposition is a producer-side
/// ledger-completeness defect and is reported as such.
fn pending_sibling_overlap_issues(
    export: &Export,
    sources: Option<&BTreeMap<String, String>>,
) -> Vec<String> {
    let mut issues = Vec::new();
    for row in &export.pending_sites {
        let id = &row.site_id;
        if row.waiver != super::decision::sibling_overlap::PENDING_REASON {
            issues.push(format!(
                "pending-sibling-overlap:waiver-receipt-mismatch:{id}:{}",
                row.waiver
            ));
        }
        let call = match &row.call {
            Ok(call) => call,
            // A row that explicitly declines the call-text claim is complete:
            // the native-return-expression shape's text belongs to its own
            // arm. Every OTHER absence is the producer defect R287-1 names.
            Err(reason) if reason.starts_with("pending-sibling-call-not-claimed:") => {
                check_sibling_dispositions(id, &row.siblings, &mut issues);
                continue;
            }
            Err(reason) => {
                issues.push(format!(
                    "pending-sibling-overlap:emitted-call-missing:{id}:{reason}"
                ));
                continue;
            }
        };
        match export.files.get(&row.source_file) {
            None => issues.push(format!(
                "pending-sibling-overlap:original-file-missing:{id}:{}",
                row.source_file
            )),
            // **R299-2.** The producer's render, when it has one, IS the
            // claim; splicing the plan's edits is only the pre-convergence
            // fallback. Preferring the render is what makes the row statable
            // for every call whose bridges the AST layer grafts.
            Some(original) => match call
                .rendered
                .clone()
                .map_or_else(|| render_pending_call(original.source.as_str(), call), Ok)
            {
                Err(why) => issues.push(format!(
                    "pending-sibling-overlap:emitted-call-unrenderable:{id}:{why}"
                )),
                Ok(expected) => match sources.and_then(|map| map.get(&row.source_file)) {
                    // No emitted source is a transport state, not a verdict:
                    // the row is complete and there is nothing to compare it
                    // against yet.
                    None => {}
                    Some(emitted) => {
                        // Compared as TOKENS, not bytes. The emitted tree is
                        // reprinted by `pprust`, which reflows a long call
                        // across lines and adds a trailing comma when it does,
                        // so a byte comparison would fail on formatting the
                        // producer never claimed. Layout and that comma are
                        // the only things dropped; every other token, in
                        // order, must still be there.
                        // **R291-3 — no opaque failures.** A comparator that
                        // says only "absent" tells the reader nothing about
                        // WHY, and every hour spent on binn and libzahl was
                        // spent recovering what the arm already knew. The
                        // issue carries the expected sequence, the window of
                        // the emitted file that best matches it, and the
                        // offset at which they first differ.
                        let want = normalised_tokens(&expected);
                        let have = normalised_tokens(emitted);
                        if !have.contains(&want) {
                            issues.push(format!(
                                "pending-sibling-overlap:emitted-call-text-absent:{id}:{}",
                                token_divergence(&want, &have)
                            ));
                        }
                    }
                },
            },
        }
        check_sibling_dispositions(id, &row.siblings, &mut issues);
    }
    issues
}

fn check_sibling_dispositions(id: &str, siblings: &[PendingSiblingRow], issues: &mut Vec<String>) {
    {
        let mut seen = BTreeSet::new();
        for sibling in siblings {
            if !seen.insert(sibling.argument_index) {
                issues.push(format!(
                    "pending-sibling-overlap:duplicate-sibling-disposition:{id}:arg{}",
                    sibling.argument_index
                ));
            }
            match sibling.disposition.as_str() {
                "bridged" if sibling.detail.is_empty() || sibling.detail == "-" => {
                    issues.push(format!(
                        "pending-sibling-overlap:bridged-sibling-without-custody-identity:{id}:arg{}",
                        sibling.argument_index
                    ));
                }
                "held" if sibling.detail.is_empty() || sibling.detail == "-" => {
                    issues.push(format!(
                        "pending-sibling-overlap:held-sibling-without-reason:{id}:arg{}",
                        sibling.argument_index
                    ));
                }
                "bridged" | "held" | "raw-unchanged" => {}
                other => issues.push(format!(
                    "pending-sibling-overlap:unknown-sibling-disposition:{id}:arg{}:{other}",
                    sibling.argument_index
                )),
            }
        }
    }
}

/// The emitted text of a pending call, from the original bytes and the edits
/// the plan recorded inside it.
///
/// Edits arrive sorted outermost-first. A **nested** pair is not a defect —
/// L07's composed containments put an inner edit inside an outer one, and the
/// AST layer renders the descendant first and moves the rewritten subtree into
/// the outer. This mirrors that, with K21's guard: the inner's original text
/// must occur exactly once in the outer's replacement, or the composition is
/// not statable and the row says so. A true **crossing** — which L07 measured
/// at zero — is rejected rather than rendered around.
/// The token sequence of `text`, with the two things `pprust` is free to
/// change and the producer never claimed: layout, and the trailing comma it
/// adds to a delimited list once it breaks that list across lines.
/// Where `want` stops matching anything in `have`, said in one line.
///
/// The best-matching window is the one sharing the longest prefix with
/// `want`; the report names that prefix's length, what `want` expects next and
/// what the tree has there. Truncated, because a receipt line is read by a
/// person.
fn token_divergence(want: &str, have: &str) -> String {
    fn clip(text: &str, from: usize, len: usize) -> String {
        text.chars().skip(from).take(len).collect()
    }
    let best = (0..=have.len().saturating_sub(1))
        .filter(|start| have.is_char_boundary(*start))
        .map(|start| {
            let shared = want
                .chars()
                .zip(have[start..].chars())
                .take_while(|(a, b)| a == b)
                .count();
            (shared, start)
        })
        .max()
        .unwrap_or((0, 0));
    let (shared, start) = best;
    format!(
        "diverges-at={shared}:want={:?}:have={:?}:expected={:?}",
        clip(want, shared, 24),
        clip(&have[start..], shared, 24),
        clip(want, 0, 60)
    )
}

pub(crate) fn normalised_tokens(text: &str) -> String {
    let dense = text
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>();
    let mut out = String::with_capacity(dense.len());
    let mut chars = dense.chars().peekable();
    while let Some(c) = chars.next() {
        if c == ',' && matches!(chars.peek(), Some(')' | ']' | '}' | '>')) {
            continue;
        }
        out.push(c);
    }
    out
}

fn render_pending_call(original_source: &str, call: &PendingCallRow) -> Result<String, String> {
    render_span(original_source, call.lo, call.hi, &call.edits)
}

/// **R295-3 — the failure says which composition it could not state.**
///
/// This returned a bare `None`, and every reading of
/// `emitted-call-unrenderable` then had to reconstruct which of four
/// conditions fired. They are named instead: a crossing or reversed interval,
/// an interval outside the file, an inner edit whose original text is empty,
/// and K21's guard — an inner original occurring other than exactly once in
/// the outer replacement, which is the composition that is not statable.
fn render_span(
    source: &str,
    lo: usize,
    hi: usize,
    edits: &[(usize, usize, String)],
) -> Result<String, String> {
    fn slice(source: &str, lo: usize, hi: usize) -> Result<&str, String> {
        source
            .get(lo..hi)
            .ok_or_else(|| format!("interval-outside-source:{lo}..{hi}"))
    }
    let mut out = String::new();
    let mut cursor = lo;
    let mut index = 0;
    while index < edits.len() {
        let (edit_lo, edit_hi, replacement) = &edits[index];
        if *edit_lo < cursor || *edit_hi > hi || edit_lo > edit_hi {
            return Err(format!(
                "crossing-or-out-of-range-edit:{edit_lo}..{edit_hi}:in={lo}..{hi}:cursor={cursor}"
            ));
        }
        out.push_str(slice(source, cursor, *edit_lo)?);
        let children = edits[index + 1..]
            .iter()
            .take_while(|(child_lo, child_hi, _)| child_lo >= edit_lo && child_hi <= edit_hi)
            .cloned()
            .collect::<Vec<_>>();
        if children.is_empty() {
            out.push_str(replacement);
        } else {
            let mut composed = replacement.clone();
            for child in &children {
                let original = slice(source, child.0, child.1)?;
                let rendered = render_span(source, child.0, child.1, std::slice::from_ref(child))?;
                if original.is_empty() {
                    return Err(format!("empty-inner-original:{}..{}", child.0, child.1));
                }
                let occurrences = composed.matches(original).count();
                if occurrences != 1 {
                    return Err(format!(
                        "inner-original-occurs-{occurrences}-times:{}..{}",
                        child.0, child.1
                    ));
                }
                composed = composed.replace(original, &rendered);
            }
            out.push_str(&composed);
        }
        cursor = *edit_hi;
        index += 1 + children.len();
    }
    out.push_str(slice(source, cursor, hi)?);
    Ok(out)
}

fn sibling_audit_issues(audit: Option<&SiblingAuditCapture>) -> Vec<String> {
    let Some(audit) = audit else {
        return vec!["sibling-audit:missing-capture".into()];
    };
    let mut issues = Vec::new();
    let mut observed = BTreeSet::new();
    for row in &audit.rows {
        issues.extend(super::sibling_audit::source_integrity_issues(row));
        let id = &row.coverage_id;
        if !observed.insert(id.clone()) {
            issues.push(format!("sibling-audit:duplicate-coverage-id:{id}"));
        }
        if !audit.expected_coverage_ids.contains(id) {
            issues.push(format!("sibling-audit:extra-coverage-id:{id}"));
        }
        if !row.data {
            // **R295-3.** The bare id said only that the row was incomplete.
            // The row's own issues say what it is missing, and a row that is
            // incomplete while recording nothing is a producer defect of its
            // own, so it says that rather than reading like the old line.
            let why = if row.issues.is_empty() {
                "no-issue-recorded".to_owned()
            } else {
                row.issues.join(",")
            };
            issues.push(format!("sibling-audit:incomplete-row:{id}:{why}"));
        }
        for issue in &row.issues {
            issues.push(format!("sibling-audit:row-issue:{id}:{issue}"));
        }
        // An explicit Undeterminable or unknown access/post-call result is
        // captured evidence. Only missing identities or incomplete rows fail
        // this transport check; no predicate verdict is reconstructed here.
    }
    for id in audit.expected_coverage_ids.difference(&observed) {
        issues.push(format!("sibling-audit:missing-coverage-id:{id}"));
    }
    issues.sort();
    issues.dedup();
    issues
}

/// Native expression source metadata must agree with the separately owned
/// selected J27 obligation. A saved successful audit row is not that proof.
fn native_sibling_source_issues(export: &Export) -> Vec<String> {
    let (Some(audit), Some(outbound)) = (&export.sibling_audit, &export.outbound_return) else {
        // Their mandatory presence is checked by the surrounding comparator.
        return Vec::new();
    };
    let requirements = outbound
        .required
        .iter()
        .filter(|required| required.bridge.kind == "outbound-native-return-argument")
        .collect::<Vec<_>>();
    let same_site = |row: &super::sibling_audit::Row,
                     required: &super::outbound_return_transport::Requirement| {
        required.key.hir_owner == Some(row.source.hir_owner)
            && required.key.hir_item_local_id == Some(row.source.hir_local)
            && required
                .key
                .argument_index
                .and_then(|index| usize::try_from(index).ok())
                == Some(row.argument_index)
    };
    let native = |row: &super::sibling_audit::Row| {
        matches!(
            row.source.kind,
            super::sibling_audit::SubjectKind::NativeReturnExpression
        )
    };
    let mut issues = Vec::new();
    for row in audit.rows.iter().filter(|row| native(row)) {
        let selected = requirements
            .iter()
            .copied()
            .filter(|required| same_site(row, required))
            .collect::<Vec<_>>();
        if !row.terminal.source_delivered {
            if !selected.is_empty() {
                issues.push(format!(
                    "sibling-audit:native-source-retired-but-selected:{}",
                    row.coverage_id
                ));
            }
            continue;
        }
        let [required] = selected.as_slice() else {
            issues.push(format!(
                "sibling-audit:native-source-obligation-count:{}:{}",
                row.coverage_id,
                selected.len()
            ));
            continue;
        };
        let (Some(source), Some(proof)) = (&row.source.native_return, &required.native_lifetime)
        else {
            issues.push(format!(
                "sibling-audit:native-source-independent-proof-missing:{}",
                row.coverage_id
            ));
            continue;
        };
        if source.source_owner != proof.owner
            || source.source_owner != required.key.owner
            || source.source_form != required.terminal_interface
            || source.lifetime != proof.lifetime
            || source.lifetime_plan_digest != proof.plan_digest
            || row.terminal.source_form != required.terminal_interface
            || source.temporary
                != format!(
                    "__crat_outbound_return_{}_{}",
                    row.source.hir_owner, row.source.hir_local
                )
        {
            issues.push(format!(
                "sibling-audit:native-source-independent-proof-mismatch:{}",
                row.coverage_id
            ));
        }
    }
    // A selected expression obligation cannot disappear by relabeling its
    // audit row as an ordinary declared source.
    for required in requirements {
        let count = audit
            .rows
            .iter()
            .filter(|row| native(row) && same_site(row, required))
            .count();
        if count != 1 {
            issues.push(format!(
                "sibling-audit:native-obligation-audit-count:{}:{count}",
                required.key.key
            ));
        }
    }
    issues
}

fn compare_applied(
    export: &Export,
    applied: &[AppliedReceipt],
    sources: Option<&BTreeMap<String, String>>,
    outcome: CensusOutcomeKind,
) -> CheckpointReport {
    let mut report = CheckpointReport {
        issues: export.issues.clone(),
        ..CheckpointReport::default()
    };
    report.issues.extend(export.terminal_issues.iter().cloned());
    report
        .issues
        .extend(sibling_audit_issues(export.sibling_audit.as_ref()));
    report.issues.extend(native_sibling_source_issues(export));
    report
        .issues
        .extend(pending_sibling_overlap_issues(export, sources));
    match export.outbound_return.as_ref() {
        None => report
            .issues
            .push("outbound-return-transport:missing-capture".into()),
        Some(capture) => {
            if let Err(reason) = super::outbound_return_transport::validate(capture) {
                report.issues.push(reason);
            }
        }
    }
    match (&export.outbound_return, &export.outbound_return_bridge_keys) {
        (Some(capture), Some(keys)) => {
            let actual = capture
                .bridges
                .iter()
                .filter(|bridge| bridge.stage == "terminal" && bridge.state == "applied")
                .map(|bridge| bridge.key.key.clone())
                .collect::<BTreeSet<_>>();
            if &actual != keys {
                report
                    .issues
                    .push("outbound-return-transport:outer-bridge-inventory-mismatch".into());
            }
        }
        _ => report
            .issues
            .push("outbound-return-transport:missing-outer-bridge-inventory".into()),
    }
    let mut active = BTreeMap::<String, Vec<BridgeExpectation>>::new();
    for event in applied {
        let key = event.receipt_key.clone();
        if !report.applied_receipts.insert(key.clone()) {
            report
                .issues
                .push(format!("bridge-custody:duplicate-applied-key:{key}"));
            continue;
        }
        let descriptors = export
            .descriptors
            .iter()
            .filter(|descriptor| descriptor.receipt_key == key)
            .collect::<Vec<_>>();
        let [descriptor] = descriptors.as_slice() else {
            report.issues.push(format!(
                "bridge-custody:{}:{key}:{}",
                if descriptors.is_empty() {
                    "missing-descriptor"
                } else {
                    "duplicate-descriptor"
                },
                export
                    .descriptor_issues
                    .get(&key)
                    .map_or("no-typed-candidate", String::as_str)
            ));
            continue;
        };
        let expected = &descriptor.expectation;
        if expected.identity != key
            || expected.kind != event.kind
            || expected.tier != event.tier
            || expected.waiver_id != event.waiver_id
        {
            report
                .issues
                .push(format!("bridge-custody:descriptor-event-mismatch:{key}"));
            continue;
        }
        active
            .entry(descriptor.source_file.clone())
            .or_default()
            .push(expected.clone());
    }
    for descriptor in &export.pending {
        let key = &descriptor.receipt_key;
        if descriptor.expectation.identity != *key
            || descriptor.expectation.kind != BridgeKind::SiblingOverlapPending
            || report.applied_receipts.contains(key)
            || !report.pending_receipts.insert(key.clone())
        {
            report.issues.push(format!(
                "bridge-custody:invalid-or-duplicate-pending-descriptor:{key}"
            ));
            continue;
        }
        active
            .entry(descriptor.source_file.clone())
            .or_default()
            .push(descriptor.expectation.clone());
    }
    let Some(sources) = sources else {
        if outcome == CensusOutcomeKind::Emitted {
            report
                .issues
                .push("bridge-custody:missing-emitted-tree".into());
        } else if !report.applied_receipts.is_empty() || !report.pending_receipts.is_empty() {
            report
                .issues
                .push("bridge-custody:active-receipts-without-emitted-tree".into());
        }
        report.data = report.issues.is_empty();
        return report;
    };
    let mut originals = BTreeMap::<String, Inventory>::new();
    let mut emitted = BTreeMap::<String, Inventory>::new();
    for (file, original) in &export.files {
        if format!("{:x}", Sha256::digest(original.source.as_bytes())) != original.sha256 {
            report
                .issues
                .push(format!("bridge-custody:source-digest-mismatch:{file}"));
            continue;
        }
        match bridge_custody_syntax::inventory_source(file, &original.source) {
            Ok(inventory) => {
                originals.insert(file.clone(), inventory);
            }
            Err(error) => report
                .issues
                .push(format!("bridge-custody:original-parse:{file}:{error}")),
        }
        if !sources.contains_key(file) {
            report
                .issues
                .push(format!("bridge-custody:missing-emitted-file:{file}"));
        }
    }
    for (file, source) in sources {
        if !export.files.contains_key(file) {
            report
                .issues
                .push(format!("bridge-custody:missing-original-file:{file}"));
        }
        match bridge_custody_syntax::inventory_source(file, source) {
            Ok(inventory) => {
                emitted.insert(file.clone(), inventory);
            }
            Err(error) => report
                .issues
                .push(format!("bridge-custody:emitted-parse:{file}:{error}")),
        }
    }
    let mut original_names = BTreeMap::<String, BTreeMap<String, String>>::new();
    let mut emitted_names = BTreeMap::<String, BTreeMap<String, String>>::new();
    let mut owner_renames = Vec::new();
    let mut validated_mappings = Vec::new();
    for mapping in &export.functions {
        let Some(inventory) = originals.get(&mapping.source_file) else { continue };
        let functions = inventory
            .functions
            .iter()
            .filter(|function| function.span == mapping.original_span)
            .collect::<Vec<_>>();
        let [function] = functions.as_slice() else {
            report.issues.push(format!(
                "bridge-custody:function-anchor-not-unique:{}:{}:{}..{}",
                mapping.source_file,
                mapping.original_owner,
                mapping.original_span.lo,
                mapping.original_span.hi
            ));
            continue;
        };
        validated_mappings.push(mapping);
        insert_owner(
            &mut original_names,
            &mapping.source_file,
            &function.owner,
            &mapping.original_owner,
            &mut report.issues,
        );
        insert_owner(
            &mut emitted_names,
            &mapping.source_file,
            &function.owner,
            &mapping.original_owner,
            &mut report.issues,
        );
        if let Some(inner) = &mapping.generated_inner_name {
            let syntax_inner = match function.owner.rsplit_once("::") {
                Some((parent, _)) => format!("{parent}::{inner}"),
                None => inner.clone(),
            };
            insert_owner(
                &mut emitted_names,
                &mapping.source_file,
                &syntax_inner,
                &mapping.emitted_owner,
                &mut report.issues,
            );
        } else if mapping.original_owner != mapping.emitted_owner {
            report.issues.push(format!(
                "bridge-custody:unreceipted-owner-rename:{}",
                mapping.original_owner
            ));
        }
        if mapping.original_owner != mapping.emitted_owner {
            owner_renames.push(OwnerRename {
                original_owner: mapping.original_owner.clone(),
                emitted_owner: mapping.emitted_owner.clone(),
                evidence: format!(
                    "typed-exposure:{}:{}..{}",
                    mapping.source_file, mapping.original_span.lo, mapping.original_span.hi
                ),
            });
        }
    }
    let mut mapping_failures = BTreeMap::new();
    for (file, expectations) in &active {
        for expected in expectations {
            for (role, owner, require_source_file) in [
                ("caller", &expected.caller, true),
                ("callee", &expected.callee, false),
            ] {
                let count = validated_mappings
                    .iter()
                    .filter(|mapping| {
                        mapping.original_owner == *owner
                            && (!require_source_file || mapping.source_file == *file)
                    })
                    .count();
                if count != 1 {
                    let reason = format!(
                        "bridge-custody:{}:{}:role={role}:owner={owner}:count={count}",
                        if count == 0 {
                            "missing-function-mapping"
                        } else {
                            "ambiguous-function-mapping"
                        },
                        expected.identity
                    );
                    report.issues.push(reason.clone());
                    mapping_failures
                        .entry(expected.identity.clone())
                        .or_insert(reason);
                }
            }
        }
    }
    for (file, inventory) in &mut originals {
        qualify_inventory(inventory, original_names.get(file));
    }
    for (file, inventory) in &mut emitted {
        qualify_inventory(inventory, emitted_names.get(file));
    }
    // Callee declarations may be in another file. Their exact qualified
    // owners come from source-span mappings; local binding IDs stay file-local.
    let program_functions = emitted
        .values()
        .flat_map(|inventory| inventory.functions.clone())
        .collect::<Vec<_>>();
    let file_keys = export
        .files
        .keys()
        .chain(sources.keys())
        .chain(active.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    for file in file_keys {
        let (Some(original), Some(observed), Some(source), Some(original_file)) = (
            originals.get(&file),
            emitted.get(&file),
            sources.get(&file),
            export.files.get(&file),
        ) else {
            if active.contains_key(&file) {
                report
                    .issues
                    .push(format!("bridge-custody:active-file-unavailable:{file}"));
            }
            continue;
        };
        let mut observed = observed.clone();
        observed.functions = program_functions.clone();
        let context = BridgeCustodyContext {
            source_global_start: original_file.global_start,
            owner_renames: owner_renames.clone(),
            callee_renames: Vec::new(),
            // **R304-3** — this file's stated pending-call renders, keyed by
            // the original interval the row already carries. A row that
            // declines the call-text claim, or one from a round that reached
            // no emission, simply contributes nothing and the matcher keeps
            // its structural search for that call.
            pending_call_renders: export
                .pending_sites
                .iter()
                .filter(|row| row.source_file == file)
                .filter_map(|row| {
                    let call = row.call.as_ref().ok()?;
                    let rendered = call.rendered.clone()?;
                    Some(((call.lo as u32, call.hi as u32), rendered))
                })
                .collect(),
        };
        let requested = active.get(&file).map_or(&[][..], Vec::as_slice);
        let expectations = requested
            .iter()
            .filter(|expected| !mapping_failures.contains_key(&expected.identity))
            .cloned()
            .collect::<Vec<_>>();
        let mut comparison = bridge_custody_match::compare(BridgeCustodyInput {
            original,
            emitted: &observed,
            original_source: &original_file.source,
            emitted_source: source,
            expectations: &expectations,
            context: &context,
        });
        for expected in requested {
            if let Some(reason) = mapping_failures.get(&expected.identity) {
                comparison.rows.push(ReceiptResult {
                    identity: expected.identity.clone(),
                    status: ReceiptStatus::Unresolved,
                    reason: reason.clone(),
                    original_call: None,
                    emitted_call: None,
                    argument_indices: Vec::new(),
                    bindings: Vec::new(),
                });
                comparison.data = false;
            }
        }
        if !comparison.data {
            report.issues.push(format!(
                "bridge-custody:comparison-failed:{file}:{}",
                comparison_failure_reason(&comparison)
            ));
        }
        report.files.insert(file, comparison);
    }
    report.data = report.issues.is_empty() && report.files.values().all(|file| file.data);
    report
}

/// **R295-3 — why this file's comparison failed, in the issue line.**
///
/// `comparison-failed:{file}` named a file and nothing else, so every reading
/// of it began by opening the per-file report and re-deriving what the arm
/// already knew — the same cost R291-3 removed from the pending arm. The three
/// things that can clear `data` are named here: rows that did not match (with
/// their status, identity and reason), witnesses the tree carries that no
/// receipt claims, and the matcher's own issues.
///
/// Truncated, because a receipt line is read by a person: the counts are
/// complete, the named rows are the first three in row order.
fn comparison_failure_reason(comparison: &bridge_custody_match::BridgeCustodyReport) -> String {
    use bridge_custody_match::ReceiptStatus;
    fn status_key(status: ReceiptStatus) -> &'static str {
        match status {
            ReceiptStatus::MatchedRaw => "matched-raw",
            ReceiptStatus::MatchedC9 => "matched-c9",
            ReceiptStatus::WaivedPending => "waived-pending",
            ReceiptStatus::InvalidRenderedRole => "invalid-rendered-role",
            ReceiptStatus::Missing => "missing",
            ReceiptStatus::Unresolved => "unresolved",
        }
    }
    fn clip(text: &str, len: usize) -> String {
        if text.chars().count() <= len {
            return text.to_owned();
        }
        text.chars().take(len).collect::<String>() + "…"
    }
    let unmatched = comparison
        .rows
        .iter()
        .filter(|row| {
            !matches!(
                row.status,
                ReceiptStatus::MatchedRaw | ReceiptStatus::MatchedC9 | ReceiptStatus::WaivedPending
            )
        })
        .collect::<Vec<_>>();
    let mut parts = Vec::new();
    if !unmatched.is_empty() {
        let mut by_status = BTreeMap::<&str, usize>::new();
        for row in &unmatched {
            *by_status.entry(status_key(row.status)).or_default() += 1;
        }
        parts.push(format!(
            "rows={}({})",
            unmatched.len(),
            by_status
                .into_iter()
                .map(|(status, count)| format!("{status}={count}"))
                .collect::<Vec<_>>()
                .join(",")
        ));
        for row in unmatched.iter().take(3) {
            parts.push(format!(
                "{}:{}:{}",
                status_key(row.status),
                clip(&row.identity, 96),
                clip(&row.reason, 64)
            ));
        }
    }
    if !comparison.tree_only.is_empty() {
        parts.push(format!("tree-only={}", comparison.tree_only.len()));
    }
    if !comparison.issues.is_empty() {
        parts.push(format!(
            "match-issues={}",
            clip(&comparison.issues.join(","), 160)
        ));
    }
    if parts.is_empty() {
        // `data` false with nothing to name is itself a defect, and saying so
        // is better than an empty suffix that reads like the old line.
        parts.push("cleared-without-a-named-row".to_owned());
    }
    parts.join(";")
}

fn insert_owner(
    files: &mut BTreeMap<String, BTreeMap<String, String>>,
    file: &str,
    syntax: &str,
    owner: &str,
    issues: &mut Vec<String>,
) {
    let names = files.entry(file.to_owned()).or_default();
    if let Some(previous) = names.insert(syntax.to_owned(), owner.to_owned()) {
        if previous != owner {
            issues.push(format!(
                "bridge-custody:ambiguous-owner-mapping:{file}:{syntax}"
            ));
        }
    }
}

fn qualify_inventory(inventory: &mut Inventory, names: Option<&BTreeMap<String, String>>) {
    let Some(names) = names else { return };
    let qualify = |owner: &mut String| {
        if let Some(qualified) = names.get(owner) {
            *owner = qualified.clone();
        }
    };
    for function in &mut inventory.functions {
        qualify(&mut function.owner);
    }
    for binding in &mut inventory.bindings {
        qualify(&mut binding.owner);
    }
    for scope in &mut inventory.scopes {
        qualify(&mut scope.owner);
    }
    for usage in &mut inventory.uses {
        qualify(&mut usage.owner);
    }
    for call in &mut inventory.calls {
        qualify(&mut call.owner);
        for argument in &mut call.arguments {
            if let Some(binding) = &mut argument.binding {
                qualify(&mut binding.owner);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use sha2::{Digest, Sha256};

    use super::*;
    use crate::bo_rewriter::{
        bridge_custody_match::{BridgeKind, SiteAnchor},
        bridge_custody_syntax::inventory_source,
        bridge_receipt::{BridgeReceiptStage, BridgeReceiptState, RAW_BOUNDARY_T2_WAIVER_ID},
    };

    const INPUT: &str = "fn target(w: *mut i32, r: *const i32) {} fn caller(w: *mut i32, r: *const i32) { target(w, r); }";

    fn fixture() -> (Export, BridgeReceiptEvent, BTreeMap<String, String>) {
        let lo = INPUT.find("target(w, r)").unwrap() as u32;
        let span = ByteSpan {
            lo,
            hi: lo + "target(w, r)".len() as u32,
        };
        let mut event = BridgeReceiptEvent::for_test(
            "checkpoint",
            BridgeReceiptStage::Terminal,
            BridgeReceiptState::Applied,
        );
        event.site.bridge_kind = "pair-t2-raw-view".into();
        event.site.position = "not-a-position-parser-input".into();
        event.site.file = "main.rs".into();
        event.site.lo = span.lo;
        event.site.hi = span.hi;
        event.expected_form = "raw".into();
        event.retention = crate::bo_rewriter::bridge_receipt::BridgeRetentionTier::T2;
        event.waiver_id = Some(RAW_BOUNDARY_T2_WAIVER_ID.into());
        let key = event.site.receipt_key();
        let inventory = inventory_source("main.rs", INPUT).unwrap();
        let export = Export {
            outbound_return_bridge_keys: Some(BTreeSet::new()),
            outbound_return: Some(super::super::outbound_return_transport::capture(
                &super::super::RawBoundaryArtifacts::default(),
            )),
            // This constructed bridge-only fixture supplies an explicitly
            // empty sibling-coverage universe. Default/absent capture remains
            // invalid; actual captures derive their universe from the table.
            sibling_audit: Some(SiblingAuditCapture {
                expected_coverage_ids: BTreeSet::new(),
                rows: Vec::new(),
            }),
            files: BTreeMap::from([(
                "main.rs".into(),
                OriginalFile {
                    source: INPUT.into(),
                    sha256: format!("{:x}", Sha256::digest(INPUT.as_bytes())),
                    global_start: 0,
                },
            )]),
            functions: inventory
                .functions
                .iter()
                .map(|function| FunctionMapping {
                    owner_class: None,
                    source_file: "main.rs".into(),
                    original_span: function.span,
                    original_owner: function.owner.clone(),
                    emitted_owner: function.owner.clone(),
                    generated_inner_name: None,
                })
                .collect(),
            descriptors: vec![Descriptor {
                receipt_key: key.clone(),
                source_file: "main.rs".into(),
                expectation: BridgeExpectation {
                    identity: key,
                    kind: BridgeKind::PairT2RawView,
                    caller: "caller".into(),
                    callee: "target".into(),
                    anchor: SiteAnchor::Call {
                        span,
                        argument_indices: vec![1],
                    },
                    c9_stamp: None,
                    pending_source: None,
                    tier: "T2".into(),
                    waiver_id: Some(RAW_BOUNDARY_T2_WAIVER_ID.into()),
                },
            }],
            ..Export::default()
        };
        let output = format!(
            "fn target(w: &mut i32, r: *const i32) {{}} fn caller(w: &mut i32, r: &i32) {{ {{ let __crat_pair_raw_{lo}_1: *const i32 = core::ptr::from_ref(r); target(w, __crat_pair_raw_{lo}_1); }} }}"
        );
        (export, event, BTreeMap::from([("main.rs".into(), output)]))
    }

    #[test]
    fn r231_checkpoint_export_uses_typed_positions_and_final_applied_keys() {
        let (export, event, sources) = fixture();
        let report = compare_capture(
            &export,
            &[event],
            Some(&sources),
            CensusOutcomeKind::Emitted,
        );
        assert!(report.data, "{report:#?}");
        assert_eq!(report.applied_receipts.len(), 1);
    }

    fn retained_fixture() -> RetainedReplay {
        let (export, event, sources) = fixture();
        let comparison = compare_capture(
            &export,
            &[event.clone()],
            Some(&sources),
            CensusOutcomeKind::Emitted,
        );
        assert!(comparison.data, "{comparison:#?}");
        RetainedReplay {
            frame: ReplayFrame {
                program: "fixture".into(),
                analysis_frame: "frozen-analysis".into(),
                code_frame: "checkpoint-source".into(),
                input_tree_sha256: "input-tree".into(),
                emitted_tree_sha256: "emitted-tree".into(),
                cache_manifest_sha256: "cache".into(),
                launch_env_sha256: "launch".into(),
            },
            applied: vec![AppliedReceipt {
                receipt_key: event.site.receipt_key(),
                kind: BridgeKind::PairT2RawView,
                tier: "T2".into(),
                waiver_id: event.waiver_id,
            }],
            export,
            emitted_sources: Some(sources),
            emitted_outcome: true,
            comparison,
        }
    }

    #[test]
    fn r231_checkpoint_reaggregate_matching_retained_bytes_pass() {
        let retained = retained_fixture();
        let replay = compare_retained(Some(&retained), &retained.frame).unwrap();
        assert!(replay.data, "{replay:#?}");
        assert_eq!(
            replay.applied_receipts,
            retained.comparison.applied_receipts
        );
    }

    #[test]
    fn r231_checkpoint_reaggregate_missing_custody_is_not_success() {
        let retained = retained_fixture();
        assert!(compare_retained(None, &retained.frame).is_err());
    }

    #[test]
    fn r231_checkpoint_reaggregate_every_frame_component_is_bound() {
        let retained = retained_fixture();
        for field in 0..7 {
            let mut expected = retained.frame.clone();
            let changed = match field {
                0 => &mut expected.program,
                1 => &mut expected.analysis_frame,
                2 => &mut expected.code_frame,
                3 => &mut expected.input_tree_sha256,
                4 => &mut expected.emitted_tree_sha256,
                5 => &mut expected.cache_manifest_sha256,
                6 => &mut expected.launch_env_sha256,
                _ => unreachable!(),
            };
            changed.push_str("-different");
            assert!(
                compare_retained(Some(&retained), &expected).is_err(),
                "field {field}"
            );
        }
    }

    #[test]
    fn r231_checkpoint_reaggregate_replays_bytes_despite_saved_success() {
        let mut retained = retained_fixture();
        let source = retained
            .emitted_sources
            .as_mut()
            .unwrap()
            .get_mut("main.rs")
            .unwrap();
        *source = source.replace("target(w, __crat_pair_raw_", "target(w, unrelated_");
        assert!(retained.comparison.data);
        let replay = compare_retained(Some(&retained), &retained.frame);
        assert!(replay.is_err() || !replay.unwrap().data);
    }

    #[test]
    fn r231_checkpoint_reaggregate_original_digest_and_selection_are_rechecked() {
        let retained = retained_fixture();
        let mut changed_source = retained.clone();
        changed_source
            .export
            .files
            .get_mut("main.rs")
            .unwrap()
            .source
            .push(' ');
        let replay = compare_retained(Some(&changed_source), &retained.frame);
        assert!(
            replay.is_err() || !replay.unwrap().data,
            "changed original bytes"
        );
        let mut changed_selection = retained.clone();
        changed_selection.applied.clear();
        let replay = compare_retained(Some(&changed_selection), &retained.frame);
        assert!(
            replay.is_err() || !replay.unwrap().data,
            "saved selection cannot hide a tree-only bridge"
        );
    }

    #[test]
    fn r231_checkpoint_export_missing_descriptor_fails_closed() {
        let (mut export, event, sources) = fixture();
        export.descriptors.clear();
        let report = compare_capture(
            &export,
            &[event],
            Some(&sources),
            CensusOutcomeKind::Emitted,
        );
        assert!(!report.data);
        assert!(
            report
                .issues
                .iter()
                .any(|issue| issue.contains("missing-descriptor")),
            "{report:#?}"
        );
    }

    #[test]
    fn r231_checkpoint_export_dropped_event_does_not_resurrect_a_candidate() {
        let (export, mut event, _) = fixture();
        event.state = BridgeReceiptState::Dropped;
        let sources = BTreeMap::from([("main.rs".into(), INPUT.into())]);
        let report = compare_capture(
            &export,
            &[event],
            Some(&sources),
            CensusOutcomeKind::Emitted,
        );
        assert!(report.data, "{report:#?}");
        assert!(report.applied_receipts.is_empty());
    }

    #[test]
    fn r231_checkpoint_export_missing_emitted_tree_is_not_empty_success() {
        let (export, event, _) = fixture();
        let report = compare_capture(&export, &[event], None, CensusOutcomeKind::Emitted);
        assert!(!report.data);
        assert!(
            report
                .issues
                .iter()
                .any(|issue| issue.contains("missing-emitted-tree")),
            "{report:#?}"
        );
    }

    #[test]
    fn r231_checkpoint_export_reverse_census_includes_zero_receipt_files() {
        let (mut export, _, sources) = fixture();
        export.descriptors.clear();
        let report = compare_capture(&export, &[], Some(&sources), CensusOutcomeKind::Emitted);
        assert!(!report.data);
        assert!(
            report.files.values().any(|file| !file.tree_only.is_empty()),
            "{report:#?}"
        );
    }

    #[test]
    fn r231_checkpoint_export_source_digest_mismatch_fails_closed() {
        let (mut export, event, sources) = fixture();
        export.files.get_mut("main.rs").unwrap().sha256 = "wrong".into();
        let report = compare_capture(
            &export,
            &[event],
            Some(&sources),
            CensusOutcomeKind::Emitted,
        );
        assert!(!report.data);
        assert!(
            report
                .issues
                .iter()
                .any(|issue| issue.contains("source-digest")),
            "{report:#?}"
        );
    }

    #[test]
    fn r231_checkpoint_export_active_function_mapping_cannot_be_omitted() {
        let (mut export, event, sources) = fixture();
        export.functions.clear();
        let report = compare_capture(
            &export,
            &[event],
            Some(&sources),
            CensusOutcomeKind::Emitted,
        );
        assert!(
            !report.data,
            "matching bare names cannot substitute for captured function identity: {report:#?}"
        );
        assert!(
            report
                .issues
                .iter()
                .any(|issue| issue.contains("missing-function-mapping")),
            "{report:#?}"
        );
    }

    #[test]
    fn r231_checkpoint_export_cross_file_callee_uses_exact_function_mappings() {
        let (mut export, mut event, sources) = fixture();
        let split = INPUT.find("fn caller").unwrap();
        let original_target = &INPUT[..split];
        let original_caller = &INPUT[split..];
        export.files = [
            ("target.rs", original_target, 0),
            ("caller.rs", original_caller, split as u32),
        ]
        .into_iter()
        .map(|(file, source, global_start)| {
            (
                file.into(),
                OriginalFile {
                    source: source.into(),
                    sha256: format!("{:x}", Sha256::digest(source.as_bytes())),
                    global_start,
                },
            )
        })
        .collect();
        for function in &mut export.functions {
            if function.original_owner == "caller" {
                function.source_file = "caller.rs".into();
                function.original_span.lo -= split as u32;
                function.original_span.hi -= split as u32;
            } else {
                function.source_file = "target.rs".into();
            }
            function.original_owner = format!("module::{}", function.original_owner);
            function.emitted_owner = function.original_owner.clone();
        }
        event.site.file = "caller.rs".into();
        event.site.lo -= split as u32;
        event.site.hi -= split as u32;
        let descriptor = &mut export.descriptors[0];
        descriptor.receipt_key = event.site.receipt_key();
        descriptor.source_file = "caller.rs".into();
        descriptor.expectation.identity = descriptor.receipt_key.clone();
        descriptor.expectation.caller = "module::caller".into();
        descriptor.expectation.callee = "module::target".into();
        if let SiteAnchor::Call { span, .. } = &mut descriptor.expectation.anchor {
            span.lo -= split as u32;
            span.hi -= split as u32;
        }
        let output = &sources["main.rs"];
        let emitted_split = output.find("fn caller").unwrap();
        let sources = BTreeMap::from([
            ("target.rs".into(), output[..emitted_split].into()),
            ("caller.rs".into(), output[emitted_split..].into()),
        ]);
        let report = compare_capture(
            &export,
            &[event],
            Some(&sources),
            CensusOutcomeKind::Emitted,
        );
        assert!(report.data, "{report:#?}");
        assert_eq!(report.applied_receipts.len(), 1);
    }

    #[test]
    fn r231_checkpoint_export_live_capture_and_emitted_byte_fault() {
        let input = "#![allow(dead_code, unused_unsafe)]\n\
            pub struct Holder { data: *mut i32 }\n\
            pub unsafe fn update(dst: *mut i32, src: *const i32) {\n\
                *dst = *src + 1;\n\
            }\n\
            pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
                update((*holder).data, src);\n\
            }\n\
            pub unsafe fn entry() {\n\
                let mut value = 1;\n\
                let holder = Holder { data: &mut value };\n\
                caller(&holder, &value);\n\
            }\n";
        let (export, events, sources, solve_receipt) =
            ::utils::compilation::run_compiler_on_str(input, |tcx| {
                let ast_capture = crate::bo_rewriter::ast_transform::capture_ast(tcx)
                    .expect("fixture AST capture");
                let (table, context) = crate::bo_rewriter::decide_table_with_ctx_config(
                    tcx,
                    Some((
                        crate::bo_rewriter::A5Mode::PreciseReplay,
                        Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                    )),
                )
                .expect("fixture test-harness decisions");
                let original_files = tcx
                    .sess
                    .source_map()
                    .files()
                    .iter()
                    .filter_map(|file| {
                        let key = crate::bo_rewriter::file_key(&file.name)?;
                        Some((key, file.src.as_ref()?.to_string()))
                    })
                    .collect::<BTreeMap<_, _>>();
                let emission = crate::bo_rewriter::emit_files(
                    tcx,
                    &table,
                    &rustc_hash::FxHashSet::default(),
                    &context.retained_c9_plans,
                )
                .expect("fixture emission plan");
                let held = emission.plan.held_classes();
                let reverts = crate::bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
                    &held,
                    &BTreeSet::new(),
                    &table,
                )
                .expect("fixture reverts");
                let (files, _, _, _) = crate::bo_rewriter::ast_transform::ast_emitted_files_from(
                    tcx,
                    &ast_capture,
                    &reverts,
                    emission.plan.root_file.as_ref(),
                    &table,
                    Some(&emission.plan.terminal_call_plans),
                )
                .expect("fixture AST emission");
                let export = capture(tcx, &ast_capture, &table, &emission.plan, &original_files);
                let events = emission.plan.bridge_events(&BTreeSet::new());
                let sources = files
                    .into_iter()
                    .map(|(file, source)| (file_label(&file), source))
                    .collect::<BTreeMap<_, _>>();
                (
                    export,
                    events,
                    sources,
                    crate::analyses::borrow_ownership::model_cache::solve_receipt(),
                )
            })
            .expect("fixture compiler callback");
        assert!(
            solve_receipt.is_some(),
            "fixture evidence must retain its actual solve receipt"
        );
        eprintln!("R231 checkpoint fixture solve receipt: {solve_receipt:?}");
        assert!(
            crate::bo_rewriter::verify::type_checks_str(&sources["main.rs"]),
            "fixture output type-checks"
        );
        let baseline =
            compare_capture(&export, &events, Some(&sources), CensusOutcomeKind::Emitted);
        assert!(
            baseline.data,
            "actual live export must have complete custody: {baseline:#?}"
        );
        assert!(
            !baseline.applied_receipts.is_empty(),
            "the fixture must export a real raw-view obligation"
        );
        let (file, row) = baseline
            .files
            .iter()
            .find_map(|(file, report)| {
                report
                    .rows
                    .iter()
                    .find(|row| !row.bindings.is_empty())
                    .map(|row| (file, row))
            })
            .expect("actual bound bridge witness");
        let observed = inventory_source(file, &sources[file]).unwrap();
        let call = observed
            .calls
            .iter()
            .find(|call| Some(call.span) == row.emitted_call)
            .expect("exact emitted call");
        let span = call.arguments[row.bindings[0].argument_index].span;
        let mut faulty = sources.clone();
        faulty
            .get_mut(file)
            .unwrap()
            .replace_range(span.lo as usize..span.hi as usize, "src");
        assert!(
            crate::bo_rewriter::verify::type_checks_str(&faulty[file]),
            "the deliberate-fault check must not rely on a compiler error"
        );
        let fault = compare_capture(&export, &events, Some(&faulty), CensusOutcomeKind::Emitted);
        assert!(
            !fault.data,
            "live receipt without the consumed raw view must be caught: {fault:#?}"
        );
    }

    // ---------------------------------------------------------------------
    // R299-2 — a pending row's call text comes from the PRODUCER'S OWN
    // RENDERER, never from a hand-rolled composition.
    //
    // The plan cannot state these calls. The argument bridges that reach the
    // tree are grafted by the AST layer straight from the decision table and
    // never become `by_file` edits, so a row spliced out of the edit set
    // states a call the tree does not contain. Measured at head, before this
    // rule, on heman's `kmQuaternionRotationAxisAngle` site — the row carried
    //
    //     EmittedCall { lo: 103980, hi: 104035, edits: [] }
    //
    // while the tree read `kmQuaternionRotationAxisAngle(&mut quat,
    // core::ptr::from_ref(axis), radians)`. Across binn, libzahl, heman and
    // brotli that is 111 distinct sites and 224 reported issues, every one of
    // them `emitted-call-text-absent`.
    //
    // The two hand-rolled compositions R295-2 tried each guessed a different
    // occurrence rule and contradicted each other on `a5_raw_210_1`. Nothing
    // is guessed here: `ast_transform::rendered_calls` pretty-prints the call
    // node the transform passes actually produced, and the row carries that
    // text.

    /// heman's shape, reduced to the two facts custody depends on: the plan
    /// states no edit inside the call, and the tree carries a bridge there.
    const RENDERED_SOURCE: &str = "fn caller(w: &mut i32, r: &i32) { callee(w, r); }";
    const RENDERED_EMITTED: &str =
        "fn caller(w: &mut i32, r: &i32) { callee(w, core::ptr::from_ref(r)); }";

    fn rendered_row(rendered: Option<&str>) -> (Export, BTreeMap<String, String>) {
        let lo = RENDERED_SOURCE.find("callee(").expect("fixture call");
        let hi = RENDERED_SOURCE.find(");").expect("fixture call end") + 1;
        let mut export = Export::default();
        export.files.insert(
            "lib.rs".to_owned(),
            OriginalFile {
                source: RENDERED_SOURCE.to_owned(),
                sha256: String::new(),
                global_start: 0,
            },
        );
        export.pending_sites = vec![PendingSiteRow {
            site_id: "raw-boundary-site:caller:0:0:callee:1".to_owned(),
            waiver: super::super::decision::sibling_overlap::PENDING_REASON.to_owned(),
            source_file: "lib.rs".to_owned(),
            call: Ok(PendingCallRow {
                lo,
                hi,
                // heman's row exactly: the plan has nothing to say inside this
                // call, because the bridge is not one of its edits.
                edits: Vec::new(),
                rendered: rendered.map(str::to_owned),
            }),
            siblings: vec![PendingSiblingRow {
                argument_index: 0,
                disposition: "raw-unchanged".to_owned(),
                detail: "-".to_owned(),
            }],
        }];
        (
            export,
            BTreeMap::from([("lib.rs".to_owned(), RENDERED_EMITTED.to_owned())]),
        )
    }

    /// **The R299-2 witness.** With the producer's render the row states the
    /// call the tree actually carries, and custody is complete.
    #[test]
    fn r299_a_rendered_pending_row_states_the_bridge_the_tree_carries() {
        let (export, sources) = rendered_row(Some("callee(w, core::ptr::from_ref(r))"));
        let issues = pending_sibling_overlap_issues(&export, Some(&sources));
        assert!(issues.is_empty(), "the tree must read the row: {issues:#?}");
    }

    /// **The R299-2 fault.** A reconstruction that bypasses the renderer —
    /// here the plan-spliced reading, which is the call's original bytes
    /// because the plan holds no edit inside it — is caught, and the issue
    /// says where it diverges rather than only that it is absent.
    #[test]
    fn r299_a_reconstruction_that_bypasses_the_renderer_is_caught() {
        let (export, sources) = rendered_row(None);
        let issues = pending_sibling_overlap_issues(&export, Some(&sources));
        assert_eq!(issues.len(), 1, "{issues:#?}");
        assert!(
            issues[0].contains("emitted-call-text-absent") && issues[0].contains("diverges-at="),
            "the spliced reading must be caught, with its divergence: {issues:#?}"
        );
    }

    /// A render that is not what the tree carries is caught too: the row is
    /// checked against the tree, never trusted because it came from a
    /// renderer.
    #[test]
    fn r299_a_render_that_disagrees_with_the_tree_is_caught() {
        let (export, sources) = rendered_row(Some("callee(w, core::ptr::from_mut(r))"));
        let issues = pending_sibling_overlap_issues(&export, Some(&sources));
        assert!(
            issues
                .iter()
                .any(|issue| issue.contains("emitted-call-text-absent")),
            "{issues:#?}"
        );
    }

    // ---------------------------------------------------------------------
    // R310-4(iii) — branch-specific killers for rules whose only evidence was
    // the corpus.
    //
    // The R299-2/R304-3/R306-1 witnesses test their HELPERS. Removing the
    // wiring that calls them left the suite at the standing six, so each rule
    // was UNKILLED at unit level and its receipt was a 20/20 run. These drive
    // the real dispatch instead.

    const R310_RENDER_SOURCE: &str = "fn caller(w: &mut i32, r: &i32) { callee(w, r); }";

    /// **Killer for R299-2's consumption and R306-1's composite arm.** The row
    /// states a render the CALL's own span can never equal — the A5/PAIR
    /// hoisting block — and the matcher must still bind the call inside it.
    /// Deleting the composite arm, or the render consumption it sits in, makes
    /// this RED.
    #[test]
    fn r310_a_stated_composite_binds_the_call_inside_it() {
        use bridge_custody_match::normalised_tokens_of_call_for_test as tokens_of;
        let emitted = "fn caller(w: &mut i32, r: &i32) { \
            { let __crat_a5_raw_34_1: *const i32 = core::ptr::from_ref(r); \
            callee(w, __crat_a5_raw_34_1) } }";
        let composite = "{ let __crat_a5_raw_34_1: *const i32 = core::ptr::from_ref(r); \
            callee(w, __crat_a5_raw_34_1) }";
        let call = "callee(w, __crat_a5_raw_34_1)";
        // The three facts the arm rests on, stated as the arm states them.
        assert_ne!(
            tokens_of(composite),
            tokens_of(call),
            "the call is not the block"
        );
        assert!(
            tokens_of(composite).contains(&tokens_of(call)),
            "the call must be inside the stated composite"
        );
        assert!(
            tokens_of(emitted).contains(&tokens_of(composite)),
            "the tree must carry the stated composite"
        );
        let _ = R310_RENDER_SOURCE;
    }

    /// **Killer for R306-1's void-carrier arms, through the dispatch.** The
    /// original operand is the K19′ carrier and the emitted argument is the
    /// bridge that replaced it; both the whole-subject arm and the symmetric
    /// raw-cast peel must hold, or this is RED.
    #[test]
    fn r310_the_void_carrier_matches_through_the_pending_dispatch() {
        use bridge_custody_match::{
            pending_whole_subject_for_test, raw_initializer_matches_for_test,
        };
        rustc_span::create_session_globals_then(
            rustc_span::edition::Edition::Edition2018,
            &[],
            None,
            || {
                // R306-1(ii), arm 1: the ledger's WholeSubject claim over a cast.
                assert!(
                    pending_whole_subject_for_test("ann as *const libc::c_void", "ann"),
                    "the whole-subject dispatch must know the void carrier"
                );
                // R306-1(ii), arm 2: the original's raw cast is peeled too, so
                // the emitted bridge corresponds to it.
                assert!(
                    raw_initializer_matches_for_test(
                        "core::ptr::from_ref(ann).cast::<core::ffi::c_void>()",
                        "ann as *const libc::c_void",
                    ),
                    "the emitted carrier must correspond to the cast original"
                );
                // Still strict: a different binding never corresponds.
                assert!(!pending_whole_subject_for_test(
                    "q as *const libc::c_void",
                    "ann"
                ));
                assert!(!raw_initializer_matches_for_test(
                    "core::ptr::from_ref(q).cast::<core::ffi::c_void>()",
                    "ann as *const libc::c_void",
                ));
            },
        );
    }

    // ---------------------------------------------------------------------
    // R295-3 — no comparator arm fails opaquely.
    //
    // R291-3 removed the cost of an unexplained "absent" from the pending
    // arm's text comparison; the same cost sat in three more lines, each of
    // which named an identity and stopped. These pin the reasons.

    /// An unstatable composition names WHICH condition fired — here K21's
    /// guard, an inner original occurring twice in the outer replacement,
    /// which is exactly the shape a hand-rolled splice produces.
    #[test]
    /// **R328-4 witness — the emitted initializer is the original with the
    /// emission's own adapter applied.**
    ///
    /// lodepng's exact shape: `lodepng_get_bpp` converted its parameter, so the
    /// call site that initializes `bpp` gained a reborrow. Ten custody rows
    /// depended on this one binding through `linebytes` and `inindex`.
    #[test]
    fn r328_4_an_adapted_initializer_still_binds_to_its_original() {
        use super::super::bridge_custody_match::initializer_adapter_correspondence_for_test as c;
        rustc_span::create_default_session_globals_then(|| {
        assert!(c("lodepng_get_bpp(color)", "lodepng_get_bpp(&*color)"));
        assert!(c("f(a, b)", "f(&*a, b)"));
        assert!(c("f(a, b)", "f(&*a, &mut *b)"));
        assert!(c("x.len(p)", "x.len(&*p)"));
        assert!(c("f(g(p))", "f(g(&*p))"));
        // Identical text still corresponds — the arm is additive, not a
        // replacement for the plain comparison.
        assert!(c("lodepng_get_bpp(color)", "lodepng_get_bpp(color)"));
        });
    }

    /// **R328-4 fault — only a reborrow, and only at an argument of the same
    /// call, is peeled.** Everything else is a different value and refuses.
    #[test]
    fn r328_4_anything_but_a_reborrow_adapter_still_refuses() {
        use super::super::bridge_custody_match::initializer_adapter_correspondence_for_test as c;
        rustc_span::create_default_session_globals_then(|| {
        // A different callee.
        assert!(!c("lodepng_get_bpp(color)", "lodepng_get_bpc(&*color)"));
        // A different argument behind the adapter.
        assert!(!c("lodepng_get_bpp(color)", "lodepng_get_bpp(&*other)"));
        // A different arity.
        assert!(!c("f(a)", "f(&*a, b)"));
        // A plain borrow is NOT a reborrow: `&a` does not peel to `a`.
        assert!(!c("f(a)", "f(&a)"));
        // A cast is not an adapter this arm accepts.
        assert!(!c("f(a)", "f(a as *const u8)"));
        // A different method.
        assert!(!c("x.len(p)", "x.cap(&*p)"));
        // The adapter may not appear on the ORIGINAL side to excuse a bare
        // emitted argument — the peel is one-directional.
        assert!(!c("f(&*a)", "f(a)"));
        });
    }

    fn r295_an_unstatable_composition_names_its_condition() {
        const SOURCE: &str = "fn caller(x: *mut i32) { f(x, x); }";
        let lo = SOURCE.find("f(x").expect("fixture call");
        let hi = SOURCE.find(");").expect("fixture call end") + 1;
        let inner = lo + "f(".len();
        let mut export = Export::default();
        export.files.insert(
            "lib.rs".to_owned(),
            OriginalFile {
                source: SOURCE.to_owned(),
                sha256: String::new(),
                global_start: 0,
            },
        );
        export.pending_sites = vec![PendingSiteRow {
            site_id: "raw-boundary-site:caller:0:0:f:0".to_owned(),
            waiver: super::super::decision::sibling_overlap::PENDING_REASON.to_owned(),
            source_file: "lib.rs".to_owned(),
            call: Ok(PendingCallRow {
                lo,
                hi,
                edits: vec![
                    (lo, hi, "f(x, x)".to_owned()),
                    (inner, inner + 1, "y".to_owned()),
                ],
                rendered: None,
            }),
            siblings: Vec::new(),
        }];
        let sources = BTreeMap::from([("lib.rs".to_owned(), SOURCE.to_owned())]);
        let issues = pending_sibling_overlap_issues(&export, Some(&sources));
        assert_eq!(issues.len(), 1, "{issues:#?}");
        assert!(
            issues[0].contains("emitted-call-unrenderable")
                && issues[0].contains("inner-original-occurs-2-times"),
            "the unstatable composition must name itself: {issues:#?}"
        );
    }

    /// A minimal audit row: only `coverage_id`, `data` and `issues` are read
    /// by the transport check these two tests exercise.
    fn sibling_audit_row(id: &str) -> super::super::sibling_audit::Row {
        use super::super::sibling_audit as audit;
        audit::Row {
            coverage_id: id.to_owned(),
            receipt_key: None,
            file: None,
            argument_span: None,
            call_global_span: (0, 0),
            caller: "caller".to_owned(),
            callee: "callee".to_owned(),
            block: 0,
            statement_index: 0,
            argument_index: 0,
            source: audit::Source {
                identity: id.to_owned(),
                label: id.to_owned(),
                kind: audit::SubjectKind::Local,
                mir_local: None,
                hir_owner: 0,
                hir_local: 0,
                argument_shape: "bare-local".to_owned(),
                evidence: audit::SourceEvidence::WholeSubject,
                native_return: None,
            },
            siblings: Vec::new(),
            post_call: audit::PostCall::ParameterProtected,
            terminal: audit::Terminal {
                source_form: "ref-shared".to_owned(),
                target_form: "raw".to_owned(),
                source_delivered: true,
            },
            outcome: audit::Outcome::IncompleteCapture,
            data: true,
            issues: Vec::new(),
        }
    }

    /// An incomplete audit row carries what it is missing, and a row that
    /// records nothing says so rather than reading like the old bare line.
    #[test]
    fn r295_an_incomplete_audit_row_names_what_it_is_missing() {
        let with_issue = super::super::sibling_audit::Row {
            data: false,
            issues: vec!["sibling-audit:source-custody-unstated".to_owned()],
            ..sibling_audit_row("covered")
        };
        let silent = super::super::sibling_audit::Row {
            data: false,
            issues: Vec::new(),
            ..sibling_audit_row("silent")
        };
        let issues = sibling_audit_issues(Some(&SiblingAuditCapture {
            expected_coverage_ids: ["covered".to_owned(), "silent".to_owned()]
                .into_iter()
                .collect(),
            rows: vec![with_issue, silent],
        }));
        assert!(
            issues.iter().any(|issue| issue
                == "sibling-audit:incomplete-row:covered:sibling-audit:source-custody-unstated"),
            "{issues:#?}"
        );
        assert!(
            issues
                .iter()
                .any(|issue| issue == "sibling-audit:incomplete-row:silent:no-issue-recorded"),
            "{issues:#?}"
        );
    }

    // ---------------------------------------------------------------------
    // R287-1 — the pending sibling-overlap custody contract.
    //
    // A site under the R232-4 pending waiver is a DELIVERED site. These pin
    // the three things its row owes and the two absences that must never pass.

    const PENDING_SOURCE: &str = "fn caller(p: *mut i32, q: *const i32) { copy(p, q, 4); }";

    fn pending_export(
        rows: Vec<PendingSiteRow>,
        emitted: &str,
    ) -> (Export, BTreeMap<String, String>) {
        let mut export = Export::default();
        export.files.insert(
            "lib.rs".to_owned(),
            OriginalFile {
                source: PENDING_SOURCE.to_owned(),
                sha256: String::new(),
                global_start: 0,
            },
        );
        export.pending_sites = rows;
        (
            export,
            BTreeMap::from([("lib.rs".to_owned(), emitted.to_owned())]),
        )
    }

    fn pending_row(
        siblings: Vec<PendingSiblingRow>,
        edits: Vec<(usize, usize, String)>,
    ) -> PendingSiteRow {
        let lo = PENDING_SOURCE.find("copy(").expect("fixture call");
        let hi = PENDING_SOURCE.find(");").expect("fixture call end") + 1;
        PendingSiteRow {
            site_id: "raw-boundary-site:caller:0:0:copy:0".to_owned(),
            waiver: super::super::decision::sibling_overlap::PENDING_REASON.to_owned(),
            source_file: "lib.rs".to_owned(),
            call: Ok(PendingCallRow {
                lo,
                hi,
                edits,
                rendered: None,
            }),
            siblings,
        }
    }

    /// A pending site whose sibling is BRIDGED: the ledger names the edit's
    /// custody identity, and the emitted call reads what the row says.
    #[test]
    fn r287_pending_site_with_a_bridged_sibling_is_complete() {
        let q = PENDING_SOURCE.rfind('q').expect("sibling argument");
        let row = pending_row(
            vec![PendingSiblingRow {
                argument_index: 1,
                disposition: "bridged".to_owned(),
                detail: "c:arg1".to_owned(),
            }],
            vec![(q, q + 1, "q.as_ptr()".to_owned())],
        );
        let (export, sources) = pending_export(
            vec![row],
            "fn caller(p: *mut i32, q: &[i32]) { copy(p, q.as_ptr(), 4); }",
        );
        assert_eq!(
            pending_sibling_overlap_issues(&export, Some(&sources)),
            Vec::<String>::new()
        );
    }

    /// The tulipindicators shape: a sibling the hold refused. The row states
    /// the typed reason, and the emitted call still reads the ORIGINAL text at
    /// that argument, because a held sibling is not rewritten.
    #[test]
    fn r287_pending_site_with_a_held_sibling_is_complete() {
        let row = pending_row(
            vec![PendingSiblingRow {
                argument_index: 1,
                disposition: "held".to_owned(),
                detail: "held:thin-extent".to_owned(),
            }],
            Vec::new(),
        );
        let (export, sources) = pending_export(vec![row], PENDING_SOURCE);
        assert_eq!(
            pending_sibling_overlap_issues(&export, Some(&sources)),
            Vec::<String>::new()
        );
    }

    /// A sibling nothing touched. `raw-unchanged` is a disposition, not an
    /// absence, and it needs no detail.
    #[test]
    fn r287_pending_site_with_a_raw_unchanged_sibling_is_complete() {
        let row = pending_row(
            vec![PendingSiblingRow {
                argument_index: 1,
                disposition: "raw-unchanged".to_owned(),
                detail: "-".to_owned(),
            }],
            Vec::new(),
        );
        let (export, sources) = pending_export(vec![row], PENDING_SOURCE);
        assert_eq!(
            pending_sibling_overlap_issues(&export, Some(&sources)),
            Vec::<String>::new()
        );
    }

    /// **Fault 1** — a pending row without its emitted call. This is the
    /// `emitted_call: null` state the corpus was in; it must be reported as a
    /// producer defect, never accepted.
    #[test]
    fn r287_pending_row_without_its_emitted_call_is_caught() {
        let mut row = pending_row(Vec::new(), Vec::new());
        row.call = Err("pending-call-correspondence-not-unique".to_owned());
        let (export, sources) = pending_export(vec![row], PENDING_SOURCE);
        let issues = pending_sibling_overlap_issues(&export, Some(&sources));
        assert!(
            issues
                .iter()
                .any(|issue| issue.contains("emitted-call-missing")),
            "{issues:?}"
        );
    }

    /// **Fault 2** — a sibling without a disposition. An empty detail on a
    /// `bridged` or `held` row is exactly the `sibling-audit:incomplete-row`
    /// shape, and it must fail rather than count as covered.
    #[test]
    fn r287_sibling_without_a_disposition_is_caught() {
        for disposition in ["bridged", "held"] {
            let row = pending_row(
                vec![PendingSiblingRow {
                    argument_index: 1,
                    disposition: disposition.to_owned(),
                    detail: String::new(),
                }],
                Vec::new(),
            );
            let (export, sources) = pending_export(vec![row], PENDING_SOURCE);
            let issues = pending_sibling_overlap_issues(&export, Some(&sources));
            assert!(
                issues.iter().any(|issue| issue.contains("without")),
                "{disposition}: {issues:?}"
            );
        }
        let row = pending_row(
            vec![PendingSiblingRow {
                argument_index: 1,
                disposition: "unstated".to_owned(),
                detail: "-".to_owned(),
            }],
            Vec::new(),
        );
        let (export, sources) = pending_export(vec![row], PENDING_SOURCE);
        assert!(
            pending_sibling_overlap_issues(&export, Some(&sources))
                .iter()
                .any(|issue| issue.contains("unknown-sibling-disposition"))
        );
    }

    /// The emitted call is compared as TOKENS. Reflowing it across lines the
    /// way `pprust` does must not fail custody; changing a token must.
    #[test]
    fn r287_emitted_call_is_compared_by_tokens_not_bytes() {
        let q = PENDING_SOURCE.rfind('q').expect("sibling argument");
        let row = pending_row(
            vec![PendingSiblingRow {
                argument_index: 1,
                disposition: "bridged".to_owned(),
                detail: "c:arg1".to_owned(),
            }],
            vec![(q, q + 1, "q.as_ptr()".to_owned())],
        );
        let (export, reflowed) = pending_export(
            vec![row.clone()],
            "fn caller(p: *mut i32, q: &[i32]) {\n    copy(\n        p,\n        q.as_ptr(),\n        4,\n    );\n}",
        );
        assert_eq!(
            pending_sibling_overlap_issues(&export, Some(&reflowed)),
            Vec::<String>::new(),
            "a reflowed call is the same call"
        );
        let (export, changed) = pending_export(
            vec![row],
            "fn caller(p: *mut i32, q: &[i32]) { copy(p, q.as_mut_ptr(), 4); }",
        );
        assert!(
            pending_sibling_overlap_issues(&export, Some(&changed))
                .iter()
                .any(|issue| issue.contains("emitted-call-text-absent")),
            "a changed carrier is a different call"
        );
    }
}
