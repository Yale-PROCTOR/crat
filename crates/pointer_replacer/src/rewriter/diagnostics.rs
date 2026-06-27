use rustc_hash::FxHashMap;
use rustc_hir::{HirId, Node};
use rustc_middle::{
    mir::Local,
    ty::{self, TyCtxt},
};
use rustc_span::{FileNameDisplayPreference, def_id::LocalDefId};

use super::decision::PtrKind;

const ENV_VAR: &str = "CRAT_POINTER_DECISION_DIAGNOSTICS";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticsMode {
    Off,
    Summary,
    Raw,
    Full,
}

impl DiagnosticsMode {
    pub fn from_env_value(value: Option<&str>) -> Self {
        let Some(value) = value else {
            return Self::Off;
        };
        if value.is_empty() || value == "0" || value.eq_ignore_ascii_case("false") {
            return Self::Off;
        }
        match value {
            "summary" => Self::Summary,
            "full" => Self::Full,
            "raw" => Self::Raw,
            _ => Self::Raw,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DecisionSubject {
    Param {
        did: LocalDefId,
        index: usize,
        hir_id: HirId,
        local: Local,
    },
    Return {
        did: LocalDefId,
    },
    Local {
        did: LocalDefId,
        hir_id: HirId,
        local: Local,
    },
    Field {
        struct_did: LocalDefId,
        field_index: usize,
    },
}

impl DecisionSubject {
    fn kind(self) -> &'static str {
        match self {
            Self::Param { .. } => "param",
            Self::Return { .. } => "return",
            Self::Local { .. } => "local",
            Self::Field { .. } => "field",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub enum DecisionStage {
    Initial,
    Signature,
    LocalCollection,
    ReturnInference,
    LifetimePlan,
    BorrowAnalysis,
    OwnershipAnalysis,
    FieldDecision,
    Downgrade,
    FieldDemotion,
    AbiPreservation,
    AstRewriteFallback,
    Final,
}

impl DecisionStage {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Initial => "initial",
            Self::Signature => "signature",
            Self::LocalCollection => "local_collection",
            Self::ReturnInference => "return_inference",
            Self::LifetimePlan => "lifetime_plan",
            Self::BorrowAnalysis => "borrow_analysis",
            Self::OwnershipAnalysis => "ownership_analysis",
            Self::FieldDecision => "field_decision",
            Self::Downgrade => "downgrade",
            Self::FieldDemotion => "field_demotion",
            Self::AbiPreservation => "abi_preservation",
            Self::AstRewriteFallback => "ast_rewrite_fallback",
            Self::Final => "final",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DecisionReason {
    CVoidOrFilePointee,
    OpaqueOrUnsizedPointee,
    MutableAliasCluster,
    OwningArrayOutputParam,
    OwningArrayLocalStruct,
    OwningArrayBoxedSlice,
    OwningScalarOutputParam,
    OwningScalarNestedPointer,
    OwningScalarBox,
    ArrayBorrowPromotedShared,
    ArrayBorrowPromotedMut,
    ArrayNeedsCursor,
    BorrowPromotedShared,
    BorrowPromotedMut,
    RawPtrNotBorrowPromoted,
    PreserveOriginalConstness,
    ProvenNonNull,
    FnPtrGroupDecision,
    ReturnedOutputLocal,
    ReturnDirectCandidate,
    ReturnFromLocalBoxCandidate,
    ReturnDecisionMerge,
    ReturnBorrowLifetimePlan,
    ReturnNullable,
    ArrayFieldPointerAlias,
    PointerFieldAlias,
    CursorFieldOffsetAlias,
    NonOutermostOwningLocal,
    UnsupportedAllocatorRoot,
    LocalStructCallConflict,
    LocalStructCallBindingConflict,
    LocalStructFieldBorrowConflict,
    LocalStructReborrowAssignment,
    LocalStructFieldMutPtr,
    LocalStructStaticProjection,
    LocalStructForeignMutCall,
    UnsupportedBoxInput,
    UnsupportedBoxOutput,
    FreedBorrowOutput,
    FreedBorrowOutputTiedInput,
    RawCastCallInput,
    CursorInputFromUnanchoredRawCaller,
    CursorFromUnanchoredRawSource,
    OwnedFieldFreeRequiresMutableInput,
    RawCallResult,
    RawLocalAssignment,
    RawAggregateContext,
    PointerOutputStorage,
    UnsupportedEnumPayload,
    UnsupportedBoxTarget,
    UnsupportedBoxUsage,
    UnsupportedBoxUsageByteViewAlias,
    UnsupportedBoxUsageLocalCalleeNonBorrowOnly,
    UnsupportedBoxUsageFreeLikeWrapper,
    DemotedFieldSource,
    DemotedFieldSourceCalleeOutput,
    CursorFromRawFieldSource,
    AstRewriteForcedRawCalleeOutput,
    AstRewriteUnsupportedBoxRhs,
    AstRewriteUnsupportedBoxAssignment,
    AstRewriteUnsupportedScalarBoxAllocator,
    AstRewriteRawRhsLocal,
    ActiveBorrowOverlap,
    LocalAssignmentWhileBorrowed,
    ConflictingReborrow,
    MutableFieldCopy,
    RawPointeeFieldMove,
    RawFieldPointerProjection,
    RawStorageAllocator,
    RawStoragePointer,
    RawBindingFromField,
    RawLocalCallArg,
    RawUnknownCallArg,
    SelfReferentialFieldStorage,
    BorrowFieldPromotedMutable,
    BorrowFieldPromotedShared,
    BorrowFieldArrayLike,
    BorrowFieldNeedsCursor,
    BorrowFieldShapeUnnamedFields,
    BorrowFieldShapePreserveCopy,
    BorrowFieldShapeByValueOutput,
    BorrowFieldShapePrefixCompatibility,
    BorrowFieldConflictDemotion,
    NonRawFieldType,
    NonScalarPointee,
    ArrayLikeOwningField,
    UnsupportedStructLiteralRhs,
    UnsupportedAssignmentRhs,
    UnsupportedCallRhs,
    UnsupportedRawLocalSource,
    AllocatorSizeMismatch,
    ReallocOrBufferPattern,
    CStringOrStrFunctionPattern,
    OwnershipFieldSelectedOptBox,
    OwnershipFieldNotExactlyOwning,
    CExposedAbiField,
    CExposedThinAbiField,
    CExposedCursorAbiField,
    FinalDecision,
}

impl DecisionReason {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::CVoidOrFilePointee => "c_void_or_file_pointee",
            Self::OpaqueOrUnsizedPointee => "opaque_or_unsized_pointee",
            Self::MutableAliasCluster => "mutable_alias_cluster",
            Self::OwningArrayOutputParam => "owning_array_output_param",
            Self::OwningArrayLocalStruct => "owning_array_local_struct",
            Self::OwningArrayBoxedSlice => "owning_array_boxed_slice",
            Self::OwningScalarOutputParam => "owning_scalar_output_param",
            Self::OwningScalarNestedPointer => "owning_scalar_nested_pointer",
            Self::OwningScalarBox => "owning_scalar_box",
            Self::ArrayBorrowPromotedShared => "array_borrow_promoted_shared",
            Self::ArrayBorrowPromotedMut => "array_borrow_promoted_mut",
            Self::ArrayNeedsCursor => "array_needs_cursor",
            Self::BorrowPromotedShared => "borrow_promoted_shared",
            Self::BorrowPromotedMut => "borrow_promoted_mut",
            Self::RawPtrNotBorrowPromoted => "raw_ptr_not_borrow_promoted",
            Self::PreserveOriginalConstness => "preserve_original_constness",
            Self::ProvenNonNull => "proven_non_null",
            Self::FnPtrGroupDecision => "fn_ptr_group_decision",
            Self::ReturnedOutputLocal => "returned_output_local",
            Self::ReturnDirectCandidate => "return_direct_candidate",
            Self::ReturnFromLocalBoxCandidate => "return_from_local_box_candidate",
            Self::ReturnDecisionMerge => "return_decision_merge",
            Self::ReturnBorrowLifetimePlan => "return_borrow_lifetime_plan",
            Self::ReturnNullable => "return_nullable",
            Self::ArrayFieldPointerAlias => "array_field_pointer_alias",
            Self::PointerFieldAlias => "pointer_field_alias",
            Self::CursorFieldOffsetAlias => "cursor_field_offset_alias",
            Self::NonOutermostOwningLocal => "non_outermost_owning_local",
            Self::UnsupportedAllocatorRoot => "unsupported_allocator_root",
            Self::LocalStructCallConflict => "local_struct_call_conflict",
            Self::LocalStructCallBindingConflict => "local_struct_call_binding_conflict",
            Self::LocalStructFieldBorrowConflict => "local_struct_field_borrow_conflict",
            Self::LocalStructReborrowAssignment => "local_struct_reborrow_assignment",
            Self::LocalStructFieldMutPtr => "local_struct_field_mut_ptr",
            Self::LocalStructStaticProjection => "local_struct_static_projection",
            Self::LocalStructForeignMutCall => "local_struct_foreign_mut_call",
            Self::UnsupportedBoxInput => "unsupported_box_input",
            Self::UnsupportedBoxOutput => "unsupported_box_output",
            Self::FreedBorrowOutput => "freed_borrow_output",
            Self::FreedBorrowOutputTiedInput => "freed_borrow_output_tied_input",
            Self::RawCastCallInput => "raw_cast_call_input",
            Self::CursorInputFromUnanchoredRawCaller => "cursor_input_from_unanchored_raw_caller",
            Self::CursorFromUnanchoredRawSource => "cursor_from_unanchored_raw_source",
            Self::OwnedFieldFreeRequiresMutableInput => "owned_field_free_requires_mutable_input",
            Self::RawCallResult => "raw_call_result",
            Self::RawLocalAssignment => "raw_local_assignment",
            Self::RawAggregateContext => "raw_aggregate_context",
            Self::PointerOutputStorage => "pointer_output_storage",
            Self::UnsupportedEnumPayload => "unsupported_enum_payload",
            Self::UnsupportedBoxTarget => "unsupported_box_target",
            Self::UnsupportedBoxUsage => "unsupported_box_usage",
            Self::UnsupportedBoxUsageByteViewAlias => "unsupported_box_usage_byte_view_alias",
            Self::UnsupportedBoxUsageLocalCalleeNonBorrowOnly => {
                "unsupported_box_usage_local_callee_non_borrow_only"
            }
            Self::UnsupportedBoxUsageFreeLikeWrapper => "unsupported_box_usage_free_like_wrapper",
            Self::DemotedFieldSource => "demoted_field_source",
            Self::DemotedFieldSourceCalleeOutput => "demoted_field_source_callee_output",
            Self::CursorFromRawFieldSource => "cursor_from_raw_field_source",
            Self::AstRewriteForcedRawCalleeOutput => "ast_rewrite_forced_raw_callee_output",
            Self::AstRewriteUnsupportedBoxRhs => "ast_rewrite_unsupported_box_rhs",
            Self::AstRewriteUnsupportedBoxAssignment => "ast_rewrite_unsupported_box_assignment",
            Self::AstRewriteUnsupportedScalarBoxAllocator => {
                "ast_rewrite_unsupported_scalar_box_allocator"
            }
            Self::AstRewriteRawRhsLocal => "ast_rewrite_raw_rhs_local",
            Self::ActiveBorrowOverlap => "active_borrow_overlap",
            Self::LocalAssignmentWhileBorrowed => "local_assignment_while_borrowed",
            Self::ConflictingReborrow => "conflicting_reborrow",
            Self::MutableFieldCopy => "mutable_field_copy",
            Self::RawPointeeFieldMove => "raw_pointee_field_move",
            Self::RawFieldPointerProjection => "raw_field_pointer_projection",
            Self::RawStorageAllocator => "raw_storage_allocator",
            Self::RawStoragePointer => "raw_storage_pointer",
            Self::RawBindingFromField => "raw_binding_from_field",
            Self::RawLocalCallArg => "raw_local_call_arg",
            Self::RawUnknownCallArg => "raw_unknown_call_arg",
            Self::SelfReferentialFieldStorage => "self_referential_field_storage",
            Self::BorrowFieldPromotedMutable => "borrow_field_promoted_mutable",
            Self::BorrowFieldPromotedShared => "borrow_field_promoted_shared",
            Self::BorrowFieldArrayLike => "borrow_field_array_like",
            Self::BorrowFieldNeedsCursor => "borrow_field_needs_cursor",
            Self::BorrowFieldShapeUnnamedFields => "borrow_field_shape_unnamed_fields",
            Self::BorrowFieldShapePreserveCopy => "borrow_field_shape_preserve_copy",
            Self::BorrowFieldShapeByValueOutput => "borrow_field_shape_by_value_output",
            Self::BorrowFieldShapePrefixCompatibility => "borrow_field_shape_prefix_compatibility",
            Self::BorrowFieldConflictDemotion => "borrow_field_conflict_demotion",
            Self::NonRawFieldType => "non_raw_field_type",
            Self::NonScalarPointee => "non_scalar_pointee",
            Self::ArrayLikeOwningField => "array_like_owning_field",
            Self::UnsupportedStructLiteralRhs => "unsupported_struct_literal_rhs",
            Self::UnsupportedAssignmentRhs => "unsupported_assignment_rhs",
            Self::UnsupportedCallRhs => "unsupported_call_rhs",
            Self::UnsupportedRawLocalSource => "unsupported_raw_local_source",
            Self::AllocatorSizeMismatch => "allocator_size_mismatch",
            Self::ReallocOrBufferPattern => "realloc_or_buffer_pattern",
            Self::CStringOrStrFunctionPattern => "cstring_or_str_function_pattern",
            Self::OwnershipFieldSelectedOptBox => "ownership_field_selected_opt_box",
            Self::OwnershipFieldNotExactlyOwning => "ownership_field_not_exactly_owning",
            Self::CExposedAbiField => "c_exposed_abi_field",
            Self::CExposedThinAbiField => "c_exposed_thin_abi_field",
            Self::CExposedCursorAbiField => "c_exposed_cursor_abi_field",
            Self::FinalDecision => "final_decision",
        }
    }
}

#[derive(Clone, Debug)]
pub struct DecisionEvent {
    pub subject: DecisionSubject,
    pub stage: DecisionStage,
    pub before: Option<PtrKind>,
    pub after: Option<PtrKind>,
    pub reason: DecisionReason,
    pub detail: Option<String>,
}

#[derive(Clone, Debug)]
pub struct DecisionDiagnostics {
    mode: DiagnosticsMode,
    events: Vec<DecisionEvent>,
}

impl DecisionDiagnostics {
    #[cfg(test)]
    pub fn disabled() -> Self {
        Self {
            mode: DiagnosticsMode::Off,
            events: Vec::new(),
        }
    }

    #[cfg(test)]
    pub fn for_test(mode: DiagnosticsMode) -> Self {
        Self {
            mode,
            events: Vec::new(),
        }
    }

    pub fn from_env() -> Self {
        let mode = std::env::var(ENV_VAR).ok();
        Self {
            mode: DiagnosticsMode::from_env_value(mode.as_deref()),
            events: Vec::new(),
        }
    }

    pub fn is_enabled(&self) -> bool {
        !matches!(self.mode, DiagnosticsMode::Off)
    }

    pub fn events(&self) -> &[DecisionEvent] {
        &self.events
    }

    pub fn record(
        &mut self,
        subject: DecisionSubject,
        stage: DecisionStage,
        before: Option<PtrKind>,
        after: Option<PtrKind>,
        reason: DecisionReason,
        detail: Option<String>,
    ) {
        if !self.is_enabled() {
            return;
        }
        self.events.push(DecisionEvent {
            subject,
            stage,
            before,
            after,
            reason,
            detail,
        });
    }

    pub fn emit(&self, tcx: TyCtxt<'_>) {
        if !self.is_enabled() {
            return;
        }
        let summaries = self.summaries();
        self.emit_summary(&summaries);
        if matches!(self.mode, DiagnosticsMode::Summary) {
            return;
        }
        let mut summaries = summaries;
        summaries.sort_by_key(|summary| self.subject_sort_key(tcx, summary.subject));
        for summary in summaries {
            if matches!(self.mode, DiagnosticsMode::Raw) && !summary.is_raw_or_none() {
                continue;
            }
            eprintln!(
                "[pointer-decision] {} final={}",
                self.subject_label(tcx, summary.subject),
                format_decision(summary.final_kind),
            );
            for event in summary.events {
                let mut line = format!(
                    "[pointer-decision]   {} before={} after={} reason={}",
                    event.stage.as_str(),
                    format_decision(event.before),
                    format_decision(event.after),
                    event.reason.as_str(),
                );
                if let Some(detail) = &event.detail {
                    line.push_str(" detail=");
                    line.push_str(detail);
                }
                eprintln!("{line}");
            }
        }
    }

    fn summaries(&self) -> Vec<DecisionSummary<'_>> {
        let mut by_subject: FxHashMap<DecisionSubject, Vec<&DecisionEvent>> = FxHashMap::default();
        for event in &self.events {
            by_subject.entry(event.subject).or_default().push(event);
        }
        by_subject
            .into_iter()
            .map(|(subject, events)| {
                let final_kind = events.last().map(|event| event.after).unwrap_or(None);
                DecisionSummary {
                    subject,
                    final_kind,
                    events,
                }
            })
            .collect()
    }

    fn emit_summary(&self, summaries: &[DecisionSummary<'_>]) {
        let mut subject_counts = FxHashMap::<&'static str, usize>::default();
        let mut final_counts = FxHashMap::<&'static str, usize>::default();
        let mut raw_reason_counts = FxHashMap::<&'static str, usize>::default();
        let mut downgrade_counts = FxHashMap::<&'static str, usize>::default();
        let mut borrow_selected = 0;
        let mut borrow_demoted = 0;
        let mut ownership_selected = 0;
        let mut ownership_blocked = 0;
        let mut abi_preserved = 0;

        for summary in summaries {
            *subject_counts.entry(summary.subject.kind()).or_default() += 1;
            *final_counts
                .entry(decision_count_name(summary.final_kind))
                .or_default() += 1;
            if summary.is_raw_or_none() {
                for event in &summary.events {
                    *raw_reason_counts.entry(event.reason.as_str()).or_default() += 1;
                }
            }
            for event in &summary.events {
                if event.stage == DecisionStage::Downgrade {
                    *downgrade_counts.entry(event.reason.as_str()).or_default() += 1;
                }
                match event.reason {
                    DecisionReason::BorrowFieldPromotedMutable
                    | DecisionReason::BorrowFieldPromotedShared => borrow_selected += 1,
                    DecisionReason::BorrowFieldConflictDemotion
                    | DecisionReason::BorrowFieldShapeUnnamedFields
                    | DecisionReason::BorrowFieldShapePreserveCopy
                    | DecisionReason::BorrowFieldShapeByValueOutput => borrow_demoted += 1,
                    DecisionReason::OwnershipFieldSelectedOptBox => ownership_selected += 1,
                    DecisionReason::NonRawFieldType
                    | DecisionReason::NonScalarPointee
                    | DecisionReason::ArrayLikeOwningField
                    | DecisionReason::OpaqueOrUnsizedPointee
                    | DecisionReason::UnsupportedStructLiteralRhs
                    | DecisionReason::UnsupportedAssignmentRhs
                    | DecisionReason::UnsupportedCallRhs
                    | DecisionReason::UnsupportedRawLocalSource
                    | DecisionReason::AllocatorSizeMismatch
                    | DecisionReason::ReallocOrBufferPattern
                    | DecisionReason::CStringOrStrFunctionPattern => ownership_blocked += 1,
                    DecisionReason::CExposedAbiField
                    | DecisionReason::CExposedThinAbiField
                    | DecisionReason::CExposedCursorAbiField => abi_preserved += 1,
                    _ => {}
                }
            }
        }

        eprintln!(
            "[pointer-decision-summary] subjects params={} returns={} locals={} fields={}",
            subject_counts.get("param").copied().unwrap_or_default(),
            subject_counts.get("return").copied().unwrap_or_default(),
            subject_counts.get("local").copied().unwrap_or_default(),
            subject_counts.get("field").copied().unwrap_or_default(),
        );
        for name in [
            "Ref",
            "OptRef",
            "Box",
            "OptBox",
            "Raw",
            "BoxedSlice",
            "OptBoxedSlice",
            "Slice",
            "SliceCursor",
            "None",
        ] {
            let count = final_counts.get(name).copied().unwrap_or_default();
            if count > 0 {
                eprintln!("[pointer-decision-summary] final {name}={count}");
            }
        }
        for (reason, count) in sorted_counts(raw_reason_counts) {
            eprintln!("[pointer-decision-summary] raw reason={reason} count={count}");
        }
        for (reason, count) in sorted_counts(downgrade_counts) {
            eprintln!("[pointer-decision-summary] downgrade reason={reason} count={count}");
        }
        eprintln!(
            "[pointer-decision-summary] fields borrow_selected={borrow_selected} borrow_demoted={borrow_demoted} ownership_selected={ownership_selected} ownership_blocked={ownership_blocked} abi_preserved_raw={abi_preserved}",
        );
    }

    fn subject_sort_key(&self, tcx: TyCtxt<'_>, subject: DecisionSubject) -> String {
        match subject {
            DecisionSubject::Param { did, index, .. } => {
                format!("0:{}:{index}", tcx.def_path_str(did))
            }
            DecisionSubject::Return { did } => format!("1:{}", tcx.def_path_str(did)),
            DecisionSubject::Local { did, hir_id, .. } => {
                format!("2:{}:{}", tcx.def_path_str(did), hir_id.local_id.index())
            }
            DecisionSubject::Field {
                struct_did,
                field_index,
            } => format!("3:{}:{field_index}", tcx.def_path_str(struct_did)),
        }
    }

    fn subject_label(&self, tcx: TyCtxt<'_>, subject: DecisionSubject) -> String {
        match subject {
            DecisionSubject::Param {
                did, index, hir_id, ..
            } => format!(
                "subject=param fn={} index={} name={} original={} span={}",
                tcx.def_path_str(did),
                index,
                hir_binding_name(tcx, hir_id).unwrap_or_else(|| "_".to_owned()),
                hir_node_ty(tcx, hir_id),
                hir_span(tcx, hir_id),
            ),
            DecisionSubject::Return { did } => format!(
                "subject=return fn={} original={}",
                tcx.def_path_str(did),
                return_ty(tcx, did),
            ),
            DecisionSubject::Local { did, hir_id, .. } => format!(
                "subject=local fn={} name={} original={} span={}",
                tcx.def_path_str(did),
                hir_binding_name(tcx, hir_id).unwrap_or_else(|| "_".to_owned()),
                hir_node_ty(tcx, hir_id),
                hir_span(tcx, hir_id),
            ),
            DecisionSubject::Field {
                struct_did,
                field_index,
            } => format!(
                "subject=field field={} original={}",
                field_label(tcx, struct_did, field_index),
                field_ty(tcx, struct_did, field_index),
            ),
        }
    }
}

struct DecisionSummary<'a> {
    subject: DecisionSubject,
    final_kind: Option<PtrKind>,
    events: Vec<&'a DecisionEvent>,
}

impl DecisionSummary<'_> {
    fn is_raw_or_none(&self) -> bool {
        matches!(self.final_kind, Some(PtrKind::Raw(_)) | None)
    }
}

fn sorted_counts(counts: FxHashMap<&'static str, usize>) -> Vec<(&'static str, usize)> {
    let mut counts = counts.into_iter().collect::<Vec<_>>();
    counts.sort_by_key(|(name, _)| *name);
    counts
}

fn format_decision(decision: Option<PtrKind>) -> String {
    decision
        .map(|kind| format!("{kind:?}"))
        .unwrap_or_else(|| "None".to_owned())
}

fn decision_count_name(decision: Option<PtrKind>) -> &'static str {
    match decision {
        Some(PtrKind::Ref(_)) => "Ref",
        Some(PtrKind::OptRef(_)) => "OptRef",
        Some(PtrKind::Box) => "Box",
        Some(PtrKind::OptBox) => "OptBox",
        Some(PtrKind::Raw(_)) => "Raw",
        Some(PtrKind::BoxedSlice) => "BoxedSlice",
        Some(PtrKind::OptBoxedSlice) => "OptBoxedSlice",
        Some(PtrKind::Slice(_)) => "Slice",
        Some(PtrKind::SliceCursor(_)) => "SliceCursor",
        None => "None",
    }
}

fn hir_binding_name(tcx: TyCtxt<'_>, hir_id: HirId) -> Option<String> {
    let Node::Pat(pat) = tcx.hir_node(hir_id) else {
        return None;
    };
    let rustc_hir::PatKind::Binding(_, _, ident, _) = pat.kind else {
        return None;
    };
    Some(ident.name.as_str().to_owned())
}

fn hir_span(tcx: TyCtxt<'_>, hir_id: HirId) -> String {
    tcx.sess
        .source_map()
        .span_to_string(tcx.hir_span(hir_id), FileNameDisplayPreference::Local)
}

fn hir_node_ty(tcx: TyCtxt<'_>, hir_id: HirId) -> String {
    format!("{}", tcx.typeck(hir_id.owner).node_type(hir_id))
}

fn return_ty(tcx: TyCtxt<'_>, did: LocalDefId) -> String {
    format!("{}", tcx.fn_sig(did).skip_binder().skip_binder().output())
}

fn field_label(tcx: TyCtxt<'_>, struct_did: LocalDefId, field_index: usize) -> String {
    let struct_name = tcx.def_path_str(struct_did);
    let field_name = tcx
        .adt_def(struct_did)
        .non_enum_variant()
        .fields
        .iter()
        .nth(field_index)
        .map(|field| field.name.as_str().to_owned())
        .unwrap_or_else(|| format!("#{field_index}"));
    format!("{struct_name}.{field_name}")
}

fn field_ty(tcx: TyCtxt<'_>, struct_did: LocalDefId, field_index: usize) -> String {
    let struct_ty = tcx.type_of(struct_did).skip_binder();
    let ty::TyKind::Adt(adt_def, args) = struct_ty.kind() else {
        return "<unknown>".to_owned();
    };
    adt_def
        .all_fields()
        .nth(field_index)
        .map(|field| format!("{}", field.ty(tcx, args)))
        .unwrap_or_else(|| "<unknown>".to_owned())
}

#[cfg(test)]
mod tests {
    use super::{DecisionDiagnostics, DiagnosticsMode};

    #[test]
    fn decision_diagnostics_env_mode_parser() {
        assert_eq!(DiagnosticsMode::from_env_value(None), DiagnosticsMode::Off);
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("")),
            DiagnosticsMode::Off
        );
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("0")),
            DiagnosticsMode::Off
        );
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("false")),
            DiagnosticsMode::Off
        );
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("FALSE")),
            DiagnosticsMode::Off
        );
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("summary")),
            DiagnosticsMode::Summary
        );
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("raw")),
            DiagnosticsMode::Raw
        );
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("full")),
            DiagnosticsMode::Full
        );
        assert_eq!(
            DiagnosticsMode::from_env_value(Some("1")),
            DiagnosticsMode::Raw
        );
    }

    #[test]
    fn disabled_diagnostics_ignore_records() {
        let diagnostics = DecisionDiagnostics::disabled();
        assert!(!diagnostics.is_enabled());
        assert!(diagnostics.events().is_empty());
    }
}
