//! Wave-3b mechanical-obligation and specialized-receipt vocabulary.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::def_id::{DefId, LocalDefId};

use super::bridge_receipt::{
    BridgeReceiptStage, BridgeReceiptState, BridgeSiteKey, RAW_BOUNDARY_T2_WAIVER_ID,
    SignatureClassId,
};
use crate::raw_boundary_census_schema as raw_schema;

pub(crate) const FALLBACK_SLICE_EXTENT: usize = 1024;
pub(crate) const SLICE_EXTENT_WAIVER_ID: &str = "slice-extent-out-of-scope@addendum-77";
pub(crate) const FALLBACK_EXTENT_RECEIPT: &str =
    "fabricated-extent:slice-extent-out-of-scope@addendum-77:FALLBACK_SLICE_EXTENT=1024";

pub(crate) fn present_unsafe_text(
    expression: impl Into<String>,
    enclosing_unsafe_fn: bool,
) -> String {
    let expression = expression.into();
    if enclosing_unsafe_fn {
        expression
    } else {
        format!("unsafe {{ {expression} }}")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum MechanicalFamily {
    UnsafeContext,
    A5ProofSiteFallback,
    SliceLocalConstruction,
    SliceUseUnsupported,
    NullInit,
    OptLocalConstruction,
    OptUseUnsupported,
    UnsupportedDeclShape,
    PairRawView,
    ReturnNotAdapted,
    FlowsIntoRawParam,
    BorrowedIntoRawParam,
    EscapesViaForeignArg,
    EscapesViaFieldStore,
    EscapesViaReturn,
    RawPointerOperation,
    PtrComparison,
    CopySourceCoupled,
    CastOfConvertingLocal,
    ArgCastFormUnbuilt,
    NestedUseEdits,
    CallSiteNotAdapted,
    ArgNullLiteral,
    PlaceReadPointee,
    DuplicatePlaceRoot,
    Composition,
    GeneratedDependency,
    MissingCArm,
    Diagnostic,
    JsonRecovery,
}

impl MechanicalFamily {
    pub(crate) const ALL: [Self; 30] = [
        Self::UnsafeContext,
        Self::A5ProofSiteFallback,
        Self::SliceLocalConstruction,
        Self::SliceUseUnsupported,
        Self::NullInit,
        Self::OptLocalConstruction,
        Self::OptUseUnsupported,
        Self::UnsupportedDeclShape,
        Self::PairRawView,
        Self::ReturnNotAdapted,
        Self::FlowsIntoRawParam,
        Self::BorrowedIntoRawParam,
        Self::EscapesViaForeignArg,
        Self::EscapesViaFieldStore,
        Self::EscapesViaReturn,
        Self::RawPointerOperation,
        Self::PtrComparison,
        Self::CopySourceCoupled,
        Self::CastOfConvertingLocal,
        Self::ArgCastFormUnbuilt,
        Self::NestedUseEdits,
        Self::CallSiteNotAdapted,
        Self::ArgNullLiteral,
        Self::PlaceReadPointee,
        Self::DuplicatePlaceRoot,
        Self::Composition,
        Self::GeneratedDependency,
        Self::MissingCArm,
        Self::Diagnostic,
        Self::JsonRecovery,
    ];

    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::UnsafeContext => "unsafe-context",
            Self::A5ProofSiteFallback => "a5-proof-site-fallback",
            Self::SliceLocalConstruction => "slice-local-construction",
            Self::SliceUseUnsupported => "slice-use-unsupported",
            Self::NullInit => "null-init",
            Self::OptLocalConstruction => "opt-local-construction",
            Self::OptUseUnsupported => "opt-use-unsupported",
            Self::UnsupportedDeclShape => "unsupported-decl-shape",
            Self::PairRawView => "pair-raw-view",
            Self::ReturnNotAdapted => "return-not-adapted",
            Self::FlowsIntoRawParam => "flows-into-raw-param",
            Self::BorrowedIntoRawParam => "borrowed-into-raw-param",
            Self::EscapesViaForeignArg => "escapes-via-foreign-arg",
            Self::EscapesViaFieldStore => "escapes-via-field-store",
            Self::EscapesViaReturn => "escapes-via-return",
            Self::RawPointerOperation => "raw-pointer-operation",
            Self::PtrComparison => "ptr-comparison",
            Self::CopySourceCoupled => "copy-source-coupled",
            Self::CastOfConvertingLocal => "cast-of-converting-local",
            Self::ArgCastFormUnbuilt => "arg-cast-form-unbuilt",
            Self::NestedUseEdits => "nested-use-edits",
            Self::CallSiteNotAdapted => "call-site-not-adapted",
            Self::ArgNullLiteral => "arg-null-literal",
            Self::PlaceReadPointee => "place-read-pointee",
            Self::DuplicatePlaceRoot => "duplicate-place-root",
            Self::Composition => "composition",
            Self::GeneratedDependency => "generated-dependency",
            Self::MissingCArm => "missing-c-arm",
            Self::Diagnostic => "diagnostic",
            Self::JsonRecovery => "json-recovery",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CanonicalCallee {
    Local(DefId),
    Foreign(String),
    Generated { owner: LocalDefId, key: String },
}

impl CanonicalCallee {
    fn receipt_key(&self) -> String {
        match self {
            Self::Local(did) => format!("def-id:{did:?}"),
            Self::Foreign(symbol) => format!("foreign:{symbol}"),
            Self::Generated { owner, key } => {
                format!("generated:{}:{key}", owner.local_def_index.as_u32())
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum MechanicalSubjectKey {
    Local {
        owner: LocalDefId,
        mir_local: u32,
        slot_depth: u32,
    },
    Field {
        owner: DefId,
        field_index: u32,
        slot_depth: u32,
    },
    Generated {
        owner: LocalDefId,
        key: String,
        slot_depth: u32,
    },
}

impl MechanicalSubjectKey {
    pub(crate) fn receipt_key(&self) -> String {
        match self {
            Self::Local {
                owner,
                mir_local,
                slot_depth,
            } => format!(
                "local:{}:{mir_local}:depth={slot_depth}",
                owner.local_def_index.as_u32()
            ),
            Self::Field {
                owner,
                field_index,
                slot_depth,
            } => format!("field:{owner:?}:{field_index}:depth={slot_depth}"),
            Self::Generated {
                owner,
                key,
                slot_depth,
            } => format!(
                "generated:{}:{key}:depth={slot_depth}",
                owner.local_def_index.as_u32()
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CanonicalLocation {
    Mir {
        basic_block: u32,
        statement_index: u32,
        terminator: bool,
    },
    Hir {
        owner: LocalDefId,
        item_local_id: u32,
    },
    Declaration {
        owner: LocalDefId,
        declaration_index: u32,
    },
    Generated {
        defining_class: SignatureClassId,
        key: String,
    },
    StaticRoot {
        owner: LocalDefId,
        root_index: u32,
    },
}

impl CanonicalLocation {
    fn receipt_key(&self) -> String {
        match self {
            Self::Mir {
                basic_block,
                statement_index,
                terminator,
            } => format!(
                "mir:bb={basic_block}:stmt={statement_index}:term={}",
                u8::from(*terminator)
            ),
            Self::Hir {
                owner,
                item_local_id,
            } => format!("hir:{}:{item_local_id}", owner.local_def_index.as_u32()),
            Self::Declaration {
                owner,
                declaration_index,
            } => format!(
                "declaration:{}:{declaration_index}",
                owner.local_def_index.as_u32()
            ),
            Self::Generated {
                defining_class,
                key,
            } => format!("generated:{}:{key}", defining_class.order_key()),
            Self::StaticRoot { owner, root_index } => format!(
                "static-root:{}:{root_index}",
                owner.local_def_index.as_u32()
            ),
        }
    }
}

/// Compiler-identity site key. Source text, byte intervals, and display paths
/// intentionally do not participate in equality or ordering.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CanonicalSiteKey {
    pub(crate) owner: LocalDefId,
    pub(crate) location: CanonicalLocation,
    pub(crate) callee: Option<CanonicalCallee>,
    pub(crate) argument_index: Option<u32>,
    pub(crate) slot_depth: u32,
}

impl CanonicalSiteKey {
    pub(crate) fn receipt_key(&self) -> String {
        format!(
            "owner={}:location={}:callee={}:arg={}:depth={}",
            self.owner.local_def_index.as_u32(),
            self.location.receipt_key(),
            self.callee
                .as_ref()
                .map_or_else(|| "-".to_owned(), CanonicalCallee::receipt_key),
            self.argument_index
                .map_or_else(|| "-".to_owned(), |index| index.to_string()),
            self.slot_depth,
        )
    }

    #[cfg(test)]
    fn for_test(index: u32) -> Self {
        Self {
            owner: rustc_hir::def_id::CRATE_DEF_ID,
            location: CanonicalLocation::Mir {
                basic_block: 0,
                statement_index: index,
                terminator: false,
            },
            callee: None,
            argument_index: None,
            slot_depth: 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct MechanicalObligationKey {
    pub(crate) owner_class: SignatureClassId,
    pub(crate) subject: MechanicalSubjectKey,
    pub(crate) site: CanonicalSiteKey,
    pub(crate) family: MechanicalFamily,
}

impl MechanicalObligationKey {
    pub(crate) fn receipt_key(&self) -> String {
        format!(
            "class={}:subject={}:site={}:family={}",
            self.owner_class.order_key(),
            self.subject.receipt_key(),
            self.site.receipt_key(),
            self.family.key(),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MechanicalStage {
    Plan,
    Terminal,
}

impl MechanicalStage {
    fn key(self) -> &'static str {
        match self {
            Self::Plan => "plan",
            Self::Terminal => "terminal",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MechanicalState {
    Planned,
    Applied,
    Dropped,
    HeldNonmechanical,
    Reclassified,
}

impl MechanicalState {
    fn key(self) -> &'static str {
        match self {
            Self::Planned => "planned",
            Self::Applied => "applied",
            Self::Dropped => "dropped",
            Self::HeldNonmechanical => "held-nonmechanical",
            Self::Reclassified => "reclassified",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MechanicalMechanism {
    UnsafeContextPresentation,
    A5RawView,
    SliceConstruction,
    SliceRawView,
    OptionPresentation,
    OptionUnwrapRequired,
    DeclarationExplicitType,
    PairRawView,
    ReturnAdapter,
    RawParameterView,
    EscapeView,
    RawSink,
    CopyPropagation,
    CastAdapter,
    NestedComposition,
    CompositionHoist,
    GeneratedDependency,
    MissingCArm,
    DiagnosticCapture,
    JsonRecovery,
    SharedRefToMutRaw,
}

impl MechanicalMechanism {
    fn for_family(family: MechanicalFamily) -> Self {
        match family {
            MechanicalFamily::UnsafeContext => Self::UnsafeContextPresentation,
            MechanicalFamily::A5ProofSiteFallback => Self::A5RawView,
            MechanicalFamily::SliceLocalConstruction => Self::SliceConstruction,
            MechanicalFamily::SliceUseUnsupported => Self::SliceRawView,
            MechanicalFamily::NullInit
            | MechanicalFamily::OptLocalConstruction
            | MechanicalFamily::OptUseUnsupported
            | MechanicalFamily::ArgNullLiteral => Self::OptionPresentation,
            MechanicalFamily::UnsupportedDeclShape => Self::DeclarationExplicitType,
            MechanicalFamily::PairRawView | MechanicalFamily::DuplicatePlaceRoot => {
                Self::PairRawView
            }
            MechanicalFamily::ReturnNotAdapted | MechanicalFamily::EscapesViaReturn => {
                Self::ReturnAdapter
            }
            MechanicalFamily::FlowsIntoRawParam
            | MechanicalFamily::BorrowedIntoRawParam
            | MechanicalFamily::CallSiteNotAdapted => Self::RawParameterView,
            MechanicalFamily::EscapesViaForeignArg | MechanicalFamily::EscapesViaFieldStore => {
                Self::EscapeView
            }
            MechanicalFamily::RawPointerOperation
            | MechanicalFamily::PtrComparison
            | MechanicalFamily::PlaceReadPointee => Self::RawSink,
            MechanicalFamily::CopySourceCoupled => Self::CopyPropagation,
            MechanicalFamily::CastOfConvertingLocal | MechanicalFamily::ArgCastFormUnbuilt => {
                Self::CastAdapter
            }
            MechanicalFamily::NestedUseEdits => Self::NestedComposition,
            MechanicalFamily::Composition => Self::CompositionHoist,
            MechanicalFamily::GeneratedDependency => Self::GeneratedDependency,
            MechanicalFamily::MissingCArm => Self::MissingCArm,
            MechanicalFamily::Diagnostic => Self::DiagnosticCapture,
            MechanicalFamily::JsonRecovery => Self::JsonRecovery,
        }
    }

    fn key(self) -> &'static str {
        match self {
            Self::UnsafeContextPresentation => "unsafe-context-presentation",
            Self::A5RawView => "a5-raw-view",
            Self::SliceConstruction => "slice-construction",
            Self::SliceRawView => "slice-raw-view",
            Self::OptionPresentation => "option-presentation",
            Self::OptionUnwrapRequired => "option-unwrap-required",
            Self::DeclarationExplicitType => "declaration-explicit-type",
            Self::PairRawView => "pair-raw-view",
            Self::ReturnAdapter => "return-adapter",
            Self::RawParameterView => "raw-parameter-view",
            Self::EscapeView => "escape-view",
            Self::RawSink => "raw-sink",
            Self::CopyPropagation => "copy-propagation",
            Self::CastAdapter => "cast-adapter",
            Self::NestedComposition => "nested-composition",
            Self::CompositionHoist => "composition-hoist",
            Self::GeneratedDependency => "generated-dependency",
            Self::MissingCArm => "missing-c-arm",
            Self::DiagnosticCapture => "diagnostic-capture",
            Self::JsonRecovery => "json-recovery",
            Self::SharedRefToMutRaw => "shared-ref-to-mut-raw",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MechanicalTerminalReason {
    ClassReverted(String),
    ProgramDegradedUnmodifiedInput,
    PreCompileDegraded(String),
    RbNegativeWriteAbsent,
    CalleeWrites,
    PositiveRetention,
    SliceUseDestinationUnbuilt(String),
    TerminalContractMissing,
    CompositionCrossingUnhoistable(String),
    Cursor,
    BoxFamily,
    FreedSlot,
    AnalysisRaw,
    ForeignItem,
    ImplItem,
    IoDomain,
    EvidenceMissing(String),
}

impl MechanicalTerminalReason {
    fn key(&self) -> String {
        match self {
            Self::ClassReverted(reason) => format!("class-reverted:{reason}"),
            Self::ProgramDegradedUnmodifiedInput => "program-degraded-unmodified-input".to_owned(),
            Self::PreCompileDegraded(reason) => format!("degraded-pre-compile:{reason}"),
            Self::RbNegativeWriteAbsent => {
                "raw-boundary-shared-to-mut:negative-write-absent".to_owned()
            }
            Self::CalleeWrites => "raw-boundary-shared-to-mut:callee-writes".to_owned(),
            Self::PositiveRetention => "positive-retention".to_owned(),
            Self::SliceUseDestinationUnbuilt(form) => {
                format!("slice-use-destination-unbuilt:{form}")
            }
            Self::TerminalContractMissing => "terminal-contract-missing".to_owned(),
            Self::CompositionCrossingUnhoistable(reason) => {
                format!("composition-crossing-unhoistable:{reason}")
            }
            Self::Cursor => "cursor".to_owned(),
            Self::BoxFamily => "box-family".to_owned(),
            Self::FreedSlot => "freed-slot".to_owned(),
            Self::AnalysisRaw => "analysis-raw".to_owned(),
            Self::ForeignItem => "foreign-item".to_owned(),
            Self::ImplItem => "impl-item".to_owned(),
            Self::IoDomain => "io-domain".to_owned(),
            Self::EvidenceMissing(evidence) => format!("evidence-missing:{evidence}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MechanicalExtent {
    None,
    Evidence(String),
    Fallback { receipt: String, waiver_id: String },
}

impl MechanicalExtent {
    fn kind(&self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Evidence(_) => "evidence",
            Self::Fallback { .. } => "fallback",
        }
    }

    fn evidence(&self) -> &str {
        match self {
            Self::None => "-",
            Self::Evidence(source) => source,
            Self::Fallback { receipt, .. } => receipt,
        }
    }

    fn waiver(&self) -> &str {
        match self {
            Self::Fallback { waiver_id, .. } => waiver_id,
            Self::None | Self::Evidence(_) => "-",
        }
    }

    pub(crate) fn is_fallback(&self) -> bool {
        matches!(self, Self::Fallback { .. })
    }

    fn validate(&self) -> Result<(), String> {
        match self {
            Self::Evidence(source) if source.is_empty() => {
                Err("empty evidence-backed slice extent".to_owned())
            }
            Self::Fallback { receipt, waiver_id }
                if receipt != FALLBACK_EXTENT_RECEIPT || waiver_id != SLICE_EXTENT_WAIVER_ID =>
            {
                Err(format!(
                    "fallback slice extent lacks typed receipt/waiver: {receipt:?}/{waiver_id:?}"
                ))
            }
            _ => Ok(()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MechanicalRetention {
    None,
    T1,
    T2 { waiver_id: String },
    PositiveRetention,
}

impl MechanicalRetention {
    fn tier(&self) -> &'static str {
        match self {
            Self::None => "none",
            Self::T1 => "T1",
            Self::T2 { .. } => "T2",
            Self::PositiveRetention => "positive-retention",
        }
    }

    fn waiver(&self) -> &str {
        match self {
            Self::T2 { waiver_id } => waiver_id,
            _ => "-",
        }
    }

    fn validate(&self) -> Result<(), String> {
        if let Self::T2 { waiver_id } = self
            && waiver_id != RAW_BOUNDARY_T2_WAIVER_ID
        {
            return Err(format!("T2 obligation has wrong waiver {waiver_id:?}"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NegativeWriteEvidence {
    NotApplicable,
    FosterImmutable,
    LibcReadOnly(String),
    Missing,
    Writes,
}

impl NegativeWriteEvidence {
    fn key(&self) -> String {
        match self {
            Self::NotApplicable => "not-applicable".to_owned(),
            Self::FosterImmutable => "foster-immutable".to_owned(),
            Self::LibcReadOnly(contract) => format!("libc-read-only:{contract}"),
            Self::Missing => "negative-write-absent".to_owned(),
            Self::Writes => "callee-writes".to_owned(),
        }
    }

    fn licenses_shared_to_mut(&self) -> bool {
        matches!(self, Self::FosterImmutable | Self::LibcReadOnly(_))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TerminalContract {
    NotApplicable,
    Required { interface: String },
    Optional { interface: String },
    Missing,
}

impl TerminalContract {
    fn key(&self) -> String {
        match self {
            Self::NotApplicable => "not-applicable".to_owned(),
            Self::Required { interface } => format!("terminal-required:{interface}"),
            Self::Optional { interface } => format!("terminal-optional:{interface}"),
            Self::Missing => "terminal-contract-missing".to_owned(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum HoistSafety {
    NotApplicable,
    Place,
    SideEffectFreeUnconditional,
    Unhoistable(String),
}

impl HoistSafety {
    fn key(&self) -> String {
        match self {
            Self::NotApplicable => "not-applicable".to_owned(),
            Self::Place => "place".to_owned(),
            Self::SideEffectFreeUnconditional => "side-effect-free-unconditional".to_owned(),
            Self::Unhoistable(reason) => format!("unhoistable:{reason}"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct UnsafeContextPresentation {
    pub(crate) unsafe_fn: bool,
    pub(crate) wrapper_inserted: bool,
    pub(crate) edition: u16,
}

impl UnsafeContextPresentation {
    fn key(self) -> String {
        format!(
            "unsafe_fn={}:wrapper={}:edition={}",
            u8::from(self.unsafe_fn),
            if self.wrapper_inserted {
                "inserted"
            } else {
                "omitted"
            },
            self.edition,
        )
    }

    fn validate(self) -> Result<(), String> {
        if self.edition != 2018 {
            return Err(format!(
                "unsupported unsafe-context edition {}",
                self.edition
            ));
        }
        if self.unsafe_fn == self.wrapper_inserted {
            return Err("unsafe-context wrapper does not match enclosing safety".to_owned());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UnsafeContextReceiptEvent {
    pub(crate) site: BridgeSiteKey,
    pub(crate) enclosing: LocalDefId,
    pub(crate) presentation: UnsafeContextPresentation,
    pub(crate) terminal_class_disposition: String,
    pub(crate) stage: BridgeReceiptStage,
    pub(crate) state: BridgeReceiptState,
    pub(crate) drop_reason: Option<String>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct UnsafeContextReceiptSummary {
    pub(crate) sites: usize,
    pub(crate) inserted: usize,
    pub(crate) omitted: usize,
    pub(crate) dropped: usize,
}

pub(crate) fn reconcile_unsafe_context_events(
    events: &[UnsafeContextReceiptEvent],
) -> Result<UnsafeContextReceiptSummary, String> {
    let mut by_site = BTreeMap::<
        String,
        (
            Option<&UnsafeContextReceiptEvent>,
            Option<&UnsafeContextReceiptEvent>,
        ),
    >::new();
    for event in events {
        event.presentation.validate()?;
        let valid_stage = matches!(
            (event.stage, event.state),
            (BridgeReceiptStage::Plan, BridgeReceiptState::Planned)
                | (
                    BridgeReceiptStage::Terminal,
                    BridgeReceiptState::Applied | BridgeReceiptState::Dropped
                )
        );
        if !valid_stage {
            return Err("invalid unsafe-context stage/state".to_owned());
        }
        if (event.state == BridgeReceiptState::Dropped) != event.drop_reason.is_some() {
            return Err("unsafe-context drop reason/state mismatch".to_owned());
        }
        let slot = by_site.entry(event.site.receipt_key()).or_default();
        let target = match event.stage {
            BridgeReceiptStage::Plan => &mut slot.0,
            BridgeReceiptStage::Terminal => &mut slot.1,
        };
        if target.replace(event).is_some() {
            return Err("duplicate unsafe-context receipt stage".to_owned());
        }
    }

    let mut summary = UnsafeContextReceiptSummary {
        sites: by_site.len(),
        ..UnsafeContextReceiptSummary::default()
    };
    for (site, (plan, terminal)) in by_site {
        let (Some(plan), Some(terminal)) = (plan, terminal) else {
            return Err(format!("unsafe-context site {site} lacks plan or terminal"));
        };
        if plan.enclosing != terminal.enclosing || plan.presentation != terminal.presentation {
            return Err(format!("unsafe-context site {site} changed between stages"));
        }
        if terminal.state == BridgeReceiptState::Dropped {
            summary.dropped += 1;
        } else if terminal.presentation.wrapper_inserted {
            summary.inserted += 1;
        } else {
            summary.omitted += 1;
        }
    }
    Ok(summary)
}

pub(crate) fn render_unsafe_context_events(events: &[UnsafeContextReceiptEvent]) -> String {
    let mut rows = events
        .iter()
        .map(|event| {
            let stage = match event.stage {
                BridgeReceiptStage::Plan => "plan",
                BridgeReceiptStage::Terminal => "terminal",
            };
            let state = match event.state {
                BridgeReceiptState::Planned => "planned",
                BridgeReceiptState::Applied => "applied",
                BridgeReceiptState::Dropped => "dropped",
            };
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                event.site.receipt_key(),
                event.site.receipt_key(),
                event.enclosing.local_def_index.as_u32(),
                u8::from(event.presentation.unsafe_fn),
                if event.presentation.wrapper_inserted {
                    "inserted"
                } else {
                    "omitted"
                },
                event.presentation.edition,
                event.terminal_class_disposition,
                stage,
                state,
                event.drop_reason.as_deref().unwrap_or("-"),
            )
        })
        .collect::<Vec<_>>();
    rows.sort();
    let columns = specialized_receipt_headers()[raw_schema::UNSAFE_CONTEXT_PRESENTATION_ROWS];
    let mut out = columns.join("\t");
    out.push('\n');
    for row in rows {
        out.push_str(&row);
        out.push('\n');
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MechanicalEvidence {
    pub(crate) extent: MechanicalExtent,
    pub(crate) retention: MechanicalRetention,
    pub(crate) negative_write: NegativeWriteEvidence,
    pub(crate) terminal_contract: TerminalContract,
    pub(crate) hoist: HoistSafety,
    pub(crate) unsafe_context: Option<UnsafeContextPresentation>,
}

impl Default for MechanicalEvidence {
    fn default() -> Self {
        Self {
            extent: MechanicalExtent::None,
            retention: MechanicalRetention::None,
            negative_write: NegativeWriteEvidence::NotApplicable,
            terminal_contract: TerminalContract::NotApplicable,
            hoist: HoistSafety::NotApplicable,
            unsafe_context: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MechanicalObligationEvent {
    pub(crate) key: MechanicalObligationKey,
    pub(crate) owner_path: String,
    pub(crate) prior_reason: String,
    pub(crate) expected_form: String,
    pub(crate) found_form: String,
    pub(crate) argument_kind: String,
    pub(crate) source_shape: String,
    pub(crate) required_arms: String,
    pub(crate) mechanism: MechanicalMechanism,
    pub(crate) composition_parent: Option<String>,
    pub(crate) dependency_classes: BTreeSet<SignatureClassId>,
    pub(crate) evidence: MechanicalEvidence,
    pub(crate) stage: MechanicalStage,
    pub(crate) state: MechanicalState,
    pub(crate) terminal_reason: Option<MechanicalTerminalReason>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MechanicalObligationPlan {
    pub(crate) planned: MechanicalObligationEvent,
    pub(crate) intended_terminal_state: MechanicalState,
    pub(crate) intended_terminal_reason: Option<MechanicalTerminalReason>,
}

impl MechanicalObligationPlan {
    pub(crate) fn events(
        &self,
        owner_class_live: bool,
        runtime_reverted: bool,
    ) -> [MechanicalObligationEvent; 2] {
        let mut planned = self.planned.clone();
        planned.stage = MechanicalStage::Plan;
        planned.state = MechanicalState::Planned;
        planned.terminal_reason = None;

        let mut terminal = self.planned.clone();
        terminal.stage = MechanicalStage::Terminal;
        if self.intended_terminal_state == MechanicalState::Applied
            && (!owner_class_live || runtime_reverted)
        {
            terminal.state = MechanicalState::Dropped;
            terminal.terminal_reason = Some(MechanicalTerminalReason::ClassReverted(
                if runtime_reverted {
                    "compiler-verify".to_owned()
                } else {
                    "class-finalization".to_owned()
                },
            ));
        } else {
            terminal.state = self.intended_terminal_state;
            terminal.terminal_reason = self.intended_terminal_reason.clone();
        }
        [planned, terminal]
    }
}

impl MechanicalObligationEvent {
    #[cfg(test)]
    pub(crate) fn for_test(
        label: &str,
        family: MechanicalFamily,
        stage: MechanicalStage,
        state: MechanicalState,
    ) -> Self {
        let family_index = MechanicalFamily::ALL
            .iter()
            .position(|candidate| *candidate == family)
            .unwrap_or_default() as u32;
        let label_index = label.bytes().fold(0_u32, |value, byte| {
            value.wrapping_mul(257).wrapping_add(u32::from(byte))
        });
        let index = family_index.wrapping_mul(1_000_003) ^ label_index;
        Self {
            key: MechanicalObligationKey {
                owner_class: SignatureClassId::of(rustc_hir::def_id::CRATE_DEF_ID),
                subject: MechanicalSubjectKey::Local {
                    owner: rustc_hir::def_id::CRATE_DEF_ID,
                    mir_local: index,
                    slot_depth: 1,
                },
                site: CanonicalSiteKey::for_test(index),
                family,
            },
            owner_path: "crate::fixture".to_owned(),
            prior_reason: family.key().to_owned(),
            expected_form: "safe".to_owned(),
            found_form: "raw".to_owned(),
            argument_kind: "bare-local".to_owned(),
            source_shape: "thin".to_owned(),
            required_arms: "c".to_owned(),
            mechanism: MechanicalMechanism::for_family(family),
            composition_parent: None,
            dependency_classes: BTreeSet::new(),
            evidence: MechanicalEvidence::default(),
            stage,
            state,
            terminal_reason: matches!(
                state,
                MechanicalState::Dropped
                    | MechanicalState::HeldNonmechanical
                    | MechanicalState::Reclassified
            )
            .then(|| MechanicalTerminalReason::ClassReverted("test".to_owned())),
        }
    }

    pub(crate) fn with_evidence(mut self, evidence: MechanicalEvidence) -> Self {
        self.evidence = evidence;
        self
    }

    #[cfg(test)]
    fn with_mechanism(mut self, mechanism: MechanicalMechanism) -> Self {
        self.mechanism = mechanism;
        self
    }

    #[cfg(test)]
    fn with_terminal_reason(mut self, reason: MechanicalTerminalReason) -> Self {
        self.terminal_reason = Some(reason);
        self
    }

    fn validate(&self) -> Result<(), String> {
        match (self.stage, self.state) {
            (MechanicalStage::Plan, MechanicalState::Planned)
            | (
                MechanicalStage::Terminal,
                MechanicalState::Applied
                | MechanicalState::Dropped
                | MechanicalState::HeldNonmechanical
                | MechanicalState::Reclassified,
            ) => {}
            _ => {
                return Err(format!(
                    "invalid mechanical stage/state: {}/{}",
                    self.stage.key(),
                    self.state.key()
                ));
            }
        }
        let needs_reason = matches!(
            self.state,
            MechanicalState::Dropped
                | MechanicalState::HeldNonmechanical
                | MechanicalState::Reclassified
        );
        if needs_reason != self.terminal_reason.is_some() {
            return Err("mechanical terminal reason/state mismatch".to_owned());
        }
        self.evidence.extent.validate()?;
        self.evidence.retention.validate()?;
        if self.state == MechanicalState::Applied
            && self.evidence.retention == MechanicalRetention::PositiveRetention
        {
            return Err("positive-retention evidence cannot license an applied bridge".to_owned());
        }
        if self.state == MechanicalState::Applied
            && self.mechanism == MechanicalMechanism::SharedRefToMutRaw
            && !self.evidence.negative_write.licenses_shared_to_mut()
        {
            return Err(format!(
                "R-B shared-to-mut bridge lacks negative-write evidence: {}",
                self.evidence.negative_write.key()
            ));
        }
        if self.state == MechanicalState::Applied
            && self.mechanism == MechanicalMechanism::OptionUnwrapRequired
            && !matches!(
                &self.evidence.terminal_contract,
                TerminalContract::Required { .. }
            )
        {
            return Err(format!(
                "Option unwrap lacks terminal required contract: {}",
                self.evidence.terminal_contract.key()
            ));
        }
        if self.state == MechanicalState::Applied
            && self.mechanism == MechanicalMechanism::CompositionHoist
            && !matches!(
                &self.evidence.hoist,
                HoistSafety::Place | HoistSafety::SideEffectFreeUnconditional
            )
        {
            return Err(format!(
                "composition hoist is not licensed: {}",
                self.evidence.hoist.key()
            ));
        }
        if let Some(context) = self.evidence.unsafe_context {
            context.validate()?;
        }
        if self.state == MechanicalState::HeldNonmechanical {
            let lawful = matches!(
                self.terminal_reason.as_ref(),
                Some(
                    MechanicalTerminalReason::RbNegativeWriteAbsent
                        | MechanicalTerminalReason::CalleeWrites
                        | MechanicalTerminalReason::PositiveRetention
                        | MechanicalTerminalReason::SliceUseDestinationUnbuilt(_)
                        | MechanicalTerminalReason::TerminalContractMissing
                        | MechanicalTerminalReason::CompositionCrossingUnhoistable(_)
                        | MechanicalTerminalReason::Cursor
                        | MechanicalTerminalReason::BoxFamily
                        | MechanicalTerminalReason::FreedSlot
                        | MechanicalTerminalReason::AnalysisRaw
                        | MechanicalTerminalReason::ForeignItem
                        | MechanicalTerminalReason::ImplItem
                        | MechanicalTerminalReason::IoDomain
                        | MechanicalTerminalReason::EvidenceMissing(_)
                )
            );
            if !lawful {
                return Err("held-nonmechanical event lacks a ruled typed boundary".to_owned());
            }
        }
        Ok(())
    }

    fn stable_evidence_eq(&self, other: &Self) -> bool {
        self.owner_path == other.owner_path
            && self.prior_reason == other.prior_reason
            && self.expected_form == other.expected_form
            && self.found_form == other.found_form
            && self.argument_kind == other.argument_kind
            && self.source_shape == other.source_shape
            && self.required_arms == other.required_arms
            && self.mechanism == other.mechanism
            && self.composition_parent == other.composition_parent
            && self.dependency_classes == other.dependency_classes
            && self.evidence == other.evidence
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct MechanicalObligationSummary {
    pub(crate) obligations: usize,
    pub(crate) applied: usize,
    pub(crate) dropped: usize,
    pub(crate) held_nonmechanical: usize,
    pub(crate) reclassified: usize,
}

pub(crate) fn reconcile_mechanical_obligations(
    events: &[MechanicalObligationEvent],
) -> Result<MechanicalObligationSummary, String> {
    let mut by_obligation = BTreeMap::<
        String,
        (
            Option<&MechanicalObligationEvent>,
            Option<&MechanicalObligationEvent>,
        ),
    >::new();
    let mut site_owners = BTreeMap::<String, SignatureClassId>::new();
    for event in events {
        event.validate()?;
        let site_key = event.key.site.receipt_key();
        if let Some(previous) = site_owners.insert(site_key.clone(), event.key.owner_class)
            && previous != event.key.owner_class
        {
            return Err(format!(
                "canonical site {} is owned by classes {} and {}",
                site_key,
                previous.order_key(),
                event.key.owner_class.order_key()
            ));
        }
        let obligation_key = event.key.receipt_key();
        let slot = by_obligation.entry(obligation_key.clone()).or_default();
        let destination = match event.stage {
            MechanicalStage::Plan => &mut slot.0,
            MechanicalStage::Terminal => &mut slot.1,
        };
        if destination.replace(event).is_some() {
            return Err(format!(
                "duplicate {} event for {}",
                event.stage.key(),
                event.key.receipt_key()
            ));
        }
    }

    let mut summary = MechanicalObligationSummary {
        obligations: by_obligation.len(),
        ..MechanicalObligationSummary::default()
    };
    for (key, (plan, terminal)) in by_obligation {
        let Some(plan) = plan else {
            return Err(format!("obligation {key} has no plan"));
        };
        let Some(terminal) = terminal else {
            return Err(format!("obligation {key} has no terminal"));
        };
        if !plan.stable_evidence_eq(terminal) {
            return Err(format!("obligation {key} changed evidence between stages"));
        }
        match terminal.state {
            MechanicalState::Applied => summary.applied += 1,
            MechanicalState::Dropped => summary.dropped += 1,
            MechanicalState::HeldNonmechanical => summary.held_nonmechanical += 1,
            MechanicalState::Reclassified => summary.reclassified += 1,
            MechanicalState::Planned => unreachable!("validated terminal state"),
        }
    }
    Ok(summary)
}

pub(crate) fn mechanical_obligation_header() -> String {
    "obligation_key\towner_local_def_id\towner_path\tsubject_key\tcanonical_site_key\tfamily\tprior_reason\texpected_form\tfound_form\targument_kind\tsource_shape\trequired_arms\tmechanism\textent_kind\textent_evidence\tretention_tier\twaiver_id\tunsafe_context\tcomposition_parent\tdependency_classes\tstage\tstate\tdrop_reason\n".to_owned()
}

pub(crate) fn render_mechanical_obligations(events: &[MechanicalObligationEvent]) -> String {
    let mut rows = events
        .iter()
        .map(|event| {
            let dependencies = event
                .dependency_classes
                .iter()
                .map(|class| class.order_key().to_string())
                .collect::<Vec<_>>()
                .join(";");
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                event.key.receipt_key(),
                event.key.owner_class.order_key(),
                event.owner_path,
                event.key.subject.receipt_key(),
                event.key.site.receipt_key(),
                event.key.family.key(),
                event.prior_reason,
                event.expected_form,
                event.found_form,
                event.argument_kind,
                event.source_shape,
                event.required_arms,
                event.mechanism.key(),
                event.evidence.extent.kind(),
                event.evidence.extent.evidence(),
                event.evidence.retention.tier(),
                event.evidence.retention.waiver(),
                event.evidence.unsafe_context.map_or_else(
                    || "-".to_owned(),
                    UnsafeContextPresentation::key,
                ),
                event.composition_parent.as_deref().unwrap_or("-"),
                if dependencies.is_empty() { "-" } else { &dependencies },
                event.stage.key(),
                event.state.key(),
                event
                    .terminal_reason
                    .as_ref()
                    .map_or_else(|| "-".to_owned(), MechanicalTerminalReason::key),
            )
        })
        .collect::<Vec<_>>();
    rows.sort();
    let mut out = mechanical_obligation_header();
    for row in rows {
        out.push_str(&row);
        out.push('\n');
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SpecializedReceiptTerminal {
    pub(crate) obligation_key: MechanicalObligationKey,
    pub(crate) stage: MechanicalStage,
    pub(crate) state: MechanicalState,
    pub(crate) reason: Option<MechanicalTerminalReason>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UnsafeContextReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) site_key: CanonicalSiteKey,
    pub(crate) enclosing: LocalDefId,
    pub(crate) presentation: UnsafeContextPresentation,
    pub(crate) terminal_class_disposition: MechanicalState,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct A5ProofSiteFallbackReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) proof_site_key: CanonicalSiteKey,
    pub(crate) verdict: String,
    pub(crate) argument_shape: String,
    pub(crate) settled_form: String,
    pub(crate) raw_view_template: String,
    pub(crate) retention: MechanicalRetention,
    pub(crate) owner_class: SignatureClassId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct A5ProofSiteReceiptPlan {
    pub(crate) obligation: MechanicalObligationPlan,
    pub(crate) proof_site_key: CanonicalSiteKey,
    pub(crate) verdict: String,
    pub(crate) argument_shape: String,
    pub(crate) settled_form: String,
    pub(crate) raw_view_template: String,
    pub(crate) retention: MechanicalRetention,
    pub(crate) owner_class: SignatureClassId,
}

impl A5ProofSiteReceiptPlan {
    pub(crate) fn materialize(
        &self,
        owner_class_live: bool,
        runtime_reverted: bool,
    ) -> (
        [MechanicalObligationEvent; 2],
        [A5ProofSiteFallbackReceiptRow; 2],
    ) {
        let events = self.obligation.events(owner_class_live, runtime_reverted);
        let row = |event: &MechanicalObligationEvent| A5ProofSiteFallbackReceiptRow {
            terminal: SpecializedReceiptTerminal {
                obligation_key: event.key.clone(),
                stage: event.stage,
                state: event.state,
                reason: event.terminal_reason.clone(),
            },
            proof_site_key: self.proof_site_key.clone(),
            verdict: self.verdict.clone(),
            argument_shape: self.argument_shape.clone(),
            settled_form: self.settled_form.clone(),
            raw_view_template: self.raw_view_template.clone(),
            retention: self.retention.clone(),
            owner_class: self.owner_class,
        };
        let rows = [row(&events[0]), row(&events[1])];
        (events, rows)
    }
}

pub(crate) fn reconcile_a5_proof_site_fallback_rows(
    rows: &[A5ProofSiteFallbackReceiptRow],
    common: &[MechanicalObligationEvent],
) -> Result<usize, String> {
    let common = common
        .iter()
        .filter(|event| event.key.family == MechanicalFamily::A5ProofSiteFallback)
        .map(|event| {
            (
                format!("{}:{}", event.key.receipt_key(), event.stage.key()),
                event,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut specialized = BTreeMap::<String, &A5ProofSiteFallbackReceiptRow>::new();
    for row in rows {
        let event_key = format!(
            "{}:{}",
            row.terminal.obligation_key.receipt_key(),
            row.terminal.stage.key()
        );
        if specialized.insert(event_key.clone(), row).is_some() {
            return Err(format!("duplicate A5 specialized row {event_key}"));
        }
        let Some(event) = common.get(&event_key) else {
            return Err(format!("unowned A5 specialized row {event_key}"));
        };
        if row.proof_site_key != row.terminal.obligation_key.site
            || row.owner_class != row.terminal.obligation_key.owner_class
            || row.terminal.state != event.state
            || row.terminal.reason != event.terminal_reason
        {
            return Err(format!("A5 specialized/common drift at {event_key}"));
        }
        if row.terminal.stage == MechanicalStage::Terminal
            && row.terminal.state == MechanicalState::Applied
            && row.retention
                != (MechanicalRetention::T2 {
                    waiver_id: RAW_BOUNDARY_T2_WAIVER_ID.to_owned(),
                })
        {
            return Err(format!(
                "A5 applied row lacks exact T2 waiver at {event_key}"
            ));
        }
    }
    for key in common.keys() {
        if !specialized.contains_key(key) {
            return Err(format!("A5 common row lacks specialized row {key}"));
        }
    }
    Ok(rows
        .iter()
        .filter(|row| row.terminal.stage == MechanicalStage::Plan)
        .count())
}

pub(crate) fn render_a5_proof_site_fallback_rows(rows: &[A5ProofSiteFallbackReceiptRow]) -> String {
    let mut rendered = rows
        .iter()
        .map(|row| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                row.terminal.obligation_key.receipt_key(),
                row.proof_site_key.receipt_key(),
                row.verdict,
                row.argument_shape,
                row.settled_form,
                row.raw_view_template,
                row.retention.tier(),
                row.retention.waiver(),
                row.owner_class.order_key(),
                row.terminal.stage.key(),
                row.terminal.state.key(),
                row.terminal
                    .reason
                    .as_ref()
                    .map_or_else(|| "-".to_owned(), MechanicalTerminalReason::key),
            )
        })
        .collect::<Vec<_>>();
    rendered.sort();
    let mut out = specialized_receipt_headers()[raw_schema::A5_PROOF_SITE_FALLBACK_ROWS].join("\t");
    out.push('\n');
    for row in rendered {
        out.push_str(&row);
        out.push('\n');
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SliceConstructionReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) allocation_result: MechanicalSubjectKey,
    pub(crate) element_type: String,
    pub(crate) mutable: bool,
    pub(crate) nullable: bool,
    pub(crate) length_expression: String,
    pub(crate) length_provenance: String,
    pub(crate) extent: MechanicalExtent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SliceConstructionReceiptPlan {
    pub(crate) obligation: MechanicalObligationPlan,
    pub(crate) allocation_result: MechanicalSubjectKey,
    pub(crate) element_type: String,
    pub(crate) mutable: bool,
    pub(crate) nullable: bool,
    pub(crate) length_expression: String,
    pub(crate) length_provenance: String,
    pub(crate) extent: MechanicalExtent,
    pub(crate) owner_class: SignatureClassId,
}

impl SliceConstructionReceiptPlan {
    pub(crate) fn materialize(
        &self,
        owner_class_live: bool,
        runtime_reverted: bool,
    ) -> (
        [MechanicalObligationEvent; 2],
        [SliceConstructionReceiptRow; 2],
    ) {
        let events = self.obligation.events(owner_class_live, runtime_reverted);
        let row = |event: &MechanicalObligationEvent| SliceConstructionReceiptRow {
            terminal: SpecializedReceiptTerminal {
                obligation_key: event.key.clone(),
                stage: event.stage,
                state: event.state,
                reason: event.terminal_reason.clone(),
            },
            allocation_result: self.allocation_result.clone(),
            element_type: self.element_type.clone(),
            mutable: self.mutable,
            nullable: self.nullable,
            length_expression: self.length_expression.clone(),
            length_provenance: self.length_provenance.clone(),
            extent: self.extent.clone(),
        };
        let rows = [row(&events[0]), row(&events[1])];
        (events, rows)
    }
}

pub(crate) fn reconcile_slice_construction_rows(
    rows: &[SliceConstructionReceiptRow],
    common: &[MechanicalObligationEvent],
) -> Result<usize, String> {
    let common = common
        .iter()
        .filter(|event| event.key.family == MechanicalFamily::SliceLocalConstruction)
        .map(|event| {
            (
                format!("{}:{}", event.key.receipt_key(), event.stage.key()),
                event,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut specialized = BTreeMap::<String, &SliceConstructionReceiptRow>::new();
    for row in rows {
        let key = format!(
            "{}:{}",
            row.terminal.obligation_key.receipt_key(),
            row.terminal.stage.key()
        );
        if specialized.insert(key.clone(), row).is_some() {
            return Err(format!(
                "duplicate slice-construction specialized row {key}"
            ));
        }
        let Some(event) = common.get(&key) else {
            return Err(format!("unowned slice-construction specialized row {key}"));
        };
        if row.allocation_result != row.terminal.obligation_key.subject
            || row.terminal.state != event.state
            || row.terminal.reason != event.terminal_reason
            || row.extent != event.evidence.extent
        {
            return Err(format!(
                "slice-construction specialized/common drift at {key}"
            ));
        }
        row.extent.validate()?;
    }
    for key in common.keys() {
        if !specialized.contains_key(key) {
            return Err(format!(
                "slice-construction common row lacks specialized row {key}"
            ));
        }
    }
    Ok(rows
        .iter()
        .filter(|row| row.terminal.stage == MechanicalStage::Plan)
        .count())
}

pub(crate) fn render_slice_construction_rows(rows: &[SliceConstructionReceiptRow]) -> String {
    let mut rendered = rows
        .iter()
        .map(|row| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                row.terminal.obligation_key.receipt_key(),
                row.allocation_result.receipt_key(),
                row.element_type,
                if row.mutable { "mut" } else { "shared" },
                if row.nullable { "nullable" } else { "required" },
                row.length_expression,
                row.length_provenance,
                row.extent.evidence(),
                row.extent.kind(),
                row.extent.waiver(),
                row.terminal.stage.key(),
                row.terminal.state.key(),
                row.terminal
                    .reason
                    .as_ref()
                    .map_or_else(|| "-".to_owned(), MechanicalTerminalReason::key),
            )
        })
        .collect::<Vec<_>>();
    rendered.sort();
    let mut out =
        specialized_receipt_headers()[raw_schema::SLICE_CONSTRUCTION_RECEIPT_ROWS].join("\t");
    out.push('\n');
    for row in rendered {
        out.push_str(&row);
        out.push('\n');
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SliceUseAdapterReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) use_site: CanonicalSiteKey,
    pub(crate) source_form: String,
    pub(crate) candidate_form: String,
    pub(crate) target_form: String,
    pub(crate) access_mutability: String,
    pub(crate) adapter: String,
    pub(crate) boundary_site: String,
    pub(crate) boundary_evidence: String,
    pub(crate) retention: MechanicalRetention,
    pub(crate) terminal_class_state: MechanicalState,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SliceUseReceiptPlan {
    pub(crate) obligation: MechanicalObligationPlan,
    pub(crate) use_site: CanonicalSiteKey,
    pub(crate) source_form: String,
    pub(crate) candidate_form: String,
    /// A safe copy/reborrow already supplies this local's complete value.
    pub(crate) same_form_initializer: Option<(LocalDefId, rustc_hir::HirId)>,
    pub(crate) target_form: String,
    pub(crate) access_mutability: String,
    pub(crate) adapter: String,
    pub(crate) boundary_site: String,
    pub(crate) boundary_evidence: String,
    pub(crate) retention: MechanicalRetention,
    pub(crate) owner_class: SignatureClassId,
}

impl SliceUseReceiptPlan {
    pub(crate) fn materialize(
        &self,
        class_live: bool,
        runtime_reverted: bool,
    ) -> (
        [MechanicalObligationEvent; 2],
        [SliceUseAdapterReceiptRow; 2],
    ) {
        let events = self.obligation.events(class_live, runtime_reverted);
        let terminal_class_state = if runtime_reverted {
            MechanicalState::Dropped
        } else if class_live {
            MechanicalState::Applied
        } else {
            MechanicalState::HeldNonmechanical
        };
        let row = |event: &MechanicalObligationEvent| SliceUseAdapterReceiptRow {
            terminal: SpecializedReceiptTerminal {
                obligation_key: event.key.clone(),
                stage: event.stage,
                state: event.state,
                reason: event.terminal_reason.clone(),
            },
            use_site: self.use_site.clone(),
            source_form: self.source_form.clone(),
            candidate_form: self.candidate_form.clone(),
            target_form: self.target_form.clone(),
            access_mutability: self.access_mutability.clone(),
            adapter: self.adapter.clone(),
            boundary_site: self.boundary_site.clone(),
            boundary_evidence: self.boundary_evidence.clone(),
            retention: self.retention.clone(),
            terminal_class_state,
        };
        let rows = [row(&events[0]), row(&events[1])];
        (events, rows)
    }
}

pub(crate) fn reconcile_slice_use_rows(
    rows: &[SliceUseAdapterReceiptRow],
    events: &[MechanicalObligationEvent],
) -> Result<usize, String> {
    let mut common = BTreeMap::new();
    for event in events
        .iter()
        .filter(|event| event.key.family == MechanicalFamily::SliceUseUnsupported)
    {
        let key = format!("{}:{}", event.key.receipt_key(), event.stage.key());
        if common.insert(key.clone(), event).is_some() {
            return Err(format!("duplicate slice-use common row {key}"));
        }
    }
    let mut specialized = BTreeSet::new();
    for row in rows {
        let key = format!(
            "{}:{}",
            row.terminal.obligation_key.receipt_key(),
            row.terminal.stage.key()
        );
        if !specialized.insert(key.clone()) {
            return Err(format!("duplicate slice-use specialized row {key}"));
        }
        let event = common
            .get(&key)
            .ok_or_else(|| format!("unowned slice-use row {key}"))?;
        if row.use_site != event.key.site
            || row.source_form != event.found_form
            || (event.source_shape == "cursor"
                && (row.source_form != "raw"
                    || !matches!(row.candidate_form.as_str(), "slice-shared" | "slice-mut")))
            || (event.source_shape != "cursor" && row.source_form != row.candidate_form)
            || row.target_form != event.expected_form
            || row.retention != event.evidence.retention
            || row.terminal.state != event.state
            || row.terminal.reason != event.terminal_reason
        {
            return Err(format!("slice-use specialized/common drift at {key}"));
        }
        event.validate()?;
    }
    if common.keys().any(|key| !specialized.contains(key)) {
        return Err("slice-use common row lacks specialized row".to_owned());
    }
    Ok(rows
        .iter()
        .filter(|row| row.terminal.stage == MechanicalStage::Plan)
        .count())
}

pub(crate) fn render_slice_use_rows(rows: &[SliceUseAdapterReceiptRow]) -> String {
    let mut rendered = rows
        .iter()
        .map(|row| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                row.terminal.obligation_key.receipt_key(),
                row.use_site.receipt_key(),
                row.source_form,
                row.candidate_form,
                row.target_form,
                row.access_mutability,
                row.adapter,
                row.boundary_site,
                row.boundary_evidence,
                row.retention.tier(),
                row.retention.waiver(),
                row.terminal_class_state.key(),
                row.terminal.stage.key(),
                row.terminal.state.key(),
                row.terminal
                    .reason
                    .as_ref()
                    .map_or_else(|| "-".to_owned(), MechanicalTerminalReason::key),
            )
        })
        .collect::<Vec<_>>();
    rendered.sort();
    let mut output = specialized_receipt_headers()[raw_schema::SLICE_USE_ADAPTER_ROWS].join("\t");
    output.push('\n');
    for row in rendered {
        output.push_str(&row);
        output.push('\n');
    }
    output
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OptionPresentationReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) nullability_fact: String,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) operation: String,
    pub(crate) terminal_contract: TerminalContract,
    pub(crate) retention: MechanicalRetention,
    pub(crate) adapter: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OptionPresentationReceiptPlan {
    pub(crate) obligation: MechanicalObligationPlan,
    pub(crate) nullability_fact: String,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) operation: String,
    pub(crate) terminal_contract: TerminalContract,
    pub(crate) retention: MechanicalRetention,
    pub(crate) adapter: String,
    pub(crate) owner_class: SignatureClassId,
}

impl OptionPresentationReceiptPlan {
    pub(crate) fn materialize(
        &self,
        class_live: bool,
        runtime_reverted: bool,
    ) -> (
        [MechanicalObligationEvent; 2],
        [OptionPresentationReceiptRow; 2],
    ) {
        let events = self.obligation.events(class_live, runtime_reverted);
        let row = |event: &MechanicalObligationEvent| OptionPresentationReceiptRow {
            terminal: SpecializedReceiptTerminal {
                obligation_key: event.key.clone(),
                stage: event.stage,
                state: event.state,
                reason: event.terminal_reason.clone(),
            },
            nullability_fact: self.nullability_fact.clone(),
            source_form: self.source_form.clone(),
            target_form: self.target_form.clone(),
            operation: self.operation.clone(),
            terminal_contract: self.terminal_contract.clone(),
            retention: self.retention.clone(),
            adapter: self.adapter.clone(),
        };
        let rows = [row(&events[0]), row(&events[1])];
        (events, rows)
    }
}

pub(crate) fn reconcile_option_presentation_rows(
    rows: &[OptionPresentationReceiptRow],
    events: &[MechanicalObligationEvent],
) -> Result<usize, String> {
    let mut common = BTreeMap::new();
    for event in events.iter().filter(|event| {
        matches!(
            event.key.family,
            MechanicalFamily::NullInit
                | MechanicalFamily::OptLocalConstruction
                | MechanicalFamily::OptUseUnsupported
                | MechanicalFamily::ArgNullLiteral
        )
    }) {
        let key = format!("{}:{}", event.key.receipt_key(), event.stage.key());
        if common.insert(key.clone(), event).is_some() {
            return Err(format!("duplicate option-presentation common row {key}"));
        }
    }
    let mut specialized = BTreeSet::new();
    for row in rows {
        let key = format!(
            "{}:{}",
            row.terminal.obligation_key.receipt_key(),
            row.terminal.stage.key()
        );
        if !specialized.insert(key.clone()) {
            return Err(format!(
                "duplicate option-presentation specialized row {key}"
            ));
        }
        let event = common
            .get(&key)
            .ok_or_else(|| format!("unowned option-presentation row {key}"))?;
        if row.terminal.obligation_key != event.key
            || row.source_form != event.found_form
            || row.target_form != event.expected_form
            || row.terminal_contract != event.evidence.terminal_contract
            || row.retention != event.evidence.retention
            || row.terminal.state != event.state
            || row.terminal.reason != event.terminal_reason
        {
            return Err(format!(
                "option-presentation specialized/common drift at {key}"
            ));
        }
        event.validate()?;
    }
    if common.keys().any(|key| !specialized.contains(key)) {
        return Err("option-presentation common row lacks specialized row".to_owned());
    }
    Ok(rows
        .iter()
        .filter(|row| row.terminal.stage == MechanicalStage::Plan)
        .count())
}

pub(crate) fn render_option_presentation_rows(rows: &[OptionPresentationReceiptRow]) -> String {
    let mut rendered = rows
        .iter()
        .map(|row| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                row.terminal.obligation_key.receipt_key(),
                row.nullability_fact,
                row.source_form,
                row.target_form,
                row.operation,
                row.terminal_contract.key(),
                row.retention.tier(),
                row.retention.waiver(),
                row.adapter,
                row.terminal.stage.key(),
                row.terminal.state.key(),
                row.terminal
                    .reason
                    .as_ref()
                    .map_or_else(|| "-".to_owned(), MechanicalTerminalReason::key),
            )
        })
        .collect::<Vec<_>>();
    rendered.sort();
    let mut output =
        specialized_receipt_headers()[raw_schema::OPTION_PRESENTATION_RECEIPT_ROWS].join("\t");
    output.push('\n');
    for row in rendered {
        output.push_str(&row);
        output.push('\n');
    }
    output
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeclarationShapeReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) declaration_site: CanonicalSiteKey,
    pub(crate) original_type_form: String,
    pub(crate) settled_emitted_type: String,
    pub(crate) initializer_kind: String,
    pub(crate) typed_temporary: Option<String>,
    pub(crate) evaluation_order: HoistSafety,
    pub(crate) terminal_class_result: MechanicalState,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OutboundReturnBridgeReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) boundary_kind: String,
    pub(crate) endpoint: CanonicalCallee,
    pub(crate) position: String,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) adapter: String,
    pub(crate) negative_write: NegativeWriteEvidence,
    pub(crate) retention: MechanicalRetention,
    pub(crate) lifetime_origin: Option<MechanicalSubjectKey>,
    pub(crate) pair_role: String,
    pub(crate) effect_carrier: Option<CanonicalSiteKey>,
    pub(crate) terminal_interface: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawSinkAdapterReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) operation_kind: String,
    pub(crate) cursor_classification: String,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) copy_a5_carrier: Option<CanonicalSiteKey>,
    pub(crate) cast_pointee: Option<String>,
    pub(crate) cast_mutability: Option<String>,
    pub(crate) null_presentation: Option<String>,
    pub(crate) adapter: String,
    pub(crate) retention: MechanicalRetention,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CompositionDependencyReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) collision_key: String,
    pub(crate) composition_kind: String,
    pub(crate) containment_parent: Option<String>,
    pub(crate) hoist_safety: HoistSafety,
    pub(crate) temporary_identity: Option<String>,
    pub(crate) dependency_classes: BTreeSet<SignatureClassId>,
    pub(crate) terminal_root: Option<SignatureClassId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MissingCShapeReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) owner_class: SignatureClassId,
    pub(crate) callee: CanonicalCallee,
    pub(crate) argument_index: u32,
    pub(crate) expected_form: String,
    pub(crate) found_form: String,
    pub(crate) argument_kind: String,
    pub(crate) synthesized_site: CanonicalSiteKey,
    pub(crate) adapter_owner: MechanicalFamily,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DiagnosticPrimaryMessageReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) error_code: String,
    pub(crate) message_full: String,
    pub(crate) file: String,
    pub(crate) line: u32,
    pub(crate) column: u32,
    pub(crate) end_line: u32,
    pub(crate) end_column: u32,
    pub(crate) rendered_line: String,
    pub(crate) attribution_rule: String,
    pub(crate) owner_class: Option<SignatureClassId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct JsonRecoveryReceiptRow {
    pub(crate) terminal: SpecializedReceiptTerminal,
    pub(crate) subject: MechanicalSubjectKey,
    pub(crate) formal_movement: String,
    pub(crate) root_class: SignatureClassId,
    pub(crate) terminal_interface: String,
    pub(crate) mechanism: MechanicalMechanism,
}

pub(crate) fn specialized_receipt_headers() -> BTreeMap<&'static str, &'static [&'static str]> {
    BTreeMap::from([
        (
            raw_schema::A5_PROOF_SITE_FALLBACK_ROWS,
            &[
                "obligation_key",
                "proof_site_key",
                "verdict",
                "argument_shape",
                "settled_form",
                "raw_view_template",
                "retention_tier",
                "waiver_id",
                "owner_class",
                "stage",
                "state",
                "drop_reason",
            ] as &[_],
        ),
        (
            raw_schema::COMPOSITION_DEPENDENCY_ROWS,
            &[
                "obligation_key",
                "collision_key",
                "composition_kind",
                "containment_parent",
                "hoist_proof",
                "temporary_identity",
                "dependency_classes",
                "terminal_root",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::DECLARATION_SHAPE_RECEIPT_ROWS,
            &[
                "obligation_key",
                "declaration_site",
                "original_type_form",
                "settled_emitted_type",
                "initializer_kind",
                "typed_temporary",
                "evaluation_order",
                "terminal_class_result",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::DIAGNOSTIC_PRIMARY_MESSAGE_ROWS,
            &[
                "obligation_key",
                "error_code",
                "message_full",
                "file",
                "line",
                "column",
                "end_line",
                "end_column",
                "rendered_line",
                "attribution_rule",
                "owner_class",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::JSON_H_RECOVERY_ROWS,
            &[
                "obligation_key",
                "subject_key",
                "formal_movement",
                "root_class",
                "terminal_interface",
                "mechanism",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::MISSING_C_SHAPE_ROWS,
            &[
                "obligation_key",
                "owner_class",
                "callee",
                "argument_index",
                "expected_form",
                "found_form",
                "argument_kind",
                "synthesized_site",
                "adapter_owner",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::OPTION_PRESENTATION_RECEIPT_ROWS,
            &[
                "obligation_key",
                "nullability_fact",
                "source_form",
                "target_form",
                "operation",
                "terminal_contract",
                "raw_view_tier",
                "waiver_id",
                "adapter",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::OUTBOUND_RETURN_BRIDGE_ROWS,
            &[
                "obligation_key",
                "boundary_kind",
                "endpoint",
                "position",
                "source_form",
                "target_form",
                "adapter",
                "negative_write_evidence",
                "retention_evidence",
                "retention_tier",
                "waiver_id",
                "lifetime_origin",
                "pair_role",
                "effect_carrier",
                "terminal_interface",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::RAW_SINK_ADAPTER_ROWS,
            &[
                "obligation_key",
                "operation_kind",
                "offset_cursor_classification",
                "source_form",
                "target_form",
                "copy_a5_carrier",
                "cast_pointee",
                "cast_mutability",
                "null_presentation",
                "adapter",
                "retention_tier",
                "waiver_id",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::SLICE_CONSTRUCTION_RECEIPT_ROWS,
            &[
                "obligation_key",
                "allocation_result_identity",
                "element_type",
                "mutability",
                "nullability",
                "length_expression",
                "length_provenance",
                "evidence_source",
                "extent_kind",
                "waiver_id",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::SLICE_USE_ADAPTER_ROWS,
            &[
                "obligation_key",
                "use_site_key",
                "source_form",
                "candidate_form",
                "target_form",
                "access_mutability",
                "adapter",
                "boundary_site",
                "boundary_evidence",
                "retention_tier",
                "waiver_id",
                "terminal_class_state",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
        (
            raw_schema::UNSAFE_CONTEXT_PRESENTATION_ROWS,
            &[
                "obligation_key",
                "site_key",
                "enclosing_local_def_id",
                "unsafe_fn",
                "wrapper",
                "edition",
                "terminal_class_disposition",
                "stage",
                "state",
                "drop_reason",
            ],
        ),
    ])
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct IdentitySetReconciliation {
    pub(crate) observed_count: usize,
    pub(crate) missing: Vec<String>,
    pub(crate) unexpected: Vec<String>,
    pub(crate) control_duplicates: Vec<String>,
    pub(crate) duplicates: Vec<String>,
}

impl IdentitySetReconciliation {
    pub(crate) fn is_exact(&self) -> bool {
        self.missing.is_empty()
            && self.unexpected.is_empty()
            && self.control_duplicates.is_empty()
            && self.duplicates.is_empty()
    }
}

pub(crate) fn reconcile_identity_rows<CI, CS, PI, PS>(
    control: CI,
    production: PI,
) -> IdentitySetReconciliation
where
    CI: IntoIterator<Item = CS>,
    CS: AsRef<str>,
    PI: IntoIterator<Item = PS>,
    PS: AsRef<str>,
{
    let mut control_counts = BTreeMap::<String, usize>::new();
    for identity in control {
        *control_counts
            .entry(identity.as_ref().to_owned())
            .or_default() += 1;
    }
    let control = control_counts.keys().cloned().collect::<BTreeSet<_>>();
    let mut counts = BTreeMap::<String, usize>::new();
    for identity in production {
        *counts.entry(identity.as_ref().to_owned()).or_default() += 1;
    }
    let observed = counts.keys().cloned().collect::<BTreeSet<_>>();
    IdentitySetReconciliation {
        observed_count: observed.len(),
        missing: control.difference(&observed).cloned().collect(),
        unexpected: observed.difference(&control).cloned().collect(),
        control_duplicates: control_counts
            .into_iter()
            .filter_map(|(identity, count)| (count > 1).then_some(identity))
            .collect(),
        duplicates: counts
            .into_iter()
            .filter_map(|(identity, count)| (count > 1).then_some(identity))
            .collect(),
    }
}

pub(crate) fn reconcile_identity_set<I, S>(
    control: &BTreeSet<String>,
    production: I,
) -> IdentitySetReconciliation
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    reconcile_identity_rows(control, production)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    /// OBL-W1 — every category-(A) obligation owns exactly one plan and one
    /// terminal event; neither omission nor duplication may aggregate.
    #[test]
    fn obl_w1_requires_exactly_one_plan_and_terminal_per_family() {
        let mut events = Vec::new();
        for (index, family) in MechanicalFamily::ALL.into_iter().enumerate() {
            let label = format!("family-{index}");
            let evidence = if family == MechanicalFamily::Composition {
                MechanicalEvidence {
                    hoist: HoistSafety::Place,
                    ..MechanicalEvidence::default()
                }
            } else {
                MechanicalEvidence::default()
            };
            events.push(
                MechanicalObligationEvent::for_test(
                    &label,
                    family,
                    MechanicalStage::Plan,
                    MechanicalState::Planned,
                )
                .with_evidence(evidence.clone()),
            );
            events.push(
                MechanicalObligationEvent::for_test(
                    &label,
                    family,
                    MechanicalStage::Terminal,
                    MechanicalState::Applied,
                )
                .with_evidence(evidence),
            );
        }

        let negative_plan = MechanicalObligationEvent::for_test(
            "composition-negative",
            MechanicalFamily::Composition,
            MechanicalStage::Plan,
            MechanicalState::Planned,
        );
        let negative_terminal = MechanicalObligationEvent::for_test(
            "composition-negative",
            MechanicalFamily::Composition,
            MechanicalStage::Terminal,
            MechanicalState::HeldNonmechanical,
        )
        .with_terminal_reason(MechanicalTerminalReason::CompositionCrossingUnhoistable(
            "hoist-proof-absent".to_owned(),
        ));
        events.push(negative_plan);
        events.push(negative_terminal.clone());

        let summary = reconcile_mechanical_obligations(&events)
            .expect("one plan and terminal row for every family");
        assert_eq!(summary.obligations, MechanicalFamily::ALL.len() + 1);
        assert_eq!(summary.held_nonmechanical, 1);

        // DF3B-A1: if the validator is mutated to accept an Applied
        // composition without a hoist proof, this negative twin fails.
        let mut unproved_applied = negative_terminal;
        unproved_applied.state = MechanicalState::Applied;
        unproved_applied.terminal_reason = None;
        assert!(
            unproved_applied.validate().is_err(),
            "DF3B-A1 survived: Applied composition lacked a hoist proof"
        );

        let mut missing = events.clone();
        missing.pop();
        assert!(reconcile_mechanical_obligations(&missing).is_err());

        let mut duplicate = events;
        duplicate.push(duplicate[1].clone());
        assert!(reconcile_mechanical_obligations(&duplicate).is_err());
    }

    #[test]
    fn obligation_reclassification_is_typed_and_reconciled() {
        let plan = MechanicalObligationEvent::for_test(
            "io-domain",
            MechanicalFamily::EscapesViaForeignArg,
            MechanicalStage::Plan,
            MechanicalState::Planned,
        );
        let terminal = MechanicalObligationEvent::for_test(
            "io-domain",
            MechanicalFamily::EscapesViaForeignArg,
            MechanicalStage::Terminal,
            MechanicalState::Reclassified,
        )
        .with_terminal_reason(MechanicalTerminalReason::IoDomain);
        let summary = reconcile_mechanical_obligations(&[plan, terminal]).unwrap();
        assert_eq!(summary.reclassified, 1);
        assert_eq!(summary.applied, 0);
    }

    #[test]
    fn canonical_site_kind_is_part_of_compiler_identity() {
        let mir = CanonicalSiteKey::for_test(7);
        let mut declaration = mir.clone();
        declaration.location = CanonicalLocation::Declaration {
            owner: rustc_hir::def_id::CRATE_DEF_ID,
            declaration_index: 7,
        };
        assert_ne!(mir, declaration);
        assert_ne!(mir.receipt_key(), declaration.receipt_key());
        assert!(!mir.receipt_key().contains(".rs"));
    }

    /// SCHEMA-W1 — the common obligation row and every specialized receipt
    /// expose their complete sealed columns before any emitter consumes them.
    #[test]
    fn schema_w1_common_and_specialized_headers_are_sealed() {
        const COMMON: &str = "obligation_key\towner_local_def_id\towner_path\tsubject_key\tcanonical_site_key\tfamily\tprior_reason\texpected_form\tfound_form\targument_kind\tsource_shape\trequired_arms\tmechanism\textent_kind\textent_evidence\tretention_tier\twaiver_id\tunsafe_context\tcomposition_parent\tdependency_classes\tstage\tstate\tdrop_reason\n";
        assert_eq!(mechanical_obligation_header(), COMMON);

        let schemas = specialized_receipt_headers();
        // R206 adds provenance detail without changing extent source kind.
        assert_eq!(
            schemas[raw_schema::SLICE_CONSTRUCTION_RECEIPT_ROWS],
            &[
                "obligation_key",
                "allocation_result_identity",
                "element_type",
                "mutability",
                "nullability",
                "length_expression",
                "length_provenance",
                "evidence_source",
                "extent_kind",
                "waiver_id",
                "stage",
                "state",
                "drop_reason",
            ]
        );
        let required = [
            "a5-proof-site-fallback.tsv",
            "composition-dependency.tsv",
            "declaration-shape-receipt.tsv",
            "diagnostic-primary-message.tsv",
            "json-h-recovery.tsv",
            "missing-c-shapes.tsv",
            "option-presentation-receipt.tsv",
            "outbound-return-bridge.tsv",
            "raw-sink-adapter.tsv",
            "slice-construction-receipt.tsv",
            "slice-use-adapter.tsv",
            "unsafe-context-presentation.tsv",
        ];
        assert_eq!(schemas.keys().copied().collect::<Vec<_>>(), required);
        for (file, columns) in schemas {
            assert!(!columns.is_empty(), "{file} has no columns");
            assert_eq!(
                columns.iter().copied().collect::<BTreeSet<_>>().len(),
                columns.len(),
                "{file} repeats a column"
            );
            for common in ["obligation_key", "stage", "state", "drop_reason"] {
                assert!(columns.contains(&common), "{file} lacks {common}");
            }
        }
        let _ = std::mem::size_of::<UnsafeContextReceiptRow>();
        let _ = std::mem::size_of::<A5ProofSiteFallbackReceiptRow>();
        let _ = std::mem::size_of::<SliceConstructionReceiptRow>();
        let _ = std::mem::size_of::<SliceUseAdapterReceiptRow>();
        let _ = std::mem::size_of::<OptionPresentationReceiptRow>();
        let _ = std::mem::size_of::<DeclarationShapeReceiptRow>();
        let _ = std::mem::size_of::<OutboundReturnBridgeReceiptRow>();
        let _ = std::mem::size_of::<RawSinkAdapterReceiptRow>();
        let _ = std::mem::size_of::<CompositionDependencyReceiptRow>();
        let _ = std::mem::size_of::<MissingCShapeReceiptRow>();
        let _ = std::mem::size_of::<DiagnosticPrimaryMessageReceiptRow>();
        let _ = std::mem::size_of::<JsonRecoveryReceiptRow>();
    }

    /// IOID-W1 — equal totals are not evidence of identity equality, and a
    /// duplicate production identity invalidates the control independently.
    #[test]
    fn ioid_w1_rejects_equal_count_substitution_and_duplicates() {
        let control = ["left".to_owned(), "right".to_owned()]
            .into_iter()
            .collect::<BTreeSet<_>>();
        let exact = reconcile_identity_set(&control, ["right", "left"]);
        assert!(exact.is_exact());
        assert_eq!(exact.observed_count, 2);

        let equal_count_different = reconcile_identity_set(&control, ["left", "other"]);
        assert!(!equal_count_different.is_exact());
        assert_eq!(equal_count_different.observed_count, control.len());
        assert_eq!(equal_count_different.missing, vec!["right"]);
        assert_eq!(equal_count_different.unexpected, vec!["other"]);

        let duplicate = reconcile_identity_set(&control, ["left", "right", "right"]);
        assert!(!duplicate.is_exact());
        assert_eq!(duplicate.duplicates, vec!["right"]);

        let duplicate_control =
            reconcile_identity_rows(["left", "right", "right"], ["left", "right"]);
        assert!(!duplicate_control.is_exact());
        assert_eq!(duplicate_control.control_duplicates, vec!["right"]);
    }

    #[test]
    fn evidence_w1_rejects_unlicensed_application_and_accepts_typed_holds() {
        let family = MechanicalFamily::FlowsIntoRawParam;
        let applied = MechanicalObligationEvent::for_test(
            "rb",
            family,
            MechanicalStage::Terminal,
            MechanicalState::Applied,
        )
        .with_mechanism(MechanicalMechanism::SharedRefToMutRaw);
        assert!(applied.validate().is_err());

        let held = MechanicalObligationEvent::for_test(
            "rb-held",
            family,
            MechanicalStage::Terminal,
            MechanicalState::HeldNonmechanical,
        )
        .with_mechanism(MechanicalMechanism::SharedRefToMutRaw)
        .with_terminal_reason(MechanicalTerminalReason::RbNegativeWriteAbsent);
        assert!(held.validate().is_ok());

        let mut evidence = MechanicalEvidence {
            negative_write: NegativeWriteEvidence::FosterImmutable,
            ..MechanicalEvidence::default()
        };
        assert!(
            applied
                .clone()
                .with_evidence(evidence.clone())
                .validate()
                .is_ok()
        );

        evidence.retention = MechanicalRetention::PositiveRetention;
        assert!(applied.clone().with_evidence(evidence).validate().is_err());

        let unwrap = MechanicalObligationEvent::for_test(
            "unwrap",
            MechanicalFamily::OptUseUnsupported,
            MechanicalStage::Terminal,
            MechanicalState::Applied,
        )
        .with_mechanism(MechanicalMechanism::OptionUnwrapRequired);
        assert!(unwrap.validate().is_err());

        let unwrap_evidence = MechanicalEvidence {
            terminal_contract: TerminalContract::Required {
                interface: "terminal:callee#arg0=required-ref".to_owned(),
            },
            ..MechanicalEvidence::default()
        };
        assert!(unwrap.with_evidence(unwrap_evidence).validate().is_ok());

        let fallback = MechanicalObligationEvent::for_test(
            "extent",
            MechanicalFamily::SliceLocalConstruction,
            MechanicalStage::Terminal,
            MechanicalState::Applied,
        )
        .with_evidence(MechanicalEvidence {
            extent: MechanicalExtent::Fallback {
                receipt: FALLBACK_EXTENT_RECEIPT.to_owned(),
                waiver_id: SLICE_EXTENT_WAIVER_ID.to_owned(),
            },
            ..MechanicalEvidence::default()
        });
        assert!(fallback.validate().is_ok());
        let invalid_fallback = fallback.with_evidence(MechanicalEvidence {
            extent: MechanicalExtent::Fallback {
                receipt: FALLBACK_EXTENT_RECEIPT.to_owned(),
                waiver_id: "wrong".to_owned(),
            },
            ..MechanicalEvidence::default()
        });
        assert!(invalid_fallback.validate().is_err());

        let t2 = MechanicalObligationEvent::for_test(
            "t2",
            MechanicalFamily::PairRawView,
            MechanicalStage::Terminal,
            MechanicalState::Applied,
        )
        .with_evidence(MechanicalEvidence {
            retention: MechanicalRetention::T2 {
                waiver_id: RAW_BOUNDARY_T2_WAIVER_ID.to_owned(),
            },
            ..MechanicalEvidence::default()
        });
        assert!(t2.validate().is_ok());
        assert!(
            t2.with_evidence(MechanicalEvidence {
                retention: MechanicalRetention::T2 {
                    waiver_id: "wrong".to_owned(),
                },
                ..MechanicalEvidence::default()
            })
            .validate()
            .is_err()
        );

        let hoist = MechanicalObligationEvent::for_test(
            "hoist",
            MechanicalFamily::Composition,
            MechanicalStage::Terminal,
            MechanicalState::Applied,
        )
        .with_mechanism(MechanicalMechanism::CompositionHoist);
        assert!(hoist.validate().is_err());
        assert!(
            hoist
                .clone()
                .with_evidence(MechanicalEvidence {
                    hoist: HoistSafety::SideEffectFreeUnconditional,
                    ..MechanicalEvidence::default()
                })
                .validate()
                .is_ok()
        );
        let held_crossing = MechanicalObligationEvent::for_test(
            "held-hoist",
            MechanicalFamily::Composition,
            MechanicalStage::Terminal,
            MechanicalState::HeldNonmechanical,
        )
        .with_mechanism(MechanicalMechanism::CompositionHoist)
        .with_terminal_reason(MechanicalTerminalReason::CompositionCrossingUnhoistable(
            "side-effecting".to_owned(),
        ));
        assert!(held_crossing.validate().is_ok());

        let unsafe_context = UnsafeContextPresentation {
            unsafe_fn: true,
            wrapper_inserted: false,
            edition: 2018,
        };
        assert!(unsafe_context.validate().is_ok());
        assert!(
            UnsafeContextPresentation {
                wrapper_inserted: true,
                ..unsafe_context
            }
            .validate()
            .is_err()
        );
    }

    #[test]
    fn a5_specialized_rows_share_identity_state_and_exact_t2_waiver_with_common_rows() {
        let planned = MechanicalObligationEvent::for_test(
            "a5-specialized",
            MechanicalFamily::A5ProofSiteFallback,
            MechanicalStage::Plan,
            MechanicalState::Planned,
        )
        .with_evidence(MechanicalEvidence {
            retention: MechanicalRetention::T2 {
                waiver_id: RAW_BOUNDARY_T2_WAIVER_ID.to_owned(),
            },
            hoist: HoistSafety::Place,
            ..MechanicalEvidence::default()
        });
        let site = planned.key.site.clone();
        let owner = planned.key.owner_class;
        let receipt = A5ProofSiteReceiptPlan {
            obligation: MechanicalObligationPlan {
                planned,
                intended_terminal_state: MechanicalState::Applied,
                intended_terminal_reason: None,
            },
            proof_site_key: site,
            verdict: "overlapping".to_owned(),
            argument_shape: "bare-local".to_owned(),
            settled_form: "slice-mut".to_owned(),
            raw_view_template: "slice-mut-to-raw-mut->c-raw-slice-mut".to_owned(),
            retention: MechanicalRetention::T2 {
                waiver_id: RAW_BOUNDARY_T2_WAIVER_ID.to_owned(),
            },
            owner_class: owner,
        };
        let (events, rows) = receipt.materialize(true, false);
        assert_eq!(
            reconcile_mechanical_obligations(&events).unwrap().applied,
            1
        );
        assert_eq!(reconcile_a5_proof_site_fallback_rows(&rows, &events), Ok(1));
        assert!(
            render_a5_proof_site_fallback_rows(&rows)
                .contains("\tT2\tc-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01\t")
        );

        let mut wrong_waiver = rows.clone();
        wrong_waiver[1].retention = MechanicalRetention::T2 {
            waiver_id: "wrong".to_owned(),
        };
        assert!(reconcile_a5_proof_site_fallback_rows(&wrong_waiver, &events).is_err());
        assert!(reconcile_a5_proof_site_fallback_rows(&rows, &[]).is_err());
        let mut duplicate = rows.to_vec();
        duplicate.push(rows[1].clone());
        assert!(reconcile_a5_proof_site_fallback_rows(&duplicate, &events).is_err());
    }
}
