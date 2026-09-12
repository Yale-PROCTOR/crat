//! Typed, in-memory R345 export contract. This is not a wire decoder or cache
//! schema. The future decoder must reject a partly absent record as Missing;
//! no required field has an Option/default. Proof bodies may live in exact,
//! typed companion records. Their digests and family tags are checked by the
//! adapter; interpreting those bodies remains the named producer's obligation.
use std::{
    collections::{BTreeMap, BTreeSet},
    marker::PhantomData,
};

use super::{EvidenceKey, FieldClassId, SiteId, emission::Kind, lifecycle::CloseKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Digest(pub [u8; 32]);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProgramId(pub String);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionId(pub String);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldKey(pub String);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CallKey {
    pub construction: u32,
    pub caller: FunctionId,
    pub block: u32,
    pub statement: usize,
    pub callee: FunctionId,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeclarationKey {
    pub call: CallKey,
    pub guard: EquationId,
    pub boundary: usize,
    /// Zero based call argument, never a one based MIR parameter.
    pub argument: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EquationId {
    pub construction: u32,
    pub ordinal: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StaticNode {
    pub construction: u32,
    pub var: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceLineage {
    Exact(Vec<CallKey>),
    Recursive { application: CallKey },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceInstance {
    pub endpoint: EquationId,
    pub lineage: SourceLineage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvidenceOwner {
    AcceptedModel,
    Era5b,
    FrameQualification,
    NativeIdentity,
    Emission,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Missing {
    pub owner: EvidenceOwner,
    pub reason: MissingReason,
}
pub type Evidence<T> = Result<T, Missing>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MissingReason {
    /// Exact contract field supplied by the decoder; no placeholder value.
    Field(&'static str),
    Conditional,
    Held(LicensingHold),
    Frame(&'static str),
    IncompleteFamily,
    DeclarationSet,
    DuplicateDeclaration(DeclarationKey),
    Selection,
    GlobalFieldScheme,
    Occurrence,
    Companion(FactFamily),
    DuplicateClose(SiteId),
    CloseReason(SiteId),
    ModelNotOwning(Kind),
    ModelInventory,
}

/// Bodies are addressed by both artifact digest and row, never by a display
/// name. A native decoder supplies the verified record inventory separately.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RecordKey {
    pub artifact: Digest,
    pub row: u32,
}
pub trait FactTag {
    const FAMILY: FactFamily;
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactRef<T: FactTag> {
    pub record: RecordKey,
    marker: PhantomData<T>,
}
impl<T: FactTag> FactRef<T> {
    pub fn new(record: RecordKey) -> Self {
        Self {
            record,
            marker: PhantomData,
        }
    }
}
macro_rules! families {
    ($($tag:ident),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub enum FactFamily { $($tag),+ }
        $(#[derive(Clone, Debug, PartialEq, Eq)] pub struct $tag;
          impl FactTag for $tag { const FAMILY: FactFamily = FactFamily::$tag; })+
    }
}
families!(
    InternalProof,
    CallerProof,
    MemberProof,
    Requirements,
    CheckedLaws,
    SelectionValidation,
    SelectedGlobalFields,
    GlobalFieldSupport,
    TypeInventory,
    ReaderRoles,
    GenerationRecipe,
    OwnCall,
    Construction,
    FieldUses,
    FieldTransaction,
    DeclarationSyntax,
    StructCopies,
    Signatures,
    CallTargets,
    FreeSites,
    CloseRoots,
    DropDepth,
    LeakCoverage,
    ScalarHoist,
    Custody,
    RawAudit,
    FamilyComparison
);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceFrame {
    L01DoublePrime,
    L01TriplePrime,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducerIdentity {
    pub source: String,
    pub analysis_digest: Digest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertificateIdentity {
    pub source: String,
    pub full_analysis_digest: Digest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    pub program: ProgramId,
    pub substrate_manifest_sha256: Digest,
    pub entry_path: String,
    pub entry_sha256: Digest,
    pub producer: ProducerIdentity,
    pub certificate: CertificateIdentity,
    pub analysis_minus_licensing_digest: Digest,
    pub configuration: Digest,
    pub toolchain: Digest,
    pub dependency_digest: Digest,
    pub accepted_round: usize,
    pub snapshot_offset: u32,
    pub source_frame: SourceFrame,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FamilyTransport {
    SameEpoch,
    /// Required for each retained entry in a mixed epoch family manifest.
    Compared(Evidence<FactRef<FamilyComparison>>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Manifest {
    pub schema: u32,
    pub artifact_digest: Digest,
    pub frame: Evidence<Frame>,
    pub family_complete: Evidence<bool>,
    pub declaration_keys: Evidence<BTreeSet<DeclarationKey>>,
    pub transport: Evidence<FamilyTransport>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Certificate {
    Caller {
        internal: Evidence<FactRef<InternalProof>>,
        caller: Evidence<FactRef<CallerProof>>,
    },
    Member {
        internal: Evidence<FactRef<InternalProof>>,
        member: Evidence<FactRef<MemberProof>>,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Valuations {
    pub owning: BTreeMap<StaticNode, bool>,
    pub guards: BTreeMap<EquationId, bool>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Selection {
    pub guard: EquationId,
    pub required: Valuations,
    pub accepted: Valuations,
    pub required_closed_frame: bool,
    pub closed_call_world: bool,
    /// This record must answer R345-3's member-only selection custody question.
    pub validation: Evidence<FactRef<SelectionValidation>>,
    pub attestation: Evidence<Frame>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Disposition {
    Held(LicensingHold),
    Conditional,
    Selected(Evidence<Selection>),
    Missing(Missing),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalFieldScheme {
    /// Whole-declaration selection. Not the union of MemberDecision.fields.
    pub fields: BTreeMap<FieldKey, FieldClassId>,
    pub owning: BTreeSet<FieldKey>,
    pub support: Evidence<FactRef<GlobalFieldSupport>>,
    /// Accepted whole-declaration selection, distinct from conditional support.
    pub selection_basis: Evidence<FactRef<SelectedGlobalFields>>,
    pub frame: Evidence<Frame>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Occurrence {
    pub declaration: DeclarationKey,
    pub source: SourceInstance,
    /// Value node is distinct from the source endpoint's equation identity.
    pub node: StaticNode,
    /// Explicit substitution supplied by native invocation binding, not var.
    pub key: EvidenceKey,
    pub generation_recipe: Evidence<FactRef<GenerationRecipe>>,
    pub transported_key: Evidence<EvidenceKey>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Projection {
    Deref,
    Field(u32),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtraCloseReason {
    LiveAtScopeExit,
    LiveAtUnwind,
    OverwrittenUniqueOwner,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtraClose {
    pub site: SiteId,
    pub path: Vec<Projection>,
    pub kind: CloseKind,
    pub owner: Evidence<EvidenceKey>,
    pub reason: ExtraCloseReason,
    pub required_proofs: Evidence<FactRef<CloseRoots>>,
    pub depth: Evidence<FactRef<DropDepth>>,
}

/// Each reference addresses a typed companion body whose named fields are the
/// report-001 contracts and the existing consumer structs. Missing facts stay
/// attached to the affected site; a kind grant is not an emission permission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Companions {
    pub types: Evidence<FactRef<TypeInventory>>,
    pub readers: Evidence<FactRef<ReaderRoles>>,
    pub own_call: Evidence<FactRef<OwnCall>>,
    pub construction: Evidence<FactRef<Construction>>,
    pub field_uses: Evidence<FactRef<FieldUses>>,
    pub transaction: Evidence<FactRef<FieldTransaction>>,
    pub declaration: Evidence<FactRef<DeclarationSyntax>>,
    pub copies: Evidence<FactRef<StructCopies>>,
    pub signatures: Evidence<FactRef<Signatures>>,
    pub calls: Evidence<FactRef<CallTargets>>,
    pub frees: Evidence<FactRef<FreeSites>>,
    pub leak_coverage: Evidence<FactRef<LeakCoverage>>,
    pub hoist: Evidence<FactRef<ScalarHoist>>,
    pub custody: Evidence<FactRef<Custody>>,
    pub raw_audit: Evidence<FactRef<RawAudit>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    pub declaration_key: Evidence<DeclarationKey>,
    pub baseline_kind: Kind,
    pub disposition: Disposition,
    pub certificate: Evidence<Certificate>,
    pub required_field_set: Evidence<BTreeSet<FieldKey>>,
    pub selected_global_field_scheme: Evidence<GlobalFieldScheme>,
    pub requirements: Evidence<FactRef<Requirements>>,
    pub checked_laws: Evidence<FactRef<CheckedLaws>>,
    pub occurrence: Evidence<Occurrence>,
    pub companions: Companions,
    pub extra_close_obligations: Evidence<Vec<ExtraClose>>,
}

// Lossless hold vocabulary from licensing at 5506aa42 (report 001 pin).
// Unknown future variants must be rejected by the decoder, never flattened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InternalSite {
    RouteCycle,
    PathWithoutReturn,
    ParameterIndex,
    MultipleOwningParameters,
    ParameterNotRawPointer,
    PointeeNotStruct,
    GenericFieldDeclaration,
    HeterogeneousPointerField,
    SinkNotFree,
    SingleDescendantOnly,
    ReturnTypeMismatch,
    ForeignCallNotSink,
    UnsupportedExpression,
    NonPointerDestinationWithSource,
    SourceOperandMissing,
    ConsumedCellNotRefilled,
    SinkOnView,
    ViewStoredIntoOwningCell,
    FieldStoreDeferred,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InternalError {
    Unsupported(InternalSite),
    Coverage(u32),
    ParentFreeWithLiveDescendant,
    CompetingDisposition,
    UnaccountedToken,
    AmbiguousRoute {
        choices: usize,
        from: StaticNode,
        to: StaticNode,
    },
    MissingTransfer,
    BoundaryCoverage,
    FrameCoverage,
    BoundaryDisagreement,
    MultipleSinks,
    PathBudget,
    LoopWithTokenOperation,
    PointerDestinationStore,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallError {
    Unsupported,
    NativeCall,
    Boundary,
    Type,
    Internal(InternalError),
    FieldScheme(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallerHold {
    Coverage,
    UnsupportedEffect,
    Origin,
    CellIdentity,
    MissingStore,
    MissingReset,
    MissingNullInit,
    CompetingResponsibility,
    Forwarding,
    LawCoverage,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LicensingHold {
    Declaration,
    Call(CallError),
    Caller(CallerHold),
}
