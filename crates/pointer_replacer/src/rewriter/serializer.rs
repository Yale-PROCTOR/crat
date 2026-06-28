use std::path::Path;

use anyhow::Context;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{
    Idx, IndexVec,
    bit_set::{DenseBitSet, MixedBitSet, SparseBitMatrix},
};
use rustc_middle::mir::Local;
use rustc_span::def_id::{CrateNum, DefId, DefIndex, LocalDefId};
use serde::{Deserialize, Serialize};

use super::Analysis;
use crate::analyses::{
    borrow::{
        BorrowPromotionResults, StructFieldSlot,
        lifetime_flow::{
            BodyLifetimeFlow, FieldPlace, LifetimeFlowResult, LifetimeFlowResults,
            LifetimeFlowSummary, LifetimeOwner, LifetimeSlot, LocalSlot, SignaturePlace,
            SignatureRoot, SignatureSlot,
        },
    },
    nullity::NullityResult,
    offset_sign::sign::OffsetSignResult,
    output_params::OutputParams,
    ownership::{
        Ownership,
        solidify::{self as ownership_solidify},
    },
    struct_copy::StructCopyAnalysisResult,
    type_qualifier::foster::{self, fatness::Fatness, mutability::Mutability},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct LocalDefIdKey(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DefIdKey(pub u32, pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableAnalysis {
    pub borrow_promotion_result: SerializableBorrowPromotionResults,
    pub borrow_lifetime_flows: SerializableLifetimeFlowResults,
    pub promoted_ref_result: SerializableLocalDenseBitSetMap,
    pub mutability_result: SerializableLocalTypeQualifiers<SerializableMutability>,
    pub fatness_result: SerializableLocalTypeQualifiers<SerializableFatness>,
    pub aliases: SerializableAliases,
    pub output_params: SerializableLocalMixedBitSetMap,
    pub ownership_schemes: Option<SerializableDefTypeQualifiers<Ownership>>,
    pub offset_sign_result: SerializableOffsetSignResult,
    pub nullity_result: SerializableNullityResult,
    pub struct_copy_result: SerializableStructCopyAnalysisResult,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableBorrowPromotionResults {
    pub mutable_locals: SerializableLocalDenseBitSetMap,
    pub shared_locals: SerializableLocalDenseBitSetMap,
    pub mutable_fields: Vec<SerializableStructFieldSlot>,
    pub shared_fields: Vec<SerializableStructFieldSlot>,
    pub lifetime_flows: SerializableLifetimeFlowResults,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SerializableStructFieldSlot {
    pub struct_did: LocalDefIdKey,
    pub field_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableBitSet {
    pub domain_size: usize,
    pub elements: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableSparseBitMatrix {
    pub num_columns: usize,
    pub rows: Vec<SerializableSparseBitMatrixRow>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableSparseBitMatrixRow {
    pub row: u32,
    pub columns: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableLifetimeFlowResult {
    pub summary: SerializableLifetimeFlowSummary,
    pub body: SerializableBodyLifetimeFlow,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableLifetimeFlowSummary {
    pub slots: Vec<SerializableSignatureSlot>,
    pub value_flows: SerializableSparseBitMatrix,
    pub storage_aliases: SerializableSparseBitMatrix,
    pub unknown_targets: SerializableBitSet,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableBodyLifetimeFlow {
    pub slots: Vec<SerializableLocalSlot>,
    pub value_flows: SerializableSparseBitMatrix,
    pub storage_aliases: SerializableSparseBitMatrix,
    pub unknown_targets: SerializableBitSet,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SerializableSignatureRoot {
    Return,
    Arg(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SerializableSignaturePlace {
    pub root: SerializableSignatureRoot,
    pub deref_depth: u8,
    pub field: Option<SerializableStructFieldSlot>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SerializableSignatureSlot {
    pub place: SerializableSignaturePlace,
    pub depth: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SerializableFieldPlace {
    pub base: u32,
    pub deref_depth: u8,
    pub field: SerializableStructFieldSlot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SerializableLifetimeOwner {
    Local(u32),
    Field(SerializableFieldPlace),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SerializableLocalSlot {
    pub owner: SerializableLifetimeOwner,
    pub depth: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableLocalTypeQualifiers<Qualifier> {
    pub struct_fields: SerializableLocalEncoding,
    pub fn_locals: SerializableLocalEncoding,
    pub model: Vec<Qualifier>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableDefTypeQualifiers<Qualifier> {
    pub struct_fields: SerializableDefEncoding,
    pub fn_locals: SerializableDefEncoding,
    pub model: Vec<Qualifier>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableLocalEncoding {
    pub did_idx: Vec<(LocalDefIdKey, usize)>,
    pub contents: Vec<Vec<u32>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableDefEncoding {
    pub did_idx: Vec<(DefIdKey, usize)>,
    pub contents: Vec<Vec<u32>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SerializableMutability {
    Imm,
    Mut,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SerializableFatness {
    Arr,
    Ptr,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableOffsetSignResult {
    pub access_signs: SerializableLocalDenseBitSetMap,
    pub field_access_signs: Vec<SerializableStructFieldSlot>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableNullityResult {
    pub non_null_params: SerializableLocalDenseBitSetMap,
    pub non_null_locals: SerializableLocalDenseBitSetMap,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializableStructCopyAnalysisResult {
    pub copy_impl_structs: Vec<LocalDefIdKey>,
    pub copy_removable_structs: Vec<LocalDefIdKey>,
}

pub type SerializableLocalDenseBitSetMap = Vec<(LocalDefIdKey, SerializableBitSet)>;
pub type SerializableLocalMixedBitSetMap = Vec<(LocalDefIdKey, SerializableBitSet)>;
pub type SerializableLifetimeFlowResults = Vec<(LocalDefIdKey, SerializableLifetimeFlowResult)>;
pub type SerializableAliases = Vec<(LocalDefIdKey, Vec<(u32, Vec<u32>)>)>;

pub fn serialize_analysis(analysis: &Analysis) -> SerializableAnalysis {
    SerializableAnalysis {
        borrow_promotion_result: serialize_borrow_promotion_results(
            &analysis.borrow_promotion_result,
        ),
        borrow_lifetime_flows: serialize_lifetime_flow_results(&analysis.borrow_lifetime_flows),
        promoted_ref_result: serialize_local_dense_bit_set_map(&analysis.promoted_ref_result),
        mutability_result: serialize_foster_type_qualifiers(
            &analysis.mutability_result,
            SerializableMutability::from,
        ),
        fatness_result: serialize_foster_type_qualifiers(
            &analysis.fatness_result,
            SerializableFatness::from,
        ),
        aliases: serialize_aliases(&analysis.aliases),
        output_params: serialize_local_mixed_bit_set_map(&analysis.output_params),
        ownership_schemes: analysis
            .ownership_schemes
            .as_ref()
            .map(|schemes| serialize_ownership_type_qualifiers(schemes, |ownership| ownership)),
        offset_sign_result: serialize_offset_sign_result(&analysis.offset_sign_result),
        nullity_result: serialize_nullity_result(&analysis.nullity_result),
        struct_copy_result: serialize_struct_copy_analysis_result(&analysis.struct_copy_result),
    }
}

pub fn dump_analysis_to_file(analysis: &Analysis, path: &Path) -> anyhow::Result<()> {
    let serialized = serialize_analysis(analysis);
    let bytes = postcard::to_stdvec(&serialized).context("serialize pointer analysis")?;
    std::fs::write(path, bytes)
        .with_context(|| format!("write pointer analysis to {}", path.display()))
}

pub fn load_analysis_from_file(path: &Path) -> anyhow::Result<Analysis> {
    let bytes = std::fs::read(path)
        .with_context(|| format!("read pointer analysis from {}", path.display()))?;
    let serialized = postcard::from_bytes(&bytes).context("deserialize pointer analysis")?;
    Ok(deserialize_analysis(serialized))
}

pub fn deserialize_analysis(serialized: SerializableAnalysis) -> Analysis {
    Analysis {
        borrow_promotion_result: deserialize_borrow_promotion_results(
            serialized.borrow_promotion_result,
        ),
        borrow_lifetime_flows: deserialize_lifetime_flow_results(serialized.borrow_lifetime_flows),
        promoted_ref_result: deserialize_local_dense_bit_set_map(serialized.promoted_ref_result),
        mutability_result: deserialize_foster_type_qualifiers(
            serialized.mutability_result,
            Mutability::from,
        ),
        fatness_result: deserialize_foster_type_qualifiers(
            serialized.fatness_result,
            Fatness::from,
        ),
        aliases: deserialize_aliases(serialized.aliases),
        output_params: deserialize_local_mixed_bit_set_map(serialized.output_params),
        ownership_schemes: serialized
            .ownership_schemes
            .map(|schemes| deserialize_ownership_type_qualifiers(schemes, |ownership| ownership)),
        offset_sign_result: deserialize_offset_sign_result(serialized.offset_sign_result),
        nullity_result: deserialize_nullity_result(serialized.nullity_result),
        struct_copy_result: deserialize_struct_copy_analysis_result(serialized.struct_copy_result),
    }
}

impl From<&Analysis> for SerializableAnalysis {
    fn from(value: &Analysis) -> Self {
        serialize_analysis(value)
    }
}

impl From<SerializableAnalysis> for Analysis {
    fn from(value: SerializableAnalysis) -> Self {
        deserialize_analysis(value)
    }
}

impl From<Mutability> for SerializableMutability {
    fn from(value: Mutability) -> Self {
        match value {
            Mutability::Imm => Self::Imm,
            Mutability::Mut => Self::Mut,
        }
    }
}

impl From<SerializableMutability> for Mutability {
    fn from(value: SerializableMutability) -> Self {
        match value {
            SerializableMutability::Imm => Self::Imm,
            SerializableMutability::Mut => Self::Mut,
        }
    }
}

impl From<Fatness> for SerializableFatness {
    fn from(value: Fatness) -> Self {
        match value {
            Fatness::Arr => Self::Arr,
            Fatness::Ptr => Self::Ptr,
        }
    }
}

impl From<SerializableFatness> for Fatness {
    fn from(value: SerializableFatness) -> Self {
        match value {
            SerializableFatness::Arr => Self::Arr,
            SerializableFatness::Ptr => Self::Ptr,
        }
    }
}

fn serialize_borrow_promotion_results(
    results: &BorrowPromotionResults,
) -> SerializableBorrowPromotionResults {
    SerializableBorrowPromotionResults {
        mutable_locals: serialize_local_dense_bit_set_map(&results.mutable_locals),
        shared_locals: serialize_local_dense_bit_set_map(&results.shared_locals),
        mutable_fields: serialize_struct_field_set(&results.mutable_fields),
        shared_fields: serialize_struct_field_set(&results.shared_fields),
        lifetime_flows: serialize_lifetime_flow_results(&results.lifetime_flows),
    }
}

fn deserialize_borrow_promotion_results(
    serialized: SerializableBorrowPromotionResults,
) -> BorrowPromotionResults {
    BorrowPromotionResults {
        mutable_locals: deserialize_local_dense_bit_set_map(serialized.mutable_locals),
        shared_locals: deserialize_local_dense_bit_set_map(serialized.shared_locals),
        mutable_fields: deserialize_struct_field_set(serialized.mutable_fields),
        shared_fields: deserialize_struct_field_set(serialized.shared_fields),
        lifetime_flows: deserialize_lifetime_flow_results(serialized.lifetime_flows),
    }
}

fn serialize_lifetime_flow_results(
    results: &LifetimeFlowResults,
) -> SerializableLifetimeFlowResults {
    let mut entries = results
        .iter()
        .map(|(&did, result)| {
            (
                local_def_id_to_key(did),
                serialize_lifetime_flow_result(result),
            )
        })
        .collect::<Vec<_>>();
    entries.sort_by_key(|(did, _)| *did);
    entries
}

fn deserialize_lifetime_flow_results(
    serialized: SerializableLifetimeFlowResults,
) -> LifetimeFlowResults {
    serialized
        .into_iter()
        .map(|(did, result)| {
            (
                local_def_id_from_key(did),
                deserialize_lifetime_flow_result(result),
            )
        })
        .collect()
}

fn serialize_lifetime_flow_result(result: &LifetimeFlowResult) -> SerializableLifetimeFlowResult {
    SerializableLifetimeFlowResult {
        summary: serialize_lifetime_flow_summary(&result.summary),
        body: serialize_body_lifetime_flow(&result.body),
    }
}

fn deserialize_lifetime_flow_result(
    serialized: SerializableLifetimeFlowResult,
) -> LifetimeFlowResult {
    LifetimeFlowResult {
        summary: deserialize_lifetime_flow_summary(serialized.summary),
        body: deserialize_body_lifetime_flow(serialized.body),
    }
}

fn serialize_lifetime_flow_summary(
    summary: &LifetimeFlowSummary,
) -> SerializableLifetimeFlowSummary {
    let domain_size = summary.slots.len();
    SerializableLifetimeFlowSummary {
        slots: serialize_index_vec(&summary.slots, serialize_signature_slot),
        value_flows: serialize_sparse_bit_matrix(&summary.value_flows, domain_size),
        storage_aliases: serialize_sparse_bit_matrix(&summary.storage_aliases, domain_size),
        unknown_targets: serialize_dense_bit_set(&summary.unknown_targets),
    }
}

fn deserialize_lifetime_flow_summary(
    serialized: SerializableLifetimeFlowSummary,
) -> LifetimeFlowSummary {
    LifetimeFlowSummary {
        slots: deserialize_index_vec(serialized.slots, deserialize_signature_slot),
        value_flows: deserialize_sparse_bit_matrix(serialized.value_flows),
        storage_aliases: deserialize_sparse_bit_matrix(serialized.storage_aliases),
        unknown_targets: deserialize_dense_bit_set(serialized.unknown_targets),
    }
}

fn serialize_body_lifetime_flow(body: &BodyLifetimeFlow) -> SerializableBodyLifetimeFlow {
    let domain_size = body.slots.len();
    SerializableBodyLifetimeFlow {
        slots: serialize_index_vec(&body.slots, serialize_local_slot),
        value_flows: serialize_sparse_bit_matrix(&body.value_flows, domain_size),
        storage_aliases: serialize_sparse_bit_matrix(&body.storage_aliases, domain_size),
        unknown_targets: serialize_dense_bit_set(&body.unknown_targets),
    }
}

fn deserialize_body_lifetime_flow(serialized: SerializableBodyLifetimeFlow) -> BodyLifetimeFlow {
    let slots = deserialize_index_vec(serialized.slots, deserialize_local_slot);
    let slot_map = lifetime_slot_map(&slots);
    BodyLifetimeFlow {
        slots,
        slot_map,
        value_flows: deserialize_sparse_bit_matrix(serialized.value_flows),
        storage_aliases: deserialize_sparse_bit_matrix(serialized.storage_aliases),
        unknown_targets: deserialize_dense_bit_set(serialized.unknown_targets),
    }
}

fn serialize_signature_slot(slot: &SignatureSlot) -> SerializableSignatureSlot {
    SerializableSignatureSlot {
        place: serialize_signature_place(&slot.place),
        depth: slot.depth,
    }
}

fn deserialize_signature_slot(serialized: SerializableSignatureSlot) -> SignatureSlot {
    SignatureSlot {
        place: deserialize_signature_place(serialized.place),
        depth: serialized.depth,
    }
}

fn serialize_signature_place(place: &SignaturePlace) -> SerializableSignaturePlace {
    SerializableSignaturePlace {
        root: serialize_signature_root(place.root),
        deref_depth: place.deref_depth,
        field: place.field.map(SerializableStructFieldSlot::from),
    }
}

fn deserialize_signature_place(serialized: SerializableSignaturePlace) -> SignaturePlace {
    SignaturePlace {
        root: deserialize_signature_root(serialized.root),
        deref_depth: serialized.deref_depth,
        field: serialized.field.map(StructFieldSlot::from),
    }
}

fn serialize_signature_root(root: SignatureRoot) -> SerializableSignatureRoot {
    match root {
        SignatureRoot::Return => SerializableSignatureRoot::Return,
        SignatureRoot::Arg(local) => SerializableSignatureRoot::Arg(idx_to_u32(local)),
    }
}

fn deserialize_signature_root(serialized: SerializableSignatureRoot) -> SignatureRoot {
    match serialized {
        SerializableSignatureRoot::Return => SignatureRoot::Return,
        SerializableSignatureRoot::Arg(local) => SignatureRoot::Arg(idx_from_u32(local)),
    }
}

fn serialize_local_slot(slot: &LocalSlot) -> SerializableLocalSlot {
    SerializableLocalSlot {
        owner: serialize_lifetime_owner(slot.owner),
        depth: slot.depth,
    }
}

fn deserialize_local_slot(serialized: SerializableLocalSlot) -> LocalSlot {
    LocalSlot {
        owner: deserialize_lifetime_owner(serialized.owner),
        depth: serialized.depth,
    }
}

fn serialize_lifetime_owner(owner: LifetimeOwner) -> SerializableLifetimeOwner {
    match owner {
        LifetimeOwner::Local(local) => SerializableLifetimeOwner::Local(idx_to_u32(local)),
        LifetimeOwner::Field(field) => {
            SerializableLifetimeOwner::Field(serialize_field_place(field))
        }
    }
}

fn deserialize_lifetime_owner(serialized: SerializableLifetimeOwner) -> LifetimeOwner {
    match serialized {
        SerializableLifetimeOwner::Local(local) => LifetimeOwner::Local(idx_from_u32(local)),
        SerializableLifetimeOwner::Field(field) => {
            LifetimeOwner::Field(deserialize_field_place(field))
        }
    }
}

fn serialize_field_place(field: FieldPlace) -> SerializableFieldPlace {
    SerializableFieldPlace {
        base: idx_to_u32(field.base),
        deref_depth: field.deref_depth,
        field: SerializableStructFieldSlot::from(field.field),
    }
}

fn deserialize_field_place(serialized: SerializableFieldPlace) -> FieldPlace {
    FieldPlace {
        base: idx_from_u32(serialized.base),
        deref_depth: serialized.deref_depth,
        field: StructFieldSlot::from(serialized.field),
    }
}

fn lifetime_slot_map(
    slots: &IndexVec<LifetimeSlot, LocalSlot>,
) -> FxHashMap<(LifetimeOwner, u8), LifetimeSlot> {
    slots
        .iter_enumerated()
        .map(|(slot, local_slot)| ((local_slot.owner, local_slot.depth), slot))
        .collect()
}

fn serialize_foster_type_qualifiers<Qualifier, SerializedQualifier>(
    qualifiers: &foster::TypeQualifiers<Qualifier>,
    mut serialize_qualifier: impl FnMut(Qualifier) -> SerializedQualifier,
) -> SerializableLocalTypeQualifiers<SerializedQualifier>
where
    Qualifier: Copy,
{
    SerializableLocalTypeQualifiers {
        struct_fields: serialize_local_encoding(&qualifiers.struct_fields.0),
        fn_locals: serialize_local_encoding(&qualifiers.fn_locals.0),
        model: qualifiers
            .model
            .raw
            .iter()
            .copied()
            .map(&mut serialize_qualifier)
            .collect(),
    }
}

fn deserialize_foster_type_qualifiers<SerializedQualifier, Qualifier>(
    serialized: SerializableLocalTypeQualifiers<SerializedQualifier>,
    mut deserialize_qualifier: impl FnMut(SerializedQualifier) -> Qualifier,
) -> foster::TypeQualifiers<Qualifier> {
    foster::TypeQualifiers {
        struct_fields: crate::analyses::encoding::StructFields(deserialize_local_encoding(
            serialized.struct_fields,
        )),
        fn_locals: crate::analyses::encoding::FnLocals(deserialize_local_encoding(
            serialized.fn_locals,
        )),
        model: index_vec_from_values(serialized.model.into_iter().map(&mut deserialize_qualifier)),
    }
}

fn serialize_ownership_type_qualifiers<Qualifier, SerializedQualifier>(
    qualifiers: &ownership_solidify::TypeQualifiers<Qualifier>,
    mut serialize_qualifier: impl FnMut(Qualifier) -> SerializedQualifier,
) -> SerializableDefTypeQualifiers<SerializedQualifier>
where
    Qualifier: Copy,
{
    SerializableDefTypeQualifiers {
        struct_fields: serialize_def_discretization(&qualifiers.struct_fields.0),
        fn_locals: serialize_def_discretization(&qualifiers.fn_locals.0),
        model: qualifiers
            .model
            .raw
            .iter()
            .copied()
            .map(&mut serialize_qualifier)
            .collect(),
    }
}

fn deserialize_ownership_type_qualifiers<SerializedQualifier, Qualifier>(
    serialized: SerializableDefTypeQualifiers<SerializedQualifier>,
    mut deserialize_qualifier: impl FnMut(SerializedQualifier) -> Qualifier,
) -> ownership_solidify::TypeQualifiers<Qualifier> {
    ownership_solidify::TypeQualifiers {
        struct_fields: crate::analyses::ownership::discretization::StructFields(
            deserialize_def_discretization(serialized.struct_fields),
        ),
        fn_locals: crate::analyses::ownership::discretization::FnLocals(
            deserialize_def_discretization(serialized.fn_locals),
        ),
        model: index_vec_from_values(serialized.model.into_iter().map(&mut deserialize_qualifier)),
    }
}

fn serialize_local_encoding<Index>(
    encoding: &crate::analyses::encoding::Encoding<Index>,
) -> SerializableLocalEncoding
where Index: Idx {
    let mut did_idx = encoding
        .did_idx
        .iter()
        .map(|(&did, &idx)| (local_def_id_to_key(did), idx))
        .collect::<Vec<_>>();
    did_idx.sort_by_key(|(did, _)| *did);
    SerializableLocalEncoding {
        did_idx,
        contents: serialize_fixed_vec_vec(&encoding.contents),
    }
}

fn deserialize_local_encoding<Index>(
    serialized: SerializableLocalEncoding,
) -> crate::analyses::encoding::Encoding<Index>
where Index: Idx {
    crate::analyses::encoding::Encoding {
        did_idx: serialized
            .did_idx
            .into_iter()
            .map(|(did, idx)| (local_def_id_from_key(did), idx))
            .collect(),
        contents: deserialize_fixed_vec_vec(serialized.contents),
    }
}

fn serialize_def_discretization<Index>(
    discretization: &crate::analyses::ownership::discretization::Discretization<Index>,
) -> SerializableDefEncoding
where Index: Idx {
    let mut did_idx = discretization
        .did_idx
        .iter()
        .map(|(&did, &idx)| (def_id_to_key(did), idx))
        .collect::<Vec<_>>();
    did_idx.sort_by_key(|(did, _)| *did);
    SerializableDefEncoding {
        did_idx,
        contents: serialize_ownership_vec_vec(&discretization.contents),
    }
}

fn deserialize_def_discretization<Index>(
    serialized: SerializableDefEncoding,
) -> crate::analyses::ownership::discretization::Discretization<Index>
where Index: Idx {
    crate::analyses::ownership::discretization::Discretization {
        did_idx: serialized
            .did_idx
            .into_iter()
            .map(|(did, idx)| (def_id_from_key(did), idx))
            .collect(),
        contents: deserialize_ownership_vec_vec(serialized.contents),
    }
}

fn serialize_offset_sign_result(result: &OffsetSignResult) -> SerializableOffsetSignResult {
    SerializableOffsetSignResult {
        access_signs: serialize_local_dense_bit_set_map(&result.access_signs),
        field_access_signs: serialize_struct_field_set(&result.field_access_signs),
    }
}

fn deserialize_offset_sign_result(serialized: SerializableOffsetSignResult) -> OffsetSignResult {
    OffsetSignResult {
        access_signs: deserialize_local_dense_bit_set_map(serialized.access_signs),
        field_access_signs: deserialize_struct_field_set(serialized.field_access_signs),
    }
}

fn serialize_nullity_result(result: &NullityResult) -> SerializableNullityResult {
    SerializableNullityResult {
        non_null_params: serialize_local_dense_bit_set_map(&result.non_null_params),
        non_null_locals: serialize_local_dense_bit_set_map(&result.non_null_locals),
    }
}

fn deserialize_nullity_result(serialized: SerializableNullityResult) -> NullityResult {
    NullityResult {
        non_null_params: deserialize_local_dense_bit_set_map(serialized.non_null_params),
        non_null_locals: deserialize_local_dense_bit_set_map(serialized.non_null_locals),
    }
}

fn serialize_struct_copy_analysis_result(
    result: &StructCopyAnalysisResult,
) -> SerializableStructCopyAnalysisResult {
    SerializableStructCopyAnalysisResult {
        copy_impl_structs: serialize_local_def_id_set(&result.copy_impl_structs),
        copy_removable_structs: serialize_local_def_id_set(&result.copy_removable_structs),
    }
}

fn deserialize_struct_copy_analysis_result(
    serialized: SerializableStructCopyAnalysisResult,
) -> StructCopyAnalysisResult {
    StructCopyAnalysisResult {
        copy_impl_structs: deserialize_local_def_id_set(serialized.copy_impl_structs),
        copy_removable_structs: deserialize_local_def_id_set(serialized.copy_removable_structs),
    }
}

fn serialize_local_dense_bit_set_map(
    map: &FxHashMap<LocalDefId, DenseBitSet<Local>>,
) -> SerializableLocalDenseBitSetMap {
    let mut entries = map
        .iter()
        .map(|(&did, set)| (local_def_id_to_key(did), serialize_dense_bit_set(set)))
        .collect::<Vec<_>>();
    entries.sort_by_key(|(did, _)| *did);
    entries
}

fn deserialize_local_dense_bit_set_map(
    serialized: SerializableLocalDenseBitSetMap,
) -> FxHashMap<LocalDefId, DenseBitSet<Local>> {
    serialized
        .into_iter()
        .map(|(did, set)| (local_def_id_from_key(did), deserialize_dense_bit_set(set)))
        .collect()
}

fn serialize_local_mixed_bit_set_map(map: &OutputParams) -> SerializableLocalMixedBitSetMap {
    let mut entries = map
        .iter()
        .map(|(&did, set)| (local_def_id_to_key(did), serialize_mixed_bit_set(set)))
        .collect::<Vec<_>>();
    entries.sort_by_key(|(did, _)| *did);
    entries
}

fn deserialize_local_mixed_bit_set_map(
    serialized: SerializableLocalMixedBitSetMap,
) -> OutputParams {
    serialized
        .into_iter()
        .map(|(did, set)| (local_def_id_from_key(did), deserialize_mixed_bit_set(set)))
        .collect()
}

fn serialize_aliases(
    aliases: &FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
) -> SerializableAliases {
    let mut entries = aliases
        .iter()
        .map(|(&did, local_aliases)| {
            (
                local_def_id_to_key(did),
                serialize_local_aliases(local_aliases),
            )
        })
        .collect::<Vec<_>>();
    entries.sort_by_key(|(did, _)| *did);
    entries
}

fn deserialize_aliases(
    serialized: SerializableAliases,
) -> FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> {
    serialized
        .into_iter()
        .map(|(did, aliases)| {
            (
                local_def_id_from_key(did),
                deserialize_local_aliases(aliases),
            )
        })
        .collect()
}

fn serialize_local_aliases(aliases: &FxHashMap<Local, FxHashSet<Local>>) -> Vec<(u32, Vec<u32>)> {
    let mut entries = aliases
        .iter()
        .map(|(&local, aliases)| (idx_to_u32(local), serialize_local_set(aliases)))
        .collect::<Vec<_>>();
    entries.sort_by_key(|(local, _)| *local);
    entries
}

fn deserialize_local_aliases(
    serialized: Vec<(u32, Vec<u32>)>,
) -> FxHashMap<Local, FxHashSet<Local>> {
    serialized
        .into_iter()
        .map(|(local, aliases)| (idx_from_u32(local), deserialize_local_set(aliases)))
        .collect()
}

fn serialize_struct_field_set(
    set: &FxHashSet<StructFieldSlot>,
) -> Vec<SerializableStructFieldSlot> {
    let mut fields = set
        .iter()
        .copied()
        .map(SerializableStructFieldSlot::from)
        .collect::<Vec<_>>();
    fields.sort();
    fields
}

fn deserialize_struct_field_set(
    serialized: Vec<SerializableStructFieldSlot>,
) -> FxHashSet<StructFieldSlot> {
    serialized.into_iter().map(StructFieldSlot::from).collect()
}

fn serialize_local_def_id_set(set: &FxHashSet<LocalDefId>) -> Vec<LocalDefIdKey> {
    let mut values = set
        .iter()
        .copied()
        .map(local_def_id_to_key)
        .collect::<Vec<_>>();
    values.sort();
    values
}

fn deserialize_local_def_id_set(serialized: Vec<LocalDefIdKey>) -> FxHashSet<LocalDefId> {
    serialized.into_iter().map(local_def_id_from_key).collect()
}

fn serialize_local_set(set: &FxHashSet<Local>) -> Vec<u32> {
    let mut values = set.iter().copied().map(idx_to_u32).collect::<Vec<_>>();
    values.sort();
    values
}

fn deserialize_local_set(serialized: Vec<u32>) -> FxHashSet<Local> {
    serialized.into_iter().map(idx_from_u32).collect()
}

fn serialize_dense_bit_set<Index>(set: &DenseBitSet<Index>) -> SerializableBitSet
where Index: Idx {
    SerializableBitSet {
        domain_size: set.domain_size(),
        elements: set.iter().map(idx_to_u32).collect(),
    }
}

fn deserialize_dense_bit_set<Index>(serialized: SerializableBitSet) -> DenseBitSet<Index>
where Index: Idx {
    let mut set = DenseBitSet::new_empty(serialized.domain_size);
    for element in serialized.elements {
        set.insert(idx_from_u32(element));
    }
    set
}

fn serialize_mixed_bit_set<Index>(set: &MixedBitSet<Index>) -> SerializableBitSet
where Index: Idx {
    SerializableBitSet {
        domain_size: set.domain_size(),
        elements: set.iter().map(idx_to_u32).collect(),
    }
}

fn deserialize_mixed_bit_set<Index>(serialized: SerializableBitSet) -> MixedBitSet<Index>
where Index: Idx {
    let mut set = MixedBitSet::new_empty(serialized.domain_size);
    for element in serialized.elements {
        set.insert(idx_from_u32(element));
    }
    set
}

fn serialize_sparse_bit_matrix<Row, Column>(
    matrix: &SparseBitMatrix<Row, Column>,
    num_columns: usize,
) -> SerializableSparseBitMatrix
where
    Row: Idx,
    Column: Idx,
{
    SerializableSparseBitMatrix {
        num_columns,
        rows: matrix
            .rows()
            .filter_map(|row| {
                matrix
                    .row(row)
                    .map(|columns| SerializableSparseBitMatrixRow {
                        row: idx_to_u32(row),
                        columns: columns.iter().map(idx_to_u32).collect(),
                    })
            })
            .collect(),
    }
}

fn deserialize_sparse_bit_matrix<Row, Column>(
    serialized: SerializableSparseBitMatrix,
) -> SparseBitMatrix<Row, Column>
where
    Row: Idx,
    Column: Idx,
{
    let mut matrix = SparseBitMatrix::new(serialized.num_columns);
    for row in serialized.rows {
        let row_index = idx_from_u32(row.row);
        for column in row.columns {
            matrix.insert(row_index, idx_from_u32(column));
        }
    }
    matrix
}

fn serialize_index_vec<Index, Value, SerializedValue>(
    values: &IndexVec<Index, Value>,
    mut serialize_value: impl FnMut(&Value) -> SerializedValue,
) -> Vec<SerializedValue>
where
    Index: Idx,
{
    values.raw.iter().map(&mut serialize_value).collect()
}

fn deserialize_index_vec<Index, SerializedValue, Value>(
    values: Vec<SerializedValue>,
    mut deserialize_value: impl FnMut(SerializedValue) -> Value,
) -> IndexVec<Index, Value>
where
    Index: Idx,
{
    IndexVec::from_raw(values.into_iter().map(&mut deserialize_value).collect())
}

fn index_vec_from_values<Index, Value>(
    values: impl IntoIterator<Item = Value>,
) -> IndexVec<Index, Value>
where Index: Idx {
    IndexVec::from_raw(values.into_iter().collect())
}

fn serialize_fixed_vec_vec<Index>(
    values: &crate::utils::dsa::fixed_shape::VecVec<Index>,
) -> Vec<Vec<u32>>
where Index: Idx {
    values
        .iter()
        .map(|items| items.iter().copied().map(idx_to_u32).collect())
        .collect()
}

fn deserialize_fixed_vec_vec<Index>(
    serialized: Vec<Vec<u32>>,
) -> crate::utils::dsa::fixed_shape::VecVec<Index>
where Index: Idx {
    serialized
        .into_iter()
        .map(|items| items.into_iter().map(idx_from_u32).collect::<Vec<_>>())
        .collect::<Vec<_>>()
        .into()
}

fn serialize_ownership_vec_vec<Index>(
    values: &crate::analyses::ownership::vec_vec::VecVec<Index>,
) -> Vec<Vec<u32>>
where Index: Idx {
    values
        .indices
        .array_windows()
        .map(|&[start, end]| {
            values.data[start..end]
                .iter()
                .copied()
                .map(idx_to_u32)
                .collect()
        })
        .collect()
}

fn deserialize_ownership_vec_vec<Index>(
    serialized: Vec<Vec<u32>>,
) -> crate::analyses::ownership::vec_vec::VecVec<Index>
where Index: Idx {
    let mut builder =
        crate::analyses::ownership::vec_vec::VecVec::with_indices_capacity(serialized.len());
    for items in serialized {
        for item in items {
            builder.push_inner(idx_from_u32(item));
        }
        builder.push();
    }
    builder.done()
}

impl From<StructFieldSlot> for SerializableStructFieldSlot {
    fn from(value: StructFieldSlot) -> Self {
        SerializableStructFieldSlot {
            struct_did: local_def_id_to_key(value.struct_did),
            field_index: value.field_index,
        }
    }
}

impl From<SerializableStructFieldSlot> for StructFieldSlot {
    fn from(value: SerializableStructFieldSlot) -> Self {
        StructFieldSlot {
            struct_did: local_def_id_from_key(value.struct_did),
            field_index: value.field_index,
        }
    }
}

fn local_def_id_to_key(def_id: LocalDefId) -> LocalDefIdKey {
    LocalDefIdKey(def_id.local_def_index.as_u32())
}

fn local_def_id_from_key(key: LocalDefIdKey) -> LocalDefId {
    LocalDefId {
        local_def_index: DefIndex::from_u32(key.0),
    }
}

fn def_id_to_key(def_id: DefId) -> DefIdKey {
    DefIdKey(def_id.index.as_u32(), def_id.krate.as_u32())
}

fn def_id_from_key(key: DefIdKey) -> DefId {
    DefId {
        index: DefIndex::from_u32(key.0),
        krate: CrateNum::from_u32(key.1),
    }
}

fn idx_to_u32<Index>(idx: Index) -> u32
where Index: Idx {
    u32::try_from(idx.index()).expect("rustc index does not fit in u32")
}

fn idx_from_u32<Index>(idx: u32) -> Index
where Index: Idx {
    Index::new(idx as usize)
}
