//! In-memory binding of an already validated cache entry to the native model.
//! The caller authenticates the expected manifest and sealed entry bytes; this
//! module performs no IO, cache loading, environment changes or analysis.
//! Dynamic generation evidence is not present in the cache and stays Missing.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use sha2::{Digest as _, Sha256};

use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        cache_contract::{self, SemanticInputs, StreamHashes, stream::Metadata},
        crate_slots::CrateSlots,
        slot_key::{field_key, local_key},
        slots::{SlotId, SlotOwner},
        solver::SlotRef,
    },
    bo_rewriter::ownership_fields::{
        OwnerId, SiteId,
        emission::Kind,
        export::{Digest, Evidence, EvidenceOwner, Missing, MissingReason, SourceFrame},
        model_adapter::{AcceptedInputs, ConsumptionPins, ExecutionRole, ModelFrame, ModelSlot},
    },
    utils::rustc::RustProgram,
};

pub(crate) struct NativeCacheInputs<'a, 'tcx> {
    pub(crate) metadata: &'a Metadata,
    pub(crate) hashes: &'a StreamHashes,
    pub(crate) actual_semantic_inputs: &'a SemanticInputs,
    pub(crate) pins: &'a Evidence<ConsumptionPins>,
    pub(crate) program: &'a RustProgram<'tcx>,
    pub(crate) slots: &'a CrateSlots,
    /// The consumed CachedModel.model, never CachedModel.baseline_model.
    pub(crate) model: &'a FxHashMap<SlotRef, SlotKind>,
    pub(crate) emission_configuration: Evidence<Digest>,
    pub(crate) required_bindings: Evidence<BTreeSet<SiteId>>,
}

pub(crate) fn bind(
    expected: &ModelFrame,
    native: NativeCacheInputs<'_, '_>,
) -> Evidence<AcceptedInputs> {
    let metadata = native.metadata;
    metadata.validate_meta().map_err(|_| Missing {
        owner: EvidenceOwner::AcceptedModel,
        reason: MissingReason::Field("validated_cache_metadata"),
    })?;
    if metadata.inputs != *native.actual_semantic_inputs {
        return Err(frame_hold("native_semantic_inputs"));
    }
    if expected.source_frame != SourceFrame::L01DoublePrime
        || expected.namespace != cache_contract::SCHEMA
        || expected.cache_root.is_empty()
        || expected.producer_source.is_empty()
        || expected.analyses_tree.is_empty()
    {
        return Err(frame_hold("accepted_manifest"));
    }
    let inputs = &metadata.inputs;
    for (value, accepted, field) in [
        (&metadata.key, expected.fingerprint, "fingerprint"),
        (
            &inputs.analysis,
            expected.analysis_digest,
            "analysis_digest",
        ),
        (
            &inputs.configuration,
            expected.configuration_digest,
            "configuration_digest",
        ),
        (
            &inputs.toolchain,
            expected.toolchain_digest,
            "toolchain_digest",
        ),
        (
            &inputs.dependencies,
            expected.dependency_digest,
            "dependency_digest",
        ),
        (&native.hashes.entry, expected.entry_sha256, "entry_sha256"),
        (
            &native.hashes.payload,
            expected.payload_sha256,
            "payload_sha256",
        ),
        (
            &native.hashes.exports,
            expected.export_sha256,
            "export_sha256",
        ),
    ] {
        if parse_digest(value, field)? != accepted {
            return Err(frame_hold(field));
        }
    }
    // Authenticate the supplied model metadata too: a matching claimed file
    // hash must not accompany a different model/baseline/receipt tuple.
    // This is the cache contract's payload encoding; exports stay streamed.
    let payload_bytes =
        serde_json::to_vec(&(&metadata.model, &metadata.baseline, &metadata.receipt))
            .map_err(|_| frame_hold("payload_metadata"))?;
    if expected.payload_sha256 != Digest(Sha256::digest(payload_bytes).into()) {
        return Err(frame_hold("payload_metadata"));
    }
    // This is the digest of this program's logical source map, not the
    // analysis fingerprint, cache payload, or corpus-wide manifest. Its byte
    // definition is serde_json::to_vec(BTreeMap<logical_path, file_sha256>).
    let source_bytes =
        serde_json::to_vec(&inputs.files).map_err(|_| frame_hold("logical_source_map"))?;
    if expected.substrate_digest != Digest(Sha256::digest(source_bytes).into()) {
        return Err(frame_hold("substrate_digest"));
    }
    let entry = std::path::Path::new(&expected.cache_root)
        .join(&expected.namespace)
        .join(format!("{}.json", metadata.key));
    if entry != std::path::Path::new(&expected.entry_path) || inputs.program != expected.program.0 {
        return Err(frame_hold("program_entry"));
    }
    let pins = native.pins.as_ref().map_err(Clone::clone)?;
    if pins.role != ExecutionRole::CacheOnly
        || pins.program != expected.program
        || pins.toolchain_digest != expected.toolchain_digest
        || pins.dependency_digest != expected.dependency_digest
        || pins.launch_digest != expected.launch_digest
    {
        return Err(frame_hold("five_consumption_pins"));
    }
    let emission_configuration = native.emission_configuration?;
    let tcx = native.program.tcx;
    let functions: BTreeSet<_> = native
        .program
        .functions
        .iter()
        .map(|function| tcx.def_path_str(function.to_def_id()))
        .collect();
    let function_ids: FxHashSet<_> = native.program.functions.iter().copied().collect();
    if functions.len() != native.program.functions.len()
        || functions != metadata.functions.iter().cloned().collect()
        || function_ids != native.slots.fn_local_slots.keys().copied().collect()
    {
        return Err(inventory_hold());
    }
    let mut universe = BTreeMap::new();
    let mut local_model = BTreeMap::new();
    for (&function, slots) in &native.slots.fn_local_slots {
        for index in 0..slots.len() {
            let id = SlotId::from_usize(index);
            let descriptor = slots.slot(id);
            let SlotOwner::Local(local) = descriptor.owner else {
                return Err(inventory_hold());
            };
            let reference = SlotRef::Local(function, id);
            let canonical = local_key(tcx, function, local.as_usize(), descriptor.depth);
            if universe.insert(canonical, reference).is_some() {
                return Err(inventory_hold());
            }
            let subject = ModelSlot {
                owner: OwnerId(function.local_def_index.as_u32()),
                local: local.as_u32(),
                depth: descriptor.depth.checked_add(1).ok_or_else(inventory_hold)?,
            };
            let kind = match native.model.get(&reference).ok_or_else(inventory_hold)? {
                SlotKind::Owning => Kind::Owning,
                SlotKind::Ref => Kind::Ref,
                SlotKind::Raw => Kind::Raw,
            };
            if local_model.insert(subject, kind).is_some() {
                return Err(inventory_hold());
            }
        }
    }
    // Field keys participate in full cache/model validation even though this
    // tranche's ModelSlot consumer represents only function-local subjects.
    for index in 0..native.slots.field_slots.len() {
        let id = SlotId::from_usize(index);
        let descriptor = native.slots.field_slots.slot(id);
        let SlotOwner::Field(field) = descriptor.owner else {
            return Err(inventory_hold());
        };
        let key = field_key(tcx, field.struct_did, field.field_index, descriptor.depth);
        if universe.insert(key, SlotRef::Field(id)).is_some() {
            return Err(inventory_hold());
        }
    }
    if universe.keys().cloned().collect::<BTreeSet<_>>()
        != metadata.universe.iter().cloned().collect()
        || native.model.len() != universe.len()
    {
        return Err(inventory_hold());
    }
    for (key, reference) in universe {
        let label = match native.model.get(&reference).ok_or_else(inventory_hold)? {
            SlotKind::Owning => "owning",
            SlotKind::Ref => "ref",
            SlotKind::Raw => "raw",
        };
        if metadata.model.get(&key).map(String::as_str) != Some(label) {
            return Err(inventory_hold());
        }
    }
    Ok(AcceptedInputs {
        frame: Ok(expected.clone()),
        entry_accepted: Ok(true),
        model: Ok(local_model),
        required_bindings: native.required_bindings,
        bindings: Err(Missing {
            owner: EvidenceOwner::NativeIdentity,
            reason: MissingReason::Field("generation_recipe"),
        }),
        records: BTreeMap::new(),
        emission_configuration,
    })
}

fn frame_hold(field: &'static str) -> Missing {
    Missing {
        owner: EvidenceOwner::FrameQualification,
        reason: MissingReason::Frame(field),
    }
}
fn inventory_hold() -> Missing {
    Missing {
        owner: EvidenceOwner::NativeIdentity,
        reason: MissingReason::ModelInventory,
    }
}
fn parse_digest(value: &str, field: &'static str) -> Evidence<Digest> {
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(frame_hold(field));
    }
    let mut digest = [0; 32];
    for (index, byte) in digest.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
            .map_err(|_| frame_hold(field))?;
    }
    Ok(Digest(digest))
}

#[cfg(test)]
mod tests {
    use sha2::{Digest as _, Sha256};

    use super::*;
    use crate::{
        analyses::borrow_ownership::{
            cache_contract,
            origin_evidence::{
                FunctionEvidence, OriginAvailability, OriginEvidence, OriginMissing,
                OwnershipCorrespondence,
            },
            slot_key::{field_key, local_key},
            slots::{SlotId, SlotOwner},
        },
        bo_rewriter::ownership_fields::{
            OwnerId,
            emission::Kind,
            export::{ProgramId, SourceFrame},
            model_adapter::{ExecutionRole, ModelSlot},
        },
    };

    /// Metadata, hashes and model kinds are synthetic test premises. Only the
    /// source IDs/universe come from rustc; no sealed cache entry is created or
    /// read and the returned generation binding must remain unavailable.
    struct Fixture<'tcx> {
        expected: ModelFrame,
        metadata: Metadata,
        hashes: StreamHashes,
        actual: SemanticInputs,
        pins: Evidence<ConsumptionPins>,
        program: RustProgram<'tcx>,
        slots: CrateSlots,
        model: FxHashMap<SlotRef, SlotKind>,
    }
    impl<'tcx> Fixture<'tcx> {
        fn inputs(&self) -> NativeCacheInputs<'_, 'tcx> {
            NativeCacheInputs {
                metadata: &self.metadata,
                hashes: &self.hashes,
                actual_semantic_inputs: &self.actual,
                pins: &self.pins,
                program: &self.program,
                slots: &self.slots,
                model: &self.model,
                emission_configuration: Ok(Digest([12; 32])),
                required_bindings: Ok(BTreeSet::new()),
            }
        }

        fn bind(&self) -> Evidence<AcceptedInputs> {
            bind(&self.expected, self.inputs())
        }
    }
    fn with_fixture(check: impl FnOnce(Fixture<'_>) + Send + Sync) {
        ::utils::compilation::run_compiler_on_input(
            ::utils::compilation::str_to_input(
                "#![allow(dead_code, unused_variables)] struct Holder { p: *mut i32 } pub fn f(p: *mut *mut i32, q: *mut i32) {}",
            ),
            |tcx| {
                let program = crate::bo_rewriter::collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let actual = SemanticInputs {
                    program: "synthetic-native-cache-binding".into(),
                    files: BTreeMap::from([("synthetic.rs".into(), "11".repeat(32))]),
                    analysis: "01".repeat(32), toolchain: "02".repeat(32),
                    dependencies: "03".repeat(32), configuration: "04".repeat(32),
                };
                let key = cache_contract::semantic_key(&actual).unwrap();
                let mut model = FxHashMap::default();
                let mut rows = BTreeMap::new();
                for (&function, universe) in &slots.fn_local_slots {
                    for index in 0..universe.len() {
                        let id = SlotId::from_usize(index);
                        let slot = universe.slot(id);
                        let SlotOwner::Local(local) = slot.owner else { unreachable!() };
                        let (kind, label) = match (local.as_u32(), slot.depth) {
                            (1, 0) => (SlotKind::Owning, "owning"),
                            (1, 1) => (SlotKind::Ref, "ref"),
                            _ => (SlotKind::Raw, "raw"),
                        };
                        model.insert(SlotRef::Local(function, id), kind);
                        rows.insert(local_key(tcx, function, local.as_usize(), slot.depth), label.into());
                    }
                }
                for index in 0..slots.field_slots.len() {
                    let id = SlotId::from_usize(index);
                    let slot = slots.field_slots.slot(id);
                    let SlotOwner::Field(field) = slot.owner else { unreachable!() };
                    model.insert(SlotRef::Field(id), SlotKind::Raw);
                    rows.insert(field_key(tcx, field.struct_did, field.field_index, slot.depth), "raw".into());
                }
                let functions: Vec<_> = program.functions.iter()
                    .map(|function| tcx.def_path_str(function.to_def_id())).collect();
                let origin = OriginEvidence {
                    functions: functions.iter().map(|function| FunctionEvidence {
                        function: function.clone(), signature_slots: vec![],
                        value_flows: OriginAvailability::Missing(OriginMissing::NativeFlowsNotAvailable),
                        storage_aliases: OriginAvailability::Missing(OriginMissing::NativeFlowsNotAvailable),
                        native_unknown_targets: OriginAvailability::Missing(OriginMissing::NativeFlowsNotAvailable),
                        no_borrow_origin: vec![], occurrences: vec![],
                        ownership: OwnershipCorrespondence {
                            versions: OriginAvailability::Missing(OriginMissing::OwnershipVersionsNotSupplied),
                            equations: OriginAvailability::Missing(OriginMissing::OwnershipEquationsNotExported),
                            consumes: OriginAvailability::Missing(OriginMissing::OwnershipConsumesNotRecorded),
                            terminals: OriginAvailability::Missing(OriginMissing::OwnershipTerminalsNotRecorded),
                            boundary_substitutions: OriginAvailability::Missing(OriginMissing::OwnershipBoundarySubstitutionsNotRecorded),
                            call_arg_registrations: OriginAvailability::Missing(OriginMissing::CallArgRegistrationsNotRecorded),
                            equation_valuation_join: OriginMissing::EquationValuationJoinNotRecorded,
                            origin_closure: OriginMissing::OriginClosureNotComputed,
                            boundary_terminal_roster: OriginMissing::IndependentSlotOwnershipJoinNotRecorded,
                            dynamic_epochs: OriginMissing::DynamicEpochNotRepresented,
                            partner_free: OriginMissing::PartnerFreeCorrespondenceNotExported,
                            conservation: OriginMissing::ConservationNotProved,
                        },
                    }).collect(),
                    licensing: None,
                    reader_replay: None,
                    stack_entry_final: None,
                };
                let metadata = Metadata {
                    schema: cache_contract::SCHEMA.into(), key: key.clone(), inputs: actual.clone(),
                    functions, universe: rows.keys().cloned().collect(), baseline: rows.clone(), model: rows,
                    receipt: "status=ok\ndata=true".into(), origin: cache_contract::stream::OriginSource::Evidence {
                        evidence: Box::new(origin), present: Default::default(),
                    },
                };
                metadata.validate_meta().unwrap();
                let payload_digest = Sha256::digest(serde_json::to_vec(
                    &(&metadata.model, &metadata.baseline, &metadata.receipt),
                ).unwrap());
                let payload_hex = format!("{payload_digest:x}");
                let fingerprint = Digest(std::array::from_fn(|index| u8::from_str_radix(&key[index*2..index*2+2], 16).unwrap()));
                let expected = ModelFrame {
                    source_frame: SourceFrame::L01DoublePrime,
                    producer_source: "synthetic-producer".into(), analyses_tree: "synthetic-analysis-tree".into(),
                    analysis_digest: Digest([1; 32]), configuration_digest: Digest([4; 32]),
                    // Exact canonical logical-source map, separate from the grant manifest.
                    substrate_digest: Digest(Sha256::digest(serde_json::to_vec(&actual.files).unwrap()).into()),
                    manifest_digest: Digest([5; 32]), program: ProgramId(actual.program.clone()), fingerprint,
                    cache_root: "/synthetic-cache-never-opened".into(), namespace: cache_contract::SCHEMA.into(),
                    entry_path: format!("/synthetic-cache-never-opened/{}/{key}.json", cache_contract::SCHEMA),
                    entry_sha256: Digest([6; 32]), payload_sha256: Digest(payload_digest.into()), export_sha256: Digest([8; 32]),
                    toolchain_digest: Digest([2; 32]), dependency_digest: Digest([3; 32]), launch_digest: Digest([9; 32]),
                };
                let pins = Ok(ConsumptionPins { role: ExecutionRole::CacheOnly,
                    toolchain_digest: expected.toolchain_digest, dependency_digest: expected.dependency_digest,
                    launch_digest: expected.launch_digest, program: expected.program.clone(),
                });
                let hashes = StreamHashes { entry: "06".repeat(32), payload: payload_hex, exports: "08".repeat(32) };
                check(Fixture { expected, metadata, hashes, actual, pins, program, slots, model });
            },
        ).expect("native binder fixture compiles; no cache is accessed");
    }

    #[test]
    fn native_cache_binding_preserves_kinds_depth_and_missing_generation() {
        with_fixture(|fixture| {
            let bound = fixture
                .bind()
                .expect("validated in-memory cache and native model agree");
            assert_eq!(bound.frame.as_ref().unwrap(), &fixture.expected);
            assert_eq!(bound.entry_accepted, Ok(true));
            let owner = OwnerId(fixture.program.functions[0].local_def_index.as_u32());
            let model = bound.model.as_ref().unwrap();
            assert_eq!(
                model.len(),
                3,
                "field slots must not impersonate local slots"
            );
            assert_eq!(
                model[&ModelSlot {
                    owner,
                    local: 1,
                    depth: 1
                }],
                Kind::Owning
            );
            assert_eq!(
                model[&ModelSlot {
                    owner,
                    local: 1,
                    depth: 2
                }],
                Kind::Ref
            );
            assert_eq!(
                model[&ModelSlot {
                    owner,
                    local: 2,
                    depth: 1
                }],
                Kind::Raw
            );
            assert_eq!(
                bound.bindings,
                Err(Missing {
                    owner: EvidenceOwner::NativeIdentity,
                    reason: MissingReason::Field("generation_recipe")
                })
            );
            assert!(
                bound.records.is_empty(),
                "no companion proof invented from a slot number"
            );
        });
    }

    #[test]
    fn native_cache_binding_rejects_hash_frame_pin_and_current_model_mismatches() {
        with_fixture(|mut fixture| {
            assert!(fixture.bind().is_ok());
            let hashes = fixture.hashes.clone();
            for field in 0..3 {
                fixture.hashes = hashes.clone();
                match field {
                    0 => fixture.hashes.entry = "ff".repeat(32),
                    1 => fixture.hashes.payload = "ff".repeat(32),
                    _ => fixture.hashes.exports = "ff".repeat(32),
                }
                assert!(fixture.bind().is_err(), "hash field {field}");
            }
            fixture.hashes = hashes;
            fixture.pins.as_mut().unwrap().role = ExecutionRole::Analysis;
            assert!(fixture.bind().is_err());
            fixture.pins.as_mut().unwrap().role = ExecutionRole::CacheOnly;
            fixture.actual.configuration = "fe".repeat(32);
            assert!(fixture.bind().is_err());
            fixture.actual = fixture.metadata.inputs.clone();
            let subject = *fixture
                .model
                .iter()
                .find(|(_, kind)| **kind == SlotKind::Owning)
                .unwrap()
                .0;
            fixture.model.insert(subject, SlotKind::Raw);
            assert!(
                fixture.bind().is_err(),
                "current consumed model must match the accepted rows"
            );
        });
    }

    #[test]
    fn native_cache_binding_rejects_stale_hash_with_coherently_changed_models() {
        with_fixture(|mut fixture| {
            assert!(fixture.bind().is_ok());
            let subject = *fixture
                .model
                .iter()
                .find(|(_, kind)| **kind == SlotKind::Owning)
                .unwrap()
                .0;
            fixture.model.insert(subject, SlotKind::Raw);
            let row = fixture
                .metadata
                .model
                .values_mut()
                .find(|kind| kind.as_str() == "owning")
                .unwrap();
            *row = "raw".into();
            // Both model representations agree and the semantic key is still
            // valid, but their bytes no longer match the accepted payload hash.
            fixture.metadata.validate_meta().unwrap();
            assert!(
                fixture.bind().is_err(),
                "a claimed hash cannot authenticate different payload bytes"
            );
        });
    }

    #[test]
    fn native_cache_binding_rejects_incomplete_native_universe_and_retains_absence() {
        with_fixture(|mut fixture| {
            let universe = fixture.metadata.universe.clone();
            fixture.metadata.universe.pop();
            assert!(fixture.bind().is_err());
            fixture.metadata.universe = universe;
            let field = *fixture
                .model
                .keys()
                .find(|slot| matches!(slot, SlotRef::Field(_)))
                .unwrap();
            fixture.model.remove(&field);
            assert!(
                fixture.bind().is_err(),
                "field inventory is checked even for a local-only consumer"
            );
            fixture.model.insert(field, SlotKind::Raw);
            let why = Missing {
                owner: EvidenceOwner::Emission,
                reason: MissingReason::Field("emission_configuration"),
            };
            let mut inputs = fixture.inputs();
            inputs.emission_configuration = Err(why.clone());
            assert_eq!(bind(&fixture.expected, inputs).unwrap_err(), why);
            let why = Missing {
                owner: EvidenceOwner::NativeIdentity,
                reason: MissingReason::Field("native_occurrence_inventory"),
            };
            let mut inputs = fixture.inputs();
            inputs.required_bindings = Err(why.clone());
            let bound = bind(&fixture.expected, inputs).unwrap();
            assert_eq!(bound.required_bindings, Err(why));
        });
    }
}
