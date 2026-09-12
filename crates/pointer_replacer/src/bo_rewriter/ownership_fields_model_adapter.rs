//! R348 tranche 1: accepted model kind, independent of licensing certificates.
//! Pure preparation over typed inputs. Native integration must use the pinned
//! cache-only loader's CachedModel.model (not baseline_model or a TSV label),
//! verify closed entry/payload/export bytes, and supply exact session bindings.
//! This module neither reads a cache nor sets environment variables or solves.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey, OwnerId, SiteId,
    emission::{
        self, EmitHold, Emitted, Grant, GrantStatus, Kind, OwnCallFacts, OwnerInput, OwnerType,
    },
    export::{
        Digest, Evidence, EvidenceOwner, FactFamily, FactRef, GenerationRecipe, Missing,
        MissingReason, ProgramId, RecordKey, SourceFrame,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModelSlot {
    pub owner: OwnerId,
    pub local: u32,
    /// Pointer-slot depth, not the local's maximum type depth.
    pub depth: u8,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelFrame {
    pub source_frame: SourceFrame,
    pub producer_source: String,
    pub analyses_tree: String,
    pub analysis_digest: Digest,
    pub configuration_digest: Digest,
    pub substrate_digest: Digest,
    pub manifest_digest: Digest,
    pub program: ProgramId,
    pub fingerprint: Digest,
    pub cache_root: String,
    pub namespace: String,
    pub entry_path: String,
    pub entry_sha256: Digest,
    pub payload_sha256: Digest,
    pub export_sha256: Digest,
    pub toolchain_digest: Digest,
    pub dependency_digest: Digest,
    pub launch_digest: Digest,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionRole {
    CacheOnly,
    Analysis,
}
/// The five L01″ consumption pins. Real environment setup remains gated;
/// fixture tests supply this value without enabling cache consumption.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsumptionPins {
    pub role: ExecutionRole,
    pub toolchain_digest: Digest,
    pub dependency_digest: Digest,
    pub launch_digest: Digest,
    pub program: ProgramId,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub subject: ModelSlot,
    pub key: EvidenceKey,
    /// May cover a generated return/rebind only when the native transport
    /// producer proves that route. It does not create a new model Owning bit.
    pub generation_recipe: Evidence<FactRef<GenerationRecipe>>,
    pub transport: Evidence<EvidenceKey>,
}
/// A second accepted input source beside adapter::AcceptedInputs. No fabricated
/// era-5b DeclarationKey, guard, global scheme or certificate frame is needed.
#[derive(Clone, Debug)]
pub struct AcceptedInputs {
    pub frame: Evidence<ModelFrame>,
    pub entry_accepted: Evidence<bool>,
    pub model: Evidence<BTreeMap<ModelSlot, Kind>>,
    pub required_bindings: Evidence<BTreeSet<SiteId>>,
    pub bindings: Evidence<Vec<Binding>>,
    pub records: BTreeMap<RecordKey, FactFamily>,
    /// Target/helper/panic identity is separate from the solver configuration.
    pub emission_configuration: Digest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelKindReceipt {
    pub frame: ModelFrame,
    pub subject: ModelSlot,
    pub key: EvidenceKey,
}
#[derive(Clone, Debug)]
pub struct ModelGrant {
    pub grant: Grant,
    pub receipt: ModelKindReceipt,
}
#[derive(Debug)]
pub struct Prepared<'a> {
    inputs: &'a AcceptedInputs,
}

fn need<T>(value: &Evidence<T>) -> Evidence<&T> {
    value.as_ref().map_err(Clone::clone)
}
fn missing(owner: EvidenceOwner, name: &'static str) -> Missing {
    Missing {
        owner,
        reason: MissingReason::Field(name),
    }
}
fn frame_hold(name: &'static str) -> Missing {
    Missing {
        owner: EvidenceOwner::FrameQualification,
        reason: MissingReason::Frame(name),
    }
}

pub fn prepare<'a>(
    expected: &ModelFrame,
    inputs: &'a AcceptedInputs,
    pins: &Evidence<ConsumptionPins>,
) -> Evidence<Prepared<'a>> {
    let frame = need(&inputs.frame)?;
    let pins = need(pins)?;
    if frame != expected
        || frame.source_frame != SourceFrame::L01DoublePrime
        || frame.namespace != "era5a-model-cache-v1"
    {
        return Err(frame_hold("model_manifest"));
    }
    if pins.role != ExecutionRole::CacheOnly
        || pins.toolchain_digest != frame.toolchain_digest
        || pins.dependency_digest != frame.dependency_digest
        || pins.launch_digest != frame.launch_digest
        || pins.program != frame.program
    {
        return Err(frame_hold("five_consumption_pins"));
    }
    if !*need(&inputs.entry_accepted)? {
        return Err(missing(EvidenceOwner::AcceptedModel, "accepted_entry"));
    }
    need(&inputs.model)?;
    let required = need(&inputs.required_bindings)?;
    let mut sites = BTreeSet::new();
    for binding in need(&inputs.bindings)? {
        if !sites.insert(binding.key.site) || binding.subject.depth == 0 {
            return Err(Missing {
                owner: EvidenceOwner::NativeIdentity,
                reason: MissingReason::ModelInventory,
            });
        }
    }
    if &sites != required {
        return Err(Missing {
            owner: EvidenceOwner::NativeIdentity,
            reason: MissingReason::ModelInventory,
        });
    }
    Ok(Prepared { inputs })
}
impl Prepared<'_> {
    pub fn owning_grant(&self, subject: ModelSlot, site: SiteId) -> Evidence<ModelGrant> {
        let frame = need(&self.inputs.frame)?;
        let kind = *need(&self.inputs.model)?
            .get(&subject)
            .ok_or_else(|| missing(EvidenceOwner::AcceptedModel, "model.slot_kind"))?;
        if kind != Kind::Owning {
            return Err(Missing {
                owner: EvidenceOwner::AcceptedModel,
                reason: MissingReason::ModelNotOwning(kind),
            });
        }
        let binding = need(&self.inputs.bindings)?
            .iter()
            .find(|binding| binding.key.site == site)
            .ok_or_else(|| missing(EvidenceOwner::NativeIdentity, "model.occurrence"))?;
        let recipe = need(&binding.generation_recipe)?;
        if self.inputs.records.get(&recipe.record) != Some(&FactFamily::GenerationRecipe) {
            return Err(Missing {
                owner: EvidenceOwner::NativeIdentity,
                reason: MissingReason::Companion(FactFamily::GenerationRecipe),
            });
        }
        let transport = need(&binding.transport)?;
        if binding.subject != subject
            || subject.owner != site.owner
            || transport != &binding.key
            || binding.key.model != frame.entry_sha256.0
            || binding.key.configuration != self.inputs.emission_configuration.0
        {
            return Err(Missing {
                owner: EvidenceOwner::NativeIdentity,
                reason: MissingReason::Occurrence,
            });
        }
        Ok(ModelGrant {
            // Selected is the existing consumer's admitted-grant status. This
            // receipt explicitly names model-kind authority, not an era-5b
            // selected-and-validated certificate or a Raw→Owning overlay.
            grant: Grant {
                key: binding.key,
                kind: Kind::Owning,
                status: GrantStatus::Selected,
                transport: Some(*transport),
            },
            receipt: ModelKindReceipt {
                frame: frame.clone(),
                subject,
                key: binding.key,
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AllocationShape {
    Ordinary,
    FlexibleTail { expression: String },
}
#[derive(Clone, Debug)]
pub struct ShapeEvidence {
    pub key: EvidenceKey,
    pub shape: Evidence<AllocationShape>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiverHold {
    Evidence(Missing),
    FlexibleTail { expression: String },
    ConstructionUnmappable { depth: u8 },
    Consumer(EmitHold),
}
/// The model grants a kind; layout, initialization and P1′-E remain emission
/// obligations. In particular neither a flexible tail nor a depth-2 slot is
/// silently turned into an ordinary outer Box allocation.
pub fn receiver(
    grant: &ModelGrant,
    shape: &ShapeEvidence,
    call: &OwnCallFacts,
    name: &str,
    ty: &OwnerType,
    input: &OwnerInput,
) -> Result<Emitted, ReceiverHold> {
    if shape.key != grant.grant.key
        || grant.receipt.key != grant.grant.key
        || grant.grant.key.model != grant.receipt.frame.entry_sha256.0
    {
        return Err(ReceiverHold::Evidence(Missing {
            owner: EvidenceOwner::NativeIdentity,
            reason: MissingReason::Occurrence,
        }));
    }
    if grant.receipt.subject.depth != 1 {
        return Err(ReceiverHold::ConstructionUnmappable {
            depth: grant.receipt.subject.depth,
        });
    }
    match need(&shape.shape).map_err(ReceiverHold::Evidence)? {
        AllocationShape::FlexibleTail { expression } => {
            return Err(ReceiverHold::FlexibleTail {
                expression: expression.clone(),
            });
        }
        AllocationShape::Ordinary => {}
    }
    let permit = emission::admit_call(&grant.grant, call).map_err(ReceiverHold::Consumer)?;
    emission::receiver(&permit, name, ty, input).map_err(ReceiverHold::Consumer)
}
