//! Recording-only T2 demand evidence. This schema grants no ownership.

use super::{
    crate_slots::CrateSlots,
    export::{BoundaryRole, ProjKey, T2AssertKey},
    realloc::ReallocOutcome,
};
use crate::utils::rustc::RustProgram;

pub(crate) const SCHEMA: &str = "era5a-demand-evidence-v1";

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum LicensingDisposition {
    #[default]
    Deferred,
}

/// Ordinal within this capture, not a program/function or endpoint identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ConstructionId(pub(crate) u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct EpochId {
    pub(crate) construction: ConstructionId,
    pub(crate) ordinal: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct EventId {
    pub(crate) epoch: EpochId,
    pub(crate) ordinal: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum IdentityGap {
    SourceOperandUnavailable,
    UnsupportedCallShape,
}

/// The local/index numbers belong to the endpoint's original function/MIR,
/// not to its solver variable universe. Ordered projections are preserved.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum OperandIdentity {
    Place {
        local: u32,
        projections: Vec<ProjKey>,
    },
    Null,
    Missing(IdentityGap),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct EndpointKey {
    pub(crate) construction: ConstructionId,
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) role: BoundaryRole,
    pub(crate) realloc_outcome: Option<ReallocOutcome>,
    pub(crate) operand: OperandIdentity,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Endpoint {
    pub(crate) key: EndpointKey,
    /// In-process correlation only; neither field participates in EndpointKey.
    pub(crate) diagnostic_var: u32,
    pub(crate) diagnostic_selector_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum QueryPhase {
    SelectorSearch,
    Restoration,
    Materialization,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum QueryOutcome {
    Sat,
    Unsat,
    Unknown { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QueryEvent {
    pub(crate) id: EventId,
    pub(crate) phase: QueryPhase,
    /// Selected removal/restoration endpoint when this operation has one.
    pub(crate) candidate: Option<EndpointKey>,
    pub(crate) active: Vec<EndpointKey>,
    pub(crate) core_endpoints: Vec<EndpointKey>,
    /// Every mandatory label returned by this exact core, without family
    /// deduplication or a nearest-free/partner reconstruction.
    pub(crate) mandatory_core_labels: Vec<String>,
    pub(crate) outcome: QueryOutcome,
}

/// A terminal selector state, not a certificate of final borrow acceptance.
/// Unknown leaves dropped=None; it must not masquerade as proven retraction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FinalSelection {
    pub(crate) epoch: EpochId,
    pub(crate) dropped: Option<Vec<EndpointKey>>,
    pub(crate) outcome: QueryOutcome,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ConstructionEvidence {
    pub(crate) id: ConstructionId,
    pub(crate) endpoints: Vec<Endpoint>,
    pub(crate) queries: Vec<QueryEvent>,
    pub(crate) final_selections: Vec<FinalSelection>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct DemandEvidence {
    pub(crate) licensing: LicensingDisposition,
    pub(crate) constructions: Vec<ConstructionEvidence>,
}

/// Register the actual endpoint universe for this construction. Capture-off
/// returns no handle and performs no MIR/identity work.
pub(crate) fn begin_construction(
    program: &RustProgram<'_>,
    _slots: &CrateSlots,
    keys: &[T2AssertKey],
) -> Option<ConstructionId> {
    let mut id = None;
    super::export::record(|output| {
        let evidence = output
            .demand_evidence
            .get_or_insert_with(DemandEvidence::default);
        let construction = ConstructionId(
            u32::try_from(evidence.constructions.len()).expect("construction ordinal"),
        );
        let endpoints = keys
            .iter()
            .enumerate()
            .map(|(index, key)| Endpoint {
                key: EndpointKey {
                    construction,
                    function: key.function_path.clone(),
                    block: key.location.block,
                    statement: key.location.statement_index,
                    role: key.role,
                    realloc_outcome: key.realloc_outcome,
                    operand: source_operand(program, key),
                },
                diagnostic_var: key.var.as_u32(),
                diagnostic_selector_index: index,
            })
            .collect();
        evidence.constructions.push(ConstructionEvidence {
            id: construction,
            endpoints,
            queries: Vec::new(),
            final_selections: Vec::new(),
        });
        id = Some(construction);
    });
    id
}

fn source_operand(program: &RustProgram<'_>, key: &T2AssertKey) -> OperandIdentity {
    use rustc_middle::mir::{BasicBlock, Operand};

    use super::export::PlaceKey;
    if !program.functions.contains(&key.fn_did) {
        return OperandIdentity::Missing(IdentityGap::UnsupportedCallShape);
    }
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(key.fn_did)
        .borrow();
    let Some(block) = body
        .basic_blocks
        .get(BasicBlock::from_u32(key.location.block))
    else {
        return OperandIdentity::Missing(IdentityGap::UnsupportedCallShape);
    };
    if key.location.statement_index != block.statements.len() {
        return OperandIdentity::Missing(IdentityGap::UnsupportedCallShape);
    }
    let rustc_middle::mir::TerminatorKind::Call {
        destination, args, ..
    } = &block.terminator().kind
    else {
        return OperandIdentity::Missing(IdentityGap::UnsupportedCallShape);
    };
    let place = match key.role {
        BoundaryRole::Source => Some(PlaceKey::from_place(*destination)),
        BoundaryRole::Sink => args
            .first()
            .and_then(|arg| arg.node.place())
            .map(PlaceKey::from_place),
    };
    if let Some(place) = place {
        return OperandIdentity::Place {
            local: place.local.as_u32(),
            projections: place.proj,
        };
    }
    if let Some(argument) = args.first()
        && matches!(argument.node, Operand::Constant(_))
        && super::source_events::operand_is_null(&argument.node, &[], program.tcx)
    {
        return OperandIdentity::Null;
    }
    OperandIdentity::Missing(IdentityGap::SourceOperandUnavailable)
}

pub(crate) fn endpoint_keys(id: ConstructionId) -> Option<Vec<EndpointKey>> {
    let mut keys = None;
    super::export::record(|output| {
        keys = output
            .demand_evidence
            .as_ref()
            .and_then(|evidence| evidence.constructions.iter().find(|unit| unit.id == id))
            .map(|unit| {
                unit.endpoints
                    .iter()
                    .map(|endpoint| endpoint.key.clone())
                    .collect()
            });
    });
    keys
}

pub(crate) fn record_query(event: QueryEvent) {
    super::export::record(|output| {
        let unit = output
            .demand_evidence
            .as_mut()
            .and_then(|evidence| {
                evidence
                    .constructions
                    .iter_mut()
                    .find(|unit| unit.id == event.id.epoch.construction)
            })
            .expect("query belongs to its bound construction");
        assert!(
            !unit.queries.iter().any(|previous| previous.id == event.id),
            "duplicate demand query identity"
        );
        unit.queries.push(event);
    });
}

pub(crate) fn mark_candidate(id: EventId, candidate: EndpointKey) {
    super::export::record(|output| {
        let unit = output
            .demand_evidence
            .as_mut()
            .and_then(|evidence| {
                evidence
                    .constructions
                    .iter_mut()
                    .find(|unit| unit.id == id.epoch.construction)
            })
            .expect("candidate belongs to its bound construction");
        let query = unit
            .queries
            .iter_mut()
            .find(|query| query.id == id)
            .expect("actual query before candidate selection");
        query.candidate = Some(candidate);
    });
}

pub(crate) fn record_final_selection(selection: FinalSelection) {
    super::export::record(|output| {
        let unit = output
            .demand_evidence
            .as_mut()
            .and_then(|evidence| {
                evidence
                    .constructions
                    .iter_mut()
                    .find(|unit| unit.id == selection.epoch.construction)
            })
            .expect("final selection belongs to its bound construction");
        if let Some(previous) = unit
            .final_selections
            .iter_mut()
            .find(|previous| previous.epoch == selection.epoch)
        {
            *previous = selection;
        } else {
            unit.final_selections.push(selection);
        }
    });
}

impl DemandEvidence {
    /// Structural completeness only. No SAT result, source path, or retained
    /// endpoint is promoted into an ownership/licensing proof by validation.
    pub(crate) fn validate(&self) -> Result<(), String> {
        use std::collections::{BTreeMap, BTreeSet};
        if self.licensing != LicensingDisposition::Deferred {
            return Err("licensing must remain deferred".to_owned());
        }
        let mut constructions = BTreeSet::new();
        for unit in &self.constructions {
            if !constructions.insert(unit.id) {
                return Err("duplicate construction".to_owned());
            }
            let endpoints: BTreeSet<_> = unit.endpoints.iter().map(|row| row.key.clone()).collect();
            if endpoints.len() != unit.endpoints.len() {
                return Err("duplicate endpoint identity".to_owned());
            }
            let mut diagnostic_indices = BTreeSet::new();
            for endpoint in &unit.endpoints {
                if endpoint.key.construction != unit.id {
                    return Err("endpoint construction mismatch".to_owned());
                }
                if !diagnostic_indices.insert(endpoint.diagnostic_selector_index) {
                    return Err("duplicate diagnostic selector index".to_owned());
                }
            }
            if diagnostic_indices
                .iter()
                .copied()
                .ne(0..unit.endpoints.len())
            {
                return Err("incomplete diagnostic selector map".to_owned());
            }
            let validate_keys = |keys: &[EndpointKey]| -> Result<(), String> {
                let unique: BTreeSet<_> = keys.iter().collect();
                if unique.len() != keys.len() {
                    return Err("duplicate endpoint reference".to_owned());
                }
                if keys.iter().any(|key| !endpoints.contains(key)) {
                    return Err("dangling endpoint reference".to_owned());
                }
                Ok(())
            };
            let mut events = BTreeSet::new();
            let mut epochs = BTreeMap::<EpochId, BTreeSet<u32>>::new();
            for event in &unit.queries {
                if event.id.epoch.construction != unit.id {
                    return Err("query construction mismatch".to_owned());
                }
                if !events.insert(event.id) {
                    return Err("duplicate query event".to_owned());
                }
                epochs
                    .entry(event.id.epoch)
                    .or_default()
                    .insert(event.id.ordinal);
                validate_keys(&event.active)?;
                validate_keys(&event.core_endpoints)?;
                if event
                    .core_endpoints
                    .iter()
                    .any(|key| !event.active.contains(key))
                {
                    return Err("core endpoint was not active".to_owned());
                }
                if let Some(candidate) = &event.candidate {
                    if !endpoints.contains(candidate) || !event.active.contains(candidate) {
                        return Err("dangling or inactive candidate".to_owned());
                    }
                }
                match event.phase {
                    QueryPhase::SelectorSearch
                        if event.candidate.is_some()
                            && (event.outcome != QueryOutcome::Unsat
                                || !event
                                    .core_endpoints
                                    .contains(event.candidate.as_ref().unwrap())) =>
                    {
                        return Err("removal candidate lacks its UNSAT core".to_owned());
                    }
                    QueryPhase::Restoration if event.candidate.is_none() => {
                        return Err("restoration candidate missing".to_owned());
                    }
                    QueryPhase::Materialization if event.candidate.is_some() => {
                        return Err("materialization has no removal candidate".to_owned());
                    }
                    _ => {}
                }
                if event.outcome != QueryOutcome::Unsat
                    && (!event.core_endpoints.is_empty() || !event.mandatory_core_labels.is_empty())
                {
                    return Err("non-UNSAT query carries a core".to_owned());
                }
                if let QueryOutcome::Unknown { reason } = &event.outcome
                    && reason.is_empty()
                {
                    return Err("Unknown query reason missing".to_owned());
                }
                let labels: BTreeSet<_> = event.mandatory_core_labels.iter().collect();
                if labels.len() != event.mandatory_core_labels.len() {
                    return Err("duplicate mandatory core label".to_owned());
                }
            }
            for ordinals in epochs.values() {
                if ordinals
                    .iter()
                    .copied()
                    .ne(0..u32::try_from(ordinals.len()).map_err(|_| "event count overflow")?)
                {
                    return Err("missing query event ordinal".to_owned());
                }
            }
            let mut finals = BTreeSet::new();
            for final_state in &unit.final_selections {
                if final_state.epoch.construction != unit.id
                    || !epochs.contains_key(&final_state.epoch)
                {
                    return Err("dangling final epoch".to_owned());
                }
                if !finals.insert(final_state.epoch) {
                    return Err("duplicate final epoch".to_owned());
                }
                let unknown = unit.queries.iter().find(|query| {
                    query.id.epoch == final_state.epoch
                        && matches!(query.outcome, QueryOutcome::Unknown { .. })
                });
                if let Some(query) = unknown {
                    if final_state.outcome != query.outcome
                        || final_state.dropped.is_some()
                        || unit.queries.iter().any(|later| {
                            later.id.epoch == query.id.epoch && later.id.ordinal > query.id.ordinal
                        })
                    {
                        return Err(
                            "Unknown query must terminate its epoch without success".to_owned()
                        );
                    }
                } else if matches!(final_state.outcome, QueryOutcome::Unknown { .. }) {
                    return Err("Unknown terminal has no actual query witness".to_owned());
                }
                match (&final_state.outcome, &final_state.dropped) {
                    (QueryOutcome::Sat, Some(dropped)) => validate_keys(dropped)?,
                    (QueryOutcome::Unsat, None) => {}
                    (QueryOutcome::Unknown { reason }, None) if !reason.is_empty() => {}
                    _ => {
                        return Err(
                            "incomplete/Unknown selection cannot carry completed dropped keys"
                                .to_owned(),
                        );
                    }
                }
            }
            if finals != epochs.keys().copied().collect() {
                return Err("query epoch has no terminal selector state".to_owned());
            }
        }
        Ok(())
    }

    pub(crate) fn canonical_json(&self) -> Result<String, String> {
        use serde_json::json;
        self.validate()?;
        let mut units = self.constructions.iter().collect::<Vec<_>>();
        units.sort_by_key(|unit| unit.id);
        let units = units.into_iter().map(|unit| {
            let mut endpoints = unit.endpoints.iter().collect::<Vec<_>>();
            endpoints.sort_by(|left, right| left.key.cmp(&right.key));
            let mut queries = unit.queries.iter().collect::<Vec<_>>();
            queries.sort_by_key(|query| query.id);
            let mut finals = unit.final_selections.iter().collect::<Vec<_>>();
            finals.sort_by_key(|state| state.epoch);
            json!({
                "construction": unit.id.0,
                "endpoints": endpoints.into_iter().map(|endpoint| json!({
                    "identity": endpoint_json(&endpoint.key),
                    "diagnostic_labels": { "var": endpoint.diagnostic_var.to_string(),
                        "selector_index": endpoint.diagnostic_selector_index.to_string() }
                })).collect::<Vec<_>>(),
                "queries": queries.into_iter().map(|query| {
                    let mut labels = query.mandatory_core_labels.clone(); labels.sort();
                    json!({ "construction": query.id.epoch.construction.0, "epoch": query.id.epoch.ordinal,
                        "event": query.id.ordinal, "phase": match query.phase {
                            QueryPhase::SelectorSearch => "selector-search", QueryPhase::Restoration => "restoration",
                            QueryPhase::Materialization => "materialization" },
                        "candidate": query.candidate.as_ref().map(endpoint_json),
                        "active": endpoint_list_json(&query.active), "core_endpoints": endpoint_list_json(&query.core_endpoints),
                        "mandatory_core_labels": labels, "outcome": outcome_json(&query.outcome) })
                }).collect::<Vec<_>>(),
                "final_selections": finals.into_iter().map(|state| json!({
                    "construction": state.epoch.construction.0, "epoch": state.epoch.ordinal,
                    "dropped": state.dropped.as_ref().map(|keys| endpoint_list_json(keys)),
                    "outcome": outcome_json(&state.outcome)
                })).collect::<Vec<_>>()
            })
        }).collect::<Vec<_>>();
        serde_json::to_string(&json!({ "schema": SCHEMA, "licensing": "deferred",
            "evidence_role": "recording-only", "constructions": units }))
        .map_err(|error| error.to_string())
    }
}

fn outcome_json(outcome: &QueryOutcome) -> serde_json::Value {
    match outcome {
        QueryOutcome::Sat => serde_json::json!({ "state": "sat" }),
        QueryOutcome::Unsat => serde_json::json!({ "state": "unsat" }),
        QueryOutcome::Unknown { reason } => {
            serde_json::json!({ "state": "unknown", "reason": reason })
        }
    }
}

fn endpoint_list_json(keys: &[EndpointKey]) -> Vec<serde_json::Value> {
    let mut keys = keys.iter().collect::<Vec<_>>();
    keys.sort();
    keys.into_iter().map(endpoint_json).collect()
}

fn endpoint_json(key: &EndpointKey) -> serde_json::Value {
    use serde_json::json;
    let operand = match &key.operand {
        OperandIdentity::Null => json!({ "state": "null" }),
        OperandIdentity::Missing(reason) => json!({ "state": "missing", "reason": match reason {
            IdentityGap::SourceOperandUnavailable => "source-operand-unavailable",
            IdentityGap::UnsupportedCallShape => "unsupported-call-shape" } }),
        OperandIdentity::Place { local, projections } => json!({ "state": "place", "local": local,
            "projections": projections.iter().map(|projection| match projection {
                ProjKey::Deref => json!({ "kind": "deref" }),
                ProjKey::Field(field) => json!({ "kind": "field", "field": field }),
                ProjKey::Index(local) => json!({ "kind": "index", "local": local }),
                ProjKey::ConstantIndex { offset, min_length, from_end } => json!({ "kind": "constant-index", "offset": offset, "min_length": min_length, "from_end": from_end }),
                ProjKey::Subslice { from, to, from_end } => json!({ "kind": "subslice", "from": from, "to": to, "from_end": from_end }),
                ProjKey::Downcast(variant) => json!({ "kind": "downcast", "variant": variant }),
                ProjKey::OpaqueCast => json!({ "kind": "opaque-cast" }),
                ProjKey::Subtype => json!({ "kind": "subtype" }),
                ProjKey::UnwrapUnsafeBinder => json!({ "kind": "unwrap-unsafe-binder" }),
            }).collect::<Vec<_>>() }),
    };
    json!({ "construction": key.construction.0, "function": key.function, "block": key.block,
        "statement": key.statement, "role": match key.role { BoundaryRole::Source => "source", BoundaryRole::Sink => "sink" },
        "realloc_outcome": key.realloc_outcome.map(|outcome| match outcome { ReallocOutcome::Success => "success", ReallocOutcome::Failure => "failure" }),
        "operand": operand })
}

#[cfg(test)]
mod tests;
