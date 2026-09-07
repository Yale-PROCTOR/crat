//! Canonical transport of existing origin evidence, not ownership licensing.
//! Native value relations are already closed and can include folded storage
//! paths. Their presence is never an ownership-transfer or dynamic-epoch proof.

use std::collections::BTreeSet;

use rustc_index::bit_set::SparseBitMatrix;
use rustc_middle::mir::{Body, Operand, Place, RETURN_PLACE, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::CrateSlots,
    export::BoExport,
    origin_flow::NativeOriginSummary,
    origin_summary::{OriginSlot, OriginSummaries, SignatureRoot, SignatureSlot},
    resolve::{ResolvedSlot, resolve_place},
    slot_key,
    slots::SlotOwner,
};
use crate::{
    analyses::mir::{CallKind, TerminatorExt},
    utils::rustc::RustProgram,
};

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum OriginMissing {
    NativeFlowsNotAvailable,
    OriginSummaryNotAvailable,
    KindSlotUnmapped,
    SourceOperandNotRepresented,
    OwnershipVersionsNotSupplied,
    OwnershipEquationsNotExported,
    DynamicEpochNotRepresented,
    PartnerFreeCorrespondenceNotExported,
    ConservationNotProved,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(tag = "state", content = "value", rename_all = "kebab-case")]
pub(crate) enum OriginAvailability<T> {
    Present(T),
    Missing(OriginMissing),
}

/// The root and path remain distinct even when a field maps to a global kind
/// slot. Canonical strings use the existing BO slot-key convention.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct SignatureKey {
    pub(crate) root: String,
    pub(crate) root_dereferences: u8,
    pub(crate) field: Option<String>,
    pub(crate) depth: u8,
    pub(crate) kind_slot: OriginAvailability<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct OriginRelation {
    pub(crate) source: SignatureKey,
    pub(crate) target: SignatureKey,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct SourceSite {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum OccurrenceKind {
    Assignment,
    Call,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", content = "target", rename_all = "kebab-case")]
pub(crate) enum SourceCallee {
    Local(String),
    ForeignC(String),
    RustLibrary(String),
    Indirect,
    Dynamic,
}

/// Original MIR occurrence only; no equation or causal path is inferred from
/// a coincident site. Unsupported operands stay explicit instead of disappearing.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct SourceOccurrence {
    pub(crate) site: SourceSite,
    pub(crate) kind: OccurrenceKind,
    pub(crate) callee: Option<SourceCallee>,
    pub(crate) destination: OriginAvailability<String>,
    pub(crate) arguments: Vec<OriginAvailability<String>>,
}

/// A supplied E-R2 emission occurrence. Var numbers are run-local diagnostics,
/// never stable identity, generation identity, equations, or conservation evidence.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct OwnershipVersionOccurrence {
    pub(crate) site: SourceSite,
    pub(crate) local: String,
    pub(crate) diagnostic_use_var: Option<u32>,
    pub(crate) diagnostic_def_var: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct OwnershipCorrespondence {
    pub(crate) versions: OriginAvailability<Vec<OwnershipVersionOccurrence>>,
    pub(crate) equations: OriginMissing,
    pub(crate) dynamic_epochs: OriginMissing,
    pub(crate) partner_free: OriginMissing,
    pub(crate) conservation: OriginMissing,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct FunctionEvidence {
    pub(crate) function: String,
    pub(crate) signature_slots: Vec<SignatureKey>,
    pub(crate) value_flows: OriginAvailability<Vec<OriginRelation>>,
    pub(crate) storage_aliases: OriginAvailability<Vec<OriginRelation>>,
    pub(crate) native_unknown_targets: OriginAvailability<Vec<SignatureKey>>,
    /// MAY no-borrow-origin membership. Fresh ownership and an opaque return
    /// both qualify, and a known incoming origin can coexist with this flag.
    pub(crate) no_borrow_origin: Vec<SignatureKey>,
    pub(crate) occurrences: Vec<SourceOccurrence>,
    pub(crate) ownership: OwnershipCorrespondence,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct OriginEvidence {
    pub(crate) functions: Vec<FunctionEvidence>,
}

fn signature_key(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    function: LocalDefId,
    signature: SignatureSlot,
) -> SignatureKey {
    let tcx = program.tcx;
    let root = match signature.place.root {
        SignatureRoot::Return => RETURN_PLACE,
        SignatureRoot::Arg(local) => local,
    };
    let field = signature
        .place
        .field
        .map(|field| slot_key::field_key(tcx, field.struct_did, field.field_index, 0));
    let kind_slot = if let Some(field) = signature.place.field {
        slots
            .field_slots
            .slot_for_field_depth(field, signature.depth)
            .map(|_| slot_key::field_key(tcx, field.struct_did, field.field_index, signature.depth))
    } else {
        signature
            .place
            .deref_depth
            .checked_add(signature.depth)
            .and_then(|depth| {
                slots
                    .fn_local_slots
                    .get(&function)?
                    .slot_for_local_depth(root, depth)
                    .map(|_| slot_key::local_key(tcx, function, root.as_usize(), depth))
            })
    };
    SignatureKey {
        root: slot_key::local_key(tcx, function, root.as_usize(), 0),
        root_dereferences: signature.place.deref_depth,
        field,
        depth: signature.depth,
        kind_slot: kind_slot
            .map(OriginAvailability::Present)
            .unwrap_or(OriginAvailability::Missing(OriginMissing::KindSlotUnmapped)),
    }
}

fn relations(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    function: LocalDefId,
    summary: &NativeOriginSummary,
    matrix: &SparseBitMatrix<OriginSlot, OriginSlot>,
) -> Vec<OriginRelation> {
    let mut rows = BTreeSet::new();
    for source in matrix.rows() {
        for target in matrix
            .row(source)
            .into_iter()
            .flat_map(|targets| targets.iter())
        {
            rows.insert(OriginRelation {
                source: signature_key(program, slots, function, summary.slots[source]),
                target: signature_key(program, slots, function, summary.slots[target]),
            });
        }
    }
    rows.into_iter().collect()
}

fn place_key<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    function: LocalDefId,
    body: &Body<'tcx>,
    place: Place<'tcx>,
) -> OriginAvailability<String> {
    let key = resolve_place(slots, function, body, place, 0, None).map(|resolved| {
        let descriptor = match resolved {
            ResolvedSlot::Local(id) => slots.fn_local_slots[&function].slot(id),
            ResolvedSlot::Field(id) => slots.field_slots.slot(id),
        };
        match descriptor.owner {
            SlotOwner::Local(local) => {
                slot_key::local_key(program.tcx, function, local.as_usize(), descriptor.depth)
            }
            SlotOwner::Field(field) => slot_key::field_key(
                program.tcx,
                field.struct_did,
                field.field_index,
                descriptor.depth,
            ),
        }
    });
    key.map(OriginAvailability::Present)
        .unwrap_or(OriginAvailability::Missing(
            OriginMissing::SourceOperandNotRepresented,
        ))
}

fn operand_key<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    function: LocalDefId,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> OriginAvailability<String> {
    operand
        .place()
        .map(|place| place_key(program, slots, function, body, place))
        .unwrap_or(OriginAvailability::Missing(
            OriginMissing::SourceOperandNotRepresented,
        ))
}

fn occurrences<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    function: LocalDefId,
) -> Vec<SourceOccurrence> {
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let name = program.tcx.def_path_str(function.to_def_id());
    let mut rows = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let site = |statement| SourceSite {
            function: name.clone(),
            block: block.as_u32(),
            statement,
        };
        for (index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(box (destination, value)) = &statement.kind else { continue };
            let operand =
                |operand: &Operand<'tcx>| operand_key(program, slots, function, &body, operand);
            // Syntactic inputs only. These rows do not assert that the origin
            // relation or an ownership equation was caused by this operation.
            let arguments = match value {
                Rvalue::Use(value)
                | Rvalue::Cast(_, value, _)
                | Rvalue::Repeat(value, _)
                | Rvalue::UnaryOp(_, value) => vec![operand(value)],
                Rvalue::CopyForDeref(place)
                | Rvalue::Ref(_, _, place)
                | Rvalue::RawPtr(_, place)
                | Rvalue::Discriminant(place)
                | Rvalue::Len(place) => vec![place_key(program, slots, function, &body, *place)],
                Rvalue::BinaryOp(_, values) => vec![operand(&values.0), operand(&values.1)],
                Rvalue::Aggregate(_, values) => values.iter().map(operand).collect(),
                // The unhandled expression's input mapping is unavailable;
                // do not report an empty-input certificate for it.
                _ => vec![OriginAvailability::Missing(
                    OriginMissing::SourceOperandNotRepresented,
                )],
            };
            rows.push(SourceOccurrence {
                site: site(index),
                kind: OccurrenceKind::Assignment,
                callee: None,
                destination: place_key(program, slots, function, &body, *destination),
                arguments,
            });
        }
        if let Some(call) = data.terminator().as_call(program.tcx) {
            let callee = match call.func {
                CallKind::FreeStanding(callee) | CallKind::Impl(callee) => {
                    SourceCallee::Local(program.tcx.def_path_str(callee.to_def_id()))
                }
                CallKind::LibC(name) => SourceCallee::ForeignC(name.to_string()),
                CallKind::RustLib(callee) => {
                    SourceCallee::RustLibrary(program.tcx.def_path_str(callee))
                }
                CallKind::Closure => SourceCallee::Indirect,
                CallKind::Dynamic => SourceCallee::Dynamic,
            };
            rows.push(SourceOccurrence {
                site: site(data.statements.len()),
                kind: OccurrenceKind::Call,
                callee: Some(callee),
                destination: place_key(program, slots, function, &body, call.destination),
                arguments: call
                    .args
                    .iter()
                    .map(|argument| operand_key(program, slots, function, &body, &argument.node))
                    .collect(),
            });
        }
    }
    rows.sort();
    rows
}

/// Transport only the supplied origin derivation and completed E-R2 capture.
/// Source occurrence enumeration performs no origin, ownership or alias inference.
pub(crate) fn collect(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    captured: Option<&BoExport>,
) -> OriginEvidence {
    use OriginAvailability::{Missing, Present};
    let mut functions = Vec::new();
    for &function in &program.functions {
        let name = program.tcx.def_path_str(function.to_def_id());
        let summary = origins.get(&function);
        let mut signature_slots: Vec<_> = summary
            .into_iter()
            .flat_map(|summary| summary.slots.iter())
            .map(|&slot| signature_key(program, slots, function, slot))
            .collect();
        signature_slots.sort();
        let mut no_borrow_origin: Vec<_> = summary
            .into_iter()
            .flat_map(|summary| summary.unknown.iter().map(|id| summary.slots[id]))
            .map(|slot| signature_key(program, slots, function, slot))
            .collect();
        no_borrow_origin.sort();
        // The fused OriginSummary.subset is deliberately not relabelled as
        // either native relation when its original matrices are unavailable.
        let native = summary.and_then(|_| origins.try_native_flows()?.get(&function));
        let (value_flows, storage_aliases, native_unknown_targets) = if let Some(native) = native {
            let native = &native.summary;
            let mut unknown: Vec<_> = native
                .unknown_targets
                .iter()
                .map(|id| signature_key(program, slots, function, native.slots[id]))
                .collect();
            unknown.sort();
            (
                Present(relations(
                    program,
                    slots,
                    function,
                    native,
                    &native.value_flows,
                )),
                Present(relations(
                    program,
                    slots,
                    function,
                    native,
                    &native.storage_aliases,
                )),
                Present(unknown),
            )
        } else {
            let why = if summary.is_some() {
                OriginMissing::NativeFlowsNotAvailable
            } else {
                OriginMissing::OriginSummaryNotAvailable
            };
            (Missing(why), Missing(why), Missing(why))
        };
        let versions = if let Some(captured) = captured {
            let mut rows: Vec<_> = captured
                .version_sites
                .iter()
                .filter(|site| site.fn_did == function)
                .map(|site| OwnershipVersionOccurrence {
                    site: SourceSite {
                        function: name.clone(),
                        block: site.location.block,
                        statement: site.location.statement_index,
                    },
                    local: slot_key::local_key(program.tcx, function, site.local.as_usize(), 0),
                    diagnostic_use_var: site.use_var.map(|var| var.as_u32()),
                    diagnostic_def_var: site.def_var.map(|var| var.as_u32()),
                })
                .collect();
            // Retain every supplied occurrence, including repeated source sites.
            rows.sort();
            Present(rows)
        } else {
            Missing(OriginMissing::OwnershipVersionsNotSupplied)
        };
        functions.push(FunctionEvidence {
            function: name,
            signature_slots,
            value_flows,
            storage_aliases,
            native_unknown_targets,
            no_borrow_origin,
            occurrences: occurrences(program, slots, function),
            ownership: OwnershipCorrespondence {
                versions,
                equations: OriginMissing::OwnershipEquationsNotExported,
                dynamic_epochs: OriginMissing::DynamicEpochNotRepresented,
                partner_free: OriginMissing::PartnerFreeCorrespondenceNotExported,
                conservation: OriginMissing::ConservationNotProved,
            },
        });
    }
    functions.sort_by(|a, b| a.function.cmp(&b.function));
    OriginEvidence { functions }
}

impl OriginEvidence {
    /// Canonical order is independent of input container order. No occurrence
    /// is deduplicated, and diagnostic Var numbers remain explicitly labelled.
    pub(crate) fn canonical_json(&self) -> String {
        let mut value = self.clone();
        value.functions.sort_by(|a, b| a.function.cmp(&b.function));
        for function in &mut value.functions {
            function.signature_slots.sort();
            function.no_borrow_origin.sort();
            function.occurrences.sort();
            for relation in [&mut function.value_flows, &mut function.storage_aliases] {
                if let OriginAvailability::Present(rows) = relation {
                    rows.sort();
                }
            }
            if let OriginAvailability::Present(rows) = &mut function.native_unknown_targets {
                rows.sort();
            }
            if let OriginAvailability::Present(rows) = &mut function.ownership.versions {
                rows.sort();
            }
        }
        serde_json::to_string(&value).expect("origin-evidence DTO serialization")
    }
}

#[cfg(test)]
mod tests;
