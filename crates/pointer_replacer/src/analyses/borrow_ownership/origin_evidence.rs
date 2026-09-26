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
    OwnershipBoundarySubstitutionsNotRecorded,
    CallArgRegistrationsNotRecorded,
    OwnershipConsumesNotRecorded,
    OwnershipTerminalsNotRecorded,
    EquationValuationJoinNotRecorded,
    DynamicEpochNotRepresented,
    PartnerFreeCorrespondenceNotExported,
    ConservationNotProved,
    LicensingTransportNotComputed,
    IndependentOwnershipRosterNotRecorded,
    IndependentSlotOwnershipJoinNotRecorded,
    OriginClosureNotComputed,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
#[serde(tag = "state", content = "value", rename_all = "kebab-case")]
pub(crate) enum OriginAvailability<T> {
    Present(T),
    Missing(OriginMissing),
}

/// R342-1: the joint envelope is a strict superset of era-5a's. Era-5a wrote
/// the positions that now carry an availability as a bare `OriginMissing`,
/// before the tag existed, and those bytes decode as `Missing`. Only the
/// tagged form is ever written, so no era-5b entry depends on this arm.
impl<'de, T: serde::Deserialize<'de>> serde::Deserialize<'de> for OriginAvailability<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(serde::Deserialize)]
        #[serde(deny_unknown_fields)]
        #[serde(tag = "state", content = "value", rename_all = "kebab-case")]
        enum Tagged<T> {
            Present(T),
            Missing(OriginMissing),
        }
        #[derive(serde::Deserialize)]
        #[serde(deny_unknown_fields)]
        #[serde(untagged)]
        enum Wire<T> {
            Era5a(OriginMissing),
            Joint(Tagged<T>),
        }
        Ok(match Wire::<T>::deserialize(deserializer)? {
            Wire::Era5a(missing) | Wire::Joint(Tagged::Missing(missing)) => Self::Missing(missing),
            Wire::Joint(Tagged::Present(value)) => Self::Present(value),
        })
    }
}

/// The root and path remain distinct even when a field maps to a global kind
/// slot. Canonical strings use the existing BO slot-key convention.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct SignatureKey {
    pub(crate) root: String,
    pub(crate) root_dereferences: u8,
    pub(crate) field: Option<String>,
    pub(crate) depth: u8,
    pub(crate) kind_slot: OriginAvailability<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct OriginRelation {
    pub(crate) source: SignatureKey,
    pub(crate) target: SignatureKey,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
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
#[serde(deny_unknown_fields)]
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
#[serde(deny_unknown_fields)]
pub(crate) struct SourceOccurrence {
    pub(crate) site: SourceSite,
    pub(crate) kind: OccurrenceKind,
    pub(crate) callee: Option<SourceCallee>,
    pub(crate) destination: OriginAvailability<String>,
    pub(crate) arguments: Vec<OriginAvailability<String>>,
    pub(crate) syntax: super::ownership_access::Syntax,
}

/// A supplied E-R2 emission occurrence. Var numbers are run-local diagnostics,
/// never stable identity, generation identity, equations, or conservation evidence.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct OwnershipVersionOccurrence {
    pub(crate) site: SourceSite,
    pub(crate) local: String,
    pub(crate) diagnostic_use_var: Option<u32>,
    pub(crate) diagnostic_def_var: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct OwnershipCorrespondence {
    pub(crate) versions: OriginAvailability<Vec<OwnershipVersionOccurrence>>,
    pub(crate) equations: OriginAvailability<Vec<super::ownership_evidence::Equation>>,
    #[serde(default = "consumes_absent")]
    pub(crate) consumes: OriginAvailability<Vec<super::ownership_occurrence::Consumption>>,
    #[serde(default = "terminals_absent")]
    pub(crate) terminals: OriginAvailability<Vec<super::ownership_occurrence::Terminal>>,
    #[serde(default = "boundary_substitutions_absent")]
    pub(crate) boundary_substitutions:
        OriginAvailability<Vec<super::ownership_boundary::Substitution>>,
    #[serde(default = "call_arg_registrations_absent")]
    pub(crate) call_arg_registrations:
        OriginAvailability<Vec<super::ownership_boundary::CallArgRegistration>>,
    /// Equations identify constructions; legacy version/value capture does not.
    /// Equal diagnostic Vars across those streams never establish a join.
    #[serde(default = "equation_valuation_join_absent")]
    pub(crate) equation_valuation_join: OriginMissing,
    #[serde(default = "origin_closure_absent")]
    pub(crate) origin_closure: OriginMissing,
    /// The complete join from rewrite-slot occurrences to accepted ownership
    /// valuations remains pending. Modeled
    /// CFG/SSA/return rosters are separately recorded in licensing snapshots.
    #[serde(default = "boundary_terminal_roster_absent")]
    pub(crate) boundary_terminal_roster: OriginMissing,
    pub(crate) dynamic_epochs: OriginMissing,
    pub(crate) partner_free: OriginMissing,
    pub(crate) conservation: OriginMissing,
}

/// An era-5a entry does not carry the era-5b ownership positions at all. Their
/// absence is the same typed fact era-5b records when it has nothing to record,
/// so the two entries validate through one path.
fn consumes_absent() -> OriginAvailability<Vec<super::ownership_occurrence::Consumption>> {
    OriginAvailability::Missing(OriginMissing::OwnershipConsumesNotRecorded)
}
fn terminals_absent() -> OriginAvailability<Vec<super::ownership_occurrence::Terminal>> {
    OriginAvailability::Missing(OriginMissing::OwnershipTerminalsNotRecorded)
}
fn boundary_substitutions_absent()
-> OriginAvailability<Vec<super::ownership_boundary::Substitution>> {
    OriginAvailability::Missing(OriginMissing::OwnershipBoundarySubstitutionsNotRecorded)
}
fn call_arg_registrations_absent()
-> OriginAvailability<Vec<super::ownership_boundary::CallArgRegistration>> {
    OriginAvailability::Missing(OriginMissing::CallArgRegistrationsNotRecorded)
}
fn equation_valuation_join_absent() -> OriginMissing {
    OriginMissing::EquationValuationJoinNotRecorded
}
fn origin_closure_absent() -> OriginMissing {
    OriginMissing::OriginClosureNotComputed
}
fn boundary_terminal_roster_absent() -> OriginMissing {
    OriginMissing::IndependentSlotOwnershipJoinNotRecorded
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
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
#[serde(deny_unknown_fields)]
pub(crate) struct OriginEvidence {
    pub(crate) functions: Vec<FunctionEvidence>,
    pub(crate) licensing: Option<Vec<super::licensing::snapshot::Snapshot>>,
    pub(crate) reader_replay: Option<Vec<super::licensing::reader_replay::Receipt>>,
    pub(crate) stack_entry_final: Option<super::licensing::stack_export::Accepted>,
}

pub(crate) fn signature_key(
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

pub(crate) fn occurrences<'tcx>(
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
                syntax: super::ownership_access::assignment(*destination, value, program.tcx, {
                    let ty = destination.ty(&*body, program.tcx).ty;
                    ty.is_raw_ptr() || ty.is_ref() || ty.is_box()
                }),
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
                syntax: super::ownership_access::call(
                    call.destination,
                    call.args.iter().map(|arg| &arg.node),
                    program.tcx,
                ),
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
            function: name.clone(),
            signature_slots,
            value_flows,
            storage_aliases,
            native_unknown_targets,
            no_borrow_origin,
            occurrences: occurrences(program, slots, function),
            ownership: OwnershipCorrespondence {
                versions,
                equations: captured
                    .and_then(|capture| capture.ownership_equations.as_ref())
                    .map(|equations| {
                        Present(
                            equations
                                .iter()
                                .filter(|eq| {
                                    eq.point
                                        .function
                                        .as_deref()
                                        .is_none_or(|function| function == name)
                                })
                                .cloned()
                                .collect(),
                        )
                    })
                    .unwrap_or(Missing(OriginMissing::OwnershipEquationsNotExported)),
                equation_valuation_join: OriginMissing::EquationValuationJoinNotRecorded,
                origin_closure: OriginMissing::OriginClosureNotComputed,
                boundary_terminal_roster: OriginMissing::IndependentSlotOwnershipJoinNotRecorded,
                consumes: captured
                    .and_then(|capture| capture.ownership_consumes.as_ref())
                    .map(|rows| {
                        Present(
                            rows.iter()
                                .filter(|row| row.point.function.as_deref() == Some(name.as_str()))
                                .cloned()
                                .collect(),
                        )
                    })
                    .unwrap_or(Missing(OriginMissing::OwnershipConsumesNotRecorded)),
                terminals: captured
                    .and_then(|capture| capture.ownership_terminals.as_ref())
                    .map(|rows| {
                        Present(
                            rows.iter()
                                .filter(|row| row.point.function.as_deref() == Some(name.as_str()))
                                .cloned()
                                .collect(),
                        )
                    })
                    .unwrap_or(Missing(OriginMissing::OwnershipTerminalsNotRecorded)),
                boundary_substitutions: captured
                    .and_then(|capture| capture.ownership_boundary_substitutions.as_ref())
                    .map(|rows| {
                        Present(
                            rows.iter()
                                .filter(|row| row.point.function.as_deref() == Some(name.as_str()))
                                .cloned()
                                .collect(),
                        )
                    })
                    .unwrap_or(Missing(
                        OriginMissing::OwnershipBoundarySubstitutionsNotRecorded,
                    )),
                call_arg_registrations: captured
                    .and_then(|capture| capture.ownership_call_arg_registrations.as_ref())
                    .map(|rows| {
                        Present(
                            rows.iter()
                                .filter(|row| row.point.function.as_deref() == Some(name.as_str()))
                                .cloned()
                                .collect(),
                        )
                    })
                    .unwrap_or(Missing(OriginMissing::CallArgRegistrationsNotRecorded)),
                dynamic_epochs: OriginMissing::DynamicEpochNotRepresented,
                partner_free: OriginMissing::PartnerFreeCorrespondenceNotExported,
                conservation: OriginMissing::ConservationNotProved,
            },
        });
    }
    functions.sort_by(|a, b| a.function.cmp(&b.function));
    OriginEvidence {
        functions,
        licensing: captured.and_then(|capture| capture.ownership_licensing.clone()),
        reader_replay: captured.and_then(|capture| capture.reader_replay.clone()),
        stack_entry_final: captured.and_then(super::licensing::stack_export::collect),
    }
}

impl OriginEvidence {
    /// Whether this entry declares the era-5b ownership family — it does so by
    /// carrying any of its evidence. The equations are all-or-nothing across
    /// functions: an entry that carries them for some and not others is refused
    /// rather than read as era-5a. An era-5a entry carries none of the four and
    /// is validated by exactly the checks it was written under.
    pub(crate) fn declares_ownership_family(&self) -> Result<bool, String> {
        let mut present = 0;
        for function in &self.functions {
            match &function.ownership.equations {
                OriginAvailability::Present(_) => present += 1,
                OriginAvailability::Missing(OriginMissing::OwnershipEquationsNotExported) => {}
                _ => return Err("invalid ownership equation availability".into()),
            }
        }
        if present != 0 && present != self.functions.len() {
            return Err("ownership family declared for some functions and not others".into());
        }
        Ok(present != 0
            || self.licensing.is_some()
            || self.reader_replay.is_some()
            || self.stack_entry_final.is_some())
    }

    /// Canonical order is independent of input container order. No occurrence
    /// is deduplicated, and diagnostic Var numbers remain explicitly labelled.
    /// R471-3 (i): the canonically ordered clone, shared by the two accessors
    /// below so their orderings can never drift apart.
    fn canonicalized(&self) -> Self {
        let mut value = self.clone();
        value.functions.sort_by(|a, b| a.function.cmp(&b.function));
        if let Some(snapshots) = &mut value.licensing {
            snapshots.sort_by_key(|snapshot| snapshot.offset);
        }
        for function in &mut value.functions {
            Self::canonicalize_function(function);
        }
        value
    }

    pub(crate) fn canonical_json(&self) -> String {
        serde_json::to_string(&self.canonicalized()).expect("origin-evidence DTO serialization")
    }

    /// R471-3 (i): the canonical form as a `Value`, WITHOUT the multi-GiB
    /// intermediate `String`. `to_value` and `from_str` both build serde_json's
    /// key-sorted `Map`, so the bytes written from it are identical to those
    /// from `from_str(&canonical_json())` -- the cache contract is unchanged.
    pub(crate) fn canonical_value(&self) -> serde_json::Value {
        serde_json::to_value(self.canonicalized()).expect("origin-evidence DTO serialization")
    }

    /// R473-4 (deeper): emit a row vector without ever holding the whole
    /// vector's `Value`. `order` is a permutation (canonical) or `None` (held).
    fn write_rows<T: serde::Serialize>(
        w: &mut impl std::io::Write,
        rows: &[T],
        order: Option<&[usize]>,
    ) -> Result<(), String> {
        w.write_all(b"[").map_err(|e| e.to_string())?;
        let emit = |w: &mut dyn std::io::Write, index: usize, first: bool| -> Result<(), String> {
            if !first {
                w.write_all(b",").map_err(|e| e.to_string())?;
            }
            let value = serde_json::to_value(&rows[index]).map_err(|e| e.to_string())?;
            serde_json::to_writer(w, &value).map_err(|e| e.to_string())
        };
        match order {
            Some(order) => {
                for (n, &index) in order.iter().enumerate() {
                    emit(w, index, n == 0)?;
                }
            }
            None => {
                for index in 0..rows.len() {
                    emit(w, index, index == 0)?;
                }
            }
        }
        w.write_all(b"]").map_err(|e| e.to_string())?;
        Ok(())
    }

    /// Sorted index permutation, matching the stable `rows.sort()` the
    /// whole-value path used -- without cloning the rows.
    fn sorted_order<T: Ord>(rows: &[T]) -> Vec<usize> {
        let mut order: Vec<usize> = (0..rows.len()).collect();
        order.sort_by(|&a, &b| rows[a].cmp(&rows[b]));
        order
    }

    /// `{"state":"present","value":[..]}` / `{"state":"missing","value":..}`.
    /// "state" < "value", so this is already the sorted key order.
    fn write_availability<T: serde::Serialize + Ord>(
        w: &mut impl std::io::Write,
        availability: &OriginAvailability<Vec<T>>,
        sort: bool,
    ) -> Result<(), String> {
        match availability {
            OriginAvailability::Present(rows) => {
                w.write_all(b"{\"state\":\"present\",\"value\":")
                    .map_err(|e| e.to_string())?;
                let order = sort.then(|| Self::sorted_order(rows));
                Self::write_rows(w, rows, order.as_deref())?;
                w.write_all(b"}").map_err(|e| e.to_string())
            }
            OriginAvailability::Missing(_) => {
                let value = serde_json::to_value(availability).map_err(|e| e.to_string())?;
                serde_json::to_writer(w, &value).map_err(|e| e.to_string())
            }
        }
    }

    /// Availability whose rows carry no `Ord` (never sorted by the pin).
    fn write_availability_unsorted<T: serde::Serialize>(
        w: &mut impl std::io::Write,
        availability: &OriginAvailability<Vec<T>>,
    ) -> Result<(), String> {
        match availability {
            OriginAvailability::Present(rows) => {
                w.write_all(b"{\"state\":\"present\",\"value\":")
                    .map_err(|e| e.to_string())?;
                Self::write_rows(w, rows, None)?;
                w.write_all(b"}").map_err(|e| e.to_string())
            }
            OriginAvailability::Missing(_) => {
                let value = serde_json::to_value(availability).map_err(|e| e.to_string())?;
                serde_json::to_writer(w, &value).map_err(|e| e.to_string())
            }
        }
    }

    /// R473-4 (deeper, licensing): one licensing `Snapshot`, streamed field by
    /// field in sorted key order with every vector emitted row by row.
    ///
    /// This is where libzahl's memory actually was: 108 functions cost 0.03 GiB,
    /// while TWO snapshots cost 15.6 GiB as whole `Value`s (report 023 measures
    /// it). `fold_callers`/`fold_members` carry `skip_serializing_if`, so an
    /// absent one is omitted exactly as the derived serializer omits it.
    fn write_snapshot(
        w: &mut impl std::io::Write,
        s: &super::licensing::snapshot::Snapshot,
    ) -> Result<(), String> {
        if std::env::var_os("CRAT_ERA5C_FIELDSIZE").is_some() {
            macro_rules! sz {
                ($name:literal, $v:expr) => {
                    eprintln!(
                        "E5C_FIELD {:<28} bytes={}",
                        $name,
                        serde_json::to_string($v).map(|s| s.len()).unwrap_or(0)
                    );
                };
            }
            sz!("caller_coverage", &s.caller_coverage);
            sz!("complete_chains", &s.complete_chains);
            sz!("field_support", &s.field_support);
            sz!("first_permissions", &s.first_permissions);
            sz!("grant_holds", &s.grant_holds);
            sz!("matched", &s.matched);
            sz!("metadata", &s.metadata);
            sz!("no_ref_carriers", &s.no_ref_carriers);
            sz!("objective_grants", &s.objective_grants);
            sz!("reader_candidates", &s.reader_candidates);
            sz!("reader_functions", &s.reader_functions);
            sz!("reader_transfers", &s.reader_transfers);
            sz!("recursive", &s.recursive);
            sz!("reference_effects", &s.reference_effects);
            sz!("traversal_calls", &s.traversal_calls);
            sz!("traversal_correspondences", &s.traversal_correspondences);
            sz!("traversal_returns", &s.traversal_returns);
            sz!("value_origins", &s.value_origins);
        }
        let raw = |w: &mut dyn std::io::Write, bytes: &[u8]| -> Result<(), String> {
            w.write_all(bytes).map_err(|e| e.to_string())
        };
        raw(w, b"{\"caller_coverage\":")?;
        Self::write_small(&mut *w, &s.caller_coverage)?;
        raw(w, b",\"complete_chains\":")?;
        Self::write_rows(&mut *w, &s.complete_chains, None)?;
        raw(w, b",\"field_support\":")?;
        Self::write_rows(&mut *w, &s.field_support, None)?;
        raw(w, b",\"first_permissions\":")?;
        Self::write_rows(&mut *w, &s.first_permissions, None)?;
        if let Some(rows) = &s.fold_callers {
            raw(w, b",\"fold_callers\":")?;
            Self::write_rows(&mut *w, rows, None)?;
        }
        if let Some(rows) = &s.fold_members {
            raw(w, b",\"fold_members\":")?;
            Self::write_rows(&mut *w, rows, None)?;
        }
        raw(w, b",\"grant_holds\":")?;
        Self::write_rows(&mut *w, &s.grant_holds, None)?;
        raw(w, b",\"matched\":")?;
        s.matched.write_canonical(&mut *w)?;
        raw(w, b",\"metadata\":")?;
        s.metadata.write_canonical(&mut *w)?;
        raw(w, b",\"no_ref_carriers\":")?;
        Self::write_rows(&mut *w, &s.no_ref_carriers, None)?;
        raw(w, b",\"objective_grants\":")?;
        Self::write_rows(&mut *w, &s.objective_grants, None)?;
        raw(w, b",\"offset\":")?;
        Self::write_small(&mut *w, &s.offset)?;
        raw(w, b",\"reader_candidates\":")?;
        Self::write_rows(&mut *w, &s.reader_candidates, None)?;
        raw(w, b",\"reader_functions\":")?;
        Self::write_rows(&mut *w, &s.reader_functions, None)?;
        raw(w, b",\"reader_transfers\":")?;
        Self::write_rows(&mut *w, &s.reader_transfers, None)?;
        raw(w, b",\"recursive\":")?;
        Self::write_rows(&mut *w, &s.recursive, None)?;
        raw(w, b",\"reference_effects\":")?;
        Self::write_small(&mut *w, &s.reference_effects)?;
        raw(w, b",\"traversal_calls\":")?;
        Self::write_rows(&mut *w, &s.traversal_calls, None)?;
        raw(w, b",\"traversal_correspondences\":")?;
        Self::write_rows(&mut *w, &s.traversal_correspondences, None)?;
        raw(w, b",\"traversal_returns\":")?;
        Self::write_rows(&mut *w, &s.traversal_returns, None)?;
        raw(w, b",\"value_origins\":")?;
        s.value_origins.write_canonical(&mut *w)?;
        raw(w, b"}")
    }

    /// A field small enough to go through a `Value` unharmed.
    fn write_small<T: serde::Serialize>(
        w: &mut impl std::io::Write,
        value: &T,
    ) -> Result<(), String> {
        let value = serde_json::to_value(value).map_err(|e| e.to_string())?;
        serde_json::to_writer(w, &value).map_err(|e| e.to_string())
    }

    /// One function, streamed field by field in the key order a sorted `Map`
    /// emits. No clone of the function, no `Value` of the whole function.
    fn write_function(
        w: &mut impl std::io::Write,
        f: &FunctionEvidence,
        canonical: bool,
    ) -> Result<(), String> {
        let s = |w: &mut dyn std::io::Write, bytes: &[u8]| -> Result<(), String> {
            w.write_all(bytes).map_err(|e| e.to_string())
        };
        s(w, b"{\"function\":")?;
        serde_json::to_writer(&mut *w, &f.function).map_err(|e| e.to_string())?;
        s(w, b",\"native_unknown_targets\":")?;
        Self::write_availability(w, &f.native_unknown_targets, canonical)?;
        s(w, b",\"no_borrow_origin\":")?;
        let order = canonical.then(|| Self::sorted_order(&f.no_borrow_origin));
        Self::write_rows(w, &f.no_borrow_origin, order.as_deref())?;
        s(w, b",\"occurrences\":")?;
        let order = canonical.then(|| Self::sorted_order(&f.occurrences));
        Self::write_rows(w, &f.occurrences, order.as_deref())?;
        s(w, b",\"ownership\":")?;
        Self::write_ownership(w, &f.ownership, canonical)?;
        s(w, b",\"signature_slots\":")?;
        let order = canonical.then(|| Self::sorted_order(&f.signature_slots));
        Self::write_rows(w, &f.signature_slots, order.as_deref())?;
        s(w, b",\"storage_aliases\":")?;
        Self::write_availability(w, &f.storage_aliases, canonical)?;
        s(w, b",\"value_flows\":")?;
        Self::write_availability(w, &f.value_flows, canonical)?;
        s(w, b"}")
    }

    /// `OwnershipCorrespondence`, fields in sorted key order. Only `versions`
    /// is sorted by the pin; the rest keep their held order.
    fn write_ownership(
        w: &mut impl std::io::Write,
        o: &OwnershipCorrespondence,
        canonical: bool,
    ) -> Result<(), String> {
        let s = |w: &mut dyn std::io::Write, bytes: &[u8]| -> Result<(), String> {
            w.write_all(bytes).map_err(|e| e.to_string())
        };
        let small = |w: &mut dyn std::io::Write, v: &OriginMissing| -> Result<(), String> {
            let value = serde_json::to_value(v).map_err(|e| e.to_string())?;
            serde_json::to_writer(w, &value).map_err(|e| e.to_string())
        };
        s(w, b"{\"boundary_substitutions\":")?;
        Self::write_availability_unsorted(w, &o.boundary_substitutions)?;
        s(w, b",\"boundary_terminal_roster\":")?;
        small(w, &o.boundary_terminal_roster)?;
        s(w, b",\"call_arg_registrations\":")?;
        Self::write_availability_unsorted(w, &o.call_arg_registrations)?;
        s(w, b",\"conservation\":")?;
        small(w, &o.conservation)?;
        s(w, b",\"consumes\":")?;
        Self::write_availability_unsorted(w, &o.consumes)?;
        s(w, b",\"dynamic_epochs\":")?;
        small(w, &o.dynamic_epochs)?;
        s(w, b",\"equation_valuation_join\":")?;
        small(w, &o.equation_valuation_join)?;
        s(w, b",\"equations\":")?;
        Self::write_availability_unsorted(w, &o.equations)?;
        s(w, b",\"origin_closure\":")?;
        small(w, &o.origin_closure)?;
        s(w, b",\"partner_free\":")?;
        small(w, &o.partner_free)?;
        s(w, b",\"terminals\":")?;
        Self::write_availability_unsorted(w, &o.terminals)?;
        s(w, b",\"versions\":")?;
        Self::write_availability(w, &o.versions, canonical)?;
        s(w, b"}")
    }

    /// R473-4 design (A): the per-function half of `validate_meta`'s origin
    /// checks, so the streaming validator and the whole-value one are ONE
    /// definition. No check is dropped here; they are re-sited.
    pub(crate) fn check_function(
        function: &FunctionEvidence,
        kind_slot_keys: &mut std::collections::BTreeSet<String>,
    ) -> Result<(), String> {
        let gaps = &function.ownership;
        if gaps.dynamic_epochs != OriginMissing::DynamicEpochNotRepresented
            || gaps.partner_free != OriginMissing::PartnerFreeCorrespondenceNotExported
            || gaps.conservation != OriginMissing::ConservationNotProved
        {
            return Err("ownership proof availability changed".into());
        }
        let mut signatures = std::collections::BTreeSet::new();
        for slot in &function.signature_slots {
            if !signatures.insert(slot) {
                return Err("duplicate signature evidence".into());
            }
            if let OriginAvailability::Present(key) = &slot.kind_slot {
                kind_slot_keys.insert(key.clone());
            }
        }
        Ok(())
    }

    /// The per-function half of `declares_ownership_family`, accumulated.
    pub(crate) fn equations_present(function: &FunctionEvidence) -> Result<bool, String> {
        match &function.ownership.equations {
            OriginAvailability::Present(_) => Ok(true),
            OriginAvailability::Missing(OriginMissing::OwnershipEquationsNotExported) => Ok(false),
            _ => Err("invalid ownership equation availability".into()),
        }
    }

    /// R473-4 design (A): write the canonical form **per element**, so the
    /// multi-GiB whole-`Value` never exists.
    ///
    /// Byte-identity argument: serializing a `serde_json::Value` emits object
    /// keys in `Map` order, which is sorted; `to_value` of one element produces
    /// exactly the sub-`Value` that `from_str` of the whole would have produced
    /// for it. So element bytes are identical, and the containers are assembled
    /// here with the top-level keys in the same sorted order the whole-`Value`
    /// emits (`functions` < `licensing` < `reader_replay` < `stack_entry_final`).
    /// The digests in the report prove it rather than resting on this argument.
    /// Emit per element in the order HELD, without re-ordering anything.
    ///
    /// The reader side uses this: its evidence came from bytes that were already
    /// canonical, so re-sorting would be a no-op there -- but on a NON-canonical
    /// entry it would silently rewrite what the old code preserved verbatim, and
    /// the contract's byte comparison must keep seeing the difference.
    pub(crate) fn write_json(
        &self,
        w: &mut impl std::io::Write,
        present: super::cache_contract::stream::OriginKeys,
    ) -> Result<(), String> {
        self.write_elements(w, false, present)
    }

    pub(crate) fn write_canonical_json(&self, w: &mut impl std::io::Write) -> Result<(), String> {
        self.write_elements(w, true, Default::default())
    }

    fn write_elements(
        &self,
        w: &mut impl std::io::Write,
        canonical: bool,
        present: super::cache_contract::stream::OriginKeys,
    ) -> Result<(), String> {
        let err = |e: std::io::Error| e.to_string();
        let rss = || -> f64 {
            std::fs::read_to_string("/proc/self/statm")
                .ok()
                .and_then(|s| {
                    s.split_whitespace()
                        .nth(1)
                        .and_then(|p| p.parse::<f64>().ok())
                })
                .map(|pages| pages * 4096.0 / 1073741824.0)
                .unwrap_or(0.0)
        };
        let profile = std::env::var_os("CRAT_ERA5C_PROFILE").is_some();
        w.write_all(b"{\"functions\":[").map_err(err)?;
        let mut order: Vec<usize> = (0..self.functions.len()).collect();
        if canonical {
            order.sort_by(|&a, &b| self.functions[a].function.cmp(&self.functions[b].function));
        }
        for (n, &index) in order.iter().enumerate() {
            if n > 0 {
                w.write_all(b",").map_err(err)?;
            }
            // R473-4 (deeper): stream the function field by field and row by
            // row. No clone of the function, no `Value` of the whole function --
            // memory is bounded by the largest single ROW.
            Self::write_function(&mut *w, &self.functions[index], canonical)?;
        }
        if profile {
            eprintln!(
                "E5C_ELEM functions n={} rss={:.2} GiB",
                self.functions.len(),
                rss()
            );
        }
        if present.licensing {
            w.write_all(b"],\"licensing\":").map_err(err)?;
        } else {
            w.write_all(b"]").map_err(err)?;
        }
        match (&self.licensing, present.licensing) {
            (_, false) => {}
            (None, true) => w.write_all(b"null").map_err(err)?,
            (Some(snapshots), true) => {
                let mut order: Vec<usize> = (0..snapshots.len()).collect();
                if canonical {
                    order.sort_by_key(|&i| snapshots[i].offset);
                }
                w.write_all(b"[").map_err(err)?;
                for (n, &index) in order.iter().enumerate() {
                    if n > 0 {
                        w.write_all(b",").map_err(err)?;
                    }
                    Self::write_snapshot(&mut *w, &snapshots[index])?;
                }
                w.write_all(b"]").map_err(err)?;
            }
        }
        if profile {
            eprintln!(
                "E5C_ELEM licensing n={} rss={:.2} GiB",
                self.licensing.as_ref().map(|s| s.len()).unwrap_or(0),
                rss()
            );
        }
        if present.reader_replay {
            w.write_all(b",\"reader_replay\":").map_err(err)?;
        }
        match (&self.reader_replay, present.reader_replay) {
            (_, false) => {}
            (None, true) => w.write_all(b"null").map_err(err)?,
            (Some(receipts), true) => {
                w.write_all(b"[").map_err(err)?;
                for (n, receipt) in receipts.iter().enumerate() {
                    if n > 0 {
                        w.write_all(b",").map_err(err)?;
                    }
                    let value = serde_json::to_value(receipt).map_err(|e| e.to_string())?;
                    serde_json::to_writer(&mut *w, &value).map_err(|e| e.to_string())?;
                }
                w.write_all(b"]").map_err(err)?;
            }
        }
        if present.stack_entry_final {
            w.write_all(b",\"stack_entry_final\":").map_err(err)?;
        }
        match (&self.stack_entry_final, present.stack_entry_final) {
            (_, false) => {}
            (None, true) => w.write_all(b"null").map_err(err)?,
            (Some(accepted), true) => {
                let value = serde_json::to_value(accepted).map_err(|e| e.to_string())?;
                serde_json::to_writer(&mut *w, &value).map_err(|e| e.to_string())?;
            }
        }
        w.write_all(b"}").map_err(err)?;
        Ok(())
    }

    /// The per-function half of `canonicalized`, so the two orderings are one
    /// definition and cannot drift.
    fn canonicalize_function(function: &mut FunctionEvidence) {
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
}

#[cfg(test)]
mod tests;
