//! Initial F05 store-support audit. Records are conditional support, not kind
//! grants; OwnedInput, recursive and retained borrowed-return roles stay pending C.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::{
    mir::{
        AggregateKind, Body, CastKind, Operand, Place, PlaceElem, ProjectionElem, Rvalue,
        StatementKind,
        visit::{PlaceContext, Visitor},
    },
    ty::{TyCtxt, TyKind},
};
use serde::{Deserialize, Serialize};

use super::{
    super::{
        crate_slots::CrateSlots,
        ownership_access::PlaceSyntax,
        ownership_occurrence::{self, Availability},
        slots::StructFieldSlot,
    },
    facts::{EquationId, Facts},
    matched::{MatchedTransport, Meet, SourceLineage, TerminalTarget},
    transport::Node,
    value_origins::{OriginAtom, ValueOrigins},
};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct Site {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) field_key: String,
    pub(crate) place: PlaceSyntax,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum StoredValue {
    Null,
    Value(PlaceSyntax),
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Store {
    pub(crate) site: Site,
    pub(crate) value: StoredValue,
    pub(crate) aggregate: bool,
    pub(crate) direct_projection: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Load {
    pub(crate) site: Site,
    pub(crate) shared_reference_root: bool,
    pub(crate) direct_projection: bool,
}

/// R304-9: a write the named store inventory cannot resolve, together with the
/// pointer fields it may alias. Recording one is a refusal, never a permission:
/// the inventory fails closed rather than treating the cell as unwritten.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct UnsupportedFieldEffect {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) reason: String,
    pub(crate) field_keys: Vec<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Inputs {
    pub(crate) fields: BTreeSet<String>,
    pub(crate) stores: Vec<Store>,
    pub(crate) loads: Vec<Load>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) unsupported: Vec<UnsupportedFieldEffect>,
}

/// Locate the last named pointer field without treating a following dereference
/// or an indirect projection as an exact pointer-cell access.
fn field<'tcx>(
    tcx: TyCtxt<'tcx>,
    slots: &CrateSlots,
    body: &Body<'tcx>,
    place: Place<'tcx>,
) -> Option<(String, bool)> {
    let mut ty = body.local_decls[place.local].ty;
    let mut found = None;
    let mut supported = true;
    for (position, element) in place.projection.iter().enumerate() {
        match element {
            ProjectionElem::Deref => {
                ty = ty.builtin_deref(true)?;
            }
            ProjectionElem::Field(index, field_ty) => {
                let TyKind::Adt(adt, _) = ty.kind() else { return found.map(|key| (key, false)) };
                if let Some(did) = adt.did().as_local()
                    && adt.is_struct()
                    && field_ty.is_raw_ptr()
                    && slots
                        .field_slots
                        .slot_for_field_depth(
                            StructFieldSlot {
                                struct_did: did,
                                field_index: index.as_usize(),
                            },
                            0,
                        )
                        .is_some()
                {
                    found = Some(super::super::slot_key::field_key(
                        tcx,
                        did,
                        index.as_usize(),
                        0,
                    ));
                    supported &= position + 1 == place.projection.len();
                }
                ty = field_ty;
            }
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                supported = false;
                ty = ty.builtin_index()?;
            }
            ProjectionElem::OpaqueCast(next)
            | ProjectionElem::Subtype(next)
            | ProjectionElem::UnwrapUnsafeBinder(next) => {
                supported = false;
                ty = next;
            }
            _ => {
                supported = false;
            }
        }
    }
    let direct = matches!(
        place.projection.as_slice(),
        [ProjectionElem::Field(..)] | [ProjectionElem::Deref, ProjectionElem::Field(..)]
    );
    found.map(|key| (key, supported && direct))
}

/// R304-9 "known base": the reaching definition of a destination's base local.
/// A constant address is a static, which can never alias a heap struct field.
/// Anything else a dereference reaches — a cast, an offset, a call result, a
/// copied pointer, or no definition in this block at all — fails closed. MIR
/// reuses locals across disjoint live ranges, so this asks the nearest earlier
/// definition rather than assuming a local is defined once.
fn constant_address_base<'tcx>(
    body: &Body<'tcx>,
    earlier: &[rustc_middle::mir::Statement<'tcx>],
    place: &Place<'tcx>,
) -> bool {
    earlier
        .iter()
        .rev()
        .find_map(|instruction| match &instruction.kind {
            StatementKind::Assign(box (target, value)) if target.local == place.local => Some(
                target.projection.is_empty()
                    && matches!(value, Rvalue::Use(Operand::Constant(_)))
                    && body.local_decls[place.local].ty.is_raw_ptr(),
            ),
            _ => None,
        })
        .unwrap_or(false)
}

/// R336-4 (ii): is this type transitively free of anything that could carry a
/// pointer? Fails closed: an unknown type, a foreign ADT, a `Box`, a function
/// pointer, a reference and a raw pointer are all NOT pointer-free, and so is
/// anything reached through one. The recursion is bounded because a struct that
/// reaches itself must do so through a pointer, which stops it.
fn pointer_free<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty<'tcx>, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => true,
        TyKind::Array(element, _) => pointer_free(tcx, *element, depth - 1),
        TyKind::Tuple(elements) => elements
            .iter()
            .all(|element| pointer_free(tcx, element, depth - 1)),
        TyKind::Adt(adt, args) => {
            !adt.is_box()
                && adt.did().is_local()
                && adt
                    .all_fields()
                    .all(|definition| pointer_free(tcx, definition.ty(tcx, args), depth - 1))
        }
        _ => false,
    }
}

/// R336-4 (iii): every assignment to this base local, anywhere in the body,
/// keeps it a pointer to the struct it is declared to point at. MIR reuses
/// locals, so this asks about all of them rather than the nearest. A cast is
/// admitted only from `c_void`, which is what an allocator returns; a cast from
/// an integer, from a pointer to a different ADT, an offset or an index is the
/// prefix pun finding A exists for and keeps the row denied.
fn base_stays_in_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: rustc_middle::mir::Local,
) -> bool {
    let declared = body.local_decls[local].ty;
    body.basic_blocks.iter().all(|data| {
        data.statements.iter().all(|instruction| {
            let StatementKind::Assign(box (target, value)) = &instruction.kind else {
                return true;
            };
            if target.local != local || !target.projection.is_empty() {
                return true;
            }
            match value {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
                    place.ty(body, tcx).ty == declared
                }
                Rvalue::Cast(CastKind::PtrToPtr, operand, _) => operand
                    .ty(body, tcx)
                    .builtin_deref(true)
                    .is_some_and(|pointee| match pointee.kind() {
                        TyKind::Adt(adt, _) => tcx.def_path_str(adt.did()).ends_with("c_void"),
                        _ => false,
                    }),
                _ => false,
            }
        })
    })
}

/// R336-4: a write to a named POINTER-FREE field of the struct the base local
/// is declared to point at. A MIR field projection is type-directed, so such a
/// write cannot reach that struct's pointer fields whatever the base's
/// provenance — provided the base really is that pointer everywhere, which is
/// what `base_stays_in_type` establishes. `field()` cannot answer this because
/// it is keyed on the REGISTERED pointer fields; this asks the struct
/// declaration instead.
fn scalar_field_write<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: Place<'tcx>) -> bool {
    let (base, field_ty) = match place.projection.as_slice() {
        [ProjectionElem::Deref, ProjectionElem::Field(_, field_ty)] => {
            let Some(pointee) = body.local_decls[place.local].ty.builtin_deref(true) else {
                return false;
            };
            (pointee, *field_ty)
        }
        [ProjectionElem::Field(_, field_ty)] => (body.local_decls[place.local].ty, *field_ty),
        _ => return false,
    };
    let TyKind::Adt(adt, _) = base.kind() else {
        return false;
    };
    adt.is_struct()
        && adt.did().is_local()
        && pointer_free(tcx, field_ty, 8)
        && base_stays_in_type(tcx, body, place.local)
}

/// R304-9: the may-alias set for a write the inventory could not resolve. A
/// known local struct pointee narrows it to that struct's registered pointer
/// fields; anything else (a cast, a punned pointer, a computed address, an
/// opaque pointee) may alias any of them.
fn unresolved_effect(
    function: &str,
    block: u32,
    statement: usize,
    ty: rustc_middle::ty::Ty<'_>,
    by_struct: &BTreeMap<String, Vec<String>>,
    all_keys: &[String],
    tcx: TyCtxt<'_>,
) -> UnsupportedFieldEffect {
    let narrowed = match ty.kind() {
        TyKind::Adt(adt, _) if adt.is_struct() && adt.did().is_local() => {
            Some(tcx.def_path_str(adt.did()))
        }
        _ => None,
    };
    let (reason, field_keys) = match narrowed {
        Some(structure) => (
            "whole-struct-write",
            by_struct.get(&structure).cloned().unwrap_or_default(),
        ),
        None => ("punned-destination", all_keys.to_vec()),
    };
    UnsupportedFieldEffect {
        function: function.to_owned(),
        block,
        statement,
        reason: reason.to_owned(),
        field_keys,
    }
}

/// R304-10: the struct a call's callee derives an impl for. Derived bodies are
/// admitted to the roster rather than filtered away, so a call into one is
/// visible here; a derived `Clone` copies the struct's pointer fields.
fn derived_impl_self_struct<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: rustc_span::def_id::LocalDefId,
    callee: rustc_hir::def_id::DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Option<String> {
    // A `(*p).clone()` names the trait item, not the impl method, so resolve the
    // instance before asking whose impl it is.
    let resolved = rustc_middle::ty::Instance::try_resolve(
        tcx,
        rustc_middle::ty::TypingEnv::post_analysis(tcx, caller.to_def_id()),
        callee,
        args,
    )
    .ok()
    .flatten()
    .map_or(callee, |instance| instance.def_id());
    let parent = tcx.parent(resolved);
    if !matches!(tcx.def_kind(parent), rustc_hir::def::DefKind::Impl { .. })
        || !tcx.is_automatically_derived(parent)
    {
        return None;
    }
    match tcx.type_of(parent).instantiate_identity().kind() {
        TyKind::Adt(adt, _) if adt.is_struct() && adt.did().is_local() => {
            Some(tcx.def_path_str(adt.did()))
        }
        _ => None,
    }
}

fn operand(value: &Operand<'_>, tcx: TyCtxt<'_>) -> StoredValue {
    match value {
        Operand::Copy(place) | Operand::Move(place) => StoredValue::Value((*place).into()),
        Operand::Constant(_) if super::super::source_events::operand_is_null(value, &[], tcx) => {
            StoredValue::Null
        }
        _ => StoredValue::Unknown,
    }
}

impl Inputs {
    pub(crate) fn collect(program: &RustProgram<'_>, slots: &CrateSlots) -> Self {
        let mut inputs = Self::default();
        let mut by_struct: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for index in 0..slots.field_slots.len() {
            let slot = slots
                .field_slots
                .slot(super::super::slots::SlotId::from_usize(index));
            if slot.depth != 0
                || slots
                    .field_slots
                    .is_array_slot(super::super::slots::SlotId::from_usize(index))
            {
                continue;
            }
            if let super::super::slots::SlotOwner::Field(field) = slot.owner {
                let key = super::super::slot_key::field_key(
                    program.tcx,
                    field.struct_did,
                    field.field_index,
                    0,
                );
                inputs.fields.insert(key.clone());
                by_struct
                    .entry(program.tcx.def_path_str(field.struct_did))
                    .or_default()
                    .push(key);
            }
        }
        for keys in by_struct.values_mut() {
            keys.sort();
            keys.dedup();
        }
        let all_keys: Vec<String> = inputs.fields.iter().cloned().collect();
        for &function in &program.functions {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let name = program.tcx.def_path_str(function);
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for (statement, instruction) in data.statements.iter().enumerate() {
                    let StatementKind::Assign(box (destination, value)) = &instruction.kind else {
                        continue;
                    };
                    let site = |place: Place<'_>, field_key| Site {
                        function: name.clone(),
                        block: block.as_u32(),
                        statement,
                        field_key,
                        place: place.into(),
                    };
                    if destination
                        .projection
                        .iter()
                        .any(|element| matches!(element, ProjectionElem::Deref))
                        && !constant_address_base(&body, &data.statements[..statement], destination)
                        && field(program.tcx, slots, &body, *destination).is_none()
                    {
                        // R336-4: a named pointer-free field of the struct the
                        // base is declared to point at denies nothing, but the
                        // row is still recorded and counted rather than dropped.
                        let scalar = scalar_field_write(program.tcx, &body, *destination);
                        inputs.unsupported.push(if scalar {
                            UnsupportedFieldEffect {
                                function: name.clone(),
                                block: block.as_u32(),
                                statement,
                                reason: "scalar-field-write".into(),
                                field_keys: vec![],
                            }
                        } else {
                            unresolved_effect(
                                &name,
                                block.as_u32(),
                                statement,
                                destination.ty(&*body, program.tcx).ty,
                                &by_struct,
                                &all_keys,
                                program.tcx,
                            )
                        });
                    }
                    if let Rvalue::Aggregate(kind, operands) = value
                        && let AggregateKind::Adt(did, _, args, _, active) = kind.as_ref()
                    {
                        let adt = program.tcx.adt_def(*did);
                        if adt.is_struct() && did.is_local() {
                            for (index, definition) in
                                adt.non_enum_variant().fields.iter_enumerated()
                            {
                                let ty = definition.ty(program.tcx, args);
                                if !ty.is_raw_ptr() {
                                    continue;
                                }
                                let place = destination
                                    .project_deeper(&[PlaceElem::Field(index, ty)], program.tcx);
                                if let Some((key, direct)) = field(program.tcx, slots, &body, place)
                                {
                                    inputs.stores.push(Store {
                                        site: site(place, key),
                                        value: if active.is_none()
                                            && operands.len() == adt.non_enum_variant().fields.len()
                                        {
                                            operands
                                                .get(index)
                                                .map(|value| operand(value, program.tcx))
                                                .unwrap_or(StoredValue::Unknown)
                                        } else {
                                            StoredValue::Unknown
                                        },
                                        aggregate: true,
                                        direct_projection: direct,
                                    });
                                }
                            }
                            continue;
                        }
                    }
                    if let Some((key, direct)) = field(program.tcx, slots, &body, *destination) {
                        let value = match value {
                            Rvalue::Use(value) => operand(value, program.tcx),
                            Rvalue::Cast(CastKind::PtrToPtr, value, _) => {
                                operand(value, program.tcx)
                            }
                            Rvalue::Cast(_, value @ Operand::Constant(_), _) => {
                                operand(value, program.tcx)
                            }
                            Rvalue::CopyForDeref(place) => StoredValue::Value((*place).into()),
                            _ => StoredValue::Unknown,
                        };
                        inputs.stores.push(Store {
                            site: site(*destination, key),
                            value,
                            aggregate: false,
                            direct_projection: direct,
                        });
                    }
                }
                if let Some(rustc_middle::mir::Terminator {
                    kind:
                        rustc_middle::mir::TerminatorKind::Call {
                            func, destination, ..
                        },
                    ..
                }) = &data.terminator
                {
                    let statement = data.statements.len();
                    if let Some((key, direct)) = field(program.tcx, slots, &body, *destination) {
                        inputs.stores.push(Store {
                            site: Site {
                                function: name.clone(),
                                block: block.as_u32(),
                                statement,
                                field_key: key,
                                place: (*destination).into(),
                            },
                            value: StoredValue::Unknown,
                            aggregate: false,
                            direct_projection: direct,
                        });
                    } else if destination
                        .projection
                        .iter()
                        .any(|element| matches!(element, ProjectionElem::Deref))
                        && !constant_address_base(&body, &data.statements, destination)
                    {
                        inputs.unsupported.push(unresolved_effect(
                            &name,
                            block.as_u32(),
                            statement,
                            destination.ty(&*body, program.tcx).ty,
                            &by_struct,
                            &all_keys,
                            program.tcx,
                        ));
                    }
                    if let TyKind::FnDef(target, args) = *func.ty(&*body, program.tcx).kind()
                        && let Some(structure) =
                            derived_impl_self_struct(program.tcx, function, target, args)
                    {
                        inputs.unsupported.push(UnsupportedFieldEffect {
                            function: name.clone(),
                            block: block.as_u32(),
                            statement,
                            reason: "derived-impl-call".to_owned(),
                            field_keys: by_struct.get(&structure).cloned().unwrap_or_default(),
                        });
                    }
                }
            }
            struct Reads<'a, 'tcx> {
                tcx: TyCtxt<'tcx>,
                slots: &'a CrateSlots,
                body: &'a Body<'tcx>,
                function: &'a str,
                loads: &'a mut Vec<Load>,
            }
            impl<'tcx> Visitor<'tcx> for Reads<'_, 'tcx> {
                fn visit_place(
                    &mut self,
                    place: &Place<'tcx>,
                    context: PlaceContext,
                    location: rustc_middle::mir::Location,
                ) {
                    if matches!(context, PlaceContext::NonMutatingUse(_))
                        && let Some((key, direct)) = field(self.tcx, self.slots, self.body, *place)
                    {
                        self.loads.push(Load {
                            site: Site {
                                function: self.function.into(),
                                block: location.block.as_u32(),
                                statement: location.statement_index,
                                field_key: key,
                                place: (*place).into(),
                            },
                            shared_reference_root: matches!(
                                self.body.local_decls[place.local].ty.kind(),
                                TyKind::Ref(_, _, rustc_hir::Mutability::Not)
                            ),
                            direct_projection: direct,
                        });
                    }
                    self.super_place(place, context, location);
                }
            }
            Reads {
                tcx: program.tcx,
                slots,
                body: &body,
                function: &name,
                loads: &mut inputs.loads,
            }
            .visit_body(&body);
        }
        inputs
            .stores
            .sort_by(|left, right| left.site.cmp(&right.site));
        inputs
            .loads
            .sort_by(|left, right| left.site.cmp(&right.site));
        inputs.loads.dedup();
        inputs
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum Pending {
    Coverage,
    UnknownStore,
    IndirectAccess,
    SharedReference,
    BorrowedReturnRoleC,
    OwnedInputOrOriginC,
    TransferBinding,
    RecursiveIdentityC,
    TerminalRoleC,
    CompetingTerminal,
    EmptyOwnedSupport,
    CallerCoverageC,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct StoreProof {
    pub(crate) site: Site,
    pub(crate) equation: EquationId,
    pub(crate) destination_use: Node,
    pub(crate) destination_def: Node,
    pub(crate) source_use: Node,
    pub(crate) source_def: Node,
    pub(crate) by_move: bool,
    /// Includes exact source/terminal equation identities and guard dependencies.
    pub(crate) meet: Meet,
    /// Conditional zero-output receipts; raw transport meets remain exported.
    pub(crate) discharged_outputs: Vec<OutputDischarge>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) traversal_outputs: Vec<super::traversal_discharge::Discharge>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ForwardedOutput {
    pub(crate) output: Meet,
    pub(crate) formal: Node,
    pub(crate) actual: Node,
    pub(crate) exit_equation: EquationId,
    pub(crate) boundary: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct InputAlternative {
    pub(crate) route: super::matched::InputStoreRoute,
    pub(crate) free: Meet,
    pub(crate) forwarded: ForwardedOutput,
    pub(crate) forwarded_returns: Vec<super::matched::ForwardedReturn>,
    /// Other outputs are retained until their own forwarding/zero contract.
    pub(crate) pending_outputs: Vec<super::matched::TerminalInstance>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct InputCallSupport {
    pub(crate) application: super::matched::InputStoreApplication,
    pub(crate) alternatives: Vec<InputAlternative>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum CallerCoverage {
    PendingCompilerAndAttestation,
    CertifiedFirst,
    CertifiedChain,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct InputStoreProof {
    pub(crate) site: Site,
    pub(crate) equation: EquationId,
    pub(crate) destination_def: Node,
    pub(crate) source_def: Node,
    pub(crate) applications: Vec<InputCallSupport>,
    pub(crate) caller_coverage: CallerCoverage,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct OutputDischarge {
    pub(crate) output: Meet,
    pub(crate) certificate: super::ref_effects::ConsumedOutput,
}

impl OutputDischarge {
    /// Match an already validated conditional lemma to these exact meets.
    /// This checks required dependencies, not their model valuation.
    pub(crate) fn certify(
        output: &Meet,
        free: &Meet,
        certificate: &super::ref_effects::ConsumedOutput,
    ) -> Option<Self> {
        if !matches!(output.terminal.target, TerminalTarget::Output { .. })
            || !matches!(free.terminal.target, TerminalTarget::Free(_))
            || output.terminal != certificate.output
            || free.terminal != certificate.free
            || output.source != free.source
            || !matches!(free.source.lineage, SourceLineage::Exact(_))
            || certificate.free.lineage != SourceLineage::Exact(vec![certificate.call.clone()])
            || certificate.output.lineage != certificate.free.lineage
            || !certificate.required_free.required
            || certificate.required_free.binding.construction != certificate.call.construction
            || free.guards.get(&certificate.required_free.binding) != Some(&true)
            || output
                .guards
                .iter()
                .any(|(key, required)| free.guards.get(key).is_some_and(|value| value != required))
        {
            return None;
        }
        Some(Self {
            output: output.clone(),
            certificate: certificate.clone(),
        })
    }
}

fn discharge_output(
    output: &Meet,
    free: &Meet,
    certificates: &[super::ref_effects::ConsumedOutput],
) -> Option<OutputDischarge> {
    let mut matches = certificates
        .iter()
        .filter_map(|certificate| OutputDischarge::certify(output, free, certificate));
    let result = matches.next()?;
    matches.next().is_none().then_some(result)
}

/// Choose a responsibility only after exact conditional output disposition.
/// Guard alternatives to the same terminal remain in the raw graph; the
/// retained meet carries one complete route and all its required predicates.
fn select_terminal(
    facts: &Facts,
    aliases: &BTreeMap<EquationId, EquationId>,
    meets: &[Meet],
    certificates: &[super::ref_effects::ConsumedOutput],
) -> Result<
    (
        Meet,
        Vec<OutputDischarge>,
        Vec<super::traversal_discharge::Discharge>,
    ),
    Pending,
> {
    let first = meets.first().ok_or(Pending::TerminalRoleC)?;
    if meets.iter().any(|meet| meet.source != first.source) {
        return Err(Pending::CompetingTerminal);
    }
    let frees: BTreeSet<_> = meets
        .iter()
        .filter(|meet| matches!(meet.terminal.target, TerminalTarget::Free(_)))
        .map(|meet| &meet.terminal)
        .collect();
    if frees.len() > 1 {
        return Err(Pending::CompetingTerminal);
    }
    let choices: Vec<_> = if frees.is_empty() {
        vec![first]
    } else {
        meets
            .iter()
            .filter(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
            .collect()
    };
    for chosen in choices {
        let mut discharged = Vec::new();
        let mut traversal_outputs = Vec::new();
        let mut covered = true;
        for other in meets {
            if other.terminal == chosen.terminal {
                continue;
            }
            if let Some(receipt) = discharge_output(other, chosen, certificates) {
                if !discharged.contains(&receipt) {
                    discharged.push(receipt);
                }
            } else if let Some(receipt) =
                super::traversal_discharge::certify(facts, other, chosen, aliases)
            {
                if !traversal_outputs.contains(&receipt) {
                    traversal_outputs.push(receipt);
                }
            } else {
                covered = false;
                break;
            }
        }
        if covered {
            return Ok((chosen.clone(), discharged, traversal_outputs));
        }
    }
    Err(Pending::TerminalRoleC)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Hold {
    pub(crate) site: Option<Site>,
    pub(crate) construction: Option<u32>,
    pub(crate) reason: Pending,
}

/// R388-1: a store's source origin, classified instead of refused. The pre-solve
/// boolean asked "is this store's source provably a fresh allocation" and held
/// everything else; the solver can carry the rest as a condition, so the coupled
/// system (params own <= fields own <= stores supported <= params own) has a
/// fixpoint the way every other coupled system here does.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum StoreSourceOrigin {
    /// A fresh allocation, or nothing at all. Supported unconditionally.
    Fresh,
    Null,
    /// The token came in as this parameter slot and went back out. Supported iff
    /// that slot owns.
    Input(String),
    /// The token was loaded from this field. Supported iff that field owns.
    FieldToken(String),
    /// Not classifiable from recorded origins. Never supported.
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ClassifiedStore {
    pub(crate) site: Site,
    pub(crate) origin: StoreSourceOrigin,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct FieldProof {
    pub(crate) field_key: String,
    pub(crate) null_stores: Vec<Site>,
    pub(crate) stores: Vec<StoreProof>,
    pub(crate) input_stores: Vec<InputStoreProof>,
    pub(crate) holds: Vec<Hold>,
    /// R388-1: the `OwnedInputOrOriginC` holds, classified. Additive — absent in
    /// entries recorded before the rule, and the default arm ignores it.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) classified: Vec<ClassifiedStore>,
}

impl FieldProof {
    pub(crate) fn supported(&self) -> bool {
        (!self.stores.is_empty() || !self.input_stores.is_empty()) && self.holds.is_empty()
    }
}

fn input_alternative(
    facts: &Facts,
    matched: &MatchedTransport,
    origins: &ValueOrigins,
    application: &super::matched::InputStoreApplication,
    route: &super::matched::InputStoreRoute,
    symbolic: &BTreeSet<OriginAtom>,
    destination: Node,
) -> Result<Option<InputAlternative>, Pending> {
    use super::super::ownership_boundary::{Role, Variables};
    let boundary = facts
        .boundary_substitutions
        .iter()
        .find(|row| {
            row.point.construction == application.call.construction
                && row.ordinal == route.output_boundary
        })
        .ok_or(Pending::TerminalRoleC)?;
    let Some(arm) = super::cell_effects::call_arm(facts, boundary, matched.guard_aliases()) else {
        return Ok(None);
    };
    if route.actual_output.var != arm.original.1 || route.guards.get(&arm.guard) != Some(&true) {
        return Ok(None);
    }
    if symbolic != &BTreeSet::from([OriginAtom::Input(route.formal_input)]) {
        return Err(Pending::OwnedInputOrOriginC);
    }
    let atoms = origins.at(route.actual_input);
    let fresh: BTreeSet<_> = atoms
        .iter()
        .filter_map(|atom| match atom {
            OriginAtom::Fresh(id) => Some(*id),
            _ => None,
        })
        .collect();
    let sources: BTreeSet<_> = route
        .anchors
        .iter()
        .map(|anchor| anchor.source.clone())
        .collect();
    if fresh.len() != 1
        || !atoms
            .iter()
            .all(|atom| matches!(atom, OriginAtom::Fresh(_) | OriginAtom::Null))
        || sources.len() != 1
    {
        return Err(Pending::OwnedInputOrOriginC);
    }
    let source = sources.first().unwrap();
    if fresh != BTreeSet::from([source.endpoint])
        || !matches!(source.lineage, SourceLineage::Exact(_))
    {
        return Err(Pending::RecursiveIdentityC);
    }
    if route
        .source_terminals
        .iter()
        .any(|meet| &meet.source != source)
    {
        return Err(Pending::CompetingTerminal);
    }
    let frees: BTreeSet<_> = route
        .source_terminals
        .iter()
        .filter(|meet| matches!(meet.terminal.target, TerminalTarget::Free(_)))
        .map(|meet| meet.terminal.clone())
        .collect();
    if frees.len() > 1 {
        return Err(Pending::CompetingTerminal);
    }
    let terminal = frees.first().ok_or(Pending::TerminalRoleC)?;
    let free = route
        .meets
        .iter()
        .find(|meet| &meet.terminal == terminal && &meet.source == source)
        .ok_or(Pending::TerminalRoleC)?;
    if !matches!(free.terminal.lineage, SourceLineage::Exact(_)) {
        return Err(Pending::RecursiveIdentityC);
    }
    let outputs: Vec<_> = route.source_terminals.iter().filter(|meet| meet.terminal.lineage == SourceLineage::Exact(vec![application.call.clone()])
        && matches!(meet.terminal.target, TerminalTarget::Output {node, ..} if node == destination)).collect();
    let output = outputs.first().ok_or(Pending::TerminalRoleC)?;
    if outputs
        .iter()
        .any(|other| other.terminal != output.terminal)
        || output
            .guards
            .iter()
            .any(|(key, required)| free.guards.get(key).is_some_and(|value| value != required))
    {
        return Err(Pending::TerminalRoleC);
    }
    let TerminalTarget::Output { ordinal, .. } = output.terminal.target else {
        return Err(Pending::TerminalRoleC);
    };
    let record = facts
        .terminals
        .iter()
        .find(|row| {
            row.point.construction == destination.construction
                && row.ordinal == ordinal
                && row.role == "parameter-output"
        })
        .ok_or(Pending::TerminalRoleC)?;
    let exits: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|row| {
            row.point == record.point
                && row.role == Role::ExitOutput
                && row.matched.iter().any(|pair| {
                    pair.actual
                        == (Variables::Single {
                            var: destination.var,
                        })
                        && pair.formal
                            == (Variables::Single {
                                var: route.formal_output.var,
                            })
                })
        })
        .collect();
    let [exit] = exits.as_slice() else { return Err(Pending::TerminalRoleC) };
    let equations: Vec<_> = facts
        .equations
        .iter()
        .filter(|row| {
            row.point == exit.point
                && row.operation == "equal"
                && row.guard.is_none()
                && row.variables == [destination.var, route.formal_output.var]
                && row.validate().is_ok()
        })
        .collect();
    let [equation] = equations.as_slice() else { return Err(Pending::TerminalRoleC) };
    let mut remaining: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for other in route.source_terminals.iter().filter(|meet| {
        matches!(meet.terminal.target, TerminalTarget::Output { .. })
            && meet.terminal != output.terminal
    }) {
        remaining
            .entry(other.terminal.clone())
            .or_default()
            .push(other);
    }
    let mut pending_outputs = Vec::new();
    let mut forwarded_returns = Vec::new();
    for (terminal, outputs) in remaining {
        // Every retained guard alternative for this output must have the exact
        // continuation. A failed alternative keeps the whole output pending.
        let certificates: Option<Vec<_>> = outputs
            .into_iter()
            .map(|other| matched.forward_return(facts, other, free))
            .collect();
        if let Some(certificates) = certificates {
            forwarded_returns.extend(certificates);
        } else {
            pending_outputs.push(terminal);
        }
    }
    Ok(Some(InputAlternative {
        route: route.clone(),
        free: free.clone(),
        forwarded: ForwardedOutput {
            output: (*output).clone(),
            formal: route.formal_output,
            actual: route.actual_output,
            exit_equation: EquationId {
                construction: equation.point.construction,
                ordinal: equation.ordinal,
            },
            boundary: exit.ordinal,
        },
        forwarded_returns,
        pending_outputs,
    }))
}

fn input_store(
    facts: &Facts,
    matched: &MatchedTransport,
    origins: &ValueOrigins,
    site: &Site,
    equation: EquationId,
    transfer: &ownership_occurrence::Transfer,
    symbolic: &BTreeSet<OriginAtom>,
) -> (InputStoreProof, Vec<Pending>) {
    let mut result = InputStoreProof {
        site: site.clone(),
        equation,
        destination_def: Node {
            construction: equation.construction,
            var: transfer.destination_def,
        },
        source_def: Node {
            construction: equation.construction,
            var: transfer.source_def,
        },
        applications: Vec::new(),
        caller_coverage: CallerCoverage::PendingCompilerAndAttestation,
    };
    let mut holds = vec![Pending::CallerCoverageC];
    for application in matched.input_store_applications(facts, equation) {
        let mut alternatives = Vec::new();
        let mut reasons = Vec::new();
        for route in &application.routes {
            match input_alternative(
                facts,
                matched,
                origins,
                &application,
                route,
                symbolic,
                result.destination_def,
            ) {
                Ok(Some(alternative)) => {
                    if !alternative.pending_outputs.is_empty() {
                        holds.push(Pending::TerminalRoleC);
                    }
                    alternatives.push(alternative);
                }
                Ok(None) => {}
                Err(reason) => reasons.push(reason),
            }
        }
        if reasons.contains(&Pending::CompetingTerminal) {
            holds.push(Pending::CompetingTerminal);
        }
        if alternatives.is_empty() {
            holds.push(if reasons.contains(&Pending::OwnedInputOrOriginC) {
                Pending::OwnedInputOrOriginC
            } else if reasons.contains(&Pending::CompetingTerminal) {
                Pending::CompetingTerminal
            } else {
                Pending::TerminalRoleC
            });
        }
        result.applications.push(InputCallSupport {
            application,
            alternatives,
        });
    }
    if result.applications.is_empty() {
        holds.push(Pending::OwnedInputOrOriginC);
    }
    (result, holds)
}

pub(crate) fn audit(
    facts: &Facts,
    inputs: &Inputs,
    matched: &MatchedTransport,
    origins: &ValueOrigins,
) -> Vec<FieldProof> {
    // Reconstruct conditional lemmas from current metadata. No selected model
    // or cached positive certificate can erase a competing terminal.
    let certificates: Vec<_> = super::ref_effects::Plan::build(facts)
        .candidates
        .iter()
        .filter_map(|candidate| {
            super::ref_effects::certify_consumed_output(facts, candidate, matched.guard_aliases())
                .ok()
        })
        .collect();
    let mut fields: BTreeMap<_, _> = inputs
        .fields
        .iter()
        .map(|key| {
            (
                key.clone(),
                FieldProof {
                    field_key: key.clone(),
                    null_stores: Vec::new(),
                    stores: Vec::new(),
                    input_stores: Vec::new(),
                    holds: Vec::new(),
                    classified: Vec::new(),
                },
            )
        })
        .collect();
    // Independent source occurrences prevent an unsupported store from being
    // omitted from the all-store certificate. Aggregate field consumes expose
    // components that have no standalone base kind slot.
    for (function, occurrences) in &facts.source_occurrences {
        for occurrence in occurrences {
            let mut expected = BTreeSet::new();
            if let super::super::origin_evidence::OriginAvailability::Present(key) =
                &occurrence.destination
                && inputs.fields.contains(key)
            {
                expected.insert(key.clone());
            }
            if matches!(
                occurrence.syntax.expression,
                super::super::ownership_access::Expression::Aggregate { .. }
            ) {
                let depth = occurrence
                    .syntax
                    .destination
                    .projection
                    .iter()
                    .filter(|step| matches!(step, super::super::export::ProjKey::Deref))
                    .count();
                for consume in facts.consumes.iter().filter(|row| {
                    row.point.function.as_ref() == Some(function)
                        && row.point.block == Some(occurrence.site.block)
                        && row.point.statement == Some(occurrence.site.statement)
                        && row.local == occurrence.syntax.destination.local
                        && row
                            .projection
                            .starts_with(&occurrence.syntax.destination.projection)
                }) {
                    let (
                        Availability::Present(base),
                        Availability::Present(window),
                        Availability::Present(paths),
                    ) = (&consume.base, &consume.projected, &consume.pointer_paths)
                    else {
                        continue;
                    };
                    for var in window.use_start..window.use_end {
                        let Some(path) = paths.get((var - base.use_start) as usize) else {
                            continue;
                        };
                        if path
                            .iter()
                            .filter(|step| matches!(step, ownership_occurrence::PathStep::Deref))
                            .count()
                            != depth
                        {
                            continue;
                        }
                        if let Some(ownership_occurrence::PathStep::Field {
                            structure,
                            index,
                            ..
                        }) = path.last()
                        {
                            let key = format!("{structure}::field{index}@d0");
                            if inputs.fields.contains(&key) {
                                expected.insert(key);
                            }
                        }
                    }
                }
            }
            for field in expected {
                if !inputs.stores.iter().any(|store| {
                    &store.site.function == function
                        && store.site.block == occurrence.site.block
                        && store.site.statement == occurrence.site.statement
                        && store.site.field_key == field
                }) {
                    fields.get_mut(&field).unwrap().holds.push(Hold {
                        site: Some(Site {
                            function: function.clone(),
                            block: occurrence.site.block,
                            statement: occurrence.site.statement,
                            field_key: field.clone(),
                            place: occurrence.syntax.destination.clone(),
                        }),
                        construction: None,
                        reason: Pending::Coverage,
                    });
                }
            }
        }
    }
    for load in &inputs.loads {
        let Some(proof) = fields.get_mut(&load.site.field_key) else { continue };
        let reader = facts
            .reader_plan
            .functions
            .iter()
            .find(|reader| reader.function == load.site.function);
        let reason = if !load.direct_projection {
            Some(Pending::IndirectAccess)
        } else if load.shared_reference_root {
            match reader {
                None => Some(Pending::SharedReference),
                Some(reader) if !reader.returned_parameters.is_empty() => {
                    Some(Pending::BorrowedReturnRoleC)
                }
                Some(_) => None,
            }
        } else {
            None
        };
        if let Some(reason) = reason {
            proof.holds.push(Hold {
                site: Some(load.site.clone()),
                construction: None,
                reason,
            });
        }
    }
    for store in &inputs.stores {
        let Some(proof) = fields.get_mut(&store.site.field_key) else { continue };
        let mut hold = |construction, reason| {
            proof.holds.push(Hold {
                site: Some(store.site.clone()),
                construction,
                reason,
            })
        };
        if !store.direct_projection {
            hold(None, Pending::IndirectAccess);
            continue;
        }
        let source = match &store.value {
            StoredValue::Null => {
                proof.null_stores.push(store.site.clone());
                continue;
            }
            StoredValue::Unknown => {
                hold(None, Pending::UnknownStore);
                continue;
            }
            StoredValue::Value(source) => source,
        };
        for construction in 0..facts.constructions {
            let scoped = |point: &super::super::ownership_evidence::Point| {
                point.construction == construction
                    && point.function.as_ref() == Some(&store.site.function)
            };
            let equations: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| scoped(&row.point))
                .cloned()
                .collect();
            let consumes: Vec<_> = facts
                .consumes
                .iter()
                .filter(|row| scoped(&row.point))
                .cloned()
                .collect();
            if super::coverage::validate_returns(facts, construction, &store.site.function).is_err()
                || ownership_occurrence::validate(&store.site.function, &consumes, &equations)
                    .is_err()
            {
                hold(Some(construction), Pending::Coverage);
                continue;
            }
            let transfers: Vec<_> = equations.iter().filter_map(|equation| {
                if equation.point.block != Some(store.site.block) || equation.point.statement != Some(store.site.statement)
                    || !matches!(equation.operation.as_str(), "linear" | "equal") || equation.validate().is_err() { return None; }
                let transfer = equation.transfer.as_ref()?;
                let (Availability::Present(destination), Availability::Present(rhs)) = (&transfer.destination, &transfer.source) else { return None; };
                if destination.local != store.site.place.local || destination.projection != store.site.place.projection
                    || rhs.local != source.local || rhs.projection != source.projection { return None; }
                if !matches!(destination.path.last(), Some(ownership_occurrence::PathStep::Field { structure, index, .. })
                    if format!("{structure}::field{index}@d0") == store.site.field_key) { return None; }
                let head = |id, use_var, def_var| consumes.iter().any(|consume| consume.ordinal == id
                    && matches!(&consume.projected, Availability::Present(window) if window.use_start == use_var && window.def_start == def_var));
                (head(destination.consume, transfer.destination_use, transfer.destination_def)
                    && head(rhs.consume, transfer.source_use, transfer.source_def)).then_some((equation, transfer))
            }).collect();
            if transfers.len() != 1 {
                hold(Some(construction), Pending::TransferBinding);
                continue;
            }
            let (equation, transfer) = transfers[0];
            let node = |var| Node { construction, var };
            let atoms = origins.at(node(transfer.source_use));
            if atoms == BTreeSet::from([OriginAtom::Null]) {
                // A proven None may arrive through a temporary or aggregate
                // operand. It supplies no source token or positive field grant.
                if !proof.null_stores.contains(&store.site) {
                    proof.null_stores.push(store.site.clone());
                }
                continue;
            }
            if !atoms.is_empty()
                && atoms
                    .iter()
                    .all(|atom| matches!(atom, OriginAtom::Input(_)))
            {
                let id = EquationId {
                    construction,
                    ordinal: equation.ordinal,
                };
                let (input, reasons) =
                    input_store(facts, matched, origins, &store.site, id, transfer, &atoms);
                for reason in reasons {
                    hold(Some(construction), reason);
                }
                proof.input_stores.push(input);
                continue;
            }
            let fresh: BTreeSet<_> = atoms
                .iter()
                .filter_map(|atom| {
                    if let OriginAtom::Fresh(id) = atom {
                        Some(*id)
                    } else {
                        None
                    }
                })
                .collect();
            if fresh.is_empty()
                || !atoms
                    .iter()
                    .all(|atom| matches!(atom, OriginAtom::Fresh(_) | OriginAtom::Null))
            {
                hold(Some(construction), Pending::OwnedInputOrOriginC);
                continue;
            }
            let meets = matched.meets_for(node(transfer.destination_def));
            let field_certificates: Vec<_> = certificates
                .iter()
                .filter(|certificate| {
                    certificate.field_key == store.site.field_key
                        && certificate.call.construction == construction
                        && certificate.call.caller == store.site.function
                })
                .cloned()
                .collect();
            let (meet, mut discharged_outputs, mut traversal_outputs) = match select_terminal(
                facts,
                matched.guard_aliases(),
                &meets,
                &field_certificates,
            ) {
                Ok(selected) => selected,
                Err(reason) => {
                    hold(Some(construction), reason);
                    continue;
                }
            };
            if !matches!(meet.source.lineage, SourceLineage::Exact(_))
                || !matches!(meet.terminal.lineage, SourceLineage::Exact(_))
            {
                hold(Some(construction), Pending::RecursiveIdentityC);
                continue;
            }
            if fresh != BTreeSet::from([meet.source.endpoint]) {
                hold(Some(construction), Pending::OwnedInputOrOriginC);
                continue;
            }
            // Inspect all candidates, never selected sinks: a retracted partner
            // free is still a competing destruction/escape responsibility.
            let seeds = matched.source_nodes(construction, &store.site.function, &meet.source);
            if seeds.is_empty() {
                hold(Some(construction), Pending::RecursiveIdentityC);
                continue;
            }
            let mut competing = false;
            for other in seeds.into_iter().flat_map(|seed| matched.meets_for(seed)) {
                if other.source != meet.source {
                    competing = true;
                    break;
                }
                if other.terminal == meet.terminal {
                    continue;
                }
                // No free is discharged, including one with a different or
                // conflicting selector. Only this same free's exact zeroed
                // projected output is eligible for a conditional receipt.
                if matches!(other.terminal.target, TerminalTarget::Free(_)) {
                    competing = true;
                    break;
                }
                if let Some(receipt) = discharge_output(&other, &meet, &field_certificates) {
                    if !discharged_outputs.contains(&receipt) {
                        discharged_outputs.push(receipt);
                    }
                } else if let Some(receipt) = super::traversal_discharge::certify(
                    facts,
                    &other,
                    &meet,
                    matched.guard_aliases(),
                ) {
                    if !traversal_outputs.contains(&receipt) {
                        traversal_outputs.push(receipt);
                    }
                } else {
                    competing = true;
                    break;
                }
            }
            if competing {
                hold(Some(construction), Pending::CompetingTerminal);
                continue;
            }
            proof.stores.push(StoreProof {
                site: store.site.clone(),
                equation: EquationId {
                    construction,
                    ordinal: equation.ordinal,
                },
                destination_use: node(transfer.destination_use),
                destination_def: node(transfer.destination_def),
                source_use: node(transfer.source_use),
                source_def: node(transfer.source_def),
                by_move: transfer.by_move,
                meet,
                discharged_outputs,
                traversal_outputs,
            });
        }
    }
    for proof in fields.values_mut() {
        if proof.stores.is_empty() && proof.input_stores.is_empty() {
            proof.holds.push(Hold {
                site: None,
                construction: None,
                reason: Pending::EmptyOwnedSupport,
            });
        }
    }
    // R388-1: classify the source origin of every store the owned path held with
    // `OwnedInputOrOriginC`. The classification is recorded; whether it licenses
    // anything is the solver's, under the pin.
    for proof in fields.values_mut() {
        let held: Vec<Site> = proof
            .holds
            .iter()
            .filter(|hold| hold.reason == Pending::OwnedInputOrOriginC)
            .filter_map(|hold| hold.site.clone())
            .collect();
        for site in held {
            let origin = classify_store_source(facts, origins, &site);
            proof.classified.push(ClassifiedStore { site, origin });
        }
    }
    fields.into_values().collect()
}

/// R388-1: the origin of the value a store puts into a field, from the recorded
/// consume rows and `ValueOrigins`. `Input` and `FieldToken` name the slot the
/// solver must tie the support to; anything the origins do not resolve is
/// `Unknown` and never supported.
fn classify_store_source(facts: &Facts, origins: &ValueOrigins, site: &Site) -> StoreSourceOrigin {
    use super::super::ownership_boundary::{Role, Variables};
    let Some(store) = facts.field_support_inputs.stores.iter().find(|store| {
        store.site.function == site.function
            && store.site.block == site.block
            && store.site.statement == site.statement
            && store.site.field_key == site.field_key
    }) else {
        return StoreSourceOrigin::Unknown;
    };
    let StoredValue::Value(place) = &store.value else {
        return StoreSourceOrigin::Null;
    };
    let nodes: Vec<Node> = facts
        .consumes
        .iter()
        .filter(|consume| {
            consume.point.function.as_deref() == Some(site.function.as_str())
                && consume.point.block == Some(site.block)
                && consume.point.statement == Some(site.statement)
                && consume.local == place.local
                && consume.projection == place.projection
        })
        .filter_map(|consume| match &consume.projected {
            Availability::Present(window) if window.use_start != window.use_end => Some(Node {
                construction: consume.point.construction,
                var: window.use_start,
            }),
            _ => None,
        })
        .collect();
    let [node] = nodes.as_slice() else {
        return StoreSourceOrigin::Unknown;
    };
    let atoms = origins.at(*node);
    if std::env::var("CRAT_R388_DEBUG").is_ok() {
        eprintln!(
            "R388CLASS {} {}:{} node={} atoms={atoms:?}",
            site.function, site.block, site.statement, node.var
        );
    }
    if atoms.iter().all(|atom| matches!(atom, OriginAtom::Null)) {
        return StoreSourceOrigin::Null;
    }
    // The formal port an `Input`/`UnresolvedInput` names, mapped to the callee's
    // parameter slot through the entry substitution's own `formal_local`.
    let parameter = |port: Node| -> Option<String> {
        facts.boundary_substitutions.iter().find_map(|row| {
            (row.role == Role::Entry
                && row.point.construction == port.construction
                && row.matched.iter().any(
                    |pair| matches!(pair.formal, Variables::Single { var } if var == port.var),
                ))
            .then(|| {
                Some(format!(
                    "{}::_{}@d0",
                    row.point.function.as_deref()?,
                    row.formal_local?
                ))
            })
            .flatten()
        })
    };
    let mut origin = StoreSourceOrigin::Fresh;
    for atom in &atoms {
        match atom {
            OriginAtom::Fresh(_) | OriginAtom::Null => {}
            OriginAtom::Input(port)
            | OriginAtom::UnresolvedInput { formal: port, .. }
            | OriginAtom::UnclassifiedInput { formal: port, .. } => {
                match (parameter(*port), &origin) {
                    // An argument arrives as its pointer COMPONENTS — report 042's
                    // entry window — so several `Input` atoms naming one parameter
                    // are one token, not several.
                    (Some(key), StoreSourceOrigin::Fresh) => {
                        origin = StoreSourceOrigin::Input(key);
                    }
                    (Some(key), StoreSourceOrigin::Input(existing)) if &key == existing => {}
                    // Two distinct parameters, or a port with no entry row.
                    _ => return StoreSourceOrigin::Unknown,
                }
            }
            // A token the origins could not resolve MAY be a field load: fields
            // are not origin-tracked, so a value read out of one arrives here as
            // `Unknown`. The loads table says whether it was, and from which
            // field. Anything else stays `Unknown`.
            OriginAtom::Unknown(port) => {
                let loaded: BTreeSet<String> = facts
                    .field_support_inputs
                    .loads
                    .iter()
                    .filter(|load| {
                        load.site.function == site.function
                            && facts.consumes.iter().any(|consume| {
                                consume.point.function.as_deref() == Some(site.function.as_str())
                                    && consume.point.block == Some(load.site.block)
                                    && consume.point.statement == Some(load.site.statement)
                                    && consume.point.construction == port.construction
                                    && matches!(
                                        &consume.projected,
                                        Availability::Present(window)
                                            if window.def_start == port.var
                                    )
                            })
                    })
                    .map(|load| load.site.field_key.clone())
                    .collect();
                match (loaded.len(), &origin) {
                    (1, StoreSourceOrigin::Fresh) => {
                        origin = StoreSourceOrigin::FieldToken(
                            loaded.into_iter().next().expect("one field"),
                        );
                    }
                    _ => return StoreSourceOrigin::Unknown,
                }
            }
            _ => return StoreSourceOrigin::Unknown,
        }
    }
    origin
}
