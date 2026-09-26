//! Static reader roles over original compiler occurrences. These are candidates
//! for guarded refinement, not accepted borrow/protector proofs.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::super::{
    origin_evidence::{OriginAvailability, SourceCallee, SourceOccurrence},
    ownership_access::{Expression, ImmediateOrigin, OperandSyntax, PlaceSyntax},
};

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Inputs {
    pub(crate) bodies: Vec<Body>,
    pub(crate) field_keys: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Body {
    pub(crate) function: String,
    pub(crate) argument_count: usize,
    pub(crate) pointer_locals: BTreeSet<u32>,
    pub(crate) raw_locals: BTreeSet<u32>,
    pub(crate) reachable: BTreeSet<u32>,
    pub(crate) occurrences: Vec<SourceOccurrence>,
    pub(crate) readonly_intrinsics: BTreeSet<(u32, usize)>,
    /// Exact compiler diagnostic-item calls with no arguments and usize result.
    /// Separate from pointer reader permissions.
    pub(crate) size_of_calls: BTreeSet<(u32, usize)>,
    pub(crate) complete_operations: bool,
    /// Aggregate/function-pointer outputs require an explicit escape contract.
    pub(crate) scalar_or_pointer_return: bool,
}

impl Body {
    /// R337-2(b): THE read-only-intrinsic test. Every gate that needs to know
    /// whether a call at a site only reads asks this one question, so the gates
    /// cannot drift apart again — `check_effects` refusing an `is_null` that
    /// `fold_internal` admits is exactly what held OL01-OL03.
    pub(crate) fn readonly_intrinsic(&self, block: u32, statement: usize) -> bool {
        self.readonly_intrinsics.contains(&(block, statement))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ReaderFunction {
    pub(crate) function: String,
    pub(crate) parameters: Vec<u32>,
    pub(crate) returned_parameters: Vec<u32>,
    /// The return may be a proper descendant of a parameter rather than the
    /// parameter itself — a view. `minValue` walking to its deepest child is
    /// one; `fn step(node) { node }` is not.
    #[serde(default)]
    pub(crate) view_return: bool,
    pub(crate) replay_required: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Candidate {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) field_key: String,
    pub(crate) source: PlaceSyntax,
    pub(crate) destination: PlaceSyntax,
    pub(crate) origin_parameter: u32,
    pub(crate) replay_required: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Plan {
    pub(crate) functions: Vec<ReaderFunction>,
    pub(crate) candidates: Vec<Candidate>,
}

impl Plan {
    /// The initial call contract has no pointer output. A readonly identity
    /// return alone does not distinguish borrowing from transferring an owner.
    pub(crate) fn borrows_parameter(&self, function: &str, index: usize) -> bool {
        self.functions.iter().any(|row| {
            row.function == function
                && row.returned_parameters.is_empty()
                && row.parameters.contains(&((index + 1) as u32))
        })
    }

    /// R335-4: a borrowing parameter with a VIEW return LENDS. The function is a
    /// reader — it performs no store and no free anywhere, which is what reader
    /// eligibility already establishes — and what it hands back is a proper
    /// descendant of this parameter, not the parameter itself. The caller keeps
    /// its token across such a call and receives a view.
    pub(crate) fn lends_parameter(&self, function: &str, index: usize) -> bool {
        self.functions.iter().any(|row| {
            row.function == function
                && row.view_return
                && row.returned_parameters.contains(&((index + 1) as u32))
                && row.parameters.contains(&((index + 1) as u32))
        })
    }
}

/// Equality alone does not authenticate a non-owning callee signature.
pub(crate) fn validate_call_roles(facts: &super::facts::Facts) -> Result<(), String> {
    use super::super::{
        ownership_boundary::{LicensingRole, Role, Window},
        ownership_occurrence::Availability::Present,
    };
    let zero = |point: &super::super::ownership_evidence::Point, var| {
        facts.equations.iter().any(|row| {
            &row.point == point
                && row.operation == "assume"
                && row.value == Some(false)
                && row.variables == [var]
        })
    };
    for call in facts
        .boundary_substitutions
        .iter()
        .filter(|row| row.licensing_role == LicensingRole::Borrowed)
    {
        let (Some(callee), Some(index)) = (&call.callee, call.argument_index) else {
            return Err("borrowed call has no target parameter".into());
        };
        if !facts.reader_plan.borrows_parameter(callee, index) {
            return Err("borrowed call has no complete readonly body contract".into());
        }
        let entries: Vec<_> = facts
            .boundary_substitutions
            .iter()
            .filter(|row| {
                row.role == Role::Entry
                    && row.point.function.as_ref() == Some(callee)
                    && row.point.construction == call.point.construction
                    && row.argument_index == Some(index)
            })
            .collect();
        if entries.len() != 1 {
            return Err("borrowed call has no unique callee entry".into());
        }
        let formal = call
            .reference_peel
            .as_ref()
            .map(|peel| &peel.original_formal)
            .or_else(|| match &call.formal {
                Present(formal) => Some(formal),
                _ => None,
            });
        let Some(Window::UseDef {
            use_start,
            use_end,
            def_start,
            def_end,
        }) = formal
        else {
            return Err("borrowed call has no full formal window".into());
        };
        if !(*use_start..*use_end)
            .chain(*def_start..*def_end)
            .all(|var| zero(&call.point, var))
        {
            return Err("borrowed call signature lost its zero-view obligation".into());
        }
        if entries[0].formal
            != Present(Window::Single {
                start: *use_start,
                end: *use_end,
            })
        {
            return Err("borrowed call input differs from its callee entry".into());
        }
        for output in facts.boundary_substitutions.iter().filter(|row| {
            row.role == Role::ExitOutput
                && row.point.function.as_ref() == Some(callee)
                && row.point.construction == call.point.construction
                && row.argument_index == Some(index)
        }) {
            if output.formal
                != Present(Window::Single {
                    start: *def_start,
                    end: *def_end,
                })
            {
                return Err("borrowed call output differs from its callee exit".into());
            }
        }
    }
    Ok(())
}

impl Inputs {
    pub(crate) fn collect(
        program: &crate::utils::rustc::RustProgram<'_>,
        slots: &super::super::crate_slots::CrateSlots,
    ) -> Self {
        use rustc_middle::mir::{StatementKind, TerminatorKind};

        use crate::analyses::mir::{CallKind, TerminatorExt};
        let mut bodies = Vec::new();
        for &function in &program.functions {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let name = program.tcx.def_path_str(function);
            let pointer_locals = body
                .local_decls
                .iter_enumerated()
                .filter(|(_, local)| local.ty.is_raw_ptr() || local.ty.is_ref())
                .map(|(local, _)| local.as_u32())
                .collect();
            let raw_locals = body
                .local_decls
                .iter_enumerated()
                .filter(|(_, local)| local.ty.is_raw_ptr())
                .map(|(local, _)| local.as_u32())
                .collect();
            let return_ty = body.local_decls[rustc_middle::mir::RETURN_PLACE].ty;
            let scalar_or_pointer_return = return_ty.is_unit()
                || matches!(
                    return_ty.kind(),
                    rustc_middle::ty::TyKind::RawPtr(..)
                        | rustc_middle::ty::TyKind::Ref(..)
                        | rustc_middle::ty::TyKind::Bool
                        | rustc_middle::ty::TyKind::Char
                        | rustc_middle::ty::TyKind::Int(..)
                        | rustc_middle::ty::TyKind::Uint(..)
                        | rustc_middle::ty::TyKind::Float(..)
                );
            let mut reachable = BTreeSet::new();
            let mut pending = vec![rustc_middle::mir::START_BLOCK];
            while let Some(block) = pending.pop() {
                if reachable.insert(block.as_u32()) {
                    pending.extend(body.basic_blocks[block].terminator().successors());
                }
            }
            let mut complete_operations = true;
            let mut readonly_intrinsics = BTreeSet::new();
            let mut size_of_calls = BTreeSet::new();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                if !reachable.contains(&block.as_u32()) {
                    continue;
                }
                for statement in &data.statements {
                    if !matches!(
                        statement.kind,
                        StatementKind::Assign(..)
                            | StatementKind::StorageLive(..)
                            | StatementKind::StorageDead(..)
                            | StatementKind::Nop
                            | StatementKind::FakeRead(..)
                            | StatementKind::AscribeUserType(..)
                    ) {
                        complete_operations = false;
                    }
                }
                if !matches!(
                    data.terminator().kind,
                    TerminatorKind::Goto { .. }
                        | TerminatorKind::SwitchInt { .. }
                        | TerminatorKind::Return
                        | TerminatorKind::Call { .. }
                        | TerminatorKind::Assert { .. }
                        | TerminatorKind::Unreachable
                ) {
                    complete_operations = false;
                }
                if let Some(call) = data.terminator().as_call(program.tcx) {
                    if let CallKind::RustLib(callee) = call.func {
                        if program
                            .tcx
                            .is_diagnostic_item(rustc_span::Symbol::intern("mem_size_of"), callee)
                            && call.args.is_empty()
                            && call.destination.projection.is_empty()
                            && body.local_decls[call.destination.local].ty
                                == program.tcx.types.usize
                        {
                            size_of_calls.insert((block.as_u32(), data.statements.len()));
                        }
                        let krate = program.tcx.crate_name(callee.krate);
                        if matches!(krate.as_str(), "core" | "std")
                            && program.tcx.item_name(callee).as_str() == "is_null"
                            && !body.local_decls[call.destination.local].ty.is_raw_ptr()
                        {
                            readonly_intrinsics.insert((block.as_u32(), data.statements.len()));
                        }
                    }
                }
            }
            bodies.push(Body {
                function: name,
                argument_count: body.arg_count,
                pointer_locals,
                raw_locals,
                reachable,
                occurrences: super::super::origin_evidence::occurrences(program, slots, function),
                readonly_intrinsics,
                size_of_calls,
                complete_operations,
                scalar_or_pointer_return,
            });
        }
        bodies.sort_by(|a, b| a.function.cmp(&b.function));
        let mut field_keys = BTreeSet::new();
        for index in 0..slots.field_slots.len() {
            let id = super::super::slots::SlotId::from_u32(index as u32);
            let slot = slots.field_slots.slot(id);
            let super::super::slots::SlotOwner::Field(field) = slot.owner else { unreachable!() };
            if slot.depth == 0 && !slots.field_slots.is_array_slot(id) {
                field_keys.insert(super::super::slot_key::field_key(
                    program.tcx,
                    field.struct_did,
                    field.field_index,
                    0,
                ));
            }
        }
        Self { bodies, field_keys }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Origins {
    parameters: BTreeSet<u32>,
    unknown: bool,
    empty: bool,
    /// Did any step of the derivation descend through a field? A value rooted
    /// in a parameter may be the parameter ITSELF or a proper descendant of it,
    /// and the two are not interchangeable at a call boundary: returning the
    /// parameter hands back the same token, returning a descendant hands back a
    /// view into it. `parameters` alone deliberately conflates them.
    projected: bool,
}
impl Origins {
    fn unknown() -> Self {
        Self {
            unknown: true,
            ..Self::default()
        }
    }

    fn union(&mut self, other: &Self) -> bool {
        let before = self.clone();
        self.parameters.extend(&other.parameters);
        self.unknown |= other.unknown;
        self.empty |= other.empty;
        self.projected |= other.projected;
        *self != before
    }

    fn rooted(&self) -> bool {
        !self.unknown && !self.parameters.is_empty()
    }
}

fn place_origin(place: &PlaceSyntax, values: &BTreeMap<u32, Origins>) -> Origins {
    // A field descendant remains rooted in the input object; arbitrary index,
    // downcast and other projections require a different proof.
    use super::super::export::ProjKey;
    if place
        .projection
        .iter()
        .any(|projection| !matches!(projection, ProjKey::Deref | ProjKey::Field(_)))
    {
        return Origins::unknown();
    }
    let mut origins = values.get(&place.local).cloned().unwrap_or_default();
    // A field step is what makes this a descendant rather than the object
    // itself. A bare deref is not: it names the same object.
    origins.projected |= place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjKey::Field(_)));
    origins
}

fn origin(
    body: &Body,
    occurrence: &SourceOccurrence,
    values: &BTreeMap<u32, Origins>,
    returns: &BTreeMap<String, Origins>,
) -> Origins {
    if occurrence.syntax.immediate_origin == ImmediateOrigin::Null {
        return Origins {
            empty: true,
            ..Origins::default()
        };
    }
    match &occurrence.syntax.expression {
        Expression::Value {
            operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
        }
        | Expression::CopyForDeref { place } => place_origin(place, values),
        Expression::Cast {
            operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
            ..
        } if occurrence.syntax.immediate_origin == ImmediateOrigin::Transfer => {
            place_origin(place, values)
        }
        Expression::Call { operands } => {
            let Some(SourceCallee::Local(callee)) = &occurrence.callee else {
                return Origins::unknown();
            };
            let Some(summary) = returns.get(callee) else { return Origins::default() };
            let mut result = Origins {
                unknown: summary.unknown,
                empty: summary.empty,
                projected: summary.projected,
                ..Origins::default()
            };
            for &parameter in &summary.parameters {
                match operands.get(parameter as usize - 1) {
                    Some(OperandSyntax::Copy { place } | OperandSyntax::Move { place }) => {
                        result.union(&place_origin(place, values));
                    }
                    Some(OperandSyntax::Constant { zero: true, .. }) => result.empty = true,
                    _ => result.unknown = true,
                }
            }
            result
        }
        _ => {
            let _ = body;
            Origins::unknown()
        }
    }
}

impl Plan {
    pub(crate) fn build(inputs: &Inputs) -> Self {
        let mut returns: BTreeMap<String, Origins> = inputs
            .bodies
            .iter()
            .map(|body| (body.function.clone(), Origins::default()))
            .collect();
        let mut all_values = BTreeMap::new();
        let mut unresolved = BTreeSet::new();
        loop {
            let mut changed = false;
            all_values.clear();
            for body in &inputs.bodies {
                let mut values: BTreeMap<_, _> = body
                    .pointer_locals
                    .iter()
                    .filter(|&&local| local > 0 && local as usize <= body.argument_count)
                    .map(|&local| {
                        (
                            local,
                            Origins {
                                parameters: BTreeSet::from([local]),
                                ..Origins::default()
                            },
                        )
                    })
                    .collect();
                for &(ref function, local) in &unresolved {
                    if function == &body.function {
                        values.entry(local).or_default().unknown = true;
                    }
                }
                loop {
                    let mut local_changed = false;
                    for occurrence in body.occurrences.iter().filter(|row| {
                        body.reachable.contains(&row.site.block)
                            && row.syntax.destination.projection.is_empty()
                            && body.pointer_locals.contains(&row.syntax.destination.local)
                    }) {
                        let incoming = origin(body, occurrence, &values, &returns);
                        local_changed |= values
                            .entry(occurrence.syntax.destination.local)
                            .or_default()
                            .union(&incoming);
                    }
                    if !local_changed {
                        break;
                    }
                }
                if body.pointer_locals.contains(&0) {
                    changed |= returns
                        .get_mut(&body.function)
                        .unwrap()
                        .union(&values.get(&0).cloned().unwrap_or_default());
                }
                all_values.insert(body.function.clone(), values);
            }
            if changed {
                continue;
            }
            let before = unresolved.len();
            for body in &inputs.bodies {
                for &local in &body.pointer_locals {
                    let value = all_values[&body.function]
                        .get(&local)
                        .cloned()
                        .unwrap_or_default();
                    if value == Origins::default() {
                        unresolved.insert((body.function.clone(), local));
                    }
                }
            }
            if unresolved.len() == before {
                break;
            }
        }
        let mut eligible: BTreeSet<String> = inputs
            .bodies
            .iter()
            .filter(|body| body.complete_operations && body.scalar_or_pointer_return)
            .map(|body| body.function.clone())
            .collect();
        loop {
            let before = eligible.len();
            for body in &inputs.bodies {
                if !eligible.contains(&body.function) {
                    continue;
                }
                let values = &all_values[&body.function];
                let returned = &returns[&body.function];
                let mut supported = !body.pointer_locals.contains(&0)
                    || (!returned.unknown && (returned.rooted() || returned.empty));
                for occurrence in body
                    .occurrences
                    .iter()
                    .filter(|row| body.reachable.contains(&row.site.block))
                {
                    if !occurrence.syntax.destination.projection.is_empty() {
                        supported = false;
                    }
                    if matches!(
                        occurrence.syntax.expression,
                        Expression::Borrow { .. }
                            | Expression::RawAddress { .. }
                            | Expression::Aggregate { .. }
                    ) {
                        // Native reference inputs are supported; creating an address
                        // needs an additional exact borrow-place proof, held here.
                        supported = false;
                    }
                    if let Expression::Cast {
                        operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
                        ..
                    } = &occurrence.syntax.expression
                    {
                        if body.pointer_locals.contains(&place.local)
                            && (occurrence.syntax.immediate_origin != ImmediateOrigin::Transfer
                                || !body
                                    .pointer_locals
                                    .contains(&occurrence.syntax.destination.local))
                        {
                            supported = false;
                        }
                    }
                    if let Some(callee) = &occurrence.callee {
                        supported &= match callee {
                            SourceCallee::Local(name) => eligible.contains(name),
                            SourceCallee::RustLibrary(_) => body.readonly_intrinsic(
                                occurrence.site.block,
                                occurrence.site.statement,
                            ),
                            _ => false,
                        };
                    }
                    if body
                        .pointer_locals
                        .contains(&occurrence.syntax.destination.local)
                        && occurrence.syntax.destination.projection.is_empty()
                    {
                        let value = values
                            .get(&occurrence.syntax.destination.local)
                            .cloned()
                            .unwrap_or_default();
                        supported &= !value.unknown && (value.rooted() || value.empty);
                    }
                }
                if !supported {
                    eligible.remove(&body.function);
                }
            }
            if eligible.len() == before {
                break;
            }
        }
        let mut plan = Self::default();
        for body in &inputs.bodies {
            if !eligible.contains(&body.function) {
                continue;
            }
            let parameters: Vec<_> = body
                .pointer_locals
                .iter()
                .copied()
                .filter(|&local| local > 0 && local as usize <= body.argument_count)
                .collect();
            if parameters.is_empty() {
                continue;
            }
            plan.functions.push(ReaderFunction {
                function: body.function.clone(),
                parameters,
                returned_parameters: returns[&body.function].parameters.iter().copied().collect(),
                view_return: returns[&body.function].projected,
                replay_required: true,
            });
            for occurrence in body.occurrences.iter().filter(|row| {
                body.reachable.contains(&row.site.block)
                    && row.syntax.destination.projection.is_empty()
                    && body.raw_locals.contains(&row.syntax.destination.local)
            }) {
                let source = match &occurrence.syntax.expression {
                    Expression::Value {
                        operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
                    }
                    | Expression::CopyForDeref { place } => place,
                    _ => continue,
                };
                let Some(OriginAvailability::Present(field_key)) = occurrence.arguments.first()
                else {
                    continue;
                };
                if !inputs.field_keys.contains(field_key) || source.projection.is_empty() {
                    continue;
                }
                let roots = place_origin(source, &all_values[&body.function]);
                if roots.unknown || roots.parameters.len() != 1 {
                    continue;
                }
                plan.candidates.push(Candidate {
                    function: body.function.clone(),
                    block: occurrence.site.block,
                    statement: occurrence.site.statement,
                    field_key: field_key.clone(),
                    source: source.clone(),
                    destination: occurrence.syntax.destination.clone(),
                    origin_parameter: *roots.parameters.first().unwrap(),
                    replay_required: true,
                });
            }
        }
        plan
    }
}

/// The same kind-derived predicate is reconstructed at the SSA and coherence
/// seams. Exact MIR places and compiler-resolved slots authenticate the site.
pub(crate) fn guards_for_body(
    facts: &super::facts::Facts,
    solver: &super::super::solver::KindSolver,
    function: rustc_span::def_id::LocalDefId,
    body: &rustc_middle::mir::Body<'_>,
) -> rustc_hash::FxHashMap<rustc_middle::mir::Location, z3::ast::Bool> {
    use rustc_middle::mir::{BasicBlock, Location, Operand, Rvalue, StatementKind};

    use super::super::solver::SlotRef;
    let mut guards = rustc_hash::FxHashMap::default();
    for candidate in &facts.reader_plan.candidates {
        let key = format!(
            "{}::_{}@d0",
            candidate.function, candidate.destination.local
        );
        let (Some(&lhs @ SlotRef::Local(owner, _)), Some(&rhs @ SlotRef::Field(_))) = (
            facts.slot_refs.get(&key),
            facts.slot_refs.get(&candidate.field_key),
        ) else {
            continue;
        };
        if owner != function {
            continue;
        }
        let location = Location {
            block: BasicBlock::from_u32(candidate.block),
            statement_index: candidate.statement,
        };
        let Some(statement) = body
            .basic_blocks
            .get(location.block)
            .and_then(|data| data.statements.get(location.statement_index))
        else {
            continue;
        };
        // CopyForDeref and erased argument proxies need their own view record;
        // they do not gain the actual-transfer arm through a coincident site.
        let StatementKind::Assign(box (
            destination,
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source)),
        )) = &statement.kind
        else {
            continue;
        };
        if PlaceSyntax::from(*destination) != candidate.destination
            || PlaceSyntax::from(*source) != candidate.source
        {
            continue;
        }
        guards.insert(location, solver.lend_guard(lhs, rhs));
    }
    guards
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TransferProof {
    pub(crate) construction: u32,
    pub(crate) candidate: Candidate,
    pub(crate) coverage:
        super::super::ownership_occurrence::Availability<Vec<super::facts::EquationId>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Components {
    pairs: BTreeSet<(u32, u32)>,
    source_tails: BTreeSet<(u32, u32)>,
    destination_tails: BTreeSet<(u32, u32)>,
}

fn components(
    source: &super::super::ownership_occurrence::Consumption,
    destination: &super::super::ownership_occurrence::Consumption,
) -> Result<Components, String> {
    use super::super::ownership_occurrence::{Availability::Present, Consumption, PathStep};
    // The source and destination have the same value type at a certified
    // field-load Use. Match relative type paths, independently of emitted
    // equations: the structural matcher may skip deeper ADT components.
    let paths = |consume: &Consumption| -> Result<BTreeMap<Vec<PathStep>, (u32, u32)>, String> {
        let (Present(base), Present(projected), Present(paths)) =
            (&consume.base, &consume.projected, &consume.pointer_paths)
        else {
            return Err("reader component paths unavailable".into());
        };
        let Some(head) = paths.get((projected.use_start - base.use_start) as usize) else {
            return Err("empty reader window".into());
        };
        let mut result = BTreeMap::new();
        for offset in 0..projected.use_end - projected.use_start {
            let path = paths
                .get((projected.use_start - base.use_start + offset) as usize)
                .and_then(|path| path.strip_prefix(head.as_slice()))
                .ok_or("reader component outside projected value")?;
            if result
                .insert(
                    path.to_vec(),
                    (projected.use_start + offset, projected.def_start + offset),
                )
                .is_some()
            {
                return Err("duplicate reader component path".into());
            }
        }
        Ok(result)
    };
    let source = paths(source)?;
    let destination = paths(destination)?;
    let mut result = Components {
        pairs: BTreeSet::new(),
        source_tails: BTreeSet::new(),
        destination_tails: BTreeSet::new(),
    };
    for (path, &(pre, post)) in &source {
        if let Some(&(_, destination_post)) = destination.get(path) {
            result.pairs.insert((pre, destination_post));
        } else {
            result.source_tails.insert((post, pre));
        }
    }
    for (path, &(pre, post)) in &destination {
        if !source.contains_key(path) {
            result.destination_tails.insert((post, pre));
        }
    }
    if result.pairs.is_empty() {
        return Err("reader has no common component".into());
    }
    Ok(result)
}

/// Authenticate the actual matched window. A reader-only syntactic candidate
/// cannot enable the kind alternative if SSA erased or failed to represent it.
pub(crate) fn audit_transfers(
    facts: &super::facts::Facts,
    aliases: &BTreeMap<super::facts::EquationId, super::facts::EquationId>,
) -> Vec<TransferProof> {
    use super::{
        super::ownership_occurrence::Availability::{Missing, Present},
        facts::EquationId,
    };
    let mut result = Vec::new();
    for construction in 0..facts.constructions {
        for candidate in &facts.reader_plan.candidates {
            let scope = |point: &super::super::ownership_evidence::Point| {
                point.construction == construction
                    && point.function.as_ref() == Some(&candidate.function)
            };
            let site = |point: &super::super::ownership_evidence::Point| {
                scope(point)
                    && point.block == Some(candidate.block)
                    && point.statement == Some(candidate.statement)
            };
            let consumes: Vec<_> = facts
                .consumes
                .iter()
                .filter(|row| scope(&row.point))
                .cloned()
                .collect();
            let equations: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| scope(&row.point))
                .cloned()
                .collect();
            let coverage = (|| {
                super::super::ownership_occurrence::validate(
                    &candidate.function,
                    &consumes,
                    &equations,
                )?;
                let rows: Vec<_> = equations
                    .iter()
                    .filter(|row| {
                        site(&row.point)
                            && matches!(
                                row.operation.as_str(),
                                "guarded-reader-copy" | "guarded-reader-move"
                            )
                    })
                    .collect();
                if rows.is_empty() {
                    return Err(
                        "reader transfer was not represented (including erased proxies)".into(),
                    );
                }
                let mut pairs = BTreeSet::new();
                let mut guards = BTreeSet::new();
                let mut expected = None;
                let mut ids = Vec::new();
                for row in rows {
                    let transfer = row
                        .transfer
                        .as_ref()
                        .ok_or("reader has no transfer binding")?;
                    let (Present(source), Present(destination)) =
                        (&transfer.source, &transfer.destination)
                    else {
                        return Err("reader transfer has missing occurrence bindings".into());
                    };
                    if source.local != candidate.source.local
                        || source.projection != candidate.source.projection
                        || destination.local != candidate.destination.local
                        || destination.projection != candidate.destination.projection
                    {
                        return Err("reader transfer belongs to different places".into());
                    }
                    let find = |ordinal| {
                        consumes
                            .iter()
                            .find(|consume| consume.ordinal == ordinal && site(&consume.point))
                    };
                    let (Some(source_consume), Some(destination_consume)) =
                        (find(source.consume), find(destination.consume))
                    else {
                        return Err("reader consumes are not at its actual site".into());
                    };
                    let shape = components(source_consume, destination_consume)?;
                    if expected
                        .replace(shape.clone())
                        .is_some_and(|old| old != shape)
                        || !pairs.insert((source.use_var, destination.def_var))
                    {
                        return Err("reader window coverage is ambiguous".into());
                    }
                    if !equations.iter().any(|old| {
                        old.point == row.point
                            && old.transfer.as_ref() == Some(transfer)
                            && old.operation == "assume"
                            && old.value == Some(false)
                            && old.variables == [transfer.destination_use]
                    }) {
                        return Err("reader lost destination-old-zero".into());
                    }
                    let id = EquationId {
                        construction,
                        ordinal: row.ordinal,
                    };
                    guards.insert(
                        *aliases
                            .get(&id)
                            .ok_or("reader lacks its actual guard identity")?,
                    );
                    ids.push(id);
                }
                let expected = expected.unwrap();
                if guards.len() != 1 || pairs != expected.pairs {
                    return Err("reader matched-window coverage is incomplete".into());
                }
                for (operation, expected) in [
                    ("guarded-reader-source-tail", expected.source_tails),
                    ("guarded-reader-view-tail", expected.destination_tails),
                ] {
                    let mut actual = BTreeSet::new();
                    for row in equations
                        .iter()
                        .filter(|row| site(&row.point) && row.operation == operation)
                    {
                        let [post, pre] = row.variables.as_slice() else {
                            return Err("invalid reader precision obligation".into());
                        };
                        let id = EquationId {
                            construction,
                            ordinal: row.ordinal,
                        };
                        if row.transfer.is_some()
                            || !actual.insert((*post, *pre))
                            || aliases.get(&id) != guards.first()
                        {
                            return Err("ambiguous reader precision obligation".into());
                        }
                        ids.push(id);
                    }
                    if actual != expected {
                        return Err("reader precision tail is unrepresented".into());
                    }
                }
                Ok(ids)
            })();
            result.push(TransferProof {
                construction,
                candidate: candidate.clone(),
                coverage: match coverage {
                    Ok(ids) => Present(ids),
                    Err(reason) => Missing(reason),
                },
            });
        }
    }
    result
}

pub(crate) fn block_incomplete_transfers(
    facts: &super::facts::Facts,
    solver: &super::super::solver::KindSolver,
) {
    let Some(frozen) = &facts.licensing else { return };
    for proof in &frozen.reader_transfers {
        if matches!(
            proof.coverage,
            super::super::ownership_occurrence::Availability::Present(_)
        ) {
            continue;
        }
        let candidate = &proof.candidate;
        let key = format!(
            "{}::_{}@d0",
            candidate.function, candidate.destination.local
        );
        if let (Some(&lhs), Some(&rhs)) = (
            facts.slot_refs.get(&key),
            facts.slot_refs.get(&candidate.field_key),
        ) {
            solver.block_field_reader(lhs, rhs);
        }
    }
}
