//! Exact reference-effect candidates for C03/C05. These metadata records do not
//! grant ownership or change the reference/transfer equations.

use std::collections::BTreeMap;

use super::{
    super::{
        export::ProjKey,
        origin_evidence::{SourceCallee, SourceOccurrence, SourceSite},
        ownership_access::{Expression, OperandSyntax, PlaceSyntax},
        ownership_boundary::{Role, Variables, Window as BoundaryWindow},
        ownership_evidence::Point,
        ownership_occurrence::{Availability, Consumption, PathStep, Window},
    },
    facts::{EquationId, Facts},
    matched::CallKey,
    transport::Node,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Candidate {
    pub(crate) construction: u32,
    pub(crate) function: String,
    pub(crate) field_key: String,
    pub(crate) cell_place: PlaceSyntax,
    pub(crate) formation: Point,
    pub(crate) address: Point,
    pub(crate) scalar_read: Point,
    pub(crate) cell_consume: usize,
    pub(crate) reference_consume: usize,
    pub(crate) scalar_consume: usize,
    pub(crate) scalar_view_consume: usize,
    pub(crate) scalar_view_old: Node,
    pub(crate) scalar_view_new: Node,
    pub(crate) scalar_before: Node,
    pub(crate) scalar_after: Node,
    pub(crate) cell_before: Node,
    pub(crate) cell_after: Node,
    pub(crate) reference_outer: Node,
    pub(crate) call: CallKey,
    pub(crate) boundary: usize,
    pub(crate) registration: usize,
    pub(crate) actual_consume: usize,
    pub(crate) payload_before: Node,
    pub(crate) payload_after: Node,
    pub(crate) formal_before: Node,
    pub(crate) formal_after: Node,
    pub(crate) callee_field_consume: usize,
    pub(crate) free: EquationId,
    pub(crate) free_operand: Node,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Pending {
    Implementation,
    MissingEvidence,
    SharedReference,
    RetainedOrMultipleUse,
    UnknownCallee,
    BranchOrLoop,
    MixedOrUnsupported,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Hold {
    pub(crate) function: Option<String>,
    pub(crate) reason: Pending,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Plan {
    pub(crate) candidates: Vec<Candidate>,
    pub(crate) holds: Vec<Hold>,
}

/// Conditional lemma only: selecting this exact free makes this exact
/// projected output zero. This does not establish source identity or a grant.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ConsumedOutput {
    pub(crate) call: CallKey,
    pub(crate) field_key: String,
    pub(crate) free: super::matched::TerminalInstance,
    pub(crate) output: super::matched::TerminalInstance,
    pub(crate) output_path: Vec<PathStep>,
    pub(crate) input: Node,
    pub(crate) free_operand: Node,
    pub(crate) retained_output: Node,
    pub(crate) formal_output: Node,
    pub(crate) actual_output: Node,
    pub(crate) split: EquationId,
    pub(crate) entry: EquationId,
    pub(crate) exit: EquationId,
    pub(crate) call_input: EquationId,
    pub(crate) call_output: EquationId,
    pub(crate) required_free: super::transport::Guard,
}

pub(crate) fn certify_consumed_output(
    facts: &Facts,
    effect: &Candidate,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<ConsumedOutput, Pending> {
    use super::matched::{SourceLineage, TerminalInstance, TerminalTarget};

    // Recheck against the observations, not a cached Plan or Bool expression.
    let rows = facts
        .source_occurrences
        .get(&effect.function)
        .ok_or(Pending::MissingEvidence)?;
    let formation = one(rows
        .iter()
        .filter(|row| same_site(&effect.formation, effect.construction, &row.site)))?;
    if candidate(facts, effect.construction, rows, formation)? != *effect {
        return Err(Pending::MissingEvidence);
    }
    super::transport::validate_guard_aliases(facts, aliases)
        .map_err(|_| Pending::MissingEvidence)?;
    let canonical_free = *aliases.get(&effect.free).ok_or(Pending::MissingEvidence)?;
    let free = one(facts.equations.iter().filter(|row| {
        row.point.construction == effect.free.construction && row.ordinal == effect.free.ordinal
    }))?;
    if free.validate().is_err()
        || free.operation != "sink"
        || free.variables != [effect.free_operand.var]
        || effect.free_operand.construction != effect.construction
    {
        return Err(Pending::MissingEvidence);
    }
    let endpoint = free.endpoint.as_ref().ok_or(Pending::MissingEvidence)?;
    if endpoint.function != effect.call.callee
        || endpoint.callee != "free"
        || endpoint.outcome.is_some()
    {
        return Err(Pending::MissingEvidence);
    }
    let field = one(facts.consumes.iter().filter(|row| {
        row.point.construction == effect.construction && row.ordinal == effect.callee_field_consume
    }))?;
    let field_window = window(field)?;
    let [x, y, z] = [
        effect.free_operand.var,
        field_window.def_start,
        field_window.use_start,
    ];
    if x == y || x == z || y == z {
        return Err(Pending::MissingEvidence);
    }
    let split = one(facts.equations.iter().filter(|row| {
        row.point == field.point
            && row.operation == "linear"
            && row.guard.is_none()
            && row.variables == [x, y, z]
    }))?;
    if split.validate().is_err() {
        return Err(Pending::MissingEvidence);
    }
    let transfer = split.transfer.as_ref().ok_or(Pending::MissingEvidence)?;
    let Availability::Present(source) = &transfer.source else {
        return Err(Pending::MissingEvidence);
    };
    let Availability::Present(destination) = &transfer.destination else {
        return Err(Pending::MissingEvidence);
    };
    if transfer.by_move
        || transfer.source_use != z
        || transfer.source_def != y
        || transfer.destination_def != x
        || source.consume != field.ordinal
        || source.local != field.local
        || source.projection != field.projection
        || source.use_var != z
        || source.def_var != y
        || destination.def_var != x
    {
        return Err(Pending::MissingEvidence);
    }
    let destination_consume = one(facts.consumes.iter().filter(|row| {
        row.point.construction == effect.construction && row.ordinal == destination.consume
    }))?;
    if destination_consume.point != split.point
        || destination_consume.local != destination.local
        || destination_consume.projection != destination.projection
        || window(destination_consume)?.def_start != x
    {
        return Err(Pending::MissingEvidence);
    }
    let boundary = one(facts.boundary_substitutions.iter().filter(|row| {
        row.point.construction == effect.construction && row.ordinal == effect.boundary
    }))?;
    if boundary.role != Role::CallArgument
        || boundary.point.function.as_ref() != Some(&effect.call.caller)
        || boundary.point.block != Some(effect.call.block)
        || boundary.point.statement != Some(effect.call.statement)
        || boundary.callee.as_ref() != Some(&effect.call.callee)
    {
        return Err(Pending::MissingEvidence);
    }
    let entry_boundary = one(facts.boundary_substitutions.iter().filter(|row| {
        row.point.construction == effect.construction
            && row.point.function.as_ref() == Some(&effect.call.callee)
            && row.role == Role::Entry
            && row.argument_index == boundary.argument_index
    }))?;
    let exit_boundary = one(facts.boundary_substitutions.iter().filter(|row| {
        row.point.construction == effect.construction
            && row.point.function.as_ref() == Some(&effect.call.callee)
            && row.role == Role::ExitOutput
            && row.argument_index == boundary.argument_index
    }))?;
    let equality = |point: &Point, variables: [u32; 2]| {
        one(facts.equations.iter().filter(|row| {
            &row.point == point
                && row.operation == "equal"
                && row.guard.is_none()
                && row.transfer.is_none()
                && row.variables == variables
                && row.validate().is_ok()
        }))
    };
    let entry = equality(&entry_boundary.point, [z, effect.formal_before.var])?;
    let exit = equality(&exit_boundary.point, [y, effect.formal_after.var])?;
    let call_output = equality(
        &boundary.point,
        [effect.formal_after.var, effect.payload_after.var],
    )?;
    // Also authenticate the input side of the same application; output equality
    // at a different call is not a certificate for this reference effect.
    let call_input = equality(
        &boundary.point,
        [effect.formal_before.var, effect.payload_before.var],
    )?;
    if exit_boundary.formal_local != Some(field.local) {
        return Err(Pending::MissingEvidence);
    }
    let terminal = one(facts.terminals.iter().filter(|row| {
        row.point == exit_boundary.point
            && row.role == "parameter-output"
            && row.local == field.local
            && row.ssa == field.ssa_def
    }))?;
    let Availability::Present(values) = &terminal.values else {
        return Err(Pending::MissingEvidence);
    };
    let value = one(values.iter().filter(|value| value.var == y))?;
    let Availability::Present(output_path) = &value.path else {
        return Err(Pending::MissingEvidence);
    };
    if output_path != &source.path
        || !matches!(output_path.as_slice(), [PathStep::Deref, PathStep::Field { structure, index, .. }]
        if format!("{structure}::field{index}@d0") == effect.field_key)
    {
        return Err(Pending::MissingEvidence);
    }
    let node = |var| Node {
        construction: effect.construction,
        var,
    };
    let id = |row: &super::super::ownership_evidence::Equation| EquationId {
        construction: row.point.construction,
        ordinal: row.ordinal,
    };
    let lineage = SourceLineage::Exact(vec![effect.call.clone()]);
    // Linear(x,y,z) contains !x || !y. The recorded free selector implies
    // x=true, hence y=false. This implication is retained, never evaluated.
    Ok(ConsumedOutput {
        call: effect.call.clone(),
        field_key: effect.field_key.clone(),
        free: TerminalInstance {
            target: TerminalTarget::Free(effect.free),
            lineage: lineage.clone(),
        },
        output: TerminalInstance {
            target: TerminalTarget::Output {
                node: node(y),
                ordinal: terminal.ordinal,
            },
            lineage,
        },
        output_path: output_path.clone(),
        input: node(z),
        free_operand: node(x),
        retained_output: node(y),
        formal_output: effect.formal_after,
        actual_output: effect.payload_after,
        split: id(split),
        entry: id(entry),
        exit: id(exit),
        call_input: id(call_input),
        call_output: id(call_output),
        required_free: super::transport::Guard {
            binding: canonical_free,
            required: true,
        },
    })
}

impl Plan {
    /// Candidate recognition only. Endpoint selection, origin/conservation,
    /// replay/protector and the guarded effect equations remain separate gates.
    pub(crate) fn build(facts: &Facts) -> Self {
        let mut result = Self {
            candidates: Vec::new(),
            holds: Vec::new(),
        };
        for occurrences in facts.source_occurrences.values() {
            for formation in occurrences
                .iter()
                .filter(|row| matches!(&row.syntax.expression, Expression::Borrow { .. }))
            {
                for construction in 0..facts.constructions {
                    match candidate(facts, construction, occurrences, formation) {
                        Ok(row) => result.candidates.push(row),
                        Err(reason) => result.holds.push(Hold {
                            function: Some(formation.site.function.clone()),
                            reason,
                        }),
                    }
                }
            }
        }
        if result.candidates.is_empty() && result.holds.is_empty() {
            result.holds.push(Hold {
                function: None,
                reason: Pending::MissingEvidence,
            });
        }
        result
    }
}

fn one<T>(mut values: impl Iterator<Item = T>) -> Result<T, Pending> {
    let value = values.next().ok_or(Pending::MissingEvidence)?;
    if values.next().is_some() {
        return Err(Pending::RetainedOrMultipleUse);
    }
    Ok(value)
}

fn operand_place(operand: &OperandSyntax) -> Option<&PlaceSyntax> {
    match operand {
        OperandSyntax::Copy { place } | OperandSyntax::Move { place } => Some(place),
        OperandSyntax::Constant { .. } => None,
    }
}

fn inputs(expression: &Expression) -> Vec<&PlaceSyntax> {
    match expression {
        Expression::Value { operand } | Expression::Cast { operand, .. } => {
            operand_place(operand).into_iter().collect()
        }
        Expression::Borrow { place, .. }
        | Expression::RawAddress { place, .. }
        | Expression::CopyForDeref { place } => vec![place],
        Expression::Aggregate { operands, .. } | Expression::Call { operands } => {
            operands.iter().filter_map(operand_place).collect()
        }
        Expression::Unrepresented { .. } => Vec::new(),
    }
}

fn uses<'a>(rows: &'a [SourceOccurrence], local: u32) -> Vec<&'a SourceOccurrence> {
    rows.iter()
        .filter(|row| {
            inputs(&row.syntax.expression)
                .iter()
                .any(|place| place.local == local)
        })
        .collect()
}

fn same_site(point: &Point, construction: u32, site: &SourceSite) -> bool {
    point.construction == construction
        && point.function.as_ref() == Some(&site.function)
        && point.block == Some(site.block)
        && point.statement == Some(site.statement)
}

fn window(consume: &Consumption) -> Result<&Window, Pending> {
    let Availability::Present(window) = &consume.projected else {
        return Err(Pending::MissingEvidence);
    };
    if window.use_end <= window.use_start
        || window.def_end <= window.def_start
        || window.use_end - window.use_start != window.def_end - window.def_start
    {
        return Err(Pending::MissingEvidence);
    }
    Ok(window)
}

fn observed<'a>(
    facts: &'a Facts,
    construction: u32,
    site: &SourceSite,
    place: &PlaceSyntax,
) -> Result<&'a Consumption, Pending> {
    let consume = one(facts.consumes.iter().filter(|row| {
        same_site(&row.point, construction, site)
            && row.local == place.local
            && row.projection == place.projection
    }))?;
    let roster = one(facts.body_rosters.iter().filter(|row| {
        row.point.construction == construction
            && row.point.function.as_ref() == Some(&site.function)
    }))?;
    let (Some(use_ssa), Some(def_ssa)) = (consume.ssa_use, consume.ssa_def) else {
        return Err(Pending::MissingEvidence);
    };
    if !roster.consumes.iter().any(|row| {
        row.block == site.block
            && row.statement == site.statement
            && row.local == place.local
            && row.use_ssa == use_ssa
            && row.def_ssa == Some(def_ssa)
    }) {
        return Err(Pending::MissingEvidence);
    }
    let projected = window(consume)?;
    for (ssa, start, end) in [
        (use_ssa, projected.use_start, projected.use_end),
        (def_ssa, projected.def_start, projected.def_end),
    ] {
        let version = one(roster
            .versions
            .iter()
            .filter(|row| row.local == place.local && row.ssa == ssa))?;
        if !(start..end).all(|var| version.variables.contains(&var)) {
            return Err(Pending::MissingEvidence);
        }
    }
    Ok(consume)
}

fn straight_line(
    facts: &Facts,
    construction: u32,
    function: &str,
) -> Result<BTreeMap<u32, usize>, Pending> {
    let roster = one(facts.body_rosters.iter().filter(|row| {
        row.point.construction == construction && row.point.function.as_deref() == Some(function)
    }))?;
    if !roster.phis.is_empty() {
        return Err(Pending::BranchOrLoop);
    }
    let mut order = BTreeMap::new();
    let mut next = 0;
    loop {
        let block = one(roster
            .blocks
            .iter()
            .filter(|row| row.block == next && row.reachable))?;
        if order.insert(next, order.len()).is_some() {
            return Err(Pending::BranchOrLoop);
        }
        match block.successors.as_slice() {
            [] if block.return_statement.is_some() => break,
            [successor] if block.return_statement.is_none() => next = *successor,
            _ => return Err(Pending::BranchOrLoop),
        }
    }
    if order.len() != roster.blocks.iter().filter(|row| row.reachable).count() {
        return Err(Pending::BranchOrLoop);
    }
    Ok(order)
}

fn candidate(
    facts: &Facts,
    construction: u32,
    rows: &[SourceOccurrence],
    formation: &SourceOccurrence,
) -> Result<Candidate, Pending> {
    let Expression::Borrow {
        borrow,
        place: cell_place,
    } = &formation.syntax.expression
    else {
        return Err(Pending::MissingEvidence);
    };
    // This is the compiler's recorded BorrowKind, never target_type parsing.
    if borrow == "Shared" {
        return Err(Pending::SharedReference);
    }
    if borrow != "Mut { kind: Default }"
        || !cell_place.projection.is_empty()
        || !formation.syntax.destination.projection.is_empty()
    {
        return Err(Pending::MixedOrUnsupported);
    }
    let function = &formation.site.function;
    let body = one(facts
        .reader_inputs
        .bodies
        .iter()
        .filter(|row| &row.function == function))?;
    if !body.complete_operations || body.occurrences.as_slice() != rows {
        return Err(Pending::MissingEvidence);
    }
    let reference_local = formation.syntax.destination.local;
    if cell_place.local <= body.argument_count as u32
        || body.pointer_locals.contains(&cell_place.local)
        || !body.pointer_locals.contains(&reference_local)
        || body.raw_locals.contains(&reference_local)
    {
        return Err(Pending::MixedOrUnsupported);
    }
    let order = straight_line(facts, construction, function)?;
    if rows.iter().any(|row| !order.contains_key(&row.site.block)) {
        return Err(Pending::MissingEvidence);
    }
    let position = |site: &SourceSite| order.get(&site.block).map(|block| (*block, site.statement));
    let original = observed(facts, construction, &formation.site, cell_place)?;
    let reference = observed(
        facts,
        construction,
        &formation.site,
        &formation.syntax.destination,
    )?;
    let cell_window = window(original)?;
    let ref_window = window(reference)?;
    let Availability::Present(paths) = &original.pointer_paths else {
        return Err(Pending::MissingEvidence);
    };
    let [path] = paths.as_slice() else { return Err(Pending::MixedOrUnsupported) };
    let [
        PathStep::Field {
            structure, index, ..
        },
    ] = path.as_slice()
    else {
        return Err(Pending::MixedOrUnsupported);
    };
    let field_key = format!("{structure}::field{index}@d0");
    if cell_window.use_end - cell_window.use_start != 1
        || ref_window.use_end - ref_window.use_start != 2
        || !facts.reader_inputs.field_keys.contains(&field_key)
    {
        return Err(Pending::MissingEvidence);
    }
    let Availability::Present(reference_paths) = &reference.pointer_paths else {
        return Err(Pending::MissingEvidence);
    };
    let mut payload_path = vec![PathStep::Deref];
    payload_path.extend(path.iter().cloned());
    if reference_paths != &vec![vec![], payload_path] {
        return Err(Pending::MixedOrUnsupported);
    }

    let address = one(uses(rows, reference_local).into_iter())?;
    let Expression::RawAddress {
        mutability,
        place: address_place,
    } = &address.syntax.expression
    else {
        return Err(Pending::MixedOrUnsupported);
    };
    if mutability != "Mut"
        || address_place.projection != [ProjKey::Deref]
        || !address.syntax.destination.projection.is_empty()
        || position(&formation.site) >= position(&address.site)
    {
        return Err(Pending::MixedOrUnsupported);
    }
    let proxy_local = address.syntax.destination.local;
    let call = one(uses(rows, proxy_local).into_iter())?;
    let Some(SourceCallee::Local(callee)) = &call.callee else {
        return Err(Pending::UnknownCallee);
    };
    let Expression::Call { operands } = &call.syntax.expression else {
        return Err(Pending::UnknownCallee);
    };
    if operands.len() != 1
        || operand_place(&operands[0]) != Some(&address.syntax.destination)
        || position(&address.site) >= position(&call.site)
    {
        return Err(Pending::MixedOrUnsupported);
    }
    for local in [reference_local, proxy_local] {
        if rows
            .iter()
            .filter(|row| row.syntax.destination.local == local)
            .count()
            != 1
        {
            return Err(Pending::RetainedOrMultipleUse);
        }
    }
    let scalar = one(uses(rows, cell_place.local)
        .into_iter()
        .filter(|row| row.site != formation.site))?;
    let Expression::CopyForDeref {
        place: scalar_place,
    } = &scalar.syntax.expression
    else {
        return Err(Pending::RetainedOrMultipleUse);
    };
    if scalar_place.local != cell_place.local
        || scalar_place.projection != [ProjKey::Field(*index)]
        || position(&scalar.site) >= position(&formation.site)
    {
        return Err(Pending::MixedOrUnsupported);
    }
    let scalar_consume = observed(facts, construction, &scalar.site, scalar_place)?;
    let scalar_window = window(scalar_consume)?;
    let scalar_view = observed(
        facts,
        construction,
        &scalar.site,
        &scalar.syntax.destination,
    )?;
    let scalar_view_window = window(scalar_view)?;
    if !scalar_view.projection.is_empty()
        || scalar_view_window.use_end - scalar_view_window.use_start != 1
    {
        return Err(Pending::MissingEvidence);
    }
    if scalar_window.def_start != cell_window.use_start
        || scalar_window.use_end - scalar_window.use_start != 1
    {
        return Err(Pending::MissingEvidence);
    }
    let scalar_use = one(uses(rows, scalar.syntax.destination.local).into_iter())?;
    let Expression::Value { operand } = &scalar_use.syntax.expression else {
        return Err(Pending::MixedOrUnsupported);
    };
    if !operand_place(operand).is_some_and(|place| {
        place.local == scalar.syntax.destination.local && place.projection == [ProjKey::Deref]
    }) || body
        .pointer_locals
        .contains(&scalar_use.syntax.destination.local)
        || position(&scalar.site) >= position(&scalar_use.site)
        || position(&scalar_use.site) >= position(&formation.site)
    {
        return Err(Pending::MixedOrUnsupported);
    }
    // Require an actual field initialization at the same cell, not just a
    // declaration or a positive result inferred from absent stores.
    let store = one(facts.field_support_inputs.stores.iter().filter(|row| {
        row.site.function == *function
            && row.site.field_key == field_key
            && row.site.place.local == cell_place.local
    }))?;
    if !store.direct_projection
        || store.site.place.projection != scalar_place.projection
        || order
            .get(&store.site.block)
            .map(|block| (*block, store.site.statement))
            >= position(&scalar.site)
    {
        return Err(Pending::MixedOrUnsupported);
    }
    let registration = one(facts.call_arg_registrations.iter().filter(|row| {
        same_site(&row.point, construction, &address.site)
            && row.proxy_local == proxy_local
            && row.by_reference
    }))?;
    let actual = observed(facts, construction, &address.site, address_place)?;
    if registration.source_occurrence != Availability::Present(actual.ordinal) {
        return Err(Pending::MissingEvidence);
    }
    let actual_window = window(actual)?;
    if actual_window.use_start != ref_window.def_start + 1
        || actual_window.use_end - actual_window.use_start != 1
    {
        return Err(Pending::MissingEvidence);
    }
    if actual.pointer_paths != reference.pointer_paths
        || registration.window
            != (BoundaryWindow::UseDef {
                use_start: actual_window.use_start,
                use_end: actual_window.use_end,
                def_start: actual_window.def_start,
                def_end: actual_window.def_end,
            })
    {
        return Err(Pending::MissingEvidence);
    }
    let boundary = one(facts.boundary_substitutions.iter().filter(|row| {
        same_site(&row.point, construction, &call.site)
            && row.role == Role::CallArgument
            && row.argument_index == Some(0)
    }))?;
    if boundary.callee.as_ref() != Some(callee)
        || boundary.call_arg_registration != Availability::Present(registration.ordinal)
        || boundary.actual_occurrence != Availability::Present(actual.ordinal)
        || !boundary.unmatched_actual_vars.is_empty()
        || !boundary.unmatched_formal_vars.is_empty()
    {
        return Err(Pending::MissingEvidence);
    }
    let [pair] = boundary.matched.as_slice() else { return Err(Pending::MixedOrUnsupported) };
    let Variables::UseDef {
        use_var: formal_before,
        def_var: formal_after,
    } = pair.formal
    else {
        return Err(Pending::MissingEvidence);
    };
    if pair.actual
        != (Variables::UseDef {
            use_var: actual_window.use_start,
            def_var: actual_window.def_start,
        })
    {
        return Err(Pending::MissingEvidence);
    }
    let peel = boundary
        .reference_peel
        .as_ref()
        .ok_or(Pending::MissingEvidence)?;
    if peel.skipped
        != (Variables::UseDef {
            use_var: formal_before
                .checked_sub(1)
                .ok_or(Pending::MissingEvidence)?,
            def_var: formal_after
                .checked_sub(1)
                .ok_or(Pending::MissingEvidence)?,
        })
        || peel.effective_formal
            != (BoundaryWindow::UseDef {
                use_start: formal_before,
                use_end: formal_before + 1,
                def_start: formal_after,
                def_end: formal_after + 1,
            })
    {
        return Err(Pending::MissingEvidence);
    }
    if peel.original_formal
        != (BoundaryWindow::UseDef {
            use_start: formal_before - 1,
            use_end: formal_before + 1,
            def_start: formal_after - 1,
            def_end: formal_after + 1,
        })
        || boundary.actual != Availability::Present(registration.window.clone())
        || boundary.formal != Availability::Present(peel.effective_formal.clone())
    {
        return Err(Pending::MissingEvidence);
    }

    let callee_body = one(facts
        .reader_inputs
        .bodies
        .iter()
        .filter(|row| &row.function == callee))?;
    let callee_rows = facts
        .source_occurrences
        .get(callee)
        .ok_or(Pending::MissingEvidence)?;
    let formal_local = boundary.formal_local.ok_or(Pending::MissingEvidence)?;
    // Detect a retained/copied outer pointer before classifying unsupported
    // operations: it must not disappear into a generic empty-effect result.
    let field_load = one(uses(callee_rows, formal_local).into_iter())?;
    let Expression::Value { operand } = &field_load.syntax.expression else {
        return Err(Pending::RetainedOrMultipleUse);
    };
    let field_place = operand_place(operand).ok_or(Pending::MissingEvidence)?;
    if field_place.projection != [ProjKey::Deref, ProjKey::Field(*index)] {
        return Err(Pending::RetainedOrMultipleUse);
    }
    if !callee_body.complete_operations
        || callee_body.occurrences != *callee_rows
        || callee_body.argument_count != 1
    {
        return Err(Pending::MissingEvidence);
    }
    let callee_order = straight_line(facts, construction, callee)?;
    if callee_rows
        .iter()
        .any(|row| !callee_order.contains_key(&row.site.block))
    {
        return Err(Pending::MissingEvidence);
    }
    let callee_position = |site: &SourceSite| {
        callee_order
            .get(&site.block)
            .map(|block| (*block, site.statement))
    };
    let field_consume = observed(facts, construction, &field_load.site, field_place)?;
    let callee_window = window(field_consume)?;
    if field_consume.pointer_paths != reference.pointer_paths
        || callee_window.use_end - callee_window.use_start != 1
    {
        return Err(Pending::MissingEvidence);
    }
    let cast = one(uses(callee_rows, field_load.syntax.destination.local).into_iter())?;
    let Expression::Cast {
        cast: cast_kind,
        operand,
        ..
    } = &cast.syntax.expression
    else {
        return Err(Pending::MixedOrUnsupported);
    };
    if cast_kind != "PtrToPtr"
        || operand_place(operand) != Some(&field_load.syntax.destination)
        || !cast.syntax.destination.projection.is_empty()
    {
        return Err(Pending::MixedOrUnsupported);
    }
    let free_call = one(uses(callee_rows, cast.syntax.destination.local).into_iter())?;
    if free_call.callee != Some(SourceCallee::ForeignC("free".into()))
        || callee_position(&field_load.site) >= callee_position(&cast.site)
        || callee_position(&cast.site) >= callee_position(&free_call.site)
    {
        return Err(Pending::UnknownCallee);
    }
    let Expression::Call {
        operands: free_args,
    } = &free_call.syntax.expression
    else {
        return Err(Pending::MissingEvidence);
    };
    if free_args.len() != 1 || operand_place(&free_args[0]) != Some(&cast.syntax.destination) {
        return Err(Pending::MixedOrUnsupported);
    }
    for row in callee_rows {
        if [
            field_load.site.clone(),
            cast.site.clone(),
            free_call.site.clone(),
        ]
        .contains(&row.site)
        {
            continue;
        }
        if !facts
            .unit_locals
            .contains(&(callee.clone(), row.syntax.destination.local))
            || !matches!(
                &row.syntax.expression,
                Expression::Value {
                    operand: OperandSyntax::Constant { .. }
                }
            )
        {
            return Err(Pending::RetainedOrMultipleUse);
        }
    }
    let free = one(facts.equations.iter().filter(|row| {
        same_site(&row.point, construction, &free_call.site)
            && row.operation == "sink"
            && row
                .endpoint
                .as_ref()
                .is_some_and(|endpoint| endpoint.callee == "free")
    }))?;
    let [free_var] = free.variables.as_slice() else { return Err(Pending::MissingEvidence) };
    let transfer = one(facts.equations.iter().filter_map(|row| {
        if !same_site(&row.point, construction, &field_load.site)
            || !matches!(row.operation.as_str(), "linear" | "equal")
        {
            return None;
        }
        let transfer = row.transfer.as_ref()?;
        let Availability::Present(source) = &transfer.source else { return None };
        (source.consume == field_consume.ordinal
            && transfer.source_use == callee_window.use_start
            && transfer.destination_def == *free_var)
            .then_some(transfer)
    }))?;
    if transfer.source_def != callee_window.def_start {
        return Err(Pending::MissingEvidence);
    }
    let entry = one(facts.boundary_substitutions.iter().filter(|row| {
        row.point.construction == construction
            && row.point.function.as_ref() == Some(callee)
            && row.role == Role::Entry
            && row.argument_index == Some(0)
    }))?;
    let exit = one(facts.boundary_substitutions.iter().filter(|row| {
        row.point.construction == construction
            && row.point.function.as_ref() == Some(callee)
            && row.role == Role::ExitOutput
            && row.argument_index == Some(0)
    }))?;
    if !entry.matched.iter().any(|pair| {
        pair.formal == (Variables::Single { var: formal_before })
            && pair.actual
                == (Variables::Single {
                    var: callee_window.use_start,
                })
    }) || !exit.matched.iter().any(|pair| {
        pair.formal == (Variables::Single { var: formal_after })
            && pair.actual
                == (Variables::Single {
                    var: callee_window.def_start,
                })
    }) {
        return Err(Pending::MissingEvidence);
    }
    let node = |var| Node { construction, var };
    Ok(Candidate {
        construction,
        function: function.clone(),
        field_key,
        cell_place: cell_place.clone(),
        formation: original.point.clone(),
        address: actual.point.clone(),
        scalar_read: scalar_consume.point.clone(),
        cell_consume: original.ordinal,
        reference_consume: reference.ordinal,
        scalar_consume: scalar_consume.ordinal,
        scalar_view_consume: scalar_view.ordinal,
        scalar_view_old: node(scalar_view_window.use_start),
        scalar_view_new: node(scalar_view_window.def_start),
        scalar_before: node(scalar_window.use_start),
        scalar_after: node(scalar_window.def_start),
        cell_before: node(cell_window.use_start),
        cell_after: node(cell_window.def_start),
        reference_outer: node(ref_window.def_start),
        call: CallKey {
            construction,
            caller: function.clone(),
            block: call.site.block,
            statement: call.site.statement,
            callee: callee.clone(),
        },
        boundary: boundary.ordinal,
        registration: registration.ordinal,
        actual_consume: actual.ordinal,
        payload_before: node(actual_window.use_start),
        payload_after: node(actual_window.def_start),
        formal_before: node(formal_before),
        formal_after: node(formal_after),
        callee_field_consume: field_consume.ordinal,
        free: EquationId {
            construction,
            ordinal: free.ordinal,
        },
        free_operand: node(*free_var),
    })
}

#[cfg(test)]
mod tests {
    use super::{
        super::{
            super::{
                ownership_access::Expression,
                ownership_boundary::{Role, Variables},
                ownership_occurrence::{Availability, Consumption, Window},
            },
            graph_tests::with_facts,
        },
        *,
    };

    // The unchanged OL07 body. The compiler constructs facts only; neither
    // this program nor the ownership solver is executed by with_facts.
    const IFL3: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: *mut H) { free((*h).ptr as *mut core::ffi::c_void); }
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 1;
    let mut h = H { ptr: owner };
    let before = *h.ptr;
    release(&mut h);
    before
}
"#;

    fn with_consumed_output(
        check: impl FnOnce(&Facts, &Candidate, &ConsumedOutput, &BTreeMap<EquationId, EquationId>)
        + Send,
    ) {
        with_facts(IFL3, move |facts| {
            let plan = Plan::build(facts);
            assert_eq!(plan.candidates.len(), 1, "{plan:#?}");
            let candidate = &plan.candidates[0];
            let aliases = facts.licensing.as_ref().unwrap().matched.guard_aliases();
            let certificate = certify_consumed_output(facts, candidate, aliases)
                .expect("exact original free conditionally discharges its projected output");
            check(facts, candidate, &certificate, aliases);
        });
    }

    #[test]
    fn c05_consumed_output_records_exact_conditional_split_and_terminal() {
        use super::super::matched::{SourceLineage, TerminalTarget};
        with_consumed_output(|facts, candidate, certificate, aliases| {
            assert_eq!(certificate.call, candidate.call);
            assert_eq!(certificate.field_key, candidate.field_key);
            assert_eq!(
                certificate.free.target,
                TerminalTarget::Free(candidate.free)
            );
            assert_eq!(
                certificate.free.lineage,
                SourceLineage::Exact(vec![candidate.call.clone()])
            );
            assert_eq!(certificate.output.lineage, certificate.free.lineage);
            assert_eq!(certificate.required_free.binding, aliases[&candidate.free]);
            assert!(
                certificate.required_free.required,
                "a retracted or unknown free is not a discharge"
            );
            assert_eq!(certificate.free_operand, candidate.free_operand);
            assert_eq!(certificate.formal_output, candidate.formal_after);
            assert_eq!(certificate.actual_output, candidate.payload_after);
            let field = consume(
                facts,
                candidate.construction,
                candidate.callee_field_consume,
            );
            assert_eq!(certificate.input.var, projected(field).use_start);
            assert_eq!(certificate.retained_output.var, projected(field).def_start);
            let equation = |id: EquationId| {
                facts
                    .equations
                    .iter()
                    .find(|row| {
                        row.point.construction == id.construction && row.ordinal == id.ordinal
                    })
                    .expect("certificate equation exists")
            };
            let split = equation(certificate.split);
            assert_eq!(split.operation, "linear");
            assert!(split.guard.is_none());
            assert_eq!(
                split.variables,
                vec![
                    certificate.free_operand.var,
                    certificate.retained_output.var,
                    certificate.input.var
                ]
            );
            assert_ne!(certificate.free_operand, certificate.retained_output);
            assert_ne!(certificate.free_operand, certificate.input);
            assert_ne!(certificate.input, certificate.retained_output);
            for (id, variables) in [
                (
                    certificate.entry,
                    vec![certificate.input.var, candidate.formal_before.var],
                ),
                (
                    certificate.exit,
                    vec![
                        certificate.retained_output.var,
                        certificate.formal_output.var,
                    ],
                ),
                (
                    certificate.call_output,
                    vec![certificate.formal_output.var, certificate.actual_output.var],
                ),
            ] {
                assert_eq!(equation(id).operation, "equal");
                assert_eq!(equation(id).variables, variables);
                assert!(equation(id).guard.is_none());
            }
            let TerminalTarget::Output { node, ordinal } = &certificate.output.target else {
                panic!("projected output identity")
            };
            assert_eq!(*node, certificate.retained_output);
            let terminal = facts
                .terminals
                .iter()
                .find(|row| row.point.construction == node.construction && row.ordinal == *ordinal)
                .expect("exact terminal record");
            assert_eq!(terminal.role, "parameter-output");
            assert_eq!(
                terminal.point.function.as_ref(),
                Some(&candidate.call.callee)
            );
            let Availability::Present(values) = &terminal.values else {
                panic!("terminal values present")
            };
            assert!(values.iter().any(|value| value.var == node.var
                && value.path == Availability::Present(certificate.output_path.clone())));
            assert!(
                certificate
                    .output_path
                    .contains(&super::super::super::ownership_occurrence::PathStep::Deref)
            );

            let mut metadata = facts.clone();
            metadata.guards.clear();
            metadata.ownership_asts = Default::default();
            assert_eq!(
                certify_consumed_output(&metadata, candidate, aliases).unwrap(),
                *certificate,
                "explicit guard-alias metadata suffices without ASTs"
            );
        });
    }

    #[test]
    fn c05_consumed_output_rejects_corrupted_split() {
        with_consumed_output(|facts, candidate, certificate, aliases| {
            let mut corrupted = facts.clone();
            let split = corrupted
                .equations
                .iter_mut()
                .find(|row| {
                    row.point.construction == certificate.split.construction
                        && row.ordinal == certificate.split.ordinal
                })
                .unwrap();
            split.variables[1] = split.variables[0];
            assert!(certify_consumed_output(&corrupted, candidate, aliases).is_err());
        });
    }

    #[test]
    fn c05_consumed_output_rejects_missing_exit_equality() {
        with_consumed_output(|facts, candidate, certificate, aliases| {
            let mut corrupted = facts.clone();
            corrupted.equations.retain(|row| {
                row.point.construction != certificate.exit.construction
                    || row.ordinal != certificate.exit.ordinal
            });
            assert!(certify_consumed_output(&corrupted, candidate, aliases).is_err());
        });
    }

    #[test]
    fn c05_consumed_output_rejects_wrong_call_identity() {
        with_consumed_output(|facts, candidate, _, aliases| {
            let mut corrupted = candidate.clone();
            corrupted.call.statement += 1;
            assert!(certify_consumed_output(facts, &corrupted, aliases).is_err());
        });
    }

    #[test]
    fn c05_consumed_output_rejects_wrong_or_missing_free_key() {
        with_consumed_output(|facts, candidate, certificate, aliases| {
            let mut corrupted = candidate.clone();
            corrupted.free = certificate.split;
            assert!(certify_consumed_output(facts, &corrupted, aliases).is_err());
            let mut absent = aliases.clone();
            absent.remove(&candidate.free);
            assert!(certify_consumed_output(facts, candidate, &absent).is_err());
        });
    }

    fn projected(consume: &Consumption) -> &Window {
        let Availability::Present(window) = &consume.projected else {
            panic!("fixture requires an exact represented consume")
        };
        window
    }

    fn consume(facts: &Facts, construction: u32, ordinal: usize) -> &Consumption {
        facts
            .consumes
            .iter()
            .find(|row| row.point.construction == construction && row.ordinal == ordinal)
            .expect("candidate names a real consume")
    }

    #[test]
    fn c05_reference_effect_ifl3_joins_original_cell_call_and_free() {
        with_facts(IFL3, |facts| {
            let plan = Plan::build(facts);
            assert_eq!(plan.candidates.len(), 1, "{plan:#?}");
            assert!(plan.holds.is_empty(), "{plan:#?}");
            let row = &plan.candidates[0];
            assert_eq!(row.function, "f");
            assert_eq!(row.field_key, "H::field0@d0");
            let node = |var| Node {
                construction: row.construction,
                var,
            };

            let formation = facts.source_occurrences["f"]
                .iter()
                .find(|site| matches!(&site.syntax.expression, Expression::Borrow { .. }))
                .expect("native reference formation");
            let syntax = &formation.syntax;
            let Expression::Borrow { borrow, place } = &syntax.expression else { unreachable!() };
            assert!(borrow.starts_with("Mut"));
            assert_eq!(&row.cell_place, place);
            assert_eq!(row.formation.block, Some(formation.site.block));
            assert_eq!(row.formation.statement, Some(formation.site.statement));
            let original = consume(facts, row.construction, row.cell_consume);
            let reference = consume(facts, row.construction, row.reference_consume);
            assert_eq!(original.point, row.formation);
            assert_eq!(reference.point, row.formation);
            assert_eq!(original.local, place.local);
            assert_eq!(original.projection, place.projection);
            assert_eq!(reference.local, syntax.destination.local);
            assert_eq!(row.cell_before, node(projected(original).use_start));
            assert_eq!(row.cell_after, node(projected(original).def_start));
            assert_eq!(row.reference_outer, node(projected(reference).def_start));

            let scalar = consume(facts, row.construction, row.scalar_consume);
            assert_eq!(scalar.point, row.scalar_read);
            assert_eq!(scalar.local, place.local);
            assert_eq!(row.scalar_before, node(projected(scalar).use_start));
            assert_eq!(row.scalar_after, node(projected(scalar).def_start));
            assert_eq!(row.scalar_after, row.cell_before);
            assert!(facts.source_occurrences["f"].iter().any(|site| {
                Some(site.site.block) == scalar.point.block
                    && Some(site.site.statement) == scalar.point.statement
                    && matches!(&site.syntax.expression, Expression::CopyForDeref { .. })
            }));

            let boundary = facts
                .boundary_substitutions
                .iter()
                .find(|b| b.point.construction == row.construction && b.ordinal == row.boundary)
                .expect("exact caller boundary");
            assert_eq!(boundary.role, Role::CallArgument);
            assert_eq!(boundary.callee.as_deref(), Some("release"));
            assert_eq!(boundary.point.function.as_deref(), Some("f"));
            assert_eq!(boundary.point.block, Some(row.call.block));
            assert_eq!(boundary.point.statement, Some(row.call.statement));
            assert_eq!(row.call.callee, "release");
            assert_eq!(row.call.caller, "f");
            assert_eq!(
                boundary.call_arg_registration,
                Availability::Present(row.registration)
            );
            assert_eq!(
                boundary.actual_occurrence,
                Availability::Present(row.actual_consume)
            );
            assert!(boundary.reference_peel.is_some());
            let actual = consume(facts, row.construction, row.actual_consume);
            assert_eq!(row.payload_before, node(projected(actual).use_start));
            assert_eq!(row.payload_after, node(projected(actual).def_start));
            assert_ne!(
                row.payload_before, row.cell_before,
                "cell and reference view remain distinct identities"
            );
            assert!(boundary.matched.iter().any(|pair| {
                pair.actual
                    == (Variables::UseDef {
                        use_var: row.payload_before.var,
                        def_var: row.payload_after.var,
                    })
                    && pair.formal
                        == (Variables::UseDef {
                            use_var: row.formal_before.var,
                            def_var: row.formal_after.var,
                        })
            }));
            let registration = facts
                .call_arg_registrations
                .iter()
                .find(|r| r.point.construction == row.construction && r.ordinal == row.registration)
                .expect("selected original proxy registration");
            assert!(registration.by_reference);
            assert_eq!(
                registration.source_occurrence,
                Availability::Present(row.actual_consume)
            );
            assert_eq!(registration.point, row.address);
            assert!(facts.source_occurrences["f"].iter().any(|site| {
                Some(site.site.block) == row.address.block
                    && Some(site.site.statement) == row.address.statement
                    && site.syntax.destination.local == registration.proxy_local
                    && matches!(&site.syntax.expression, Expression::RawAddress { mutability, place }
                        if mutability == "Mut" && place.local == reference.local
                            && place.projection == actual.projection)
            }), "the exact Mut Borrow -> Mut RawAddress -> selected call proxy chain");

            let free = facts
                .equations
                .iter()
                .find(|e| {
                    e.point.construction == row.free.construction && e.ordinal == row.free.ordinal
                })
                .expect("original free endpoint");
            assert_eq!(free.operation, "sink");
            assert_eq!(free.point.function.as_deref(), Some("release"));
            assert_eq!(free.variables, vec![row.free_operand.var]);
            assert_eq!(free.endpoint.as_ref().unwrap().callee, "free");
            let field = consume(facts, row.construction, row.callee_field_consume);
            assert_eq!(field.point.function.as_deref(), Some("release"));
            assert!(facts.equations.iter().any(|e| {
                e.point == field.point
                    && e.transfer.as_ref().is_some_and(|t| {
                        t.source_use == projected(field).use_start
                            && t.destination_def == row.free_operand.var
                    })
            }));
        });
    }

    fn held(code: &str, reason: Pending) {
        with_facts(code, move |facts| {
            let plan = Plan::build(facts);
            assert!(plan.candidates.is_empty(), "{plan:#?}");
            assert!(
                plan.holds.iter().any(|hold| hold.reason == reason),
                "{plan:#?}"
            );
        });
    }

    #[test]
    fn c05_reference_effect_holds_shared_native_reference() {
        held(
            &IFL3.replace("release(&mut h)", "release(&h as *const H as *mut H)"),
            Pending::SharedReference,
        );
    }

    #[test]
    fn c05_reference_effect_holds_retained_outer_alias() {
        let code = IFL3.replace(
            "pub unsafe fn release(h: *mut H) {",
            "static mut KEPT: *mut H = 0 as *mut H;\npub unsafe fn release(h: *mut H) { KEPT = h;",
        );
        held(&code, Pending::RetainedOrMultipleUse);
    }

    #[test]
    fn c05_reference_effect_holds_unknown_callee() {
        let code = IFL3.replace(
            "pub unsafe fn release(h: *mut H) { free((*h).ptr as *mut core::ffi::c_void); }",
            "unsafe extern \"C\" { fn release(h: *mut H); }",
        );
        held(&code, Pending::UnknownCallee);
    }

    #[test]
    fn c05_reference_effect_guard_requires_permission_in_the_mandatory_model() {
        super::super::graph_tests::with_solver_facts(IFL3, |facts, original, slots| {
            use crate::analyses::borrow_ownership::solver::KindSolver;
            let row = facts
                .equations
                .iter()
                .find(|row| row.operation == "guarded-reference-field")
                .expect("actual guarded reference");
            let key = EquationId {
                construction: row.point.construction,
                ordinal: row.ordinal,
            };
            let guard = &facts
                .guards
                .iter()
                .find(|binding| binding.equation == key)
                .unwrap()
                .predicate;
            let probe = KindSolver::new(slots);
            assert_eq!(
                probe.check_with_assumptions(&[guard.clone()]),
                z3::SatResult::Sat,
                "omitting the permission hold must expose the arm, not pass vacuously"
            );
            let before = probe.hard_assertion_count();
            let mut unsupported = facts.clone();
            let mut incomplete = (**facts.licensing.as_ref().unwrap()).clone();
            incomplete.field_support.clear();
            unsupported.licensing = Some(std::rc::Rc::new(incomplete));
            probe
                .constrain_reference_field_effects(&unsupported)
                .unwrap();
            assert!(probe.hard_assertion_count() > before);
            assert_eq!(
                probe.hard_loop_solver().assertion_count(),
                probe.hard_assertion_count()
            );
            assert_eq!(
                probe.check_with_assumptions(&[guard.clone()]),
                z3::SatResult::Unsat,
                "candidate metadata alone cannot enable delegated ownership"
            );
            assert_eq!(probe.check_with_assumptions(&[!guard]), z3::SatResult::Sat);
            let mut missing = unsupported;
            missing.guards.clear();
            let before = probe.hard_assertion_count();
            assert!(probe.constrain_reference_field_effects(&missing).is_err());
            assert_eq!(probe.hard_assertion_count(), before);
            assert_eq!(
                original.check_sat_count(),
                0,
                "construction stayed query-free"
            );
        });
    }

    #[test]
    fn c05_reference_effect_export_preserves_candidates_and_explicit_holds() {
        with_facts(IFL3, |facts| {
            let snapshot = super::super::snapshot::Snapshot::capture(facts, 0).unwrap();
            let document = serde_json::to_value(&snapshot).unwrap();
            assert_eq!(
                document["reference_effects"]["candidates"]
                    .as_array()
                    .map(Vec::len),
                Some(1)
            );
            assert_eq!(
                document["reference_effects"]["candidates"][0]["field_key"],
                "H::field0@d0"
            );
            snapshot.validate().unwrap();
            let mut omitted = document;
            omitted["reference_effects"]["candidates"] = serde_json::json!([]);
            let omitted: super::super::snapshot::Snapshot =
                serde_json::from_value(omitted).unwrap();
            assert!(
                omitted.validate().is_err(),
                "reference-effect evidence cannot disappear from readback"
            );
        });
    }

    #[test]
    fn c05_reference_effect_transport_names_emitted_read_and_return_obligations() {
        with_facts(IFL3, |facts| {
            let plan = Plan::build(facts);
            let candidate = &plan.candidates[0];
            let graph = super::super::transport::CandidateGraph::build(facts);
            for (operation, before, after) in [
                (
                    "guarded-reference-scalar-read",
                    candidate.scalar_before,
                    candidate.scalar_after,
                ),
                (
                    "guarded-reference-output",
                    candidate.payload_after,
                    candidate.cell_after,
                ),
            ] {
                let row = facts
                    .equations
                    .iter()
                    .find(|row| {
                        row.operation == operation
                            && row.point.function.as_deref() == Some("f")
                            && row.variables == [after.var, before.var]
                    })
                    .unwrap_or_else(|| panic!("{operation} must be an actual mandatory equation"));
                assert!(row.guard.is_some() && row.transfer.is_none());
                assert!(
                    graph.edges.iter().any(|edge| edge.from == before
                        && edge.to == after
                        && edge.guard.is_some_and(|guard| guard.required)),
                    "the exact emitted {operation} must be transported under its guard"
                );
            }
            assert!(
                graph
                    .edges
                    .iter()
                    .any(|edge| edge.from == candidate.cell_before
                        && edge.to == candidate.payload_before
                        && edge.guard.is_some_and(|guard| guard.required))
            );
            let matched = super::super::matched::MatchedTransport::build(facts);
            assert!(matched.meets_for(candidate.scalar_before).iter().any(|meet|
                matches!(meet.terminal.target, super::super::matched::TerminalTarget::Free(equation)
                    if equation == candidate.free)),
                "the exact guarded chain must reach its actual callee free");
        });
    }

    #[test]
    fn c05_ifl3_all_original_endpoints_fit_the_hard_universe() {
        use rustc_hir::{ItemKind, OwnerNode};

        use crate::analyses::borrow_ownership::{
            construction::{CopyLendMode, construct_bo_into},
            crate_slots::CrateSlots,
            mutability_facts::MutFacts,
            origins::compute_origins,
            solver::KindSolver,
        };
        ::utils::compilation::run_compiler_on_str(IFL3, |tcx| {
            let mut functions = Vec::new();
            let mut structs = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else { continue };
                let OwnerNode::Item(item) = owner.node() else { continue };
                match item.kind {
                    ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                    ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                    _ => {}
                }
            }
            let program = crate::utils::rustc::RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let mutability = MutFacts::from_program(&program);
            let solver = KindSolver::new_tracked(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &mutability,
                &solver,
                CopyLendMode::Baseline,
            )
            .unwrap();
            let tracker = solver.tracker().unwrap();
            let mut assumptions = tracker.tracks();
            assumptions.extend_from_slice(construction.selectors.sources());
            assumptions.extend_from_slice(construction.selectors.sinks());
            let outcome = solver.check_with_assumptions(&assumptions);
            if outcome == z3::SatResult::Unsat {
                let labels: Vec<_> = solver
                    .optimize()
                    .get_unsat_core()
                    .iter()
                    .map(|literal| {
                        tracker
                            .label_of(literal)
                            .unwrap_or_else(|| literal.to_string())
                    })
                    .collect();
                eprintln!("C05_HARD_CORE={}", serde_json::to_string(&labels).unwrap());
            }
            assert_eq!(
                outcome,
                z3::SatResult::Sat,
                "the complete original source/free obligations must coexist before borrow replay"
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn c05_permission_requires_every_actual_obligation_despite_cached_support() {
        super::super::graph_tests::with_solver_facts(IFL3, |facts, _, slots| {
            use crate::analyses::borrow_ownership::solver::KindSolver;
            let formation = facts
                .equations
                .iter()
                .find(|row| row.operation == "guarded-reference-field")
                .unwrap();
            let key = EquationId {
                construction: formation.point.construction,
                ordinal: formation.ordinal,
            };
            let guard = facts
                .guards
                .iter()
                .find(|row| row.equation == key)
                .unwrap()
                .predicate
                .clone();
            let probe = KindSolver::new(slots);
            probe.constrain_reference_field_effects(facts).unwrap();
            assert_eq!(
                probe.check_with_assumptions(&[guard.clone()]),
                z3::SatResult::Sat
            );
            for operation in [
                "guarded-reference-scalar-read",
                "guarded-reference-output",
                "guarded-reference-outer",
                "guarded-reference-view-zero",
            ] {
                let mut missing = facts.clone();
                let before = missing.equations.len();
                missing.equations.retain(|row| row.operation != operation);
                assert!(missing.equations.len() < before);
                let probe = KindSolver::new(slots);
                probe.constrain_reference_field_effects(&missing).unwrap();
                assert_eq!(
                    probe.check_with_assumptions(&[guard.clone()]),
                    z3::SatResult::Unsat,
                    "cached source/store support cannot replace missing {operation}"
                );
            }
        });
    }

    #[test]
    fn c05_attested_shared_retained_and_partner_free_inputs_remain_unowned() {
        let inputs = [
            IFL3.replace("release(&mut h)", "release(&h as *const H as *mut H)"),
            IFL3.replace("pub unsafe fn release(h: *mut H) {",
                "static mut KEPT: *mut H = 0 as *mut H;\npub unsafe fn release(h: *mut H) { KEPT = h;"),
            IFL3.replace("release(&mut h);", "release(&mut h); free(owner as *mut core::ffi::c_void);"),
        ];
        for input in inputs {
            let fixture = super::super::tests::inspect_era5_frame(&input);
            fixture.assert_not_owning("H.ptr");
        }
    }

    #[test]
    fn c05_unattested_public_entry_keeps_its_unknown_object_protection() {
        let fixture = super::super::tests::inspect(IFL3);
        fixture.assert_kind(
            "release::h",
            crate::analyses::borrow_ownership::SlotKind::Raw,
        );
    }

    #[test]
    fn c05_permission_withdraws_with_each_original_endpoint() {
        super::super::graph_tests::with_solver_facts(IFL3, |facts, _, slots| {
            use crate::analyses::borrow_ownership::solver::KindSolver;
            let effect = &Plan::build(facts).candidates[0];
            let formation = facts
                .equations
                .iter()
                .find(|row| {
                    row.operation == "guarded-reference-field" && row.point == effect.formation
                })
                .unwrap();
            let guard = &facts
                .guards
                .iter()
                .find(|binding| binding.equation.ordinal == formation.ordinal)
                .unwrap()
                .predicate;
            let probe = KindSolver::new(slots);
            probe.constrain_reference_field_effects(facts).unwrap();
            assert_eq!(
                probe.check_with_assumptions(&[guard.clone()]),
                z3::SatResult::Sat
            );
            for row in facts
                .equations
                .iter()
                .filter(|row| matches!(row.operation.as_str(), "source" | "sink"))
            {
                let key = EquationId {
                    construction: row.point.construction,
                    ordinal: row.ordinal,
                };
                let endpoint = &facts
                    .guards
                    .iter()
                    .find(|binding| binding.equation == key)
                    .unwrap()
                    .predicate;
                assert_eq!(
                    probe.check_with_assumptions(&[guard.clone(), !endpoint]),
                    z3::SatResult::Unsat
                );
                assert_eq!(
                    probe.check_with_assumptions(&[!guard, !endpoint]),
                    z3::SatResult::Sat,
                    "withdrawing permission leaves the original inactive arm available"
                );
            }
        });
    }

    #[test]
    fn c05_attested_mixed_stack_and_allocation_field_cannot_own() {
        let code = IFL3.replace("pub unsafe fn f() -> i32 {", "pub unsafe fn f(heap: bool) -> i32 { let mut stack = 1;")
            .replace("let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;",
                "let owner = if heap { malloc(core::mem::size_of::<i32>()) as *mut i32 } else { &mut stack as *mut i32 };");
        let fixture = super::super::tests::inspect_era5_frame(&code);
        fixture.assert_not_owning("H.ptr");
    }

    #[test]
    fn c05_attested_accepted_model_retains_one_payload_and_original_free() {
        use crate::analyses::borrow_ownership::{SlotKind, ssa::constraint::Var};
        let fixture = super::super::tests::inspect_era5_frame(IFL3);
        fixture.assert_kind("H.ptr", SlotKind::Owning);
        fixture.assert_kind("release::h", SlotKind::Ref);
        let snapshot = fixture
            .export
            .ownership_licensing
            .as_ref()
            .unwrap()
            .last()
            .unwrap();
        let effect = &snapshot.reference_effects.candidates[0];
        let owns = fixture.export.version_owns.as_ref().unwrap();
        for node in [
            effect.scalar_before,
            effect.scalar_after,
            effect.payload_before,
            effect.formal_before,
            effect.free_operand,
        ] {
            assert!(
                owns[Var::from_u32(node.var)],
                "selected responsibility at {node:?}"
            );
        }
        for node in [
            effect.scalar_view_old,
            effect.scalar_view_new,
            effect.cell_after,
            effect.payload_after,
            effect.formal_after,
            effect.reference_outer,
        ] {
            assert!(
                !owns[Var::from_u32(node.var)],
                "discharged/nonowning responsibility at {node:?}"
            );
        }
        assert!(
            fixture
                .export
                .reader_replay
                .as_ref()
                .unwrap()
                .iter()
                .any(|row| row.owned_cell.as_ref() == Some(effect)
                    && row.matched_loans == 1
                    && row.origin_linked)
        );
        assert!(
            fixture
                .export
                .retirement_rounds
                .iter()
                .any(|round| !round.known_stack_entries.is_empty())
        );
    }
}
