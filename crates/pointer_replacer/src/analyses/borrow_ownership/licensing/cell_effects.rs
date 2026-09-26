//! Exact native-reference to original-cell call correspondences. Discovery is
//! metadata only; it supplies neither permission nor an ownership constraint.
use serde::{Deserialize, Serialize};

use super::{
    super::{ownership_access::PlaceSyntax, ownership_evidence::Point},
    facts::Facts,
    matched::CallKey,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Candidate {
    pub(crate) call: CallKey,
    pub(crate) argument: usize,
    pub(crate) boundary: usize,
    pub(crate) field_key: String,
    pub(crate) cell: PlaceSyntax,
    pub(crate) formation: Point,
    pub(crate) original_consume: usize,
    pub(crate) reference_consume: usize,
    pub(crate) address: Point,
    pub(crate) registration: usize,
    pub(crate) reference_use: usize,
}

/// Formation-time eligibility, deliberately independent of future boundary
/// records. This is not a consuming/input/output permission certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Early {
    pub(crate) call: CallKey,
    pub(crate) argument: usize,
    pub(crate) original_consume: usize,
    pub(crate) reference_consume: usize,
}

pub(crate) fn early(facts: &Facts, point: &Point) -> Option<Early> {
    use super::super::{
        export::ProjKey,
        origin_evidence::SourceCallee,
        ownership_access::Expression,
        ownership_occurrence::{Availability::Present, PathStep},
    };
    let function = point.function.as_ref()?;
    let rows = facts.source_occurrences.get(function)?;
    let formation = one(rows.iter().filter(|row| {
        point.block == Some(row.site.block) && point.statement == Some(row.site.statement)
    }))?;
    let Expression::Borrow {
        borrow,
        place: cell,
    } = &formation.syntax.expression
    else {
        return None;
    };
    if borrow != "Mut { kind: Default }"
        || !cell.projection.is_empty()
        || !formation.syntax.destination.projection.is_empty()
    {
        return None;
    }
    let body = one(facts
        .reader_inputs
        .bodies
        .iter()
        .filter(|body| &body.function == function))?;
    if !body.complete_operations
        || !body.reachable.contains(&formation.site.block)
        || cell.local as usize <= body.argument_count
        || body.pointer_locals.contains(&cell.local)
        || !body
            .pointer_locals
            .contains(&formation.syntax.destination.local)
        || body
            .raw_locals
            .contains(&formation.syntax.destination.local)
    {
        return None;
    }
    let address = one(rows
        .iter()
        .filter(|row| uses(&row.syntax.expression, formation.syntax.destination.local)))?;
    let Expression::RawAddress { mutability, place } = &address.syntax.expression else {
        return None;
    };
    if mutability != "Mut"
        || place.local != formation.syntax.destination.local
        || place.projection != [ProjKey::Deref]
        || !address.syntax.destination.projection.is_empty()
    {
        return None;
    }
    let call = one(rows
        .iter()
        .filter(|row| uses(&row.syntax.expression, address.syntax.destination.local)))?;
    let Some(SourceCallee::Local(callee)) = &call.callee else { return None };
    let Expression::Call { operands } = &call.syntax.expression else { return None };
    let argument = one(operands.iter().enumerate().filter_map(|(index, value)| {
        (operand_place(value) == Some(&address.syntax.destination)).then_some(index)
    }))?;
    if formation.site.block != address.site.block
        || formation.site.block != call.site.block
        || !(formation.site.statement < address.site.statement
            && address.site.statement < call.site.statement)
        || rows.iter().any(|row| {
            row.site.block == formation.site.block
                && formation.site.statement < row.site.statement
                && row.site.statement < call.site.statement
                && row != address
                && (uses(&row.syntax.expression, cell.local)
                    || row.syntax.destination.local == cell.local
                    || matches!(
                        row.syntax.expression,
                        Expression::Call { .. } | Expression::Unrepresented { .. }
                    ))
        })
    {
        return None;
    }
    // Preserve C05's direct field-to-free path. This initial dormant alternative
    // is for a field write or a local-call output chain; neither grants a role.
    let callee_rows = facts.source_occurrences.get(callee)?;
    if !callee_rows.iter().any(|row| {
        !row.syntax.destination.projection.is_empty()
            || matches!(row.callee, Some(SourceCallee::Local(_)))
    }) {
        return None;
    }
    let original = one(facts.consumes.iter().filter(|row| {
        &row.point == point && row.local == cell.local && row.projection == cell.projection
    }))?;
    let reference = one(facts.consumes.iter().filter(|row| {
        &row.point == point
            && row.local == formation.syntax.destination.local
            && row.projection.is_empty()
    }))?;
    let (Present(cell_window), Present(reference_window), Present(paths), Present(reference_paths)) = (
        &original.projected,
        &reference.projected,
        &original.pointer_paths,
        &reference.pointer_paths,
    ) else {
        return None;
    };
    if cell_window.use_end.checked_sub(cell_window.use_start) != Some(1)
        || cell_window.def_end.checked_sub(cell_window.def_start) != Some(1)
        || reference_window
            .use_end
            .checked_sub(reference_window.use_start)
            != Some(2)
        || reference_window
            .def_end
            .checked_sub(reference_window.def_start)
            != Some(2)
    {
        return None;
    }
    let [path] = paths.as_slice() else { return None };
    if !matches!(path.as_slice(), [PathStep::Field { .. }])
        || reference_paths != &vec![vec![], vec![PathStep::Deref, path[0].clone()]]
    {
        return None;
    }
    Some(Early {
        call: CallKey {
            construction: point.construction,
            caller: function.clone(),
            block: call.site.block,
            statement: call.site.statement,
            callee: callee.clone(),
        },
        argument,
        original_consume: original.ordinal,
        reference_consume: reference.ordinal,
    })
}

pub(crate) fn validate_frames(
    facts: &Facts,
    aliases: &std::collections::BTreeMap<super::facts::EquationId, super::facts::EquationId>,
) -> Result<(), String> {
    use super::{super::ownership_occurrence::Availability::Present, facts::EquationId};
    for row in facts
        .equations
        .iter()
        .filter(|row| row.operation == "guarded-original-cell-frame")
    {
        let id = EquationId {
            construction: row.point.construction,
            ordinal: row.ordinal,
        };
        let candidate = early(facts, &row.point)
            .ok_or("original-cell frame has no exact early correspondence")?;
        let transfer = row
            .transfer
            .as_ref()
            .ok_or("original-cell frame has no transfer binding")?;
        let (Present(source), Present(destination)) = (&transfer.source, &transfer.destination)
        else {
            return Err("original-cell frame binding missing".into());
        };
        if row.validate().is_err()
            || source.consume != candidate.original_consume
            || destination.consume != candidate.reference_consume
            || transfer.by_move
            || row.variables
                != [
                    transfer.destination_def,
                    transfer.source_def,
                    transfer.source_use,
                ]
        {
            return Err("original-cell frame correspondence mismatch".into());
        }
        let reference = one(facts.consumes.iter().filter(|consume| {
            consume.point == row.point && consume.ordinal == candidate.reference_consume
        }))
        .ok_or("original-cell reference consume missing")?;
        let Present(window) = &reference.projected else {
            return Err("original-cell reference window missing".into());
        };
        for var in (window.use_start..window.use_end).chain(window.def_start..window.def_end) {
            if !facts.equations.iter().any(|zero| {
                zero.point == row.point
                    && zero.operation == "assume"
                    && zero.variables == [var]
                    && zero.value == Some(false)
                    && zero.guard.is_none()
                    && zero.transfer.is_none()
                    && zero.validate().is_ok()
            }) {
                return Err("original-cell reference old/new zero evidence missing".into());
            }
        }
        let canonical = aliases
            .get(&id)
            .ok_or("original-cell frame guard missing")?;
        let held = facts
            .equations
            .iter()
            .filter(|hold| {
                hold.point == row.point
                    && hold.operation == "guarded-original-cell-declared"
                    && hold.validate().is_ok()
                    && aliases.get(&EquationId {
                        construction: hold.point.construction,
                        ordinal: hold.ordinal,
                    }) == Some(canonical)
            })
            .count();
        if held != 1 {
            return Err("original-cell frame lacks its mandatory guard declaration".into());
        }
    }
    Ok(())
}

pub(crate) fn discover(facts: &Facts) -> Vec<Candidate> {
    facts
        .boundary_substitutions
        .iter()
        .filter_map(|boundary| candidate(facts, boundary))
        .collect()
}

fn candidate(
    facts: &Facts,
    boundary: &super::super::ownership_boundary::Substitution,
) -> Option<Candidate> {
    use super::super::{
        export::ProjKey,
        origin_evidence::SourceCallee,
        ownership_access::Expression,
        ownership_boundary::{Role, Variables, Window},
        ownership_occurrence::{Availability::Present, PathStep},
    };
    if boundary.role != Role::CallArgument {
        return None;
    }
    let function = boundary.point.function.as_ref()?;
    let callee = boundary.callee.as_ref()?;
    let argument = boundary.argument_index?;
    let Present(registration_id) = boundary.call_arg_registration else {
        return None;
    };
    let registration = one(facts.call_arg_registrations.iter().filter(|row| {
        row.point.construction == boundary.point.construction && row.ordinal == registration_id
    }))?;
    if !registration.by_reference
        || registration.point.function.as_ref() != Some(function)
        || registration.point.block != boundary.point.block
    {
        return None;
    }
    let Present(actual_id) = registration.source_occurrence else {
        return None;
    };
    if boundary.actual_occurrence != Present(actual_id)
        || boundary.actual != Present(registration.window.clone())
    {
        return None;
    }
    let actual = one(facts.consumes.iter().filter(|row| {
        row.point.construction == boundary.point.construction && row.ordinal == actual_id
    }))?;
    if actual.point != registration.point
        || actual.ssa_use.is_none()
        || actual.projection != [ProjKey::Deref]
    {
        return None;
    }
    let Present(actual_window) = &actual.projected else {
        return None;
    };
    if registration.window
        != (Window::UseDef {
            use_start: actual_window.use_start,
            use_end: actual_window.use_end,
            def_start: actual_window.def_start,
            def_end: actual_window.def_end,
        })
    {
        return None;
    }
    let rows = facts.source_occurrences.get(function)?;
    let at = |point: &Point, row: &super::super::origin_evidence::SourceOccurrence| {
        point.function.as_ref() == Some(&row.site.function)
            && point.block == Some(row.site.block)
            && point.statement == Some(row.site.statement)
    };
    let address = one(rows.iter().filter(|row| at(&registration.point, row)))?;
    if address.syntax.destination
        != (PlaceSyntax {
            local: registration.proxy_local,
            projection: vec![],
        })
    {
        return None;
    }
    let Expression::RawAddress {
        mutability,
        place: address_place,
    } = &address.syntax.expression
    else {
        return None;
    };
    if mutability != "Mut"
        || address_place.local != actual.local
        || address_place.projection != [ProjKey::Deref]
    {
        return None;
    }
    let call = one(rows.iter().filter(|row| at(&boundary.point, row)))?;
    if call.callee.as_ref() != Some(&SourceCallee::Local(callee.clone())) {
        return None;
    }
    let Expression::Call { operands } = &call.syntax.expression else {
        return None;
    };
    if operand_place(operands.get(argument)?) != Some(&address.syntax.destination) {
        return None;
    }
    let formation = one(rows.iter().filter(|row| {
        row.syntax.destination.local == actual.local
            && row.syntax.destination.projection.is_empty()
            && matches!(row.syntax.expression, Expression::Borrow { .. })
    }))?;
    let Expression::Borrow {
        borrow,
        place: cell,
    } = &formation.syntax.expression
    else {
        return None;
    };
    if !borrow.starts_with("Mut")
        || !cell.projection.is_empty()
        || formation.site.block != call.site.block
        || !(formation.site.statement < address.site.statement
            && address.site.statement < call.site.statement)
    {
        return None;
    }
    let body = one(facts
        .reader_inputs
        .bodies
        .iter()
        .filter(|body| &body.function == function))?;
    if cell.local as usize <= body.argument_count || body.pointer_locals.contains(&cell.local) {
        return None;
    }
    // The reference and raw proxy each have one original syntactic use. An
    // independent argument copy may intervene, but no use/write of this cell.
    let reference_uses: Vec<_> = rows
        .iter()
        .filter(|row| uses(&row.syntax.expression, actual.local))
        .collect();
    let proxy_uses: Vec<_> = rows
        .iter()
        .filter(|row| uses(&row.syntax.expression, registration.proxy_local))
        .collect();
    if reference_uses != [address]
        || proxy_uses != [call]
        || operands
            .iter()
            .filter(|value| {
                operand_place(value).is_some_and(|place| place.local == registration.proxy_local)
            })
            .count()
            != 1
        || rows.iter().any(|row| {
            row.site.block == formation.site.block
                && formation.site.statement < row.site.statement
                && row.site.statement < call.site.statement
                && row != address
                && (uses(&row.syntax.expression, cell.local)
                    || row.syntax.destination.local == cell.local
                    || matches!(row.syntax.expression, Expression::Call { .. })
                    || matches!(row.syntax.expression, Expression::Unrepresented { .. }))
        })
    {
        return None;
    }
    let at_formation =
        |point: &Point| point.construction == boundary.point.construction && at(point, formation);
    let original = one(facts.consumes.iter().filter(|row| {
        at_formation(&row.point) && row.local == cell.local && row.projection == cell.projection
    }))?;
    let reference = one(facts.consumes.iter().filter(|row| {
        at_formation(&row.point) && row.local == actual.local && row.projection.is_empty()
    }))?;
    let (
        Present(cell_window),
        Present(reference_window),
        Present(cell_paths),
        Present(reference_paths),
        Present(actual_base),
    ) = (
        &original.projected,
        &reference.projected,
        &original.pointer_paths,
        &reference.pointer_paths,
        &actual.base,
    )
    else {
        return None;
    };
    if cell_window.use_end.checked_sub(cell_window.use_start) != Some(1)
        || cell_window.def_end.checked_sub(cell_window.def_start) != Some(1)
        || reference_window
            .use_end
            .checked_sub(reference_window.use_start)
            != Some(2)
        || reference_window
            .def_end
            .checked_sub(reference_window.def_start)
            != Some(2)
        || reference.ssa_def.is_none()
        || reference.ssa_def != actual.ssa_use
        || actual_base.use_start != reference_window.def_start
        || actual_base.use_end != reference_window.def_end
        || actual_window.use_start != reference_window.def_start.checked_add(1)?
        || actual_window.use_end != reference_window.def_end
        || actual_window.def_end.checked_sub(actual_window.def_start) != Some(1)
    {
        return None;
    }
    let [cell_path] = cell_paths.as_slice() else {
        return None;
    };
    let [
        PathStep::Field {
            structure, index, ..
        },
    ] = cell_path.as_slice()
    else {
        return None;
    };
    let [outer, inner] = reference_paths.as_slice() else {
        return None;
    };
    if !outer.is_empty()
        || inner.len() != 2
        || inner[0] != PathStep::Deref
        || inner[1] != cell_path[0]
    {
        return None;
    }
    let [matched] = boundary.matched.as_slice() else {
        return None;
    };
    if matched.actual
        != (Variables::UseDef {
            use_var: actual_window.use_start,
            def_var: actual_window.def_start,
        })
    {
        return None;
    }
    let peel = boundary.reference_peel.as_ref()?;
    if peel.effective_formal
        != match matched.formal {
            Variables::UseDef { use_var, def_var } => Window::UseDef {
                use_start: use_var,
                use_end: use_var.checked_add(1)?,
                def_start: def_var,
                def_end: def_var.checked_add(1)?,
            },
            _ => return None,
        }
    {
        return None;
    }
    Some(Candidate {
        call: CallKey {
            construction: boundary.point.construction,
            caller: function.clone(),
            block: call.site.block,
            statement: call.site.statement,
            callee: callee.clone(),
        },
        argument,
        boundary: boundary.ordinal,
        field_key: format!("{structure}::field{index}@d0"),
        cell: cell.clone(),
        formation: original.point.clone(),
        original_consume: original.ordinal,
        reference_consume: reference.ordinal,
        address: actual.point.clone(),
        registration: registration.ordinal,
        reference_use: actual.ordinal,
    })
}

fn operand_place(value: &super::super::ownership_access::OperandSyntax) -> Option<&PlaceSyntax> {
    use super::super::ownership_access::OperandSyntax;
    match value {
        OperandSyntax::Copy { place } | OperandSyntax::Move { place } => Some(place),
        _ => None,
    }
}
fn uses(expression: &super::super::ownership_access::Expression, local: u32) -> bool {
    use super::super::ownership_access::Expression;
    match expression {
        Expression::Value { operand } | Expression::Cast { operand, .. } => {
            operand_place(operand).is_some_and(|place| place.local == local)
        }
        Expression::Borrow { place, .. }
        | Expression::RawAddress { place, .. }
        | Expression::CopyForDeref { place } => place.local == local,
        Expression::Aggregate { operands, .. } | Expression::Call { operands } => operands
            .iter()
            .any(|operand| operand_place(operand).is_some_and(|place| place.local == local)),
        Expression::Unrepresented { .. } => true,
    }
}
fn one<T>(mut values: impl Iterator<Item = T>) -> Option<T> {
    let value = values.next()?;
    values.next().is_none().then_some(value)
}

pub(crate) fn at_boundary(
    facts: &Facts,
    boundary: &super::super::ownership_boundary::Substitution,
) -> Option<Candidate> {
    candidate(facts, boundary)
}

pub(crate) fn frame<'a>(
    facts: &'a Facts,
    candidate: &Candidate,
) -> Option<&'a super::super::ownership_evidence::Equation> {
    use super::super::ownership_occurrence::Availability::Present;
    let early = early(facts, &candidate.formation)?;
    if early.call != candidate.call
        || early.argument != candidate.argument
        || early.original_consume != candidate.original_consume
        || early.reference_consume != candidate.reference_consume
    {
        return None;
    }
    one(facts.equations.iter().filter(|row| row.point == candidate.formation
        && row.operation == "guarded-original-cell-frame" && row.validate().is_ok()
        && row.transfer.as_ref().is_some_and(|transfer| matches!((&transfer.source, &transfer.destination), (Present(source), Present(destination))
            if source.consume == candidate.original_consume && destination.consume == candidate.reference_consume))))
}

/// Exact call alternatives. Flat boundary matched pairs retain the legacy
/// proxy identity; this separate record supplies the original-cell true arm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallArm {
    pub(crate) candidate: Candidate,
    pub(crate) guard: super::facts::EquationId,
    pub(crate) formal: (u32, u32),
    pub(crate) legacy: (u32, u32),
    pub(crate) original: (u32, u32),
}

pub(crate) fn call_arm(
    facts: &Facts,
    boundary: &super::super::ownership_boundary::Substitution,
    aliases: &std::collections::BTreeMap<super::facts::EquationId, super::facts::EquationId>,
) -> Option<CallArm> {
    use super::{
        super::{
            ownership_boundary::{LicensingRole, Variables},
            ownership_occurrence::Availability::Present,
        },
        facts::EquationId,
    };
    if boundary.licensing_role != LicensingRole::OriginalCell {
        return None;
    }
    let candidate = candidate(facts, boundary)?;
    let native = frame(facts, &candidate)?;
    let native_id = EquationId {
        construction: native.point.construction,
        ordinal: native.ordinal,
    };
    let guard = *aliases.get(&native_id)?;
    let original = one(facts.consumes.iter().filter(|row| {
        row.point.construction == candidate.call.construction
            && row.ordinal == candidate.original_consume
    }))?;
    let Present(window) = &original.projected else {
        return None;
    };
    let [pair] = boundary.matched.as_slice() else {
        return None;
    };
    let (
        Variables::UseDef {
            use_var: formal_pre,
            def_var: formal_post,
        },
        Variables::UseDef {
            use_var: legacy_pre,
            def_var: legacy_post,
        },
    ) = (&pair.formal, &pair.actual)
    else {
        return None;
    };
    let Variables::UseDef {
        use_var: outer_pre,
        def_var: outer_post,
    } = boundary.reference_peel.as_ref()?.skipped
    else {
        return None;
    };
    for (operation, variables) in [
        (
            "guarded-original-cell-argument",
            vec![
                *formal_pre,
                *formal_post,
                window.use_start,
                window.def_start,
            ],
        ),
        (
            "guarded-original-cell-legacy",
            vec![*formal_pre, *legacy_pre, *formal_post, *legacy_post],
        ),
        ("guarded-original-cell-outer", vec![outer_pre, outer_post]),
    ] {
        one(facts.equations.iter().filter(|row| {
            row.point == boundary.point
                && row.operation == operation
                && row.variables == variables
                && row.transfer.is_none()
                && row.validate().is_ok()
                && aliases.get(&EquationId {
                    construction: row.point.construction,
                    ordinal: row.ordinal,
                }) == Some(&guard)
        }))?;
    }
    Some(CallArm {
        candidate,
        guard,
        formal: (*formal_pre, *formal_post),
        legacy: (*legacy_pre, *legacy_post),
        original: (window.use_start, window.def_start),
    })
}

pub(crate) fn validate_calls(
    facts: &Facts,
    aliases: &std::collections::BTreeMap<super::facts::EquationId, super::facts::EquationId>,
) -> Result<(), String> {
    use super::super::ownership_boundary::LicensingRole;
    for boundary in &facts.boundary_substitutions {
        if boundary.licensing_role == LicensingRole::OriginalCell
            && call_arm(facts, boundary, aliases).is_none()
        {
            return Err(
                "original-cell call lost its exact formation/proxy/guard alternatives".into(),
            );
        }
    }
    for row in facts.equations.iter().filter(|row| {
        matches!(
            row.operation.as_str(),
            "guarded-original-cell-argument"
                | "guarded-original-cell-legacy"
                | "guarded-original-cell-outer"
        )
    }) {
        let binding = aliases.get(&super::facts::EquationId {
            construction: row.point.construction,
            ordinal: row.ordinal,
        });
        if facts
            .boundary_substitutions
            .iter()
            .filter(|boundary| {
                boundary.point == row.point
                    && boundary.licensing_role == LicensingRole::OriginalCell
                    && call_arm(facts, boundary, aliases).is_some_and(|arm| {
                        if Some(&arm.guard) != binding {
                            return false;
                        }
                        use super::super::ownership_boundary::Variables;
                        let expected = match row.operation.as_str() {
                            "guarded-original-cell-argument" => {
                                vec![arm.formal.0, arm.formal.1, arm.original.0, arm.original.1]
                            }
                            "guarded-original-cell-legacy" => {
                                vec![arm.formal.0, arm.legacy.0, arm.formal.1, arm.legacy.1]
                            }
                            "guarded-original-cell-outer" => {
                                match boundary.reference_peel.as_ref().map(|peel| &peel.skipped) {
                                    Some(Variables::UseDef { use_var, def_var }) => {
                                        vec![*use_var, *def_var]
                                    }
                                    _ => return false,
                                }
                            }
                            _ => return false,
                        };
                        row.variables == expected
                            && row.validate().is_ok()
                            && row.transfer.is_none()
                    })
            })
            .count()
            != 1
        {
            return Err("original-cell call equation lacks one explicit boundary role".into());
        }
    }
    Ok(())
}
