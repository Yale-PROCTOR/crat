//! Exact conditional caller folding. These records do not grant ownership.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    facts::{EquationId, Facts},
    matched::CallKey,
    transport::Node,
};
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum FieldPremise {
    Owning { field: String },
    Unused { field: String },
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Descendant {
    pub(crate) path: Vec<super::super::ownership_occurrence::PathStep>,
    pub(crate) formal_use: u32,
    pub(crate) formal_def: u32,
    pub(crate) input: Node,
    pub(crate) output: Node,
    pub(crate) premise: FieldPremise,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Proof {
    pub(crate) call: CallKey,
    pub(crate) boundary: usize,
    pub(crate) receiver_boundary: usize,
    pub(crate) actual_consume: usize,
    pub(crate) actual_before: Node,
    pub(crate) actual_after: Node,
    pub(crate) receiver: Node,
    pub(crate) descendants: Vec<Descendant>,
    /// An owning input is a premise, not a source endpoint invented at the call.
    pub(crate) requires_consuming_root: bool,
    pub(crate) internal: super::fold_internal::Proof,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Error {
    Unsupported,
    NativeCall,
    Boundary,
    Type,
    Internal(super::fold_internal::Error),
    FieldScheme(String),
}
pub(crate) fn certify(
    facts: &Facts,
    call: &CallKey,
    argument: usize,
    owning_fields: &BTreeSet<String>,
) -> Result<Proof, Error> {
    certify_metadata(
        facts,
        call,
        argument,
        owning_fields,
        &super::matched::guard_aliases(&facts.guards),
    )
}
fn one<T>(items: impl IntoIterator<Item = T>) -> Result<T, Error> {
    let mut items = items.into_iter();
    let value = items.next().ok_or(Error::Boundary)?;
    if items.next().is_some() {
        return Err(Error::Boundary);
    }
    Ok(value)
}

pub(crate) fn certify_metadata(
    facts: &Facts,
    call: &CallKey,
    argument: usize,
    owning_fields: &BTreeSet<String>,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<Proof, Error> {
    let parameter = u32::try_from(argument)
        .ok()
        .and_then(|a| a.checked_add(1))
        .ok_or(Error::Boundary)?;
    let internal_result = super::fold_internal::certify_linear_metadata(
        facts,
        call.construction,
        &call.callee,
        parameter,
        aliases,
    );
    admit_internal(&internal_result)?;
    let internal = internal_result.map_err(Error::Internal)?;
    let candidate = join_native(facts, call, argument, owning_fields, &internal.used_fields)?;
    // R304-9/R304-10: a write or copy the named store inventory could not
    // resolve denies the field scheme it may alias. The inventory fails closed,
    // so the fold holds rather than treating the cell as unwritten.
    for descendant in &candidate.descendants {
        let (FieldPremise::Owning { field } | FieldPremise::Unused { field }) = &descendant.premise;
        if facts
            .field_support_inputs
            .unsupported
            .iter()
            .any(|effect| effect.field_keys.iter().any(|key| key == field))
        {
            return Err(Error::FieldScheme(field.clone()));
        }
    }
    Ok(Proof {
        call: candidate.call,
        boundary: candidate.boundary,
        receiver_boundary: candidate.receiver_boundary,
        actual_consume: candidate.actual_consume,
        actual_before: candidate.actual_before,
        actual_after: candidate.actual_after,
        receiver: candidate.receiver,
        descendants: candidate.descendants,
        requires_consuming_root: candidate.requires_consuming_root,
        internal,
    })
}

pub(crate) fn join_native(
    facts: &Facts,
    call: &CallKey,
    argument: usize,
    owning_fields: &BTreeSet<String>,
    used_fields: &[String],
) -> Result<Candidate, Error> {
    use super::super::{
        ownership_access::PlaceSyntax,
        ownership_boundary::{self, LicensingRole, Role, Variables, Window},
        ownership_occurrence::{Availability::Present, PathStep},
    };
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_deref() == Some(&call.caller)
    };
    let at_call = |b: &&super::super::ownership_boundary::Substitution| {
        scope(&b.point)
            && b.point.block == Some(call.block)
            && b.point.statement == Some(call.statement)
            && b.callee.as_ref() == Some(&call.callee)
    };
    let boundary = one(facts
        .boundary_substitutions
        .iter()
        .filter(at_call)
        .filter(|b| b.role == Role::CallArgument && b.argument_index == Some(argument)))?;
    let parameter = boundary.formal_local.ok_or(Error::Boundary)?;
    if parameter != argument as u32 + 1
        || boundary.reference_peel.is_some()
        || boundary.licensing_role != LicensingRole::Legacy
    {
        return Err(Error::Unsupported);
    }
    let occurrences = facts
        .source_occurrences
        .get(&call.caller)
        .ok_or(Error::NativeCall)?;
    let occurrence = one(occurrences.iter().filter(|o| {
        o.site.function == call.caller
            && o.site.block == call.block
            && o.site.statement == call.statement
            && o.callee
                == Some(super::super::origin_evidence::SourceCallee::Local(
                    call.callee.clone(),
                ))
    }))
    .map_err(|_| Error::NativeCall)?;
    let coverage = facts.caller_coverage.as_ref().ok_or(Error::NativeCall)?;
    if !coverage
        .local_calls
        .iter()
        .any(|c| c.site == occurrence.site && c.target == call.callee)
        || !coverage.compiler_bodies.contains(&call.caller)
        || !coverage.compiler_bodies.contains(&call.callee)
    {
        return Err(Error::NativeCall);
    }
    let super::super::ownership_access::Expression::Call { operands } =
        &occurrence.syntax.expression
    else {
        return Err(Error::NativeCall);
    };
    let Some(
        super::super::ownership_access::OperandSyntax::Copy { place }
        | super::super::ownership_access::OperandSyntax::Move { place },
    ) = operands.get(argument)
    else {
        return Err(Error::NativeCall);
    };
    let Present(registration_id) = boundary.call_arg_registration else {
        return Err(Error::NativeCall);
    };
    let registration = one(facts
        .call_arg_registrations
        .iter()
        .filter(|r| scope(&r.point) && r.ordinal == registration_id))
    .map_err(|_| Error::NativeCall)?;
    if !place.projection.is_empty()
        || registration.proxy_local != place.local
        || registration.by_reference
    {
        return Err(Error::NativeCall);
    }
    let internal = input_shape(facts, call, parameter)?;
    let boundaries: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|b| scope(&b.point))
        .cloned()
        .collect();
    let registrations: Vec<_> = facts
        .call_arg_registrations
        .iter()
        .filter(|r| scope(&r.point))
        .cloned()
        .collect();
    let consumes: Vec<_> = facts
        .consumes
        .iter()
        .filter(|c| scope(&c.point))
        .cloned()
        .collect();
    let equations: Vec<_> = facts
        .equations
        .iter()
        .filter(|e| scope(&e.point))
        .cloned()
        .collect();
    ownership_boundary::validate_shapes(&call.caller, &boundaries, &registrations)
        .map_err(|_| Error::Boundary)?;
    ownership_boundary::validate_links(
        &call.caller,
        &boundaries,
        &registrations,
        &consumes,
        &equations,
    )
    .map_err(|_| Error::Boundary)?;
    let (
        Present(Window::UseDef {
            use_start: a0,
            use_end: a1,
            def_start: a2,
            def_end: a3,
        }),
        Present(Window::UseDef {
            use_start: f0,
            use_end: f1,
            def_start: f2,
            def_end: f3,
        }),
    ) = (&boundary.actual, &boundary.formal)
    else {
        return Err(Error::Boundary);
    };
    if *a1 != *a0 + 1
        || *a3 != *a2 + 1
        || *f1 - *f0 != *f3 - *f2
        || *f1 - *f0 != internal.input_components.len() as u32
        || !boundary.unmatched_actual_vars.is_empty()
    {
        return Err(Error::Boundary);
    }
    let [matched] = boundary.matched.as_slice() else { return Err(Error::Boundary) };
    if matched.actual
        != (Variables::UseDef {
            use_var: *a0,
            def_var: *a2,
        })
        || matched.formal
            != (Variables::UseDef {
                use_var: *f0,
                def_var: *f2,
            })
    {
        return Err(Error::Boundary);
    }
    let Present(consume_id) = boundary.actual_occurrence else { return Err(Error::Boundary) };
    let actual = one(consumes.iter().filter(|c| c.ordinal == consume_id))?;
    let types = facts.fold_types.as_ref().ok_or(Error::Type)?;
    let actual_type = one(types.places.iter().filter(|p| {
        p.function == call.caller
            && p.place
                == (PlaceSyntax {
                    local: actual.local,
                    projection: actual.projection.clone(),
                })
    }))
    .map_err(|_| Error::Type)?;
    let formal_type = one(types.places.iter().filter(|p| {
        p.function == call.callee
            && p.place
                == (PlaceSyntax {
                    local: parameter,
                    projection: vec![],
                })
    }))
    .map_err(|_| Error::Type)?;
    if actual_type.pointee_struct.as_ref() != Some(&internal.structure)
        || actual_type.pointee_struct != formal_type.pointee_struct
        || actual_type.pointee_type != formal_type.pointee_type
    {
        return Err(Error::Type);
    }
    let declaration = one(types
        .structures
        .iter()
        .filter(|s| s.identity == internal.structure))
    .map_err(|_| Error::Type)?;
    let callee_scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_deref() == Some(&call.callee)
    };
    let entry = one(facts.boundary_substitutions.iter().filter(|b| {
        callee_scope(&b.point) && b.ordinal == internal.entry_boundary && b.role == Role::Entry
    }))?;
    let output = one(facts.boundary_substitutions.iter().filter(|b| {
        callee_scope(&b.point) && b.role == Role::ExitOutput && b.formal_local == Some(parameter)
    }))?;
    let terminal = one(facts
        .terminals
        .iter()
        .filter(|t| callee_scope(&t.point) && t.local == parameter))?;
    let Present(values) = &terminal.values else { return Err(Error::Boundary) };
    let mapped =
        |b: &super::super::ownership_boundary::Substitution, var: u32| -> Result<u32, Error> {
            let matched = one(b
                .matched
                .iter()
                .filter(|p| p.actual == Variables::Single { var }))?;
            let Variables::Single { var } = matched.formal else { return Err(Error::Boundary) };
            Ok(var)
        };
    let node = |var| Node {
        construction: call.construction,
        var,
    };
    if mapped(entry, internal.input_components[0].1.var)? != *f0
        || mapped(output, values[0].var)? != *f2
    {
        return Err(Error::Boundary);
    }
    let mut descendants = Vec::new();
    for (path, input) in internal.input_components.iter().skip(1) {
        let [
            PathStep::Deref,
            PathStep::Field {
                structure, index, ..
            },
        ] = path.as_slice()
        else {
            return Err(Error::Type);
        };
        if structure != &internal.structure {
            return Err(Error::Type);
        }
        let field = one(declaration.fields.iter().filter(|f| f.index == *index))
            .map_err(|_| Error::Type)?;
        let key = field.field_key.as_ref().ok_or(Error::Type)?;
        let premise = if owning_fields.contains(key) {
            FieldPremise::Owning { field: key.clone() }
        } else if !used_fields.contains(key) {
            FieldPremise::Unused { field: key.clone() }
        } else {
            return Err(Error::FieldScheme(key.clone()));
        };
        let value = one(values.iter().filter(|v| v.path == Present(path.clone())))?;
        descendants.push(Descendant {
            path: path.clone(),
            formal_use: mapped(entry, input.var)?,
            formal_def: mapped(output, value.var)?,
            input: *input,
            output: node(value.var),
            premise,
        });
    }
    let expected: BTreeSet<_> = (*f0 + 1..*f1).chain(*f2 + 1..*f3).collect();
    let recorded: BTreeSet<_> = boundary.unmatched_formal_vars.iter().copied().collect();
    let folded: Vec<_> = descendants
        .iter()
        .flat_map(|d| [d.formal_use, d.formal_def])
        .collect();
    if expected.is_empty()
        || recorded != expected
        || recorded.len() != boundary.unmatched_formal_vars.len()
        || folded.iter().copied().collect::<BTreeSet<_>>() != expected
        || folded.len() != expected.len()
    {
        return Err(Error::Boundary);
    }
    let receiver = one(facts
        .boundary_substitutions
        .iter()
        .filter(at_call)
        .filter(|b| b.role == Role::ReturnReceiver))?;
    let Present(receiver_id) = receiver.actual_occurrence else { return Err(Error::NativeCall) };
    let receiver_consume =
        one(consumes.iter().filter(|c| c.ordinal == receiver_id)).map_err(|_| Error::NativeCall)?;
    if receiver_consume.local != occurrence.syntax.destination.local
        || receiver_consume.projection != occurrence.syntax.destination.projection
        || receiver_consume.point != receiver.point
    {
        return Err(Error::NativeCall);
    }
    let receiver_type = one(types
        .places
        .iter()
        .filter(|p| p.function == call.caller && p.place == occurrence.syntax.destination))
    .map_err(|_| Error::Type)?;
    let output_type = one(types.places.iter().filter(|p| {
        p.function == call.callee
            && p.place
                == (PlaceSyntax {
                    local: 0,
                    projection: vec![],
                })
    }))
    .map_err(|_| Error::Type)?;
    if receiver_type.pointee_struct != formal_type.pointee_struct
        || receiver_type.pointee_type != formal_type.pointee_type
        || output_type.pointee_struct != formal_type.pointee_struct
        || output_type.pointee_type != formal_type.pointee_type
    {
        return Err(Error::Type);
    }
    let (
        Present(Window::UseDef {
            use_start: r0,
            use_end: r1,
            def_start: r2,
            def_end: r3,
        }),
        Present(Window::Single { start: q0, end: q1 }),
    ) = (&receiver.actual, &receiver.formal)
    else {
        return Err(Error::Boundary);
    };
    let mut actual_vars = Vec::new();
    let mut formal_vars = Vec::new();
    for pair in &receiver.matched {
        let (Variables::UseDef { use_var, def_var }, Variables::Single { var }) =
            (&pair.actual, &pair.formal)
        else {
            return Err(Error::Boundary);
        };
        actual_vars.extend([*use_var, *def_var]);
        formal_vars.push(*var);
    }
    let actual_expected: BTreeSet<_> = (*r0..*r1).chain(*r2..*r3).collect();
    let formal_expected: BTreeSet<_> = (*q0..*q1).collect();
    if actual_vars.iter().copied().collect::<BTreeSet<_>>() != actual_expected
        || actual_vars.len() != actual_expected.len()
        || formal_vars.iter().copied().collect::<BTreeSet<_>>() != formal_expected
        || formal_vars.len() != formal_expected.len()
    {
        return Err(Error::Boundary);
    }
    let returned = one(facts
        .terminals
        .iter()
        .filter(|t| callee_scope(&t.point) && t.local == 0))?;
    let Present(return_values) = &returned.values else { return Err(Error::Boundary) };
    let exit = one(facts
        .boundary_substitutions
        .iter()
        .filter(|b| callee_scope(&b.point) && b.role == Role::ExitReturn))?;
    let return_var = mapped(exit, return_values.first().ok_or(Error::Boundary)?.var)?;
    let pair = one(receiver
        .matched
        .iter()
        .filter(|p| p.formal == Variables::Single { var: return_var }))?;
    let Variables::UseDef { def_var, .. } = pair.actual else { return Err(Error::Boundary) };
    if !receiver.unmatched_actual_vars.is_empty() || !receiver.unmatched_formal_vars.is_empty() {
        return Err(Error::Boundary);
    }
    Ok(Candidate {
        call: call.clone(),
        boundary: boundary.ordinal,
        receiver_boundary: receiver.ordinal,
        actual_consume: actual.ordinal,
        actual_before: node(*a0),
        actual_after: node(*a2),
        receiver: node(def_var),
        descendants,
        requires_consuming_root: true,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Candidate {
    pub(crate) call: CallKey,
    pub(crate) boundary: usize,
    pub(crate) receiver_boundary: usize,
    pub(crate) actual_consume: usize,
    pub(crate) actual_before: Node,
    pub(crate) actual_after: Node,
    pub(crate) receiver: Node,
    pub(crate) descendants: Vec<Descendant>,
    /// An owning input is a premise, not a source endpoint invented at the call.
    pub(crate) requires_consuming_root: bool,
}

pub(crate) fn admit_internal(
    result: &Result<super::fold_internal::Proof, super::fold_internal::Error>,
) -> Result<(), Error> {
    result
        .as_ref()
        .map(|_| ())
        .map_err(|error| Error::Internal(error.clone()))
}

struct InputShape {
    structure: String,
    entry_boundary: usize,
    input_components: Vec<(Vec<super::super::ownership_occurrence::PathStep>, Node)>,
}

// Structural inventory only: this does not certify token disposition.
fn input_shape(facts: &Facts, call: &CallKey, parameter: u32) -> Result<InputShape, Error> {
    use super::super::{
        ownership_boundary::{self, Role, Window},
        ownership_occurrence::Availability::Present,
    };
    super::fold_coverage::validate(facts, call.construction, &call.callee)
        .map_err(|_| Error::Boundary)?;
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_deref() == Some(&call.callee)
    };
    let boundaries: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|b| scope(&b.point))
        .cloned()
        .collect();
    let registrations: Vec<_> = facts
        .call_arg_registrations
        .iter()
        .filter(|b| scope(&b.point))
        .cloned()
        .collect();
    ownership_boundary::validate_shapes(&call.callee, &boundaries, &registrations)
        .map_err(|_| Error::Boundary)?;
    let entry = one(boundaries
        .iter()
        .filter(|b| b.role == Role::Entry && b.formal_local == Some(parameter)))?;
    let Present(Window::Single { start, end }) = &entry.actual else { return Err(Error::Boundary) };
    let body = one(facts.body_rosters.iter().filter(|b| scope(&b.point)))?;
    let version = one(body.versions.iter().filter(|v| {
        v.local == parameter && v.definition == super::coverage::DefinitionKind::Entry
    }))?;
    if version.variables.iter().copied().ne(*start..*end) {
        return Err(Error::Boundary);
    }
    let terminal = one(facts
        .terminals
        .iter()
        .filter(|t| scope(&t.point) && t.local == parameter))?;
    let Present(values) = &terminal.values else { return Err(Error::Boundary) };
    if values.len() != version.variables.len() {
        return Err(Error::Boundary);
    }
    let ty = one(facts
        .fold_types
        .as_ref()
        .ok_or(Error::Type)?
        .places
        .iter()
        .filter(|p| {
            p.function == call.callee && p.place.local == parameter && p.place.projection.is_empty()
        }))
    .map_err(|_| Error::Type)?;
    let structure = ty.pointee_struct.clone().ok_or(Error::Type)?;
    let input_components = values
        .iter()
        .zip(&version.variables)
        .map(|(value, &var)| {
            let Present(path) = &value.path else { return Err(Error::Boundary) };
            Ok((
                path.clone(),
                Node {
                    construction: call.construction,
                    var,
                },
            ))
        })
        .collect::<Result<_, _>>()?;
    Ok(InputShape {
        structure,
        entry_boundary: entry.ordinal,
        input_components,
    })
}
