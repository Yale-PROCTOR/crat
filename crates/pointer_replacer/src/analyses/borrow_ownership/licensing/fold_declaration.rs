//! Exact fold declarations. Post-freeze caller certification disposes each guard.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    facts::{EquationId, Facts},
    matched::CallKey,
};
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Declaration {
    pub(crate) guard: EquationId,
    pub(crate) boundary: usize,
    pub(crate) call: CallKey,
    pub(crate) argument: usize,
}

pub(crate) fn eligible(
    facts: &Facts,
    b: &super::super::ownership_boundary::Substitution,
) -> Option<(CallKey, usize)> {
    use super::super::{
        ownership_boundary::{LicensingRole, Role, Variables, Window},
        ownership_occurrence::Availability::Present,
    };
    if b.role != Role::CallArgument
        || b.licensing_role != LicensingRole::Legacy
        || b.reference_peel.is_some()
        || !b.unmatched_actual_vars.is_empty()
    {
        return None;
    }
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
    ) = (&b.actual, &b.formal)
    else {
        return None;
    };
    if a0.checked_add(1) != Some(*a1)
        || a2.checked_add(1) != Some(*a3)
        || f1.checked_sub(*f0)? <= 1
        || f1.checked_sub(*f0) != f3.checked_sub(*f2)
    {
        return None;
    }
    let [pair] = b.matched.as_slice() else { return None };
    if pair.actual
        != (Variables::UseDef {
            use_var: *a0,
            def_var: *a2,
        })
        || pair.formal
            != (Variables::UseDef {
                use_var: *f0,
                def_var: *f2,
            })
    {
        return None;
    }
    let expected: BTreeSet<_> = (*f0 + 1..*f1).chain(*f2 + 1..*f3).collect();
    if expected != b.unmatched_formal_vars.iter().copied().collect()
        || expected.len() != b.unmatched_formal_vars.len()
    {
        return None;
    }
    let Present(id) = b.actual_occurrence else { return None };
    let Present(reg) = b.call_arg_registration else { return None };
    let caller = b.point.function.as_ref()?;
    let callee = b.callee.as_ref()?;
    let actual = facts.consumes.iter().find(|c| {
        c.point.construction == b.point.construction
            && c.ordinal == id
            && c.point.function.as_ref() == Some(caller)
    })?;
    if !facts.call_arg_registrations.iter().any(|r| {
        r.point.construction == b.point.construction
            && r.ordinal == reg
            && r.point.function.as_ref() == Some(caller)
            && !r.by_reference
            && r.source_occurrence == Present(id)
    }) {
        return None;
    }
    let types = facts.fold_types.as_ref()?;
    let actual_type = types.places.iter().find(|p| {
        &p.function == caller
            && p.place.local == actual.local
            && p.place.projection == actual.projection
    })?;
    let formal_type = types.places.iter().find(|p| {
        &p.function == callee
            && Some(p.place.local) == b.formal_local
            && p.place.projection.is_empty()
    })?;
    if actual_type.pointee_struct.is_none()
        || actual_type.pointee_struct != formal_type.pointee_struct
        || actual_type.pointee_type != formal_type.pointee_type
    {
        return None;
    }
    Some((
        CallKey {
            construction: b.point.construction,
            caller: caller.clone(),
            block: b.point.block?,
            statement: b.point.statement?,
            callee: callee.clone(),
        },
        b.argument_index?,
    ))
}

pub(crate) fn validate(
    facts: &Facts,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<(), String> {
    let markers: Vec<_> = facts
        .equations
        .iter()
        .filter(|e| e.operation == "guarded-fold-call")
        .collect();
    let Some(declarations) = &facts.fold_declarations else {
        return if markers.is_empty() {
            Ok(())
        } else {
            Err("fold declarations unavailable with marker".into())
        };
    };
    let expected: BTreeMap<_, _> = facts
        .boundary_substitutions
        .iter()
        .filter_map(|b| eligible(facts, b).map(|key| ((b.point.construction, b.ordinal), key)))
        .collect();
    let mut seen = BTreeSet::new();
    let mut guards = BTreeSet::new();
    for d in declarations {
        if !seen.insert((d.guard.construction, d.boundary))
            || !guards.insert(d.guard)
            || expected.get(&(d.guard.construction, d.boundary))
                != Some(&(d.call.clone(), d.argument))
        {
            return Err("fold declaration boundary inventory mismatch".into());
        }
        let rows: Vec<_> = markers
            .iter()
            .filter(|e| {
                e.point.construction == d.guard.construction && e.ordinal == d.guard.ordinal
            })
            .collect();
        let [row] = rows.as_slice() else {
            return Err("fold declaration marker missing or ambiguous".into());
        };
        if row.point.function.as_ref() != Some(&d.call.caller)
            || row.point.block != Some(d.call.block)
            || row.point.statement != Some(d.call.statement)
            || row.validate().is_err()
            || row.transfer.is_some()
            || aliases.get(&d.guard) != Some(&d.guard)
        {
            return Err("fold declaration predicate mismatch".into());
        }
    }
    if seen != expected.keys().copied().collect() || markers.len() != guards.len() {
        return Err("fold declaration coverage incomplete".into());
    }
    Ok(())
}

pub(crate) fn validate_selection(
    facts: &Facts,
    aliases: &BTreeMap<EquationId, EquationId>,
    values: Option<&[(EquationId, bool)]>,
) -> Result<(), String> {
    validate_selection_coverage(facts, aliases, values)?;
    if values.is_some_and(|values| values.iter().any(|(_, selected)| *selected)) {
        return Err("pending fold selected without closure".into());
    }
    Ok(())
}

/// Selected values need the caller custody validator after this identity check.
pub(crate) fn validate_selection_coverage(
    facts: &Facts,
    aliases: &BTreeMap<EquationId, EquationId>,
    values: Option<&[(EquationId, bool)]>,
) -> Result<(), String> {
    validate(facts, aliases)?;
    let Some(declarations) = &facts.fold_declarations else {
        return if values.is_none() {
            Ok(())
        } else {
            Err("fold selection availability differs".into())
        };
    };
    let values = values.ok_or("fold selection availability differs")?;
    let selected: BTreeMap<_, _> = values.iter().copied().collect();
    let expected: BTreeSet<_> = declarations.iter().map(|d| d.guard).collect();
    if selected.len() != values.len()
        || selected.keys().copied().collect::<BTreeSet<_>>() != expected
    {
        return Err("fold selection coverage differs".into());
    }
    Ok(())
}
