//! Exact five-function effect evidence. Ownership and replay are separate obligations.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    super::{
        export::ProjKey,
        origin_evidence::{SourceCallee, SourceOccurrence, SourceSite},
        ownership_access::{Expression, ImmediateOrigin, OperandSyntax, PlaceSyntax},
        ownership_boundary::Role,
    },
    cell_effects,
    facts::{EquationId, Facts},
    field_support::FieldProof,
    matched::{CallKey, SourceLineage, TerminalTarget},
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Effects {
    pub(crate) source: EquationId,
    pub(crate) free: EquationId,
    pub(crate) calls: Vec<CallKey>,
    pub(crate) initialized_cell: SourceSite,
    pub(crate) payload_write: SourceSite,
    pub(crate) field_store: SourceSite,
    pub(crate) field_load: SourceSite,
    pub(crate) field_reset: SourceSite,
    pub(crate) returns: Vec<SourceSite>,
    pub(crate) formations: Vec<SourceSite>,
    pub(crate) addresses: Vec<SourceSite>,
    pub(crate) checked_occurrences: Vec<SourceSite>,
    pub(crate) size_of_calls: Vec<SourceSite>,
}

fn one<T>(items: impl IntoIterator<Item = T>) -> Option<T> {
    let mut it = items.into_iter();
    let value = it.next()?;
    it.next().is_none().then_some(value)
}
fn operand_place(value: &OperandSyntax) -> Option<&PlaceSyntax> {
    match value {
        OperandSyntax::Copy { place } | OperandSyntax::Move { place } => Some(place),
        _ => None,
    }
}
fn at(call: &CallKey, row: &SourceOccurrence) -> bool {
    call.caller == row.site.function
        && call.block == row.site.block
        && call.statement == row.site.statement
}
fn same_point(point: &super::super::ownership_evidence::Point, site: &SourceSite) -> bool {
    point.function.as_ref() == Some(&site.function)
        && point.block == Some(site.block)
        && point.statement == Some(site.statement)
}

// The roles are derived from existing exact applications, never function spelling.
pub(crate) fn effects(
    facts: &Facts,
    put: &cell_effects::Candidate,
    release: &cell_effects::Candidate,
    field: &FieldProof,
) -> Option<Effects> {
    if put.call.construction != release.call.construction
        || put.call.caller != release.call.caller
        || put.cell != release.cell
        || put.field_key != release.field_key
        || field.field_key != put.field_key
        || !field.stores.is_empty()
    {
        return None;
    }
    let store = one(&field.input_stores)?;
    let application = one(&store.applications)?;
    if application.application.call != put.call {
        return None;
    }
    let alternative = one(&application.alternatives)?;
    if !alternative.pending_outputs.is_empty() {
        return None;
    }
    let forward = one(&alternative.forwarded_returns)?;
    let SourceLineage::Exact(source_path) = &alternative.free.source.lineage else { return None };
    let make = one(source_path)?.clone();
    let take = forward.call.clone();
    if make.caller != put.call.caller
        || take.caller != release.call.callee
        || forward.call_path != [release.call.clone(), take.clone()]
        || alternative.free.terminal.lineage != SourceLineage::Exact(vec![release.call.clone()])
        || forward.continuation.source != alternative.free.source
        || forward.continuation.terminal != alternative.free.terminal
    {
        return None;
    }
    let TerminalTarget::Free(free) = alternative.free.terminal.target else { return None };
    let source = alternative.free.source.endpoint;
    let source_eq = one(facts
        .equations
        .iter()
        .filter(|e| e.point.construction == source.construction && e.ordinal == source.ordinal))?;
    let free_eq = one(facts
        .equations
        .iter()
        .filter(|e| e.point.construction == free.construction && e.ordinal == free.ordinal))?;
    if source_eq.operation != "source"
        || free_eq.operation != "sink"
        || source_eq.point.function.as_ref() != Some(&make.callee)
        || free_eq.point.function.as_ref() != Some(&release.call.callee)
        || source_eq.endpoint.as_ref()?.callee != "malloc"
        || source_eq.endpoint.as_ref()?.outcome.is_some()
        || free_eq.endpoint.as_ref()?.callee != "free"
        || free_eq.endpoint.as_ref()?.outcome.is_some()
    {
        return None;
    }
    let names = [
        &put.call.caller,
        &make.callee,
        &put.call.callee,
        &take.callee,
        &release.call.callee,
    ];
    if names.iter().copied().collect::<BTreeSet<_>>().len() != 5
        || facts.source_occurrences.keys().collect::<BTreeSet<_>>() != names.into_iter().collect()
    {
        return None;
    }
    let outer = |candidate: &cell_effects::Candidate| {
        one(facts.boundary_substitutions.iter().filter(|b| {
            b.point.construction == candidate.call.construction && b.ordinal == candidate.boundary
        }))?
        .formal_local
    };
    let put_outer = outer(put)?;
    let release_outer = outer(release)?;
    let take_argument = one(facts.boundary_substitutions.iter().filter(|b| {
        b.role == Role::CallArgument
            && b.point.function.as_ref() == Some(&take.caller)
            && b.point.block == Some(take.block)
            && b.point.statement == Some(take.statement)
            && b.callee.as_ref() == Some(&take.callee)
    }))?
    .formal_local?;
    let value_argument = one(facts.boundary_substitutions.iter().filter(|b| {
        b.point.construction == put.call.construction
            && b.ordinal == alternative.route.input_boundary
    }))?
    .formal_local?;
    if value_argument == put_outer {
        return None;
    }
    let field_projection = store.site.place.projection.clone();
    if !matches!(
        field_projection.as_slice(),
        [ProjKey::Deref, ProjKey::Field(_)]
    ) || store.site.place.local != put_outer
    {
        return None;
    }
    let mut output = Effects {
        source,
        free,
        calls: vec![
            make.clone(),
            put.call.clone(),
            take.clone(),
            release.call.clone(),
        ],
        initialized_cell: store.site.clone().into_site(),
        payload_write: store.site.clone().into_site(),
        field_store: store.site.clone().into_site(),
        field_load: store.site.clone().into_site(),
        field_reset: store.site.clone().into_site(),
        returns: vec![],
        formations: vec![],
        addresses: vec![],
        checked_occurrences: vec![],
        size_of_calls: vec![],
    };
    let mut init = None;
    let mut write = None;
    let mut load = None;
    let mut reset = None;
    let mut put_store = None;
    for name in names {
        let body = one(facts
            .reader_inputs
            .bodies
            .iter()
            .filter(|b| &b.function == name))?;
        if &body.occurrences != facts.source_occurrences.get(name)? {
            return None;
        }
        let roster = one(facts.body_rosters.iter().filter(|b| {
            b.point.construction == put.call.construction && b.point.function.as_ref() == Some(name)
        }))?;
        if !body.complete_operations
            || !roster.phis.is_empty()
            || super::coverage::validate_returns(facts, put.call.construction, name).is_err()
        {
            return None;
        }
        let expected_args = if name == &put.call.callee {
            2
        } else if name == &take.callee || name == &release.call.callee {
            1
        } else {
            0
        };
        if body.argument_count != expected_args {
            return None;
        }
        let mut ranks = BTreeMap::new();
        let mut next = Some(0);
        while let Some(block) = next {
            if ranks.insert(block, ranks.len()).is_some() {
                return None;
            }
            let row = one(roster
                .blocks
                .iter()
                .filter(|b| b.block == block && b.reachable))?;
            next = match row.successors.as_slice() {
                [] if row.return_statement.is_some() => None,
                [n] => Some(*n),
                _ => return None,
            };
        }
        if ranks.len() != roster.blocks.iter().filter(|b| b.reachable).count() {
            return None;
        }
        let mut rows: Vec<_> = body
            .occurrences
            .iter()
            .filter(|r| ranks.contains_key(&r.site.block))
            .collect();
        rows.sort_by_key(|r| (ranks[&r.site.block], r.site.statement));
        if rows
            .iter()
            .map(|r| (&r.site.function, r.site.block, r.site.statement))
            .collect::<BTreeSet<_>>()
            .len()
            != rows.len()
        {
            return None;
        }
        // Exact local-token flow: no overwrite, unconsumed intermediate alias,
        // second consuming use, arithmetic, hidden call, or projected escape.
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Value {
            Heap,
            Cell,
            Null,
            NativeCellRef,
            Size,
        }
        let mut values: BTreeMap<u32, Value> = BTreeMap::new();
        let mut used = BTreeMap::<u32, usize>::new();
        if name == &put.call.callee {
            values.insert(put_outer, Value::Cell);
            values.insert(value_argument, Value::Heap);
        }
        if name == &take.callee {
            values.insert(take_argument, Value::Cell);
        }
        if name == &release.call.callee {
            values.insert(release_outer, Value::Cell);
        }
        let mut saw_calls = BTreeSet::new();
        let mut field_state = if name == &take.callee {
            Some(Value::Heap)
        } else {
            None
        };
        for row in rows {
            output.checked_occurrences.push(row.site.clone());
            let dst = &row.syntax.destination;
            let use_value = |p: &PlaceSyntax,
                             values: &BTreeMap<u32, Value>,
                             used: &mut BTreeMap<u32, usize>|
             -> Option<Value> {
                if !p.projection.is_empty() {
                    return None;
                }
                let value = *values.get(&p.local)?;
                *used.entry(p.local).or_default() += 1;
                Some(value)
            };
            let mut produced = None;
            match &row.syntax.expression {
                Expression::Call { operands } => {
                    let args: Vec<_> = operands
                        .iter()
                        .filter_map(operand_place)
                        .map(|p| use_value(p, &values, &mut used))
                        .collect::<Option<_>>()?;
                    if same_point(&source_eq.point, &row.site) && name == &make.callee {
                        if row.callee != Some(SourceCallee::ForeignC("malloc".into()))
                            || operands.len() != 1
                            || !(args == [Value::Size]
                                || (args.is_empty()
                                    && matches!(
                                        &operands[0],
                                        OperandSyntax::Constant { zero: false, .. }
                                    )))
                        {
                            return None;
                        }
                        produced = Some(Value::Heap);
                        saw_calls.insert(0);
                    } else if name == &make.callee
                        && body
                            .size_of_calls
                            .contains(&(row.site.block, row.site.statement))
                        && matches!(row.callee, Some(SourceCallee::RustLibrary(_)))
                        && operands.is_empty()
                        && !body.pointer_locals.contains(&dst.local)
                    {
                        produced = Some(Value::Size);
                        output.size_of_calls.push(row.site.clone());
                    } else if same_point(&free_eq.point, &row.site) && name == &release.call.callee
                    {
                        if row.callee != Some(SourceCallee::ForeignC("free".into()))
                            || args != [Value::Heap]
                            || operands.len() != 1
                        {
                            return None;
                        }
                        saw_calls.insert(1);
                    } else {
                        let call = one([&make, &put.call, &take, &release.call]
                            .into_iter()
                            .filter(|c| at(c, row)))?;
                        if row.callee != Some(SourceCallee::Local(call.callee.clone())) {
                            return None;
                        }
                        if call == &make {
                            if !operands.is_empty() {
                                return None;
                            }
                            produced = Some(Value::Heap);
                        } else if call == &put.call {
                            if operands.len() != 2
                                || args.get(put.argument) != Some(&Value::Cell)
                                || args.iter().filter(|v| **v == Value::Heap).count() != 1
                                || field_state != Some(Value::Null)
                            {
                                return None;
                            }
                            field_state = Some(Value::Heap);
                        } else if call == &take {
                            if args != [Value::Cell] || operands.len() != 1 {
                                return None;
                            }
                            produced = Some(Value::Heap);
                        } else {
                            if args != [Value::Cell]
                                || operands.len() != 1
                                || field_state != Some(Value::Heap)
                            {
                                return None;
                            }
                            field_state = Some(Value::Null);
                        }
                        saw_calls.insert(if call == &make {
                            2
                        } else if call == &put.call {
                            3
                        } else if call == &take {
                            4
                        } else {
                            5
                        });
                    }
                }
                Expression::Borrow { borrow, place } => {
                    let candidate = one([put, release]
                        .into_iter()
                        .filter(|c| same_point(&c.formation, &row.site)))?;
                    if name != &put.call.caller
                        || place != &put.cell
                        || candidate.cell != put.cell
                        || borrow != "Mut { kind: Default }"
                        || values.get(&place.local) != Some(&Value::Cell)
                    {
                        return None;
                    }
                    output.formations.push(row.site.clone());
                    produced = Some(Value::NativeCellRef);
                }
                Expression::RawAddress { mutability, place } => {
                    one([put, release]
                        .into_iter()
                        .filter(|c| same_point(&c.address, &row.site)))?;
                    if mutability != "Mut"
                        || place.projection != [ProjKey::Deref]
                        || values.get(&place.local) != Some(&Value::NativeCellRef)
                    {
                        return None;
                    }
                    *used.entry(place.local).or_default() += 1;
                    output.addresses.push(row.site.clone());
                    produced = Some(Value::Cell);
                }
                Expression::Aggregate { operands, .. } => {
                    if name != &put.call.caller
                        || dst != &put.cell
                        || operands.len() != 1
                        || init.is_some()
                    {
                        return None;
                    }
                    if use_value(operand_place(&operands[0])?, &values, &mut used)
                        != Some(Value::Null)
                    {
                        return None;
                    }
                    init = Some(row.site.clone());
                    produced = Some(Value::Cell);
                    field_state = Some(Value::Null);
                }
                Expression::Value { operand } | Expression::Cast { operand, .. } => {
                    if let Expression::Cast { cast, .. } = &row.syntax.expression {
                        if cast != "PtrToPtr"
                            && row.syntax.immediate_origin != ImmediateOrigin::Null
                        {
                            return None;
                        }
                    }
                    if !dst.projection.is_empty() {
                        if name == &make.callee
                            && dst.projection == [ProjKey::Deref]
                            && values.get(&dst.local) == Some(&Value::Heap)
                            && used.get(&dst.local).copied().unwrap_or(0) == 0
                            && matches!(operand, OperandSyntax::Constant { .. })
                            && write.is_none()
                        {
                            write = Some(row.site.clone());
                            continue;
                        }
                        let outer = if name == &put.call.callee {
                            put_outer
                        } else if name == &take.callee {
                            take_argument
                        } else {
                            return None;
                        };
                        if dst.local != outer || dst.projection != field_projection {
                            return None;
                        }
                        if name == &put.call.callee {
                            if row.site.block != store.site.block
                                || row.site.statement != store.site.statement
                                || put_store.is_some()
                                || use_value(operand_place(operand)?, &values, &mut used)
                                    != Some(Value::Heap)
                            {
                                return None;
                            }
                            put_store = Some(row.site.clone());
                        } else {
                            if row.syntax.immediate_origin != ImmediateOrigin::Null
                                || field_state != Some(Value::Heap)
                                || reset.is_some()
                            {
                                return None;
                            }
                            reset = Some(row.site.clone());
                            field_state = Some(Value::Null);
                        }
                        continue;
                    }
                    if let Some(p) = operand_place(operand) {
                        if p.projection == field_projection
                            && name == &take.callee
                            && p.local == take_argument
                        {
                            if field_state != Some(Value::Heap) || load.is_some() {
                                return None;
                            }
                            load = Some(row.site.clone());
                            produced = Some(Value::Heap);
                        } else {
                            produced = Some(use_value(p, &values, &mut used)?);
                        }
                    } else if row.syntax.immediate_origin == ImmediateOrigin::Null {
                        produced = Some(Value::Null);
                    } else if !(dst.local == 0 && facts.unit_locals.contains(&(name.clone(), 0))) {
                        return None;
                    }
                }
                _ => return None,
            }
            if let Some(value) = produced {
                if !dst.projection.is_empty() || values.insert(dst.local, value).is_some() {
                    return None;
                }
                if dst.local == 0 {
                    if value != Value::Heap || !(name == &make.callee || name == &take.callee) {
                        return None;
                    }
                    if name == &take.callee && field_state != Some(Value::Null) {
                        return None;
                    }
                    output.returns.push(row.site.clone());
                }
            }
        }
        let wanted: BTreeSet<_> = if name == &put.call.caller {
            [2, 3, 5].into_iter().collect()
        } else if name == &make.callee {
            [0].into_iter().collect()
        } else if name == &release.call.callee {
            [1, 4].into_iter().collect()
        } else {
            BTreeSet::new()
        };
        if saw_calls != wanted {
            return None;
        }
        for (&local, &value) in &values {
            if local == 0
                || (value == Value::Cell
                    && ((name == &put.call.caller && local == put.cell.local)
                        || (name == &put.call.callee && local == put_outer)
                        || (name == &take.callee && local == take_argument)))
            {
                continue;
            }
            if used.get(&local) != Some(&1) {
                return None;
            }
        }
    }
    output.initialized_cell = init?;
    output.payload_write = write?;
    output.field_store = put_store?;
    output.field_load = load?;
    output.field_reset = reset?;
    if output.returns.len() != 2 || output.formations.len() != 2 || output.addresses.len() != 2 {
        return None;
    }
    Some(output)
}

// Preserve source coordinates without introducing an equation identity.
trait IntoSite {
    fn into_site(self) -> SourceSite;
}
impl IntoSite for super::field_support::Site {
    fn into_site(self) -> SourceSite {
        SourceSite {
            function: self.function,
            block: self.block,
            statement: self.statement,
        }
    }
}
