//! Conditional membership of one owned child inside a narrowed parent token.
//! This metadata does not discharge full caller closure or activate a fold.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    facts::{EquationId, Facts},
    field_support::Site,
    fold_call,
    fold_declaration::Declaration,
    matched::SourceInstance,
    transport::Node,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Membership {
    pub(crate) declaration: Declaration,
    pub(crate) fold: fold_call::Proof,
    pub(crate) field: String,
    pub(crate) parent: SourceInstance,
    pub(crate) member: SourceInstance,
    pub(crate) child_store: Site,
    pub(crate) narrowing_store: Site,
    pub(crate) child_transfer: EquationId,
    pub(crate) narrowing_transfer: EquationId,
    pub(crate) parent_before: Node,
    pub(crate) parent_after: Node,
    pub(crate) member_before: Node,
    pub(crate) member_after: Node,
    pub(crate) cell: Node,
    pub(crate) formal: Node,
    pub(crate) requirements: super::fold_permission::Requirements,
    pub(crate) terminal_inventory: Vec<usize>,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Hold {
    Declaration,
    Call,
    FieldScheme,
    /// R369-2: the folding frame's own shape — see `fold_caller::Hold::BodyShape`.
    /// The membership certificate additionally needs the frame to return
    /// nothing.
    BodyShape {
        arguments: usize,
        returns: usize,
        phis: usize,
    },
    /// R363-1: membership is written for one descendant; this is how many the
    /// admitted field set produced. `FieldScheme` stays the premise refusal.
    Descendants(usize),
    /// R363-1: the line that refused, across the 14 explicit coverage sites of
    /// the membership certificate. Recorded through `fold_caller::Hold::Member`.
    Coverage(u32),
    UnsupportedEffect,
    StoreInventory,
    SourceIdentity,
    MemberPath,
    Overwrite,
    PartnerFree,
    MissingZero,
    Changed,
}

pub(crate) fn certify(
    facts: &Facts,
    declaration: &Declaration,
    fold: &fold_call::Proof,
) -> Result<Membership, Hold> {
    certify_metadata(
        facts,
        declaration,
        fold,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}
fn one<T>(items: impl IntoIterator<Item = T>, hold: Hold) -> Result<T, Hold> {
    let mut items = items.into_iter();
    let value = items.next().ok_or_else(|| hold.clone())?;
    if items.next().is_some() {
        return Err(hold);
    }
    Ok(value)
}

pub(crate) fn certify_metadata(
    facts: &Facts,
    declaration: &Declaration,
    fold: &fold_call::Proof,
    aliases: &BTreeMap<EquationId, EquationId>,
    slots: &BTreeSet<String>,
) -> Result<Membership, Hold> {
    use super::{
        super::{
            ownership_boundary,
            ownership_occurrence::{self, Availability::Present, PathStep},
        },
        field_support::StoredValue,
        matched::{MatchedTransport, SourceLineage, TerminalTarget},
        value_origins::{OriginAtom, ValueOrigins},
    };
    super::fold_declaration::validate(facts, aliases).map_err(|_| Hold::Declaration)?;
    if !facts
        .fold_declarations
        .as_ref()
        .is_some_and(|rows| rows.contains(declaration))
        || declaration.call != fold.call
        || declaration.boundary != fold.boundary
    {
        return Err(Hold::Declaration);
    }
    let [descendant] = fold.descendants.as_slice() else {
        return Err(Hold::Descendants(fold.descendants.len()));
    };
    let fold_call::FieldPremise::Owning { field } = &descendant.premise else {
        return Err(Hold::FieldScheme);
    };
    let Some(packed) = &fold.internal.packed_return else { return Err(Hold::Call) };
    if &packed.field_scheme != field || packed.carrier_input != descendant.input {
        return Err(Hold::Call);
    }
    // R304-9: membership's closed store inventory is only closed if every write
    // that could reach this field resolved to a named store. It does not rely on
    // the scheme gate in `fold_call` having run.
    if facts
        .field_support_inputs
        .unsupported
        .iter()
        .any(|effect| effect.field_keys.iter().any(|key| key == field))
    {
        return Err(Hold::UnsupportedEffect);
    }
    let mut requirements =
        super::fold_permission::requirements_metadata(facts, fold, aliases, slots)
            .map_err(|_| Hold::Call)?;
    super::fold_caller::check_effects(facts, fold, aliases).map_err(|_| Hold::UnsupportedEffect)?;
    if super::caller_coverage::assess(facts) != super::caller_coverage::Status::Complete {
        return Err(Hold::Coverage(line!()));
    }
    let call = &fold.call;
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_ref() == Some(&call.caller)
    };
    let body = one(
        facts.body_rosters.iter().filter(|b| scope(&b.point)),
        Hold::Coverage(line!()),
    )?;
    let shape =
        (body.argument_count != 0 || body.return_width != 0) && !super::facts::relax_frame();
    if shape || !body.phis.is_empty() {
        return Err(Hold::BodyShape {
            arguments: body.argument_count,
            returns: body.return_width,
            phis: body.phis.len(),
        });
    }
    let mut order = BTreeMap::new();
    let mut next = 0;
    loop {
        let block = one(
            body.blocks
                .iter()
                .filter(|b| b.block == next && b.reachable),
            Hold::Coverage(line!()),
        )?;
        if order.insert(next, order.len()).is_some() {
            return Err(Hold::UnsupportedEffect);
        }
        match block.successors.as_slice() {
            [] if block.return_statement.is_some() => break,
            [successor] => next = *successor,
            _ => return Err(Hold::UnsupportedEffect),
        }
    }
    if order.len() != body.blocks.iter().filter(|b| b.reachable).count() {
        return Err(Hold::Coverage(line!()));
    }
    let terminal_inventory = super::fold_coverage::validate(facts, call.construction, &call.caller)
        .map_err(|_| Hold::Coverage(line!()))?;
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
    ownership_occurrence::validate(&call.caller, &consumes, &equations)
        .map_err(|_| Hold::Coverage(line!()))?;
    ownership_boundary::validate_shapes(&call.caller, &boundaries, &registrations)
        .map_err(|_| Hold::Coverage(line!()))?;
    ownership_boundary::validate_links(
        &call.caller,
        &boundaries,
        &registrations,
        &consumes,
        &equations,
    )
    .map_err(|_| Hold::Coverage(line!()))?;
    if equations.iter().any(|e| e.validate().is_err()) {
        return Err(Hold::Coverage(line!()));
    }
    let node = |var| Node {
        construction: call.construction,
        var,
    };
    let id = |e: &super::super::ownership_evidence::Equation| EquationId {
        construction: call.construction,
        ordinal: e.ordinal,
    };
    let actual = one(
        consumes.iter().filter(|c| c.ordinal == fold.actual_consume),
        Hold::Call,
    )?;
    let stores = &facts.field_support_inputs.stores;
    let child_store = one(
        stores
            .iter()
            .filter(|s| s.site.field_key == *field && matches!(s.value, StoredValue::Value(_))),
        Hold::StoreInventory,
    )?;
    let narrowing_store = one(
        stores.iter().filter(|s| {
            s.site.function == call.caller
                && s.site.place.local == actual.local
                && s.site.place.projection == actual.projection
                && matches!(s.value, StoredValue::Value(_))
        }),
        Hold::StoreInventory,
    )?;
    let child_null = one(
        stores
            .iter()
            .filter(|s| s.site.field_key == *field && s.value == StoredValue::Null),
        Hold::StoreInventory,
    )?;
    let reset = one(
        stores.iter().filter(|s| {
            s.site.function == call.caller
                && s.site.place == narrowing_store.site.place
                && s.site.field_key == narrowing_store.site.field_key
                && s.value == StoredValue::Null
        }),
        Hold::StoreInventory,
    )?;
    if stores.len() != 4
        || narrowing_store.site.field_key == *field
        || [child_store, narrowing_store, child_null, reset]
            .iter()
            .any(|s| !s.direct_projection || s.aggregate || s.site.function != call.caller)
    {
        return Err(Hold::StoreInventory);
    }
    let at = |point: &super::super::ownership_evidence::Point, site: &Site| {
        point.block == Some(site.block)
            && point.statement == Some(site.statement)
            && point.function.as_ref() == Some(&site.function)
    };
    let transfer = |store: &super::field_support::Store| {
        let StoredValue::Value(source) = &store.value else { return Err(Hold::StoreInventory) };
        one(equations.iter().filter(|e| at(&e.point, &store.site) && e.operation == "equal"
            && e.transfer.as_ref().is_some_and(|t| t.by_move && matches!((&t.source, &t.destination),(Present(s),Present(d))
                if s.local == source.local && s.projection == source.projection
                    && d.local == store.site.place.local && d.projection == store.site.place.projection))), Hold::MemberPath)
    };
    let child_equation = transfer(child_store)?;
    let narrow_equation = transfer(narrowing_store)?;
    let child = child_equation.transfer.as_ref().ok_or(Hold::MemberPath)?;
    let narrow = narrow_equation.transfer.as_ref().ok_or(Hold::MemberPath)?;
    let (Present(child_destination), Present(narrow_source), Present(narrow_destination)) =
        (&child.destination, &narrow.source, &narrow.destination)
    else {
        return Err(Hold::MemberPath);
    };
    let child_consume = one(
        consumes
            .iter()
            .filter(|c| c.ordinal == child_destination.consume),
        Hold::MemberPath,
    )?;
    let wide = one(
        consumes
            .iter()
            .filter(|c| c.ordinal == narrow_source.consume),
        Hold::MemberPath,
    )?;
    let cell_consume = one(
        consumes
            .iter()
            .filter(|c| c.ordinal == narrow_destination.consume),
        Hold::MemberPath,
    )?;
    let (
        Present(child_base),
        Present(base),
        Present(paths),
        Present(cell_window),
        Present(container_base),
    ) = (
        &child_consume.base,
        &wide.base,
        &wide.pointer_paths,
        &cell_consume.projected,
        &cell_consume.base,
    )
    else {
        return Err(Hold::MemberPath);
    };
    let [PathStep::Deref, PathStep::Field { .. }] = descendant.path.as_slice() else {
        return Err(Hold::MemberPath);
    };
    let offset = one(
        paths
            .iter()
            .enumerate()
            .filter(|(_, p)| **p == descendant.path)
            .map(|(i, _)| i),
        Hold::MemberPath,
    )? as u32;
    if base.use_end.checked_sub(base.use_start) != Some(2)
        || offset != 1
        || cell_window.use_end.checked_sub(cell_window.use_start) != Some(1)
        || narrow.destination_def != fold.actual_before.var
        || child_destination.path != descendant.path
    {
        return Err(Hold::MemberPath);
    }
    let member_before = node(base.use_start + offset);
    let member_after = node(base.def_start + offset);
    let origins =
        ValueOrigins::build_metadata(facts, aliases).map_err(|_| Hold::Coverage(line!()))?;
    let fresh = |value| {
        let atoms = origins.at(value);
        if !atoms
            .iter()
            .all(|a| matches!(a, OriginAtom::Fresh(_) | OriginAtom::Null))
        {
            return Err(Hold::SourceIdentity);
        }
        one(
            atoms.iter().filter_map(|a| match a {
                OriginAtom::Fresh(id) => Some(*id),
                _ => None,
            }),
            Hold::SourceIdentity,
        )
    };
    let member_source = fresh(node(child.source_use))?;
    let parent_source = fresh(node(child_base.use_start))?;
    let container_source = fresh(node(container_base.use_start))?;
    if BTreeSet::from([member_source, parent_source, container_source]).len() != 3
        || fresh(node(narrow.source_use))? != parent_source
        || fresh(member_before)? != member_source
    {
        return Err(Hold::SourceIdentity);
    }
    let Present(actual_base) = &actual.base else { return Err(Hold::MemberPath) };
    if fresh(node(actual_base.use_start))? != container_source {
        return Err(Hold::SourceIdentity);
    }
    for load in &facts.field_support_inputs.loads {
        let caller_cell = load.site.field_key == narrowing_store.site.field_key
            && load.site.function == call.caller
            && load.site.place.local == actual.local
            && load.site.place.projection == actual.projection
            && actual.point.block == Some(load.site.block)
            && actual.point.statement == Some(load.site.statement);
        let callee_take = load.site.field_key == *field
            && load.site.function == call.callee
            && fold.internal.actions.iter().any(|a| {
                a.kind == "take" && a.block == load.site.block && a.statement == load.site.statement
            });
        if !load.direct_projection || load.shared_reference_root || !(caller_cell || callee_take) {
            return Err(Hold::UnsupportedEffect);
        }
    }
    if !facts.terminals.iter().any(|t| {
        scope(&t.point)
            && t.role == "local-final-zero"
            && matches!(&t.values,Present(values) if values.iter().any(|v|v.var==member_after.var))
    }) {
        return Err(Hold::MissingZero);
    }
    let parent = SourceInstance {
        endpoint: parent_source,
        lineage: SourceLineage::Exact(vec![]),
    };
    let member = SourceInstance {
        endpoint: member_source,
        lineage: SourceLineage::Exact(vec![]),
    };
    let transport =
        MatchedTransport::build_metadata(facts, aliases).map_err(|_| Hold::Coverage(line!()))?;
    if !transport.reaches(node(child.destination_def), member_before)
        || transport.sources_for(member_before) != BTreeSet::from([member.clone()])
        || transport.sources_for(node(narrow.source_use)) != BTreeSet::from([parent.clone()])
    {
        return Err(Hold::MemberPath);
    }
    let seeds = transport.source_nodes(call.construction, &call.caller, &member);
    if seeds.is_empty() {
        return Err(Hold::SourceIdentity);
    }
    if seeds
        .into_iter()
        .flat_map(|seed| transport.meets_for(seed))
        .any(|m| m.source != member || matches!(m.terminal.target, TerminalTarget::Free(_)))
    {
        return Err(Hold::PartnerFree);
    }
    let pos = |site: &Site| -> Result<_, Hold> {
        Ok((
            *order.get(&site.block).ok_or(Hold::Coverage(line!()))?,
            site.statement,
        ))
    };
    let call_pos = (
        *order.get(&call.block).ok_or(Hold::Coverage(line!()))?,
        call.statement,
    );
    if !(pos(&child_null.site)? < pos(&child_store.site)?
        && pos(&child_store.site)? < pos(&narrowing_store.site)?
        && pos(&narrowing_store.site)? < call_pos
        && call_pos < pos(&reset.site)?)
    {
        return Err(Hold::Overwrite);
    }
    let null_consume = one(
        consumes.iter().filter(|c| {
            at(&c.point, &child_null.site)
                && c.local == child_null.site.place.local
                && c.projection == child_null.site.place.projection
        }),
        Hold::StoreInventory,
    )?;
    let (Present(null_base), Present(null_window)) = (&null_consume.base, &null_consume.projected)
    else {
        return Err(Hold::MemberPath);
    };
    if fresh(node(null_base.use_start))? != member_source
        || origins.at(node(null_window.def_start)) != BTreeSet::from([OriginAtom::Null])
    {
        return Err(Hold::SourceIdentity);
    }
    for (equation, t) in [(child_equation, child), (narrow_equation, narrow)] {
        for var in [t.destination_use, t.source_def] {
            one(
                equations.iter().filter(|e| {
                    e.point == equation.point
                        && e.transfer.as_ref() == Some(t)
                        && e.operation == "assume"
                        && e.value == Some(false)
                        && e.variables == [var]
                }),
                Hold::MissingZero,
            )?;
            requirements.zero.push(node(var));
        }
    }
    for store in [child_null, reset] {
        let consume = one(
            consumes.iter().filter(|c| {
                at(&c.point, &store.site)
                    && c.local == store.site.place.local
                    && c.projection == store.site.place.projection
            }),
            Hold::StoreInventory,
        )?;
        let Present(window) = &consume.projected else { return Err(Hold::MemberPath) };
        one(
            equations.iter().filter(|e| {
                e.point == consume.point
                    && e.operation == "assume"
                    && e.value == Some(false)
                    && e.variables == [window.use_start]
            }),
            Hold::MissingZero,
        )?;
    }
    requirements.kind_keys.push(field.clone());
    requirements.owning.extend([
        node(child.destination_def),
        member_before,
        node(narrow.source_use),
        fold.actual_before,
        node(descendant.formal_use),
    ]);
    requirements.zero.push(member_after);
    for source in [member_source, parent_source, container_source] {
        let equation = one(
            facts.equations.iter().filter(|e| {
                e.point.construction == source.construction
                    && e.ordinal == source.ordinal
                    && e.operation == "source"
                    && e.endpoint.as_ref().is_some_and(|p| {
                        p.function == call.caller && p.callee == "malloc" && p.outcome.is_none()
                    })
            }),
            Hold::SourceIdentity,
        )?;
        if equation.validate().is_err() {
            return Err(Hold::Coverage(line!()));
        }
        requirements
            .guards
            .push((*aliases.get(&source).ok_or(Hold::SourceIdentity)?, true));
    }
    requirements.guards.push((declaration.guard, true));
    requirements.kind_keys.sort();
    requirements.kind_keys.dedup();
    requirements.owning.sort();
    requirements.owning.dedup();
    requirements.zero.sort();
    requirements.zero.dedup();
    requirements.guards.sort();
    requirements.guards.dedup();
    if requirements
        .owning
        .iter()
        .any(|n| requirements.zero.contains(n))
        || requirements
            .guards
            .windows(2)
            .any(|w| w[0].0 == w[1].0 && w[0].1 != w[1].1)
    {
        return Err(Hold::Changed);
    }
    Ok(Membership {
        declaration: declaration.clone(),
        fold: fold.clone(),
        field: field.clone(),
        parent,
        member,
        child_store: child_store.site.clone(),
        narrowing_store: narrowing_store.site.clone(),
        child_transfer: id(child_equation),
        narrowing_transfer: id(narrow_equation),
        parent_before: node(narrow.source_use),
        parent_after: node(narrow.source_def),
        member_before,
        member_after,
        cell: fold.actual_before,
        formal: node(descendant.formal_use),
        requirements,
        terminal_inventory,
    })
}
