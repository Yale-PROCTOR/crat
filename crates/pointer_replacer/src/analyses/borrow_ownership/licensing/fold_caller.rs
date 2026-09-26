//! Conditional closed-caller vocabulary for the initial folded identity chain.
//! Certificates are conditional; no production hold is released here.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    super::origin_evidence::SourceSite,
    facts::{EquationId, Facts},
    field_support::Site,
    fold_call,
    fold_declaration::Declaration,
    fold_permission::Requirements,
    matched::{FoldedReturn, Meet, SourceInstance},
    transport::Node,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct EndpointRoute {
    pub(crate) source: SourceInstance,
    pub(crate) free: EquationId,
    pub(crate) meet: Meet,
    /// All entry nodes and their unfiltered terminal alternatives for this source.
    pub(crate) source_nodes: Vec<Node>,
    pub(crate) source_meets: Vec<Meet>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CellReceipt {
    pub(crate) site: Site,
    pub(crate) consume: usize,
    pub(crate) before: Node,
    pub(crate) after: Node,
    pub(crate) equations: Vec<EquationId>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CallerProof {
    pub(crate) guard: EquationId,
    pub(crate) fold: fold_call::Proof,
    /// A premise for activation, not a claim inferred from local call syntax.
    pub(crate) required_closed_frame: bool,
    pub(crate) payload: EndpointRoute,
    pub(crate) container: EndpointRoute,
    pub(crate) store: CellReceipt,
    pub(crate) reset: CellReceipt,
    pub(crate) null_init: CellReceipt,
    pub(crate) forwarding: FoldedReturn,
    pub(crate) requirements: Requirements,
    pub(crate) checked_occurrences: Vec<SourceSite>,
    pub(crate) checked_consumes: Vec<usize>,
    pub(crate) checked_equations: Vec<EquationId>,
    pub(crate) terminal_inventory: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Hold {
    /// Retained for decoding entries recorded before the line existed; no site
    /// emits it. R363-1 emission carries the refusing line in `CoverageAt`.
    Coverage,
    /// R363-1: the line that refused, across the 30 explicit coverage sites of
    /// the caller and member-caller certificates.
    CoverageAt(u32),
    UnsupportedEffect,
    /// R339-5 D2/K-D2: two fold sites the caller can reach on one path. Sites
    /// on mutually exclusive paths are admitted; these are not.
    MultipleFoldSitesOnPath,
    /// R363-1: the membership certificate's own refusal, carried instead of
    /// collapsed. `UnsupportedEffect` keeps its own variant.
    Member(super::fold_subtree::Hold),
    /// R369-2: the folding frame's own shape. The cell plan walks one linear
    /// chain of blocks and names every SSA version in it, which assumes a frame
    /// that takes nothing, returns nothing and joins nowhere — a top-level
    /// `run()`. A recursive tree function is none of those, and this says which
    /// of the three it violates instead of a bare `UnsupportedEffect`.
    BodyShape {
        arguments: usize,
        returns: usize,
        phis: usize,
    },
    /// Retained for decoding entries recorded before the line existed; no site
    /// emits it. R363-1 emission carries the refusing line in `OriginAt`.
    Origin,
    /// R363-1: the line that refused, across the 23 explicit origin sites of the
    /// caller, member-caller and member-law certificates.
    OriginAt(u32),
    CellIdentity,
    MissingStore,
    MissingReset,
    MissingNullInit,
    CompetingResponsibility,
    Forwarding,
    LawCoverage,
}

pub(crate) fn certify(
    facts: &Facts,
    declaration: &Declaration,
    fold: &fold_call::Proof,
) -> Result<CallerProof, Hold> {
    certify_metadata(
        facts,
        declaration,
        fold,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}

pub(crate) fn certify_metadata(
    facts: &Facts,
    declaration: &Declaration,
    fold: &fold_call::Proof,
    aliases: &BTreeMap<EquationId, EquationId>,
    slot_keys: &BTreeSet<String>,
) -> Result<CallerProof, Hold> {
    use super::{
        super::ownership_occurrence::Availability::Present,
        matched::{MatchedTransport, TerminalTarget},
    };
    check_effects(facts, fold, aliases)?;
    if super::caller_coverage::assess(facts) != super::caller_coverage::Status::Complete {
        return Err(Hold::CoverageAt(line!()));
    }
    let call = &fold.call;
    let calls: Vec<_> = facts
        .caller_coverage
        .as_ref()
        .ok_or(Hold::CoverageAt(line!()))?
        .local_calls
        .iter()
        .filter(|c| c.target == call.callee)
        .collect();
    // R339-5 D2-a, the same rule the member path already asks: one call to this
    // callee on THIS path, not one in the whole body. `insert` calls itself from
    // two mutually exclusive arms, and a body-wide uniqueness test reads that as
    // an unsupported effect. Both gates go through `mutually_exclusive`, so they
    // cannot disagree about the same pair of sites.
    let blocks = facts
        .body_rosters
        .iter()
        .find(|roster| roster.point.function.as_deref() == Some(call.caller.as_str()))
        .map(|roster| roster.blocks.as_slice())
        .unwrap_or_default();
    let here = calls.iter().filter(|c| {
        c.site.function == call.caller
            && c.site.block == call.block
            && c.site.statement == call.statement
    });
    if here.count() != 1
        || calls.iter().any(|c| {
            (c.site.function.as_str(), c.site.block, c.site.statement)
                != (call.caller.as_str(), call.block, call.statement)
                && !(c.site.function == call.caller
                    && mutually_exclusive(blocks, call.block, c.site.block))
        })
    {
        return Err(Hold::UnsupportedEffect);
    }
    let (payload, container) = endpoint_routes(facts, declaration, fold, aliases)?;
    let cell = cell_plan(facts, fold, &payload, &container, aliases)?;
    let laws = super::fold_laws::audit(facts, fold, &payload, &container, &cell, aliases)?;
    let transport = MatchedTransport::build_with_conditional_folds_metadata(
        facts,
        &[(declaration.guard, fold.clone())],
        aliases,
    )
    .map_err(|_| Hold::CoverageAt(line!()))?;
    let mut forwarded = Vec::new();
    for output in payload
        .source_meets
        .iter()
        .filter(|m| matches!(m.terminal.target, TerminalTarget::Output { .. }))
    {
        forwarded.push(
            transport
                .forward_folded_return(facts, output, &payload.meet, declaration.guard, fold)
                .ok_or(Hold::Forwarding)?,
        );
    }
    let forwarding = one(forwarded, Hold::Forwarding)?;
    if container
        .source_meets
        .iter()
        .any(|m| m.terminal.target != TerminalTarget::Free(container.free))
    {
        return Err(Hold::CompetingResponsibility);
    }
    let endpoints: BTreeSet<_> = facts
        .equations
        .iter()
        .filter(|e| {
            e.point.construction == call.construction
                && e.point.function.as_ref() == Some(&call.caller)
                && e.endpoint.is_some()
        })
        .map(|e| EquationId {
            construction: e.point.construction,
            ordinal: e.ordinal,
        })
        .collect();
    if endpoints
        != BTreeSet::from([
            payload.source.endpoint,
            payload.free,
            container.source.endpoint,
            container.free,
        ])
    {
        return Err(Hold::CompetingResponsibility);
    }
    let mut requirements =
        super::fold_permission::requirements_metadata(facts, fold, aliases, slot_keys)
            .map_err(|_| Hold::CoverageAt(line!()))?;
    let actual = one(
        facts.consumes.iter().filter(|c| {
            c.point.construction == call.construction && c.ordinal == fold.actual_consume
        }),
        Hold::CellIdentity,
    )?;
    let container_key = one(
        facts
            .raw_pointer_heads
            .iter()
            .filter(|h| h.function == call.caller && h.local == actual.local),
        Hold::CellIdentity,
    )?
    .slot_key
    .clone();
    if !slot_keys.contains(&container_key) {
        return Err(Hold::CoverageAt(line!()));
    }
    requirements.kind_keys.push(container_key);
    requirements.kind_keys.sort();
    requirements.kind_keys.dedup();
    requirements.owning.extend(laws.owning);
    requirements.owning.sort();
    requirements.owning.dedup();
    requirements.zero.extend(laws.zero);
    requirements.zero.sort();
    requirements.zero.dedup();
    if requirements
        .owning
        .iter()
        .any(|n| requirements.zero.contains(n))
    {
        return Err(Hold::LawCoverage);
    }
    let mut guards: BTreeMap<_, _> = requirements.guards.iter().copied().collect();
    for (key, value) in laws
        .guards
        .into_iter()
        .chain(forwarding.forwarding.guards.iter().map(|(k, v)| (*k, *v)))
    {
        if guards.insert(key, value).is_some_and(|old| old != value) {
            return Err(Hold::LawCoverage);
        }
    }
    requirements.guards = guards.into_iter().collect();
    // Explicitly retain the current full base, including zero descendant slots.
    if !matches!(&actual.base, Present(_)) {
        return Err(Hold::CellIdentity);
    }
    Ok(CallerProof {
        guard: declaration.guard,
        fold: fold.clone(),
        required_closed_frame: true,
        payload,
        container,
        store: cell.store,
        reset: cell.reset,
        null_init: cell.null_init,
        forwarding,
        requirements,
        checked_occurrences: cell.sites,
        checked_consumes: laws.consumes,
        checked_equations: laws.equations,
        terminal_inventory: cell.terminals,
    })
}

fn one<T>(items: impl IntoIterator<Item = T>, hold: Hold) -> Result<T, Hold> {
    let mut items = items.into_iter();
    let value = items.next().ok_or_else(|| hold.clone())?;
    if items.next().is_some() {
        return Err(hold);
    }
    Ok(value)
}

/// Endpoint sub-check only; it does not close caller effects or zero laws.
pub(crate) fn endpoint_routes(
    facts: &Facts,
    declaration: &Declaration,
    fold: &fold_call::Proof,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<(EndpointRoute, EndpointRoute), Hold> {
    use super::{
        super::ownership_occurrence::Availability::Present,
        matched::{MatchedTransport, SourceLineage, TerminalTarget},
        value_origins::{OriginAtom, ValueOrigins},
    };
    let call = &fold.call;
    let transport = MatchedTransport::build_with_conditional_folds_metadata(
        facts,
        &[(declaration.guard, fold.clone())],
        aliases,
    )
    .map_err(|_| Hold::CoverageAt(line!()))?;
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_ref() == Some(&call.caller)
    };
    let actual = one(
        facts
            .consumes
            .iter()
            .filter(|c| scope(&c.point) && c.ordinal == fold.actual_consume),
        Hold::CellIdentity,
    )?;
    let store = one(
        facts.field_support_inputs.stores.iter().filter(|s| {
            s.site.function == call.caller
                && s.site.place.local == actual.local
                && s.site.place.projection == actual.projection
                && matches!(s.value, super::field_support::StoredValue::Value(_))
        }),
        Hold::MissingStore,
    )?;
    let equation = one(
        facts.equations.iter().filter(|e| {
            scope(&e.point)
                && e.point.block == Some(store.site.block)
                && e.point.statement == Some(store.site.statement)
                && matches!(e.operation.as_str(), "linear" | "equal")
                && e.transfer.as_ref().is_some_and(|t| {
                    matches!(&t.destination,Present(d)
            if d.local==actual.local && d.projection==actual.projection)
                })
        }),
        Hold::LawCoverage,
    )?;
    let transfer = equation.transfer.as_ref().ok_or(Hold::LawCoverage)?;
    let (Present(base), Present(paths)) = (&actual.base, &actual.pointer_paths) else {
        return Err(Hold::CellIdentity);
    };
    if paths.first() != Some(&Vec::new()) || base.use_start >= base.use_end {
        return Err(Hold::CellIdentity);
    }
    let origins =
        ValueOrigins::build_metadata(facts, aliases).map_err(|_| Hold::OriginAt(line!()))?;
    // R365-3: the owner-return shape. A callee handed the caller's token for
    // argument `a` and handing it back has not created a second owner — one
    // token in, the same token out, which is what `root = insert(root, key)`
    // is and what a `Box<Node>` insert compiles to.
    //
    // The premise is the transfer INTO the callee recorded at THIS call. A
    // callee that returns an argument it was only lent still refuses, because
    // the caller kept its token and would then hold it twice (K-R365-a); an
    // `Input` port that is not a consumed argument of this call is a different
    // token and still refuses (K-R365-b). `Borrowed` and `TraversalBorrow` are
    // exactly the lending roles, and an argument whose caller place the
    // substitution could not identify is not evidence that the caller's token
    // is what moved.
    let fresh = |node| -> Result<EquationId, Hold> {
        let atoms = origins.at(node);
        if !atoms.iter().all(|v| {
            matches!(v, OriginAtom::Fresh(_) | OriginAtom::Null) || returned_token(facts, call, v)
        }) {
            return Err(Hold::OriginAt(line!()));
        }
        one(
            atoms.iter().filter_map(|v| match v {
                OriginAtom::Fresh(id) => Some(*id),
                _ => None,
            }),
            Hold::OriginAt(line!()),
        )
    };
    let node = |var| Node {
        construction: call.construction,
        var,
    };
    let payload_source = fresh(node(transfer.source_use))?;
    let container_node = node(base.use_start);
    let container_source = fresh(container_node)?;
    if payload_source == container_source {
        return Err(Hold::CompetingResponsibility);
    }
    let route = |at: Node, source_id: EquationId| -> Result<EndpointRoute, Hold> {
        let source_eq = one(
            facts.equations.iter().filter(|e| {
                e.point.construction == source_id.construction && e.ordinal == source_id.ordinal
            }),
            Hold::OriginAt(line!()),
        )?;
        if source_eq.validate().is_err()
            || source_eq.operation != "source"
            || !source_eq.endpoint.as_ref().is_some_and(|e| {
                e.function == call.caller
                    && matches!(e.callee.as_str(), "malloc" | "calloc")
                    && e.outcome.is_none()
            })
        {
            return Err(Hold::OriginAt(line!()));
        }
        let local = transport.meets_for(at);
        let instances: BTreeSet<_> = local
            .iter()
            .filter(|m| m.source.endpoint == source_id)
            .map(|m| m.source.clone())
            .collect();
        let source = one(instances, Hold::OriginAt(line!()))?;
        if source.lineage != SourceLineage::Exact(vec![]) {
            return Err(Hold::OriginAt(line!()));
        }
        let source_nodes = transport.source_nodes(call.construction, &call.caller, &source);
        if source_nodes.is_empty() {
            return Err(Hold::OriginAt(line!()));
        }
        let mut source_meets = Vec::new();
        for seed in &source_nodes {
            for meet in transport
                .meets_for(*seed)
                .into_iter()
                .filter(|m| m.source == source)
            {
                if !source_meets.contains(&meet) {
                    source_meets.push(meet);
                }
            }
        }
        let frees: BTreeSet<_> = source_meets
            .iter()
            .filter(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
            .map(|m| m.terminal.clone())
            .collect();
        if frees.len() > 1 {
            return Err(Hold::CompetingResponsibility);
        }
        let terminal = one(frees, Hold::OriginAt(line!()))?;
        let TerminalTarget::Free(free) = terminal.target else {
            return Err(Hold::OriginAt(line!()));
        };
        if terminal.lineage != SourceLineage::Exact(vec![]) {
            return Err(Hold::OriginAt(line!()));
        }
        let free_eq = one(
            facts
                .equations
                .iter()
                .filter(|e| e.point.construction == free.construction && e.ordinal == free.ordinal),
            Hold::OriginAt(line!()),
        )?;
        if free_eq.validate().is_err()
            || free_eq.operation != "sink"
            || !free_eq.endpoint.as_ref().is_some_and(|e| {
                e.function == call.caller && e.callee == "free" && e.outcome.is_none()
            })
        {
            return Err(Hold::OriginAt(line!()));
        }
        let meet = local
            .iter()
            .find(|m| m.source == source && m.terminal == terminal)
            .cloned()
            .ok_or(Hold::OriginAt(line!()))?;
        if !source_meets.contains(&meet) {
            return Err(Hold::CoverageAt(line!()));
        }
        Ok(EndpointRoute {
            source,
            free,
            meet,
            source_nodes,
            source_meets,
        })
    };
    let payload = route(fold.actual_before, payload_source)?;
    let container = route(container_node, container_source)?;
    if payload.free == container.free {
        return Err(Hold::CompetingResponsibility);
    }
    Ok((payload, container))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CellPlan {
    pub(crate) store: CellReceipt,
    pub(crate) reset: CellReceipt,
    pub(crate) null_init: CellReceipt,
    pub(crate) order: BTreeMap<u32, usize>,
    pub(crate) sites: Vec<SourceSite>,
    pub(crate) terminals: Vec<usize>,
}
pub(crate) fn cell_plan(
    facts: &Facts,
    fold: &fold_call::Proof,
    payload: &EndpointRoute,
    container: &EndpointRoute,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<CellPlan, Hold> {
    use super::{
        super::{
            ownership_access::{Expression, OperandSyntax},
            ownership_occurrence::Availability::Present,
        },
        field_support::StoredValue,
        value_origins::{OriginAtom, ValueOrigins},
    };
    let call = &fold.call;
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_ref() == Some(&call.caller)
    };
    let body = one(
        facts.body_rosters.iter().filter(|b| scope(&b.point)),
        Hold::CoverageAt(line!()),
    )?;
    let arguments = body.argument_count != 0 && !super::facts::relax_frame();
    if arguments || !body.phis.is_empty() {
        return Err(Hold::BodyShape {
            arguments: body.argument_count,
            returns: body.return_width,
            phis: body.phis.len(),
        });
    }
    let reader = one(
        facts
            .reader_inputs
            .bodies
            .iter()
            .filter(|b| b.function == call.caller),
        Hold::CoverageAt(line!()),
    )?;
    if !reader.complete_operations
        || facts.source_occurrences.get(&call.caller) != Some(&reader.occurrences)
    {
        return Err(Hold::CoverageAt(line!()));
    }
    let mut order = BTreeMap::new();
    let mut next = 0;
    loop {
        let block = one(
            body.blocks
                .iter()
                .filter(|b| b.block == next && b.reachable),
            Hold::CoverageAt(line!()),
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
        return Err(Hold::CoverageAt(line!()));
    }
    let at = |block: u32, statement: usize| -> Result<(usize, usize), Hold> {
        Ok((
            *order.get(&block).ok_or(Hold::CoverageAt(line!()))?,
            statement,
        ))
    };
    let types = facts.fold_types.as_ref().ok_or(Hold::CoverageAt(line!()))?;
    let actual = one(
        facts
            .consumes
            .iter()
            .filter(|c| scope(&c.point) && c.ordinal == fold.actual_consume),
        Hold::CellIdentity,
    )?;
    let cell = super::super::ownership_access::PlaceSyntax {
        local: actual.local,
        projection: actual.projection.clone(),
    };
    check_effects(facts, fold, aliases)?;
    let origins =
        ValueOrigins::build_metadata(facts, aliases).map_err(|_| Hold::OriginAt(line!()))?;
    let stores = &facts.field_support_inputs.stores;
    let store = one(
        stores.iter().filter(|s| {
            s.site.function == call.caller
                && s.site.place == cell
                && matches!(s.value, StoredValue::Value(_))
        }),
        Hold::MissingStore,
    )?;
    let reset = one(
        stores.iter().filter(|s| {
            s.site.function == call.caller && s.site.place == cell && s.value == StoredValue::Null
        }),
        Hold::MissingReset,
    )?;
    if fold.internal.input_components.len() != 2
        || fold.internal.packed_return.is_some()
        || !fold.internal.used_fields.is_empty()
    {
        return Err(Hold::UnsupportedEffect);
    }
    let path = &fold.internal.input_components[1].0;
    let [
        super::super::ownership_occurrence::PathStep::Deref,
        super::super::ownership_occurrence::PathStep::Field {
            structure, index, ..
        },
    ] = path.as_slice()
    else {
        return Err(Hold::MissingNullInit);
    };
    let field = one(
        types.structures.iter().filter(|s| &s.identity == structure),
        Hold::MissingNullInit,
    )?
    .fields
    .iter()
    .find(|f| f.index == *index)
    .ok_or(Hold::MissingNullInit)?;
    let field_key = field.field_key.as_ref().ok_or(Hold::MissingNullInit)?;
    let null_init = one(
        stores.iter().filter(|s| {
            s.site.function == call.caller
                && &s.site.field_key == field_key
                && s.value == StoredValue::Null
        }),
        Hold::MissingNullInit,
    )?;
    let relevant: BTreeSet<_> = [
        store.site.clone(),
        reset.site.clone(),
        null_init.site.clone(),
    ]
    .into_iter()
    .collect();
    if stores
        .iter()
        .filter(|s| s.site.field_key == store.site.field_key || &s.site.field_key == field_key)
        .any(|s| !relevant.contains(&s.site) || !s.direct_projection || s.aggregate)
    {
        return Err(Hold::UnsupportedEffect);
    }
    let loads: Vec<_> = facts
        .field_support_inputs
        .loads
        .iter()
        .filter(|l| l.site.field_key == store.site.field_key || &l.site.field_key == field_key)
        .collect();
    let [load] = loads.as_slice() else { return Err(Hold::UnsupportedEffect) };
    if load.site.function != call.caller
        || load.site.place != cell
        || Some(load.site.block) != actual.point.block
        || Some(load.site.statement) != actual.point.statement
        || !load.direct_projection
        || load.shared_reference_root
    {
        return Err(Hold::CellIdentity);
    }
    for o in &reader.occurrences {
        if !o.syntax.destination.projection.is_empty()
            && !relevant.iter().any(|s| {
                s.block == o.site.block
                    && s.statement == o.site.statement
                    && s.place == o.syntax.destination
            })
        {
            return Err(Hold::UnsupportedEffect);
        }
        let source = match &o.syntax.expression {
            Expression::Value {
                operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
            }
            | Expression::Cast {
                operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
                ..
            } => Some(place),
            _ => None,
        };
        if source.is_some_and(|p| {
            !p.projection.is_empty()
                && (p != &cell
                    || o.site.block != load.site.block
                    || o.site.statement != load.site.statement)
        }) {
            return Err(Hold::UnsupportedEffect);
        }
    }
    let receipt = |store: &super::field_support::Store| -> Result<CellReceipt, Hold> {
        let consume = one(
            facts.consumes.iter().filter(|c| {
                scope(&c.point)
                    && c.point.block == Some(store.site.block)
                    && c.point.statement == Some(store.site.statement)
                    && c.local == store.site.place.local
                    && c.projection == store.site.place.projection
            }),
            Hold::CellIdentity,
        )?;
        let Present(w) = &consume.projected else { return Err(Hold::CellIdentity) };
        if w.use_end.checked_sub(w.use_start) != Some(1)
            || w.def_end.checked_sub(w.def_start) != Some(1)
        {
            return Err(Hold::CellIdentity);
        }
        let equations: Vec<_> = facts
            .equations
            .iter()
            .filter(|e| e.point == consume.point)
            .map(|e| EquationId {
                construction: call.construction,
                ordinal: e.ordinal,
            })
            .collect();
        if !facts.equations.iter().any(|e| {
            e.point == consume.point
                && e.operation == "assume"
                && e.value == Some(false)
                && e.variables == [w.use_start]
        }) {
            return Err(Hold::LawCoverage);
        }
        let node = |var| Node {
            construction: call.construction,
            var,
        };
        if store.value == StoredValue::Null
            && origins.at(node(w.def_start)) != BTreeSet::from([OriginAtom::Null])
        {
            return Err(Hold::MissingNullInit);
        }
        Ok(CellReceipt {
            site: store.site.clone(),
            consume: consume.ordinal,
            before: node(w.use_start),
            after: node(w.def_start),
            equations,
        })
    };
    let store = receipt(store)?;
    let reset = receipt(reset)?;
    let null_init = receipt(null_init)?;
    let init_consume = one(
        facts
            .consumes
            .iter()
            .filter(|c| scope(&c.point) && c.ordinal == null_init.consume),
        Hold::CellIdentity,
    )?;
    let Present(init_base) = &init_consume.base else { return Err(Hold::CellIdentity) };
    if origins.at(Node {
        construction: call.construction,
        var: init_base.use_start,
    }) != BTreeSet::from([OriginAtom::Fresh(payload.source.endpoint)])
    {
        return Err(Hold::CellIdentity);
    }
    let point = |id: EquationId| -> Result<(usize, usize), Hold> {
        let e = one(
            facts
                .equations
                .iter()
                .filter(|e| e.point.construction == id.construction && e.ordinal == id.ordinal),
            Hold::CoverageAt(line!()),
        )?;
        at(
            e.point.block.ok_or(Hold::CoverageAt(line!()))?,
            e.point.statement.ok_or(Hold::CoverageAt(line!()))?,
        )
    };
    if !(point(payload.source.endpoint)? < at(null_init.site.block, null_init.site.statement)?
        && at(null_init.site.block, null_init.site.statement)?
            < at(store.site.block, store.site.statement)?
        && point(container.source.endpoint)? < at(store.site.block, store.site.statement)?
        && at(store.site.block, store.site.statement)? < at(call.block, call.statement)?
        && at(call.block, call.statement)? < at(reset.site.block, reset.site.statement)?
        && at(reset.site.block, reset.site.statement)? < point(payload.free)?
        && point(payload.free)? < point(container.free)?)
    {
        return Err(Hold::CellIdentity);
    }
    let terminals = super::fold_coverage::validate(facts, call.construction, &call.caller)
        .map_err(|_| Hold::CoverageAt(line!()))?;
    Ok(CellPlan {
        store,
        reset,
        null_init,
        order,
        sites: reader.occurrences.iter().map(|o| o.site.clone()).collect(),
        terminals,
    })
}

/// Reject unmodelled effects before endpoint routing can lose their provenance.
/// R337-2: every occurrence this gate refuses, not just the first. The gate
/// itself returns at the first one, which made "held by one thing" mean "held by
/// the first thing"; the instrument needs the whole list to classify it.
/// R363-1: the aliases are a parameter because a re-derived snapshot has no
/// Z3-valued guards to compute them from, and D3 asks `ValueOrigins` — an
/// instrument computing its own would answer a different question than the gate
/// it reports on, and would answer it with an empty origin graph.
pub(crate) fn unsupported_occurrences<'a>(
    facts: &'a Facts,
    call: &super::matched::CallKey,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<Vec<&'a super::super::origin_evidence::SourceOccurrence>, Hold> {
    let mut refused = Vec::new();
    effects(facts, call, aliases, &mut |occurrence| {
        refused.push(occurrence)
    })?;
    Ok(refused)
}

pub(crate) fn check_effects(
    facts: &Facts,
    fold: &fold_call::Proof,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<(), Hold> {
    let mut held = false;
    effects(facts, &fold.call, aliases, &mut |_| held = true)?;
    if held {
        return Err(Hold::UnsupportedEffect);
    }
    Ok(())
}

/// R365-3: whether `atom` is the caller's own token coming back out of `call` —
/// the owner-return shape, one token in and the same token out, which is what
/// `root = insert(root, key)` is and what a `Box<Node>` insert compiles to.
///
/// The premise is the transfer INTO the callee recorded at THIS call. A callee
/// that returns an argument it was only lent is not this shape: the caller kept
/// its token, and admitting the return would let it hold the token twice. An
/// `Input` port that is not a consumed argument of this call is a different
/// token. `Borrowed` and `TraversalBorrow` are exactly the lending roles, and an
/// argument whose caller place the substitution could not identify is not
/// evidence that the caller's token is what moved.
pub(crate) fn returned_token(
    facts: &Facts,
    call: &super::matched::CallKey,
    atom: &super::value_origins::OriginAtom,
) -> bool {
    use super::{
        super::{
            ownership_boundary::{LicensingRole, Role, Window},
            ownership_occurrence::Availability::Present,
        },
        value_origins::OriginAtom,
    };
    let (OriginAtom::Input(port) | OriginAtom::UnresolvedInput { formal: port, .. }) = atom else {
        return false;
    };
    if port.construction != call.construction {
        return false;
    }
    facts
        .boundary_substitutions
        .iter()
        .filter(|row| {
            row.role == Role::CallArgument
                && row.point.construction == call.construction
                && row.point.function.as_deref() == Some(call.caller.as_str())
                && row.point.block == Some(call.block)
                && row.point.statement == Some(call.statement)
                && row.callee.as_deref() == Some(call.callee.as_str())
                && !matches!(
                    row.licensing_role,
                    LicensingRole::Borrowed | LicensingRole::TraversalBorrow
                )
                && matches!(row.actual_occurrence, Present(_))
        })
        .any(|row| match &row.formal {
            // The argument's ports are its formal ENTRY window, not only the
            // pairs the substitution matched: an owning argument transfers at
            // its root and the boundary pairs that root alone, so the deeper
            // components are `unmatched_formal_vars` of the same argument — the
            // ports `Input` is seeded on and `UnresolvedInput` names. A port
            // outside this window belongs to another argument or another call.
            Present(Window::Single { start, end }) => (*start..*end).contains(&port.var),
            Present(Window::UseDef {
                use_start, use_end, ..
            }) => (*use_start..*use_end).contains(&port.var),
            _ => false,
        })
}

/// Blocks reachable from `from`, over the recorded successor lists. The CFG is
/// the compiler's own snapshot, not the emitted equations, so a branch the
/// equation producer omitted is still present here.
pub(crate) fn reaches(blocks: &[super::coverage::Block], from: u32, to: u32) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![from];
    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }
        if block == to {
            return true;
        }
        if let Some(row) = blocks.iter().find(|row| row.block == block) {
            stack.extend(row.successors.iter().copied());
        }
    }
    false
}

/// R339-5 D2-a: two sites lie on mutually exclusive paths when neither block
/// reaches the other. A path is a sequence, so it can contain both only by
/// reaching one from the other — which makes this exact rather than
/// conservative.
pub(crate) fn mutually_exclusive(blocks: &[super::coverage::Block], left: u32, right: u32) -> bool {
    left != right && !reaches(blocks, left, right) && !reaches(blocks, right, left)
}

fn effects<'a>(
    facts: &'a Facts,
    call: &super::matched::CallKey,
    aliases: &BTreeMap<EquationId, EquationId>,
    refuse: &mut dyn FnMut(&'a super::super::origin_evidence::SourceOccurrence),
) -> Result<(), Hold> {
    use super::super::{
        origin_evidence::SourceCallee,
        ownership_access::{Expression, ImmediateOrigin, OperandSyntax},
    };
    let reader = one(
        facts
            .reader_inputs
            .bodies
            .iter()
            .filter(|b| b.function == call.caller),
        Hold::CoverageAt(line!()),
    )?;
    if !reader.complete_operations
        || facts.source_occurrences.get(&call.caller) != Some(&reader.occurrences)
    {
        return Err(Hold::CoverageAt(line!()));
    }
    let types = facts.fold_types.as_ref().ok_or(Hold::CoverageAt(line!()))?;
    let pointer = |place: &super::super::ownership_access::PlaceSyntax| -> Result<bool, Hold> {
        Ok(one(
            types
                .places
                .iter()
                .filter(|p| p.function == call.caller && &p.place == place),
            Hold::CoverageAt(line!()),
        )?
        .pointer
        .is_some())
    };
    // R339-5 D2-a: this caller's other declared fold sites, with the CFG the
    // exclusivity test reads.
    let fold_sites: std::collections::BTreeSet<(u32, usize)> = facts
        .fold_declarations
        .as_deref()
        .unwrap_or_default()
        .iter()
        .filter(|declaration| declaration.call.caller == call.caller)
        .map(|declaration| (declaration.call.block, declaration.call.statement))
        .collect();
    let blocks = facts
        .body_rosters
        .iter()
        .find(|roster| roster.point.function.as_deref() == Some(call.caller.as_str()))
        .map(|roster| roster.blocks.as_slice())
        .unwrap_or_default();
    // R339-5 D3: the node this site defines, from the compiler's own consume
    // rows. One row or none — a destination two rows claim is not a value this
    // gate can name.
    let defined = |o: &super::super::origin_evidence::SourceOccurrence| -> Option<Node> {
        use super::super::ownership_occurrence::Availability;
        let mut found = None;
        for consume in facts.consumes.iter().filter(|consume| {
            consume.point.function.as_deref() == Some(call.caller.as_str())
                && consume.point.block == Some(o.site.block)
                && consume.point.statement == Some(o.site.statement)
                && consume.local == o.syntax.destination.local
                && consume.projection == o.syntax.destination.projection
        }) {
            let Availability::Present(window) = &consume.projected else { return None };
            if window.def_start == window.def_end || found.is_some() {
                return None;
            }
            found = Some(Node {
                construction: consume.point.construction,
                var: window.def_start,
            });
        }
        found
    };
    // Built once and only if a D3 candidate is reached: every other arm decides
    // on facts already in hand.
    let mut origins: Option<super::value_origins::ValueOrigins> = None;
    // Effect rejection precedes using any selected endpoint/cell story.
    for o in &reader.occurrences {
        // D4: an integer branch predicate is not a token operation at all, and
        // refusing it would refuse every branching body for computing its own
        // condition. One predicate decides it, on recorded facts.
        if super::fold_types::moves_no_token(types, &call.caller, o) {
            continue;
        }
        if let Some(callee) = &o.callee {
            let allowed = match callee {
                SourceCallee::ForeignC(name) => {
                    matches!(name.as_str(), "malloc" | "calloc" | "free")
                }
                SourceCallee::Local(name) => {
                    let own = name == &call.callee
                        && o.site.block == call.block
                        && o.site.statement == call.statement;
                    let other_site = (o.site.block, o.site.statement);
                    // R339-5 D1: a callee that lends or borrows every pointer
                    // argument it is given moves no token out of this caller —
                    // it frames the argument and hands back a view, and the
                    // caller keeps its token across the call, which is what
                    // `lends_parameter` already establishes. The gate defers to
                    // the internal certificate for what becomes of the view:
                    // `SinkOnView` and `ViewStoredIntoOwningCell` are its rules,
                    // and this gate derives no view set of its own.
                    //
                    // A callee that neither lends nor borrows a pointer argument
                    // is a producer or a consumer and still refuses (K-D1), and
                    // so does an argument whose slot is not represented.
                    let lends_every_pointer_argument = || {
                        let mut pointers = 0;
                        for (index, argument) in o.arguments.iter().enumerate() {
                            if !matches!(
                                argument,
                                super::super::origin_evidence::OriginAvailability::Present(_)
                            ) {
                                continue;
                            }
                            pointers += 1;
                            if !facts.reader_plan.lends_parameter(name, index)
                                && !facts.reader_plan.borrows_parameter(name, index)
                            {
                                return false;
                            }
                        }
                        pointers > 0
                    };
                    if !own && !fold_sites.contains(&other_site) && lends_every_pointer_argument() {
                        continue;
                    }
                    // R339-5 D3: a callee given no pointer at all, whose return
                    // is fresh on every path, moves no token out of this caller
                    // — it creates one. `ValueOrigins` carries the callee's own
                    // origins across the boundary substitution, so this asks the
                    // callee's certificate rather than re-deriving freshness
                    // here, and `fresh_without_borrow` is the predicate this
                    // module already uses for the payload endpoint, so the two
                    // cannot disagree about the same value.
                    //
                    // Taking no pointer argument is necessary and not
                    // sufficient (K-D3): a callee handed an owning pointer could
                    // free it and still return a fresh cell, which the freshness
                    // half alone would admit. A callee that returns one of its
                    // inputs, a borrow, a null alone, or anything unclassified
                    // fails `fresh_without_borrow` and still refuses.
                    let takes_no_pointer = o.arguments.iter().all(|argument| {
                        !matches!(
                            argument,
                            super::super::origin_evidence::OriginAvailability::Present(_)
                        )
                    });
                    if !own && !fold_sites.contains(&other_site) && takes_no_pointer {
                        if origins.is_none() {
                            origins = Some(
                                super::value_origins::ValueOrigins::build_metadata(facts, aliases)
                                    .map_err(|_| Hold::OriginAt(line!()))?,
                            );
                        }
                        let produced = defined(o).is_some_and(|node| {
                            origins
                                .as_ref()
                                .expect("value origins built above")
                                .fresh_without_borrow(node)
                        });
                        if produced {
                            continue;
                        }
                    }
                    if !own && fold_sites.contains(&other_site) {
                        // D2-a: admitted when the two cannot share a path, and
                        // named when they can — the caller is then folding
                        // twice over one execution, which is D2-b's hold.
                        if !mutually_exclusive(blocks, call.block, o.site.block) {
                            return Err(Hold::MultipleFoldSitesOnPath);
                        }
                        true
                    } else {
                        own
                    }
                }
                SourceCallee::RustLibrary(name) => {
                    // R337-2(b): a read-only intrinsic reads and returns; it
                    // moves no token, which is why the internal certificate
                    // already admits it. Same predicate, so the two cannot
                    // disagree about the same call again.
                    reader.readonly_intrinsic(o.site.block, o.site.statement)
                        || (matches!(name.as_str(), "std::mem::size_of" | "core::mem::size_of")
                            && matches!(&o.syntax.expression,Expression::Call{operands} if operands.is_empty())
                            && !pointer(&o.syntax.destination)?)
                }
                _ => false,
            };
            if !allowed {
                refuse(o);
            }
        } else {
            let supported = match &o.syntax.expression {
                Expression::Value {
                    operand: OperandSyntax::Copy { .. } | OperandSyntax::Move { .. },
                } => true,
                Expression::Value {
                    operand: OperandSyntax::Constant { .. },
                } => !pointer(&o.syntax.destination)?,
                Expression::Cast {
                    operand: OperandSyntax::Copy { .. } | OperandSyntax::Move { .. },
                    cast,
                    ..
                } => cast == "PtrToPtr",
                Expression::Cast {
                    operand: OperandSyntax::Constant { zero: true, .. },
                    ..
                } => o.syntax.immediate_origin == ImmediateOrigin::Null,
                _ => false,
            };
            if !supported {
                refuse(o);
            }
        }
    }
    Ok(())
}

/// R377-1: the slot keys admitted by the return-port rule — a fresh allocation
/// whose ONLY escape from its frame is that frame's return.
///
/// The subject is the allocation's own slot, which is what carries the
/// undischarged `AllocationSource` guard; "at the return port" is the premise,
/// not the subject. Four conditions, each read off recorded evidence:
///
/// 1. every exit-return port of the frame is `Fresh | Null` with at least one
///    `Fresh` — every path returns a fresh token or nothing (null is
///    `Option::None` and carries no token, the 2026-08-23 ruling);
/// 2. this allocation reaches one of those ports;
/// 3. its token is never stored into a field — a `Value` store of it is a second
///    escape, and a `Null` store is not;
/// 4. its token is never handed to a callee — an outgoing call argument is a
///    second escape unless that callee's own no-retention evidence covers it,
///    which this rule does not yet consume (R377-1 §3).
///
/// A frame containing ANY in-frame free is refused. R377-1 ruled the error-path
/// free admissible, but admitting it needs per-return-statement delivery — which
/// return site delivers the token and which delivers null — and the recorded
/// `ReturnSelection` carries SSA versions that do not join to the port nodes.
/// Refusing is the sound reading until that evidence exists; see report 047.
/// R378-2 STOP 1: why a producer that is otherwise the shape was not admitted.
/// `ReturnSiteDeliveryUnknown` is the ruled-admissible error-path free that the
/// record cannot yet decide — which return site delivers the token and which
/// delivers null — so refusing is the sound reading, and the hold says so
/// instead of the producer silently missing from the set.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum ReturnPortHold {
    ReturnSiteDeliveryUnknown,
    PortNotFreshOrNull,
    StoredIntoField,
    HandedToCallee,
}

pub(crate) fn return_port_owning(
    facts: &Facts,
    origins: &super::value_origins::ValueOrigins,
) -> (BTreeSet<String>, BTreeMap<String, ReturnPortHold>) {
    use super::{
        super::{
            ownership_boundary::{Role, Variables},
            ownership_occurrence::Availability::Present,
        },
        field_support::StoredValue,
        value_origins::OriginAtom,
    };
    let mut admitted = BTreeSet::new();
    let mut holds: BTreeMap<String, ReturnPortHold> = BTreeMap::new();
    let mut hold = |keys: &[String], reason: ReturnPortHold| {
        for key in keys {
            holds.entry(key.clone()).or_insert(reason);
        }
    };
    for roster in &facts.body_rosters {
        let Some(function) = roster.point.function.as_deref() else { continue };
        let construction = roster.point.construction;
        let node = |var| Node { construction, var };
        let ports: Vec<Node> = facts
            .boundary_substitutions
            .iter()
            .filter(|row| {
                row.role == Role::ExitReturn
                    && row.point.construction == construction
                    && row.point.function.as_deref() == Some(function)
            })
            .flat_map(|row| {
                row.matched
                    .iter()
                    .filter_map(move |pair| match pair.formal {
                        Variables::Single { var } => Some(node(var)),
                        Variables::UseDef { .. } => None,
                    })
            })
            .collect();
        if ports.is_empty() {
            continue;
        }
        // (1) every port is fresh-or-null, and some port carries a token.
        let atoms: Vec<_> = ports.iter().flat_map(|port| origins.at(*port)).collect();
        let frame_heads: Vec<String> = facts
            .raw_pointer_heads
            .iter()
            .filter(|head| head.function == function)
            .map(|head| head.slot_key.clone())
            .collect();
        if !atoms
            .iter()
            .all(|atom| matches!(atom, OriginAtom::Fresh(_) | OriginAtom::Null))
        {
            hold(&frame_heads, ReturnPortHold::PortNotFreshOrNull);
            continue;
        }
        let returned: BTreeSet<EquationId> = atoms
            .iter()
            .filter_map(|atom| match atom {
                OriginAtom::Fresh(id) => Some(*id),
                _ => None,
            })
            .collect();
        if returned.is_empty() {
            continue;
        }
        // A free anywhere in the frame refuses it; see the note above.
        if facts.equations.iter().any(|equation| {
            equation.point.construction == construction
                && equation.point.function.as_deref() == Some(function)
                && equation
                    .endpoint
                    .as_ref()
                    .is_some_and(|endpoint| endpoint.callee == "free")
        }) {
            hold(&frame_heads, ReturnPortHold::ReturnSiteDeliveryUnknown);
            continue;
        }
        // The node a place holds at a site, from the frame's own consume rows.
        let at_place =
            |block: u32, statement: usize, place: &super::super::ownership_access::PlaceSyntax| {
                facts
                    .consumes
                    .iter()
                    .filter(|consume| {
                        consume.point.construction == construction
                            && consume.point.function.as_deref() == Some(function)
                            && consume.point.block == Some(block)
                            && consume.point.statement == Some(statement)
                            && consume.local == place.local
                            && consume.projection == place.projection
                    })
                    .filter_map(|consume| match &consume.projected {
                        Present(window) if window.use_start != window.use_end => {
                            Some(node(window.use_start))
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>()
            };
        let escapes = |source: EquationId| {
            // (3) stored into a field.
            let stored = facts.field_support_inputs.stores.iter().any(|store| {
                store.site.function == function
                    && matches!(store.value, StoredValue::Value(_))
                    && match &store.value {
                        StoredValue::Value(place) => {
                            at_place(store.site.block, store.site.statement, place)
                                .into_iter()
                                .any(|n| origins.at(n).contains(&OriginAtom::Fresh(source)))
                        }
                        _ => false,
                    }
            });
            // (4) handed to a callee.
            let passed = facts.boundary_substitutions.iter().any(|row| {
                row.role == Role::CallArgument
                    && row.point.construction == construction
                    && row.point.function.as_deref() == Some(function)
                    && row.matched.iter().any(|pair| match pair.actual {
                        Variables::Single { var } => {
                            origins.at(node(var)).contains(&OriginAtom::Fresh(source))
                        }
                        Variables::UseDef { use_var, .. } => origins
                            .at(node(use_var))
                            .contains(&OriginAtom::Fresh(source)),
                    })
            });
            stored || passed
        };
        for head in facts
            .raw_pointer_heads
            .iter()
            .filter(|head| head.function == function)
        {
            // (2) this allocation reaches a port: the slot's own versions carry a
            // returned `Fresh`, and nothing else.
            let mut reaches = None;
            for consume in facts.consumes.iter().filter(|consume| {
                consume.point.construction == construction
                    && consume.point.function.as_deref() == Some(function)
                    && consume.local == head.local
            }) {
                let Present(window) = &consume.projected else { continue };
                for var in [window.use_start, window.def_start] {
                    for atom in origins.at(node(var)) {
                        if let OriginAtom::Fresh(id) = atom
                            && returned.contains(&id)
                        {
                            reaches = Some(id);
                        }
                    }
                }
            }
            if let Some(source) = reaches {
                if escapes(source) {
                    hold(
                        std::slice::from_ref(&head.slot_key),
                        ReturnPortHold::StoredIntoField,
                    );
                } else {
                    admitted.insert(head.slot_key.clone());
                }
            }
        }
    }
    holds.retain(|key, _| !admitted.contains(key));
    (admitted, holds)
}
