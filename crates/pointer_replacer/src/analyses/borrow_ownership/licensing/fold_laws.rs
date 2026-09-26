//! Conditional caller ownership-law audit; no solver query or activation.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    super::{
        ownership_access::{Expression, OperandSyntax},
        ownership_boundary,
        ownership_evidence::{Equation, Point},
        ownership_occurrence::{self, Availability::Present, Consumption},
    },
    facts::{EquationId, Facts},
    fold_call,
    fold_caller::{CellPlan, EndpointRoute, Hold},
    matched::CallKey,
    transport::{CandidateGraph, Evidence, Node, Rule},
};
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Plan {
    pub(crate) owning: Vec<Node>,
    pub(crate) zero: Vec<Node>,
    pub(crate) guards: Vec<(EquationId, bool)>,
    pub(crate) equations: Vec<EquationId>,
    pub(crate) consumes: Vec<usize>,
}
/// The native caller inventory both law audits stand on: complete occurrence and
/// boundary shapes, every projection frame including the zero components off the
/// live route, and an exact transfer law with its old-zero for each native
/// source window. It contracts no call and seeds no ownership.
pub(crate) struct Inventory {
    pub(crate) equations: Vec<Equation>,
    pub(crate) consumes: Vec<Consumption>,
}

fn scoped(call: &CallKey) -> impl Fn(&Point) -> bool + '_ {
    move |point: &Point| {
        point.construction == call.construction && point.function.as_ref() == Some(&call.caller)
    }
}

pub(crate) fn inventory(facts: &Facts, call: &CallKey) -> Result<Inventory, Hold> {
    let scope = scoped(call);
    let equations: Vec<_> = facts
        .equations
        .iter()
        .filter(|e| scope(&e.point))
        .cloned()
        .collect();
    let consumes: Vec<_> = facts
        .consumes
        .iter()
        .filter(|c| scope(&c.point))
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
        .map_err(|_| Hold::LawCoverage)?;
    ownership_boundary::validate_shapes(&call.caller, &boundaries, &registrations)
        .map_err(|_| Hold::LawCoverage)?;
    ownership_boundary::validate_links(
        &call.caller,
        &boundaries,
        &registrations,
        &consumes,
        &equations,
    )
    .map_err(|_| Hold::LawCoverage)?;
    if equations.iter().any(|e| e.validate().is_err()) {
        return Err(Hold::LawCoverage);
    }
    // Complete projection frames, including zero components off the live route.
    for c in &consumes {
        let Present(base) = &c.base else { continue };
        for (u, d) in (base.use_start..base.use_end).zip(base.def_start..base.def_end) {
            if matches!(&c.projected,Present(w) if (w.use_start..w.use_end).contains(&u)) {
                continue;
            }
            if !equations.iter().any(|e| {
                e.point == c.point
                    && e.transfer.is_none()
                    && e.operation == "equal"
                    && e.variables == [u, d]
            }) {
                return Err(Hold::LawCoverage);
            }
        }
    }
    // Use native source/consume windows as the component denominator.
    for o in facts
        .source_occurrences
        .get(&call.caller)
        .ok_or(Hold::LawCoverage)?
    {
        let source = match &o.syntax.expression {
            Expression::Value {
                operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
            }
            | Expression::Cast {
                operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
                ..
            } => place,
            _ => continue,
        };
        let at = |p: &Point| p.block == Some(o.site.block) && p.statement == Some(o.site.statement);
        let src = one(consumes
            .iter()
            .filter(|c| {
                at(&c.point) && c.local == source.local && c.projection == source.projection
            })
            .collect())?;
        let destinations: Vec<_> = consumes
            .iter()
            .filter(|c| {
                at(&c.point)
                    && c.local == o.syntax.destination.local
                    && c.projection == o.syntax.destination.projection
            })
            .collect();
        let dst = one(destinations)?;
        let (Present(sw), Present(dw)) = (&src.projected, &dst.projected) else {
            if registrations.iter().any(|r| {
                at(&r.point)
                    && !r.by_reference
                    && r.proxy_local == o.syntax.destination.local
                    && r.source_occurrence == Present(src.ordinal)
            }) {
                continue;
            }
            return Err(Hold::LawCoverage);
        };
        let width = (sw.use_end - sw.use_start).min(dw.use_end - dw.use_start);
        let width = if matches!(o.syntax.expression, Expression::Cast { .. }) {
            width.min(1)
        } else {
            width
        };
        for offset in 0..width {
            let laws:Vec<_>=equations.iter().filter(|e|at(&e.point) && matches!(e.operation.as_str(),"equal"|"linear")
                && e.transfer.as_ref().is_some_and(|t|matches!((&t.source,&t.destination),(Present(s),Present(d))
                    if s.consume==src.ordinal && d.consume==dst.ordinal && t.source_use==sw.use_start+offset && t.destination_use==dw.use_start+offset))).collect();
            let [law] = laws.as_slice() else { return Err(Hold::LawCoverage) };
            let t = law.transfer.as_ref().unwrap();
            let zero = |var| {
                equations.iter().any(|e| {
                    e.point == law.point
                        && e.transfer.as_ref() == Some(t)
                        && e.operation == "assume"
                        && e.value == Some(false)
                        && e.variables == [var]
                })
            };
            if !zero(t.destination_use) || (t.by_move && !zero(t.source_def)) {
                return Err(Hold::LawCoverage);
            }
        }
    }
    Ok(Inventory {
        equations,
        consumes,
    })
}

/// Directed identity edges inside this caller. No call is contracted here: each
/// audit adds exactly the crossing its own certificate authenticates.
pub(crate) fn edge_map(
    facts: &Facts,
    equations: &[Equation],
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<(CandidateGraph, BTreeMap<Node, BTreeSet<Node>>), Hold> {
    let graph = CandidateGraph::build_metadata(facts, aliases).map_err(|_| Hold::LawCoverage)?;
    let mut edges: BTreeMap<Node, BTreeSet<Node>> = BTreeMap::new();
    for edge in &graph.edges {
        let id = match edge.evidence {
            Evidence::Transfer(id) | Evidence::Frame { equation: id, .. } => id,
            _ => continue,
        };
        if equations
            .iter()
            .any(|e| e.ordinal == id.ordinal && e.point.construction == id.construction)
            && edge.guard.is_none()
            && matches!(edge.rule, Rule::Copy | Rule::Frame)
        {
            edges.entry(edge.from).or_default().insert(edge.to);
        }
    }
    Ok((graph, edges))
}

/// The single positive route from a source to a target, or a hold. A fork, a
/// cycle or a dead end is never resolved by choosing.
pub(crate) fn walk(
    edges: &BTreeMap<Node, BTreeSet<Node>>,
    source: Node,
    target: Node,
) -> Result<BTreeSet<Node>, Hold> {
    let mut reaches = BTreeSet::from([target]);
    loop {
        let before = reaches.len();
        for (from, to) in edges {
            if to.iter().any(|n| reaches.contains(n)) {
                reaches.insert(*from);
            }
        }
        if reaches.len() == before {
            break;
        }
    }
    let mut path = BTreeSet::new();
    let mut at = source;
    while at != target {
        if !path.insert(at) {
            return Err(Hold::LawCoverage);
        }
        let next: Vec<_> = edges
            .get(&at)
            .into_iter()
            .flatten()
            .filter(|n| reaches.contains(n))
            .copied()
            .collect();
        let [successor] = next.as_slice() else { return Err(Hold::LawCoverage) };
        at = *successor;
    }
    path.insert(target);
    Ok(path)
}

/// Validate every caller equation under a seeding, and report the zero set it
/// forces. The seeding is the caller's, never the model's.
pub(crate) fn evaluate(
    facts: &Facts,
    call: &CallKey,
    native: &Inventory,
    owning: &BTreeSet<Node>,
    known_owning: &BTreeSet<Node>,
    known_zero: &BTreeSet<Node>,
) -> Result<Vec<Node>, Hold> {
    let scope = scoped(call);
    let node = |var| Node {
        construction: call.construction,
        var,
    };
    let body = facts
        .body_rosters
        .iter()
        .find(|b| scope(&b.point))
        .ok_or(Hold::LawCoverage)?;
    let mut values: BTreeMap<u32, bool> = body
        .versions
        .iter()
        .flat_map(|v| v.variables.iter().copied())
        .map(|v| (v, owning.contains(&node(v))))
        .collect();
    for c in &native.consumes {
        if let Present(w) = &c.base {
            for v in (w.use_start..w.use_end).chain(w.def_start..w.def_end) {
                values.insert(v, owning.contains(&node(v)));
            }
        }
    }
    // A boundary variable outside the body roster still has to carry a value.
    // The identity audit seeds none of these; the member audit seeds the
    // descendant its consuming input owns.
    for n in known_owning {
        if known_zero.contains(n) {
            return Err(Hold::LawCoverage);
        }
        values.insert(n.var, true);
    }
    for n in known_zero {
        if owning.contains(n) {
            return Err(Hold::LawCoverage);
        }
        values.insert(n.var, false);
    }
    // The native signature variables at this boundary are exact equalities.
    loop {
        let before = values.len();
        for e in &native.equations {
            if e.operation == "equal" && e.transfer.is_none() {
                let (a, b) = (e.variables[0], e.variables[1]);
                match (values.get(&a).copied(), values.get(&b).copied()) {
                    (Some(v), None) => {
                        values.insert(b, v);
                    }
                    (None, Some(v)) => {
                        values.insert(a, v);
                    }
                    _ => {}
                }
            }
        }
        if values.len() == before {
            break;
        }
    }
    for e in &native.equations {
        let v = |index: usize| {
            values
                .get(&e.variables[index])
                .copied()
                .ok_or(Hold::LawCoverage)
        };
        let ok = match e.operation.as_str() {
            "source" | "sink" => v(0)?,
            "assume" => v(0)? == e.value.ok_or(Hold::LawCoverage)?,
            "equal" => v(0)? == v(1)?,
            "linear" => (u8::from(v(0)?) + u8::from(v(1)?)) == u8::from(v(2)?),
            "guarded-fold-call" => true,
            _ => false,
        };
        if !ok {
            return Err(Hold::LawCoverage);
        }
    }
    Ok(values
        .iter()
        .filter_map(|(&var, &value)| (!value).then_some(node(var)))
        .collect())
}

pub(crate) fn audit(
    facts: &Facts,
    fold: &fold_call::Proof,
    payload: &EndpointRoute,
    container: &EndpointRoute,
    cell: &CellPlan,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Result<Plan, Hold> {
    let call = &fold.call;
    if super::fold_coverage::validate(facts, call.construction, &call.caller)
        .map_err(|_| Hold::LawCoverage)?
        != cell.terminals
    {
        return Err(Hold::LawCoverage);
    }
    let native = inventory(facts, call)?;
    let node = |var| Node {
        construction: call.construction,
        var,
    };
    let (graph, mut edges) = edge_map(facts, &native.equations, aliases)?;
    // GF05/ForwardedReturn justify this one-token contraction of the callee.
    edges
        .entry(fold.actual_before)
        .or_default()
        .insert(fold.receiver);
    let route = |endpoint: &EndpointRoute| -> Result<BTreeSet<Node>, Hold> {
        let source = graph
            .sources
            .iter()
            .find(|s| s.equation == endpoint.source.endpoint)
            .ok_or(Hold::LawCoverage)?
            .node;
        let target = graph
            .sinks
            .iter()
            .find(|s| s.equation == endpoint.free)
            .ok_or(Hold::LawCoverage)?
            .node;
        walk(&edges, source, target)
    };
    let payload_route = route(payload)?;
    let container_route = route(container)?;
    if !payload_route.is_disjoint(&container_route) {
        return Err(Hold::CompetingResponsibility);
    }
    let owning: BTreeSet<_> = payload_route.union(&container_route).copied().collect();
    if !owning.contains(&fold.actual_before) || !owning.contains(&fold.receiver) {
        return Err(Hold::LawCoverage);
    }
    let mut known_zero = BTreeSet::from([
        fold.actual_after,
        cell.store.before,
        cell.reset.before,
        cell.reset.after,
        cell.null_init.before,
        cell.null_init.after,
    ]);
    // The admitted caller initializes the sole descendant to None, and the
    // identity contract does not touch it. No extra descendant owner is born.
    for d in &fold.descendants {
        known_zero.extend([node(d.formal_use), node(d.formal_def), d.input, d.output]);
    }
    let mut guards = BTreeMap::new();
    for endpoint in [
        payload.source.endpoint,
        payload.free,
        container.source.endpoint,
        container.free,
    ] {
        guards.insert(*aliases.get(&endpoint).ok_or(Hold::LawCoverage)?, true);
    }
    for (key, value) in &fold.internal.required_guards {
        if guards.insert(*key, *value).is_some_and(|old| old != *value) {
            return Err(Hold::LawCoverage);
        }
    }
    let zero = evaluate(facts, call, &native, &owning, &BTreeSet::new(), &known_zero)?;
    Ok(Plan {
        owning: owning.into_iter().collect(),
        zero,
        guards: guards.into_iter().collect(),
        equations: native
            .equations
            .iter()
            .map(|e| EquationId {
                construction: e.point.construction,
                ordinal: e.ordinal,
            })
            .collect(),
        consumes: native.consumes.iter().map(|c| c.ordinal).collect(),
    })
}

fn one<'a>(
    rows: Vec<&'a super::super::ownership_occurrence::Consumption>,
) -> Result<&'a super::super::ownership_occurrence::Consumption, Hold> {
    let [row] = rows.as_slice() else { return Err(Hold::LawCoverage) };
    Ok(*row)
}
