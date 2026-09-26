//! Three distinct caller responsibility routes for a consuming member return.
//!
//! The identity audit contracts the call into one token, which is exactly what
//! a folded member may not do: the parent stops at the consuming actual and is
//! freed inside the callee, while the member crosses the same call and comes
//! back through the authenticated return. This audit therefore adds the
//! member-to-receiver bridge instead of the identity contraction, and it never
//! seeds the descendants all-zero — the member's input is owning, and only its
//! projected parameter-output is zero.
use std::collections::BTreeSet;

use super::{
    facts::{EquationId, Facts},
    fold_caller::Hold,
    fold_laws::{self, Plan},
    fold_member_output::ZeroOutput,
    fold_subtree::Membership,
    matched::{MatchedTransport, MemberReturn, SourceInstance, TerminalTarget},
    transport::Node,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Route {
    pub(crate) source: SourceInstance,
    pub(crate) free: EquationId,
    pub(crate) target: Node,
    pub(crate) owning: Vec<Node>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct MemberPlan {
    pub(crate) laws: Plan,
    pub(crate) routes: Vec<Route>,
}

pub(crate) fn audit(
    facts: &Facts,
    member: &Membership,
    forwarded: &MemberReturn,
    zero: &ZeroOutput,
) -> Result<MemberPlan, Hold> {
    audit_metadata(
        facts,
        member,
        forwarded,
        zero,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}

pub(crate) fn audit_metadata(
    facts: &Facts,
    member: &Membership,
    forwarded: &MemberReturn,
    zero: &ZeroOutput,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
    slots: &BTreeSet<String>,
) -> Result<MemberPlan, Hold> {
    let call = &member.fold.call;
    let [descendant] = member.fold.descendants.as_slice() else {
        return Err(Hold::LawCoverage);
    };
    // Both receipts must be this member's, at this call, under its guard.
    if forwarded.membership.as_ref() != member
        || forwarded.forwarding.receiver != member.fold.receiver
        || forwarded.forwarding.call != *call
        || zero.source != member.member
        || zero.call != *call
        || zero.guard != member.declaration.guard
        || zero.required_zero != descendant.output
        || zero.formal.var != descendant.formal_def
    {
        return Err(Hold::Forwarding);
    }
    if super::fold_coverage::validate(facts, call.construction, &call.caller)
        .map_err(|_| Hold::LawCoverage)?
        != member.terminal_inventory
    {
        return Err(Hold::LawCoverage);
    }
    let native = fold_laws::inventory(facts, call)?;
    let node = |var| Node {
        construction: call.construction,
        var,
    };
    let (graph, mut edges) = fold_laws::edge_map(facts, &native.equations, aliases)?;
    // The only crossing of this call is the one OC04 authenticated: the member
    // leaves through the packed return and lands in the receiver. The parent's
    // own token never crosses back, so no `actual_before -> receiver` edge.
    edges
        .entry(member.member_before)
        .or_default()
        .insert(member.fold.receiver);
    let transport = MatchedTransport::build_with_subtree_folds_metadata(
        facts,
        &[(member.declaration.guard, member.fold.clone())],
        std::slice::from_ref(member),
        aliases,
        slots,
    )
    .map_err(|_| Hold::CoverageAt(line!()))?;
    let mut routes: Vec<Route> = Vec::new();
    for endpoint in &graph.sources {
        let frees: Vec<_> = transport
            .meets_for(endpoint.node)
            .into_iter()
            .filter(|meet| matches!(meet.terminal.target, TerminalTarget::Free(_)))
            .collect();
        let [meet] = frees.as_slice() else {
            return Err(Hold::CompetingResponsibility);
        };
        let TerminalTarget::Free(free) = meet.terminal.target else {
            return Err(Hold::OriginAt(line!()));
        };
        let sink = graph
            .sinks
            .iter()
            .find(|s| s.equation == free)
            .ok_or(Hold::OriginAt(line!()))?;
        // The parent's responsibility ends at the consuming actual; its free is
        // inside the callee and is closed by the internal certificate, not by a
        // caller-side route. Everything else walks to its own free.
        let parent = meet.source == member.parent;
        if parent != (sink.endpoint.function == call.callee) {
            return Err(Hold::OriginAt(line!()));
        }
        let target = if parent {
            member.fold.actual_before
        } else {
            sink.node
        };
        let owning = fold_laws::walk(&edges, endpoint.node, target)?;
        if parent && owning.contains(&member.fold.receiver) {
            return Err(Hold::CompetingResponsibility);
        }
        routes.push(Route {
            source: meet.source.clone(),
            free,
            target,
            owning: owning.into_iter().collect(),
        });
    }
    let leaf = routes
        .iter()
        .find(|route| route.source == member.member)
        .ok_or(Hold::OriginAt(line!()))?;
    if !leaf.owning.contains(&member.member_before) || !leaf.owning.contains(&member.fold.receiver)
    {
        return Err(Hold::Forwarding);
    }
    if !routes.iter().any(|route| route.source == member.parent)
        || routes.len() != graph.sources.len()
    {
        return Err(Hold::OriginAt(line!()));
    }
    for (index, route) in routes.iter().enumerate() {
        let nodes: BTreeSet<_> = route.owning.iter().copied().collect();
        for other in &routes[index + 1..] {
            if !nodes.is_disjoint(&other.owning.iter().copied().collect()) {
                return Err(Hold::CompetingResponsibility);
            }
        }
    }
    let mut owning: BTreeSet<_> = routes
        .iter()
        .flat_map(|route| route.owning.iter().copied())
        .collect();
    owning.extend(member.requirements.owning.iter().copied());
    // The member's input is consumed by the callee, so it owns; the identity
    // audit's all-descendants-zero seed would contradict the fold.
    let known_owning = BTreeSet::from([node(descendant.formal_use), descendant.input]);
    owning.extend(known_owning.iter().copied());
    let mut known_zero = BTreeSet::from([
        member.fold.actual_after,
        member.member_after,
        zero.formal,
        zero.required_zero,
    ]);
    known_zero.extend(member.requirements.zero.iter().copied());
    let mut guards = std::collections::BTreeMap::new();
    for endpoint in graph.sources.iter().chain(&graph.sinks) {
        guards.insert(
            *aliases.get(&endpoint.equation).ok_or(Hold::LawCoverage)?,
            true,
        );
    }
    for (key, value) in member
        .requirements
        .guards
        .iter()
        .chain(&member.fold.internal.required_guards)
        .copied()
        .chain(
            forwarded
                .forwarding
                .guards
                .iter()
                .map(|(key, value)| (*key, *value)),
        )
    {
        if guards.insert(key, value).is_some_and(|old| old != value) {
            return Err(Hold::LawCoverage);
        }
    }
    let zero_nodes =
        fold_laws::evaluate(facts, call, &native, &owning, &known_owning, &known_zero)?;
    Ok(MemberPlan {
        laws: Plan {
            owning: owning.into_iter().collect(),
            zero: zero_nodes,
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
        },
        routes,
    })
}
