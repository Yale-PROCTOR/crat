//! The caller certificate for a consuming member return. Metadata only: it
//! selects nothing, grants nothing, and activates no fold. It binds the four
//! things that must agree — membership, the authenticated return, the projected
//! zero receipt and the three-route law plan — and refuses if any of them is
//! about a different member, call or guard.
use std::collections::BTreeSet;

use super::{
    facts::{EquationId, Facts},
    fold_call,
    fold_caller::Hold,
    fold_declaration::Declaration,
    fold_member_laws::MemberPlan,
    fold_member_output::ZeroOutput,
    fold_permission::Requirements,
    fold_subtree::Membership,
    matched::{MatchedTransport, Meet, MemberReturn, TerminalTarget},
    transport::CandidateGraph,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct MemberCallerProof {
    pub(crate) guard: EquationId,
    /// A premise for activation, not a claim inferred from local call syntax.
    pub(crate) required_closed_frame: bool,
    pub(crate) membership: Membership,
    pub(crate) forwarding: MemberReturn,
    pub(crate) zero_output: ZeroOutput,
    pub(crate) plan: MemberPlan,
    pub(crate) requirements: Requirements,
    /// The caller's own endpoints, all of them on a route. The parent's free is
    /// the callee's and is deliberately absent.
    pub(crate) endpoints: Vec<EquationId>,
    pub(crate) checked_consumes: Vec<usize>,
    pub(crate) checked_equations: Vec<EquationId>,
    pub(crate) terminal_inventory: Vec<usize>,
}

fn one<T>(items: impl IntoIterator<Item = T>, hold: Hold) -> Result<T, Hold> {
    let mut items = items.into_iter();
    let value = items.next().ok_or_else(|| hold.clone())?;
    if items.next().is_some() {
        return Err(hold);
    }
    Ok(value)
}

pub(crate) fn certify(
    facts: &Facts,
    declaration: &Declaration,
    fold: &fold_call::Proof,
) -> Result<MemberCallerProof, Hold> {
    certify_metadata(
        facts,
        declaration,
        fold,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}

/// Reconstruction consumes predicate identity metadata only; no ASTs.
pub(crate) fn certify_metadata(
    facts: &Facts,
    declaration: &Declaration,
    fold: &fold_call::Proof,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
    slots: &BTreeSet<String>,
) -> Result<MemberCallerProof, Hold> {
    super::fold_caller::check_effects(facts, fold, aliases)?;
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
    // R339-5 D2-a, in the member path too: the requirement is one call to this
    // callee on THIS path, not one in the whole body. `deleteNode` calls itself
    // from three mutually exclusive arms, and a body-wide uniqueness test reads
    // that as an unsupported effect.
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
                    && super::fold_caller::mutually_exclusive(blocks, call.block, c.site.block))
        })
    {
        return Err(Hold::UnsupportedEffect);
    }
    let member = super::fold_subtree::certify_metadata(facts, declaration, fold, aliases, slots)
        .map_err(|hold| match hold {
            super::fold_subtree::Hold::UnsupportedEffect => Hold::UnsupportedEffect,
            other => Hold::Member(other),
        })?;
    let [descendant] = member.fold.descendants.as_slice() else {
        return Err(Hold::CoverageAt(line!()));
    };
    let transport = MatchedTransport::build_with_subtree_folds_metadata(
        facts,
        &[(declaration.guard, fold.clone())],
        std::slice::from_ref(&member),
        aliases,
        slots,
    )
    .map_err(|_| Hold::CoverageAt(line!()))?;
    let graph =
        CandidateGraph::build_metadata(facts, aliases).map_err(|_| Hold::CoverageAt(line!()))?;
    let seed = one(
        graph
            .sources
            .iter()
            .filter(|s| s.equation == member.member.endpoint),
        Hold::OriginAt(line!()),
    )?;
    let meets = transport.meets_for(seed.node);
    let at = |node| move |meet: &&Meet| matches!(meet.terminal.target, TerminalTarget::Output { node: n, .. } if n == node);
    let returned = member
        .fold
        .internal
        .packed_return
        .as_ref()
        .ok_or(Hold::CoverageAt(line!()))?
        .root;
    let output = one(meets.iter().filter(at(returned)), Hold::Forwarding)?;
    let projected = one(meets.iter().filter(at(descendant.output)), Hold::Forwarding)?;
    let free = one(
        meets
            .iter()
            .filter(|m| matches!(m.terminal.target, TerminalTarget::Free(_))),
        Hold::Forwarding,
    )?;
    let forwarding = transport
        .forward_member_return_metadata(facts, output, free, &member, slots)
        .ok_or(Hold::Forwarding)?;
    let zero_output =
        super::fold_member_output::certify_metadata(facts, &member, projected, aliases, slots)
            .map_err(|_| Hold::Forwarding)?;
    let plan = super::fold_member_laws::audit_metadata(
        facts,
        &member,
        &forwarding,
        &zero_output,
        aliases,
        slots,
    )?;

    // Every endpoint this caller declares belongs to one of the three routes.
    // The parent's free is the callee's and is deliberately not in this set.
    let declared: BTreeSet<_> = facts
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
    let mut routed: BTreeSet<_> = plan
        .routes
        .iter()
        .map(|route| route.source.endpoint)
        .collect();
    for route in &plan.routes {
        let sink = graph
            .sinks
            .iter()
            .find(|s| s.equation == route.free)
            .ok_or(Hold::OriginAt(line!()))?;
        if sink.endpoint.function == call.caller {
            routed.insert(route.free);
        }
    }
    if declared != routed {
        return Err(Hold::CompetingResponsibility);
    }
    let endpoints: Vec<_> = routed.into_iter().collect();

    let mut requirements = member.requirements.clone();
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
    if !slots.contains(&container_key) {
        return Err(Hold::CoverageAt(line!()));
    }
    requirements.kind_keys.push(container_key);
    requirements.kind_keys.sort();
    requirements.kind_keys.dedup();
    requirements.owning.extend(plan.laws.owning.iter().copied());
    requirements.owning.sort();
    requirements.owning.dedup();
    requirements.zero.extend(plan.laws.zero.iter().copied());
    requirements.zero.sort();
    requirements.zero.dedup();
    if requirements
        .owning
        .iter()
        .any(|node| requirements.zero.contains(node))
    {
        return Err(Hold::LawCoverage);
    }
    let mut guards: std::collections::BTreeMap<_, _> =
        requirements.guards.iter().copied().collect();
    for (key, value) in plan
        .laws
        .guards
        .iter()
        .copied()
        .chain(forwarding.forwarding.guards.iter().map(|(k, v)| (*k, *v)))
    {
        if guards.insert(key, value).is_some_and(|old| old != value) {
            return Err(Hold::LawCoverage);
        }
    }
    requirements.guards = guards.into_iter().collect();
    Ok(MemberCallerProof {
        guard: declaration.guard,
        required_closed_frame: true,
        terminal_inventory: member.terminal_inventory.clone(),
        checked_consumes: plan.laws.consumes.clone(),
        checked_equations: plan.laws.equations.clone(),
        endpoints,
        membership: member,
        forwarding,
        zero_output,
        plan,
        requirements,
    })
}
