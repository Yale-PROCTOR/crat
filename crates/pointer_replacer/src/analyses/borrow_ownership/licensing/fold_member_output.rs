//! Conditional zero-output receipt; never removes an output or invents a free.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    facts::{EquationId, Facts},
    fold_subtree::Membership,
    matched::{CallKey, Meet, SourceInstance},
    transport::Node,
};
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ZeroOutput {
    pub(crate) source: SourceInstance,
    pub(crate) call: CallKey,
    pub(crate) guard: EquationId,
    pub(crate) output: Meet,
    pub(crate) required_zero: Node,
    pub(crate) formal: Node,
    pub(crate) boundary: usize,
    pub(crate) equality: EquationId,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    Membership,
    NotProjectedOutput,
    Identity,
    MissingZero,
    Boundary,
}
pub(crate) fn certify(
    facts: &Facts,
    member: &Membership,
    output: &Meet,
) -> Result<ZeroOutput, Hold> {
    certify_metadata(
        facts,
        member,
        output,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}
pub(crate) fn certify_metadata(
    facts: &Facts,
    member: &Membership,
    output: &Meet,
    aliases: &BTreeMap<EquationId, EquationId>,
    slots: &BTreeSet<String>,
) -> Result<ZeroOutput, Hold> {
    use super::{
        super::{
            ownership_boundary::{Role, Variables},
            ownership_occurrence::{Availability::Present, PathStep},
        },
        matched::{MatchedTransport, SourceLineage, TerminalTarget},
    };
    let TerminalTarget::Output { node, ordinal } = output.terminal.target else {
        return Err(Hold::NotProjectedOutput);
    };
    let descendant = one(
        member.fold.descendants.iter().filter(|d| d.output == node),
        Hold::NotProjectedOutput,
    )?;
    if !matches!(
        descendant.path.as_slice(),
        [PathStep::Deref, PathStep::Field { .. }]
    ) {
        return Err(Hold::NotProjectedOutput);
    }
    let call = &member.fold.call;
    if output.source != member.member
        || output.terminal.lineage != SourceLineage::Exact(vec![call.clone()])
        || node.construction != call.construction
        || output.guards.get(&member.declaration.guard) != Some(&true)
        || member
            .requirements
            .guards
            .iter()
            .any(|(key, value)| output.guards.get(key) != Some(value))
    {
        return Err(Hold::Identity);
    }
    // These are conditional obligations. No model evaluation or default zero
    // substitutes for the consuming contract's exact projected-output node.
    if !member.requirements.zero.contains(&node)
        || !member
            .fold
            .internal
            .actions
            .iter()
            .any(|a| a.kind == "return-subtree" && a.zero_requirements.contains(&node))
    {
        return Err(Hold::MissingZero);
    }
    let current = super::fold_subtree::certify_metadata(
        facts,
        &member.declaration,
        &member.fold,
        aliases,
        slots,
    )
    .map_err(|_| Hold::Membership)?;
    if &current != member {
        return Err(Hold::Membership);
    }
    let required =
        super::fold_permission::requirements_metadata(facts, &member.fold, aliases, slots)
            .map_err(|_| Hold::Membership)?;
    if !required.zero.contains(&node) {
        return Err(Hold::MissingZero);
    }
    let transport = MatchedTransport::build_with_subtree_folds_metadata(
        facts,
        &[(member.declaration.guard, member.fold.clone())],
        std::slice::from_ref(member),
        aliases,
        slots,
    )
    .map_err(|_| Hold::Membership)?;
    let observed = transport
        .source_nodes(call.construction, &call.caller, &member.member)
        .into_iter()
        .flat_map(|source| transport.meets_for(source));
    if !observed.into_iter().any(|meet| &meet == output) {
        return Err(Hold::Identity);
    }
    let terminal = one(
        facts.terminals.iter().filter(|t| {
            t.point.construction == call.construction
                && t.ordinal == ordinal
                && t.point.function.as_ref() == Some(&call.callee)
        }),
        Hold::NotProjectedOutput,
    )?;
    if terminal.local != member.fold.internal.parameter
        || terminal.role != "parameter-output"
        || !matches!(&terminal.values, Present(values) if values.iter().any(|v|
            v.var == node.var && v.path == Present(descendant.path.clone())))
    {
        return Err(Hold::NotProjectedOutput);
    }
    if !member.fold.internal.actions.iter().any(|a| {
        a.kind == "return-subtree"
            && a.zero_requirements.contains(&node)
            && Some(a.block) == terminal.point.block
            && Some(a.statement) == terminal.point.statement
    }) {
        return Err(Hold::MissingZero);
    }
    let boundary = one(
        facts.boundary_substitutions.iter().filter(|b| {
            b.point == terminal.point
                && b.role == Role::ExitOutput
                && b.formal_local == Some(terminal.local)
        }),
        Hold::Boundary,
    )?;
    one(
        boundary.matched.iter().filter(|pair| {
            pair.actual == (Variables::Single { var: node.var })
                && pair.formal
                    == (Variables::Single {
                        var: descendant.formal_def,
                    })
        }),
        Hold::Boundary,
    )?;
    let equality = one(
        facts.equations.iter().filter(|e| {
            e.point == boundary.point
                && e.operation == "equal"
                && e.guard.is_none()
                && e.transfer.is_none()
                && e.variables == [node.var, descendant.formal_def]
                && e.validate().is_ok()
        }),
        Hold::Boundary,
    )?;
    Ok(ZeroOutput {
        source: member.member.clone(),
        call: call.clone(),
        guard: member.declaration.guard,
        output: output.clone(),
        required_zero: node,
        formal: Node {
            construction: call.construction,
            var: descendant.formal_def,
        },
        boundary: boundary.ordinal,
        equality: EquationId {
            construction: call.construction,
            ordinal: equality.ordinal,
        },
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
