//! Conditional discharge of a traversal's zero-owning return alternative.
//! The original free remains the terminal; this creates no endpoint or grant.

use serde::{Deserialize, Serialize};

use super::{
    facts::Facts,
    matched::{Meet, SourceLineage, TerminalTarget},
    traversal_call, traversal_correspondence,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Discharge {
    pub(crate) output: Meet,
    pub(crate) proof: traversal_correspondence::Proof,
}

pub(crate) fn certify(
    facts: &Facts,
    output: &Meet,
    chosen_free: &Meet,
    aliases: &std::collections::BTreeMap<super::facts::EquationId, super::facts::EquationId>,
) -> Option<Discharge> {
    if output.source != chosen_free.source
        || !matches!(output.source.lineage, SourceLineage::Exact(_))
        || !matches!(chosen_free.terminal.target, TerminalTarget::Free(_))
    {
        return None;
    }
    let TerminalTarget::Output { node, ordinal } = output.terminal.target else {
        return None;
    };
    let SourceLineage::Exact(path) = &output.terminal.lineage else { return None };
    let [call] = path.as_slice() else { return None };
    let candidates = traversal_call::discover_metadata(facts, aliases);
    let mut matching = candidates
        .iter()
        .filter(|candidate| &candidate.call == call);
    let candidate = matching.next()?;
    if matching.next().is_some() {
        return None;
    }
    let proof = traversal_correspondence::certify_metadata(facts, candidate, aliases).ok()?;
    if !proof.traversal.returned.contains(&node)
        || chosen_free.guards.get(&candidate.guard) != Some(&true)
        || output.guards.get(&candidate.guard) != Some(&false)
    {
        return None;
    }
    // The named Output must be this callee's real return component, not a
    // different output which happens to carry the same ownership variable.
    let mut terminals = facts.terminals.iter().filter(|terminal| {
        terminal.point.construction == node.construction
            && terminal.ordinal == ordinal
            && terminal.point.function.as_ref() == Some(&call.callee)
            && terminal.role == "return-output"
            && matches!(&terminal.values,
                super::super::ownership_occurrence::Availability::Present(values)
                    if values.iter().any(|value| value.var == node.var))
    });
    terminals.next()?;
    if terminals.next().is_some()
        || output.guards.iter().any(|(guard, value)| {
            *guard != candidate.guard
                && chosen_free
                    .guards
                    .get(guard)
                    .is_some_and(|other| other != value)
        })
    {
        return None;
    }
    Some(Discharge {
        output: output.clone(),
        proof,
    })
}
