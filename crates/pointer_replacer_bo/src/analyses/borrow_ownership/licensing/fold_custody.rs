//! Same-model values for conditional folded caller obligations.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    facts::{EquationId, Facts},
    transport::Node,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Values {
    pub(crate) ownership: Vec<(Node, bool)>,
    pub(crate) guards: Vec<(EquationId, bool)>,
}
fn required(
    rows: &[super::fold_eligibility::Decision],
    members: &[super::fold_eligibility::MemberDecision],
) -> (BTreeSet<Node>, BTreeSet<EquationId>) {
    let mut nodes = BTreeSet::new();
    let mut guards = BTreeSet::new();
    let identity = rows
        .iter()
        .filter_map(|row| row.outcome.as_ref().ok())
        .map(|proof| &proof.requirements);
    let member = members
        .iter()
        .filter_map(|row| row.outcome.as_ref().ok())
        .map(|proof| &proof.requirements);
    for requirements in identity.chain(member) {
        nodes.extend(
            requirements
                .owning
                .iter()
                .chain(&requirements.zero)
                .copied(),
        );
        guards.extend(requirements.guards.iter().map(|(key, _)| *key));
    }
    (nodes, guards)
}

pub(crate) fn capture(
    facts: &Facts,
    evaluate: &mut impl FnMut(&z3::ast::Bool) -> Option<bool>,
) -> Option<Values> {
    let licensing = facts.licensing.as_ref()?;
    let rows = licensing.fold_callers.as_deref()?;
    let (nodes, guards) = required(rows, licensing.fold_members.as_deref().unwrap_or_default());
    let ownership = nodes
        .into_iter()
        .filter_map(|node| {
            (facts.constructions == 1 && node.construction == 0).then_some(())?;
            let ast = facts
                .ownership_asts
                .get(super::super::ssa::constraint::Var::from_u32(node.var))?;
            evaluate(ast).map(|value| (node, value))
        })
        .collect();
    let guards = guards
        .into_iter()
        .filter_map(|key| {
            let mut rows = facts.guards.iter().filter(|row| row.equation == key);
            let row = rows.next()?;
            if rows.next().is_some() {
                return None;
            }
            evaluate(&row.predicate).map(|value| (key, value))
        })
        .collect();
    Some(Values { ownership, guards })
}

pub(crate) fn validate(
    snapshot: &super::snapshot::Snapshot,
    accepted: &super::stack_export::Accepted,
    model: &BTreeMap<String, String>,
) -> Result<(), String> {
    let facts = snapshot.metadata.facts();
    let current = super::fold_eligibility::plan_metadata(
        &facts,
        &snapshot.metadata.guard_aliases.iter().copied().collect(),
        &snapshot.metadata.slot_keys.iter().cloned().collect(),
    );
    if current != snapshot.fold_callers {
        return Err("fold custody eligibility differs".into());
    }
    let members = super::fold_eligibility::member_plan_metadata(
        &facts,
        &snapshot.metadata.guard_aliases.iter().copied().collect(),
        &snapshot.metadata.slot_keys.iter().cloned().collect(),
    );
    if members != snapshot.fold_members {
        return Err("fold custody member eligibility differs".into());
    }
    let Some(rows) = &current else {
        return if accepted.fold_values.is_none() {
            Ok(())
        } else {
            Err("fold custody availability differs".into())
        };
    };
    let values = accepted
        .fold_values
        .as_ref()
        .ok_or("fold custody availability differs")?;
    let ownership: BTreeMap<_, _> = values.ownership.iter().copied().collect();
    let guards: BTreeMap<_, _> = values.guards.iter().copied().collect();
    let (nodes, keys) = required(rows, members.as_deref().unwrap_or_default());
    if ownership.len() != values.ownership.len()
        || ownership.keys().copied().collect::<BTreeSet<_>>() != nodes
    {
        return Err("fold ownership valuation coverage differs".into());
    }
    if guards.len() != values.guards.len()
        || guards.keys().copied().collect::<BTreeSet<_>>() != keys
    {
        return Err("fold guard valuation coverage differs".into());
    }
    let selections: BTreeMap<_, _> = accepted
        .fold_guards
        .as_deref()
        .unwrap_or_default()
        .iter()
        .copied()
        .collect();
    if guards.iter().any(|(key, value)| {
        selections
            .get(key)
            .is_some_and(|selected| selected != value)
    }) {
        return Err("fold predicate custody disagrees with selection".into());
    }
    if accepted.closed_call_world != snapshot.metadata.frame_attested {
        return Err("selected fold lacks closed caller frame".into());
    }
    for row in rows {
        if snapshot.metadata.frame_attested
            && let Ok(proof) = &row.outcome
        {
            let endpoints = [
                proof.payload.source.endpoint,
                proof.payload.free,
                proof.container.source.endpoint,
                proof.container.free,
            ];
            if endpoints.iter().all(|key| guards.get(key) == Some(&true))
                && selections.get(&row.declaration.guard) != Some(&true)
            {
                return Err("fold original endpoints lack selected guard".into());
            }
        }
        if selections.get(&row.declaration.guard) != Some(&true) {
            continue;
        }
        let proof = row
            .outcome
            .as_ref()
            .map_err(|_| "pending fold selected without closure")?;
        if !accepted.closed_call_world
            || !snapshot.metadata.frame_attested
            || !proof.required_closed_frame
        {
            return Err("selected fold lacks closed caller frame".into());
        }
        if proof
            .requirements
            .kind_keys
            .iter()
            .any(|key| model.get(key).map(String::as_str) != Some("owning"))
        {
            return Err("selected fold kind differs".into());
        }
        if proof
            .requirements
            .owning
            .iter()
            .any(|n| ownership.get(n) != Some(&true))
            || proof
                .requirements
                .zero
                .iter()
                .any(|n| ownership.get(n) != Some(&false))
        {
            return Err("selected fold responsibility differs".into());
        }
        if proof
            .requirements
            .guards
            .iter()
            .any(|(k, v)| guards.get(k) != Some(v))
        {
            return Err("selected fold endpoint or law guard differs".into());
        }
    }
    Ok(())
}
