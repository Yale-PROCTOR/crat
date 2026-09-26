//! Same-construction requirements of one conditional consuming call fold.
use std::collections::BTreeSet;

use super::{
    facts::{EquationId, Facts},
    fold_call::{FieldPremise, Proof},
    transport::Node,
};
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Requirements {
    pub(crate) kind_keys: Vec<String>,
    pub(crate) owning: Vec<Node>,
    pub(crate) zero: Vec<Node>,
    pub(crate) guards: Vec<(EquationId, bool)>,
}

pub(crate) fn requirements(facts: &Facts, proof: &Proof) -> Result<Requirements, String> {
    requirements_metadata(
        facts,
        proof,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}

pub(crate) fn requirements_metadata(
    facts: &Facts,
    proof: &Proof,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
    slot_keys: &BTreeSet<String>,
) -> Result<Requirements, String> {
    use super::super::{
        export::ProjKey, ownership_access::PlaceSyntax, ownership_occurrence::Availability::Present,
    };
    let call = &proof.call;
    if facts.constructions != 1 || call.construction != 0 || !proof.requires_consuming_root {
        return Err("fold construction/consuming premise missing".into());
    }
    let boundary = facts
        .boundary_substitutions
        .iter()
        .find(|b| b.point.construction == call.construction && b.ordinal == proof.boundary)
        .ok_or("fold argument boundary missing")?;
    let fields: BTreeSet<_> = proof
        .descendants
        .iter()
        .filter_map(|d| match &d.premise {
            FieldPremise::Owning { field } => Some(field.clone()),
            FieldPremise::Unused { .. } => None,
        })
        .collect();
    let rebuilt = super::fold_call::certify_metadata(
        facts,
        call,
        boundary
            .argument_index
            .ok_or("fold argument index missing")?,
        &fields,
        aliases,
    )
    .map_err(|e| format!("fold proof no longer qualifies: {e:?}"))?;
    if &rebuilt != proof {
        return Err("fold proof changed".into());
    }
    let actual = facts
        .consumes
        .iter()
        .find(|c| c.point.construction == call.construction && c.ordinal == proof.actual_consume)
        .ok_or("fold actual consume missing")?;
    let raw_head = |function: &str, local: u32| -> Result<String, String> {
        let rows: Vec<_> = facts
            .raw_pointer_heads
            .iter()
            .filter(|h| h.function == function && h.local == local)
            .collect();
        let [head] = rows.as_slice() else {
            return Err("fold raw head missing or ambiguous".into());
        };
        Ok(head.slot_key.clone())
    };
    let actual_key = if actual.projection.is_empty() {
        raw_head(&call.caller, actual.local)?
    } else {
        if !matches!(
            actual.projection.as_slice(),
            [ProjKey::Field(_)] | [ProjKey::Deref, ProjKey::Field(_)]
        ) {
            return Err("fold actual is not one direct cell".into());
        }
        let place = PlaceSyntax {
            local: actual.local,
            projection: actual.projection.clone(),
        };
        let loads: Vec<_> = facts
            .field_support_inputs
            .loads
            .iter()
            .filter(|l| {
                l.direct_projection
                    && !l.shared_reference_root
                    && l.site.function == call.caller
                    && Some(l.site.block) == actual.point.block
                    && Some(l.site.statement) == actual.point.statement
                    && l.site.place == place
            })
            .collect();
        let [load] = loads.as_slice() else {
            return Err("fold cell identity missing or ambiguous".into());
        };
        load.site.field_key.clone()
    };
    let receiver = facts
        .boundary_substitutions
        .iter()
        .find(|b| b.point.construction == call.construction && b.ordinal == proof.receiver_boundary)
        .ok_or("fold receiver boundary missing")?;
    let Present(id) = receiver.actual_occurrence else {
        return Err("fold receiver consume missing".into());
    };
    let receiver = facts
        .consumes
        .iter()
        .find(|c| c.point.construction == call.construction && c.ordinal == id)
        .ok_or("fold receiver local missing")?;
    if !receiver.projection.is_empty() {
        return Err("fold receiver projection unsupported".into());
    }
    let mut kind_keys = fields;
    kind_keys.insert(actual_key);
    kind_keys.insert(raw_head(
        &call.callee,
        boundary.formal_local.ok_or("fold formal missing")?,
    )?);
    kind_keys.insert(raw_head(&call.callee, 0)?);
    kind_keys.insert(raw_head(&call.caller, receiver.local)?);
    if kind_keys.iter().any(|key| !slot_keys.contains(key)) {
        return Err("fold kind key has no native slot".into());
    }
    let owning = BTreeSet::from([proof.actual_before, proof.receiver]);
    let mut zero: BTreeSet<_> = proof
        .internal
        .actions
        .iter()
        .flat_map(|a| a.zero_requirements.iter().copied())
        .collect();
    zero.insert(proof.actual_after);
    if owning.iter().chain(&zero).any(|n| n.construction != 0) || !owning.is_disjoint(&zero) {
        return Err("fold responsibility requirements conflict".into());
    }
    Ok(Requirements {
        kind_keys: kind_keys.into_iter().collect(),
        owning: owning.into_iter().collect(),
        zero: zero.into_iter().collect(),
        guards: proof.internal.required_guards.clone(),
    })
}
