//! One conditional outcome per observed fold; never selected-model evidence.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    facts::{EquationId, Facts},
    fold_caller::CallerProof,
    fold_declaration::Declaration,
};

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum Hold {
    Declaration,
    Call(super::fold_call::Error),
    Caller(super::fold_caller::Hold),
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Decision {
    pub(crate) declaration: Declaration,
    pub(crate) outcome: Result<CallerProof, Hold>,
}

/// A used-child declaration the identity certificate cannot admit, with its
/// member caller certificate. This is an APPENDED family: the `fold_callers`
/// decisions above are unchanged in name, order and bytes.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct MemberDecision {
    pub(crate) declaration: Declaration,
    /// R336-5: the admitted set, not one field. A member that uses two of its
    /// structure's pointer fields needs both, and which ones is what the rest
    /// of the chain has to carry.
    pub(crate) fields: BTreeSet<String>,
    pub(crate) outcome: Result<super::fold_member_caller::MemberCallerProof, Hold>,
}

pub(crate) fn member_plan(facts: &Facts) -> Option<Vec<MemberDecision>> {
    member_plan_metadata(
        facts,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}

pub(crate) fn member_plan_metadata(
    facts: &Facts,
    aliases: &BTreeMap<EquationId, EquationId>,
    slots: &BTreeSet<String>,
) -> Option<Vec<MemberDecision>> {
    let declarations = facts.fold_declarations.as_ref()?;
    let valid = super::fold_declaration::validate(facts, aliases).is_ok();
    let mut rows = Vec::new();
    for declaration in declarations {
        // Only a declaration the identity certificate refuses *because* the
        // callee uses the descendant field enters this family. Every other
        // refusal stays exactly where it was.
        let Err(super::fold_call::Error::FieldScheme(field)) = super::fold_call::certify_metadata(
            facts,
            &declaration.call,
            declaration.argument,
            &BTreeSet::new(),
            aliases,
        ) else {
            continue;
        };
        // R336-5: admit the refused field and ask again. A re-run that refuses
        // ANOTHER registered pointer field of the same structure is the same
        // member needing a wider set, so admit that too; anything else — a
        // field of a different structure, or any other refusal — is the answer.
        // The set only grows and is bounded by the structure's registered
        // fields, so this terminates.
        let structure = field.split("::").next().unwrap_or_default().to_owned();
        let mut fields: BTreeSet<String> = std::iter::once(field).collect();
        let outcome = if !valid {
            Err(Hold::Declaration)
        } else {
            loop {
                let attempt = super::fold_call::certify_metadata(
                    facts,
                    &declaration.call,
                    declaration.argument,
                    &fields,
                    aliases,
                );
                if let Err(super::fold_call::Error::FieldScheme(wider)) = &attempt
                    && wider.split("::").next() == Some(structure.as_str())
                    && facts.field_support_inputs.fields.contains(wider)
                    && !fields.contains(wider)
                {
                    fields.insert(wider.clone());
                    continue;
                }
                break attempt.map_err(Hold::Call).and_then(|fold| {
                    super::fold_member_caller::certify_metadata(
                        facts,
                        declaration,
                        &fold,
                        aliases,
                        slots,
                    )
                    .map_err(Hold::Caller)
                });
            }
        };
        rows.push(MemberDecision {
            declaration: declaration.clone(),
            fields,
            outcome,
        });
    }
    Some(rows)
}

pub(crate) fn plan(facts: &Facts) -> Option<Vec<Decision>> {
    plan_metadata(
        facts,
        &super::matched::guard_aliases(&facts.guards),
        &facts.slot_refs.keys().cloned().collect(),
    )
}
pub(crate) fn plan_metadata(
    facts: &Facts,
    aliases: &BTreeMap<EquationId, EquationId>,
    slots: &BTreeSet<String>,
) -> Option<Vec<Decision>> {
    let declarations = facts.fold_declarations.as_ref()?;
    let valid = super::fold_declaration::validate(facts, aliases).is_ok();
    Some(
        declarations
            .iter()
            .map(|declaration| {
                let outcome = if !valid {
                    Err(Hold::Declaration)
                } else {
                    // Initial caller certificate admits only the unchanged, unused
                    // descendant. Used-field premises need their later caller scope.
                    super::fold_call::certify_metadata(
                        facts,
                        &declaration.call,
                        declaration.argument,
                        &BTreeSet::new(),
                        aliases,
                    )
                    .map_err(Hold::Call)
                    .and_then(|fold| {
                        super::fold_caller::certify_metadata(
                            facts,
                            declaration,
                            &fold,
                            aliases,
                            slots,
                        )
                        .map_err(Hold::Caller)
                    })
                };
                Decision {
                    declaration: declaration.clone(),
                    outcome,
                }
            })
            .collect(),
    )
}
