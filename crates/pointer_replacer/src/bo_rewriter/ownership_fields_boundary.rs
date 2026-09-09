//! Local owning signatures and exact caller/formal contracts, over typed facts.
use std::collections::BTreeSet;

use super::{
    EvidenceKey, OwnerId, SiteId,
    emission::{Grant, GrantStatus, Kind, OwnCallFacts, OwnerType, admit_call},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundaryType {
    Owner(OwnerType),
    Borrow {
        pointee: String,
        mutable: bool,
        optional: bool,
        lifetime: String,
    },
    Scalar(String),
}
impl BoundaryType {
    pub fn render(&self) -> String {
        match self {
            Self::Owner(ty) => ty.render(),
            Self::Borrow {
                pointee,
                mutable,
                optional,
                lifetime,
            } => {
                let ty = format!(
                    "&'{lifetime} {}{pointee}",
                    if *mutable { "mut " } else { "" }
                );
                if *optional {
                    format!("Option<{ty}>")
                } else {
                    ty
                }
            }
            Self::Scalar(ty) => ty.clone(),
        }
    }
}
#[derive(Clone, Debug)]
pub struct SignatureSlot {
    pub key: EvidenceKey,
    pub ty: BoundaryType,
    pub grant: Option<Grant>,
    pub borrow_origin: Option<EvidenceKey>,
}
#[derive(Clone, Debug)]
pub struct Parameter {
    pub index: u32,
    pub name: String,
    pub slot: SignatureSlot,
}
#[derive(Clone, Debug)]
pub struct Signature {
    pub owner: OwnerId,
    pub parameters: Vec<Parameter>,
    pub result: SignatureSlot,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignaturePlan {
    pub owner: OwnerId,
    pub parameters: Vec<String>,
    pub result: String,
    pub lifetimes: Vec<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundaryHold {
    ParameterInventory,
    OwnerIdentity,
    Frame,
    Grant,
    BorrowOrigin,
    TargetSet,
    Type,
    Transfer,
    Call,
    DuplicateOwner,
    BorrowAcrossConsume,
}

fn validate_slot(
    slot: &SignatureSlot,
    owner: OwnerId,
    frame: EvidenceKey,
) -> Result<(), BoundaryHold> {
    if slot.key.site.owner != owner {
        return Err(BoundaryHold::OwnerIdentity);
    }
    if slot.key.model != frame.model || slot.key.configuration != frame.configuration {
        return Err(BoundaryHold::Frame);
    }
    let required_kind = match &slot.ty {
        BoundaryType::Owner(_) => Some(Kind::Owning),
        BoundaryType::Borrow { .. } => Some(Kind::Ref),
        BoundaryType::Scalar(_) => None,
    };
    if let Some(kind) = required_kind {
        let grant = slot.grant.as_ref().ok_or(BoundaryHold::Grant)?;
        if grant.key != slot.key
            || grant.kind != kind
            || grant.status != GrantStatus::Selected
            || grant.transport != Some(slot.key)
        {
            return Err(BoundaryHold::Grant);
        }
    }
    if matches!(slot.ty, BoundaryType::Borrow { .. }) && slot.borrow_origin != Some(slot.key) {
        return Err(BoundaryHold::BorrowOrigin);
    }
    Ok(())
}

pub fn plan_signature(signature: &Signature) -> Result<SignaturePlan, BoundaryHold> {
    validate_slot(&signature.result, signature.owner, signature.result.key)?;
    let mut parameters: Vec<_> = signature.parameters.iter().collect();
    parameters.sort_by_key(|p| p.index);
    let mut rendered = Vec::new();
    let mut lifetimes = BTreeSet::new();
    let mut names = BTreeSet::new();
    for (index, param) in parameters.iter().enumerate() {
        if param.index as usize != index || !names.insert(&param.name) {
            return Err(BoundaryHold::ParameterInventory);
        }
        validate_slot(&param.slot, signature.owner, signature.result.key)?;
        if let BoundaryType::Borrow { lifetime, .. } = &param.slot.ty {
            lifetimes.insert(lifetime.clone());
        }
        rendered.push(format!("mut {}: {}", param.name, param.slot.ty.render()));
    }
    if let BoundaryType::Borrow { lifetime, .. } = &signature.result.ty {
        lifetimes.insert(lifetime.clone());
    }
    Ok(SignaturePlan {
        owner: signature.owner,
        parameters: rendered,
        result: signature.result.ty.render(),
        lifetimes: lifetimes.into_iter().collect(),
    })
}

#[derive(Clone, Debug)]
pub enum PassingMode {
    Move,
    TakeOptionalStorage,
    BorrowShared,
    BorrowMutable,
    Scalar,
}
#[derive(Clone, Debug)]
pub struct ArgumentEdge {
    pub call_site: SiteId,
    pub index: u32,
    pub actual: EvidenceKey,
    pub formal: EvidenceKey,
    pub expression: String,
    pub source_type: BoundaryType,
    pub actual_grant: Option<Grant>,
    pub mode: PassingMode,
    pub transport: Option<(EvidenceKey, EvidenceKey)>,
    pub borrow_proof: Option<EvidenceKey>,
    pub exclusive_storage: bool,
    pub call_facts: Option<OwnCallFacts>,
}
#[derive(Clone, Debug)]
pub struct CallContract {
    pub site: SiteId,
    pub required_targets: BTreeSet<OwnerId>,
    pub targets: Vec<Signature>,
    pub arguments: Vec<ArgumentEdge>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallPlan {
    pub arguments: Vec<String>,
    pub consumed: Vec<EvidenceKey>,
    pub result_type: String,
}
pub fn plan_call(call: &CallContract) -> Result<CallPlan, BoundaryHold> {
    let targets: BTreeSet<_> = call.targets.iter().map(|s| s.owner).collect();
    if targets.is_empty() || targets != call.required_targets || targets.len() != call.targets.len()
    {
        return Err(BoundaryHold::TargetSet);
    }
    let mut output: Option<CallPlan> = None;
    let mut type_template: Option<Vec<BoundaryType>> = None;
    let mut actual_template: Option<Vec<(EvidenceKey, BoundaryType)>> = None;
    let frame = call.targets[0].result.key;
    let mut used_edges = BTreeSet::new();
    for target in &call.targets {
        if target.result.key.model != frame.model
            || target.result.key.configuration != frame.configuration
        {
            return Err(BoundaryHold::Frame);
        }
        let signature = plan_signature(target)?;
        let mut parameters: Vec<_> = target.parameters.iter().collect();
        parameters.sort_by_key(|p| p.index);
        let types: Vec<_> = parameters.iter().map(|p| p.slot.ty.clone()).collect();
        if let Some(previous) = &type_template {
            if previous != &types {
                return Err(BoundaryHold::TargetSet);
            }
        } else {
            type_template = Some(types);
        }
        let mut actuals = Vec::new();
        let mut arguments = Vec::new();
        let mut consumed = Vec::new();
        let mut borrowed = BTreeSet::new();
        let mut moved = BTreeSet::new();
        for param in parameters {
            let edges: Vec<_> = call
                .arguments
                .iter()
                .enumerate()
                .filter(|(_, e)| e.formal.site.owner == target.owner && e.index == param.index)
                .collect();
            let [(edge_index, edge)] = edges.as_slice() else {
                return Err(BoundaryHold::ParameterInventory);
            };
            used_edges.insert(*edge_index);
            if edge.call_site != call.site {
                return Err(BoundaryHold::Call);
            }
            actuals.push((edge.actual, edge.source_type.clone()));
            if edge.formal != param.slot.key
                || edge.transport != Some((edge.actual, edge.formal))
                || edge.actual.site.owner != call.site.owner
            {
                return Err(BoundaryHold::Transfer);
            }
            if edge.actual.model != edge.formal.model
                || edge.actual.configuration != edge.formal.configuration
                || edge.actual.generation != edge.formal.generation
            {
                return Err(BoundaryHold::Frame);
            }
            let code = match (&param.slot.ty, &edge.mode) {
                (BoundaryType::Owner(ty), PassingMode::Move | PassingMode::TakeOptionalStorage) => {
                    if edge.source_type != param.slot.ty {
                        return Err(BoundaryHold::Type);
                    }
                    let actual = edge.actual_grant.as_ref().ok_or(BoundaryHold::Grant)?;
                    if actual.key != edge.actual
                        || actual.kind != Kind::Owning
                        || actual.status != GrantStatus::Selected
                        || actual.transport != Some(edge.actual)
                    {
                        return Err(BoundaryHold::Grant);
                    }
                    if !moved.insert(edge.actual.generation) {
                        return Err(BoundaryHold::DuplicateOwner);
                    }
                    let facts = edge.call_facts.as_ref().ok_or(BoundaryHold::Call)?;
                    admit_call(actual, facts).map_err(|_| BoundaryHold::Call)?;
                    consumed.push(edge.actual);
                    if matches!(edge.mode, PassingMode::TakeOptionalStorage) {
                        if !ty.optional || !edge.exclusive_storage {
                            return Err(BoundaryHold::Type);
                        }
                        format!("({}).take()", edge.expression)
                    } else {
                        edge.expression.clone()
                    }
                }
                (
                    BoundaryType::Borrow {
                        pointee,
                        mutable,
                        optional,
                        ..
                    },
                    PassingMode::BorrowShared | PassingMode::BorrowMutable,
                ) => {
                    if *mutable != matches!(edge.mode, PassingMode::BorrowMutable)
                        || (*mutable && !edge.exclusive_storage)
                    {
                        return Err(BoundaryHold::Type);
                    }
                    let compatible = match &edge.source_type {
                        BoundaryType::Owner(source) => {
                            source.pointee == *pointee && source.optional == *optional
                        }
                        BoundaryType::Borrow {
                            pointee: p,
                            mutable: m,
                            optional: o,
                            ..
                        } => p == pointee && o == optional && (!*mutable || *m),
                        BoundaryType::Scalar(_) => false,
                    };
                    if !compatible {
                        return Err(BoundaryHold::Type);
                    }
                    if edge.borrow_proof != Some(edge.actual) {
                        return Err(BoundaryHold::BorrowOrigin);
                    }
                    borrowed.insert(edge.actual.generation);
                    if *optional {
                        format!(
                            "({}).{}()",
                            edge.expression,
                            if *mutable { "as_deref_mut" } else { "as_deref" }
                        )
                    } else {
                        format!(
                            "&{}*({})",
                            if *mutable { "mut " } else { "" },
                            edge.expression
                        )
                    }
                }
                (BoundaryType::Scalar(_), PassingMode::Scalar)
                    if edge.source_type == param.slot.ty =>
                {
                    edge.expression.clone()
                }
                _ => return Err(BoundaryHold::Type),
            };
            arguments.push(code);
        }
        if let Some(previous) = &actual_template {
            if previous != &actuals {
                return Err(BoundaryHold::TargetSet);
            }
        } else {
            actual_template = Some(actuals);
        }
        if moved.iter().any(|g| borrowed.contains(g)) {
            return Err(BoundaryHold::BorrowAcrossConsume);
        }
        let plan = CallPlan {
            arguments,
            consumed,
            result_type: signature.result,
        };
        if let Some(previous) = &output {
            if previous != &plan {
                return Err(BoundaryHold::TargetSet);
            }
        } else {
            output = Some(plan);
        }
    }
    if used_edges.len() != call.arguments.len() {
        return Err(BoundaryHold::ParameterInventory);
    }
    Ok(output.expect("nonempty target set checked"))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoistedCallPlan {
    pub binding: String,
    pub call: CallPlan,
}

pub fn plan_hoisted_call(
    call: &CallContract,
    witness: &super::hoist::HoistWitness,
    reserved: &BTreeSet<String>,
) -> Result<HoistedCallPlan, BoundaryHold> {
    let mut plan = plan_call(call)?;
    let target = call.targets.first().ok_or(BoundaryHold::TargetSet)?.owner;
    let mut edges: Vec<_> = call
        .arguments
        .iter()
        .filter(|edge| edge.formal.site.owner == target)
        .collect();
    edges.sort_by_key(|e| e.index);
    let mut arguments = Vec::new();
    for (edge, expression) in edges.iter().zip(&plan.arguments) {
        let argument = if edge.actual == witness.read {
            if !matches!(edge.mode, PassingMode::Scalar) {
                return Err(BoundaryHold::Type);
            }
            super::hoist::Argument::ScalarRead {
                key: edge.actual,
                expression: expression.clone(),
            }
        } else if edge.actual == witness.consume {
            if !matches!(
                edge.mode,
                PassingMode::Move | PassingMode::TakeOptionalStorage
            ) {
                return Err(BoundaryHold::Type);
            }
            super::hoist::Argument::Consume {
                key: edge.actual,
                expression: expression.clone(),
            }
        } else {
            super::hoist::Argument::Other {
                site: edge.actual.site,
                expression: expression.clone(),
            }
        };
        arguments.push(argument);
    }
    let hoisted = super::hoist::plan_scalar_hoist(call.site, &arguments, witness, reserved)
        .map_err(|_| BoundaryHold::Call)?;
    plan.arguments = hoisted.arguments;
    Ok(HoistedCallPlan {
        binding: hoisted.binding,
        call: plan,
    })
}

#[derive(Clone, Debug)]
pub struct ReturnEdge {
    pub source: SignatureSlot,
    pub result: SignatureSlot,
    pub expression: String,
    pub take_optional_storage: bool,
    pub exclusive_storage: bool,
    pub transport: Option<(EvidenceKey, EvidenceKey)>,
}
pub fn plan_return(edge: &ReturnEdge) -> Result<String, BoundaryHold> {
    if edge.transport != Some((edge.source.key, edge.result.key))
        || edge.source.key.site.owner != edge.result.key.site.owner
        || edge.source.key.generation != edge.result.key.generation
    {
        return Err(BoundaryHold::Transfer);
    }
    validate_slot(&edge.source, edge.result.key.site.owner, edge.result.key)?;
    validate_slot(&edge.result, edge.result.key.site.owner, edge.result.key)?;
    if edge.source.ty != edge.result.ty {
        return Err(BoundaryHold::Type);
    }
    let BoundaryType::Owner(ty) = &edge.result.ty else {
        return Err(BoundaryHold::Type);
    };
    let value = if edge.take_optional_storage {
        if !ty.optional || !edge.exclusive_storage {
            return Err(BoundaryHold::Type);
        }
        format!("({}).take()", edge.expression)
    } else {
        edge.expression.clone()
    };
    Ok(format!("return {value};"))
}
