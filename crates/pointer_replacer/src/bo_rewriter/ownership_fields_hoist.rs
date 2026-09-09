//! P2d scalar-read planning over a resolved argument list.
use std::collections::BTreeSet;

use super::{EvidenceKey, SiteId};

#[derive(Clone, Debug)]
pub enum Argument {
    ScalarRead {
        key: EvidenceKey,
        expression: String,
    },
    Consume {
        key: EvidenceKey,
        expression: String,
    },
    Other {
        site: SiteId,
        expression: String,
    },
}
impl Argument {
    pub fn expression(&self) -> &str {
        match self {
            Self::ScalarRead { expression, .. }
            | Self::Consume { expression, .. }
            | Self::Other { expression, .. } => expression,
        }
    }

    pub fn site(&self) -> SiteId {
        match self {
            Self::ScalarRead { key, .. } | Self::Consume { key, .. } => key.site,
            Self::Other { site, .. } => *site,
        }
    }
}

/// Evidence is tied to the entire original argument order. No missing
/// commutation edge, trapping projection or active independent protector may
/// be converted to a positive fact by this mechanical consumer.
#[derive(Clone, Debug)]
pub struct HoistWitness {
    pub call: SiteId,
    pub read: EvidenceKey,
    pub consume: EvidenceKey,
    pub original_order: Vec<SiteId>,
    pub scalar_effect_free_nontrapping: bool,
    pub callee_commutes: bool,
    pub commutes_with: BTreeSet<SiteId>,
    pub no_independent_protector: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoistPlan {
    pub binding: String,
    pub arguments: Vec<String>,
    pub read: EvidenceKey,
    pub consume: EvidenceKey,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HoistHold {
    MissingOccurrence,
    DuplicateOccurrence,
    StaleOrder,
    WrongFlow,
    EffectfulRead,
    CalleeOrder,
    InterveningEffect(SiteId),
    Protector,
}

pub fn plan_scalar_hoist(
    call: SiteId,
    args: &[Argument],
    witness: &HoistWitness,
    reserved_names: &BTreeSet<String>,
) -> Result<HoistPlan, HoistHold> {
    let order: Vec<_> = args.iter().map(Argument::site).collect();
    if order.iter().copied().collect::<BTreeSet<_>>().len() != order.len() {
        return Err(HoistHold::DuplicateOccurrence);
    }
    if call != witness.call || order != witness.original_order {
        return Err(HoistHold::StaleOrder);
    }
    let read = args
        .iter()
        .position(|arg| matches!(arg, Argument::ScalarRead { key, .. } if *key == witness.read))
        .ok_or(HoistHold::MissingOccurrence)?;
    let consume = args
        .iter()
        .position(|arg| matches!(arg, Argument::Consume { key, .. } if *key == witness.consume))
        .ok_or(HoistHold::MissingOccurrence)?;
    if consume >= read
        || witness.read.model != witness.consume.model
        || witness.read.configuration != witness.consume.configuration
        || witness.read.generation != witness.consume.generation
        || witness.read.site.owner != call.owner
        || witness.consume.site.owner != call.owner
    {
        return Err(HoistHold::WrongFlow);
    }
    if !witness.scalar_effect_free_nontrapping {
        return Err(HoistHold::EffectfulRead);
    }
    if !witness.no_independent_protector {
        return Err(HoistHold::Protector);
    }
    if !witness.callee_commutes {
        return Err(HoistHold::CalleeOrder);
    }
    // The binding precedes the entire argument list, not only the consume:
    // every crossed evaluation requires its own commutation fact.
    for site in &order[..read] {
        if !witness.commutes_with.contains(site) {
            return Err(HoistHold::InterveningEffect(*site));
        }
    }
    let mut name = "__crat_scalar".to_owned();
    let mut suffix = 0;
    while reserved_names.contains(&name) {
        suffix += 1;
        name = format!("__crat_scalar_{suffix}");
    }
    let binding = format!("let {name} = {};", args[read].expression());
    let mut arguments: Vec<_> = args.iter().map(|arg| arg.expression().to_owned()).collect();
    arguments[read] = name;
    Ok(HoistPlan {
        binding,
        arguments,
        read: witness.read,
        consume: witness.consume,
    })
}
