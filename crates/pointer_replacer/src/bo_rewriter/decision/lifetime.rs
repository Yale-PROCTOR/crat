//! E2-FN lifetime planning.
//!
//! This module is the sole rewriter-side consumer of the intact NB5-O
//! [`OriginSummaries`] carrier for lifetime semantics.  It starts with the
//! carrier-shape witness; eligibility, SCC planning, and emission receipts are
//! filled by the subsequent RED-first steps.

use std::collections::{BTreeMap, BTreeSet};

use crate::analyses::borrow_ownership::origin_summary::{
    OriginSlot, OriginSummaries, OriginSummary, SignatureRoot, SignatureSlot,
};

/// The minimal E2-X1 observation used to prove that the carrier reaches this
/// module without an A5-specific projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CarrierReceipt {
    pub(crate) summary_count: usize,
    pub(crate) native_flows: bool,
}

pub(crate) fn carrier_receipt(origins: Option<&OriginSummaries>) -> CarrierReceipt {
    CarrierReceipt {
        summary_count: origins.map_or(0, |origins| origins.len()),
        native_flows: origins.is_some_and(|origins| origins.try_native_flows().is_some()),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FnSignatureRoot {
    Arg(u32),
    Return,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FnSignatureSlot {
    pub(crate) root: FnSignatureRoot,
    pub(crate) deref_depth: u8,
    pub(crate) depth: u8,
}

impl FnSignatureSlot {
    pub(crate) const RETURN: Self = Self {
        root: FnSignatureRoot::Return,
        deref_depth: 0,
        depth: 0,
    };

    pub(crate) fn arg(index: usize, deref_depth: u8, depth: u8) -> Self {
        Self {
            root: FnSignatureRoot::Arg(u32::try_from(index).expect("argument index fits u32")),
            deref_depth,
            depth,
        }
    }

    fn from_summary(slot: SignatureSlot) -> Result<Self, LifetimeFailure> {
        if slot.place.field.is_some() {
            return Err(LifetimeFailure::FieldHeld);
        }
        Ok(Self {
            root: match slot.place.root {
                SignatureRoot::Arg(local) => FnSignatureRoot::Arg(local.as_u32()),
                SignatureRoot::Return => FnSignatureRoot::Return,
            },
            deref_depth: slot.place.deref_depth,
            depth: slot.depth,
        })
    }

    fn needs_modeled_source(self) -> bool {
        matches!(self.root, FnSignatureRoot::Return)
            || matches!(self.root, FnSignatureRoot::Arg(_)) && self.deref_depth > 0
    }

    fn receipt_key(self) -> String {
        match self.root {
            FnSignatureRoot::Arg(index) => {
                format!("arg{index}/deref{}/depth{}", self.deref_depth, self.depth)
            }
            FnSignatureRoot::Return => {
                format!("return/deref{}/depth{}", self.deref_depth, self.depth)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LifetimeFailure {
    OriginUnknown,
    OriginAbsent,
    OriginConflict,
    FieldHeld,
    ExternalContractAbsent,
    FnPtrWebHeld,
    AstUnplaceable,
    SeamIncompatible,
}

impl LifetimeFailure {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::OriginUnknown => "lifetime-origin-unknown",
            Self::OriginAbsent => "lifetime-origin-absent",
            Self::OriginConflict => "lifetime-origin-conflict",
            Self::FieldHeld => "lifetime-field-held",
            Self::ExternalContractAbsent => "lifetime-external-contract-absent",
            Self::FnPtrWebHeld => "lifetime-fnptr-web-held",
            Self::AstUnplaceable => "lifetime-ast-unplaceable",
            Self::SeamIncompatible => "lifetime-seam-incompatible",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FunctionPlan {
    lifetimes: BTreeMap<FnSignatureSlot, String>,
    pub(crate) sccs: Vec<Vec<FnSignatureSlot>>,
    pub(crate) outlives: Vec<(String, String)>,
}

impl FunctionPlan {
    pub(crate) fn lifetime_for(&self, slot: FnSignatureSlot) -> Option<&str> {
        self.lifetimes.get(&slot).map(String::as_str)
    }

    pub(crate) fn receipt(&self) -> String {
        let mut rows = Vec::new();
        for (slot, lifetime) in &self.lifetimes {
            rows.push(format!("slot\t{}\t{lifetime}", slot.receipt_key()));
        }
        for (longer, shorter) in &self.outlives {
            rows.push(format!("outlives\t{longer}\t{shorter}"));
        }
        rows.join("\n")
    }
}

fn next_lifetime_name(used: &mut BTreeSet<String>) -> String {
    for byte in b'a'..=b'z' {
        let name = char::from(byte).to_string();
        if used.insert(name.clone()) {
            return name;
        }
    }
    let mut index = 0usize;
    loop {
        let name = format!("lt{index}");
        if used.insert(name.clone()) {
            return name;
        }
        index += 1;
    }
}

pub(crate) fn plan_function(
    summary: &OriginSummary,
    required: &[OriginSlot],
    existing_names: &BTreeSet<String>,
) -> Result<FunctionPlan, LifetimeFailure> {
    if required.is_empty() {
        return Err(LifetimeFailure::OriginAbsent);
    }

    let mut by_key = BTreeMap::<FnSignatureSlot, OriginSlot>::new();
    for &origin_slot in required {
        let Some(&signature_slot) = summary.slots.get(origin_slot) else {
            return Err(LifetimeFailure::OriginConflict);
        };
        let key = FnSignatureSlot::from_summary(signature_slot)?;
        if by_key.insert(key, origin_slot).is_some() {
            return Err(LifetimeFailure::OriginConflict);
        }
        if summary.unknown.contains(origin_slot) {
            return Err(LifetimeFailure::OriginUnknown);
        }
    }

    for (&target_key, &target) in &by_key {
        if target_key.needs_modeled_source()
            && !by_key
                .values()
                .copied()
                .any(|source| source != target && summary.subset.contains(source, target))
        {
            return Err(LifetimeFailure::OriginAbsent);
        }
    }

    let mut unassigned = by_key.clone();
    let mut groups = Vec::<Vec<(FnSignatureSlot, OriginSlot)>>::new();
    while let Some((&seed_key, &seed)) = unassigned.first_key_value() {
        let mut group = vec![(seed_key, seed)];
        unassigned.remove(&seed_key);
        let peers = unassigned
            .iter()
            .filter_map(|(&key, &slot)| {
                (summary.subset.contains(seed, slot) && summary.subset.contains(slot, seed))
                    .then_some((key, slot))
            })
            .collect::<Vec<_>>();
        for (key, slot) in peers {
            unassigned.remove(&key);
            group.push((key, slot));
        }
        group.sort_by_key(|(key, _)| *key);
        groups.push(group);
    }
    groups.sort_by_key(|group| group[0].0);

    let mut used = existing_names
        .iter()
        .map(|name| name.trim_start_matches('\'').to_owned())
        .collect::<BTreeSet<_>>();
    let mut lifetimes = BTreeMap::new();
    let mut group_names = Vec::new();
    for group in &groups {
        let name = next_lifetime_name(&mut used);
        for &(key, _) in group {
            lifetimes.insert(key, name.clone());
        }
        group_names.push(name);
    }

    let mut outlives = BTreeSet::new();
    for (source_index, source_group) in groups.iter().enumerate() {
        for (target_index, target_group) in groups.iter().enumerate() {
            if source_index == target_index {
                continue;
            }
            let flows = source_group.iter().any(|(_, source)| {
                target_group
                    .iter()
                    .any(|(_, target)| summary.subset.contains(*source, *target))
            });
            if flows {
                outlives.insert((
                    group_names[source_index].clone(),
                    group_names[target_index].clone(),
                ));
            }
        }
    }

    Ok(FunctionPlan {
        lifetimes,
        sccs: groups
            .into_iter()
            .map(|group| group.into_iter().map(|(key, _)| key).collect())
            .collect(),
        outlives: outlives.into_iter().collect(),
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use rustc_index::{
        IndexVec,
        bit_set::{DenseBitSet, SparseBitMatrix},
    };
    use rustc_middle::mir::Local;

    use super::*;
    use crate::analyses::borrow_ownership::origin_summary::{
        OriginSlot, OriginSummary, SignaturePlace, SignatureRoot, SignatureSlot,
    };

    fn arg(index: usize) -> SignatureSlot {
        SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Arg(Local::from_usize(index)),
                deref_depth: 0,
                field: None,
            },
            depth: 0,
        }
    }

    fn ret() -> SignatureSlot {
        SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Return,
                deref_depth: 0,
                field: None,
            },
            depth: 0,
        }
    }

    fn summary(
        slots: Vec<SignatureSlot>,
        edges: &[(usize, usize)],
        unknowns: &[usize],
    ) -> OriginSummary {
        let mut subset = SparseBitMatrix::new(slots.len());
        for &(source, target) in edges {
            subset.insert(
                OriginSlot::from_usize(source),
                OriginSlot::from_usize(target),
            );
        }
        let mut unknown = DenseBitSet::new_empty(slots.len());
        for &slot in unknowns {
            unknown.insert(OriginSlot::from_usize(slot));
        }
        OriginSummary {
            slots: IndexVec::from_raw(slots),
            subset,
            unknown,
        }
    }

    #[test]
    fn e2_w1_arg_return_shares_one_lifetime_relation() {
        let summary = summary(vec![arg(1), ret()], &[(0, 1)], &[]);
        let plan = plan_function(
            &summary,
            &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
            &BTreeSet::new(),
        )
        .expect("modeled input-to-return plan");

        assert_eq!(plan.lifetime_for(FnSignatureSlot::arg(1, 0, 0)), Some("a"));
        assert_eq!(plan.lifetime_for(FnSignatureSlot::RETURN), Some("b"));
        assert_eq!(plan.outlives, vec![("a".to_owned(), "b".to_owned())]);
    }

    #[test]
    fn e2_w2_multi_source_return_emits_ordered_outlives() {
        let summary = summary(vec![arg(1), arg(2), ret()], &[(0, 2), (1, 2)], &[]);
        let required = [
            OriginSlot::from_usize(2),
            OriginSlot::from_usize(0),
            OriginSlot::from_usize(1),
        ];
        let plan =
            plan_function(&summary, &required, &BTreeSet::new()).expect("multi-source return plan");

        assert_eq!(
            plan.outlives,
            vec![
                ("a".to_owned(), "c".to_owned()),
                ("b".to_owned(), "c".to_owned()),
            ]
        );
        assert_eq!(plan.sccs.len(), 3);
    }

    #[test]
    fn e2_w5_existing_names_and_input_order_do_not_change_plan_bytes() {
        let summary = summary(vec![arg(1), ret()], &[(0, 1)], &[]);
        let existing = BTreeSet::from(["a".to_owned(), "b".to_owned()]);
        let forward = plan_function(
            &summary,
            &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
            &existing,
        )
        .expect("forward plan");
        let reverse = plan_function(
            &summary,
            &[OriginSlot::from_usize(1), OriginSlot::from_usize(0)],
            &existing,
        )
        .expect("reverse plan");

        assert_eq!(forward.receipt(), reverse.receipt());
        assert_eq!(
            forward.lifetime_for(FnSignatureSlot::arg(1, 0, 0)),
            Some("c")
        );
        assert_eq!(forward.lifetime_for(FnSignatureSlot::RETURN), Some("d"));
    }

    #[test]
    fn e2_n1_unknown_origin_is_a_mandatory_veto() {
        let summary = summary(vec![arg(1), ret()], &[(0, 1)], &[1]);
        assert_eq!(
            plan_function(
                &summary,
                &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
                &BTreeSet::new(),
            ),
            Err(LifetimeFailure::OriginUnknown)
        );
    }

    #[test]
    fn e2_n2_return_without_a_modeled_source_is_absent() {
        let summary = summary(vec![arg(1), ret()], &[], &[]);
        assert_eq!(
            plan_function(
                &summary,
                &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
                &BTreeSet::new(),
            ),
            Err(LifetimeFailure::OriginAbsent)
        );
    }
}
