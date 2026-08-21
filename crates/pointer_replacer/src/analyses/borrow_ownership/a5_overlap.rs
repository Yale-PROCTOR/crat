//! Pure domain for A5 parameter may-overlap summaries.

use std::collections::{BTreeMap, BTreeSet};

use super::l2::{FnKey, MirLocationKey, SlotKey};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ParamPair {
    first: u32,
    second: u32,
}

impl ParamPair {
    pub(crate) fn new(left: u32, right: u32) -> Option<Self> {
        (left != right).then(|| Self {
            first: left.min(right),
            second: left.max(right),
        })
    }

    pub(crate) fn first(self) -> u32 {
        self.first
    }

    pub(crate) fn second(self) -> u32 {
        self.second
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct FunctionPairKey {
    function: FnKey,
    params: ParamPair,
}

impl FunctionPairKey {
    pub(crate) fn new(function: FnKey, left: u32, right: u32) -> Option<Self> {
        Some(Self {
            function,
            params: ParamPair::new(left, right)?,
        })
    }

    pub(crate) fn function(self) -> FnKey {
        self.function
    }

    pub(crate) fn params(self) -> ParamPair {
        self.params
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct CallSiteWitnessKey {
    pair: FunctionPairKey,
    caller: FnKey,
    location: MirLocationKey,
    actuals: (SlotKey, SlotKey),
}

impl CallSiteWitnessKey {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        callee: FnKey,
        left_param: u32,
        left_actual: SlotKey,
        right_param: u32,
        right_actual: SlotKey,
        caller: FnKey,
        location: MirLocationKey,
    ) -> Option<Self> {
        let pair = FunctionPairKey::new(callee, left_param, right_param)?;
        let actuals = if left_param < right_param {
            (left_actual, right_actual)
        } else {
            (right_actual, left_actual)
        };
        Some(Self {
            pair,
            caller,
            location,
            actuals,
        })
    }

    pub(crate) fn pair(self) -> FunctionPairKey {
        self.pair
    }

    pub(crate) fn actuals(self) -> (SlotKey, SlotKey) {
        self.actuals
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct MayOverlapSummary {
    witnesses: BTreeMap<FunctionPairKey, BTreeSet<CallSiteWitnessKey>>,
}

impl MayOverlapSummary {
    pub(crate) fn insert(&mut self, witness: CallSiteWitnessKey) -> bool {
        self.witnesses
            .entry(witness.pair())
            .or_default()
            .insert(witness)
    }

    pub(crate) fn union_from(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for witnesses in other.witnesses.values() {
            for &witness in witnesses {
                changed |= self.insert(witness);
            }
        }
        changed
    }

    pub(crate) fn witnesses(&self, pair: FunctionPairKey) -> &BTreeSet<CallSiteWitnessKey> {
        self.witnesses
            .get(&pair)
            .expect("may-overlap pair must have at least one witness")
    }

    pub(crate) fn ordered_rows(&self) -> Vec<(FunctionPairKey, CallSiteWitnessKey)> {
        self.witnesses
            .iter()
            .flat_map(|(&pair, witnesses)| {
                witnesses
                    .iter()
                    .copied()
                    .map(move |witness| (pair, witness))
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SetPairEvidence<T> {
    Unknown,
    Complete {
        left: BTreeSet<T>,
        right: BTreeSet<T>,
    },
    Incomplete {
        left: BTreeSet<T>,
        right: BTreeSet<T>,
    },
}

impl<T> Default for SetPairEvidence<T> {
    fn default() -> Self {
        Self::Unknown
    }
}

impl<T: Ord> SetPairEvidence<T> {
    pub(crate) fn proves_disjoint(&self) -> bool {
        let Self::Complete { left, right } = self else {
            return false;
        };
        !left.is_empty() && !right.is_empty() && left.is_disjoint(right)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PairFacts<T> {
    pub(crate) storage_alias: bool,
    pub(crate) projection_disjoint: bool,
    pub(crate) origins: SetPairEvidence<T>,
    pub(crate) points_to: SetPairEvidence<T>,
}

impl<T> Default for PairFacts<T> {
    fn default() -> Self {
        Self {
            storage_alias: false,
            projection_disjoint: false,
            origins: SetPairEvidence::Unknown,
            points_to: SetPairEvidence::Unknown,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PairClass {
    ProvenDisjoint,
    NotProvenDisjoint,
}

pub(crate) fn classify_pair<T: Ord>(facts: &PairFacts<T>) -> PairClass {
    if facts.storage_alias {
        return PairClass::NotProvenDisjoint;
    }
    if facts.projection_disjoint
        || facts.origins.proves_disjoint()
        || facts.points_to.proves_disjoint()
    {
        PairClass::ProvenDisjoint
    } else {
        PairClass::NotProvenDisjoint
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn slot(owner: u32, slot: usize) -> SlotKey {
        SlotKey {
            variant: 1,
            owner,
            slot,
        }
    }

    fn witness(
        callee: u32,
        caller: u32,
        block: u32,
        left_param: u32,
        left_actual: SlotKey,
        right_param: u32,
        right_actual: SlotKey,
    ) -> CallSiteWitnessKey {
        CallSiteWitnessKey::new(
            callee,
            left_param,
            left_actual,
            right_param,
            right_actual,
            caller,
            MirLocationKey::new(block, 0),
        )
        .expect("distinct formal parameters")
    }

    #[test]
    fn parameter_pair_keys_are_unordered_and_reject_self_pairs() {
        let forward = ParamPair::new(2, 5).expect("distinct pair");
        let reverse = ParamPair::new(5, 2).expect("distinct pair");

        assert_eq!(forward, reverse);
        assert_eq!((forward.first(), forward.second()), (2, 5));
        assert_eq!(ParamPair::new(3, 3), None);
    }

    #[test]
    fn witness_keys_canonicalize_formals_and_actual_correspondence() {
        let left = slot(10, 2);
        let right = slot(10, 7);
        let forward = witness(8, 3, 4, 1, left, 6, right);
        let reverse = witness(8, 3, 4, 6, right, 1, left);

        assert_eq!(forward, reverse);
        assert_eq!(forward.pair(), FunctionPairKey::new(8, 1, 6).unwrap());
        assert_eq!(forward.actuals(), (left, right));
    }

    #[test]
    fn may_overlap_union_is_monotone_and_deduplicates_witnesses() {
        let first = witness(8, 3, 4, 1, slot(3, 1), 2, slot(3, 2));
        let second = witness(8, 5, 1, 1, slot(5, 4), 2, slot(5, 9));
        let pair = first.pair();
        let mut left = MayOverlapSummary::default();
        let mut right = MayOverlapSummary::default();
        assert!(left.insert(first));
        assert!(right.insert(first));
        assert!(right.insert(second));

        assert!(left.union_from(&right));
        assert!(!left.union_from(&right));
        assert_eq!(left.witnesses(pair).len(), 2);
    }

    #[test]
    fn summary_order_is_stable_across_registration_order() {
        let witnesses = [
            witness(9, 7, 2, 4, slot(7, 8), 1, slot(7, 3)),
            witness(8, 5, 3, 2, slot(5, 9), 1, slot(5, 4)),
            witness(8, 3, 1, 1, slot(3, 1), 2, slot(3, 2)),
        ];
        let mut forward = MayOverlapSummary::default();
        let mut reverse = MayOverlapSummary::default();
        for witness in witnesses {
            forward.insert(witness);
        }
        for witness in witnesses.into_iter().rev() {
            reverse.insert(witness);
        }

        assert_eq!(forward.ordered_rows(), reverse.ordered_rows());
        assert_eq!(
            forward
                .ordered_rows()
                .into_iter()
                .map(|(pair, _)| pair.function())
                .collect::<Vec<_>>(),
            vec![8, 8, 9]
        );
    }

    #[test]
    fn missing_or_incomplete_positive_evidence_is_conservatively_overlap() {
        let missing = PairFacts::<String>::default();
        let incomplete = PairFacts {
            points_to: SetPairEvidence::Incomplete {
                left: BTreeSet::from(["left".to_owned()]),
                right: BTreeSet::from(["right".to_owned()]),
            },
            ..PairFacts::default()
        };
        let complete = PairFacts {
            origins: SetPairEvidence::Complete {
                left: BTreeSet::from(["left".to_owned()]),
                right: BTreeSet::from(["right".to_owned()]),
            },
            ..PairFacts::default()
        };
        let storage_alias_dominates = PairFacts::<String> {
            storage_alias: true,
            projection_disjoint: true,
            ..PairFacts::default()
        };

        assert_eq!(classify_pair(&missing), PairClass::NotProvenDisjoint);
        assert_eq!(classify_pair(&incomplete), PairClass::NotProvenDisjoint);
        assert_eq!(classify_pair(&complete), PairClass::ProvenDisjoint);
        assert_eq!(
            classify_pair(&storage_alias_dominates),
            PairClass::NotProvenDisjoint
        );
    }
}
