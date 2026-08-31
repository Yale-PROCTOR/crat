//! E2-FN lifetime planning.
//!
//! This module is the sole rewriter-side consumer of the intact NB5-O
//! [`OriginSummaries`] carrier for lifetime semantics.  It starts with the
//! carrier-shape witness; eligibility, SCC planning, and emission receipts are
//! filled by the subsequent RED-first steps.

use crate::analyses::borrow_ownership::origin_summary::OriginSummaries;

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
