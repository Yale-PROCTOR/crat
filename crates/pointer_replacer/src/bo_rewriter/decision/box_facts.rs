//! Derive-on-load ownership facts used by Box emission.
//!
//! The production implementation is intentionally RED-first.  These tests pin
//! the conservative concrete replay before the frozen ownership emitter is
//! connected to it.

#[cfg(test)]
mod tests {
    use rustc_index::IndexVec;

    use super::{
        EndpointStatus, FactValue, RecordedEquation, classify_endpoint, render_equations,
        replay_values,
    };
    use crate::analyses::borrow_ownership::{
        SlotKind,
        ssa::constraint::Var,
    };

    fn var(index: u32) -> Var {
        Var::from_u32(index)
    }

    #[test]
    fn box_x1_equal_and_linear_replay_reaches_a_unique_model() {
        let mut seeds = IndexVec::from_raw(vec![FactValue::Unknown; 5]);
        seeds[var(1)] = FactValue::MustOwn;
        seeds[var(4)] = FactValue::NotOwn;
        let equations = [
            RecordedEquation::Equal {
                left: var(1),
                right: var(2),
            },
            RecordedEquation::Linear {
                left: var(2),
                right: var(3),
                result: var(1),
            },
        ];

        let values = replay_values(seeds, &equations).expect("consistent replay");
        assert_eq!(values[var(1)], FactValue::MustOwn);
        assert_eq!(values[var(2)], FactValue::MustOwn);
        assert_eq!(values[var(3)], FactValue::NotOwn);
        assert_eq!(values[var(4)], FactValue::NotOwn);
    }

    #[test]
    fn box_x1_underdetermined_linear_stays_unknown() {
        let mut seeds = IndexVec::from_raw(vec![FactValue::Unknown; 4]);
        seeds[var(3)] = FactValue::MustOwn;
        let equations = [RecordedEquation::Linear {
            left: var(1),
            right: var(2),
            result: var(3),
        }];

        let values = replay_values(seeds, &equations).expect("consistent replay");
        assert_eq!(values[var(1)], FactValue::Unknown);
        assert_eq!(values[var(2)], FactValue::Unknown);
        assert_eq!(values[var(3)], FactValue::MustOwn);
    }

    #[test]
    fn box_x1_contradictory_facts_fail_closed() {
        let mut seeds = IndexVec::from_raw(vec![FactValue::Unknown; 3]);
        seeds[var(1)] = FactValue::MustOwn;
        seeds[var(2)] = FactValue::NotOwn;
        let equations = [RecordedEquation::Equal {
            left: var(1),
            right: var(2),
        }];

        assert!(replay_values(seeds, &equations).is_err());
    }

    #[test]
    fn box_n7_endpoint_is_active_only_for_must_own_over_owning_slot() {
        assert_eq!(
            classify_endpoint(FactValue::MustOwn, SlotKind::Owning),
            EndpointStatus::Active,
        );
        assert_eq!(
            classify_endpoint(FactValue::MustOwn, SlotKind::Raw),
            EndpointStatus::InactiveSlot,
        );
        assert_eq!(
            classify_endpoint(FactValue::NotOwn, SlotKind::Owning),
            EndpointStatus::InactiveVar,
        );
        assert_eq!(
            classify_endpoint(FactValue::Unknown, SlotKind::Owning),
            EndpointStatus::Unknown,
        );
    }

    #[test]
    fn box_n8_equation_receipt_is_order_independent() {
        let left = RecordedEquation::Equal {
            left: var(1),
            right: var(2),
        };
        let right = RecordedEquation::Assume {
            var: var(3),
            value: false,
        };
        assert_eq!(
            render_equations(&[left.clone(), right.clone()]),
            render_equations(&[right, left]),
        );
    }
}
