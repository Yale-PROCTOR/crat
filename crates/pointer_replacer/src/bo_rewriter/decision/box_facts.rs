//! Derive-on-load ownership facts used by Box emission.
//!
//! The production implementation is intentionally RED-first.  These tests pin
//! the conservative concrete replay before the frozen ownership emitter is
//! connected to it.

use rustc_index::IndexVec;

use crate::analyses::borrow_ownership::{SlotKind, ssa::constraint::Var};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FactValue {
    MustOwn,
    NotOwn,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RecordedEquation {
    Linear { left: Var, right: Var, result: Var },
    Assume { var: Var, value: bool },
    Equal { left: Var, right: Var },
    LessEqual { left: Var, right: Var },
    EqMin { result: Var, left: Var, right: Var },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EndpointStatus {
    Active,
    InactiveSlot,
    InactiveVar,
    Unknown,
}

pub(crate) fn classify_endpoint(value: FactValue, slot: SlotKind) -> EndpointStatus {
    match (value, slot) {
        (FactValue::MustOwn, SlotKind::Owning) => EndpointStatus::Active,
        (FactValue::MustOwn, _) => EndpointStatus::InactiveSlot,
        (FactValue::NotOwn, _) => EndpointStatus::InactiveVar,
        (FactValue::Unknown, _) => EndpointStatus::Unknown,
    }
}

fn assign(
    values: &mut IndexVec<Var, FactValue>,
    var: Var,
    value: FactValue,
) -> Result<bool, String> {
    if value == FactValue::Unknown {
        return Ok(false);
    }
    match values[var] {
        FactValue::Unknown => {
            values[var] = value;
            Ok(true)
        }
        current if current == value => Ok(false),
        current => Err(format!(
            "contradictory ownership facts for {var:?}: {current:?} versus {value:?}"
        )),
    }
}

fn replay_one(
    values: &mut IndexVec<Var, FactValue>,
    equation: &RecordedEquation,
) -> Result<bool, String> {
    use FactValue::{MustOwn, NotOwn, Unknown};
    let mut changed = false;
    match *equation {
        RecordedEquation::Assume { var, value } => {
            changed |= assign(values, var, if value { MustOwn } else { NotOwn })?;
        }
        RecordedEquation::Equal { left, right } => match (values[left], values[right]) {
            (Unknown, value) => changed |= assign(values, left, value)?,
            (value, Unknown) => changed |= assign(values, right, value)?,
            (left_value, right_value) if left_value != right_value => {
                return Err(format!(
                    "equal equation disagrees for {left:?}/{right:?}: {left_value:?}/{right_value:?}"
                ));
            }
            _ => {}
        },
        RecordedEquation::LessEqual { left, right } => {
            if values[left] == MustOwn {
                changed |= assign(values, right, MustOwn)?;
            }
            if values[right] == NotOwn {
                changed |= assign(values, left, NotOwn)?;
            }
        }
        RecordedEquation::EqMin {
            result,
            left,
            right,
        } => {
            if values[result] == MustOwn {
                changed |= assign(values, left, MustOwn)?;
                changed |= assign(values, right, MustOwn)?;
            }
            if values[left] == NotOwn || values[right] == NotOwn {
                changed |= assign(values, result, NotOwn)?;
            }
            if values[left] == MustOwn && values[right] == MustOwn {
                changed |= assign(values, result, MustOwn)?;
            }
        }
        RecordedEquation::Linear {
            left,
            right,
            result,
        } => {
            if values[left] == MustOwn {
                changed |= assign(values, right, NotOwn)?;
                changed |= assign(values, result, MustOwn)?;
            }
            if values[right] == MustOwn {
                changed |= assign(values, left, NotOwn)?;
                changed |= assign(values, result, MustOwn)?;
            }
            if values[result] == NotOwn {
                changed |= assign(values, left, NotOwn)?;
                changed |= assign(values, right, NotOwn)?;
            }
            if values[left] == NotOwn && values[right] == NotOwn {
                changed |= assign(values, result, NotOwn)?;
            }
            if values[result] == MustOwn && values[left] == NotOwn {
                changed |= assign(values, right, MustOwn)?;
            }
            if values[result] == MustOwn && values[right] == NotOwn {
                changed |= assign(values, left, MustOwn)?;
            }
        }
    }
    Ok(changed)
}

pub(crate) fn replay_values(
    mut values: IndexVec<Var, FactValue>,
    equations: &[RecordedEquation],
) -> Result<IndexVec<Var, FactValue>, String> {
    loop {
        let mut changed = false;
        for equation in equations {
            changed |= replay_one(&mut values, equation)?;
        }
        if !changed {
            return Ok(values);
        }
    }
}

pub(crate) fn render_equations(equations: &[RecordedEquation]) -> String {
    let mut rows = equations
        .iter()
        .map(|equation| match *equation {
            RecordedEquation::Linear {
                left,
                right,
                result,
            } => format!("linear\t{}\t{}\t{}", left.as_u32(), right.as_u32(), result.as_u32()),
            RecordedEquation::Assume { var, value } => {
                format!("assume\t{}\t{}", var.as_u32(), u8::from(value))
            }
            RecordedEquation::Equal { left, right } => {
                format!("equal\t{}\t{}", left.as_u32(), right.as_u32())
            }
            RecordedEquation::LessEqual { left, right } => {
                format!("less-equal\t{}\t{}", left.as_u32(), right.as_u32())
            }
            RecordedEquation::EqMin {
                result,
                left,
                right,
            } => format!("eq-min\t{}\t{}\t{}", result.as_u32(), left.as_u32(), right.as_u32()),
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows.join("\n") + "\n"
}

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
