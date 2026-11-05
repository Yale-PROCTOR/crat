//! Uniform declaration summaries for fixed arrays of raw pointers.

use super::{crate_slots::CrateSlots, nullability::NullabilityFacts, solver::KindSolver};
use crate::utils::rustc::RustProgram;

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum HoldReason {
    ElementBorrowNotRepresented,
    ElementOwnershipNotRepresented,
    OpaqueElement,
    UnknownValue,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ArrayFieldRow {
    pub(crate) field: String,
    pub(crate) slot_keys: Vec<String>,
    pub(crate) source_slots: Vec<String>,
    pub(crate) loaded_slots: Vec<String>,
    pub(crate) null_literal: bool,
    pub(crate) opaque: bool,
    pub(crate) unknown: bool,
    pub(crate) holds: Vec<HoldReason>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ArrayFieldFacts {
    pub(crate) rows: Vec<ArrayFieldRow>,
}

pub(crate) fn constrain(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    solver: &KindSolver,
    nullability: &mut NullabilityFacts,
) -> ArrayFieldFacts {
    let mut values = values::collect(program, slots, nullability);
    for index in 0..slots.field_slots.len() {
        let id = super::slots::SlotId::from_usize(index);
        if slots.field_slots.is_array_slot(id) {
            solver.forbid_field_ref(super::solver::SlotRef::Field(id));
            solver.forbid_field_own(super::solver::SlotRef::Field(id));
        }
    }
    // An indexed load carries the summary's conservative form, including
    // loads through a known field-address alias. This grants no source owner.
    for slot in values.raw_load_slots {
        solver.assume(slot, super::SlotKind::Raw);
    }
    nullability.null_literal.extend(values.null_literal_slots);
    nullability.is_null_use.extend(values.null_use_slots);
    for row in &mut values.rows {
        row.holds.extend([
            HoldReason::ElementBorrowNotRepresented,
            HoldReason::ElementOwnershipNotRepresented,
        ]);
        row.holds.sort();
        row.holds.dedup();
    }
    ArrayFieldFacts { rows: values.rows }
}

mod values;

#[cfg(test)]
mod tests;
