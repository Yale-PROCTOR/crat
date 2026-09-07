//! Comparison occurrence is separate from a comparison-derived rejection.

use std::collections::BTreeSet;

use super::{crate_slots::CrateSlots, export::PlaceKey};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum ComparisonDisposition {
    #[default]
    NoComparisonCauseIdentified,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ComparisonOperand {
    pub(crate) place: Option<PlaceKey>,
    /// Missing means this operand has no resolved BO slot, never a safe fact.
    pub(crate) slot: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ComparisonSite {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) operator: String,
    pub(crate) operands: Vec<ComparisonOperand>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum GuardRule {
    AllocationSource,
    NoBorrowOrigin,
    FieldOpaque,
    FieldUnresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct RefGuard {
    pub(crate) slot: String,
    pub(crate) rule: GuardRule,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ComparisonLedger {
    pub(crate) sites: Vec<ComparisonSite>,
    /// Direct eager Ref guards only. These are actual producer actions, not a
    /// complete explanation of every Raw model or transitive solver consequence.
    pub(crate) guards: BTreeSet<RefGuard>,
    pub(crate) disposition: ComparisonDisposition,
}

fn canonical(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    slots: &CrateSlots,
    reference: super::solver::SlotRef,
) -> String {
    use super::{slot_key, slots::SlotOwner, solver::SlotRef};
    match reference {
        SlotRef::Local(function, id) => {
            let slot = slots.fn_local_slots[&function].slot(id);
            let SlotOwner::Local(local) = slot.owner else { unreachable!() };
            slot_key::local_key(tcx, function, local.as_usize(), slot.depth)
        }
        SlotRef::Field(id) => {
            let slot = slots.field_slots.slot(id);
            let SlotOwner::Field(field) = slot.owner else { unreachable!() };
            slot_key::field_key(tcx, field.struct_did, field.field_index, slot.depth)
        }
    }
}

pub(crate) fn record_sites(program: &RustProgram<'_>, slots: &CrateSlots) {
    use rustc_middle::mir::{BinOp, Rvalue, StatementKind};

    use super::{
        resolve::{ResolvedSlot, resolve_place},
        solver::SlotRef,
    };
    if !super::export::capturing() {
        return;
    }
    let mut sites = Vec::new();
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement, operation) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (_, Rvalue::BinaryOp(op, operands))) =
                    &operation.kind
                else {
                    continue;
                };
                if !matches!(
                    op,
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                ) || !operands.0.ty(&*body, program.tcx).is_any_ptr()
                    || !operands.1.ty(&*body, program.tcx).is_any_ptr()
                {
                    continue;
                }
                let operands = [&operands.0, &operands.1]
                    .into_iter()
                    .map(|operand| {
                        let place = operand.place();
                        let slot = place
                            .and_then(|place| resolve_place(slots, function, &body, place, 0, None))
                            .map(|resolved| match resolved {
                                ResolvedSlot::Local(id) => SlotRef::Local(function, id),
                                ResolvedSlot::Field(id) => SlotRef::Field(id),
                            })
                            .map(|slot| canonical(program.tcx, slots, slot));
                        ComparisonOperand {
                            place: place.map(PlaceKey::from_place),
                            slot,
                        }
                    })
                    .collect();
                sites.push(ComparisonSite {
                    function: program.tcx.def_path_str(function.to_def_id()),
                    block: block.as_u32(),
                    statement,
                    operator: format!("{op:?}"),
                    operands,
                });
            }
        }
    }
    sites.sort_by(|a, b| {
        (&a.function, a.block, a.statement).cmp(&(&b.function, b.block, b.statement))
    });
    super::export::record(|export| {
        export.comparisons = Some(ComparisonLedger {
            sites,
            guards: BTreeSet::new(),
            disposition: ComparisonDisposition::NoComparisonCauseIdentified,
        })
    });
}

/// Called only beside the actual guard emission. It neither queries nor
/// changes the solver and never infers a cause from comparison syntax.
pub(crate) fn record_guard(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    slots: &CrateSlots,
    reference: super::solver::SlotRef,
    rule: GuardRule,
) {
    if !super::export::capturing() {
        return;
    }
    let guard = RefGuard {
        slot: canonical(tcx, slots, reference),
        rule,
    };
    super::export::record(|export| {
        if let Some(ledger) = &mut export.comparisons {
            ledger.guards.insert(guard);
        }
    });
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod export_tests;
