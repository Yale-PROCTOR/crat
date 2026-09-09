//! R245 local coverage outcomes, with actual kind and copy-carrier identities.
use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::{CastKind, Rvalue, StatementKind};

use super::*;
use crate::analyses::borrow_ownership::{
    crate_slots::MAX_SLOT_DEPTH,
    resolve::{ResolvedSlot, resolve_place},
};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Reason {
    InnerLoanMissing { depth: u8 },
    OwnerMissing,
}
impl Reason {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::InnerLoanMissing { .. } => "p1s-inner-loan-missing:demote",
            Self::OwnerMissing => "p1s-owner-missing:demote",
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Demotion {
    pub(crate) source: SourceEventKey,
    pub(crate) function: LocalDefId,
    pub(crate) location: Location,
    pub(crate) phase: SourcePhase,
    pub(crate) route: Vec<RouteStep>,
    pub(crate) holder: SlotRef,
    pub(crate) reason: Reason,
    pub(crate) chain: Vec<SlotRef>,
}
pub(crate) fn copy_graph(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
) -> FxHashMap<SlotRef, Vec<SlotRef>> {
    let mut graph: FxHashMap<SlotRef, Vec<SlotRef>> = FxHashMap::default();
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let slot = |resolved| match resolved {
            ResolvedSlot::Local(id) => SlotRef::Local(function, id),
            ResolvedSlot::Field(id) => SlotRef::Field(id),
        };
        for statement in body.basic_blocks.iter().flat_map(|block| &block.statements) {
            let StatementKind::Assign(box (lhs, value)) = &statement.kind else { continue };
            let (rhs, shift) = match value {
                Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                    let Some(place) = operand.place() else { continue };
                    (place, 0)
                }
                Rvalue::CopyForDeref(place) => (*place, 0),
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => (*place, 1),
                _ => continue,
            };
            for depth in 0..MAX_SLOT_DEPTH {
                if let (Some(a), Some(b)) = (
                    resolve_place(slots, function, &body, *lhs, depth + shift, None),
                    resolve_place(slots, function, &body, rhs, depth, None),
                ) {
                    let (a, b) = (slot(a), slot(b));
                    if a != b {
                        graph.entry(a).or_default().push(b);
                        graph.entry(b).or_default().push(a);
                    }
                }
            }
        }
    }
    graph
}
impl Context {
    pub(super) fn overlapping_holders(
        &self,
        function: LocalDefId,
        event: &FrameEvent,
        heap_only: bool,
    ) -> Vec<SlotRef> {
        self.safe_holders
            .iter()
            .filter_map(|&(slot, owner, depth)| {
                let target = if let Some((owner_function, local)) = owner {
                    if owner_function != function {
                        return None;
                    }
                    self.objects.pointer_at(
                        function,
                        event.location,
                        &PlaceKey::from_place(rustc_middle::mir::Place::from(local)),
                        depth,
                    )
                } else {
                    ObjectSet::default()
                };
                overlap(&target, &event.objects, function, heap_only).map(|_| slot)
            })
            .collect()
    }

    pub(super) fn demote(
        &self,
        review: &mut RetirementReview,
        event: &FrameEvent,
        holder: SlotRef,
        reason: Reason,
    ) {
        let mut pending = vec![holder];
        let mut visited = FxHashSet::default();
        while let Some(slot) = pending.pop() {
            if visited.insert(slot) {
                pending.extend(self.copy_graph.get(&slot).into_iter().flatten().copied());
            }
        }
        let chain = visited
            .into_iter()
            .filter(|slot| self.safe_holders.iter().any(|(safe, _, _)| safe == slot))
            .map(|slot| (self.keys[&slot].clone(), slot))
            .collect::<BTreeMap<_, _>>()
            .into_values()
            .collect::<Vec<_>>();
        if chain.is_empty() {
            return;
        }
        review.demotions.push(Demotion {
            source: event.source.key.clone(),
            function: event.frame,
            location: event.location,
            phase: event.phase,
            route: event.route.clone(),
            holder,
            reason,
            chain,
        });
    }
}
impl RetirementReview {
    pub(crate) fn raw_targets(&self) -> Vec<SlotRef> {
        self.demotions
            .iter()
            .flat_map(|row| row.chain.iter().copied())
            .map(|slot| (super::super::l2::SlotKey::of(slot), slot))
            .collect::<BTreeMap<_, _>>()
            .into_values()
            .collect()
    }
}
