//! Local coverage outcomes, with actual kind and copy-carrier identities.
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
    InnerLoanMissing {
        depth: u8,
    },
    /// The holder's value leaves the frame, so its copy closure is
    /// incomplete and its liveness is not a statement about the program. The
    /// VERDICT is the same demotion as `InnerLoanMissing`; the label is separate
    /// so the escaped population is counted rather than inferred.
    InnerLoanEscaped {
        depth: u8,
    },
}
impl Reason {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::InnerLoanMissing { .. } => "p1s-inner-loan-missing:demote",
            Self::InnerLoanEscaped { .. } => "p1s-inner-loan-escaped:demote",
        }
    }

    /// The depth, when this is an inner-loan demotion of either kind.
    ///
    /// `InnerLoanMissing` and `InnerLoanEscaped` are ONE verdict -- the demotion
    /// this site has always done -- and differ only in why the facts were
    /// missing. A receipt reader that cares about the verdict asks this; one that
    /// cares about the population asks the label.
    #[cfg(test)]
    pub(crate) fn inner_loan_depth(self) -> Option<u8> {
        match self {
            Self::InnerLoanMissing { depth } | Self::InnerLoanEscaped { depth } => Some(depth),
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
/// Relay main/388 stage 2 (R1347-1), 270 row 6: the copy graph split by direction. A depth-0 copy
/// (`a = b`, a pointer-to-pointer cast, `CopyForDeref`) moves `b`'s value INTO `a`: the forward edge
/// `b -> a`. Every other edge of [`copy_graph`] -- a copy's deeper levels, `&x` / `&raw x` at every
/// level -- names one cell two ways and stays two-way. `leaks` are the slots whose value leaves
/// through a channel the graph does not see, with the channel's kind.
#[derive(Default)]
pub(crate) struct DirectedCopies {
    forward: FxHashMap<SlotRef, Vec<SlotRef>>,
    identity: FxHashMap<SlotRef, Vec<SlotRef>>,
    leaks: FxHashMap<SlotRef, LeakKind>,
}

/// Where a value leaves the copy graph (R1352-1 (b)'s count).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LeakKind {
    /// An argument of a call into a local function.
    LocalCallee,
    /// An argument of a call through a function pointer.
    FnPointer,
    /// An argument of a call into a foreign function (`memcpy` and its family among them).
    Foreign,
    /// An argument of any other library call: a pointer method that reads or writes the pointee
    /// (`read`, `write`, `replace`, `swap`, `copy_*`, ...) among them.
    Library,
    /// The return place.
    Return,
    /// A place through a union.
    Union,
}

impl LeakKind {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::LocalCallee => "local-callee-argument",
            Self::FnPointer => "fn-pointer-argument",
            Self::Foreign => "foreign-argument",
            Self::Library => "library-argument",
            Self::Return => "return",
            Self::Union => "union",
        }
    }
}

/// R1352-1 (a): the core raw-pointer methods modeled as copies -- each derives its result from its
/// receiver and stores nothing, so its arguments flow into its destination (forward at depth 0,
/// one cell's names below). `is_null` / `addr` / `offset_from` return no pointer, so they add no
/// edge and leak nothing. Any other method -- one that reads or writes the pointee, and `as_ref` /
/// `as_mut`, whose `Option<&T>` the walk cannot follow into its payload -- is a leak.
const COPY_METHODS: &[&str] = &[
    "offset",
    "add",
    "sub",
    "wrapping_offset",
    "wrapping_add",
    "wrapping_sub",
    "byte_offset",
    "byte_add",
    "byte_sub",
    "wrapping_byte_offset",
    "wrapping_byte_add",
    "wrapping_byte_sub",
    "cast",
    "cast_mut",
    "cast_const",
    "is_null",
    "addr",
    "offset_from",
];

pub(crate) fn directed_copies<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
) -> DirectedCopies {
    let mut graph = DirectedCopies::default();
    let tcx = program.tcx;
    for &function in &program.functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let slot = |resolved| match resolved {
            ResolvedSlot::Local(id) => SlotRef::Local(function, id),
            ResolvedSlot::Field(id) => SlotRef::Field(id),
        };
        let union = |place: rustc_middle::mir::Place<'tcx>| {
            place
                .iter_projections()
                .any(|(base, _)| base.ty(&body.local_decls, tcx).ty.is_union())
        };
        let leak = |place: rustc_middle::mir::Place<'tcx>,
                    kind: LeakKind,
                    leaks: &mut FxHashMap<SlotRef, LeakKind>| {
            for depth in 0..MAX_SLOT_DEPTH {
                if let Some(resolved) = resolve_place(slots, function, &body, place, depth, None) {
                    leaks.entry(slot(resolved)).or_insert(kind);
                }
            }
        };
        let edge = |a: SlotRef, b: SlotRef, forward: bool, graph: &mut DirectedCopies| {
            if a == b {
            } else if forward {
                graph.forward.entry(b).or_default().push(a);
            } else {
                graph.identity.entry(a).or_default().push(b);
                graph.identity.entry(b).or_default().push(a);
            }
        };
        leak(
            rustc_middle::mir::RETURN_PLACE.into(),
            LeakKind::Return,
            &mut graph.leaks,
        );
        for data in body.basic_blocks.iter() {
            let (func, args, destination) = match &data.terminator().kind {
                rustc_middle::mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => (func, args, Some(*destination)),
                rustc_middle::mir::TerminatorKind::TailCall { func, args, .. } => {
                    (func, args, None)
                }
                _ => continue,
            };
            let callee = func.const_fn_def().map(|(callee, _)| callee);
            let copy_method = callee.is_some_and(|callee| {
                !callee.is_local()
                    && COPY_METHODS.contains(&tcx.item_name(callee).as_str())
                    && tcx
                        .impl_of_method(callee)
                        .is_some_and(|block| tcx.type_of(block).skip_binder().is_raw_ptr())
            });
            let kind = match callee {
                None => LeakKind::FnPointer,
                Some(callee) if callee.is_local() => LeakKind::LocalCallee,
                Some(callee) if tcx.is_foreign_item(callee) => LeakKind::Foreign,
                Some(_) => LeakKind::Library,
            };
            for place in args.iter().filter_map(|argument| argument.node.place()) {
                let Some(destination) = destination.filter(|_| copy_method) else {
                    leak(place, kind, &mut graph.leaks);
                    continue;
                };
                for depth in 0..MAX_SLOT_DEPTH {
                    if let (Some(a), Some(b)) = (
                        resolve_place(slots, function, &body, destination, depth, None),
                        resolve_place(slots, function, &body, place, depth, None),
                    ) {
                        edge(slot(a), slot(b), depth == 0, &mut graph);
                    }
                }
            }
        }
        for statement in body.basic_blocks.iter().flat_map(|data| &data.statements) {
            let StatementKind::Assign(box (lhs, value)) = &statement.kind else { continue };
            let (rhs, shift, copy) = match value {
                Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                    let Some(place) = operand.place() else { continue };
                    (place, 0, true)
                }
                Rvalue::CopyForDeref(place) => (*place, 0, true),
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => (*place, 1, false),
                _ => continue,
            };
            if union(*lhs) || union(rhs) {
                leak(*lhs, LeakKind::Union, &mut graph.leaks);
                leak(rhs, LeakKind::Union, &mut graph.leaks);
            }
            for depth in 0..MAX_SLOT_DEPTH {
                if let (Some(a), Some(b)) = (
                    resolve_place(slots, function, &body, *lhs, depth + shift, None),
                    resolve_place(slots, function, &body, rhs, depth, None),
                ) {
                    edge(slot(a), slot(b), copy && depth == 0, &mut graph);
                }
            }
        }
    }
    graph
}

/// Relay main/388 stage 2: the slots a demoted holder's VALUE can reach -- forward along copies, both
/// ways along one cell's names -- not the slots that merely copy from the same field elsewhere. Fail
/// closed: a walk that reaches a leak takes the undirected closure, as before; the first leak it met
/// is returned with its kind.
pub(super) fn directed_closure(
    holder: SlotRef,
    directed: &DirectedCopies,
    undirected: &FxHashMap<SlotRef, Vec<SlotRef>>,
) -> (FxHashSet<SlotRef>, Option<(SlotRef, LeakKind)>) {
    let mut first = None;
    let mut pending = vec![holder];
    let mut visited = FxHashSet::default();
    while let Some(slot) = pending.pop() {
        if !visited.insert(slot) {
            continue;
        }
        if first.is_none()
            && let Some(&kind) = directed.leaks.get(&slot)
        {
            first = Some((slot, kind));
        }
        pending.extend(directed.forward.get(&slot).into_iter().flatten());
        pending.extend(directed.identity.get(&slot).into_iter().flatten());
    }
    if first.is_none() {
        return (visited, None);
    }
    let mut pending = vec![holder];
    let mut undirected_visited = FxHashSet::default();
    while let Some(slot) = pending.pop() {
        if undirected_visited.insert(slot) {
            pending.extend(undirected.get(&slot).into_iter().flatten());
        }
    }
    (undirected_visited, first)
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
        let (visited, leak) = directed_closure(holder, &self.directed_copies, &self.copy_graph);
        let chain = visited
            .into_iter()
            .filter(|slot| self.safe_holders.iter().any(|(safe, _, _)| safe == slot))
            .map(|slot| (self.keys[&slot].clone(), slot))
            .collect::<BTreeMap<_, _>>();
        // R1352-1 (b): a fallback names the first leak its walk met, and the slots it pins (log only).
        if let Some((slot, kind)) = leak
            && crate::phase_log::on()
            && !chain.is_empty()
        {
            let key = |slot: &SlotRef| {
                self.keys
                    .get(slot)
                    .map(|key| key.to_string())
                    .unwrap_or_else(|| format!("{slot:?}"))
            };
            crate::phase_log::mark(
                "retirement:fallback",
                "leak",
                &format!(
                    "holder={} kind={} leak={} chain={}",
                    key(&holder),
                    kind.label(),
                    key(&slot),
                    chain.keys().cloned().collect::<Vec<_>>().join(",")
                ),
            );
        }
        let chain = chain.into_values().collect::<Vec<_>>();
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
            .map(|slot| (super::super::guarded_repair::SlotKey::of(slot), slot))
            .collect::<BTreeMap<_, _>>()
            .into_values()
            .collect()
    }
}
