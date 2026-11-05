//! Compiler-derived possible callees for source Call/TailCall locations.
//!
//! A nonempty known set is complete only when `unknown` is false. Unsupported
//! memory flow never acquires a callee or a retirement role from its spelling.

use std::collections::{BTreeSet, VecDeque};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        Body, CastKind, Local, Location, Operand, Place, Rvalue, START_BLOCK, StatementKind,
        TerminatorKind,
    },
    ty::{TyCtxt, TyKind, adjustment::PointerCoercion},
};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::{analyses::mir::CallKind, utils::rustc::RustProgram};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Targets {
    pub(crate) known: FxHashSet<DefId>,
    pub(crate) unknown: bool,
}

impl Default for Targets {
    fn default() -> Self {
        Self {
            known: FxHashSet::default(),
            unknown: true,
        }
    }
}

impl Targets {
    fn singleton(target: DefId) -> Self {
        Self {
            known: FxHashSet::from_iter([target]),
            unknown: false,
        }
    }

    fn union(&mut self, other: &Self) -> bool {
        let before = self.known.len();
        let changed = other.unknown && !self.unknown;
        self.unknown |= other.unknown;
        self.known.extend(other.known.iter().copied());
        changed || self.known.len() != before
    }
}

pub(crate) type CallTargets = FxHashMap<(LocalDefId, Location), Targets>;

/// Missing cells represent default Unknown, not an empty complete target set.
type State = FxHashMap<Local, Targets>;

fn function_cell(body: &Body<'_>, local: Local) -> bool {
    matches!(
        body.local_decls[local].ty.kind(),
        TyKind::FnDef(..) | TyKind::FnPtr(..)
    )
}

fn function_item<'tcx>(body: &Body<'tcx>, operand: &Operand<'tcx>) -> Option<DefId> {
    let ty = match operand {
        Operand::Constant(constant) => constant.ty(),
        Operand::Copy(place) | Operand::Move(place) => body.local_decls[place.as_local()?].ty,
    };
    match ty.kind() {
        TyKind::FnDef(target, _) => Some(*target),
        // An evaluated FnPtr constant needs a separate allocation/provenance
        // resolver. Do not send it through as_call's FnDef-only assertion.
        _ => None,
    }
}

fn operand_targets<'tcx>(body: &Body<'tcx>, operand: &Operand<'tcx>, state: &State) -> Targets {
    if let Some(target) = function_item(body, operand) {
        return Targets::singleton(target);
    }
    operand
        .place()
        .and_then(|place| place.as_local())
        .and_then(|local| state.get(&local))
        .cloned()
        .unwrap_or_default()
}

fn clobber(state: &mut State) {
    for targets in state.values_mut() {
        targets.unknown = true;
    }
}

fn forget(place: Place<'_>, state: &mut State) {
    if let Some(local) = place.as_local() {
        state.remove(&local);
    } else {
        clobber(state);
    }
}

fn forget_move(operand: &Operand<'_>, state: &mut State) {
    if let Operand::Move(place) = operand {
        forget(*place, state);
    }
}

fn statement_effect<'tcx>(
    body: &Body<'tcx>,
    statement: &StatementKind<'tcx>,
    addressed: &BTreeSet<Local>,
    state: &mut State,
) {
    match statement {
        StatementKind::Assign(box (destination, value)) => {
            let operand = match value {
                Rvalue::Use(operand) => Some(operand),
                Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer, _),
                    operand,
                    _,
                ) if function_item(body, operand).is_some() => Some(operand),
                _ => None,
            };
            // Read before strong update, including self-move/reification.
            let targets = operand
                .map(|operand| operand_targets(body, operand, state))
                .unwrap_or_default();
            let Some(local) = destination.as_local() else {
                // Unknown alias identity cannot make a visible replacement
                // disappear. Weakly join it into every exposed function cell;
                // retain Unknown for other values the store may introduce.
                clobber(state);
                for &local in addressed {
                    if function_cell(body, local) {
                        let cell = state.entry(local).or_default();
                        cell.union(&targets);
                        cell.unknown = true;
                    }
                }
                return;
            };
            if let Some(operand) = operand {
                forget_move(operand, state);
            }
            state.remove(&local);
            if function_cell(body, local) && (!targets.unknown || !targets.known.is_empty()) {
                state.insert(local, targets);
            }
        }
        StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
            state.remove(local);
        }
        StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
            forget(**place, state);
        }
        StatementKind::Intrinsic(
            box rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(_),
        ) => {
            clobber(state);
        }
        _ => {}
    }
}

fn terminator_effect(
    terminator: &TerminatorKind<'_>,
    addressed: &BTreeSet<Local>,
    state: &mut State,
) {
    match terminator {
        TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
            // An unexposed local cannot be rebound by a callee. Address-exposed
            // target cells may change through aliases, including on unwind.
            for local in addressed {
                if let Some(targets) = state.get_mut(local) {
                    targets.unknown = true;
                }
            }
            for argument in args {
                forget_move(&argument.node, state);
            }
        }
        TerminatorKind::Drop { place, .. } => {
            for local in addressed {
                if let Some(targets) = state.get_mut(local) {
                    targets.unknown = true;
                }
            }
            forget(*place, state);
        }
        TerminatorKind::InlineAsm { .. } => clobber(state),
        _ => {}
    }
}

fn join(entry: &mut Option<State>, incoming: State) -> bool {
    let Some(previous) = entry else {
        *entry = Some(incoming);
        return true;
    };
    let mut changed = false;
    for (local, targets) in previous.iter_mut() {
        changed |= targets.union(incoming.get(local).unwrap_or(&Targets::default()));
    }
    for (local, targets) in incoming {
        if let std::collections::hash_map::Entry::Vacant(entry) = previous.entry(local) {
            // The preceding path had an unknown binding for this local.
            let mut combined = Targets::default();
            combined.union(&targets);
            entry.insert(combined);
            changed = true;
        }
    }
    changed
}

pub(crate) fn analyze(program: &RustProgram<'_>) -> CallTargets {
    let mut calls = CallTargets::default();
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let addressed = super::addressed_locals(&body);
        let mut entries = vec![None; body.basic_blocks.len()];
        entries[START_BLOCK.as_usize()] = Some(State::default());
        let mut queue = VecDeque::from([START_BLOCK]);
        let mut queued = vec![false; body.basic_blocks.len()];
        queued[START_BLOCK.as_usize()] = true;
        while let Some(block) = queue.pop_front() {
            queued[block.as_usize()] = false;
            let data = &body.basic_blocks[block];
            let mut state = entries[block.as_usize()]
                .clone()
                .expect("reachable callee state");
            for statement in &data.statements {
                statement_effect(&body, &statement.kind, &addressed, &mut state);
            }
            terminator_effect(&data.terminator().kind, &addressed, &mut state);
            for successor in data.terminator().successors() {
                let mut outgoing = state.clone();
                if let TerminatorKind::Call {
                    destination,
                    target: Some(target),
                    ..
                } = &data.terminator().kind
                    && successor == *target
                {
                    // No interprocedural return-value summary is claimed.
                    forget(*destination, &mut outgoing);
                }
                if join(&mut entries[successor.as_usize()], outgoing)
                    && !queued[successor.as_usize()]
                {
                    queued[successor.as_usize()] = true;
                    queue.push_back(successor);
                }
            }
        }
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let operand = match &data.terminator().kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => continue,
            };
            // Source inventory includes unreachable calls. With no reachable
            // entry, only this block's explicit assignments supply known facts.
            let mut state = entries[block.as_usize()].clone().unwrap_or_default();
            for statement in &data.statements {
                statement_effect(&body, &statement.kind, &addressed, &mut state);
            }
            calls.insert(
                (
                    function,
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                ),
                operand_targets(&body, operand, &state),
            );
        }
    }
    calls
}

/// Classify an already resolved compiler identity using the existing boundary
/// discipline. This never classifies a local body as ForeignC by its name.
pub(crate) fn kind_for_target(tcx: TyCtxt<'_>, target: DefId) -> CallKind {
    let Some(local) = target.as_local() else { return CallKind::RustLib(target) };
    match tcx.hir_node_by_def_id(local) {
        rustc_hir::Node::Item(_) => CallKind::FreeStanding(local),
        rustc_hir::Node::ForeignItem(item) => CallKind::LibC(item.ident.name),
        rustc_hir::Node::ImplItem(_) => CallKind::Impl(local),
        _ => CallKind::Dynamic,
    }
}
