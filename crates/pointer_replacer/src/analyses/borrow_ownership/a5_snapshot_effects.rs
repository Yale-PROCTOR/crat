//! MIR producer for A5's fail-closed snapshot-equivalence check.

use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        Body, Local, Operand, Place, StatementKind, TerminatorKind,
        visit::{PlaceContext, Visitor},
    },
    ty::TyCtxt,
};

use super::a5_overlap::{
    PairSide, SnapshotEffect, SnapshotEffectGraph, SnapshotVerdict, check_snapshot_equivalence,
};

struct Uses {
    mutable: Local,
    shared: Local,
    shared_read: bool,
    bare_or_opaque: bool,
}

impl<'tcx> Visitor<'tcx> for Uses {
    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        _context: PlaceContext,
        _location: rustc_middle::mir::Location,
    ) {
        if place.local == self.shared {
            if place.projection.first() == Some(&rustc_middle::mir::PlaceElem::Deref) {
                self.shared_read = true;
            } else {
                self.bare_or_opaque = true;
            }
        } else if place.local == self.mutable && place.projection.is_empty() {
            self.bare_or_opaque = true;
        }
    }
}

fn operand_mentions(operand: &Operand<'_>, locals: [Local; 2]) -> bool {
    operand
        .place()
        .is_some_and(|place| locals.contains(&place.local))
}

pub(crate) fn snapshot_verdict_for_target(
    tcx: TyCtxt<'_>,
    target: LocalDefId,
    left_argument: usize,
    right_argument: usize,
    read_only: PairSide,
) -> SnapshotVerdict {
    let body = tcx.mir_drops_elaborated_and_const_checked(target).borrow();
    snapshot_verdict_for_body(tcx, target, &body, left_argument, right_argument, read_only)
}

fn snapshot_verdict_for_body(
    tcx: TyCtxt<'_>,
    target: LocalDefId,
    body: &Body<'_>,
    left_argument: usize,
    right_argument: usize,
    read_only: PairSide,
) -> SnapshotVerdict {
    let left = Local::from_usize(left_argument + 1);
    let right = Local::from_usize(right_argument + 1);
    let (mutable, shared) = match read_only {
        PairSide::Left => (right, left),
        PairSide::Right => (left, right),
    };
    if mutable.index() > body.arg_count || shared.index() > body.arg_count {
        return SnapshotVerdict::OpaqueEscape;
    }

    let mut events = Vec::new();
    let mut recursive = false;
    for data in body.basic_blocks.iter() {
        let start = events.len();
        for statement in &data.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                events.push(SnapshotEffect::None);
                continue;
            };
            let mut uses = Uses {
                mutable,
                shared,
                shared_read: false,
                bare_or_opaque: false,
            };
            uses.visit_rvalue(rvalue, rustc_middle::mir::Location::START);
            if uses.bare_or_opaque {
                events.push(SnapshotEffect::OpaqueEscape);
            } else if uses.shared_read {
                events.push(SnapshotEffect::SharedRead);
            }
            if lhs.local == mutable
                && lhs.projection.first() == Some(&rustc_middle::mir::PlaceElem::Deref)
            {
                events.push(SnapshotEffect::MutableWrite);
            } else if lhs.local == shared || (lhs.local == mutable && lhs.projection.is_empty()) {
                events.push(SnapshotEffect::OpaqueEscape);
            }
            if events.len() == start {
                events.push(SnapshotEffect::None);
            }
        }
        let term_start = events.len();
        match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                let mentions = args
                    .iter()
                    .any(|arg| operand_mentions(&arg.node, [mutable, shared]));
                if mentions {
                    let name = func
                        .constant()
                        .and_then(|constant| match constant.ty().kind() {
                            rustc_type_ir::TyKind::FnDef(did, _) => Some(tcx.def_path_str(*did)),
                            _ => None,
                        });
                    if name
                        .as_deref()
                        .is_some_and(|name| name.contains("volatile"))
                    {
                        events.push(SnapshotEffect::Volatile);
                    } else if name
                        .as_deref()
                        .is_some_and(|name| name.contains("atomic") || name.contains("__atomic_"))
                    {
                        events.push(SnapshotEffect::Atomic);
                    } else {
                        events.push(SnapshotEffect::OpaqueEscape);
                    }
                    recursive |= func.constant().is_some_and(|constant| matches!(constant.ty().kind(), rustc_type_ir::TyKind::FnDef(did, _) if did.as_local() == Some(target)));
                }
            }
            TerminatorKind::Return => {}
            _ => {}
        }
        if events.len() == term_start {
            events.push(SnapshotEffect::None);
        }
    }
    let mut edges = Vec::new();
    for index in 0..events.len().saturating_sub(1) {
        edges.push((index, index + 1));
    }
    let graph = if recursive {
        SnapshotEffectGraph::recursive(events)
    } else {
        SnapshotEffectGraph::new(events, edges).expect("producer indices are internal")
    };
    check_snapshot_equivalence(&graph)
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::*;

    fn verdict(code: &str) -> SnapshotVerdict {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let function = tcx
                .hir_crate(())
                .owners
                .iter()
                .filter_map(|owner| owner.as_owner())
                .find_map(|owner| {
                    let OwnerNode::Item(item) = owner.node() else { return None };
                    matches!(item.kind, ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
                })
                .unwrap();
            snapshot_verdict_for_target(tcx, function, 0, 1, PairSide::Right)
        })
        .unwrap()
    }

    #[test]
    fn mir_producer_preserves_rhs_read_before_lhs_write() {
        assert_eq!(
            verdict("unsafe fn f(x:*mut i32,y:*const i32){*x=*y+1;}"),
            SnapshotVerdict::Markable
        );
    }

    #[test]
    fn mir_producer_rejects_shared_read_after_mutable_write() {
        assert_eq!(
            verdict("unsafe fn f(x:*mut i32,y:*const i32)->i32{*x=1;*y}"),
            SnapshotVerdict::ReadAfterWrite
        );
    }
}
