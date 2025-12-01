use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_middle::{mir, ty::TyCtxt};
use utils::ir::ThirToMir;

use crate::rustc_mir_dataflow::Analysis as _;

pub struct UnusedAssignments {
    pub thir_to_mir: FxHashMap<LocalDefId, ThirToMir>,
    pub dead_assignments: FxHashSet<(LocalDefId, mir::Location)>,
}

pub fn find_unused_assignments(tcx: TyCtxt<'_>) -> UnusedAssignments {
    let mut thir_to_mirs = FxHashMap::default();
    let mut dead_assignments = FxHashSet::default();

    for def_id in tcx.hir_body_owners() {
        if tcx.def_kind(def_id) != DefKind::Fn {
            continue;
        }
        if tcx.item_name(def_id.to_def_id()).as_str() == "main" {
            continue;
        }
        if tcx.def_path_str(def_id).contains("c_lib::") {
            continue;
        }

        let thir_to_mir = utils::ir::map_thir_to_mir(def_id, false, tcx);
        thir_to_mirs.insert(def_id, thir_to_mir);

        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        let mut cursor = rustc_mir_dataflow::impls::MaybeLiveLocals
            .iterate_to_fixpoint(tcx, &body, None)
            .into_results_cursor(&body);

        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            for (i, stmt) in bbd.statements.iter().enumerate() {
                if let mir::StatementKind::Assign(box (place, _)) = &stmt.kind
                    && let Some(local) = place.as_local()
                {
                    let loc = mir::Location {
                        block: bb,
                        statement_index: i,
                    };
                    cursor.seek_before_primary_effect(loc);
                    let lives = cursor.get();
                    if !lives.contains(local) {
                        dead_assignments.insert((def_id, loc));
                    }
                }
            }
            let terminator = bbd.terminator();
            if let mir::TerminatorKind::Call {
                destination,
                target: Some(target),
                ..
            } = terminator.kind
            {
                let loc = mir::Location {
                    block: target,
                    statement_index: 0,
                };
                cursor.seek_after_primary_effect(loc);
                let lives = cursor.get();
                if let Some(local) = destination.as_local()
                    && !lives.contains(local)
                {
                    let loc = mir::Location {
                        block: bb,
                        statement_index: bbd.statements.len(),
                    };
                    dead_assignments.insert((def_id, loc));
                }
            }
        }
    }

    UnusedAssignments {
        thir_to_mir: thir_to_mirs,
        dead_assignments,
    }
}
