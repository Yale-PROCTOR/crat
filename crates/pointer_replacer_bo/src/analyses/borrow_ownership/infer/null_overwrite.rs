use rustc_middle::mir::{StatementKind, TerminatorKind};

use super::*;
use crate::analyses::borrow_ownership::{ownership_evidence, source_events};

/// A direct pointer destination whose old value is null on every reaching path.
/// The proof is taken before the write; nullable types and allocation results
/// do not establish that the previous value is empty.
pub(super) fn sites<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> FxHashSet<Location> {
    let addressed = source_events::addressed_locals(body);
    let entries = source_events::null_entries(body, &addressed, tcx);
    let mut sites = FxHashSet::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(mut state) = entries[block.as_usize()].clone() else { continue };
        let null_pointer = |place: Place<'_>, state: &[bool]| {
            place.projection.is_empty()
                && body.local_decls[place.local].ty.is_raw_ptr()
                && state[place.local.as_usize()]
        };
        for (statement_index, statement) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, _)) = statement.kind
                && null_pointer(place, &state)
            {
                sites.insert(Location {
                    block,
                    statement_index,
                });
            }
            source_events::transfer_statement(&statement.kind, &mut state, &addressed, tcx);
        }
        if let TerminatorKind::Call { destination, .. } = data.terminator().kind
            // The callee can write an exposed destination before storing its return value.
            && !addressed.contains(&destination.local)
            && null_pointer(destination, &state)
        {
            sites.insert(Location {
                block,
                statement_index: data.statements.len(),
            });
        }
    }
    sites
}

pub(super) fn require_empty(database: &mut impl Database, old: Var, null_old: Option<Var>) {
    if Some(old) == null_old {
        // This is emptiness of the value, not a claim that its SSA ownership
        // bit is false. The same null version may own vacuously at a phi join.
        ownership_evidence::record("null-overwrite", &[old], None, None);
    } else {
        database.push_assume::<crate::analyses::borrow_ownership::ssa::constraint::Debug>(
            (),
            old,
            false,
        );
    }
}

#[cfg(test)]
mod tests {
    use rustc_middle::mir::VarDebugInfoContents;

    use super::*;

    #[test]
    fn direct_call_destinations_need_an_unexposed_null_local() {
        ::utils::compilation::run_compiler_on_str(
            r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn make() -> *mut u8 { malloc(8) }
unsafe fn fill(cell: *mut *mut u8) -> *mut u8 { *cell = malloc(8); malloc(16) }
pub unsafe fn plain(flag: bool) {
    let mut p = core::ptr::null_mut();
    if flag { p = make(); }
    free(p);
}
pub unsafe fn exposed(flag: bool) {
    let mut p = core::ptr::null_mut();
    if flag { p = fill(&raw mut p); }
    free(p);
}
"#,
            |tcx| {
                for (name, callee, expected) in
                    [("plain", "make", true), ("exposed", "fill", false)]
                {
                    let function = tcx
                        .hir_body_owners()
                        .find(|function| tcx.item_name(function.to_def_id()).as_str() == name)
                        .unwrap();
                    let mut body = tcx
                        .mir_drops_elaborated_and_const_checked(function)
                        .borrow()
                        .clone();
                    let local = body
                        .var_debug_info
                        .iter()
                        .find_map(|info| match info.value {
                            VarDebugInfoContents::Place(place) if info.name.as_str() == "p" => {
                                place.as_local()
                            }
                            _ => None,
                        })
                        .unwrap();
                    let block = body
                        .basic_blocks
                        .iter_enumerated()
                        .find_map(|(block, data)| {
                            let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                                return None;
                            };
                            func.const_fn_def()
                                .is_some_and(|(did, _)| tcx.item_name(did).as_str() == callee)
                                .then_some(block)
                        })
                        .unwrap();
                    // Source MIR uses a return temporary then copies it into p. Construct
                    // the direct destination in memory to exercise the call-time proof.
                    let TerminatorKind::Call { destination, .. } =
                        &mut body.basic_blocks.as_mut()[block].terminator_mut().kind
                    else {
                        unreachable!()
                    };
                    *destination = Place::from(local);
                    let location = Location {
                        block,
                        statement_index: body.basic_blocks[block].statements.len(),
                    };
                    assert_eq!(sites(tcx, &body).contains(&location), expected, "{name}");
                }
            },
        )
        .unwrap();
    }
}
