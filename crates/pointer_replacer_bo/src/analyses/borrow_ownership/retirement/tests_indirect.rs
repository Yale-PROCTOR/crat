//! Source-proven indirect targets: retirement routes versus a read-only twin.
//! Fixtures are compiled, never executed. No MayRetain fact invents a free.

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::{Location, Rvalue, StatementKind, TerminatorKind},
    ty::TyKind,
};

use super::tests::accepts;
use crate::{
    analyses::{
        borrow_ownership::source_events::{self, SourceEvents, SourceRole},
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

struct Inspection {
    events: SourceEvents,
    indirect: Location,
}

fn inspect(code: &str, target_name: &str, foreign: bool) -> Inspection {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let callers: Vec<_> = functions
            .iter()
            .copied()
            .filter(|function| tcx.item_name(function.to_def_id()).as_str() == "caller")
            .collect();
        assert_eq!(callers.len(), 1, "exact source caller");
        let body = tcx
            .mir_drops_elaborated_and_const_checked(callers[0])
            .borrow();
        let mut indirect = Vec::new();
        let mut resolved_assignments = 0;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                let StatementKind::Assign(box (_, Rvalue::Cast(_, operand, target_ty))) =
                    &statement.kind
                else {
                    continue;
                };
                if !matches!(target_ty.kind(), TyKind::FnPtr(..)) {
                    continue;
                }
                let TyKind::FnDef(target, _) = operand.ty(&*body, tcx).kind() else { continue };
                if tcx.item_name(*target).as_str() != target_name {
                    continue;
                }
                let local = target.as_local().expect("fixture-owned target declaration");
                assert_eq!(
                    matches!(
                        tcx.hir_node_by_def_id(local),
                        rustc_hir::Node::ForeignItem(_)
                    ),
                    foreign,
                    "target class must come from compiler identity, not its name"
                );
                resolved_assignments += 1;
            }
            let Some(call) = data.terminator().as_call(tcx) else { continue };
            if matches!(call.func, CallKind::Closure) {
                let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    panic!("fixture requires an original indirect call");
                };
                assert!(
                    func.constant().is_none(),
                    "the call operand must remain indirect"
                );
                assert!(matches!(func.ty(&*body, tcx).kind(), TyKind::FnPtr(..)));
                assert_eq!(call.args.len(), 1);
                indirect.push(Location {
                    block,
                    statement_index: data.statements.len(),
                });
            }
        }
        assert_eq!(
            resolved_assignments, 1,
            "one compiler-proven function-pointer target assignment"
        );
        assert_eq!(
            indirect.len(),
            1,
            "MIR must preserve the indirect CallKind::Closure witness"
        );
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        Inspection {
            events: source_events::collect(&program),
            indirect: indirect[0],
        }
    })
    .unwrap_or_else(|error| error.raise())
}

#[test]
fn e5_p_d_indirect_local_release_reaches_the_protected_caller() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
unsafe fn release(raw: *mut u8) { free(raw); }
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    let target: unsafe fn(*mut u8) = release;
    target(p as *mut u8);
    value
}
"#;
    let inspection = inspect(CODE, "release", false);
    assert!(
        inspection
            .events
            .retirements
            .values()
            .any(|event| event.key.function == "release" && event.key.role == SourceRole::Free),
        "the original local body contains the source free"
    );
    assert!(
        !accepts(CODE, &[("caller", 1, 0)]),
        "the proven local target must route its retirement or decline explicitly; indirect={:?}, inventory={:?}",
        inspection.indirect,
        inspection.events
    );
}

#[test]
fn e5_p_d_foreign_free_function_pointer_needs_retirement_coverage() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    let target: unsafe extern "C" fn(*mut u8) = free;
    target(p as *mut u8);
    value
}
"#;
    let inspection = inspect(CODE, "free", true);
    // No assertion prescribes an invented direct event. A bounded producer may
    // instead report a typed coverage gap for this proven ForeignC target.
    assert!(
        !accepts(CODE, &[("caller", 1, 0)]),
        "an exact ForeignC free target requires an event or typed decline; indirect={:?}, inventory={:?}",
        inspection.indirect,
        inspection.events
    );
}

#[test]
fn e5_p_d_known_nonretiring_indirect_read_does_not_invent_retirement() {
    const CODE: &str = r#"
unsafe fn read_value(raw: *mut u8) -> u8 { *raw }
pub unsafe fn caller(p: *const u8) -> u8 {
    let before = *p;
    let target: unsafe fn(*mut u8) -> u8 = read_value;
    let after = target(p as *mut u8);
    before + after
}
"#;
    let inspection = inspect(CODE, "read_value", false);
    assert!(
        inspection
            .events
            .retirements
            .values()
            .all(|event| !matches!(event.key.role, SourceRole::Free | SourceRole::ReallocOld)),
        "indirect/opaque provenance is not evidence of a retirement"
    );
    assert!(
        accepts(CODE, &[("caller", 1, 0)]),
        "the known local shared-read target preserves ordinary semantics"
    );
}
