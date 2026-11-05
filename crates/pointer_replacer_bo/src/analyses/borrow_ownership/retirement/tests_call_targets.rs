//! Target propagation and completeness at original indirect call locations.

use std::collections::BTreeSet;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::{
        Location, ProjectionElem, Rvalue, START_BLOCK, StatementKind, TerminatorKind,
        VarDebugInfoContents,
    },
    ty::TyKind,
};

use crate::{
    analyses::borrow_ownership::source_events::{self, SourceRole},
    utils::rustc::RustProgram,
};

const BODIES: &str = r#"
unsafe extern "C" { fn free(raw: *mut u8); }
unsafe fn release(raw: *mut u8) { free(raw); }
unsafe fn noop(_raw: *mut u8) {}
"#;

struct Inspection {
    known: BTreeSet<String>,
    unknown: bool,
    assignments: BTreeSet<String>,
    source_frees: usize,
    routed_release: bool,
    addressed_target: bool,
    projected_store: bool,
}

fn inspect(code: &str) -> Inspection {
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
        let caller = *functions
            .iter()
            .find(|function| tcx.item_name(function.to_def_id()).as_str() == "caller")
            .unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let target = body
            .var_debug_info
            .iter()
            .find_map(|info| {
                if info.name.as_str() != "target" {
                    return None;
                }
                let VarDebugInfoContents::Place(place) = info.value else { return None };
                place.as_local()
            })
            .expect("exact named function-pointer cell");
        let mut reachable = BTreeSet::new();
        let mut pending = vec![START_BLOCK];
        while let Some(block) = pending.pop() {
            if reachable.insert(block) {
                pending.extend(body.basic_blocks[block].terminator().successors());
            }
        }
        let mut calls = Vec::new();
        let mut assignments = BTreeSet::new();
        let mut addressed_target = false;
        let mut projected_store = false;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for statement in &data.statements {
                let StatementKind::Assign(box (destination, value)) = &statement.kind else {
                    continue;
                };
                projected_store |= destination
                    .projection
                    .iter()
                    .any(|projection| matches!(projection, ProjectionElem::Deref));
                if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = value {
                    addressed_target |= place.as_local() == Some(target);
                }
                let operand = match value {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand,
                    _ => continue,
                };
                if let TyKind::FnDef(definition, _) = operand.ty(&*body, tcx).kind() {
                    assignments.insert(tcx.def_path_str(*definition));
                }
            }
            let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) =
                &data.terminator().kind
            else {
                continue;
            };
            if func.constant().is_none() && matches!(func.ty(&*body, tcx).kind(), TyKind::FnPtr(..))
            {
                assert!(
                    reachable.contains(&block),
                    "the inspected indirect call must be reachable"
                );
                calls.push(Location {
                    block,
                    statement_index: data.statements.len(),
                });
            }
        }
        assert_eq!(calls.len(), 1, "exact original indirect FnPtr call");
        let location = calls[0];
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let events = source_events::collect(&program);
        let targets = events
            .call_targets
            .get(&(caller, location))
            .expect("collected target fact for original call");
        Inspection {
            known: targets
                .known
                .iter()
                .map(|target| tcx.def_path_str(*target))
                .collect(),
            unknown: targets.unknown,
            assignments,
            source_frees: events
                .retirements
                .keys()
                .filter(|key| key.role == SourceRole::Free)
                .count(),
            routed_release: events.calls.iter().any(|route| {
                route.caller == "caller"
                    && route.block == location.block.as_u32()
                    && route.callee == "release"
                    && route
                        .events
                        .iter()
                        .any(|key| key.function == "release" && key.role == SourceRole::Free)
            }),
            addressed_target,
            projected_store,
        }
    })
    .unwrap_or_else(|error| error.raise())
}

fn names(expected: &[&str]) -> BTreeSet<String> {
    expected.iter().map(|name| (*name).to_owned()).collect()
}

#[test]
fn e5_p_call_target_strong_overwrite_removes_the_old_release() {
    let code = format!(
        "{BODIES} pub unsafe fn caller(p: *const u8) -> u8 {{ let value = *p; let mut target: unsafe fn(*mut u8) = release; target = noop; target(p as *mut u8); value }}"
    );
    let found = inspect(&code);
    assert_eq!(
        found.assignments,
        names(&["release", "noop"]),
        "both source assignments must survive MIR construction"
    );
    assert_eq!(found.known, names(&["noop"]));
    assert!(!found.unknown);
    assert_eq!(
        found.source_frees, 1,
        "release's body remains in the source inventory"
    );
    assert!(
        !found.routed_release,
        "a body-only free is not an executed target of this call"
    );
    assert!(super::tests::accepts(&code, &[("caller", 1, 0)]));
}

#[test]
fn e5_p_call_target_branch_union_keeps_both_complete_alternatives() {
    let code = format!(
        "{BODIES} pub unsafe fn caller(p: *const u8, choose: bool) -> u8 {{ let value = *p; let mut target: unsafe fn(*mut u8) = noop; if choose {{ target = release; }} target(p as *mut u8); value }}"
    );
    let found = inspect(&code);
    assert_eq!(found.known, names(&["noop", "release"]));
    assert!(!found.unknown);
    assert!(
        found.routed_release,
        "the possible free must reach this exact indirect call"
    );
    assert!(!super::tests::accepts(&code, &[("caller", 1, 0)]));
}

#[test]
fn e5_p_call_target_unknown_parameter_alternative_exports_missing_availability() {
    const CODE: &str = r#"
unsafe fn noop(_raw: *mut u8) {}
pub unsafe fn caller(p: *const u8, other: unsafe fn(*mut u8), choose: bool) -> u8 {
    let value = *p;
    let mut target: unsafe fn(*mut u8) = noop;
    if choose { target = other; }
    target(p as *mut u8);
    value
}
"#;
    let found = inspect(CODE);
    assert_eq!(found.known, names(&["noop"]));
    assert!(
        found.unknown,
        "a known alternative does not make the set complete"
    );
    assert_eq!(
        found.source_frees, 0,
        "unknown coverage must not invent a ForeignC free"
    );
    assert!(!found.routed_release);
    assert!(
        super::tests::accepts(CODE, &[("caller", 1, 0)]),
        "without an identified retirement, unknown target availability does not introduce an opaque-call admission rule"
    );
}

#[test]
fn e5_p_call_target_alias_store_invalidates_closed_target_knowledge() {
    let code = format!(
        "{BODIES} pub unsafe fn caller(p: *const u8) -> u8 {{ let value = *p; let mut target: unsafe fn(*mut u8) = noop; let alias = &raw mut target; *alias = release; target(p as *mut u8); value }}"
    );
    let found = inspect(&code);
    assert!(
        found.addressed_target && found.projected_store,
        "the original target cell must be overwritten through its address"
    );
    assert_eq!(found.assignments, names(&["noop", "release"]));
    assert!(
        found.unknown,
        "a projected store cannot leave a complete stale no-op target"
    );
    assert!(
        found.known.contains("release") && found.routed_release,
        "the compiler-visible replacement is a possible retiring target, independently of the unknown remainder"
    );
    assert!(
        !super::tests::accepts(&code, &[("caller", 1, 0)]),
        "the overwritten function cell can retire the caller's protected input"
    );
}

#[test]
fn e5_p_call_target_loop_union_is_finite_and_keeps_the_retiring_alternative() {
    let code = format!(
        "{BODIES} pub unsafe fn caller(p: *const u8, turns: u8) -> u8 {{ let value = *p; let mut target: unsafe fn(*mut u8) = noop; let mut count = 0u8; while count < turns {{ let next: unsafe fn(*mut u8) = release; target = next; count += 1; }} target(p as *mut u8); value }}"
    );
    let found = inspect(&code);
    assert_eq!(found.known, names(&["noop", "release"]));
    assert!(!found.unknown);
    assert!(
        found.routed_release,
        "loop convergence must preserve a reachable free alternative"
    );
    assert!(!super::tests::accepts(&code, &[("caller", 1, 0)]));
}
