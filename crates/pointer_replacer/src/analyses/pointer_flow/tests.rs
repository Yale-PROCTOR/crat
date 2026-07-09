use rustc_hash::FxHashSet;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::Local;

use super::{
    PointerFlowResult,
    collector::analyze_body_with_summaries,
    field_access::{FieldAccess, FieldAccessKind, FieldAccessReject, FieldAccessRejectKind},
    graph::BaseId,
    pointer_flow_analysis,
};
use crate::utils::rustc::RustProgram;

// local copy of the array_local_provenance test helper; test modules cannot
// import each other's private items
fn build_rust_program(tcx: rustc_middle::ty::TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = vec![];
    let mut structs = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn analyze_single(code: &str, fn_name: &str) -> PointerFlowResult {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = build_rust_program(tcx);
        let did = program
            .functions
            .iter()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == fn_name)
            .unwrap_or_else(|| panic!("missing function {fn_name}"));
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        analyze_body_with_summaries(tcx, did, &body, &FxHashSet::default(), None)
    })
    .unwrap()
}

fn analyze_interprocedural(code: &str, fn_name: &str) -> PointerFlowResult {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = build_rust_program(tcx);
        let results = pointer_flow_analysis(&program, &FxHashSet::default());
        let did = program
            .functions
            .iter()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == fn_name)
            .unwrap_or_else(|| panic!("missing function {fn_name}"));
        results.get(&did).cloned().expect("missing analysis result")
    })
    .unwrap()
}

fn param_base(result: &PointerFlowResult, param_index: usize) -> BaseId {
    let local = Local::from_usize(param_index + 1);
    let slot = result
        .slot_table
        .local_head_slot(local)
        .expect("param has no pointer slot");
    BaseId::Param { local, slot }
}

fn accesses_reaching_param(result: &PointerFlowResult, param_index: usize) -> Vec<FieldAccess> {
    let base = param_base(result, param_index);
    result
        .field_accesses
        .iter()
        .filter(|access| {
            result
                .provenance
                .reachable_bases
                .get(&access.node)
                .is_some_and(|bases| bases.contains(&base))
        })
        .cloned()
        .collect()
}

fn rejects_reaching_param(
    result: &PointerFlowResult,
    param_index: usize,
) -> Vec<FieldAccessReject> {
    let base = param_base(result, param_index);
    result
        .field_rejects
        .iter()
        .filter(|reject| {
            result
                .provenance
                .reachable_bases
                .get(&reject.node)
                .is_some_and(|bases| bases.contains(&base))
        })
        .cloned()
        .collect()
}

#[test]
fn no_events_without_field_uses() {
    let result = analyze_single(
        r#"
pub unsafe fn passthrough(p: *mut i32) -> *mut i32 {
    p
}
"#,
        "passthrough",
    );
    assert!(result.field_accesses.is_empty());
    assert!(result.field_rejects.is_empty());
}
