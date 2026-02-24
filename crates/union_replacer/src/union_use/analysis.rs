// use etrace::some_or;
use rustc_hash::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{Body, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::{DefId, LocalDefId};

pub type AnalysisMap = ();
pub struct AnalysisResult {
    pub _map: FxHashMap<LocalDefId, AnalysisMap>,
}

fn collect_union_uses_map<'a>(tcx: TyCtxt<'a>, print_mir: bool) -> () {
    for def_id in tcx.hir_body_owners() {
        let _ = print_local_body(def_id, tcx, print_mir);
    }
}

/// Print the MIR body of a local function definition.
/// Returns a list of function DefIds called within the body.
fn print_local_body<'a>(
    def_id: LocalDefId,
    tcx: TyCtxt<'a>,
    print_mir: bool,
) -> Option<Vec<DefId>> {
    let mut func_calls = Vec::new();
    if tcx.def_kind(def_id) != DefKind::Fn {
        return None;
    }
    if print_mir {
        println!("\nDEF: {def_id:?}");
    }

    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body: &Body<'_> = &body.borrow();
    // let body = if tcx.is_mir_available(def_id) {
    //     tcx.optimized_mir(def_id)
    // } else {
    //     return None;
    // };

    if print_mir {
        body.args_iter().for_each(|arg| {
            println!("\tARG: {arg:?} -> {:?}", body.local_decls[arg].ty);
        });
    }
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        if print_mir {
            println!("\tBB: {bb:?}");
        }
        for (stmt_idx, stmt) in bbd.statements.iter().enumerate() {
            if print_mir && let StatementKind::Assign(box (place, _)) = stmt.kind {
                let ty = place.ty(body, tcx).ty;
                println!("\t\tSTMT {stmt_idx}: {stmt:?}\n\t\t{ty:?}\n");
            } else {
                // println!("\t\tSTMT {stmt_idx}: {stmt:?}\n");
            }
        }
        if print_mir {
            println!("\t\tTERM: {:?}", bbd.terminator().kind);
            if let TerminatorKind::Call {
                func, destination, ..
            } = &bbd.terminator().kind
            {
                let ty = destination.ty(body, tcx).ty;
                println!("\t\t{ty:?}\n");

                let func_def_id = func.const_fn_def().unwrap().0;
                func_calls.push(func_def_id);
            }
        }
    }
    Some(func_calls)
}

fn _print_foreign_body<'a>(def_id: DefId, tcx: TyCtxt<'a>, print_mir: bool) -> Option<Vec<DefId>> {
    let mut func_calls = Vec::new();

    if print_mir {
        println!("\nDEF: {def_id:?}");
    }
    let body = if tcx.is_mir_available(def_id) {
        tcx.optimized_mir(def_id)
    } else {
        return None;
    };

    if print_mir {
        body.args_iter().for_each(|arg| {
            println!("\tARG: {arg:?} -> {:?}", body.local_decls[arg].ty);
        });
    }
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        if print_mir {
            println!("\tBB: {bb:?}");
        }
        for (stmt_idx, stmt) in bbd.statements.iter().enumerate() {
            if print_mir && let StatementKind::Assign(box (place, _)) = stmt.kind {
                let ty = place.ty(body, tcx).ty;
                println!("\t\tSTMT {stmt_idx}: {stmt:?}\n\t\t{ty:?}\n");
            }
        }
        if print_mir {
            println!("\t\tTERM: {:?}", bbd.terminator().kind);
            if let TerminatorKind::Call {
                func, destination, ..
            } = &bbd.terminator().kind
            {
                let ty = destination.ty(body, tcx).ty;
                println!("\t\t{ty:?}\n");

                let func_def_id = func.const_fn_def().unwrap().0;
                func_calls.push(func_def_id);
            }
        }
    }
    Some(func_calls)
}

pub fn analyze(tcx: TyCtxt, verbose: bool, print_mir: bool) -> AnalysisResult {
    let _ = collect_union_uses_map(tcx, print_mir);
    let result_map = FxHashMap::default();

    if verbose {
        println!("\nUnion use analysis result:");
    }

    AnalysisResult { _map: result_map }
}
