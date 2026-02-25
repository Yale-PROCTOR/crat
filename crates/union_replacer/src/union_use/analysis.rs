// use etrace::some_or;
use points_to::andersen;
use rustc_hash::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{Body, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::{DefId, LocalDefId};
use typed_arena::Arena;
use utils::ty_shape;

pub struct AnalysisResult {
    pub _map: (),
}

pub fn analyze(tcx: TyCtxt, verbose: bool, _print_mir: bool) -> AnalysisResult {
    let use_optimized_mir = true;
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx, use_optimized_mir);

    let points_to_config = andersen::Config {
        use_optimized_mir,
        c_exposed_fns: FxHashSet::default(),
    };

    let pre = andersen::pre_analyze(&points_to_config, &tss, tcx);

    let solutions = andersen::analyze(&points_to_config, &pre, &tss, tcx);

    let _may_points_to = andersen::post_analyze(&points_to_config, pre, solutions, &tss, tcx);

    if verbose {
        println!("\nUnion use analysis result:");
    }

    AnalysisResult { _map: () }
}

/// Print the MIR body of a local function definition.
/// Return: a list of function DefIds called within the body.
fn _print_local_body<'a>(
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

/// Print the MIR body of a foreign function definition.
/// Return: a list of function DefIds called within the body.
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
