use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

use super::{
    analysis::analyze,
    callgraph::{
        CondensationGraph, build_union_callgraphs, callgraphs_to_condensation_graphs,
        collect_union_seed_functions,
    },
    ty_visit::{collect_local_union_types, collect_union_related_types},
};

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let krate = utils::ast::expanded_ast(tcx);

    let (union_tys, ty_visitor) = collect_local_union_types(&tcx, verbose);
    let related_types_map = collect_union_related_types(&tcx, &union_tys, &ty_visitor, verbose);
    let seed_functions = collect_union_seed_functions(tcx, &union_tys, verbose);
    let callgraphs = build_union_callgraphs(tcx, &seed_functions, &related_types_map, verbose);
    let condensation_graphs = callgraphs_to_condensation_graphs(&callgraphs);

    if verbose {
        print_condensation_graphs(tcx, &condensation_graphs);
    }

    analyze(tcx, verbose, false);

    let str = pprust::crate_to_string_for_macros(&krate);
    if false {
        println!("\n{str}");
    }
    str
}

fn print_condensation_graphs(
    tcx: TyCtxt<'_>,
    condensation_graphs: &FxHashMap<LocalDefId, CondensationGraph>,
) {
    println!("\nCondensation Graphs:");
    let mut union_tys = condensation_graphs.keys().copied().collect::<Vec<_>>();
    union_tys.sort_by_key(|def_id| tcx.def_path_str(*def_id));
    for union_ty in union_tys {
        if let Some(graph) = condensation_graphs.get(&union_ty) {
            println!("\n{}\n{:?}", tcx.def_path_str(union_ty), graph);
        }
    }
}
