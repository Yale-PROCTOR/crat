use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

use super::{
    analysis::analyze,
    callgraph::{build_union_call_contexts, collect_union_seed_functions},
    reverse_cfg::{analyze_reaching_writes, detect_overlapping_types},
    ty_visit::{collect_local_union_types, collect_union_related_types},
};

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    // for debug
    let use_optimized_mir = false;
    let print_mir = false;

    // collect union types and build call graphs
    let (union_tys, ty_visitor) = collect_local_union_types(&tcx, verbose);
    let related_types_map = collect_union_related_types(&tcx, &union_tys, &ty_visitor, verbose);
    let seed_functions = collect_union_seed_functions(tcx, &union_tys, verbose);
    let call_contexts = build_union_call_contexts(
        tcx,
        &seed_functions,
        &related_types_map,
        use_optimized_mir,
        verbose,
    );

    // analyze union uses and detect overlapping unions
    let union_uses = analyze(
        tcx,
        &union_tys,
        &call_contexts,
        print_mir,
        use_optimized_mir,
        verbose,
    );
    let reaching_writes =
        analyze_reaching_writes(tcx, &union_uses, &call_contexts, use_optimized_mir);
    let overlapping_tys = detect_overlapping_types(tcx, &union_uses, &reaching_writes, verbose);

    if !overlapping_tys.is_empty() {
        println!("\noverlapping:");
        for union_ty in overlapping_tys {
            println!("{}", tcx.def_path_str(union_ty));
        }
    }

    let str = pprust::crate_to_string_for_macros(&krate);
    if true {
        println!("\n{str}");
    }
    str
}
