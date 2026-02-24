use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

use super::{
    callgraph::{build_union_callgraphs, collect_union_seed_functions},
    ty_visit::{collect_foreign_and_union_types, collect_union_related_types},
};

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let krate = utils::ast::expanded_ast(tcx);

    let (_, union_tys) = collect_foreign_and_union_types(&tcx, verbose);
    let related_types_map = collect_union_related_types(&tcx, &union_tys, verbose);
    let seed_functions = collect_union_seed_functions(tcx, &union_tys, verbose);
    let _callgraphs = build_union_callgraphs(tcx, &seed_functions, &related_types_map, verbose);

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }
    str
}
