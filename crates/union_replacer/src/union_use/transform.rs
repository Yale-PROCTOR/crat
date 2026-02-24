use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

use super::{callgraph::collect_union_seed_functions, ty_visit::collect_foreign_and_union_types};

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let krate = utils::ast::expanded_ast(tcx);

    let (_, union_tys) = collect_foreign_and_union_types(&tcx, verbose);
    let _seed_functions = collect_union_seed_functions(tcx, &union_tys, verbose);

    // visitor.visit_crate(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }
    str
}
