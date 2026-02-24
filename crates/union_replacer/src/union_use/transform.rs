use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

use super::{callgraph::collect_union_seed_functions, ty_visit::collect_foreign_and_union_types};

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let krate = utils::ast::expanded_ast(tcx);

    let (_, union_tys) = collect_foreign_and_union_types(&tcx, verbose);
    let seed_functions = collect_union_seed_functions(tcx, &union_tys);

    println!("Union seed functions:\n\t{}", {
        let names = seed_functions
            .iter()
            .map(|(ty, funcs)| {
                let ty_name = tcx.def_path_str(*ty);
                let func_names = funcs
                    .iter()
                    .map(|def_id| tcx.def_path_str(*def_id))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{ty_name} -> {func_names}")
            })
            .collect::<Vec<_>>();
        names.join("\n\t")
    });

    // visitor.visit_crate(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }
    str
}
