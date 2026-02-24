use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

use super::ty_visit::TyVisitor;

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let krate = utils::ast::expanded_ast(tcx);

    if verbose {
        let ty_visitor = TyVisitor::new(tcx);
        let (_local_types, foreign_tys, union_tys) = ty_visitor.analyse_tys(tcx);

        println!("Foreign types identified:\n\t{}", {
            let mut for_vec = foreign_tys
                .iter()
                .map(|def_id| tcx.def_path_str(*def_id))
                .collect::<Vec<_>>();
            for_vec.sort();
            for_vec.join("\n\t")
        });

        println!("\nUnion Types: \n\t{}", {
            let mut for_vec = union_tys
                .iter()
                .map(|def_id| tcx.def_path_str(*def_id))
                .collect::<Vec<_>>();
            for_vec.sort();
            for_vec.join("\n\t")
        });
    }

    // visitor.visit_crate(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }
    str
}
