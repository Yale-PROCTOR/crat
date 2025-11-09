use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

pub fn replace_unions(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let analysis_result = super::analysis::analyze(tcx);
    println!("{analysis_result:?}");

    pprust::crate_to_string_for_macros(&krate)
}
