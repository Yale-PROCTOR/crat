use rustc_middle::ty::TyCtxt;

use crate::ast_utils;

pub fn format(tcx: TyCtxt<'_>) {
    let res = ast_utils::transform_ast(|_| true, tcx);
    res.apply();
}

pub fn formatted(tcx: TyCtxt<'_>) -> String {
    let r = tcx.crate_for_resolver(()).borrow();
    let (ref krate, _) = *r;
    rustc_ast_pretty::pprust::crate_to_string_for_macros(krate)
}
