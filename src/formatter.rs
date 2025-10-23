use rustc_middle::ty::TyCtxt;

use crate::ast_utils;

pub fn format(tcx: TyCtxt<'_>) {
    let res = ast_utils::transform_ast(|_| true, tcx);
    res.apply();
}
