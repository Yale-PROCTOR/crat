use rustc_middle::ty::TyCtxt;

pub fn format(tcx: TyCtxt<'_>) {
    let res = utils::ast::transform_ast(|_| true, tcx);
    res.apply();
}
