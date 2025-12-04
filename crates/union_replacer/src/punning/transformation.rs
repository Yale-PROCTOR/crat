use rustc_ast::{Crate, Expr, mut_visit::MutVisitor};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_middle::{mir::Location, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;
use utils::ir::{AstToHir, HirToThir, ThirToMir};

use super::analysis::AnalysisResult;

pub fn replace_unions(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);

    let analysis_result = super::analysis::analyze(tcx);
    let mut visitor = TransformVisitor::new(tcx, &mut krate, analysis_result);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    println!("{:?}", visitor.analysis);
    visitor.visit_crate(&mut krate);

    // let str = pprust::crate_to_string_for_macros(&krate);
    // println!("{}", str);
    // str
    pprust::crate_to_string_for_macros(&krate)
}

struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    analysis: AnalysisResult<'tcx>,
    ast_to_hir: AstToHir,
    hir_to_thir: HirToThir,
    thir_to_mir: FxHashMap<LocalDefId, ThirToMir>,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item(&mut self, item: &mut rustc_ast::ast::Item) {
        rustc_ast::mut_visit::walk_item(self, item);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_expr(expr) {
            println!("Visiting expr: {def_id:?}: {mir_locs:?}");
        }
        rustc_ast::mut_visit::walk_expr(self, expr);
    }
}

impl<'a> TransformVisitor<'a> {
    fn new(tcx: TyCtxt<'a>, krate: &mut Crate, analysis: AnalysisResult<'a>) -> Self {
        let ast_to_hir = utils::ast::make_ast_to_hir(krate, tcx);
        let hir_to_thir = utils::ir::map_hir_to_thir(tcx);
        let mut thir_to_mir = FxHashMap::default();
        for def_id in tcx.hir_body_owners() {
            thir_to_mir.insert(def_id, utils::ir::map_thir_to_mir(def_id, false, tcx));
        }

        Self {
            tcx,
            analysis,
            ast_to_hir,
            hir_to_thir,
            thir_to_mir,
        }
    }

    fn get_mir_func_locs_from_expr(&self, expr: &Expr) -> Option<(LocalDefId, Vec<Location>)> {
        let expr_id = expr.id;
        let hir_expr = self.ast_to_hir.get_expr(expr_id, self.tcx)?;

        let hir_id = hir_expr.hir_id;
        let owner_id = hir_id.owner.def_id;

        let thir_to_mir = self.thir_to_mir.get(&owner_id)?;

        let thir_expr_id = self.hir_to_thir.exprs.get(&hir_expr.hir_id)?;

        thir_to_mir
            .expr_to_locs
            .get(thir_expr_id)
            .cloned()
            .map(|locs| locs.to_vec())
            .map(|locs| (owner_id, locs))
    }
}
