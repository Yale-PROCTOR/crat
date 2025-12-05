use rustc_ast::{Crate, Expr, NodeId, Stmt, StmtKind, mut_visit, mut_visit::MutVisitor};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_middle::{
    mir::{Location, Place},
    ty::TyCtxt,
};
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

#[allow(unused)]
struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    analysis: AnalysisResult<'tcx>,
    ast_to_hir: AstToHir,
    hir_to_thir: HirToThir,
    thir_to_mir: FxHashMap<LocalDefId, ThirToMir>,
    place_to_ident: FxHashMap<(LocalDefId, Place<'tcx>), String>,
}

impl MutVisitor for TransformVisitor<'_> {
    // fn visit_item(&mut self, item: &mut rustc_ast::ast::Item) {
    //     rustc_ast::mut_visit::walk_item(self, item);
    // }

    fn visit_expr(&mut self, expr: &mut Expr) {
        // if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&expr.id) {
        //     println!(
        //         "\tVisiting AST Expr: {:?}\n\t\tMIR --> {def_id:?}: {mir_locs:?}",
        //         expr
        //     );
        // }
        rustc_ast::mut_visit::walk_expr(self, expr);
    }

    fn flat_map_stmt(&mut self, s: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let stmts = mut_visit::walk_flat_map_stmt(self, s);
        // 그냥 이게 항상 성립하는지가 궁금해서 넣음
        assert_eq!(stmts.len(), 1);
        for s in &stmts {
            println!("Visiting Stmt: {}", pprust::stmt_to_string(s));
            if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&s.id) {
                println!("\tMIR --> {def_id:?}: {mir_locs:?}",);
            }

            match s.kind.clone() {
                StmtKind::Let(local) => {
                    let pat = local.pat;
                    // println!("\tLet Pat: {}", pprust::pat_to_string(&pat));
                    // println!("\tLet Pat: {:?}", pat);
                    match &pat.kind {
                        rustc_ast::PatKind::Ident(_, ident, _) => {
                            println!("\t{}", ident.as_str());
                        }
                        _ => {}
                    }
                    match &local.kind {
                        rustc_ast::LocalKind::Init(init_expr) => {
                            println!("\tLet Expr: {}", pprust::expr_to_string(init_expr));
                            if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&init_expr.id) {
                                println!("\t\tMIR --> {def_id:?}: {mir_locs:?}",);
                            }
                        }
                        _ => {}
                    }
                }
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                    println!("\tExpr: {}", pprust::expr_to_string(&expr));
                    if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&expr.id) {
                        println!("\t\tMIR --> {def_id:?}: {mir_locs:?}",);
                    }
                }
                _ => {}
            }
        }
        stmts
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
            place_to_ident: FxHashMap::default(),
        }
    }

    fn get_mir_func_locs_from_node(&self, node_id: &NodeId) -> Option<(LocalDefId, Vec<Location>)> {
        // let hir_expr = self.ast_to_hir.get_expr(node_id.clone(), self.tcx)?;
        let hir_id = self.ast_to_hir.local_map.get(&node_id)?;

        // let hir_id = hir_expr.hir_id;
        let def_id = hir_id.owner.def_id;

        let thir_to_mir = self.thir_to_mir.get(&def_id)?;

        // let thir_expr_id = self.hir_to_thir.exprs.get(&hir_expr.hir_id)?;
        let thir_expr_id = self.hir_to_thir.exprs.get(&hir_id)?;

        thir_to_mir
            .expr_to_locs
            .get(thir_expr_id)
            .cloned()
            .map(|locs| locs.to_vec())
            .map(|locs| (def_id, locs))
    }
}
