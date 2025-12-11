use rustc_ast::{Crate, Expr, NodeId, Stmt, StmtKind, mut_visit, mut_visit::MutVisitor};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_middle::{mir::Location, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;
use utils::ir::{AstToHir, HirToThir, ThirToMir};

use super::analysis::AnalysisResult;

pub fn replace_unions(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);

    let analysis_result = super::analysis::analyze(tcx);
    println!("{analysis_result:?}");
    let mut visitor = TransformVisitor::new(tcx, &mut krate, analysis_result);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    visitor.visit_crate(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    println!("\n{str}");
    str
    // pprust::crate_to_string_for_macros(&krate)
}

#[allow(unused)]
struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    hir_to_thir: HirToThir,
    thir_to_mir: FxHashMap<LocalDefId, ThirToMir>,
    transform_info: FxHashMap<LocalDefId, Vec<TransformInfo>>,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&expr.id) {
            println!(
                "\tExpr: {}\n\t\tMIR --> {def_id:?}: {mir_locs:?}",
                pprust::expr_to_string(expr)
            );
        }
        rustc_ast::mut_visit::walk_expr(self, expr);
    }

    fn flat_map_stmt(&mut self, s: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let stmts = mut_visit::walk_flat_map_stmt(self, s);
        let mut new_stmts = smallvec::SmallVec::<[Stmt; 1]>::new();
        for s in &stmts {
            match s.kind.clone() {
                // Init
                StmtKind::Let(local) => match &local.kind {
                    rustc_ast::LocalKind::Init(init_expr) => {
                        let pat = local.pat;
                        if let Some((def_id, mir_locs)) =
                            self.get_mir_func_locs_from_node(&init_expr.id)
                        {
                            let infos = self.transform_info.get_mut(&def_id);
                            if let Some(infos) = infos {
                                let mut found = false;
                                for info in infos {
                                    let init_loc = info.init_loc;
                                    // Init Location Found
                                    if mir_locs.contains(&init_loc) {
                                        found = true;
                                        let ident = match &pat.kind {
                                            rustc_ast::PatKind::Ident(_, ident, _) => {
                                                Some(ident.as_str().to_string())
                                            }
                                            _ => None,
                                        };
                                        info.ident = ident.clone();

                                        // Transform Init
                                        // TODO: from/to_bytes
                                        // TODO: mut tag
                                        if let Some(replacable) = info.write_locs.get(&init_loc) {
                                            if *replacable {
                                                // Replacable Init
                                                new_stmts.push(utils::stmt!(
                                                    "let mut {}_bytes: [u8; {}] = ({}).to_bytes();",
                                                    ident.unwrap(),
                                                    info.size,
                                                    pprust::expr_to_string(init_expr)
                                                ));
                                            } else {
                                                // Non-Replacable Init
                                                new_stmts.push(s.clone());
                                                new_stmts.push(utils::stmt!(
                                                    "let mut {}_bytes: [u8; {}] = ({}).to_bytes();",
                                                    ident.unwrap(),
                                                    info.size,
                                                    pprust::expr_to_string(init_expr)
                                                ));
                                            }
                                        } else {
                                            // Non-Replacable Init
                                            new_stmts.push(s.clone());
                                            new_stmts.push(utils::stmt!(
                                                "let mut {}_bytes: [u8; {}] = ({}).to_bytes();",
                                                ident.unwrap(),
                                                info.size,
                                                pprust::expr_to_string(init_expr)
                                            ));
                                        }
                                    }
                                }
                                if !found {
                                    new_stmts.push(s.clone());
                                }
                            } else {
                                new_stmts.push(s.clone());
                            }
                        } else {
                            new_stmts.push(s.clone());
                        }
                    }
                    _ => new_stmts.push(s.clone()), // TODO? LocalKind - Decl, InitElse
                },
                // Writes
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                    println!("\tStmt Expr: {}", pprust::expr_to_string(&expr));
                    if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&expr.id) {
                        println!("\t\tMIR --> {def_id:?}: {mir_locs:?}",);
                    }
                    new_stmts.push(s.clone());
                }
                _ => new_stmts.push(s.clone()),
            }
        }

        if !new_stmts.is_empty() {
            new_stmts
        } else {
            stmts
        }
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
            ast_to_hir,
            hir_to_thir,
            thir_to_mir,
            transform_info: analysis.refine_result(),
        }
    }

    fn get_mir_func_locs_from_node(&self, node_id: &NodeId) -> Option<(LocalDefId, Vec<Location>)> {
        let hir_id = self.ast_to_hir.local_map.get(node_id)?;
        let def_id = hir_id.owner.def_id;
        let thir_to_mir = self.thir_to_mir.get(&def_id)?;
        let thir_expr_id = self.hir_to_thir.exprs.get(hir_id)?;

        thir_to_mir
            .expr_to_locs
            .get(thir_expr_id)
            .cloned()
            .map(|locs| locs.to_vec())
            .map(|locs| (def_id, locs))
    }
}

struct TransformInfo {
    /// Identifier in AST
    pub ident: Option<String>,
    pub size: u64,
    pub init_loc: Location,
    /// locations of replacable reads
    pub read_locs: Vec<Location>,
    /// locations of all writes: (replacable, loc)
    pub write_locs: FxHashMap<Location, bool>,
}

impl TransformInfo {
    fn new(size: u64, init_loc: Location) -> Self {
        Self {
            ident: None,
            size,
            init_loc,
            read_locs: vec![],
            write_locs: FxHashMap::default(),
        }
    }
}

impl<'a> AnalysisResult<'a> {
    fn refine_result(self) -> FxHashMap<LocalDefId, Vec<TransformInfo>> {
        let mut result = FxHashMap::default();
        for (def_id, place_map) in self.map {
            let mut trans_info_vec = vec![];
            for (_, (init, read_map)) in place_map {
                let size = match &init.kind {
                    super::analysis::UnionUseKind::InitUnion(_, _, _, size) => *size,
                    _ => unreachable!(),
                };
                let mut trans_info = TransformInfo::new(size, init.location);

                for (read, (replacable, writes)) in read_map {
                    trans_info.read_locs.push(read.location);
                    for write in writes {
                        trans_info
                            .write_locs
                            .entry(write.location)
                            .and_modify(|r| *r = *r && replacable)
                            .or_insert(replacable);
                    }
                }
                trans_info_vec.push(trans_info);
            }
            result.insert(def_id, trans_info_vec);
        }
        result
    }
}
