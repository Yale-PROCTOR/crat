use etrace::some_or;
use rustc_ast::{Crate, Expr, NodeId, Stmt, StmtKind, mut_visit, mut_visit::MutVisitor};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_middle::{mir::Location, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;
use smallvec::SmallVec;
use utils::ir::{AstToHir, HirToThir, ThirToMir, mir_ty_to_string};

use super::analysis::AnalysisResult;

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);

    let analysis_result = super::analysis::analyze(tcx, verbose);

    let mut visitor = TransformVisitor::new(tcx, &mut krate, analysis_result);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    visitor.visit_crate(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }
    str
}

struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    hir_to_thir: HirToThir,
    thir_to_mir: FxHashMap<LocalDefId, ThirToMir>,
    transform_info: FxHashMap<LocalDefId, Vec<TransformInfo>>,
}

fn get_write_info_by_mir_loc<'a>(
    transform_info: &'a FxHashMap<LocalDefId, Vec<TransformInfo>>,
    def_id: &LocalDefId,
    mir_loc: &Location,
) -> Option<&'a TransformInfo> {
    let infos = transform_info.get(def_id);
    if let Some(infos) = infos {
        for info in infos {
            let write_locs = &info.write_locs;
            if write_locs.contains_key(mir_loc) {
                return Some(info);
            }
        }
    }
    None
}

fn get_read_info_by_mir_loc<'a>(
    transform_info: &'a FxHashMap<LocalDefId, Vec<TransformInfo>>,
    def_id: &LocalDefId,
    mir_loc: &Location,
) -> Option<&'a TransformInfo> {
    let infos = transform_info.get(def_id);
    if let Some(infos) = infos {
        for info in infos {
            let read_locs = &info.read_locs;
            if read_locs.contains(mir_loc) {
                return Some(info);
            }
        }
    }
    None
}

fn get_mut_init_info_by_mir_loc<'a>(
    transform_info: &'a mut FxHashMap<LocalDefId, Vec<TransformInfo>>,
    def_id: &LocalDefId,
    mir_loc: &Location,
) -> Option<&'a mut TransformInfo> {
    let infos = transform_info.get_mut(def_id);
    if let Some(infos) = infos {
        for info in infos {
            let init_loc = &info.init_loc;
            if init_loc == mir_loc {
                return Some(info);
            }
        }
    }
    None
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        rustc_ast::mut_visit::walk_expr(self, expr);

        match &expr.kind {
            // Write - Assign
            rustc_ast::ExprKind::Assign(_, rhs_expr, _) => {
                if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&expr.id) {
                    let mir_loc = mir_locs[0];
                    if let Some(info) =
                        get_write_info_by_mir_loc(&self.transform_info, &def_id, &mir_loc)
                    {
                        let ident = info.ident.as_ref().unwrap();
                        let replacable = info.write_locs.get(&mir_loc).unwrap();

                        let typecheck = self.tcx.typeck(def_id);
                        let hir_expr =
                            some_or!(self.ast_to_hir.get_expr(rhs_expr.id, self.tcx), return);
                        let expr_ty = typecheck.expr_ty_adjusted(hir_expr);
                        if let Some(replacable) = replacable {
                            if *replacable {
                                // Replacable Write
                                *expr = utils::expr!(
                                    "{}_bytes = ({} as {}).to_ne_bytes()",
                                    ident,
                                    pprust::expr_to_string(rhs_expr),
                                    mir_ty_to_string(expr_ty, self.tcx)
                                );
                            } else {
                                // Non-Replacable Write
                                *expr = utils::expr!(
                                    "{{ {}; {}_bytes = ({} as {}).to_ne_bytes() }}",
                                    pprust::expr_to_string(expr),
                                    ident,
                                    pprust::expr_to_string(rhs_expr),
                                    mir_ty_to_string(expr_ty, self.tcx)
                                );
                            }
                        }
                    }
                }
            }
            // TODO: Write - AssignOp
            // Ex. u.field += 1;

            // Read
            rustc_ast::ExprKind::Field(_, _) => {
                if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&expr.id) {
                    // TODO: Multiple Locations
                    let mir_loc = mir_locs[0];
                    if let Some(info) =
                        get_read_info_by_mir_loc(&self.transform_info, &def_id, &mir_loc)
                    {
                        let ident = info.ident.as_ref().unwrap();
                        if let rustc_ast::ExprKind::Field(e, _) = &expr.kind
                            && pprust::expr_to_string(e) == *ident
                        {
                            let typecheck = self.tcx.typeck(def_id);
                            let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                            let expr_ty = typecheck.expr_ty_adjusted(hir_expr);

                            *expr = utils::expr!(
                                "{}::from_ne_bytes({}_bytes)",
                                utils::ir::mir_ty_to_string(expr_ty, self.tcx),
                                ident
                            );
                        }
                    }
                }
            }
            _ => (),
        }
    }

    fn flat_map_stmt(&mut self, s: Stmt) -> SmallVec<[Stmt; 1]> {
        let mut stmts = mut_visit::walk_flat_map_stmt(self, s);
        let mut new_stmts = SmallVec::<[Stmt; 1]>::new();
        for s in &stmts {
            if let StmtKind::Let(local) = s.kind.clone()
                && let rustc_ast::LocalKind::Init(init_expr) = &local.kind
            {
                let pat = local.pat;
                if let Some((def_id, mir_locs)) = self.get_mir_func_locs_from_node(&init_expr.id) {
                    let mir_loc = mir_locs[0];
                    if let Some(info) =
                        get_mut_init_info_by_mir_loc(&mut self.transform_info, &def_id, &mir_loc)
                    {
                        let init_loc = info.init_loc;
                        let ident = match &pat.kind {
                            rustc_ast::PatKind::Ident(_, ident, _) => {
                                Some(ident.as_str().to_string())
                            }
                            _ => None,
                        };
                        info.ident = ident.clone();

                        let val_expr = get_init_field_expr(init_expr).unwrap();

                        let typecheck = self.tcx.typeck(def_id);
                        let hir_expr = self.ast_to_hir.get_expr(val_expr.id, self.tcx).unwrap();
                        let expr_ty = typecheck.expr_ty_adjusted(hir_expr);

                        // Transform Init
                        if let Some(Some(_replacable)) = info.write_locs.get(&init_loc) {
                            // If a value in write_locs is not None, then the type to write can be transformed into bytes
                            // Also, it is readable from some replacable reads
                            // Add a byte array definition with the rvalue in bytes
                            new_stmts.push(utils::stmt!(
                                "let mut {}_bytes: [u8; {}] = ({} as {}).to_ne_bytes();",
                                ident.unwrap(),
                                info.size,
                                pprust::expr_to_string(val_expr),
                                mir_ty_to_string(expr_ty, self.tcx)
                            ));
                        } else {
                            // Non-Replacable Init but will not be read
                            // Define byte array with dummy initialization
                            // Actually, no difference in just using the original rvalue
                            new_stmts.push(utils::stmt!(
                                "let mut {}_bytes: [u8; {}] = [0u8; {}];",
                                ident.unwrap(),
                                info.size,
                                info.size,
                            ));
                        }
                    }
                }
            }
        }

        if new_stmts.is_empty() {
            stmts
        } else {
            stmts.append(&mut new_stmts);
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
            if analysis.map.contains_key(&def_id) {
                thir_to_mir.insert(def_id, utils::ir::map_thir_to_mir(def_id, false, tcx));
            }
        }

        Self {
            tcx,
            ast_to_hir,
            hir_to_thir,
            thir_to_mir,
            transform_info: analysis.refine_result(),
        }
    }

    fn get_mir_func_locs_from_node(
        &self,
        node_id: &NodeId,
    ) -> Option<(LocalDefId, &SmallVec<[Location; 1]>)> {
        let hir_id = self.ast_to_hir.local_map.get(node_id)?;
        let def_id = hir_id.owner.def_id;
        let thir_to_mir = self.thir_to_mir.get(&def_id)?;
        let thir_expr_id = self.hir_to_thir.exprs.get(hir_id)?;

        thir_to_mir
            .expr_to_locs
            .get(thir_expr_id)
            .map(|locs| (def_id, locs))
    }
}

struct TransformInfo {
    /// Identifier in AST
    pub ident: Option<String>,
    /// Size in bytes
    pub size: u64,
    /// Location of initialization
    pub init_loc: Location,
    /// Locations of replacable reads
    pub read_locs: Vec<Location>,
    /// Locations of writes
    /// is_replacable:
    /// - Some(true): replacable
    /// - Some(false): readable from both non-readable and replacable reads
    /// - None: otherwise (e.g., readable only from non-replacable read)
    /// - If the type to write cannot be transformed into bytes, it will be None (as all reads will be non-replacable, see analysis::is_replacable_read)
    /// - If a write is not readable from any read, it will not be in this map
    pub write_locs: FxHashMap<Location, Option<bool>>,
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

                let mut read_locs = vec![];
                let mut write_locs = FxHashMap::default();
                for (read, (replacable, writes)) in read_map {
                    if replacable {
                        read_locs.push(read.location);
                    }
                    for write in writes {
                        write_locs
                            .entry(write.location)
                            .and_modify(|r| {
                                if let Some(r) = r {
                                    *r &= replacable;
                                } else {
                                    *r = if replacable { Some(true) } else { None };
                                }
                            })
                            .or_insert(if replacable { Some(true) } else { None });
                    }
                }
                if read_locs.is_empty() {
                    // If all reads are non-replacable, skip
                    continue;
                }
                let trans_info = TransformInfo {
                    ident: None,
                    size,
                    init_loc: init.location,
                    read_locs,
                    write_locs,
                };

                trans_info_vec.push(trans_info);
            }
            result.insert(def_id, trans_info_vec);
        }
        result
    }
}

fn get_init_field_expr(init_expr: &Expr) -> Option<&Expr> {
    if let rustc_ast::ExprKind::Struct(struct_expr) = &init_expr.kind {
        if let Some(field) = struct_expr.fields.first() {
            Some(&field.expr)
        } else {
            None
        }
    } else {
        None
    }
}
