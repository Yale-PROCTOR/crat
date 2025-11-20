use etrace::some_or;
use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::{HirId, def::Res};
use rustc_middle::{
    mir::{self, Statement},
    ty::{self, TyCtxt},
};
use rustc_span::{
    DUMMY_SP,
    def_id::LocalDefId,
    sym::{new, unwrap},
};
use utils::ir::{AstToHir, mir_ty_to_string};

use super::{
    Analysis,
    collector::collect_diffs,
    decision::{PtrKind, SigDecisions},
};
use crate::utils::rustc::RustProgram;

pub(crate) struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    sig_decs: SigDecisions,
    ptr_kinds: FxHashMap<HirId, PtrKind>,
    ast_to_hir: AstToHir,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item(&mut self, item: &mut Item) {
        let node_id = item.id;
        match &mut item.kind {
            ItemKind::Impl(_) => return,
            ItemKind::Fn(box fn_item) => {
                let def_id = self.ast_to_hir.global_map[&node_id];
                let mir_body = self
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let sig_dec = self.sig_decs.data.get(&def_id).unwrap();

                // let fn_name = fn_item.ident.name.as_str();
                // let debug = fn_name == "keccak_inc_squeeze";

                // Currently intra-procedural borrow inference:
                // skip return type; only consider parameters
                for ((local_decl, input_dec), param) in mir_body
                    .local_decls
                    .iter()
                    .skip(1)
                    .zip(&sig_dec.input_decs)
                    .zip(&mut fn_item.sig.decl.inputs)
                {
                    // if debug {
                    //     println!(
                    //         "Transforming fn {fn_name}:\nparam with decl {local_decl:?} and decision {input_dec:?}\n\n"
                    //     );
                    // }
                    match input_dec {
                        Some(PtrKind::OptRef(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = mk_opt_ref_ty(inner_ty, *m, self.tcx);
                            if let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind {
                                binding_mode.1 = Mutability::Mut; // TODO: is this precise?
                            }
                        }
                        Some(PtrKind::Slice(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected array pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = mk_slice_ty(inner_ty, *m, self.tcx);
                        }
                        Some(PtrKind::Raw(_)) => continue,
                        None => continue,
                    }
                }
            }
            _ => {}
        }

        mut_visit::walk_item(self, item);
    }

    fn flat_map_stmt(&mut self, s: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let stmts = mut_visit::walk_flat_map_stmt(self, s);
        let mut new_stmts = smallvec::SmallVec::new();
        for s in stmts {
            match &s.kind {
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                    if let ExprKind::Assign(lhs, rhs, _) = &expr.kind
                        && let ExprKind::AddrOf(BorrowKind::Ref, mutability, rhs_inner) = &rhs.kind
                        && let ExprKind::MethodCall(_) = rhs_inner.kind
                    {
                        new_stmts.push(utils::stmt!(
                            "let {}_tmp = {};",
                            mutability.prefix_str(),
                            pprust::expr_to_string(&rhs_inner),
                        ));
                        new_stmts.push(utils::stmt!(
                            "{} = {}_tmp;",
                            pprust::expr_to_string(&lhs),
                            mutability.ref_prefix_str(),
                        ));
                    } else {
                        new_stmts.push(s);
                    }
                }
                _ => {
                    new_stmts.push(s);
                }
            }
        }
        return new_stmts;
    }

    fn visit_local(&mut self, local: &mut Local) {
        mut_visit::walk_local(self, local);

        if let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
            && let Some(lhs_kind) = self.ptr_kinds.get(&hir_id).copied()
        {
            let typeck = self.tcx.typeck(hir_id.owner);
            let lhs_ty = typeck.node_type(hir_id);
            let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();

            match lhs_kind {
                PtrKind::OptRef(m) => {
                    local.ty = Some(P(mk_opt_ref_ty(lhs_inner_ty, m, self.tcx)));
                }
                PtrKind::Slice(m) => {
                    local.ty = Some(P(mk_slice_ty(lhs_inner_ty, m, self.tcx)));
                }
                PtrKind::Raw(_) => {}
            }

            if let LocalKind::Init(box rhs) | LocalKind::InitElse(box rhs, _) = &mut local.kind {
                self.transform_rhs(rhs, let_stmt.init.unwrap(), lhs_kind);
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        match &mut expr.kind {
            ExprKind::Assign(lhs, rhs, _) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                let hir::ExprKind::Assign(hir_lhs, hir_rhs, _) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let lhs_ty = typeck.expr_ty(hir_lhs);
                let (_, m) = some_or!(unwrap_ptr_from_mir_ty(lhs_ty), return);
                let lhs_kind = if let ExprKind::Path(_, _) = lhs.kind {
                    let hir_id = self.hir_id_of_path(lhs.id).unwrap();
                    self.ptr_kinds[&hir_id]
                } else {
                    PtrKind::Raw(m.is_mut())
                };
                self.transform_rhs(rhs, hir_rhs, lhs_kind);
            }
            ExprKind::Binary(bin_op, l, r)
                if matches!(
                    bin_op.node,
                    BinOpKind::Eq
                        | BinOpKind::Ne
                        | BinOpKind::Lt
                        | BinOpKind::Le
                        | BinOpKind::Gt
                        | BinOpKind::Ge
                ) =>
            {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                let hir::ExprKind::Binary(_, hir_l, hir_r) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let ty = typeck.expr_ty_adjusted(hir_l);
                if let Some((_, m)) = unwrap_ptr_from_mir_ty(ty) {
                    let kind = PtrKind::Raw(m.is_mut());
                    self.transform_rhs(l, hir_l, kind);
                    self.transform_rhs(r, hir_r, kind);
                }
            }
            ExprKind::Unary(UnOp::Deref, e) => {
                let e = unwrap_paren_mut(e);
                match &e.kind {
                    ExprKind::Path(_, _) => {
                        let hir_id = self.hir_id_of_path(e.id).unwrap();
                        let ptr_kind = self.ptr_kinds[&hir_id];
                        match ptr_kind {
                            PtrKind::OptRef(m) => {
                                let m = if m { "_mut" } else { "" };
                                *e = utils::expr!(
                                    "{}.as_deref{}().unwrap()",
                                    pprust::expr_to_string(e),
                                    m
                                );
                            }
                            PtrKind::Slice(_) => {
                                *expr = utils::expr!("{}[0]", pprust::expr_to_string(e));
                            }
                            PtrKind::Raw(_) => {}
                        }
                    }
                    ExprKind::Cast(_, box cast_ty) => {
                        let cast_ty = self.ast_to_hir.get_ty(cast_ty.id, self.tcx).unwrap();
                        let unwrapped_e = unwrap_expr(e);
                        if let Some(unwrapped_hir_id) = self.hir_id_of_path(unwrapped_e.id)
                            && let hir::TyKind::Ptr(_) = cast_ty.kind
                        {
                            match self.ptr_kinds[&unwrapped_hir_id] {
                                PtrKind::OptRef(m) | PtrKind::Slice(m) => {
                                    let hir_expr =
                                        self.ast_to_hir.get_expr(e.id, self.tcx).unwrap();
                                    self.transform_rhs(e, hir_expr, PtrKind::Raw(m));
                                }
                                PtrKind::Raw(_) => {}
                            }
                        }
                    }
                    ExprKind::MethodCall(box MethodCall {
                        seg,
                        receiver,
                        args,
                        ..
                    }) if seg.ident.name.as_str() == "offset" => match receiver.kind {
                        ExprKind::Path(_, _) => {
                            let hir_id = self.hir_id_of_path(receiver.id).unwrap();
                            let ptr_kind = self.ptr_kinds[&hir_id];
                            match ptr_kind {
                                PtrKind::OptRef(_) => {
                                    panic!(
                                        "Cannot offset an optional reference: {:?}",
                                        pprust::expr_to_string(receiver)
                                    );
                                }
                                PtrKind::Slice(_) => {
                                    let idx_expr = unwrap_expr(&args[0]);
                                    *expr = utils::expr!(
                                        "{}[({}) as usize]",
                                        pprust::expr_to_string(receiver),
                                        pprust::expr_to_string(idx_expr)
                                    );
                                }
                                PtrKind::Raw(_) => {}
                            }
                        }
                        _ => {}
                    },
                    ExprKind::AddrOf(BorrowKind::Ref, _, box inner)
                        if matches!(
                            &inner.kind,
                            ExprKind::Index(
                                _,
                                box Expr {
                                    kind: ExprKind::Range(Some(_), _, _),
                                    ..
                                },
                                _,
                            )
                        ) =>
                    {
                        if let ExprKind::Index(
                            _,
                            box Expr {
                                kind: ExprKind::Range(Some(start), _, _),
                                ..
                            },
                            _,
                        ) = &inner.kind
                        {
                            // previously transformed from offset method call.
                            // Dereferencing
                            *expr = utils::expr!(
                                "{}[{}]",
                                pprust::expr_to_string(inner),
                                pprust::expr_to_string(start)
                            );
                        } else {
                            unreachable!()
                        };
                    }
                    _ => {}
                }
            }
            ExprKind::Call(_, args) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::Call(func, hargs) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let sig_dec = if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
                    && let Res::Def(_, def_id) = path.res
                    && let Some(def_id) = def_id.as_local()
                {
                    self.sig_decs.data.get(&def_id)
                } else {
                    None
                };
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                for (i, (arg, harg)) in args.iter_mut().zip(hargs).enumerate() {
                    let ty = typeck.expr_ty_adjusted(harg);
                    let (_, m) = some_or!(unwrap_ptr_from_mir_ty(ty), continue);
                    let param_kind = sig_dec
                        .and_then(|sig| sig.input_decs.get(i).copied())
                        .flatten()
                        .unwrap_or(PtrKind::Raw(
                            self.get_mutability_decision(harg).unwrap_or(m.is_mut()),
                        ));
                    self.transform_rhs(arg, harg, param_kind);
                }
            }
            ExprKind::MethodCall(box MethodCall { seg, receiver, .. })
                if seg.ident.name.as_str() == "is_null" =>
            {
                if matches!(receiver.kind, ExprKind::Path(_, _)) {
                    let hir_id = self.hir_id_of_path(receiver.id).unwrap();
                    let ptr_kind = self.ptr_kinds[&hir_id];
                    match ptr_kind {
                        PtrKind::OptRef(_) => {
                            *expr = utils::expr!("{}.is_none()", pprust::expr_to_string(receiver));
                        }
                        PtrKind::Slice(_) => {
                            *expr = utils::expr!("{}.is_empty()", pprust::expr_to_string(receiver));
                        }
                        PtrKind::Raw(_) => {}
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall {
                seg,
                receiver,
                args,
                ..
            }) if seg.ident.name.as_str() == "offset" => match &unwrap_paren(receiver).kind {
                ExprKind::Path(_, _) => {
                    let hir_id = self.hir_id_of_path(receiver.id).unwrap();
                    let ptr_kind = self.ptr_kinds[&hir_id];
                    let idx_expr = unwrap_expr(&args[0]);
                    if let PtrKind::Slice(m) = ptr_kind {
                        *expr = utils::expr!(
                            "&{}{}[({}) as usize..]",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(receiver),
                            pprust::expr_to_string(idx_expr)
                        );
                    }
                }
                ExprKind::AddrOf(
                    BorrowKind::Ref,
                    mutability,
                    inner @ box Expr {
                        kind:
                            ExprKind::Index(
                                _,
                                box Expr {
                                    kind: ExprKind::Range(Some(_), _, _),
                                    ..
                                },
                                _,
                            ),
                        ..
                    },
                ) => {
                    *expr = utils::expr!(
                        "{}{}[({}) as usize..]",
                        mutability.ref_prefix_str(),
                        pprust::expr_to_string(&inner),
                        pprust::expr_to_string(unwrap_expr(&args[0])),
                    );
                }
                ExprKind::Cast(_, box cast_ty) => {
                    let cast_ty = self.ast_to_hir.get_ty(cast_ty.id, self.tcx).unwrap();
                    if let hir::TyKind::Ptr(_) = cast_ty.kind {
                        let unwrapped_receiver = unwrap_expr_mut(receiver);
                        if let ExprKind::Path(_, _) = unwrapped_receiver.kind {
                            let hir_id = self.hir_id_of_path(unwrapped_receiver.id).unwrap();
                            match self.ptr_kinds[&hir_id] {
                                PtrKind::OptRef(_) => {
                                    unreachable!()
                                }
                                PtrKind::Slice(m) => {
                                    *unwrapped_receiver = utils::expr!(
                                        "{}.as_{}ptr()",
                                        pprust::expr_to_string(&unwrapped_receiver),
                                        if m { "mut_" } else { "" },
                                    );
                                }
                                _ => {}
                            }
                        }
                    }
                }
                _ => {}
            },
            ExprKind::Ret(Some(ret)) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::Ret(Some(hir_ret)) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let sig = self
                    .tcx
                    .fn_sig(hir_ret.hir_id.owner)
                    .skip_binder()
                    .skip_binder();
                if let ty::TyKind::RawPtr(_, m) = sig.output().kind() {
                    let kind = PtrKind::Raw(m.is_mut());
                    self.transform_rhs(ret, hir_ret, kind);
                }
            }
            _ => {}
        }
    }
}

impl<'tcx> TransformVisitor<'tcx> {
    pub fn new(
        rust_program: &RustProgram<'tcx>,
        analysis: &Analysis,
        ast_to_hir: AstToHir,
    ) -> TransformVisitor<'tcx> {
        let sig_decs = SigDecisions::new(rust_program, analysis); // TODO: Move outside
        let ptr_kinds = collect_diffs(rust_program, analysis); // TODO: Move outside

        TransformVisitor {
            tcx: rust_program.tcx,
            sig_decs,
            ptr_kinds,
            ast_to_hir,
        }
    }

    fn hir_id_of_path(&self, id: NodeId) -> Option<HirId> {
        let hir_rhs = self.ast_to_hir.get_expr(id, self.tcx)?;
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_rhs.kind else { return None };
        let Res::Local(hir_id) = path.res else { return None };
        Some(hir_id)
    }

    fn transform_rhs(&self, rhs: &mut Expr, hir_rhs: &hir::Expr, lhs_kind: PtrKind) {
        let e = unwrap_expr(rhs);
        if let ExprKind::Lit(token::Lit {
            kind: token::LitKind::Integer,
            symbol,
            ..
        }) = e.kind
            && symbol.as_str() == "0"
        {
            // rhs_ty will be `usize`, not a pointer, so we early return here
            match lhs_kind {
                PtrKind::Slice(m) => {
                    *rhs = utils::expr!("&{}[]", if m { "mut " } else { "" });
                }
                PtrKind::OptRef(_) => {
                    *rhs = utils::expr!("None");
                }
                PtrKind::Raw(_) => {}
            }
            return;
        }

        let typeck = self.tcx.typeck(hir_rhs.hir_id.owner);
        let lhs_ty = typeck.expr_ty_adjusted(hir_rhs);
        let rhs_ty = typeck.expr_ty(unwrap_hir_expr(hir_rhs));
        let lhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(lhs_ty).unwrap();
        let rhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(rhs_ty).unwrap();
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let extern_ty = matches!(rhs_inner_ty.kind(), ty::TyKind::Foreign(_));
        match &e.kind {
            ExprKind::Path(_, _) => {
                let hir_id = some_or!(self.hir_id_of_path(e.id), return);
                let rhs_kind = self.ptr_kinds[&hir_id];
                match (lhs_kind, rhs_kind) {
                    (PtrKind::OptRef(m), PtrKind::OptRef(_)) => {
                        if need_cast {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            *rhs = utils::expr!(
                                "({}).as_deref{}().map(|x| &{}*(x as *{3} _ as *{3} {4}))",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                                if m { "mut " } else { "" },
                                if m { "mut" } else { "const" },
                                lhs_inner_ty,
                            );
                        } else {
                            *rhs = utils::expr!(
                                "({}).as_deref{}()",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                            );
                        }
                    }
                    (PtrKind::Slice(m), PtrKind::OptRef(_)) => {
                        // TODO: handle c char arrays properly
                        if need_cast {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            // HACK: assume length 1024 if not null, 0 if null
                            *rhs = utils::expr!(
                                "({}).as_deref{1}().map_or(&{3}[], |x| std::slice::from_raw_parts{1}(x as *{2} _ as *{2} {4}, 1024))",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                if m { "mut " } else { "" },
                                lhs_inner_ty,
                            );
                        } else {
                            // HACK: assume length 1024 if not null, 0 if null
                            *rhs = utils::expr!(
                                "({}).as_deref{1}().map_or(&{2}[], |x| std::slice::from_raw_parts{1}(x, 1024))",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                                if m { "mut " } else { "" }
                            );
                        }
                    }
                    (PtrKind::Raw(m), PtrKind::OptRef(_)) => {
                        if need_cast {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            *rhs = utils::expr!(
                                "({}).as_deref{1}().map_or(std::ptr::null{1}(), |x| x as *{2} _ as *{2} {3})",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                lhs_inner_ty,
                            );
                        } else if extern_ty {
                            *rhs = utils::expr!(
                                "
    match &{}({}) {{
        Some(x) => *x as *{} {},
        None => std::ptr::null{}(),
    }}
",
                                if m { "mut " } else { "" },
                                pprust::expr_to_string(e),
                                if m { "mut" } else { "const" },
                                mir_ty_to_string(rhs_inner_ty, self.tcx),
                                if m { "_mut" } else { "" },
                            );
                        } else {
                            *rhs = utils::expr!(
                                "({}).as_deref{1}().map_or(std::ptr::null{1}(), |x| x)",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                            );
                        }
                    }
                    (PtrKind::OptRef(m), PtrKind::Slice(_)) => {
                        if need_cast {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            *rhs = utils::expr!(
                                "Some(&{1}*(({0}).as{2}_ptr() as *{3} _ as *{3} {4}))",
                                pprust::expr_to_string(e),
                                if m { "mut " } else { "" },
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                lhs_inner_ty,
                            );
                        } else {
                            *rhs = utils::expr!(
                                "Some(&{}{}[0])",
                                if m { "mut " } else { "" },
                                pprust::expr_to_string(e),
                            );
                        }
                    }
                    (PtrKind::Raw(m), PtrKind::Slice(_)) => {
                        if need_cast {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            *rhs = utils::expr!(
                                "({0}).as_{1}ptr() as *{2} _ as *{2} {3}",
                                pprust::expr_to_string(e),
                                if m { "mut_" } else { "" },
                                if m { "mut" } else { "const" },
                                lhs_inner_ty,
                            );
                        } else {
                            *rhs = utils::expr!(
                                "({}).as_{}ptr()",
                                pprust::expr_to_string(e),
                                if m { "mut_" } else { "" },
                            );
                        }
                    }
                    (PtrKind::Slice(m), PtrKind::Slice(_)) => {
                        if need_cast {
                            *rhs = utils::expr!(
                                "std::slice::from_raw_parts{1}({0}.as{1}_ptr() as *{2} _ as *{2} {3}, {0}.len())",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                mir_ty_to_string(lhs_inner_ty, self.tcx),
                            );
                        } else {
                            *rhs = e.clone();
                        }
                    }
                    (PtrKind::OptRef(m), PtrKind::Raw(m1)) => {
                        if need_cast {
                            if *lhs_inner_ty.kind() == ty::TyKind::Int(ty::IntTy::I8) {
                                // special handling for c_char TODO: better solution for char arrays
                                *rhs = utils::expr!(
                                    "(({0}) as *{1} u8 as *{1} std::ffi::c_char).as_{2}()",
                                    pprust::expr_to_string(e),
                                    if m { "mut" } else { "const" },
                                    if m { "mut" } else { "ref" },
                                );
                            } else {
                                let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                                *rhs = utils::expr!(
                                    "(({}) as *{} {}).as_{}()",
                                    pprust::expr_to_string(e),
                                    if m { "mut" } else { "const" },
                                    lhs_inner_ty,
                                    if m { "mut" } else { "ref" },
                                );
                            }
                        } else if m && !m1 {
                            *rhs = utils::expr!(
                                "({}).cast_mut().as_mut()",
                                pprust::expr_to_string(e),
                            );
                        } else {
                            *rhs = utils::expr!(
                                "({}).as_{}()",
                                pprust::expr_to_string(e),
                                if m { "mut" } else { "ref" },
                            );
                        }
                    }
                    (PtrKind::Slice(m), PtrKind::Raw(_)) => {
                        if need_cast {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            // HACK: assume length 1024, 0 if null
                            *rhs = utils::expr!(
                                "({0}).as_{1}().map_or(&{4}[], |x| std::slice::from_raw_parts{2}(x as *{3} _ as *{3} {5}, 1024))",
                                pprust::expr_to_string(e),
                                if m { "mut" } else { "ref" },
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                if m { "mut " } else { "" },
                                lhs_inner_ty,
                            );
                        } else {
                            // HACK: assume length 1024
                            *rhs = utils::expr!(
                                "({0}).as_{1}().map_or(&{4}[], |x| std::slice::from_raw_parts{2}(x as *{3} _, 1024))",
                                pprust::expr_to_string(e),
                                if m { "mut" } else { "ref" },
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                if m { "mut " } else { "" },
                            );
                        }
                    }
                    (PtrKind::Raw(_), PtrKind::Raw(_)) => {}
                }
            }
            ExprKind::AddrOf(_, _, e) => {
                // if rhs is `&mut x` and `x`'s type has been updated to `Option<&(mut) T>`,
                // we need a cast
                let e_inner = unwrap_idx(e);
                let ty_updated = if matches!(e_inner.kind, ExprKind::Path(_, _))
                    && let Some(hir_e) = self.ast_to_hir.get_expr(e_inner.id, self.tcx)
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_e.kind
                    && let Res::Local(hir_id) = path.res
                {
                    match self.ptr_kinds.get(&hir_id) {
                        Some(PtrKind::OptRef(_)) => true,
                        Some(PtrKind::Slice(_)) => true,
                        _ => false,
                    }
                } else {
                    false
                };
                match lhs_kind {
                    PtrKind::OptRef(m) => {
                        if need_cast || ty_updated {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            *rhs = utils::expr!(
                                "Some(&{}*(&raw {1} ({2}) as *{1} {3}))",
                                if m { "mut " } else { "" },
                                if m { "mut" } else { "const" },
                                pprust::expr_to_string(e),
                                lhs_inner_ty,
                            );
                        } else {
                            let is_arr = match e.kind {
                                ExprKind::Array(_) => true,
                                ExprKind::Index(
                                    _,
                                    box Expr {
                                        kind: ExprKind::Range(_, _, _),
                                        ..
                                    },
                                    _,
                                ) => true,
                                _ => false,
                            };
                            *rhs = utils::expr!(
                                "Some(&{}({}{}))",
                                if m { "mut " } else { "" },
                                pprust::expr_to_string(e),
                                if is_arr { "[0]" } else { "" }
                            );
                        }
                    }
                    PtrKind::Slice(m) => {
                        if let ExprKind::Index(r, idx_expr, _) = &e.kind {
                            if need_cast {
                                println!(
                                    "Casting slice index rhs: {}",
                                    pprust::expr_to_string(rhs)
                                );
                                *rhs = utils::expr!(
                                    "std::slice::from_raw_parts{2}(&{0}({3}[{4}{5}]) as *{1} _ as *{1} {6}, 1024)",
                                    if m { "mut " } else { "" },
                                    if m { "mut" } else { "const" },
                                    if m { "_mut" } else { "" },
                                    pprust::expr_to_string(r),
                                    pprust::expr_to_string(idx_expr),
                                    if matches!(idx_expr.kind, ExprKind::Range(_, _, _)) {
                                        ""
                                    } else {
                                        ".."
                                    },
                                    mir_ty_to_string(lhs_inner_ty, self.tcx),
                                );
                            } else {
                                *rhs = utils::expr!(
                                    "&{}{}[{}{}]",
                                    if m { "mut " } else { "" },
                                    pprust::expr_to_string(r),
                                    pprust::expr_to_string(idx_expr),
                                    if matches!(idx_expr.kind, ExprKind::Range(_, _, _)) {
                                        ""
                                    } else {
                                        ".."
                                    }
                                );
                            }
                        } else {
                            if need_cast {
                                unimplemented!()
                            } else {
                                *rhs = utils::expr!(
                                    "&{}[{}]",
                                    if m { "mut " } else { "" },
                                    pprust::expr_to_string(e),
                                );
                            }
                        }
                    }
                    PtrKind::Raw(m) => {
                        if let ExprKind::Index(r, box idx_expr, _) = &e.kind
                            && let ExprKind::Range(Some(start_expr), _, _) = &idx_expr.kind
                        {
                            // dereferencing a slice with range indexing
                            if need_cast {
                                *rhs = utils::expr!(
                                    "(&raw {0} {1}[{2}]) as *{0} {3}",
                                    if m { "mut" } else { "const" },
                                    pprust::expr_to_string(r),
                                    pprust::expr_to_string(start_expr),
                                    mir_ty_to_string(lhs_inner_ty, self.tcx),
                                );
                            } else {
                                *rhs = utils::expr!(
                                    "&raw {0} ({1}[{2}])",
                                    if m { "mut" } else { "const" },
                                    pprust::expr_to_string(r),
                                    pprust::expr_to_string(start_expr),
                                );
                            }
                        } else if need_cast || ty_updated {
                            *rhs = utils::expr!(
                                "&raw {0} ({1}) as *{0} {2}",
                                if m { "mut" } else { "const" },
                                pprust::expr_to_string(e),
                                mir_ty_to_string(lhs_inner_ty, self.tcx),
                            );
                        } else {
                            *rhs = utils::expr!(
                                "&raw {0} ({1})",
                                if m { "mut" } else { "const" },
                                pprust::expr_to_string(e),
                            );
                        }
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall { seg, receiver, .. })
                if matches!(seg.ident.name.as_str(), "as_ptr" | "as_mut_ptr") =>
            {
                let m = seg.ident.name.as_str() == "as_mut_ptr";
                match lhs_kind {
                    PtrKind::OptRef(_) => {
                        *rhs = utils::expr!(
                            "Some(&{}{}[0])",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(receiver)
                        );
                    }
                    PtrKind::Slice(_) => {
                        *rhs = utils::expr!(
                            "&{}{}",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(receiver)
                        );
                    }
                    PtrKind::Raw(_) => {
                        // no change needed
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall { seg, receiver, .. })
                if seg.ident.name.as_str() == "offset" =>
            {
                // HACK: currently, fields are not promoted, so we assume that they remain as raw
                // pointers
                if matches!(unwrap_expr(receiver).kind, ExprKind::Field(_, _)) {
                    match lhs_kind {
                        PtrKind::Slice(m) => {
                            *rhs = utils::expr!(
                                "std::slice::from_raw_parts{}(({}) as *{} _, 1024)",
                                if m { "_mut" } else { "" },
                                pprust::expr_to_string(rhs),
                                if m { "mut" } else { "" },
                            );
                        }
                        PtrKind::OptRef(m) => {
                            *rhs = utils::expr!(
                                "({}).as_{}()",
                                pprust::expr_to_string(rhs),
                                if m { "mut" } else { "ref" },
                            );
                        }
                        PtrKind::Raw(_) => {}
                    }
                    return;
                }
                let mut offset_exprs = vec![];
                let mut curr_expr = &*rhs;
                // loop {
                //     match &curr_expr.kind {
                //         ExprKind::MethodCall(box MethodCall {
                //             seg,
                //             receiver: inner_receiver,
                //             args,
                //             ..
                //         }) if seg.ident.name.as_str() == "offset" => {
                //             let idx_expr = unwrap_expr(&args[0]);
                //             offset_exprs.push(idx_expr);
                //             curr_expr = inner_receiver;
                //         }
                //         _ => break,
                //     }
                // }
                if let ExprKind::MethodCall(box MethodCall { seg, receiver, .. }) = &curr_expr.kind
                    && matches!(seg.ident.name.as_str(), "as_ptr" | "as_mut_ptr")
                {
                    curr_expr = receiver;
                }
                let index_str = offset_exprs
                    .iter()
                    .rev()
                    .map(|idx_expr| format!("[({}) as usize..]", pprust::expr_to_string(idx_expr)))
                    .collect::<String>();
                match lhs_kind {
                    PtrKind::Slice(m) => {
                        if need_cast {
                            *rhs = utils::expr!(
                                "{6}std::slice::from_raw_parts{1}({3}{0} as *{2} _ as *{2} {4}, 1024){5}",
                                pprust::expr_to_string(curr_expr),
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                if m { "mut " } else { "" },
                                mir_ty_to_string(lhs_inner_ty, self.tcx),
                                index_str,
                                if index_str.is_empty() {
                                    ""
                                } else {
                                    if m { "&mut " } else { "&" }
                                }
                            );
                        } else {
                            // *rhs = utils::expr!(
                            //     "&{}{}{}",
                            //     if m { "mut " } else { "" },
                            //     pprust::expr_to_string(curr_expr),
                            //     index_str
                            // );
                            *rhs = utils::expr!(
                                "std::slice::from_raw_parts{1}({0}{2}, 1024)",
                                pprust::expr_to_string(curr_expr),
                                if m { "_mut" } else { "" },
                                index_str
                            );
                        }
                    }
                    PtrKind::OptRef(m) => {
                        if need_cast {
                            *rhs = utils::expr!(
                                "Some(&{0}*({5}{2}{4} as *{1} _ as *{1} {3}){})",
                                if m { "mut " } else { "" },
                                if m { "mut" } else { "const" },
                                pprust::expr_to_string(curr_expr),
                                mir_ty_to_string(lhs_inner_ty, self.tcx),
                                index_str,
                                if index_str.is_empty() {
                                    ""
                                } else {
                                    if m { "&mut " } else { "&" }
                                }
                            );
                        } else {
                            // *rhs = utils::expr!(
                            //     "Some(&{}{}{}[0])",
                            //     if m { "mut " } else { "" },
                            //     pprust::expr_to_string(curr_expr),
                            //     index_str
                            // );
                            *rhs = utils::expr!(
                                "Some(&{0}*({2} as *{1} {3}))",
                                if m { "mut " } else { "" },
                                if m { "mut" } else { "const" },
                                pprust::expr_to_string(curr_expr),
                                mir_ty_to_string(lhs_inner_ty, self.tcx),
                            );
                        }
                    }
                    PtrKind::Raw(_) => {
                        // skipping cases like
                        // memset(((*ctx).ctr).as_mut_ptr().offset(12 as libc::c_int as isize)
                    }
                }
            }
            ExprKind::Lit(token::Lit { kind, symbol, .. }) => {
                match kind {
                    token::LitKind::ByteStr => {
                        match lhs_kind {
                            PtrKind::Slice(m) => {
                                *rhs = utils::expr!(
                                    "std::slice::from_raw_parts{1}({0}.as{1}_ptr(){2}, {3})",
                                    pprust::expr_to_string(e),
                                    if m { "_mut" } else { "" },
                                    match lhs_inner_ty.kind() {
                                        ty::TyKind::Int(ty::IntTy::I8) => format!(
                                            " as *{} libc::c_char",
                                            if m { "mut" } else { "const" }
                                        ),
                                        ty::TyKind::Uint(ty::UintTy::U8) => format!(""),
                                        _ => unreachable!(),
                                    },
                                    symbol.as_str().len(), // including null terminator
                                );
                            }
                            PtrKind::OptRef(m) => {
                                // TODO: this is not safe and idiomatic; translating byte string literal to Option<&i8>
                                *rhs = utils::expr!(
                                    "({}).as_{}()",
                                    pprust::expr_to_string(rhs),
                                    if m { "mut" } else { "ref" },
                                );
                            }
                            PtrKind::Raw(_) => {
                                // skipping cases like
                                // std::mem::transmute::<&[u8; 18], &[uint8_t; 18]>(b"KAT-TRANSCRIPT-v1\0")
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => match lhs_kind {
                PtrKind::OptRef(m) => {
                    if need_cast {
                        if *lhs_inner_ty.kind() == ty::TyKind::Int(ty::IntTy::I8) {
                            // special handling for c_char TODO: better solution for char arrays
                            *rhs = utils::expr!(
                                "(({0}) as *{1} u8 as *{1} std::ffi::c_char).as_{2}()",
                                pprust::expr_to_string(e),
                                if m { "mut" } else { "const" },
                                if m { "mut" } else { "ref" },
                            );
                        } else {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            *rhs = utils::expr!(
                                "(({}) as *{} {}).as_{}()",
                                pprust::expr_to_string(e),
                                if m { "mut" } else { "const" },
                                lhs_inner_ty,
                                if m { "mut" } else { "ref" },
                            );
                        }
                    } else {
                        *rhs = utils::expr!(
                            "({}).as_{}()",
                            pprust::expr_to_string(e),
                            if m { "mut" } else { "ref" },
                        );
                    }
                }
                PtrKind::Slice(m) => {
                    if matches!(lhs_ty.kind(), ty::TyKind::Array(_, _)) {
                        if need_cast {
                            unimplemented!()
                        } else {
                            *rhs = utils::expr!(
                                "&{}{}",
                                if m { "mut " } else { "" },
                                pprust::expr_to_string(e),
                            );
                        }
                    } else {
                        if need_cast {
                            *rhs = utils::expr!(
                                "std::slice::from_raw_parts{1}({0} as *{2} _ as *{2} {3}, 1024)",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                                if m { "mut" } else { "const" },
                                mir_ty_to_string(lhs_inner_ty, self.tcx),
                            );
                        } else {
                            *rhs = utils::expr!(
                                "std::slice::from_raw_parts{1}({0}, 1024)",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                            );
                        }
                    }
                }
                PtrKind::Raw(_) => {}
            },
        }
    }

    fn get_mutability_decision(&self, hexpr: &hir::Expr<'tcx>) -> Option<bool> {
        // find the root of this hir expr and if it's a path, get its decision from ptr_kinds and return its mutability
        let mut curr_expr = hexpr;
        loop {
            match &curr_expr.kind {
                hir::ExprKind::MethodCall(seg, receiver, ..)
                    if seg.ident.name.as_str() == "offset" =>
                {
                    curr_expr = receiver;
                }
                _ => break,
            }
        }
        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = &curr_expr.kind
            && let Res::Local(hir_id) = path.res
        {
            match self.ptr_kinds.get(&hir_id) {
                Some(PtrKind::OptRef(m)) => Some(*m),
                Some(PtrKind::Slice(m)) => Some(*m),
                Some(PtrKind::Raw(m)) => Some(*m),
                None => None,
            }
        } else {
            None
        }
    }
}

fn unwrap_expr(expr: &Expr) -> &Expr {
    if let ExprKind::Cast(expr, _) | ExprKind::Paren(expr) = &expr.kind {
        unwrap_expr(expr)
    } else {
        expr
    }
}

fn unwrap_expr_mut(expr: &mut Expr) -> &mut Expr {
    if matches!(&expr.kind, ExprKind::Cast(_, _) | ExprKind::Paren(_)) {
        let (ExprKind::Cast(expr, _) | ExprKind::Paren(expr)) = &mut expr.kind else {
            unreachable!()
        };
        unwrap_expr_mut(expr)
    } else {
        expr
    }
}

fn unwrap_paren(expr: &Expr) -> &Expr {
    if let ExprKind::Paren(e) = &expr.kind {
        unwrap_paren(e)
    } else {
        expr
    }
}

fn unwrap_paren_mut(expr: &mut Expr) -> &mut Expr {
    if matches!(&expr.kind, ExprKind::Paren(_)) {
        let ExprKind::Paren(e) = &mut expr.kind else { unreachable!() };
        unwrap_paren_mut(e)
    } else {
        expr
    }
}

fn unwrap_idx(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Index(receiver, _, _) => unwrap_idx(receiver),
        ExprKind::Paren(e) => unwrap_idx(e),
        _ => e,
    }
}

#[inline]
fn unwrap_ptr_from_mir_ty(ty: ty::Ty<'_>) -> Option<(ty::Ty<'_>, ty::Mutability)> {
    match ty.kind() {
        ty::TyKind::RawPtr(ty, m) | ty::TyKind::Ref(_, ty, m) => Some((*ty, *m)),
        _ => None,
    }
}

fn unwrap_ptr_or_arr_from_mir_ty(ty: ty::Ty<'_>) -> Option<ty::Ty<'_>> {
    match ty.kind() {
        ty::TyKind::RawPtr(ty, _)
        | ty::TyKind::Ref(_, ty, _)
        | ty::TyKind::Slice(ty)
        | ty::TyKind::Array(ty, _) => Some(*ty),
        _ => None,
    }
}

#[inline]
fn mk_opt_ref_ty<'tcx>(ty: ty::Ty<'tcx>, mutability: bool, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    let m = if mutability { "mut " } else { "" };
    utils::ty!("Option<&{m}{ty}>")
}

#[inline]
fn mk_slice_ty<'tcx>(ty: ty::Ty<'tcx>, mutability: bool, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    let m = if mutability { "mut " } else { "" };
    utils::ty!("&{m}[{ty}]")
}

struct OffsetVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    params: FxHashMap<LocalDefId, Vec<HirId>>,
    offsets: FxHashSet<HirId>,
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for OffsetVisitor<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        kind: hir::intravisit::FnKind<'tcx>,
        decl: &'tcx hir::FnDecl<'tcx>,
        body_id: hir::BodyId,
        _: rustc_span::Span,
        def_id: LocalDefId,
    ) {
        let body = self.tcx.hir_body(body_id);
        let params = body
            .params
            .iter()
            .map(|param| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else { panic!() };
                hir_id
            })
            .collect();
        self.params.insert(def_id, params);
        hir::intravisit::walk_fn(self, kind, decl, body_id, def_id);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        match expr.kind {
            hir::ExprKind::MethodCall(seg, e, _, _) => {
                if seg.ident.name == rustc_span::sym::offset
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) =
                        unwrap_hir_expr(e).kind
                    && let Res::Local(hir_id) = path.res
                {
                    self.offsets.insert(hir_id);
                }
            }
            hir::ExprKind::Call(callee, args) => {
                if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = callee.kind
                    && let Res::Def(_, def_id) = path.res
                    && matches!(
                        self.tcx.hir_get_if_local(def_id),
                        Some(hir::Node::ForeignItem(_))
                    )
                    && let Some(name) = utils::ir::def_id_to_symbol(def_id, self.tcx)
                    && name.as_str() == "strtol"
                    && let [arg, ..] = args
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) =
                        unwrap_hir_expr(arg).kind
                    && let Res::Local(hir_id) = path.res
                {
                    self.offsets.insert(hir_id);
                }
            }
            _ => {}
        }
        hir::intravisit::walk_expr(self, expr);
    }
}

fn unwrap_hir_expr<'tcx>(expr: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
    if let hir::ExprKind::Cast(expr, _) | hir::ExprKind::DropTemps(expr) = &expr.kind {
        unwrap_hir_expr(expr)
    } else {
        expr
    }
}
