use std::cell::Cell;

use etrace::some_or;
use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Symbol;
use utils::{
    ast::{unwrap_cast_and_paren, unwrap_cast_and_paren_mut, unwrap_paren, unwrap_paren_mut},
    ir::{AstToHir, mir_ty_to_string},
};

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
    forced_raw_bindings: FxHashSet<HirId>,
    raw_scalar_bridge_bindings: FxHashSet<HirId>,
    ast_to_hir: AstToHir,
    pub bytemuck: Cell<bool>,
    pub slice_cursor: Cell<bool>,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item(&mut self, item: &mut Item) {
        let node_id = item.id;
        let mut fn_output_transform: Option<(LocalDefId, PtrKind)> = None;
        match &mut item.kind {
            ItemKind::Impl(_) => return,
            ItemKind::Fn(box fn_item) => {
                let def_id = self.ast_to_hir.global_map[&node_id];
                let mir_body = self
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let sig_dec = self.sig_decs.data.get(&def_id).unwrap();

                for ((local_decl, input_dec), param) in mir_body
                    .local_decls
                    .iter()
                    .skip(1)
                    .zip(&sig_dec.input_decs)
                    .zip(&mut fn_item.sig.decl.inputs)
                {
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
                        }
                        Some(PtrKind::OptBox) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = mk_opt_box_ty(inner_ty, self.tcx);
                        }
                        Some(PtrKind::Slice(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = mk_slice_ty(inner_ty, *m, self.tcx);
                        }
                        Some(PtrKind::Raw(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = mk_raw_ptr_ty(inner_ty, *m, self.tcx);
                        }
                        Some(PtrKind::SliceCursor(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = mk_cursor_ty(inner_ty, *m, self.tcx);
                            self.slice_cursor.set(true);
                        }
                        Some(PtrKind::OptBoxedSlice) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = mk_opt_boxed_slice_ty(inner_ty, self.tcx);
                        }
                        None => continue,
                    }

                    if input_dec.is_some_and(|kind| kind.is_mut())
                        && let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind
                    {
                        binding_mode.1 = Mutability::Mut;
                    }
                }

                let adjusted_output_dec = sig_dec.output_dec.map(|output_dec| {
                    let return_decl = &mir_body.local_decls[rustc_middle::mir::Local::from_u32(0)];
                    let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(return_decl.ty) else {
                        return output_dec;
                    };
                    if matches!(output_dec, PtrKind::OptBox | PtrKind::OptBoxedSlice)
                        && fn_tail_returns_unsupported_box_binding(
                            self.tcx,
                            &self.sig_decs,
                            &self.ptr_kinds,
                            def_id,
                            output_dec,
                            inner_ty,
                        )
                    {
                        PtrKind::Raw(true)
                    } else {
                        output_dec
                    }
                });

                if let Some(output_dec) = adjusted_output_dec {
                    let return_decl = &mir_body.local_decls[rustc_middle::mir::Local::from_u32(0)];
                    if let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(return_decl.ty)
                        && let FnRetTy::Ty(ret_ty) = &mut fn_item.sig.decl.output
                    {
                        *ret_ty = P(match output_dec {
                            PtrKind::OptRef(m) => mk_opt_ref_ty(inner_ty, m, self.tcx),
                            PtrKind::OptBox => mk_opt_box_ty(inner_ty, self.tcx),
                            PtrKind::Raw(m) => mk_raw_ptr_ty(inner_ty, m, self.tcx),
                            PtrKind::OptBoxedSlice => mk_opt_boxed_slice_ty(inner_ty, self.tcx),
                            PtrKind::Slice(m) => mk_slice_ty(inner_ty, m, self.tcx),
                            PtrKind::SliceCursor(m) => {
                                self.slice_cursor.set(true);
                                mk_cursor_ty(inner_ty, m, self.tcx)
                            }
                        });
                    }
                }

                let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                let output_kind = match sig.output().kind() {
                    ty::TyKind::RawPtr(_, m) => {
                        Some(adjusted_output_dec.unwrap_or(PtrKind::Raw(m.is_mut())))
                    }
                    _ => adjusted_output_dec,
                };
                fn_output_transform = output_kind.map(|kind| (def_id, kind));
            }
            _ => {}
        }

        mut_visit::walk_item(self, item);

        if let Some((def_id, output_kind)) = fn_output_transform
            && let ItemKind::Fn(box fn_item) = &mut item.kind
            && let Some(body) = &mut fn_item.body
            && let Some(stmt) = body.stmts.last_mut()
            && let StmtKind::Expr(expr) = &mut stmt.kind
        {
            let hir_item = self.tcx.hir_expect_item(def_id);
            let hir::ItemKind::Fn { body: body_id, .. } = hir_item.kind else { return };
            let hir_body = self.tcx.hir_body(body_id);
            let hir::ExprKind::Block(hir_block, _) = hir_body.value.kind else { return };
            let Some(hir_tail) = hir_block.expr else { return };
            self.transform_rhs(expr, hir_tail, output_kind);
        }
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
                            pprust::expr_to_string(rhs_inner),
                        ));
                        new_stmts.push(utils::stmt!(
                            "{} = {}_tmp;",
                            pprust::expr_to_string(lhs),
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
        new_stmts
    }

    fn visit_local(&mut self, local: &mut Local) {
        mut_visit::walk_local(self, local);

        if let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, _ident, _) = let_stmt.pat.kind
            && let Some(mut lhs_kind) = self.effective_ptr_kind(hir_id)
        {
            let typeck = self.tcx.typeck(hir_id.owner);
            let lhs_ty = typeck.node_type(hir_id);
            let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
            let original_lhs_kind = lhs_kind;
            if matches!(lhs_kind, PtrKind::OptBox | PtrKind::OptBoxedSlice)
                && let Some(init) = let_stmt.init
                && !self.rhs_supports_box_target(init, lhs_kind, lhs_inner_ty)
            {
                lhs_kind = PtrKind::Raw(true);
            }
            if matches!(lhs_kind, PtrKind::OptBox | PtrKind::OptBoxedSlice)
                && self.fn_has_unsupported_box_assignment(hir_id, lhs_kind, lhs_inner_ty)
            {
                lhs_kind = PtrKind::Raw(true);
            }
            if lhs_kind != original_lhs_kind && matches!(lhs_kind, PtrKind::Raw(_)) {
                self.ptr_kinds.insert(hir_id, lhs_kind);
                self.forced_raw_bindings.insert(hir_id);
            }

            match lhs_kind {
                PtrKind::OptRef(m) => {
                    local.ty = Some(P(mk_opt_ref_ty(lhs_inner_ty, m, self.tcx)));
                }
                PtrKind::OptBox => {
                    local.ty = Some(P(mk_opt_box_ty(lhs_inner_ty, self.tcx)));
                }
                PtrKind::OptBoxedSlice => {
                    local.ty = Some(P(mk_opt_boxed_slice_ty(lhs_inner_ty, self.tcx)));
                }
                PtrKind::Slice(m) => {
                    local.ty = Some(P(mk_slice_ty(lhs_inner_ty, m, self.tcx)));
                }
                PtrKind::Raw(m) => {
                    local.ty = Some(P(mk_raw_ptr_ty(lhs_inner_ty, m, self.tcx)));
                }
                PtrKind::SliceCursor(m) => {
                    local.ty = Some(P(mk_cursor_ty(lhs_inner_ty, m, self.tcx)));
                    self.slice_cursor.set(true);
                }
            }

            if lhs_kind.is_mut()
                && let PatKind::Ident(binding_mode, ..) = &mut local.pat.kind
            {
                binding_mode.1 = Mutability::Mut;
            }

            if let LocalKind::Init(box rhs) | LocalKind::InitElse(box rhs, _) = &mut local.kind {
                let hir_rhs = let_stmt.init.unwrap();
                if !self.try_bridge_scalar_raw_root(rhs, lhs_kind, lhs_inner_ty, Some(hir_id)) {
                    self.transform_rhs(rhs, hir_rhs, lhs_kind);
                }
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
                let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                let lhs_hir_id = if let ExprKind::Path(_, _) = lhs.kind
                    && let Some(hir_id) = self.hir_id_of_path(lhs.id)
                    && let ExprKind::Path(_, path) = &lhs.kind
                    && let Some(seg) = path.segments.last()
                {
                    let _ = seg;
                    Some(hir_id)
                } else {
                    None
                };
                let mut lhs_kind = if let Some(hir_id) = lhs_hir_id {
                    self.effective_ptr_kind(hir_id).unwrap_or(PtrKind::Raw(m.is_mut()))
                } else {
                    PtrKind::Raw(m.is_mut())
                };
                let original_lhs_kind = lhs_kind;
                if matches!(lhs_kind, PtrKind::OptBox | PtrKind::OptBoxedSlice)
                    && !self.rhs_supports_box_target(hir_rhs, lhs_kind, lhs_inner_ty)
                {
                    lhs_kind = PtrKind::Raw(true);
                } else if matches!(lhs_kind, PtrKind::OptBox) {
                    if hir_is_unsupported_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_rhs) {
                        lhs_kind = PtrKind::Raw(true);
                    }
                    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_rhs.kind
                        && let Res::Local(rhs_hir_id) = path.res
                        && matches!(self.effective_ptr_kind(rhs_hir_id), Some(PtrKind::Raw(_)))
                    {
                        lhs_kind = PtrKind::Raw(true);
                    }
                }
                if lhs_kind != original_lhs_kind
                    && matches!(lhs_kind, PtrKind::Raw(_))
                    && let Some(hir_id) = lhs_hir_id
                {
                    self.ptr_kinds.insert(hir_id, lhs_kind);
                    self.forced_raw_bindings.insert(hir_id);
                }

                match lhs_kind {
                    PtrKind::SliceCursor(_) => {
                        // Detect self-assignment with offset: p = p.offset(k)
                        if let Some(lhs_hir_id) = self.hir_id_of_path(lhs.id) {
                            let rhs_e = unwrap_addr_of_deref(unwrap_cast_and_paren(rhs));
                            let hir_rhs_e = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_rhs));
                            let seek_offset = self.ptr_expr(rhs_e, hir_rhs_e).and_then(|pe| {
                                if let PtrExprBaseKind::Path(Res::Local(rhs_hir_id)) = pe.base_kind
                                    && rhs_hir_id == lhs_hir_id
                                    && pe.projs.len() == 1
                                    && let PtrExprProj::Offset(offset_expr) = &pe.projs[0]
                                {
                                    Some(pprust::expr_to_string(offset_expr))
                                } else {
                                    None
                                }
                            });
                            if let Some(ref offset_str) = seek_offset {
                                let lhs_str = pprust::expr_to_string(lhs);
                                *expr = utils::expr!("{}.seek(({}) as isize)", lhs_str, offset_str);
                                return;
                            }
                        }
                        if let Some(lhs_hir_id) = lhs_hir_id
                            && !self.try_bridge_scalar_raw_root(
                                rhs,
                                lhs_kind,
                                lhs_inner_ty,
                                Some(lhs_hir_id),
                            )
                        {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        } else if lhs_hir_id.is_none() {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        }
                    }
                    PtrKind::Slice(_)
                    | PtrKind::OptRef(_)
                    | PtrKind::OptBox
                    | PtrKind::OptBoxedSlice
                    | PtrKind::Raw(_) => {
                        if let Some(lhs_hir_id) = lhs_hir_id
                            && !self.try_bridge_scalar_raw_root(
                                rhs,
                                lhs_kind,
                                lhs_inner_ty,
                                Some(lhs_hir_id),
                            )
                        {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        } else if lhs_hir_id.is_none() {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        }
                    }
                }
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
                let ty = typeck.expr_ty(hir_l);
                if let Some((_, m)) = unwrap_ptr_from_mir_ty(ty) {
                    let kind = PtrKind::Raw(m.is_mut());
                    self.transform_rhs(l, hir_l, kind);
                    self.transform_rhs(r, hir_r, kind);
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
                    let param_kind = sig_dec
                        .and_then(|sig| sig.input_decs.get(i).copied())
                        .flatten()
                        .or_else(|| {
                            unwrap_ptr_from_mir_ty(ty).map(|(_, m)| {
                                PtrKind::Raw(self.get_mutability_decision(harg).unwrap_or(m.is_mut()))
                            })
                        });
                    let Some(param_kind) = param_kind else { continue };

                    self.transform_rhs(arg, harg, param_kind);
                }

                if let Some(free_rewrite) = self.rewrite_direct_free_call(hir_expr, &args[..]) {
                    *expr = free_rewrite;
                    return;
                }

                hoist_opt_ref_borrow(expr);
            }
            ExprKind::MethodCall(box MethodCall { seg, receiver, .. })
                if seg.ident.name.as_str() == "is_null" =>
            {
                let receiver = unwrap_paren(receiver);
                if matches!(receiver.kind, ExprKind::Path(_, _))
                    && let Some(hir_id) = self.hir_id_of_path(receiver.id)
                    && let Some(ptr_kind) = self.effective_ptr_kind(hir_id)
                {
                    match ptr_kind {
                        PtrKind::OptRef(_) => {
                            seg.ident.name = Symbol::intern("is_none");
                        }
                        PtrKind::OptBox | PtrKind::OptBoxedSlice => {
                            seg.ident.name = Symbol::intern("is_none");
                        }
                        PtrKind::Slice(_) | PtrKind::SliceCursor(_) => {
                            seg.ident.name = Symbol::intern("is_empty");
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
            }) if seg.ident.name.as_str() == "add" && args.len() == 1 => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::MethodCall(_, hir_receiver, _, _) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                if let Some((_, raw_mut)) = unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(hir_receiver))
                {
                    self.transform_ptr(receiver, hir_receiver, PtrCtx::Rhs(PtrKind::Raw(raw_mut.is_mut())));
                }
            }
            ExprKind::MethodCall(box MethodCall {
                seg,
                receiver,
                args,
                ..
            }) if seg.ident.name.as_str() == "offset_from" => {
                let hir_receiver = self.ast_to_hir.get_expr(receiver.id, self.tcx).unwrap();
                self.transform_ptr(receiver, hir_receiver, PtrCtx::Rhs(PtrKind::Raw(true)));
                let [arg] = &mut args[..] else { panic!() };
                let hir_arg = self.ast_to_hir.get_expr(arg.id, self.tcx).unwrap();
                self.transform_ptr(arg, hir_arg, PtrCtx::Rhs(PtrKind::Raw(true)));
            }
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
                    let kind = self
                        .sig_decs
                        .data
                        .get(&hir_ret.hir_id.owner.def_id)
                        .and_then(|sd| sd.output_dec)
                        .unwrap_or(PtrKind::Raw(m.is_mut()));
                    self.transform_rhs(ret, hir_ret, kind);
                } else if let ty::TyKind::Tuple(tys) = sig.output().kind() {
                    let ExprKind::Tup(elems) = &mut ret.kind else {
                        panic!("expected tuple expr for tuple return type")
                    };
                    let hir::ExprKind::Tup(hir_elems) = hir_ret.kind else {
                        panic!("expected HIR tuple expr for tuple return type")
                    };
                    for (i, elem_ty) in tys.iter().enumerate() {
                        if let ty::TyKind::RawPtr(_, m) = elem_ty.kind() {
                            self.transform_rhs(
                                &mut elems[i],
                                &hir_elems[i],
                                PtrKind::Raw(m.is_mut()),
                            );
                        }
                    }
                }
            }
            ExprKind::Unary(UnOp::Deref, e) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::Unary(UnOp::Deref, hir_e) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let m = match self.expr_ctx(hir_expr) {
                    ExprCtx::ImmediatelyAddrTaken => None,
                    ExprCtx::AddrTaken(m) => Some(m),
                    ExprCtx::Rvalue => Some(false),
                    ExprCtx::Lvalue => Some(true),
                };
                if let Some(m) = m {
                    // For SliceCursor with offset projections, try to emit base[offset] directly
                    let inner = unwrap_addr_of_deref(unwrap_cast_and_paren(e));
                    let hir_inner = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_e));
                    let pe = self.ptr_expr(inner, hir_inner);
                    if let Some(pe) = pe
                        && let PtrExprBaseKind::Path(Res::Local(hir_id)) = pe.base_kind
                        && matches!(self.effective_ptr_kind(hir_id), Some(PtrKind::SliceCursor(_)))
                        && pe.projs.len() == 1
                        && let PtrExprProj::Offset(offset) = &pe.projs[0]
                        && !pe.addr_of
                        && !pe.as_ptr
                        && !pe.cast_int
                    {
                        let base_str = pprust::expr_to_string(pe.base);
                        let offset_str = pprust::expr_to_string(offset);
                        *expr = utils::expr!("({})[({}) as isize]", base_str, offset_str)
                    } else {
                        match self.transform_ptr(e, hir_e, PtrCtx::Deref(m)) {
                            PtrKind::Raw(_) => {}
                            PtrKind::OptRef(_) => {
                                **e = utils::expr!("{}.unwrap()", pprust::expr_to_string(e));
                            }
                            PtrKind::OptBox => {
                                **e = utils::expr!(
                                    "{}.as_deref{}().unwrap()",
                                    pprust::expr_to_string(e),
                                    if m { "_mut" } else { "" },
                                );
                            }
                            PtrKind::OptBoxedSlice => {
                                *expr = utils::expr!(
                                    "({}).as_deref{}().unwrap()[0]",
                                    pprust::expr_to_string(e),
                                    if m { "_mut" } else { "" },
                                );
                            }
                            PtrKind::Slice(_) => {
                                *expr = utils::expr!("({})[0]", pprust::expr_to_string(e));
                            }
                            PtrKind::SliceCursor(_) => {
                                *expr = utils::expr!("({})[0 as usize]", pprust::expr_to_string(e));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PtrCtx {
    Rhs(PtrKind),
    Deref(bool),
}

#[derive(Clone, Copy, Debug)]
enum AllocatorRoot<'a> {
    Malloc { bytes: &'a Expr },
    Calloc { count: &'a Expr },
}

impl<'tcx> TransformVisitor<'tcx> {
    pub fn new(
        rust_program: &RustProgram<'tcx>,
        analysis: &Analysis,
        ast_to_hir: AstToHir,
    ) -> TransformVisitor<'tcx> {
        let mut sig_decs = SigDecisions::new(rust_program, analysis); // TODO: Move outside
        let mut ptr_kinds = collect_diffs(rust_program, analysis); // TODO: Move outside
        let mut forced_raw_bindings = downgrade_unsupported_allocator_box_kinds(rust_program.tcx);
        normalize_forced_raw_bindings(&mut ptr_kinds, &forced_raw_bindings);
        loop {
            let mut changed = false;
            if downgrade_unsupported_box_outputs(
                rust_program.tcx,
                &mut sig_decs,
                &ptr_kinds,
            ) {
                changed = true;
            }
            let raw_call_result_bindings =
                collect_raw_call_result_bindings(rust_program.tcx, &sig_decs);
            let raw_local_assignment_bindings =
                collect_raw_local_assignment_bindings(rust_program.tcx, &ptr_kinds);
            let unsupported_box_target_bindings = collect_unsupported_box_target_bindings(
                rust_program.tcx,
                &sig_decs,
                &ptr_kinds,
            );
            let old_len = forced_raw_bindings.len();
            forced_raw_bindings.extend(raw_call_result_bindings);
            forced_raw_bindings.extend(raw_local_assignment_bindings);
            forced_raw_bindings.extend(unsupported_box_target_bindings);
            if forced_raw_bindings.len() != old_len {
                changed = true;
                normalize_forced_raw_bindings(&mut ptr_kinds, &forced_raw_bindings);
            }
            if !changed {
                break;
            }
        }

        let raw_scalar_bridge_bindings =
            collect_scalar_raw_bridge_bindings(rust_program.tcx, &ptr_kinds);

        TransformVisitor {
            tcx: rust_program.tcx,
            sig_decs,
            ptr_kinds,
            forced_raw_bindings,
            raw_scalar_bridge_bindings,
            ast_to_hir,
            bytemuck: Cell::new(false),
            slice_cursor: Cell::new(false),
        }
    }

    fn try_bridge_scalar_raw_root(
        &self,
        rhs: &mut Expr,
        lhs_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
        lhs_hir_id: Option<HirId>,
    ) -> bool {
        let PtrKind::Raw(m) = lhs_kind else {
            return false;
        };
        let Some(lhs_hir_id) = lhs_hir_id else {
            return false;
        };
        if !self.raw_scalar_bridge_bindings.contains(&lhs_hir_id) {
            return false;
        }
        if !expr_supports_scalar_opt_box_allocator_root(self.tcx, rhs, lhs_inner_ty) {
            return false;
        }
        *rhs = self.raw_scalar_bridge_expr(lhs_inner_ty, m);
        true
    }

    fn raw_scalar_bridge_expr(&self, lhs_inner_ty: ty::Ty<'tcx>, m: bool) -> Expr {
        let ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let default_expr = self.default_value_expr(lhs_inner_ty);
        utils::expr!(
            "Box::into_raw(Box::new({})) as *{} {}",
            pprust::expr_to_string(&default_expr),
            if m { "mut" } else { "const" },
            ty,
        )
    }

    fn rewrite_direct_free_call(
        &self,
        hir_expr: &'tcx hir::Expr<'tcx>,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        let Some((hir_id, _harg)) = hir_free_arg_local_id(self.tcx, hir_expr) else {
            return None;
        };
        if !self.raw_scalar_bridge_bindings.contains(&hir_id) {
            return None;
        }
        let [arg] = args else { return None };
        let arg_ty = self.tcx.typeck(hir_expr.hir_id.owner).node_type(hir_id);
        let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(arg_ty) else {
            return None;
        };
        let arg_str = pprust::expr_to_string(arg);
        let inner_ty_str = mir_ty_to_string(inner_ty, self.tcx);
        Some(utils::expr!(
            "if !({0}).is_null() {{ drop(unsafe {{ Box::from_raw(({0}) as *mut {1}) }}); }}",
            arg_str,
            inner_ty_str,
        ))
    }

    fn hir_id_of_path(&self, id: NodeId) -> Option<HirId> {
        let hir_rhs = self.ast_to_hir.get_expr(id, self.tcx)?;
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_rhs.kind else { return None };
        let Res::Local(hir_id) = path.res else { return None };
        Some(hir_id)
    }

    fn effective_ptr_kind(&self, hir_id: HirId) -> Option<PtrKind> {
        let kind = self.ptr_kinds.get(&hir_id).copied()?;
        if self.forced_raw_bindings.contains(&hir_id)
            && matches!(kind, PtrKind::OptBox | PtrKind::OptBoxedSlice)
        {
            Some(PtrKind::Raw(true))
        } else {
            Some(kind)
        }
    }

    fn forced_local_callee_output_kind(&self, hir_expr: &hir::Expr<'tcx>) -> Option<PtrKind> {
        let hir::ExprKind::Call(func, _) = hir_expr.kind else {
            return None;
        };
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind else {
            return None;
        };
        let Res::Def(_, def_id) = path.res else {
            return None;
        };
        let def_id = def_id.as_local()?;
        if !local_def_id_has_fn_body(self.tcx, def_id) {
            return None;
        }
        self.sig_decs.data.get(&def_id)?.output_dec
    }

    fn rhs_supports_box_target(
        &self,
        hir_expr: &hir::Expr<'tcx>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> bool {
        let hir_uncast = hir_unwrap_casts(hir_expr);
        if hir_is_null_like_ptr_arg(self.tcx, hir_uncast) {
            return true;
        }

        match target_kind {
            PtrKind::OptBox => {
                if hir_supports_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_uncast) {
                    return true;
                }
            }
            PtrKind::OptBoxedSlice => {
                if hir_is_supported_boxed_slice_allocator_root(self.tcx, hir_uncast) {
                    return true;
                }
            }
            _ => return true,
        }

        if let hir::ExprKind::Call(..) = hir_expr.kind
            && self.forced_local_callee_output_kind(hir_expr) == Some(target_kind)
        {
            return true;
        }

        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind
            && let Res::Local(hir_id) = path.res
            && self.effective_ptr_kind(hir_id) == Some(target_kind)
        {
            return true;
        }

        false
    }

    fn fn_has_unsupported_box_assignment(
        &self,
        target_hir_id: HirId,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> bool {
        struct UnsupportedBoxAssignmentVisitor<'a, 'tcx> {
            transform: &'a TransformVisitor<'tcx>,
            target_hir_id: HirId,
            target_kind: PtrKind,
            lhs_inner_ty: ty::Ty<'tcx>,
            found: bool,
        }

        impl<'tcx> Visitor<'tcx> for UnsupportedBoxAssignmentVisitor<'_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if self.found {
                    return;
                }
                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let Res::Local(lhs_hir_id) = path.res
                    && lhs_hir_id == self.target_hir_id
                    && !self
                        .transform
                        .rhs_supports_box_target(rhs, self.target_kind, self.lhs_inner_ty)
                {
                    self.found = true;
                    return;
                }
                intravisit::walk_expr(self, expr);
            }
        }

        let body = self.tcx.hir_body_owned_by(target_hir_id.owner.def_id);
        let mut visitor = UnsupportedBoxAssignmentVisitor {
            transform: self,
            target_hir_id,
            target_kind,
            lhs_inner_ty,
            found: false,
        };
        visitor.visit_body(body);
        visitor.found
    }

    fn transform_rhs(
        &self,
        rhs: &mut Expr,
        hir_rhs: &hir::Expr<'tcx>,
        lhs_kind: PtrKind,
    ) -> PtrKind {
        self.transform_ptr(rhs, hir_rhs, PtrCtx::Rhs(lhs_kind))
    }

    fn transform_ptr(&self, ptr: &mut Expr, hir_ptr: &hir::Expr<'tcx>, ctx: PtrCtx) -> PtrKind {
        let allocator_root_expr = unwrap_addr_of_deref(unwrap_cast_and_paren(ptr)).clone();
        let e = unwrap_addr_of_deref_mut(unwrap_cast_and_paren_mut(ptr));
        let hir_e = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_ptr));

        if let ExprKind::If(_, t, Some(f)) = &mut e.kind {
            let hir::ExprKind::If(_, hir_t, Some(hir_f)) = hir_e.kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let StmtKind::Expr(t) = &mut t.stmts.last_mut().unwrap().kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let hir::ExprKind::Block(hir_t, _) = hir_t.kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let kind1 = self.transform_ptr(t, hir_t.expr.unwrap(), ctx);
            let kind2 = if let ExprKind::Block(f, _) = &mut f.kind {
                let StmtKind::Expr(f) = &mut f.stmts.last_mut().unwrap().kind else {
                    panic!("{}", pprust::expr_to_string(e));
                };
                let hir::ExprKind::Block(hir_f, _) = hir_f.kind else {
                    panic!("{}", pprust::expr_to_string(e));
                };
                self.transform_ptr(f, hir_f.expr.unwrap(), ctx)
            } else {
                // if-else chain
                self.transform_ptr(f, hir_f, ctx)
            };
            assert_eq!(kind1, kind2);
            return kind1;
        }

        if let ExprKind::Block(block, _) = &mut e.kind {
            let hir::ExprKind::Block(hir_block, _) = hir_e.kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let StmtKind::Expr(inner) = &mut block.stmts.last_mut().unwrap().kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            return self.transform_ptr(inner, hir_block.expr.unwrap(), ctx);
        }

        if is_null_ptr_constructor(&allocator_root_expr) {
            match ctx {
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = if m {
                        utils::expr!("crate::slice_cursor::SliceCursor::empty()")
                    } else {
                        utils::expr!("crate::slice_cursor::SliceCursorRef::empty()")
                    };
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = if m { utils::expr!("&mut []") } else { utils::expr!("&[]") };
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBox;
                }
                PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBoxedSlice;
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    *ptr = utils::expr!("std::ptr::null{}()", if m { "_mut" } else { "" });
                    return PtrKind::Raw(m);
                }
                PtrCtx::Deref(m) => return PtrKind::Raw(m),
            }
        }

        if let PtrCtx::Rhs(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) = ctx {
            let lhs_ty = self.tcx.typeck(hir_ptr.hir_id.owner).expr_ty_adjusted(hir_ptr);
            let lhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(lhs_ty, self.tcx)
                .unwrap_or_else(|| panic!("{} {}", lhs_ty, pprust::expr_to_string(ptr)));
            if let Some(kind) = self.try_materialize_box_allocator_root(
                ptr,
                &allocator_root_expr,
                kind,
                lhs_inner_ty,
            ) {
                return kind;
            }
        }

        let e = unwrap_addr_of_deref(unwrap_cast_and_paren(ptr));
        let typeck = self.tcx.typeck(hir_ptr.hir_id.owner);
        let lhs_ty = typeck.expr_ty_adjusted(hir_ptr);
        let rhs_ty = typeck.expr_ty(hir_unwrap_cast(hir_ptr));
        let mut pe = if let Some(pe) = self.ptr_expr(e, hir_e) {
            pe
        } else if let Some((rhs_inner_ty, rhs_mut)) = unwrap_ptr_from_mir_ty(rhs_ty) {
            let lhs_inner_ty =
                unwrap_ptr_or_arr_from_mir_ty(lhs_ty, self.tcx).unwrap_or(rhs_inner_ty);
            match ctx {
                PtrCtx::Rhs(PtrKind::Raw(m)) | PtrCtx::Deref(m) => {
                    if lhs_ty != rhs_ty {
                        *ptr = utils::expr!(
                            "{} as *{} {}",
                            pprust::expr_to_string(ptr),
                            if m { "mut" } else { "const" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    } else if m && !rhs_mut.is_mut() {
                        *ptr = utils::expr!(
                            "{} as *mut {}",
                            pprust::expr_to_string(ptr),
                            mir_ty_to_string(rhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    *ptr = self.opt_ref_from_raw(e, m, rhs_mut.is_mut(), lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = self.slice_from_raw(e, m, rhs_mut.is_mut(), lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = self.cursor_from_raw(e, m, rhs_mut.is_mut(), lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox) => {
                    *ptr = self.opt_box_from_raw(e, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptBox;
                }
                PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                    panic!(
                        "owning array box target requires allocator-root length evidence: {}",
                        pprust::expr_to_string(ptr)
                    );
                }
            }
        } else {
            panic!("{}", pprust::expr_to_string(ptr));
        };

        if pe.is_zero() {
            // rhs_ty will be `usize`, not a pointer, so we early return here
            match ctx {
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = if m {
                        utils::expr!("crate::slice_cursor::SliceCursorMut::empty()")
                    } else {
                        utils::expr!("crate::slice_cursor::SliceCursor::empty()")
                    };
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = if m {
                        utils::expr!("&mut []")
                    } else {
                        utils::expr!("&[]")
                    };
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBox;
                }
                PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBoxedSlice;
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    *ptr = utils::expr!("std::ptr::null{}()", if m { "_mut" } else { "" });
                    return PtrKind::Raw(m);
                }
                PtrCtx::Deref(m) => {
                    return PtrKind::Raw(m);
                }
            }
        }

        if pe.cast_int {
            match ctx {
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    let mut base = pe.base.clone();
                    // Rewrite inner pointer before integer casting
                    let kind =
                        self.transform_ptr(&mut base, pe.hir_base, PtrCtx::Rhs(PtrKind::Raw(m)));
                    pe.base = &base;
                    // Assume always need a cast from integer to pointer
                    pe.push_cast(lhs_ty);

                    let is_raw = matches!(kind, PtrKind::Raw(_));
                    *ptr = self.projected_expr(&pe, m, is_raw);
                    return PtrKind::Raw(m);
                }
                _ => panic!("{}", pprust::expr_to_string(ptr)),
            }
        }

        let lhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(lhs_ty, self.tcx).unwrap_or_else(|| {
            panic!("{} {} {}", lhs_ty, rhs_ty, pprust::expr_to_string(ptr));
        });
        let rhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(rhs_ty, self.tcx)
            .unwrap_or_else(|| panic!("{} {} {}", lhs_ty, rhs_ty, pprust::expr_to_string(ptr)));
        let need_cast = lhs_inner_ty != rhs_inner_ty;

        let def_id = hir_ptr.hir_id.owner.def_id;

        if pe.addr_of {
            let e = unwrap_addr_of(e);
            // if rhs is `&mut x` and `x`'s type has been updated, we need a cast
            let e_inner = unwrap_subscript(e);
            let ty_updated = if matches!(e_inner.kind, ExprKind::Path(_, _))
                && let Some(hir_e) = self.ast_to_hir.get_expr(e_inner.id, self.tcx)
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_e.kind
                && let Res::Local(hir_id) = path.res
            {
                matches!(
                    self.effective_ptr_kind(hir_id),
                    Some(
                        PtrKind::OptRef(_)
                            | PtrKind::OptBox
                            | PtrKind::OptBoxedSlice
                            | PtrKind::Slice(_)
                            | PtrKind::SliceCursor(_)
                    )
                )
            } else {
                false
            };
            // Handle addr_of with pointer arithmetic (offset, wrapping_add, etc.)
            // by building a slice from the base and applying projections as slice ops.
            if pe.projs.iter().any(|p| {
                matches!(
                    p,
                    PtrExprProj::Offset(_)
                        | PtrExprProj::IntegerOp(..)
                        | PtrExprProj::IntegerBinOp(..)
                )
            }) {
                let m = match ctx {
                    PtrCtx::Rhs(PtrKind::Raw(m))
                    | PtrCtx::Rhs(PtrKind::OptRef(m))
                    | PtrCtx::Rhs(PtrKind::Slice(m))
                    | PtrCtx::Rhs(PtrKind::SliceCursor(m))
                    | PtrCtx::Deref(m) => m,
                    PtrCtx::Rhs(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                        panic!("unsupported M4A box target for addr_of arithmetic")
                    }
                };
                // Create initial slice from the single element:
                //   std::slice::from_mut(&mut x) or std::slice::from_ref(&x)
                let base_str = pprust::expr_to_string(pe.base);
                let mut result = utils::expr!(
                    "std::slice::from_{}(&{}({}))",
                    if m { "mut" } else { "ref" },
                    if m { "mut " } else { "" },
                    base_str,
                );
                // Apply projections (mirrors projected_expr logic for !is_raw)
                let mut from_ty = pe.base_ty;
                for proj in &pe.projs {
                    match proj {
                        PtrExprProj::Cast(ty) if !ty.is_usize() => {
                            let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty).unwrap();
                            if from_ty != to_ty {
                                // slice to slice
                                result =
                                    self.plain_slice_from_slice(&result, &pe, m, to_ty, from_ty);
                            }
                            from_ty = to_ty;
                        }
                        PtrExprProj::Offset(offset) => {
                            result = utils::expr!(
                                "({})[({}) as usize..]",
                                pprust::expr_to_string(&result),
                                pprust::expr_to_string(offset),
                            );
                        }
                        // Complex arithmetic or cast-to-usize: leave as raw
                        _ => return PtrKind::Raw(m),
                    }
                }
                // Final wrapping depends on the target context
                match ctx {
                    PtrCtx::Deref(m) | PtrCtx::Rhs(PtrKind::Slice(m)) => {
                        // slice to slice
                        *ptr = self.plain_slice_from_slice(
                            &result,
                            &pe,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::Slice(m);
                    }
                    PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                        // slice to cursor
                        self.slice_cursor.set(true);
                        *ptr = self.cursor_from_plain_slice(
                            &result,
                            &pe,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::SliceCursor(m);
                    }
                    PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                        // slice to optref
                        *ptr = self.opt_ref_from_slice_or_cursor(
                            &result,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                        return PtrKind::OptRef(m);
                    }
                    PtrCtx::Rhs(PtrKind::Raw(m)) => {
                        let (_, m_lhs) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                        // slice to raw
                        *ptr = self.raw_from_slice_or_cursor(
                            &result,
                            m,
                            m_lhs.is_mut(),
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::Raw(m);
                    }
                    PtrCtx::Rhs(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                        panic!("unsupported M4A box target for addr_of slice wrapping")
                    }
                }
            }
            match ctx {
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    if !need_cast && !ty_updated {
                        *ptr = utils::expr!(
                            "&raw {} ({})",
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                        );
                    } else {
                        *ptr = utils::expr!(
                            "&raw {0} ({1}) as *{0} {2}",
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m) => {
                    if !need_cast && !ty_updated {
                        *ptr = utils::expr!(
                            "Some(&{}({}))",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(e),
                        );
                    } else if !ty_updated
                        && lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        // can be used for deref, so type must be specified
                        *ptr = utils::expr!(
                            "Some(bytemuck::cast_{}::<_, {}>(&{}({})))",
                            if m { "mut" } else { "ref" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(e),
                        );
                    } else {
                        // can be used for deref, so type must be specified
                        *ptr = utils::expr!(
                            "Some(&{}*(&raw {1} ({2}) as *{1} {3}))",
                            if m { "mut " } else { "" },
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    // ref -> cursor
                    self.slice_cursor.set(true);
                    if !need_cast && !ty_updated {
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorMut::from_mut(&mut ({}))",
                                pprust::expr_to_string(e),
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::from_ref(&({}))",
                                pprust::expr_to_string(e),
                            )
                        };
                    } else if !ty_updated
                        && lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorMut::new(std::slice::from_mut(bytemuck::cast_mut(&mut ({}))))",
                                pprust::expr_to_string(e),
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::new(std::slice::from_ref(bytemuck::cast_ref(&({}))))",
                                pprust::expr_to_string(e),
                            )
                        };
                    } else {
                        let rhs_ty_str = mir_ty_to_string(rhs_inner_ty, self.tcx);
                        let lhs_ty_str = mir_ty_to_string(lhs_inner_ty, self.tcx);
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorMut::from_raw_parts_mut(&raw mut ({0}) as *mut {1}, std::mem::size_of::<{2}>() / std::mem::size_of::<{1}>())",
                                pprust::expr_to_string(e),
                                lhs_ty_str,
                                rhs_ty_str,
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::from_raw_parts(&raw const ({0}) as *const {1}, std::mem::size_of::<{2}>() / std::mem::size_of::<{1}>())",
                                pprust::expr_to_string(e),
                                lhs_ty_str,
                                rhs_ty_str,
                            )
                        };
                    }
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    // ref -> slice
                    if !need_cast && !ty_updated {
                        *ptr = utils::expr!(
                            "std::slice::from_{}(&{}({}))",
                            if m { "mut" } else { "ref" },
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(e),
                        );
                    } else if !ty_updated
                        && lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "std::slice::from_{0}(bytemuck::cast_{0}(&{1}({2})))",
                            if m { "mut" } else { "ref" },
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(e),
                        );
                    } else {
                        *ptr = utils::expr!(
                            "std::slice::from_raw_parts{0}(&raw {1} ({2}) as *{1} _, 100000)",
                            if m { "_mut" } else { "" },
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                        );
                    }
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                    panic!("unsupported M4A box target for addr_of")
                }
            }
        }

        if pe.as_ptr && self.is_base_not_a_raw_ptr(&pe) {
            let base = self.projected_expr(&pe, pe.as_mut_ptr, false);
            let raw_expr = utils::expr!(
                "({}).as_{}ptr()",
                pprust::expr_to_string(&base),
                if pe.as_mut_ptr { "mut_" } else { "" },
            );
            match ctx {
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    if !need_cast {
                        *ptr = raw_expr;
                    } else {
                        *ptr = utils::expr!(
                            "({}) as *{} _",
                            pprust::expr_to_string(&raw_expr),
                            if m { "mut" } else { "const" },
                        );
                    }
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m) => {
                    *ptr = self.opt_ref_from_raw(&raw_expr, m, pe.as_mut_ptr, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = self.cursor_from_raw(&raw_expr, m, pe.as_mut_ptr, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = self.slice_from_raw(&raw_expr, m, pe.as_mut_ptr, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                    panic!("unsupported M4A box target for as_ptr")
                }
            }
        }

        if !pe.as_ptr && matches!(pe.base_ty.kind(), ty::TyKind::Array(..)) {
            match ctx {
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = utils::expr!(
                        "({}).as_{}ptr()",
                        pprust::expr_to_string(&base),
                        if m { "mut_" } else { "" },
                    );
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m) => {
                    let base = self.projected_expr(&pe, m, false);
                    if !need_cast {
                        *ptr = utils::expr!(
                            "Some(&{}({})[0])",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(&base),
                        );
                    } else if lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "Some(bytemuck::cast_{}::<_, {}>(&{}({})[0]))",
                            if m { "mut" } else { "ref" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(&base),
                        );
                    } else {
                        *ptr = utils::expr!(
                            "Some(&{}*(({}).as_{}ptr() as *{} {}))",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(&base),
                            if m { "mut_" } else { "" },
                            if m { "mut" } else { "const" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_from_plain_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.plain_slice_from_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                    panic!("unsupported M5 box target for array base")
                }
            }
        }

        if let Some(rhs_kind) = self.ptr_source_kind(&pe) {
            match (ctx, rhs_kind) {
                (PtrCtx::Rhs(PtrKind::Raw(m)) | PtrCtx::Deref(m), PtrKind::Raw(m1)) => {
                    if m && !m1 {
                        let inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                        *ptr = utils::expr!("{} as *mut {}", pprust::expr_to_string(ptr), inner_ty);
                    }
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::OptRef(m1)) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.raw_from_opt_ref(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::Slice(m1)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.raw_from_slice_or_cursor(&base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::SliceCursor(m1)) => {
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.raw_from_slice_or_cursor(&base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::Raw(m1)) => {
                    // to keep offsets, we use `e` instead of `pe.base`
                    *ptr = self.opt_ref_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.opt_ref_from_opt_box(pe.base, m, lhs_inner_ty, rhs_inner_ty, def_id);
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m), PtrKind::OptRef(m1)) => {
                    assert!(pe.projs.is_empty());
                    // can be used for deref, so type must be specified
                    *ptr = self.opt_ref_from_opt_ref(
                        pe.base,
                        m,
                        m1,
                        lhs_inner_ty,
                        rhs_inner_ty,
                        def_id,
                    );
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::OptBoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.opt_ref_from_slice_or_cursor(
                        &base,
                        m,
                        lhs_inner_ty,
                        source_inner_ty,
                        def_id,
                    );
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::Slice(_)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.opt_ref_from_slice_or_cursor(
                        &base,
                        m,
                        lhs_inner_ty,
                        rhs_inner_ty,
                        def_id,
                    );
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::SliceCursor(_)) => {
                    let base_str = pprust::expr_to_string(pe.base);
                    let offsets: Vec<String> = pe
                        .projs
                        .iter()
                        .filter_map(|p| {
                            if let PtrExprProj::Offset(o) = p {
                                Some(pprust::expr_to_string(o))
                            } else {
                                None
                            }
                        })
                        .collect();
                    let only_offsets = offsets.len() == pe.projs.len();

                    if only_offsets {
                        let as_slice = if m { "as_slice_mut" } else { "as_slice" };
                        let slice_expr = if offsets.is_empty() {
                            format!("({base_str}).{as_slice}()")
                        } else {
                            let offset_str = offsets.join(" + ");
                            format!(
                                "&{}({}).{}()[({}) as usize..]",
                                if m { "mut " } else { "" },
                                base_str,
                                as_slice,
                                offset_str,
                            )
                        };
                        *ptr = self.opt_ref_from_slice_or_cursor(
                            &utils::expr!("{}", slice_expr),
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                    } else {
                        let base = self.projected_expr(&pe, m, false);
                        *ptr = self.opt_ref_from_slice_or_cursor(
                            &base,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::Raw(m1)) => {
                    // // Raw → slice: delegate via cursor then unwrap.
                    // to keep offsets, we use `e` instead of `pe.base`
                    *ptr = self.slice_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Deref(_m), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.opt_box_from_opt_box(pe.base, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptBox;
                }
                (PtrCtx::Deref(m), PtrKind::OptBoxedSlice) => {
                    if pe.projs.is_empty() {
                        *ptr =
                            self.opt_boxed_slice_from_opt_boxed_slice(pe.base, lhs_inner_ty, rhs_inner_ty);
                        return PtrKind::OptBoxedSlice;
                    }
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.plain_slice_from_expr(&base, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)) | PtrCtx::Deref(m), PtrKind::Slice(_)) => {
                    let base = self.projected_expr(&pe, m, false);
                    // can be used for deref, so type must be specified
                    *ptr = self.plain_slice_from_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::OptBoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.plain_slice_from_expr(&base, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::SliceCursor(_)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_or_slice_to_slice_expr(&base, m);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Deref(m), PtrKind::SliceCursor(_)) => {
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_from_cursor(&base, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::Raw(m1)) => {
                    self.slice_cursor.set(true);
                    // to keep offsets, we use `e` instead of `pe.base`
                    *ptr = self.cursor_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::OptBoxedSlice) => {
                    self.slice_cursor.set(true);
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.cursor_from_slice_or_cursor_inner(
                        &base,
                        m,
                        lhs_inner_ty,
                        source_inner_ty,
                        true,
                    );
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::Slice(_)) => {
                    // Plain slice → cursor
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_from_plain_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::SliceCursor(m1)) => {
                    // Cursor → cursor
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    let mut result =
                        self.cursor_from_slice_or_cursor(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    if !m && m1 {
                        result = utils::expr!("({}).as_deref()", pprust::expr_to_string(&result),);
                    }
                    // need fork only for identity copy (no projections, no cast)
                    if pe.projs.is_empty() && lhs_inner_ty == rhs_inner_ty && m1 && m {
                        result =
                            utils::expr!("({}).as_deref_mut()", pprust::expr_to_string(&result));
                    }
                    *ptr = result;
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(_) | PtrKind::Slice(_)), PtrKind::OptRef(_)) => {
                    panic!()
                }
                (PtrCtx::Rhs(PtrKind::Slice(_) | PtrKind::SliceCursor(_)), PtrKind::OptBox) => {
                    panic!("unsupported M4A slice/cursor target from scalar owning box");
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.raw_from_opt_box(pe.base, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::OptBoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr =
                        self.raw_from_slice_or_cursor(&base, m, true, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::OptBox), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr = if matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_))) {
                        utils::expr!("({}).take()", pprust::expr_to_string(pe.base))
                    } else {
                        self.opt_box_from_opt_box(pe.base, lhs_inner_ty, rhs_inner_ty)
                    };
                    return PtrKind::OptBox;
                }
                (PtrCtx::Rhs(PtrKind::OptBox), PtrKind::Raw(_)) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.opt_box_from_raw(pe.base, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptBox;
                }
                (PtrCtx::Rhs(PtrKind::OptBoxedSlice), PtrKind::OptBoxedSlice) => {
                    assert!(pe.projs.is_empty());
                    *ptr = if matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_))) {
                        utils::expr!("({}).take()", pprust::expr_to_string(pe.base))
                    } else {
                        self.opt_boxed_slice_from_opt_boxed_slice(pe.base, lhs_inner_ty, rhs_inner_ty)
                    };
                    return PtrKind::OptBoxedSlice;
                }
                (PtrCtx::Rhs(PtrKind::OptBoxedSlice), PtrKind::Raw(_)) => {
                    panic!(
                        "owning array box target requires allocator-root length evidence: {}",
                        pprust::expr_to_string(ptr)
                    );
                }
                (PtrCtx::Rhs(PtrKind::OptBox), other)
                | (PtrCtx::Rhs(PtrKind::OptBoxedSlice), other) => {
                    panic!("unsupported M4A box target/source combination: {:?}", other);
                }
            }
        }

        if pe.base_kind == PtrExprBaseKind::ByteStr {
            match ctx {
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    assert!(!m, "{}", pprust::expr_to_string(ptr));
                    if lhs_inner_ty == self.tcx.types.u8 {
                        *ptr = utils::expr!("{}.first()", pprust::expr_to_string(e));
                    } else {
                        assert!(lhs_inner_ty.is_numeric());
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "bytemuck::cast_slice({}).first()",
                            pprust::expr_to_string(e)
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                    panic!("unsupported M4A box target for byte string source")
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    assert!(!m, "{}", pprust::expr_to_string(ptr));
                    self.slice_cursor.set(true);
                    if lhs_inner_ty == self.tcx.types.u8 {
                        *ptr = utils::expr!(
                            "crate::slice_cursor::SliceCursor::new({})",
                            pprust::expr_to_string(e)
                        );
                    } else {
                        assert!(lhs_inner_ty.is_numeric());
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "crate::slice_cursor::SliceCursor::new(bytemuck::cast_slice({}))",
                            pprust::expr_to_string(e),
                        );
                    }
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    assert!(!m, "{}", pprust::expr_to_string(ptr));
                    if lhs_inner_ty == self.tcx.types.u8 {
                        *ptr = e.clone();
                    } else {
                        assert!(lhs_inner_ty.is_numeric());
                        self.bytemuck.set(true);
                        *ptr = utils::expr!("bytemuck::cast_slice({})", pprust::expr_to_string(e),);
                    }
                    return PtrKind::Slice(m);
                }
                PtrCtx::Deref(_) => panic!(),
            }
        }

        let m1 = if let Some((_, rhs_mut)) = unwrap_ptr_from_mir_ty(rhs_ty) {
            rhs_mut.is_mut()
        } else {
            match pe.base_ty.kind() {
                ty::TyKind::RawPtr(_, m) | ty::TyKind::Ref(_, _, m) => m.is_mut(),
                ty::TyKind::Array(_, _) => match self.behind_subscripts(pe.hir_base) {
                    PathOrDeref::Path => true,
                    PathOrDeref::Deref(hir_id) => self.ptr_kinds[&hir_id].is_mut(),
                    PathOrDeref::Other => {
                        panic!("{}", pprust::expr_to_string(pe.base))
                    }
                },
                _ => panic!("{:?}", pe.base_ty),
            }
        };
        // Override m1 if this is a call to a function whose return type was changed
        let m1 = if let hir::ExprKind::Call(func, _) = pe.hir_base.kind
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
            && let Some(PtrKind::Raw(m)) =
                self.sig_decs.data.get(&def_id).and_then(|sd| sd.output_dec)
        {
            m
        } else {
            m1
        };
        match ctx {
            PtrCtx::Rhs(PtrKind::Raw(m)) | PtrCtx::Deref(m) => {
                if m && !m1 {
                    let inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                    *ptr = utils::expr!("{} as *mut {}", pprust::expr_to_string(e), inner_ty);
                }
                PtrKind::Raw(m)
            }
            PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                *ptr = self.opt_ref_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                PtrKind::OptRef(m)
            }
            PtrCtx::Rhs(PtrKind::OptBox) => {
                panic!(
                    "owning scalar box target requires allocator-root evidence: {}",
                    pprust::expr_to_string(ptr)
                )
            }
            PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                panic!(
                    "owning array box target requires allocator-root length evidence: {}",
                    pprust::expr_to_string(ptr)
                )
            }
            PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                self.slice_cursor.set(true);
                *ptr = self.cursor_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                PtrKind::SliceCursor(m)
            }
            PtrCtx::Rhs(PtrKind::Slice(m)) => {
                *ptr = self.slice_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                PtrKind::Slice(m)
            }
        }
    }

    fn cursor_or_slice_to_slice_expr(&self, e: &Expr, m: bool) -> Expr {
        let e = unwrap_paren(e);
        if matches!(e.kind, ExprKind::Index(..) | ExprKind::Array(..)) {
            utils::expr!(
                "&{}({})",
                if m { "mut " } else { "" },
                pprust::expr_to_string(e),
            )
        } else if let ExprKind::MethodCall(call) = &e.kind
            && matches!(call.seg.ident.name.as_str(), "as_slice" | "as_slice_mut")
        {
            e.clone()
        } else if is_std_slice_constructor_call(e) {
            e.clone()
        } else {
            let s = pprust::expr_to_string(e);
            if m {
                utils::expr!("({}).as_slice_mut()", s)
            } else {
                utils::expr!("({}).as_slice()", s)
            }
        }
    }

    fn ptr_source_kind(&self, pe: &PtrExpr<'_, 'tcx>) -> Option<PtrKind> {
        if let PtrExprBaseKind::Path(Res::Local(hir_id)) = pe.base_kind {
            return self.effective_ptr_kind(hir_id);
        }
        if let hir::ExprKind::Call(func, _) = pe.hir_base.kind
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            return self
                .sig_decs
                .data
                .get(&def_id)
                .and_then(|sd| sd.output_dec);
        }
        None
    }

    fn allocator_root<'a>(&self, expr: &'a Expr) -> Option<AllocatorRoot<'a>> {
        let ExprKind::Call(callee, args) = &unwrap_cast_and_paren(expr).kind else {
            return None;
        };
        let ExprKind::Path(_, path) = &unwrap_paren(callee).kind else {
            return None;
        };
        let name = path.segments.last()?.ident.name.as_str();
        match (name, &args[..]) {
            ("malloc", [bytes]) => Some(AllocatorRoot::Malloc { bytes }),
            ("calloc", [count, _elem_size]) => Some(AllocatorRoot::Calloc { count }),
            ("realloc", [ptr, bytes]) if is_null_like_ptr_arg(ptr) => {
                Some(AllocatorRoot::Malloc { bytes })
            }
            _ => None,
        }
    }

    fn default_value_expr(&self, ty: ty::Ty<'tcx>) -> Expr {
        match ty.kind() {
            ty::TyKind::RawPtr(pointee, mutability) => utils::expr!(
                "std::ptr::null{}::<{}>()",
                if mutability.is_mut() { "_mut" } else { "" },
                mir_ty_to_string(*pointee, self.tcx),
            ),
            ty::TyKind::Adt(adt_def, args) if adt_def.did().is_local() && adt_def.is_struct() => {
                let ty_name = mir_ty_to_string(ty, self.tcx);
                let fields = adt_def
                    .all_fields()
                    .map(|field| {
                        let field_name = self.tcx.item_name(field.did).as_str().to_owned();
                        let field_expr = self.default_value_expr(field.ty(self.tcx, args));
                        format!("{field_name}: {}", pprust::expr_to_string(&field_expr))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                utils::expr!("{} {{ {} }}", ty_name, fields)
            }
            _ => {
                let ty = mir_ty_to_string(ty, self.tcx);
                utils::expr!("<{ty} as Default>::default()")
            }
        }
    }

    fn empty_slice_expr(&self, m: bool) -> Expr {
        if m {
            utils::expr!("&mut []")
        } else {
            utils::expr!("&[]")
        }
    }

    fn opt_box_view_expr(&self, e: &Expr, m: bool) -> Expr {
        utils::expr!(
            "({}).as_deref{}()",
            pprust::expr_to_string(e),
            if m { "_mut" } else { "" },
        )
    }

    fn opt_boxed_slice_view_expr(&self, e: &Expr, m: bool) -> Expr {
        utils::expr!(
            "({}).as_deref{}().unwrap_or({})",
            pprust::expr_to_string(e),
            if m { "_mut" } else { "" },
            pprust::expr_to_string(&self.empty_slice_expr(m)),
        )
    }

    fn try_materialize_box_allocator_root(
        &self,
        ptr: &mut Expr,
        expr: &Expr,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> Option<PtrKind> {
        let alloc_root = self.allocator_root(expr)?;
        let ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let default_expr = self.default_value_expr(lhs_inner_ty);
        let default_expr_str = pprust::expr_to_string(&default_expr);
        match (target_kind, alloc_root) {
            (PtrKind::OptBox, _)
                if expr_supports_scalar_opt_box_allocator_root(self.tcx, expr, lhs_inner_ty) =>
            {
                *ptr = utils::expr!("Some(Box::<{ty}>::new({default_expr_str}))");
                Some(PtrKind::OptBox)
            }
            (PtrKind::OptBoxedSlice, AllocatorRoot::Calloc { count }) => {
                *ptr = utils::expr!(
                    "Some(std::iter::repeat_with(|| {{ {0} }}).take(({1}) as usize).collect::<Vec<{2}>>().into_boxed_slice())",
                    default_expr_str,
                    pprust::expr_to_string(count),
                    ty,
                );
                Some(PtrKind::OptBoxedSlice)
            }
            (PtrKind::OptBoxedSlice, AllocatorRoot::Malloc { bytes }) => {
                *ptr = utils::expr!(
                    "Some(std::iter::repeat_with(|| {{ {0} }}).take((({1}) / std::mem::size_of::<{2}>()) as usize).collect::<Vec<{2}>>().into_boxed_slice())",
                    default_expr_str,
                    pprust::expr_to_string(bytes),
                    ty,
                );
                Some(PtrKind::OptBoxedSlice)
            }
            _ => None,
        }
    }

    fn plain_slice_from_expr(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
        if !need_cast {
            if matches!(e.kind, ExprKind::Index(..)) {
                utils::expr!(
                    "&{}({})",
                    if m { "mut " } else { "" },
                    pprust::expr_to_string(e),
                )
            } else {
                e.clone()
            }
        } else if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
            self.bytemuck.set(true);
            utils::expr!(
                "bytemuck::cast_slice{}::<_, {}>({})",
                if m { "_mut" } else { "" },
                lhs_ty,
                pprust::expr_to_string(e),
            )
        } else {
            let ptr_method = if m { "as_mut_ptr" } else { "as_ptr" };
            utils::expr!(
                "std::slice::from_raw_parts{0}(({1}).{2}() as *{3} {4}, (({1}).len() * std::mem::size_of::<{5}>()) / std::mem::size_of::<{4}>())",
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                ptr_method,
                if m { "mut" } else { "const" },
                lhs_ty,
                rhs_ty,
            )
        }
    }

    fn projected_opt_boxed_slice_expr(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
    ) -> Option<(Expr, ty::Ty<'tcx>)> {
        let mut expr = self.opt_boxed_slice_view_expr(pe.base, m);
        let mut from_ty = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx)?;
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    expr = utils::expr!(
                        "({})[({}) as usize..]",
                        pprust::expr_to_string(&expr),
                        pprust::expr_to_string(offset),
                    );
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => return None,
                PtrExprProj::Cast(ty) => {
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty)?;
                    expr = self.plain_slice_from_expr(&expr, m, to_ty, from_ty);
                    from_ty = to_ty;
                }
                PtrExprProj::IntegerOp(..) | PtrExprProj::IntegerBinOp(..) => return None,
            }
        }
        Some((expr, from_ty))
    }

    fn raw_from_opt_box(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let deref = if m { "as_deref_mut" } else { "as_deref" };
        let null = if m { "null_mut" } else { "null" };
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        if !need_cast {
            utils::expr!(
                "({}).{}().map_or(std::ptr::{}::<{}>(), |_x| _x)",
                pprust::expr_to_string(e),
                deref,
                null,
                lhs_ty,
            )
        } else {
            let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
            utils::expr!(
                "({}).{}().map_or(std::ptr::{}::<{}>(), |_x| _x as *{} {} as *{} {})",
                pprust::expr_to_string(e),
                deref,
                null,
                lhs_ty,
                if m { "mut" } else { "const" },
                rhs_ty,
                if m { "mut" } else { "const" },
                lhs_ty,
            )
        }
    }

    fn opt_ref_from_opt_box(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        if !need_cast {
            self.opt_box_view_expr(e, m)
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            self.bytemuck.set(true);
            utils::expr!(
                "({}).as_deref{}().map(|_x| bytemuck::cast_{}::<_, {}>(_x))",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
                if m { "mut" } else { "ref" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        } else {
            panic!("unsupported M4A casted OptBox -> OptRef reinterpretation")
        }
    }

    fn opt_box_from_opt_box(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4A does not support casted Option<Box<_>> reinterpretation"
        );
        e.clone()
    }

    fn opt_box_from_raw(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4B raw-to-box fallback requires matching pointee types"
        );
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        if !utils::ast::has_side_effects(e) {
            utils::expr!(
                "if ({0}).is_null() {{
                    None
                }} else {{
                    Some(unsafe {{ Box::from_raw(({0}) as *mut {1}) }})
                }}",
                pprust::expr_to_string(e),
                lhs_ty,
            )
        } else {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        None
                    }} else {{
                        Some(unsafe {{ Box::from_raw(_x as *mut {}) }})
                    }}
                }}",
                pprust::expr_to_string(e),
                lhs_ty,
            )
        }
    }

    fn opt_boxed_slice_from_opt_boxed_slice(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4A does not support casted Option<Box<[_]>> reinterpretation"
        );
        e.clone()
    }

    fn raw_from_opt_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        let extern_ty = matches!(rhs_inner_ty.kind(), ty::TyKind::Foreign(_));
        if extern_ty {
            utils::expr!(
                "match &{}({}) {{
                    Some(x) => *x as *{} {},
                    None => std::ptr::null{}(),
                }}",
                if m && m1 { "mut " } else { "" },
                pprust::expr_to_string(e),
                if m && m1 { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m && m1 { "_mut" } else { "" },
            )
        } else if !need_cast {
            utils::expr!(
                "({}).as_deref{1}().map_or(std::ptr::null{1}::<{2}>(), |_x| _x){3}",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                cast_mut,
            )
        } else {
            utils::expr!(
                "({}).as_deref{1}().map_or(std::ptr::null{1}::<{2}>(), |_x| _x as *{3} _ as *{3} _){4}",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m && m1 { "mut" } else { "const" },
                cast_mut,
            )
        }
    }

    fn raw_from_slice_or_cursor(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        if !need_cast {
            utils::expr!(
                "({}).as_{}ptr(){}",
                pprust::expr_to_string(e),
                if m && m1 { "mut_" } else { "" },
                cast_mut
            )
        } else {
            utils::expr!(
                "({}).as_{}ptr(){} as *{} _",
                pprust::expr_to_string(e),
                if m && m1 { "mut_" } else { "" },
                cast_mut,
                if m { "mut" } else { "const" },
            )
        }
    }

    fn opt_ref_from_raw(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        if !need_cast {
            utils::expr!(
                "({}){}.as_{}()",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "ref" },
            )
        } else {
            utils::expr!(
                "(({}){} as *{} {}).as_{}()",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m { "mut" } else { "ref" },
            )
        }
    }

    fn opt_ref_from_opt_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        if !need_cast {
            utils::expr!(
                "({}).as_deref{}()",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
            )
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            // can be used for deref, so type must be specified
            self.bytemuck.set(true);
            utils::expr!(
                "({}).as_deref{}().map(|_x| bytemuck::cast_{}::<_, {}>(_x))",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                if m && m1 { "mut" } else { "ref" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        } else {
            // can be used for deref, so type must be specified
            utils::expr!(
                "({}).as_deref{}().map(|_x| &{}*(_x as *{3} _ as *{3} {4}))",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                if m && m1 { "mut " } else { "" },
                if m && m1 { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn opt_ref_from_slice_or_cursor(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        if !need_cast {
            utils::expr!(
                "({}).first{}()",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
            )
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            self.bytemuck.set(true);
            utils::expr!(
                "({}).first{}().map(|_x| bytemuck::cast_{}(_x))",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
                if m { "mut" } else { "ref" },
            )
        } else {
            utils::expr!(
                "({}).first{}().map(|_x| &{}*(_x as *{3} _ as *{3} _))",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
                if m { "mut " } else { "" },
                if m { "mut" } else { "const" },
            )
        }
    }

    fn slice_from_raw(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { " as *mut _" } else { "" };
        if let Some(name) = method_call_name(e)
            && let name = name.as_str()
            && (name == "offset" || name == "as_mut_ptr" || name == "as_ptr")
        {
            // we assume that the pointer is not null when such methods are called
            if !need_cast {
                utils::expr!(
                    "std::slice::from_raw_parts{}(({}){}, 100000)",
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "std::slice::from_raw_parts{}(({}){} as *{} _, 100000)",
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !utils::ast::has_side_effects(e) {
            if !need_cast {
                utils::expr!(
                    "if ({0}).is_null() {{
                        &{1}[]
                    }} else {{
                        std::slice::from_raw_parts{2}(({0}){3}, 100000)
                    }}",
                    pprust::expr_to_string(e),
                    if m { "mut " } else { "" },
                    if m { "_mut" } else { "" },
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "if ({0}).is_null() {{
                        &{1}[]
                    }} else {{
                        std::slice::from_raw_parts{2}(({0}){3} as *{4} _, 100000)
                    }}",
                    pprust::expr_to_string(e),
                    if m { "mut " } else { "" },
                    if m { "_mut" } else { "" },
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !need_cast {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        &{}[]
                    }} else {{
                        std::slice::from_raw_parts{}(_x{}, 100000)
                    }}
                }}",
                pprust::expr_to_string(e),
                if m { "mut " } else { "" },
                if m { "_mut" } else { "" },
                cast_mut,
            )
        } else {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        &{}[]
                    }} else {{
                        std::slice::from_raw_parts{}(_x{} as *{} _, 100000)
                    }}
                }}",
                pprust::expr_to_string(e),
                if m { "mut " } else { "" },
                if m { "_mut" } else { "" },
                cast_mut,
                if m { "mut" } else { "const" },
            )
        }
    }

    fn cursor_from_raw(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { " as *mut _" } else { "" };
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursorMut"
        } else {
            "crate::slice_cursor::SliceCursor"
        };

        if let Some(name) = method_call_name(e)
            && let name = name.as_str()
            && (name == "offset" || name == "as_mut_ptr" || name == "as_ptr")
        {
            // we assume that the pointer is not null when such methods are called
            if !need_cast {
                utils::expr!(
                    "{}::from_raw_parts{}(({}){}, 100000)",
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "{}::from_raw_parts{}(({}){} as *{} _, 100000)",
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !utils::ast::has_side_effects(e) {
            if !need_cast {
                utils::expr!(
                    "if ({0}).is_null() {{
                        {1}::empty()
                    }} else {{
                        {1}::from_raw_parts{2}(({0}){3}, 100000)
                    }}",
                    pprust::expr_to_string(e),
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "if ({0}).is_null() {{
                        {1}::empty()
                    }} else {{
                        {1}::from_raw_parts{2}(({0}){3} as *{4} _, 100000)
                    }}",
                    pprust::expr_to_string(e),
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !need_cast {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        {}::empty()
                    }} else {{
                        {}::from_raw_parts{}(_x{}, 100000)
                    }}
                }}",
                pprust::expr_to_string(e),
                cursor_ty,
                cursor_ty,
                if m { "_mut" } else { "" },
                cast_mut,
            )
        } else {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        {}::empty()
                    }} else {{
                        {}::from_raw_parts{}(_x{} as *{} _, 100000)
                    }}
                }}",
                pprust::expr_to_string(e),
                cursor_ty,
                cursor_ty,
                if m { "_mut" } else { "" },
                cast_mut,
                if m { "mut" } else { "const" },
            )
        }
    }

    // slice -> slice
    fn plain_slice_from_slice(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let is_rewritten_slice_like_local = matches!(
            pe.base_kind,
            PtrExprBaseKind::Path(Res::Local(_))
        ) && matches!(
            self.ptr_source_kind(pe),
            Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_) | PtrKind::OptBoxedSlice)
        ) && pe.projs.is_empty();
        let get_reference = |use_ref| {
            if use_ref {
                if m { "&mut " } else { "&" }
            } else {
                ""
            }
        };
        if !need_cast {
            let reference = get_reference(
                pe.base_kind != PtrExprBaseKind::Alloca
                    && !is_rewritten_slice_like_local,
            );
            utils::expr!("{}({})", reference, pprust::expr_to_string(e),)
        } else if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
            self.bytemuck.set(true);
            let reference = get_reference(
                !matches!(e.kind, ExprKind::Index(..))
                    && pe.base_kind != PtrExprBaseKind::Alloca
                    && !is_rewritten_slice_like_local,
            );
            // can be used for deref, so type must be specified
            utils::expr!(
                "bytemuck::cast_slice{}::<_, {}>({}({}))",
                if m { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                reference,
                pprust::expr_to_string(e),
            )
        } else {
            // can be used for deref, so type must be specified
            utils::expr!(
                "std::slice::from_raw_parts{0}(({1}).as{0}_ptr() as *{2} {3}, 100000)",
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn cursor_from_slice_or_cursor(
        &self,
        e: &Expr,
        pe: &PtrExpr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        if is_plain_slice_expr(e) {
            self.cursor_from_plain_slice(e, pe, m, lhs_inner_ty, rhs_inner_ty)
        } else {
            self.cursor_from_cursor(e, m, lhs_inner_ty, rhs_inner_ty)
        }
    }

    fn cursor_from_plain_slice(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let is_rewritten_slice_like_local = matches!(
            pe.base_kind,
            PtrExprBaseKind::Path(Res::Local(_))
        ) && matches!(
            self.ptr_source_kind(pe),
            Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_) | PtrKind::OptBoxedSlice)
        ) && pe.projs.is_empty();
        let get_reference = |use_ref| {
            if use_ref {
                if m { "&mut " } else { "&" }
            } else {
                ""
            }
        };
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursorMut"
        } else {
            "crate::slice_cursor::SliceCursor"
        };

        if !need_cast {
            let reference =
                get_reference(pe.base_kind != PtrExprBaseKind::Alloca && !is_rewritten_slice_like_local);
            if pe.projs.len() == 1
                && let PtrExprProj::Offset(offset) = pe.projs[0]
            {
                // if there are only offsets, we can use the original slice and let the cursor handle the offsets
                utils::expr!(
                    "{}::with_pos({}{}, ({}) as usize)",
                    cursor_ty,
                    reference,
                    pprust::expr_to_string(pe.base),
                    pprust::expr_to_string(offset),
                )
            } else {
                utils::expr!(
                    "{}::new({}{})",
                    cursor_ty,
                    reference,
                    pprust::expr_to_string(e),
                )
            }
        } else if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
            let reference = get_reference(
                pe.base_kind != PtrExprBaseKind::Alloca
                    && !is_rewritten_slice_like_local,
            );
            self.bytemuck.set(true);
            utils::expr!(
                "{}::new(bytemuck::cast_slice{}::<_, {}>({}({})))",
                cursor_ty,
                if m { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                reference,
                pprust::expr_to_string(e),
            )
        } else {
            utils::expr!(
                "{}::from_raw_parts{}(({}).as_{}ptr() as *{} {}, 100000)",
                cursor_ty,
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                if m { "mut_" } else { "" },
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn cursor_from_cursor(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursorMut"
        } else {
            "crate::slice_cursor::SliceCursor"
        };
        if !need_cast {
            e.clone()
        } else if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
            self.bytemuck.set(true);
            utils::expr!(
                "{}::new(bytemuck::cast_slice{}::<_, {}>(({}).as_slice{}()))",
                cursor_ty,
                if m { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
            )
        } else {
            utils::expr!(
                "{}::from_raw_parts{}(({}).as_ptr() as *{} {}, 100000)",
                cursor_ty,
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn same_size(&self, ty1: ty::Ty<'tcx>, ty2: ty::Ty<'tcx>, def_id: LocalDefId) -> bool {
        utils::ir::ty_size(ty1, def_id, self.tcx) == utils::ir::ty_size(ty2, def_id, self.tcx)
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
            match self.effective_ptr_kind(hir_id) {
                Some(PtrKind::OptRef(m)) => Some(m),
                Some(PtrKind::OptBox | PtrKind::OptBoxedSlice) => Some(true),
                Some(PtrKind::Slice(m)) | Some(PtrKind::SliceCursor(m)) => Some(m),
                Some(PtrKind::Raw(m)) => Some(m),
                None => None,
            }
        } else {
            None
        }
    }

    fn ptr_expr<'a>(
        &self,
        expr: &'a Expr,
        hir_expr: &'a hir::Expr<'tcx>,
    ) -> Option<PtrExpr<'a, 'tcx>> {
        let expr = unwrap_addr_of_deref(expr);
        let hir_expr = hir_unwrap_addr_of_deref(hir_expr);
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        let base_ty = typeck.expr_ty(hir_expr);
        match &expr.kind {
            ExprKind::Path(_, _) => {
                let hir::ExprKind::Path(hir::QPath::Resolved(_, hpath)) = hir_expr.kind else {
                    panic!()
                };
                Some(PtrExpr::new(
                    expr,
                    hir_expr,
                    base_ty,
                    PtrExprBaseKind::Path(hpath.res),
                ))
            }
            ExprKind::Cast(e, _) => {
                let e = unwrap_cast_and_paren(e);
                let he = hir_unwrap_cast(hir_expr);
                let mut ptr_expr = self.ptr_expr(e, he)?;
                ptr_expr.push_cast(base_ty);
                if base_ty.is_usize() {
                    ptr_expr.cast_int = true;
                }
                Some(ptr_expr)
            }
            ExprKind::Field(_, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Index(_, _, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Unary(UnOp::Deref, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Call(_, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Lit(lit) => match lit.kind {
                token::LitKind::Integer if lit.symbol.as_str() == "0" => {
                    Some(PtrExpr::new(expr, hir_expr, base_ty, PtrExprBaseKind::Zero))
                }
                token::LitKind::ByteStr => Some(PtrExpr::new(
                    expr,
                    hir_expr,
                    base_ty,
                    PtrExprBaseKind::ByteStr,
                )),
                _ => None,
            },
            ExprKind::AddrOf(_, _, pointee) => {
                let hir::ExprKind::AddrOf(_, _, hpointee) = hir_expr.kind else { panic!() };
                let mut ptr_expr = self.ptr_expr(pointee, hpointee)?;
                if ptr_expr.addr_of {
                    None
                } else {
                    ptr_expr.addr_of = true;
                    Some(ptr_expr)
                }
            }
            ExprKind::MethodCall(call) => {
                let hir::ExprKind::MethodCall(seg, hreceiver, _, _) = hir_expr.kind else {
                    panic!()
                };
                let name = seg.ident.name.as_str();
                if name == "offset" {
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    ptr_expr.push_offset(&call.args[0]);
                    Some(ptr_expr)
                } else if name == "as_mut_ptr" || name == "as_ptr" {
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    if ptr_expr.as_ptr {
                        None
                    } else {
                        ptr_expr.as_ptr = true;
                        ptr_expr.as_mut_ptr = name == "as_mut_ptr";
                        Some(ptr_expr)
                    }
                } else if name == "unwrap"
                    && let ExprKind::MethodCall(call) = &call.receiver.kind
                    && let name = call.seg.ident.name.as_str()
                    && (name == "last_mut" || name == "last")
                {
                    Some(PtrExpr::new(
                        expr,
                        hir_expr,
                        base_ty,
                        PtrExprBaseKind::Alloca,
                    ))
                } else if name == "wrapping_add" || name == "wrapping_sub" {
                    let opkind = match name {
                        "wrapping_add" => OpKind::WrappingAdd,
                        "wrapping_sub" => OpKind::WrappingSub,
                        _ => panic!(),
                    };
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    ptr_expr.push_integer_op(&call.args[0], opkind);
                    Some(ptr_expr)
                } else {
                    Some(PtrExpr::new(
                        expr,
                        hir_expr,
                        base_ty,
                        PtrExprBaseKind::Other,
                    ))
                }
            }
            ExprKind::Binary(binop, lhs, rhs) if base_ty.is_usize() => {
                let hir::ExprKind::Binary(_, hlhs, _) = hir_expr.kind else { panic!() };
                let mut ptr_expr = self.ptr_expr(lhs, hlhs)?;
                ptr_expr.push_integer_bin_op(rhs, binop.node);
                Some(ptr_expr)
            }
            ExprKind::Array(..) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Array,
            )),
            _ => None,
        }
    }

    fn expr_ctx(&self, expr: &hir::Expr<'tcx>) -> ExprCtx {
        let mut init_id = expr.hir_id;
        let mut curr_id = expr.hir_id;
        for (parent_id, parent_node) in self.tcx.hir_parent_iter(expr.hir_id) {
            let hir::Node::Expr(parent) = parent_node else { return ExprCtx::Rvalue };
            match parent.kind {
                hir::ExprKind::Cast(..) | hir::ExprKind::Field(..) => {}
                hir::ExprKind::DropTemps(..) => {
                    if curr_id == init_id {
                        init_id = parent_id;
                    }
                }
                hir::ExprKind::Assign(l, _r, _) | hir::ExprKind::AssignOp(_, l, _r) => {
                    if curr_id == l.hir_id {
                        return ExprCtx::Lvalue;
                    } else {
                        return ExprCtx::Rvalue;
                    }
                }
                hir::ExprKind::Index(e, _idx, _) => {
                    if curr_id != e.hir_id {
                        return ExprCtx::Rvalue;
                    }
                }
                hir::ExprKind::AddrOf(_, m, _) => {
                    if curr_id == init_id {
                        return ExprCtx::ImmediatelyAddrTaken;
                    } else {
                        return ExprCtx::AddrTaken(m.is_mut());
                    }
                }
                hir::ExprKind::MethodCall(seg, receiver, _, _) => {
                    let name = seg.ident.name.as_str();
                    if curr_id != receiver.hir_id {
                        return ExprCtx::Rvalue;
                    } else if name == "as_mut_ptr" || name.starts_with("set_") {
                        return ExprCtx::AddrTaken(true);
                    } else if name == "as_ptr" {
                        return ExprCtx::AddrTaken(false);
                    } else {
                        return ExprCtx::Rvalue;
                    }
                }
                _ => return ExprCtx::Rvalue,
            }
            curr_id = parent_id;
        }
        ExprCtx::Rvalue
    }

    fn behind_subscripts(&self, expr: &hir::Expr<'tcx>) -> PathOrDeref {
        match hir_unwrap_subscript(expr).kind {
            hir::ExprKind::Path(_) => PathOrDeref::Path,
            hir::ExprKind::Unary(UnOp::Deref, e) => {
                let e = utils::hir::unwrap_drop_temps(e);
                let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = e.kind else {
                    return PathOrDeref::Other;
                };
                let Res::Local(hir_id) = path.res else { return PathOrDeref::Other };
                PathOrDeref::Deref(hir_id)
            }
            _ => PathOrDeref::Other,
        }
    }

    fn is_base_not_a_raw_ptr(&self, pe: &PtrExpr<'_, 'tcx>) -> bool {
        match pe.base_kind {
            PtrExprBaseKind::Path(_) | PtrExprBaseKind::Alloca | PtrExprBaseKind::Array => true,
            PtrExprBaseKind::Other => match self.behind_subscripts(pe.hir_base) {
                PathOrDeref::Path => true,
                PathOrDeref::Deref(hir_id) => {
                    matches!(
                        self.effective_ptr_kind(hir_id).unwrap_or(self.ptr_kinds[&hir_id]),
                        PtrKind::OptRef(_)
                            | PtrKind::OptBox
                            | PtrKind::OptBoxedSlice
                            | PtrKind::Slice(_)
                            | PtrKind::SliceCursor(_)
                    )
                }
                PathOrDeref::Other => pe.base_ty.is_array(),
            },
            _ => false,
        }
    }

    fn projected_expr(&self, pe: &PtrExpr<'_, 'tcx>, m: bool, mut is_raw: bool) -> Expr {
        let current_mut = self.ptr_source_kind(pe).map_or_else(
            || match pe.base_ty.kind() {
                ty::TyKind::RawPtr(_, m) => m.is_mut(),
                ty::TyKind::Array(..) => true,
                _ => m,
            },
            |kind| kind.is_mut(),
        );
        let mut is_plain_slice = if let PtrExprBaseKind::Path(Res::Local(hir_id)) = pe.base_kind {
            matches!(self.effective_ptr_kind(hir_id), Some(PtrKind::Slice(_)))
        } else {
            false
        };
        // A "data container" is a Vec/array accessed via as_ptr that is NOT a cursor.
        // For these, offsets should produce re-sliced expressions, not cursor operations.
        let is_data_container = pe.as_ptr
            || matches!(
                pe.base_kind,
                PtrExprBaseKind::Array | PtrExprBaseKind::Alloca
            );
        let is_mut_cursor_base = if let PtrExprBaseKind::Path(Res::Local(hir_id)) = pe.base_kind {
            matches!(
                self.ptr_kinds.get(&hir_id),
                Some(PtrKind::SliceCursor(true))
            )
        } else {
            false
        };
        let mut e = pe.base.clone();
        if pe.projs.is_empty() {
            return e;
        }
        let mut from_ty = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx).unwrap();
        let mut is_array = pe.base_ty.is_array();
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    if is_raw {
                        e = utils::expr!(
                            "({}).offset({})",
                            pprust::expr_to_string(&e),
                            pprust::expr_to_string(offset),
                        );
                    } else if is_data_container || is_plain_slice {
                        // Base is a data container (Vec, array) — return a re-sliced expression.
                        e = utils::expr!(
                            "({})[({}) as usize..]",
                            pprust::expr_to_string(&e),
                            pprust::expr_to_string(offset),
                        );
                    } else if m && is_mut_cursor_base {
                        e = utils::expr!(
                            "{{ let mut _c = ({}).as_deref_mut(); _c.seek(({}) as isize); _c }}",
                            pprust::expr_to_string(&e),
                            pprust::expr_to_string(offset),
                        );
                    } else {
                        e = utils::expr!(
                            "{{ let mut _c = ({}); _c.seek(({}) as isize); _c }}",
                            pprust::expr_to_string(&e),
                            pprust::expr_to_string(offset),
                        );
                    }
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => {
                    if is_raw {
                        e = utils::expr!("({}) as usize", pprust::expr_to_string(&e),);
                    } else {
                        e = utils::expr!(
                            "({}).as{}_ptr() as usize",
                            pprust::expr_to_string(&e),
                            if current_mut { "_mut" } else { "" },
                        );
                    }
                    is_raw = true;
                }
                PtrExprProj::Cast(ty) => {
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty).unwrap();
                    if is_raw {
                        e = utils::expr!(
                            "({}) as *{} {}",
                            pprust::expr_to_string(&e),
                            if m { "mut" } else { "const" },
                            mir_ty_to_string(to_ty, self.tcx),
                        );
                        from_ty = to_ty;
                    } else {
                        if matches!(e.kind, ExprKind::Index(..)) || is_array || is_plain_slice {
                            e = self.plain_slice_from_slice(&e, pe, current_mut, to_ty, from_ty);
                            is_plain_slice = true;
                        } else {
                            e = self.cursor_from_slice_or_cursor(
                                &e,
                                pe,
                                current_mut,
                                to_ty,
                                from_ty,
                            );
                        }
                        from_ty = to_ty;
                    }
                }
                PtrExprProj::IntegerOp(expr, op) => {
                    let method = match op {
                        OpKind::WrappingAdd => "wrapping_add",
                        OpKind::WrappingSub => "wrapping_sub",
                    };
                    e = utils::expr!(
                        "({}).{}({})",
                        pprust::expr_to_string(&e),
                        method,
                        pprust::expr_to_string(expr),
                    );
                }
                PtrExprProj::IntegerBinOp(expr, op) => {
                    let op_str = match op {
                        BinOpKind::BitAnd => "&",
                        BinOpKind::BitOr => "|",
                        _ => panic!(),
                    };
                    e = utils::expr!(
                        "({}) {} ({})",
                        pprust::expr_to_string(&e),
                        op_str,
                        pprust::expr_to_string(expr),
                    );
                }
            }
            is_array = false;
        }
        e
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PathOrDeref {
    Path,
    Deref(HirId),
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprCtx {
    Lvalue,
    Rvalue,
    ImmediatelyAddrTaken,
    AddrTaken(bool),
}

#[inline]
pub fn unwrap_ptr_from_mir_ty(ty: ty::Ty<'_>) -> Option<(ty::Ty<'_>, ty::Mutability)> {
    match ty.kind() {
        ty::TyKind::RawPtr(ty, m) | ty::TyKind::Ref(_, ty, m) => Some((*ty, *m)),
        _ => None,
    }
}

fn unwrap_ptr_or_arr_from_mir_ty<'tcx>(
    ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    match ty.kind() {
        ty::TyKind::RawPtr(ty, _)
        | ty::TyKind::Ref(_, ty, _)
        | ty::TyKind::Slice(ty)
        | ty::TyKind::Array(ty, _) => Some(*ty),
        ty::TyKind::Adt(adt_def, gargs) => {
            let name = tcx.item_name(adt_def.did());
            if name == rustc_span::sym::Vec {
                let ty::GenericArgKind::Type(ty) = gargs[0].kind() else { panic!() };
                Some(ty)
            } else {
                None
            }
        }
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
fn mk_opt_box_ty<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    utils::ty!("Option<Box<{ty}>>")
}

#[inline]
fn mk_opt_boxed_slice_ty<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    utils::ty!("Option<Box<[{ty}]>>")
}

#[inline]
fn mk_cursor_ty<'tcx>(ty: ty::Ty<'tcx>, mutability: bool, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    if mutability {
        utils::ty!("crate::slice_cursor::SliceCursorMut<'_, {ty}>")
    } else {
        utils::ty!("crate::slice_cursor::SliceCursor<'_, {ty}>")
    }
}

#[inline]
fn mk_slice_ty<'tcx>(ty: ty::Ty<'tcx>, mutability: bool, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    if mutability {
        utils::ty!("&mut [{ty}]")
    } else {
        utils::ty!("&[{ty}]")
    }
}

#[inline]
fn mk_raw_ptr_ty<'tcx>(ty: ty::Ty<'tcx>, mutability: bool, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    let m = if mutability { "mut" } else { "const" };
    utils::ty!("*{m} {ty}")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PtrExprBaseKind {
    Path(Res),
    Alloca,
    ByteStr,
    Zero,
    Array,
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpKind {
    WrappingAdd,
    WrappingSub,
}

#[derive(Debug, Clone, Copy)]
enum PtrExprProj<'a, 'tcx> {
    Offset(&'a Expr),
    Cast(ty::Ty<'tcx>),
    IntegerOp(&'a Expr, OpKind),
    IntegerBinOp(&'a Expr, BinOpKind),
}

#[derive(Debug, Clone)]
struct PtrExpr<'a, 'tcx> {
    addr_of: bool,
    base: &'a Expr,
    hir_base: &'a hir::Expr<'tcx>,
    base_ty: ty::Ty<'tcx>,
    base_kind: PtrExprBaseKind,
    as_ptr: bool,
    as_mut_ptr: bool,
    projs: Vec<PtrExprProj<'a, 'tcx>>,
    cast_int: bool,
}

impl<'a, 'tcx> PtrExpr<'a, 'tcx> {
    #[inline]
    fn new(
        base: &'a Expr,
        hir_base: &'a hir::Expr<'tcx>,
        base_ty: ty::Ty<'tcx>,
        base_kind: PtrExprBaseKind,
    ) -> Self {
        PtrExpr {
            addr_of: false,
            base,
            hir_base,
            base_ty,
            base_kind,
            as_ptr: false,
            as_mut_ptr: false,
            projs: vec![],
            cast_int: false,
        }
    }

    #[inline]
    fn push_offset(&mut self, offset: &'a Expr) {
        self.projs.push(PtrExprProj::Offset(offset));
    }

    #[inline]
    fn push_cast(&mut self, ty: ty::Ty<'tcx>) {
        self.projs.push(PtrExprProj::Cast(ty));
    }

    #[inline]
    fn push_integer_op(&mut self, expr: &'a Expr, op: OpKind) {
        self.projs.push(PtrExprProj::IntegerOp(expr, op));
    }

    #[inline]
    fn push_integer_bin_op(&mut self, expr: &'a Expr, op: BinOpKind) {
        self.projs.push(PtrExprProj::IntegerBinOp(expr, op));
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.base_kind == PtrExprBaseKind::Zero
            && self.projs.is_empty()
            && !self.addr_of
            && !self.as_ptr
    }
}

fn unwrap_addr_of_deref(expr: &Expr) -> &Expr {
    if let ExprKind::AddrOf(_, _, e) = &unwrap_paren(expr).kind
        && let ExprKind::Unary(UnOp::Deref, e) = &unwrap_paren(e).kind
    {
        unwrap_addr_of_deref(e)
    } else {
        unwrap_paren(expr)
    }
}

fn unwrap_addr_of_deref_mut(expr: &mut Expr) -> &mut Expr {
    let expr = unwrap_paren_mut(expr);
    if let ExprKind::AddrOf(_, _, e) = &unwrap_paren(expr).kind
        && let ExprKind::Unary(UnOp::Deref, _) = &unwrap_paren(e).kind
    {
        let ExprKind::AddrOf(_, _, e) = &mut expr.kind else { unreachable!() };
        let e = unwrap_paren_mut(e);
        let ExprKind::Unary(UnOp::Deref, e) = &mut e.kind else { unreachable!() };
        unwrap_addr_of_deref_mut(e)
    } else {
        expr
    }
}

fn unwrap_addr_of(expr: &Expr) -> &Expr {
    if let ExprKind::AddrOf(_, _, e) = &unwrap_paren(expr).kind {
        unwrap_addr_of(e)
    } else {
        unwrap_paren(expr)
    }
}

#[allow(unused)]
fn unwrap_subscript(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::Index(e, _, _) | ExprKind::Field(e, _) | ExprKind::Paren(e) => {
            unwrap_subscript(e)
        }
        _ => expr,
    }
}

#[allow(unused)]
fn unwrap_subscript_mut(expr: &mut Expr) -> &mut Expr {
    if !matches!(
        expr.kind,
        ExprKind::Index(_, _, _) | ExprKind::Field(_, _) | ExprKind::Paren(_)
    ) {
        return expr;
    }
    let (ExprKind::Index(e, _, _) | ExprKind::Field(e, _) | ExprKind::Paren(e)) = &mut expr.kind
    else {
        unreachable!()
    };
    unwrap_subscript_mut(e)
}

fn hir_unwrap_cast<'a, 'tcx>(expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    if let hir::ExprKind::Cast(e, _) = utils::hir::unwrap_drop_temps(expr).kind {
        hir_unwrap_cast(e)
    } else {
        utils::hir::unwrap_drop_temps(expr)
    }
}

fn hir_unwrap_addr_of_deref<'a, 'tcx>(expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    if let hir::ExprKind::AddrOf(_, _, e) = utils::hir::unwrap_drop_temps(expr).kind
        && let hir::ExprKind::Unary(UnOp::Deref, e) = utils::hir::unwrap_drop_temps(e).kind
    {
        hir_unwrap_addr_of_deref(e)
    } else {
        utils::hir::unwrap_drop_temps(expr)
    }
}

fn hir_unwrap_subscript<'a, 'tcx>(expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    match expr.kind {
        hir::ExprKind::Index(e, _, _)
        | hir::ExprKind::Field(e, _)
        | hir::ExprKind::DropTemps(e) => hir_unwrap_subscript(e),
        _ => expr,
    }
}

fn method_call_name(expr: &Expr) -> Option<Symbol> {
    if let ExprKind::MethodCall(call) = &unwrap_cast_and_paren(expr).kind {
        Some(call.seg.ident.name)
    } else {
        None
    }
}

fn is_null_ptr_constructor(expr: &Expr) -> bool {
    let ExprKind::Call(callee, args) = &unwrap_cast_and_paren(expr).kind else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    let ExprKind::Path(_, path) = &unwrap_paren(callee).kind else {
        return false;
    };
    path.segments
        .last()
        .is_some_and(|seg| matches!(seg.ident.name.as_str(), "null" | "null_mut"))
}

fn is_null_like_ptr_arg(expr: &Expr) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    if is_null_ptr_constructor(expr) {
        return true;
    }
    match &expr.kind {
        ExprKind::Lit(lit) => {
            matches!(lit.kind, token::LitKind::Integer) && lit.symbol.as_str() == "0"
        }
        ExprKind::Path(_, path) => path
            .segments
            .last()
            .is_some_and(|seg| seg.ident.name.as_str() == "NULL"),
        _ => false,
    }
}

fn expr_snippet(tcx: TyCtxt<'_>, expr: &Expr) -> Option<String> {
    tcx.sess
        .source_map()
        .span_to_snippet(expr.span)
        .ok()
        .map(|snippet| normalize_expr_snippet(&snippet))
}

fn ast_is_exact_size_of_expr(tcx: TyCtxt<'_>, expr: &Expr, ty_name: &str) -> bool {
    let Some(snippet) = expr_snippet(tcx, unwrap_cast_and_paren(expr)) else {
        return false;
    };
    [
        format!("::core::mem::size_of::<{ty_name}>()"),
        format!("core::mem::size_of::<{ty_name}>()"),
        format!("::std::mem::size_of::<{ty_name}>()"),
        format!("std::mem::size_of::<{ty_name}>()"),
    ]
    .into_iter()
    .map(|candidate| normalize_expr_snippet(&candidate))
    .any(|candidate| snippet == candidate)
}

fn ast_is_literal_one(expr: &Expr) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    matches!(expr.kind, ExprKind::Lit(lit) if matches!(lit.kind, token::LitKind::Integer) && lit.symbol.as_str() == "1")
}

fn expr_supports_scalar_opt_box_allocator_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &Expr,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    let ExprKind::Call(callee, args) = &unwrap_cast_and_paren(expr).kind else {
        return false;
    };
    let ExprKind::Path(_, path) = &unwrap_paren(callee).kind else {
        return false;
    };
    let Some(name) = path.segments.last().map(|seg| seg.ident.name.as_str()) else {
        return false;
    };
    let ty_name = mir_ty_to_string(lhs_inner_ty, tcx);
    match (name, &args[..]) {
        ("malloc", [bytes]) => ast_is_exact_size_of_expr(tcx, bytes, &ty_name),
        ("calloc", [count, elem_size]) => {
            ast_is_literal_one(count) && ast_is_exact_size_of_expr(tcx, elem_size, &ty_name)
        }
        ("realloc", [ptr, bytes]) if is_null_like_ptr_arg(ptr) => {
            ast_is_exact_size_of_expr(tcx, bytes, &ty_name)
        }
        _ => false,
    }
}

fn hir_unwrap_casts<'tcx>(mut expr: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
    loop {
        match expr.kind {
            hir::ExprKind::Cast(inner, _) | hir::ExprKind::DropTemps(inner) => expr = inner,
            _ => return expr,
        }
    }
}

fn hir_call_name(expr: &hir::Expr<'_>) -> Option<Symbol> {
    let hir::ExprKind::Call(callee, _) = hir_unwrap_casts(expr).kind else {
        return None;
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind else {
        return None;
    };
    path.segments.last().map(|seg| seg.ident.name)
}

fn normalize_expr_snippet(snippet: &str) -> String {
    snippet.chars().filter(|c| !c.is_whitespace()).collect()
}

fn hir_expr_snippet(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> Option<String> {
    tcx.sess
        .source_map()
        .span_to_snippet(expr.span)
        .ok()
        .map(|snippet| normalize_expr_snippet(&snippet))
}

fn hir_is_exact_size_of_expr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>, ty_name: &str) -> bool {
    let Some(snippet) = hir_expr_snippet(tcx, hir_unwrap_casts(expr)) else {
        return false;
    };
    [
        format!("::core::mem::size_of::<{ty_name}>()"),
        format!("core::mem::size_of::<{ty_name}>()"),
        format!("::std::mem::size_of::<{ty_name}>()"),
        format!("std::mem::size_of::<{ty_name}>()"),
    ]
    .into_iter()
    .map(|candidate| normalize_expr_snippet(&candidate))
    .any(|candidate| snippet == candidate)
}

fn hir_is_literal_one(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    hir_expr_snippet(tcx, hir_unwrap_casts(expr)).is_some_and(|snippet| snippet == "1")
}

fn hir_is_null_ptr_constructor(expr: &hir::Expr<'_>) -> bool {
    let hir::ExprKind::Call(callee, args) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind else {
        return false;
    };
    path.segments
        .last()
        .is_some_and(|seg| matches!(seg.ident.name.as_str(), "null" | "null_mut"))
}

fn hir_is_null_like_ptr_arg(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    let expr = hir_unwrap_casts(expr);
    if hir_is_null_ptr_constructor(expr) {
        return true;
    }
    match expr.kind {
        hir::ExprKind::Lit(_) => hir_expr_snippet(tcx, expr).is_some_and(|snippet| snippet == "0"),
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => path
            .segments
            .last()
            .is_some_and(|seg| seg.ident.name.as_str() == "NULL"),
        _ => false,
    }
}

fn hir_supports_scalar_box_allocator_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &hir::Expr<'_>,
) -> bool {
    let ty_name = mir_ty_to_string(lhs_inner_ty, tcx);
    let hir::ExprKind::Call(_, args) = hir_unwrap_casts(rhs).kind else {
        return false;
    };
    let Some(name) = hir_call_name(rhs) else {
        return false;
    };
    match (name, args) {
        (name, [bytes]) if name == Symbol::intern("malloc") => {
            hir_is_exact_size_of_expr(tcx, bytes, &ty_name)
        }
        (name, [count, elem_size]) if name == Symbol::intern("calloc") => {
            hir_is_literal_one(tcx, count) && hir_is_exact_size_of_expr(tcx, elem_size, &ty_name)
        }
        (name, [ptr, bytes])
            if name == Symbol::intern("realloc") && hir_is_null_like_ptr_arg(tcx, ptr) =>
        {
            hir_is_exact_size_of_expr(tcx, bytes, &ty_name)
        }
        _ => false,
    }
}

fn hir_is_supported_boxed_slice_allocator_root(tcx: TyCtxt<'_>, rhs: &hir::Expr<'_>) -> bool {
    let hir::ExprKind::Call(_, args) = hir_unwrap_casts(rhs).kind else {
        return false;
    };
    let Some(name) = hir_call_name(rhs) else {
        return false;
    };
    match (name, args) {
        (name, [_]) if name == Symbol::intern("malloc") => true,
        (name, [_, _]) if name == Symbol::intern("calloc") => true,
        (name, [ptr, _]) if name == Symbol::intern("realloc") => {
            hir_is_null_like_ptr_arg(tcx, ptr)
        }
        _ => false,
    }
}

fn hir_is_unsupported_scalar_box_allocator_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &hir::Expr<'_>,
) -> bool {
    matches!(
        hir_call_name(rhs),
        Some(name)
            if name == Symbol::intern("malloc")
                || name == Symbol::intern("calloc")
                || name == Symbol::intern("realloc")
    ) && !hir_supports_scalar_box_allocator_root(tcx, lhs_inner_ty, rhs)
}

fn fn_has_unsupported_scalar_box_assignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    target_hir_id: HirId,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    fn_has_unsupported_box_assignment(
        tcx,
        &SigDecisions {
            data: FxHashMap::default(),
        },
        &FxHashMap::default(),
        target_hir_id,
        PtrKind::OptBox,
        lhs_inner_ty,
    )
}

fn fn_has_unsupported_box_assignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    target_hir_id: HirId,
    target_kind: PtrKind,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    struct AssignmentVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_hir_id: HirId,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for AssignmentVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let Res::Local(lhs_hir_id) = path.res
                    && lhs_hir_id == self.target_hir_id
                    && !hir_rhs_supports_box_target(
                        self.tcx,
                        self.sig_decs,
                        self.ptr_kinds,
                        rhs,
                        self.target_kind,
                        self.lhs_inner_ty,
                    )
                {
                    self.found = true;
                    return;
                }
                intravisit::walk_expr(self, expr);
        }
    }

    let body_id = tcx.hir_body_owned_by(target_hir_id.owner.def_id);
    let mut visitor = AssignmentVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        target_hir_id,
        target_kind,
        lhs_inner_ty,
        found: false,
    };
    visitor.visit_body(body_id);
    visitor.found
}

fn fn_tail_returns_unsupported_box_binding<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    owner: LocalDefId,
    target_kind: PtrKind,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    fn returned_expr_is_unsupported<'tcx>(
        tcx: TyCtxt<'tcx>,
        sig_decs: &SigDecisions,
        ptr_kinds: &FxHashMap<HirId, PtrKind>,
        expr: &hir::Expr<'tcx>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> bool {
        if !hir_rhs_supports_box_target(tcx, sig_decs, ptr_kinds, expr, target_kind, lhs_inner_ty) {
            return true;
        }
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind else {
            return false;
        };
        let Res::Local(hir_id) = path.res else {
            return false;
        };
        fn_has_unsupported_box_assignment(tcx, sig_decs, ptr_kinds, hir_id, target_kind, lhs_inner_ty)
    }

    struct ReturnVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for ReturnVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Ret(Some(ret)) = expr.kind
                && returned_expr_is_unsupported(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    ret,
                    self.target_kind,
                    self.lhs_inner_ty,
                )
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let body = tcx.hir_body_owned_by(owner);
    let mut visitor = ReturnVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        target_kind,
        lhs_inner_ty,
        found: false,
    };
    visitor.visit_body(body);
    if visitor.found {
        return true;
    }

    let hir::ExprKind::Block(block, _) = body.value.kind else {
        return false;
    };
    let Some(tail) = block.expr else {
        return false;
    };
    returned_expr_is_unsupported(tcx, sig_decs, ptr_kinds, tail, target_kind, lhs_inner_ty)
}

fn normalize_forced_raw_bindings(
    ptr_kinds: &mut FxHashMap<HirId, PtrKind>,
    forced_raw_bindings: &FxHashSet<HirId>,
) {
    for (hir_id, kind) in ptr_kinds.iter_mut() {
        if forced_raw_bindings.contains(hir_id)
            && matches!(kind, PtrKind::OptBox | PtrKind::OptBoxedSlice)
        {
            *kind = PtrKind::Raw(true);
        }
    }
}

fn downgrade_unsupported_box_outputs<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> bool {
    let mut to_raw = Vec::new();
    for (did, sig_dec) in &sig_decs.data {
        let Some(output_kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) = sig_dec.output_dec
        else {
            continue;
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let Some((inner_ty, _)) =
            unwrap_ptr_from_mir_ty(body.local_decls[rustc_middle::mir::Local::from_u32(0)].ty)
        else {
            continue;
        };
        if fn_tail_returns_unsupported_box_binding(
            tcx,
            sig_decs,
            ptr_kinds,
            *did,
            output_kind,
            inner_ty,
        ) {
            to_raw.push(*did);
        }
    }
    let changed = !to_raw.is_empty();
    for did in to_raw {
        if let Some(sig_dec) = sig_decs.data.get_mut(&did) {
            sig_dec.output_dec = Some(PtrKind::Raw(true));
        }
    }
    changed
}

fn hir_callee_output_kind(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    hir_expr: &hir::Expr<'_>,
) -> Option<PtrKind> {
    let hir::ExprKind::Call(func, _) = hir_expr.kind else {
        return None;
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind else {
        return None;
    };
    let Res::Def(_, def_id) = path.res else {
        return None;
    };
    let def_id = def_id.as_local()?;
    if !local_def_id_has_fn_body(tcx, def_id) {
        return None;
    }
    sig_decs.data.get(&def_id)?.output_dec
}

fn local_def_id_has_fn_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    matches!(
        tcx.hir_node_by_def_id(def_id),
        hir::Node::Item(hir::Item {
            kind: hir::ItemKind::Fn { .. },
            ..
        })
    )
}

fn hir_call_matches_foreign_name(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>, name: &str) -> bool {
    let hir::ExprKind::Call(func, _) = expr.kind else {
        return false;
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(func).kind else {
        return false;
    };
    if path
        .segments
        .last()
        .is_none_or(|seg| seg.ident.name.as_str() != name)
    {
        return false;
    }
    let Res::Def(_, def_id) = path.res else {
        return false;
    };
    !def_id
        .as_local()
        .is_some_and(|local| local_def_id_has_fn_body(tcx, local))
}

fn hir_free_arg_local_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> Option<(HirId, &'tcx hir::Expr<'tcx>)> {
    if !hir_call_matches_foreign_name(tcx, expr, "free") {
        return None;
    }
    let hir::ExprKind::Call(_, args) = expr.kind else {
        return None;
    };
    let [arg] = args else { return None };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(arg).kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    Some((hir_id, arg))
}

fn hir_unwrapped_local_id(expr: &hir::Expr<'_>) -> Option<HirId> {
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    Some(hir_id)
}

fn collect_scalar_raw_bridge_bindings(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    #[derive(Default)]
    struct State {
        saw_bridge: bool,
        saw_free: bool,
        disqualified: bool,
    }

    struct RawScalarBridgeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        states: FxHashMap<HirId, State>,
    }

    impl<'tcx> RawScalarBridgeVisitor<'_, 'tcx> {
        fn update_rhs(&mut self, hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>, lhs_inner_ty: ty::Ty<'tcx>) {
            let state = self.states.entry(hir_id).or_default();
            if hir_supports_scalar_box_allocator_root(self.tcx, lhs_inner_ty, rhs) {
                state.saw_bridge = true;
            } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                state.disqualified = true;
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for RawScalarBridgeVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
                && let Some(init) = let_stmt.init
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                if let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) {
                    self.update_rhs(hir_id, init, lhs_inner_ty);
                }
            }
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let Some(init) = let_stmt.init
                && let Some(rhs_hir_id) = hir_unwrapped_local_id(init)
                && matches!(self.ptr_kinds.get(&rhs_hir_id), Some(PtrKind::Raw(_)))
            {
                self.states.entry(rhs_hir_id).or_default().disqualified = true;
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
                && matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                if let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) {
                    self.update_rhs(hir_id, rhs, lhs_inner_ty);
                }
            }
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs)
                && matches!(self.ptr_kinds.get(&rhs_hir_id), Some(PtrKind::Raw(_)))
            {
                let lhs_hir_id = hir_unwrapped_local_id(lhs);
                if lhs_hir_id != Some(rhs_hir_id) {
                    self.states.entry(rhs_hir_id).or_default().disqualified = true;
                }
            }
            if let Some((hir_id, _)) = hir_free_arg_local_id(self.tcx, expr)
                && matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
            {
                self.states.entry(hir_id).or_default().saw_free = true;
            }
            if let hir::ExprKind::Call(_, args) = expr.kind
                && !hir_call_matches_foreign_name(self.tcx, expr, "free")
            {
                for arg in args {
                    if let Some(hir_id) = hir_unwrapped_local_id(arg)
                        && matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
                    {
                        self.states.entry(hir_id).or_default().disqualified = true;
                    }
                }
            }
            if let hir::ExprKind::Ret(Some(ret)) = expr.kind
                && let Some(hir_id) = hir_unwrapped_local_id(ret)
                && matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
            {
                self.states.entry(hir_id).or_default().disqualified = true;
            }
            intravisit::walk_expr(self, expr);
        }

        fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
            intravisit::walk_body(self, body);
            if let Some(hir_id) = hir_unwrapped_local_id(body.value)
                && matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
            {
                self.states.entry(hir_id).or_default().disqualified = true;
            }
        }
    }

    let mut bindings = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawScalarBridgeVisitor {
            tcx,
            ptr_kinds,
            states: FxHashMap::default(),
        };
        visitor.visit_body(body);
        bindings.extend(visitor.states.into_iter().filter_map(|(hir_id, state)| {
            (state.saw_bridge && state.saw_free && !state.disqualified).then_some(hir_id)
        }));
    }
    bindings
}

fn collect_raw_call_result_bindings(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
) -> FxHashSet<HirId> {
    struct RawCallResultVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for RawCallResultVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, ident, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && matches!(
                    hir_callee_output_kind(self.tcx, self.sig_decs, init),
                    Some(PtrKind::Raw(_))
                )
            {
                let _ = ident;
                self.bindings.insert(hir_id);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
                && matches!(
                    hir_callee_output_kind(self.tcx, self.sig_decs, rhs),
                    Some(PtrKind::Raw(_))
                )
            {
                self.bindings.insert(hir_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawCallResultVisitor {
            tcx,
            sig_decs,
            bindings: FxHashSet::default(),
        };
        visitor.visit_expr(body.value);
        bindings.extend(visitor.bindings);
    }
    bindings
}

fn collect_raw_local_assignment_bindings(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct RawLocalBindingVisitor<'a, 'tcx> {
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        bindings: FxHashSet<HirId>,
        _marker: std::marker::PhantomData<TyCtxt<'tcx>>,
    }

    impl<'tcx> Visitor<'tcx> for RawLocalBindingVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, lhs_path)) = lhs.kind
                && let Res::Local(lhs_hir_id) = lhs_path.res
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, rhs_path)) = rhs.kind
                && let Res::Local(rhs_hir_id) = rhs_path.res
                && matches!(self.ptr_kinds.get(&rhs_hir_id), Some(PtrKind::Raw(_)))
            {
                self.bindings.insert(lhs_hir_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawLocalBindingVisitor {
            ptr_kinds,
            bindings: FxHashSet::default(),
            _marker: std::marker::PhantomData,
        };
        visitor.visit_expr(body.value);
        bindings.extend(visitor.bindings);
    }
    bindings
}

fn hir_rhs_supports_box_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    hir_expr: &hir::Expr<'_>,
    target_kind: PtrKind,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    let hir_uncast = hir_unwrap_casts(hir_expr);
    if hir_is_null_like_ptr_arg(tcx, hir_uncast) {
        return true;
    }

    match target_kind {
        PtrKind::OptBox => {
            if hir_supports_scalar_box_allocator_root(tcx, lhs_inner_ty, hir_uncast) {
                return true;
            }
        }
        PtrKind::OptBoxedSlice => {
            if hir_is_supported_boxed_slice_allocator_root(tcx, hir_uncast) {
                return true;
            }
        }
        _ => return true,
    }

    if let hir::ExprKind::Call(..) = hir_expr.kind
        && hir_callee_output_kind(tcx, sig_decs, hir_expr) == Some(target_kind)
    {
        return true;
    }

    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind
        && let Res::Local(hir_id) = path.res
        && ptr_kinds.get(&hir_id).copied() == Some(target_kind)
    {
        return true;
    }

    false
}

fn collect_unsupported_box_target_bindings(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct UnsupportedBoxBindingVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for UnsupportedBoxBindingVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && let Some(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) =
                    self.ptr_kinds.get(&hir_id).copied()
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                if !hir_rhs_supports_box_target(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    init,
                    kind,
                    lhs_inner_ty,
                ) {
                    self.bindings.insert(hir_id);
                }
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
                && let Some(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) =
                    self.ptr_kinds.get(&hir_id).copied()
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                if !hir_rhs_supports_box_target(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    rhs,
                    kind,
                    lhs_inner_ty,
                ) {
                    self.bindings.insert(hir_id);
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = UnsupportedBoxBindingVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            bindings: FxHashSet::default(),
        };
        visitor.visit_expr(body.value);
        bindings.extend(visitor.bindings);
    }
    bindings
}

fn downgrade_unsupported_allocator_box_kinds(
    tcx: TyCtxt<'_>,
) -> FxHashSet<HirId> {
    struct BoxDowngradeVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
        downgraded: FxHashSet<HirId>,
    }

    impl<'tcx> BoxDowngradeVisitor<'tcx> {
        fn maybe_downgrade(
            &mut self,
            hir_id: HirId,
            lhs_ty: ty::Ty<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            if !matches!(
                hir_call_name(rhs),
                Some(name)
                    if matches!(
                        name,
                        _ if name == Symbol::intern("malloc")
                            || name == Symbol::intern("calloc")
                            || name == Symbol::intern("realloc")
                    )
            ) {
                return;
            }
            if !hir_supports_scalar_box_allocator_root(self.tcx, inner_ty, rhs) {
                self.downgraded.insert(hir_id);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for BoxDowngradeVisitor<'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, ident, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                let _ = ident;
                self.maybe_downgrade(hir_id, lhs_ty, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                self.maybe_downgrade(hir_id, lhs_ty, rhs);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut downgraded: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = BoxDowngradeVisitor {
            tcx,
            downgraded: FxHashSet::default(),
        };
        visitor.visit_expr(body.value);
        downgraded.extend(visitor.downgraded);
    }

    downgraded
}

fn is_std_slice_constructor_call(expr: &Expr) -> bool {
    if let ExprKind::Call(callee, _) = &unwrap_cast_and_paren(expr).kind
        && let ExprKind::Path(_, path) = &unwrap_paren(callee).kind
    {
        let segs = &path.segments;
        if segs.len() >= 2 {
            let ctor = segs[segs.len() - 1].ident.name.as_str();
            let owner = segs[segs.len() - 2].ident.name.as_str();
            return owner == "slice"
                && matches!(
                    ctor,
                    "from_mut" | "from_ref" | "from_raw_parts" | "from_raw_parts_mut"
                );
        }
    }
    false
}

fn is_plain_slice_expr(expr: &Expr) -> bool {
    let expr = unwrap_paren(expr);
    if matches!(expr.kind, ExprKind::Index(..) | ExprKind::Array(..)) {
        return true;
    }
    if let ExprKind::MethodCall(call) = &expr.kind
        && matches!(call.seg.ident.name.as_str(), "as_slice" | "as_slice_mut")
    {
        return true;
    }
    if is_std_slice_constructor_call(expr) {
        return true;
    }
    false
}

fn hoist_opt_ref_borrow(expr: &mut Expr) {
    let mut visitor = OptRefBorrowVisitor::default();
    visitor.visit_expr(expr);

    let mut lets = String::new();
    for (name, uses) in &visitor.args {
        let total_uses = uses.raw_mut + uses.unwrap_mut + uses.unwrap_shared;
        if uses.unwrap_mut == 0 && !(uses.raw_mut > 0 && total_uses > 1) {
            continue;
        }
        use std::fmt::Write as _;
        let new_name = format!("{name}_borrowed");
        write!(
            &mut lets,
            "let {new_name} = {name}.as_deref_mut().unwrap();",
        )
        .unwrap();
        visitor.rewrite_targets.insert(*name, new_name);
    }
    if !lets.is_empty() {
        visitor.visit_expr(expr);
        *expr = utils::expr!("{{ {lets} {} }}", pprust::expr_to_string(expr))
    }
}

#[derive(Default)]
struct OptRefBorrowVisitor {
    rewrite_targets: FxHashMap<Symbol, String>,
    args: FxHashMap<Symbol, BorrowUseCounts>,
}

#[derive(Default)]
struct BorrowUseCounts {
    raw_mut: usize,
    unwrap_mut: usize,
    unwrap_shared: usize,
}

struct CapturePathRewriter<'a> {
    from: Symbol,
    to: &'a str,
}

impl mut_visit::MutVisitor for CapturePathRewriter<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);
        if let ExprKind::Path(_, path) = &expr.kind
            && path.segments.len() == 1
            && path.segments[0].ident.name == self.from
        {
            *expr = utils::expr!("{}", self.to);
        }
    }
}

fn unwrap_opt_deref_call(expr: &mut Expr) -> Option<(Symbol, bool)> {
    let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(expr).kind else {
        return None;
    };
    if call.seg.ident.name != rustc_span::sym::unwrap {
        return None;
    }
    let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(&mut call.receiver).kind else {
        return None;
    };
    let method = call.seg.ident.name.as_str();
    let is_mut = method == "as_deref_mut";
    if !is_mut && method != "as_deref" {
        return None;
    }
    let ExprKind::Path(_, path) = &mut unwrap_paren_mut(&mut call.receiver).kind else {
        return None;
    };
    Some((path.segments.last()?.ident.name, is_mut))
}

fn null_ptr_inner_ty(expr: &Expr) -> Option<String> {
    let expr = pprust::expr_to_string(expr);
    let (_, rest) = expr.rsplit_once("::<")?;
    let (ty, _) = rest.split_once(">()")?;
    Some(ty.to_string())
}

fn raw_map_or_opt_deref(expr: &mut Expr) -> Option<(Symbol, String, &mut Expr)> {
    let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(expr).kind else {
        return None;
    };
    if call.seg.ident.name.as_str() != "map_or" || call.args.len() != 2 {
        return None;
    }
    let ExprKind::MethodCall(receiver_call) = &mut unwrap_paren_mut(&mut call.receiver).kind else {
        return None;
    };
    if receiver_call.seg.ident.name.as_str() != "as_deref_mut" {
        return None;
    }
    let ExprKind::Path(_, path) = &mut unwrap_paren_mut(&mut receiver_call.receiver).kind else {
        return None;
    };
    let pointee_ty = null_ptr_inner_ty(&call.args[0])?;
    let ExprKind::Closure(box closure) = &mut call.args[1].kind else {
        return None;
    };
    Some((path.segments.last()?.ident.name, pointee_ty, &mut closure.body))
}

impl mut_visit::MutVisitor for OptRefBorrowVisitor {
    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        if let Some((name, is_mut)) = unwrap_opt_deref_call(expr) {
            if self.rewrite_targets.is_empty() {
                let uses = self.args.entry(name).or_default();
                if is_mut {
                    uses.unwrap_mut += 1;
                } else {
                    uses.unwrap_shared += 1;
                }
            } else if let Some(new_name) = self.rewrite_targets.get(&name) {
                *expr = utils::expr!("{new_name}");
            }
            return;
        }

        if let Some((name, pointee_ty, body)) = raw_map_or_opt_deref(expr) {
            if self.rewrite_targets.is_empty() {
                self.args.entry(name).or_default().raw_mut += 1;
            } else if let Some(new_name) = self.rewrite_targets.get(&name) {
                let mut replacement = body.clone();
                let replacement_expr = format!("({new_name} as *mut {pointee_ty})");
                let mut rewriter = CapturePathRewriter {
                    from: Symbol::intern("_x"),
                    to: &replacement_expr,
                };
                rewriter.visit_expr(&mut replacement);
                *expr = replacement;
            }
        }
    }

}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use rustc_ast::{Crate, Expr, ItemKind, LocalKind, PatKind, StmtKind};
    use rustc_ast_pretty::pprust;
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::{ItemKind as HirItemKind, OwnerNode};
    use rustc_middle::ty::{self, TyCtxt};

    use super::*;

    fn synthetic_transform_visitor<'tcx>(tcx: TyCtxt<'tcx>) -> TransformVisitor<'tcx> {
        TransformVisitor {
            tcx,
            sig_decs: SigDecisions {
                data: FxHashMap::default(),
            },
            ptr_kinds: FxHashMap::default(),
            forced_raw_bindings: FxHashSet::default(),
            raw_scalar_bridge_bindings: FxHashSet::default(),
            ast_to_hir: AstToHir::default(),
            bytemuck: Cell::new(false),
            slice_cursor: Cell::new(false),
        }
    }

    fn find_struct_ty<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> ty::Ty<'tcx> {
        tcx.hir_crate(())
            .owners
            .iter()
            .filter_map(|maybe_owner| {
                let owner = maybe_owner.as_owner()?;
                let OwnerNode::Item(item) = owner.node() else {
                    return None;
                };
                match item.kind {
                    HirItemKind::Struct(..)
                        if tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == name =>
                    {
                        Some(tcx.type_of(item.owner_id.def_id).instantiate_identity())
                    }
                    _ => None,
                }
            })
            .next()
            .expect("expected local struct type")
    }

    fn find_local_init_expr<'a>(krate: &'a Crate, fn_name: &str, local_name: &str) -> &'a Expr {
        krate
            .items
            .iter()
            .find_map(|item| {
                let ItemKind::Fn(box fn_item) = &item.kind else {
                    return None;
                };
                if fn_item.ident.name.as_str() != fn_name {
                    return None;
                }
                let body = fn_item.body.as_ref()?;
                body.stmts.iter().find_map(|stmt| {
                    let StmtKind::Let(local) = &stmt.kind else {
                        return None;
                    };
                    let PatKind::Ident(_, ident, _) = &local.pat.kind else {
                        return None;
                    };
                    if ident.name.as_str() != local_name {
                        return None;
                    }
                    match &local.kind {
                        LocalKind::Init(expr) | LocalKind::InitElse(expr, _) => Some(expr.as_ref()),
                        LocalKind::Decl => None,
                    }
                })
            })
            .expect("expected matching local initializer")
    }

    #[test]
    fn struct_default_materialization_uses_recursive_defaults() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct StructDefaultProbe {
    pub next: *mut i32,
    pub value: i32,
}

pub unsafe fn alloc_struct() {
    let state: *mut StructDefaultProbe =
        malloc(std::mem::size_of::<crate::StructDefaultProbe>()) as *mut crate::StructDefaultProbe;
    let _ = state;
}
"#;

        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut krate = ::utils::ast::expanded_ast(tcx);
            ::utils::ast::remove_unnecessary_items_from_ast(&mut krate);

            let struct_ty = find_struct_ty(tcx, "StructDefaultProbe");
            let init_expr = find_local_init_expr(&krate, "alloc_struct", "state");
            let mut materialized = init_expr.clone();
            let visitor = synthetic_transform_visitor(tcx);

            let kind = visitor.try_materialize_box_allocator_root(
                &mut materialized,
                init_expr,
                PtrKind::OptBox,
                struct_ty,
            );
            assert_eq!(kind, Some(PtrKind::OptBox));

            let emitted = pprust::expr_to_string(&materialized);
            assert!(emitted.contains("Some(Box::<crate::StructDefaultProbe>::new("), "{emitted}");
            assert!(
                emitted.contains("crate::StructDefaultProbe {"),
                "{emitted}"
            );
            assert!(
                emitted.contains("next: std::ptr::null_mut::<i32>()"),
                "{emitted}"
            );
            assert!(
                emitted.contains("value: <i32 as Default>::default()"),
                "{emitted}"
            );

            let check_code = format!(
                r#"
#[repr(C)]
pub struct StructDefaultProbe {{
    pub next: *mut i32,
    pub value: i32,
}}

pub fn check() {{
    let _: Option<Box<crate::StructDefaultProbe>> = {emitted};
}}
"#
            );
            ::utils::compilation::run_compiler_on_str(&check_code, ::utils::type_check)
                .expect(&check_code);
        })
        .unwrap();
    }
}
