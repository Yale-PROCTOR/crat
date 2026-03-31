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
    raw_bridge_bindings: FxHashMap<HirId, RawBridgeInfo>,
    alloc_wrappers: FxHashMap<LocalDefId, AllocWrapperInfo>,
    free_like_wrappers: FxHashSet<LocalDefId>,
    ast_to_hir: AstToHir,
    pub bytemuck: Cell<bool>,
    pub slice_cursor: Cell<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum RawBridgeInfo {
    Scalar,
    Array { len_expr: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AllocWrapperInfo {
    Fixed(RawBridgeInfo),
    Bytes {
        bytes_param: usize,
    },
    CountSize {
        count_param: usize,
        elem_size_param: usize,
    },
    Realloc {
        ptr_param: usize,
        bytes_param: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LocalRawParamSummary {
    BorrowOnly,
    Escapes,
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
            let (lhs_inner_ty, lhs_mutability) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
            let original_lhs_kind = lhs_kind;
            if let Some(init) = let_stmt.init
                && matches!(
                    self.forced_local_callee_output_kind(init),
                    Some(PtrKind::Raw(_))
                )
            {
                lhs_kind = PtrKind::Raw(lhs_mutability.is_mut());
            }
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
                if !self.try_bridge_raw_root(rhs, hir_rhs, lhs_kind, lhs_inner_ty, Some(hir_id)) {
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
                    self.effective_ptr_kind(hir_id)
                        .unwrap_or(PtrKind::Raw(m.is_mut()))
                } else {
                    PtrKind::Raw(m.is_mut())
                };
                let original_lhs_kind = lhs_kind;
                if matches!(
                    self.forced_local_callee_output_kind(hir_rhs),
                    Some(PtrKind::Raw(_))
                ) {
                    lhs_kind = PtrKind::Raw(m.is_mut());
                }
                if matches!(lhs_kind, PtrKind::OptBox | PtrKind::OptBoxedSlice)
                    && !self.rhs_supports_box_target(hir_rhs, lhs_kind, lhs_inner_ty)
                {
                    lhs_kind = PtrKind::Raw(true);
                } else if matches!(lhs_kind, PtrKind::OptBox) {
                    if hir_is_unsupported_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_rhs)
                    {
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
                            && !self.try_bridge_raw_root(
                                rhs,
                                hir_rhs,
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
                            && !self.try_bridge_raw_root(
                                rhs,
                                hir_rhs,
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
                                PtrKind::Raw(
                                    self.get_mutability_decision(harg).unwrap_or(m.is_mut()),
                                )
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
                if let Some((_, raw_mut)) =
                    unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(hir_receiver))
                {
                    self.transform_ptr(
                        receiver,
                        hir_receiver,
                        PtrCtx::Rhs(PtrKind::Raw(raw_mut.is_mut())),
                    );
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
                        && matches!(
                            self.effective_ptr_kind(hir_id),
                            Some(PtrKind::SliceCursor(_))
                        )
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
        let free_like_wrappers = collect_local_free_wrappers(rust_program.tcx);
        let local_raw_free_summaries =
            collect_local_raw_free_summaries(rust_program.tcx, &free_like_wrappers);
        let local_raw_param_summaries =
            collect_local_raw_param_summaries(rust_program.tcx, &free_like_wrappers);
        let mut forced_raw_bindings =
            downgrade_unsupported_allocator_box_kinds(rust_program.tcx, &ptr_kinds);
        normalize_forced_raw_bindings(rust_program.tcx, &mut ptr_kinds, &forced_raw_bindings);
        loop {
            let mut changed = false;
            let (box_input_changed, unsupported_box_input_bindings) =
                downgrade_unsupported_box_inputs(
                    rust_program.tcx,
                    &mut sig_decs,
                    &local_raw_free_summaries,
                );
            if box_input_changed {
                changed = true;
            }
            if downgrade_unsupported_box_outputs(rust_program.tcx, &mut sig_decs, &ptr_kinds) {
                changed = true;
            }
            let raw_call_result_bindings =
                collect_raw_call_result_bindings(rust_program.tcx, &sig_decs, &ptr_kinds);
            let raw_local_assignment_bindings =
                collect_raw_local_assignment_bindings(rust_program.tcx, &ptr_kinds);
            let unsupported_box_target_bindings =
                collect_unsupported_box_target_bindings(rust_program.tcx, &sig_decs, &ptr_kinds);
            let unsupported_box_usage_bindings = collect_unsupported_box_usage_bindings(
                rust_program.tcx,
                &ptr_kinds,
                &free_like_wrappers,
                &local_raw_param_summaries,
            );
            let old_len = forced_raw_bindings.len();
            forced_raw_bindings.extend(unsupported_box_input_bindings);
            forced_raw_bindings.extend(raw_call_result_bindings);
            forced_raw_bindings.extend(raw_local_assignment_bindings);
            forced_raw_bindings.extend(unsupported_box_target_bindings);
            forced_raw_bindings.extend(unsupported_box_usage_bindings);
            if forced_raw_bindings.len() != old_len {
                changed = true;
                normalize_forced_raw_bindings(
                    rust_program.tcx,
                    &mut ptr_kinds,
                    &forced_raw_bindings,
                );
            }
            if !changed {
                break;
            }
        }

        let alloc_wrappers = collect_local_allocator_wrappers(rust_program.tcx);
        let raw_bridge_bindings = collect_raw_bridge_bindings(
            rust_program.tcx,
            &ptr_kinds,
            &alloc_wrappers,
            &free_like_wrappers,
            &local_raw_param_summaries,
        );

        TransformVisitor {
            tcx: rust_program.tcx,
            sig_decs,
            ptr_kinds,
            forced_raw_bindings,
            raw_bridge_bindings,
            alloc_wrappers,
            free_like_wrappers,
            ast_to_hir,
            bytemuck: Cell::new(false),
            slice_cursor: Cell::new(false),
        }
    }

    fn try_bridge_raw_root(
        &self,
        rhs: &mut Expr,
        hir_rhs: &'tcx hir::Expr<'tcx>,
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
        let Some(current_info) = hir_raw_bridge_info(
            self.tcx,
            lhs_inner_ty,
            hir_rhs,
            Some(&self.alloc_wrappers),
            None,
        ) else {
            return false;
        };
        let info = self.raw_bridge_bindings.get(&lhs_hir_id).or_else(|| {
            self.alloc_wrappers
                .contains_key(&lhs_hir_id.owner.def_id)
                .then_some(&current_info)
        });
        let Some(info) = info else {
            return false;
        };
        if &current_info != info {
            return false;
        }
        *rhs = self.raw_bridge_expr(lhs_inner_ty, m, info);
        true
    }

    fn raw_bridge_expr(&self, lhs_inner_ty: ty::Ty<'tcx>, m: bool, info: &RawBridgeInfo) -> Expr {
        let ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let default_expr = self.default_value_expr(lhs_inner_ty);
        let default_expr_str = pprust::expr_to_string(&default_expr);
        match info {
            RawBridgeInfo::Scalar => utils::expr!(
                "Box::into_raw(Box::new({})) as *{} {}",
                default_expr_str,
                if m { "mut" } else { "const" },
                ty,
            ),
            RawBridgeInfo::Array { len_expr } => {
                let ptr_expr = if m {
                    format!(
                        "Box::leak(std::iter::repeat_with(|| {{ {default_expr_str} }}).take(({len_expr}) as usize).collect::<Vec<{ty}>>().into_boxed_slice()).as_mut_ptr()"
                    )
                } else {
                    format!(
                        "Box::leak(std::iter::repeat_with(|| {{ {default_expr_str} }}).take(({len_expr}) as usize).collect::<Vec<{ty}>>().into_boxed_slice()).as_ptr()"
                    )
                };
                utils::expr!("{ptr_expr}")
            }
        }
    }

    fn rewrite_direct_free_call(
        &self,
        hir_expr: &'tcx hir::Expr<'tcx>,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        let Some((hir_id, _harg)) =
            hir_free_like_arg_local_id(self.tcx, hir_expr, &self.free_like_wrappers)
        else {
            return None;
        };
        if hir_call_matches_foreign_name(self.tcx, hir_expr, "free")
            && matches!(
                self.effective_ptr_kind(hir_id),
                Some(PtrKind::OptBox | PtrKind::OptBoxedSlice)
            )
        {
            let local_name = self.tcx.hir_name(hir_id).to_string();
            return Some(utils::expr!("drop(({local_name}).take())"));
        }
        let Some(info) = self.raw_bridge_bindings.get(&hir_id) else {
            return None;
        };
        let [arg] = args else { return None };
        let arg_ty = self.tcx.typeck(hir_expr.hir_id.owner).node_type(hir_id);
        let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(arg_ty) else {
            return None;
        };
        let arg_str = pprust::expr_to_string(arg);
        let inner_ty_str = mir_ty_to_string(inner_ty, self.tcx);
        Some(match info {
            RawBridgeInfo::Scalar => utils::expr!(
                "if !({0}).is_null() {{ drop(unsafe {{ Box::from_raw(({0}) as *mut {1}) }}); }}",
                arg_str,
                inner_ty_str,
            ),
            RawBridgeInfo::Array { len_expr } => utils::expr!(
                "if !({0}).is_null() {{ drop(unsafe {{ Box::from_raw(std::ptr::slice_from_raw_parts_mut(({0}) as *mut {1}, ({2}) as usize)) }}); }}",
                arg_str,
                inner_ty_str,
                len_expr,
            ),
        })
    }

    fn hir_id_of_path(&self, id: NodeId) -> Option<HirId> {
        let hir_rhs = self.ast_to_hir.get_expr(id, self.tcx)?;
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_rhs.kind else { return None };
        let Res::Local(hir_id) = path.res else { return None };
        Some(hir_id)
    }

    fn effective_ptr_kind(&self, hir_id: HirId) -> Option<PtrKind> {
        let kind = self.ptr_kinds.get(&hir_id).copied()?;
        if self.forced_raw_bindings.contains(&hir_id) {
            match kind {
                PtrKind::Raw(_) => Some(kind),
                other => Some(PtrKind::Raw(other.is_mut())),
            }
        } else {
            Some(kind)
        }
    }

    fn forced_local_callee_output_kind(&self, hir_expr: &hir::Expr<'tcx>) -> Option<PtrKind> {
        let def_id = local_called_fn_def_id(self.tcx, hir_expr)?;
        effective_callee_output_kind(self.tcx, &self.sig_decs, &self.ptr_kinds, def_id)
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

        if self.forced_local_callee_output_kind(hir_expr) == Some(target_kind) {
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
                    && !self.transform.rhs_supports_box_target(
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
                PtrCtx::Deref(m) => return PtrKind::Raw(m),
            }
        }

        if let PtrCtx::Rhs(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) = ctx {
            let lhs_ty = self
                .tcx
                .typeck(hir_ptr.hir_id.owner)
                .expr_ty_adjusted(hir_ptr);
            let lhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(lhs_ty, self.tcx)
                .unwrap_or_else(|| panic!("{} {}", lhs_ty, pprust::expr_to_string(ptr)));
            if let Some(kind) = self.try_materialize_box_allocator_root(
                ptr,
                &allocator_root_expr,
                Some(hir_e),
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
                    *ptr =
                        self.opt_ref_from_raw(e, m, rhs_mut.is_mut(), lhs_inner_ty, rhs_inner_ty);
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
                    *ptr = self.opt_ref_from_raw(
                        &raw_expr,
                        m,
                        pe.as_mut_ptr,
                        lhs_inner_ty,
                        rhs_inner_ty,
                    );
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = self.cursor_from_raw(
                        &raw_expr,
                        m,
                        pe.as_mut_ptr,
                        lhs_inner_ty,
                        rhs_inner_ty,
                    );
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = self.slice_from_raw(
                        &raw_expr,
                        m,
                        pe.as_mut_ptr,
                        lhs_inner_ty,
                        rhs_inner_ty,
                    );
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
                    *ptr =
                        self.opt_ref_from_opt_box(pe.base, m, lhs_inner_ty, rhs_inner_ty, def_id);
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
                        *ptr = self.opt_boxed_slice_from_opt_boxed_slice(
                            pe.base,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
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
                    *ptr = self.cursor_from_slice_or_cursor(
                        &base,
                        &pe,
                        m,
                        lhs_inner_ty,
                        source_inner_ty,
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
                    *ptr = self.raw_from_slice_or_cursor(
                        &base,
                        m,
                        true,
                        lhs_inner_ty,
                        source_inner_ty,
                    );
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
                        self.opt_boxed_slice_from_opt_boxed_slice(
                            pe.base,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        )
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
            return self.sig_decs.data.get(&def_id).and_then(|sd| sd.output_dec);
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
            ty::TyKind::Array(elem, _) => {
                let elem_expr = self.default_value_expr(*elem);
                utils::expr!(
                    "std::array::from_fn(|_| {{ {} }})",
                    pprust::expr_to_string(&elem_expr)
                )
            }
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
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_union() => {
                let ty_name = mir_ty_to_string(ty, self.tcx);
                utils::expr!(
                    "unsafe {{ std::mem::MaybeUninit::<{ty_name}>::zeroed().assume_init() }}"
                )
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
        hir_expr: Option<&hir::Expr<'tcx>>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> Option<PtrKind> {
        let alloc_root = self.allocator_root(expr)?;
        let ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let default_expr = self.default_value_expr(lhs_inner_ty);
        let default_expr_str = pprust::expr_to_string(&default_expr);
        match (target_kind, alloc_root) {
            (PtrKind::OptBox, _)
                if hir_expr.is_some_and(|hir_expr| {
                    hir_supports_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_expr)
                }) || expr_supports_scalar_opt_box_allocator_root(
                    self.tcx,
                    expr,
                    lhs_inner_ty,
                ) =>
            {
                *ptr = utils::expr!("Some(Box::new({default_expr_str}))");
                Some(PtrKind::OptBox)
            }
            (PtrKind::OptBoxedSlice, AllocatorRoot::Calloc { count }) => {
                *ptr = utils::expr!(
                    "Some(std::iter::repeat_with(|| {0}).take(({1}) as usize).collect::<Vec<{2}>>().into_boxed_slice())",
                    default_expr_str,
                    pprust::expr_to_string(count),
                    ty,
                );
                Some(PtrKind::OptBoxedSlice)
            }
            (PtrKind::OptBoxedSlice, AllocatorRoot::Malloc { bytes }) => {
                *ptr = utils::expr!(
                    "Some(std::iter::repeat_with(|| {0}).take((({1}) / std::mem::size_of::<{2}>()) as usize).collect::<Vec<{2}>>().into_boxed_slice())",
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
                "unsafe {{ ({}){}.as_{}() }}",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "ref" },
            )
        } else {
            utils::expr!(
                "unsafe {{ (({}){} as *{} {}).as_{}() }}",
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
        let is_rewritten_slice_like_local =
            matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_)))
                && matches!(
                    self.ptr_source_kind(pe),
                    Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_) | PtrKind::OptBoxedSlice)
                )
                && pe.projs.is_empty();
        let get_reference = |use_ref| {
            if use_ref {
                if m { "&mut " } else { "&" }
            } else {
                ""
            }
        };
        if !need_cast {
            let reference = get_reference(
                pe.base_kind != PtrExprBaseKind::Alloca && !is_rewritten_slice_like_local,
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
        pe: &PtrExpr<'_, 'tcx>,
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
        let is_rewritten_slice_like_local =
            matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_)))
                && matches!(
                    self.ptr_source_kind(pe),
                    Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_) | PtrKind::OptBoxedSlice)
                )
                && pe.projs.is_empty();
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
            let reference = get_reference(
                pe.base_kind != PtrExprBaseKind::Alloca && !is_rewritten_slice_like_local,
            );
            if pe.projs.len() == 1
                && let PtrExprProj::Offset(offset) = pe.projs[0]
            {
                // if there are only offsets, we can use the original slice and let the cursor handle the offsets
                let cursor_base = if matches!(self.ptr_source_kind(pe), Some(PtrKind::OptBoxedSlice))
                {
                    self.opt_boxed_slice_view_expr(pe.base, m)
                } else {
                    pe.base.clone()
                };
                utils::expr!(
                    "{}::with_pos({}{}, ({}) as usize)",
                    cursor_ty,
                    reference,
                    pprust::expr_to_string(&cursor_base),
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
                pe.base_kind != PtrExprBaseKind::Alloca && !is_rewritten_slice_like_local,
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

    fn projected_base_mutability(&self, pe: &PtrExpr<'_, 'tcx>, fallback: bool) -> bool {
        match self.behind_subscripts(pe.hir_base) {
            PathOrDeref::Deref(hir_id) => self
                .effective_ptr_kind(hir_id)
                .or_else(|| self.ptr_kinds.get(&hir_id).copied())
                .map_or(fallback, |kind| kind.is_mut()),
            PathOrDeref::Path | PathOrDeref::Other => fallback,
        }
    }

    fn is_base_not_a_raw_ptr(&self, pe: &PtrExpr<'_, 'tcx>) -> bool {
        match pe.base_kind {
            PtrExprBaseKind::Path(_) | PtrExprBaseKind::Alloca | PtrExprBaseKind::Array => true,
            PtrExprBaseKind::Other => match self.behind_subscripts(pe.hir_base) {
                PathOrDeref::Path => true,
                PathOrDeref::Deref(hir_id) => {
                    matches!(
                        self.effective_ptr_kind(hir_id)
                            .unwrap_or(self.ptr_kinds[&hir_id]),
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
                ty::TyKind::Array(..) => self.projected_base_mutability(pe, m),
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
                        let base_str = pprust::expr_to_string(&e);
                        if is_array {
                            e = utils::expr!(
                                "(&{}({}))[({}) as usize..]",
                                if current_mut { "mut " } else { "" },
                                base_str,
                                pprust::expr_to_string(offset),
                            );
                            is_plain_slice = true;
                        } else {
                            e = utils::expr!(
                                "({})[({}) as usize..]",
                                base_str,
                                pprust::expr_to_string(offset),
                            );
                        }
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

fn size_of_type_name_candidates(ty_name: &str) -> Vec<String> {
    let mut candidates = vec![ty_name.to_string()];
    if let Some(stripped) = ty_name.strip_prefix("crate::") {
        candidates.push(stripped.to_string());
    }
    if let Some(last) = ty_name.rsplit("::").next() {
        candidates.push(last.to_string());
    }
    candidates.sort();
    candidates.dedup();
    candidates
}

fn ast_is_exact_size_of_expr(tcx: TyCtxt<'_>, expr: &Expr, ty_name: &str) -> bool {
    let Some(snippet) = expr_snippet(tcx, unwrap_cast_and_paren(expr)) else {
        return false;
    };
    size_of_type_name_candidates(ty_name)
        .into_iter()
        .flat_map(|candidate_ty| {
            [
                format!("::core::mem::size_of::<{candidate_ty}>()"),
                format!("core::mem::size_of::<{candidate_ty}>()"),
                format!("::std::mem::size_of::<{candidate_ty}>()"),
                format!("std::mem::size_of::<{candidate_ty}>()"),
            ]
        })
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

fn hir_unwrap_casts<'a, 'tcx>(mut expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
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

fn hir_size_of_call_matches_expected<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &hir::Expr<'_>,
    expected_ty: ty::Ty<'tcx>,
) -> bool {
    let hir::ExprKind::Call(callee, args) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind else {
        return false;
    };
    let Some(seg) = path.segments.last() else {
        return false;
    };
    if seg.ident.name != Symbol::intern("size_of") {
        return false;
    }
    let Some(args) = seg.args else {
        return false;
    };
    let [hir::GenericArg::Type(hir_ty)] = &args.args[..] else {
        return false;
    };
    let matched_ty = tcx.typeck(hir_ty.hir_id.owner).node_type(hir_ty.hir_id);
    match expected_ty.kind() {
        ty::TyKind::Bool => matches!(matched_ty.kind(), ty::TyKind::Bool),
        ty::TyKind::Char => matches!(matched_ty.kind(), ty::TyKind::Char),
        ty::TyKind::Int(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Int(found) if found == expected)
        }
        ty::TyKind::Uint(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Uint(found) if found == expected)
        }
        ty::TyKind::Float(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Float(found) if found == expected)
        }
        ty::TyKind::Adt(expected, _) => {
            matches!(matched_ty.kind(), ty::TyKind::Adt(found, _) if found.did() == expected.did())
        }
        ty::TyKind::Foreign(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Foreign(found) if found == expected)
        }
        _ => matched_ty == expected_ty,
    }
}

fn hir_is_exact_size_of_expr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>, ty_name: &str) -> bool {
    let Some(snippet) = hir_expr_snippet(tcx, hir_unwrap_casts(expr)) else {
        return false;
    };
    size_of_type_name_candidates(ty_name)
        .into_iter()
        .flat_map(|candidate_ty| {
            [
                format!("::core::mem::size_of::<{candidate_ty}>()"),
                format!("core::mem::size_of::<{candidate_ty}>()"),
                format!("::std::mem::size_of::<{candidate_ty}>()"),
                format!("std::mem::size_of::<{candidate_ty}>()"),
            ]
        })
        .map(|candidate| normalize_expr_snippet(&candidate))
        .any(|candidate| snippet == candidate)
}

fn hir_is_exact_c_char_size_of_expr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    let Some(snippet) = hir_expr_snippet(tcx, hir_unwrap_casts(expr)) else {
        return false;
    };
    [
        "::core::mem::size_of::<core::ffi::c_char>()",
        "core::mem::size_of::<core::ffi::c_char>()",
        "::std::mem::size_of::<core::ffi::c_char>()",
        "std::mem::size_of::<core::ffi::c_char>()",
        "::core::mem::size_of::<std::ffi::c_char>()",
        "core::mem::size_of::<std::ffi::c_char>()",
        "::std::mem::size_of::<std::ffi::c_char>()",
        "std::mem::size_of::<std::ffi::c_char>()",
    ]
    .into_iter()
    .map(normalize_expr_snippet)
    .any(|candidate| snippet == candidate)
}

fn ty_is_byte_sized_raw_inner(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Int(ty::IntTy::I8) | ty::TyKind::Uint(ty::UintTy::U8)
    )
}

fn hir_is_casted_local(rhs: &hir::Expr<'_>, target: HirId) -> bool {
    match rhs.kind {
        hir::ExprKind::Cast(inner, _) | hir::ExprKind::DropTemps(inner) => {
            hir_unwrapped_local_id(inner) == Some(target) || hir_is_casted_local(inner, target)
        }
        _ => false,
    }
}

fn hir_is_byte_view_self_update(target: HirId, rhs: &hir::Expr<'_>) -> bool {
    let rhs = hir_unwrap_casts(rhs);
    match rhs.kind {
        hir::ExprKind::MethodCall(seg, receiver, args, _)
            if hir_unwrapped_local_id(receiver) == Some(target)
                && args.len() == 1
                && matches!(
                    seg.ident.name.as_str(),
                    "offset" | "add" | "wrapping_offset"
                ) =>
        {
            true
        }
        _ => false,
    }
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
    rhs: &hir::Expr<'tcx>,
) -> bool {
    let expected_ty_name = mir_ty_to_string(lhs_inner_ty, tcx);
    let hir::ExprKind::Call(_, args) = hir_unwrap_casts(rhs).kind else {
        return false;
    };
    let Some(name) = hir_call_name(rhs) else {
        return false;
    };
    match (name, args) {
        (name, [bytes]) if name == Symbol::intern("malloc") => {
            hir_size_of_call_matches_expected(tcx, bytes, lhs_inner_ty)
                || hir_is_exact_size_of_expr(tcx, bytes, &expected_ty_name)
        }
        (name, [count, elem_size]) if name == Symbol::intern("calloc") => {
            hir_is_literal_one(tcx, count)
                && (hir_size_of_call_matches_expected(tcx, elem_size, lhs_inner_ty)
                    || hir_is_exact_size_of_expr(tcx, elem_size, &expected_ty_name))
        }
        (name, [ptr, bytes])
            if name == Symbol::intern("realloc") && hir_is_null_like_ptr_arg(tcx, ptr) =>
        {
            hir_size_of_call_matches_expected(tcx, bytes, lhs_inner_ty)
                || hir_is_exact_size_of_expr(tcx, bytes, &expected_ty_name)
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
        (name, [ptr, _]) if name == Symbol::intern("realloc") => hir_is_null_like_ptr_arg(tcx, ptr),
        _ => false,
    }
}

fn hir_is_unsupported_scalar_box_allocator_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &hir::Expr<'tcx>,
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
        expr: &'tcx hir::Expr<'tcx>,
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
        fn_has_unsupported_box_assignment(
            tcx,
            sig_decs,
            ptr_kinds,
            hir_id,
            target_kind,
            lhs_inner_ty,
        )
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
    tcx: TyCtxt<'_>,
    ptr_kinds: &mut FxHashMap<HirId, PtrKind>,
    forced_raw_bindings: &FxHashSet<HirId>,
) {
    for (hir_id, kind) in ptr_kinds.iter_mut() {
        if forced_raw_bindings.contains(hir_id) {
            let ty = tcx.typeck(hir_id.owner).node_type(*hir_id);
            let raw_mut = unwrap_ptr_from_mir_ty(ty)
                .map(|(_, m)| m.is_mut())
                .unwrap_or_else(|| kind.is_mut());
            *kind = PtrKind::Raw(raw_mut);
        }
    }
}

fn downgrade_unsupported_box_inputs(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for (did, sig_dec) in &mut sig_decs.data {
        let hir::Node::Item(item) = tcx.hir_node_by_def_id(*did) else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        for (idx, param) in body.params.iter().enumerate() {
            let Some(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) =
                sig_dec.input_decs.get(idx).copied().flatten()
            else {
                continue;
            };
            let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                continue;
            };
            if local_raw_param_summaries.get(&(*did, idx))
                != Some(&LocalRawParamSummary::BorrowOnly)
            {
                sig_dec.input_decs[idx] = Some(PtrKind::Raw(kind.is_mut()));
                bindings.insert(hir_id);
                changed = true;
            }
        }
    }
    (changed, bindings)
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
        ) || fn_output_has_nonowning_local_consumers(tcx, ptr_kinds, *did, output_kind)
        {
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

fn fn_output_has_nonowning_local_consumers(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    callee_did: LocalDefId,
    output_kind: PtrKind,
) -> bool {
    struct NonOwningCallConsumerVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        callee_did: LocalDefId,
        output_kind: PtrKind,
        found: bool,
    }

    impl<'tcx> NonOwningCallConsumerVisitor<'_, 'tcx> {
        fn local_target_kind(&self, hir_id: HirId) -> Option<PtrKind> {
            self.ptr_kinds.get(&hir_id).copied().or_else(|| {
                let ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                unwrap_ptr_from_mir_ty(ty).map(|(_, m)| PtrKind::Raw(m.is_mut()))
            })
        }

        fn expr_target_kind(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<PtrKind> {
            let expr = hir_unwrap_casts(expr);
            if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = expr.kind
                && let Res::Local(hir_id) = path.res
            {
                return self.local_target_kind(hir_id);
            }
            let ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(expr);
            unwrap_ptr_from_mir_ty(ty).map(|(_, m)| PtrKind::Raw(m.is_mut()))
        }

        fn call_targets_callee(&self, expr: &'tcx hir::Expr<'tcx>) -> bool {
            let expr = hir_unwrap_casts(expr);
            let hir::ExprKind::Call(func, _) = expr.kind else {
                return false;
            };
            let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(func).kind
            else {
                return false;
            };
            let Res::Def(_, def_id) = path.res else {
                return false;
            };
            def_id.as_local() == Some(self.callee_did)
        }

        fn target_kind_is_nonowning(&self, kind: Option<PtrKind>) -> bool {
            kind != Some(self.output_kind)
        }
    }

    impl<'tcx> Visitor<'tcx> for NonOwningCallConsumerVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && self.call_targets_callee(init)
                && self.target_kind_is_nonowning(self.local_target_kind(hir_id))
            {
                self.found = true;
                return;
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && self.call_targets_callee(rhs)
                && self.target_kind_is_nonowning(self.expr_target_kind(lhs))
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

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
        let mut visitor = NonOwningCallConsumerVisitor {
            tcx,
            ptr_kinds,
            callee_did,
            output_kind,
            found: false,
        };
        visitor.visit_body(body);
        if visitor.found {
            return true;
        }
    }

    false
}

fn local_called_fn_def_id(tcx: TyCtxt<'_>, hir_expr: &hir::Expr<'_>) -> Option<LocalDefId> {
    let hir_expr = hir_unwrap_casts(hir_expr);
    let hir::ExprKind::Call(func, _) = hir_expr.kind else {
        return None;
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(func).kind else {
        return None;
    };
    let Res::Def(_, def_id) = path.res else {
        return None;
    };
    let def_id = def_id.as_local()?;
    local_def_id_has_fn_body(tcx, def_id).then_some(def_id)
}

fn effective_callee_output_kind(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    def_id: LocalDefId,
) -> Option<PtrKind> {
    let sig_dec = sig_decs.data.get(&def_id)?;
    if let Some(output_dec) = sig_dec.output_dec {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        let Some((inner_ty, _)) =
            unwrap_ptr_from_mir_ty(body.local_decls[rustc_middle::mir::Local::from_u32(0)].ty)
        else {
            return Some(output_dec);
        };
        if matches!(output_dec, PtrKind::OptBox | PtrKind::OptBoxedSlice)
            && (fn_tail_returns_unsupported_box_binding(
                tcx, sig_decs, ptr_kinds, def_id, output_dec, inner_ty,
            ) || fn_output_has_nonowning_local_consumers(tcx, ptr_kinds, def_id, output_dec))
        {
            return Some(PtrKind::Raw(true));
        }
        return Some(output_dec);
    }
    let sig = tcx.fn_sig(def_id).skip_binder().skip_binder();
    match sig.output().kind() {
        ty::TyKind::RawPtr(_, m) => Some(PtrKind::Raw(m.is_mut())),
        _ => None,
    }
}

fn hir_callee_output_kind(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    hir_expr: &hir::Expr<'_>,
) -> Option<PtrKind> {
    let def_id = local_called_fn_def_id(tcx, hir_expr)?;
    effective_callee_output_kind(tcx, sig_decs, ptr_kinds, def_id)
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
    let expr = hir_unwrap_casts(expr);
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

fn hir_called_local_fn(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> Option<LocalDefId> {
    local_called_fn_def_id(tcx, expr)
}

fn hir_is_borrow_only_foreign_buffer_arg(
    tcx: TyCtxt<'_>,
    expr: &hir::Expr<'_>,
    arg_index: usize,
) -> bool {
    if hir_called_local_fn(tcx, expr).is_some() {
        return false;
    }
    let Some(name) = hir_call_name(expr) else {
        return false;
    };
    match name.as_str() {
        "memcpy" | "memmove" => arg_index < 2,
        "memset" => arg_index == 0,
        "strncpy" => arg_index < 2,
        _ => false,
    }
}

fn hir_free_like_arg_local_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> Option<(HirId, &'tcx hir::Expr<'tcx>)> {
    let is_direct_free = hir_call_matches_foreign_name(tcx, expr, "free");
    let is_wrapper_free =
        hir_called_local_fn(tcx, expr).is_some_and(|def_id| free_like_wrappers.contains(&def_id));
    if !is_direct_free && !is_wrapper_free {
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

fn hir_expr_verbatim_snippet(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> Option<String> {
    tcx.sess.source_map().span_to_snippet(expr.span).ok()
}

struct WrapperScalarDagContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    param_positions: &'a FxHashMap<HirId, usize>,
    scalar_defs: &'a FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
}

fn ty_is_wrapper_scalar_dag_ty(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Bool
            | ty::TyKind::Char
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Float(_)
    )
}

fn hir_expr_uses_any_local(expr: &hir::Expr<'_>) -> bool {
    struct LocalUseVisitor {
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for LocalUseVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if hir_unwrapped_local_id(expr).is_some() {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = LocalUseVisitor { found: false };
    visitor.visit_expr(expr);
    visitor.found
}

fn hir_is_const_like_scalar_path(expr: &hir::Expr<'_>) -> bool {
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    matches!(
        path.res,
        Res::Def(
            rustc_hir::def::DefKind::Const
                | rustc_hir::def::DefKind::AssocConst
                | rustc_hir::def::DefKind::ConstParam,
            _
        )
    )
}

fn hir_is_any_size_of_expr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    hir_expr_snippet(tcx, hir_unwrap_casts(expr)).is_some_and(|snippet| {
        snippet.contains("::core::mem::size_of::<")
            || snippet.contains("core::mem::size_of::<")
            || snippet.contains("::std::mem::size_of::<")
            || snippet.contains("std::mem::size_of::<")
    })
}

fn hir_is_allowed_size_query_arg(expr: &hir::Expr<'_>) -> bool {
    let expr = hir_unwrap_casts(expr);
    matches!(expr.kind, hir::ExprKind::Path(..) | hir::ExprKind::Lit(..))
}

fn hir_is_allowed_size_query_call<'tcx>(tcx: TyCtxt<'tcx>, expr: &'tcx hir::Expr<'tcx>) -> bool {
    let hir::ExprKind::Call(_, args) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    let Some(name) = hir_call_name(expr) else {
        return false;
    };
    matches!(name.as_str(), "strlen" | "strnlen" | "strcspn")
        && args.iter().all(|arg| hir_is_allowed_size_query_arg(arg))
        && tcx.typeck(expr.hir_id.owner).expr_ty(expr).is_integral()
}

fn resolve_wrapper_param_index<'tcx>(
    ctx: &WrapperScalarDagContext<'_, 'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    visiting: &mut FxHashSet<HirId>,
) -> Option<usize> {
    let expr = hir_unwrap_casts(expr);
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = expr.kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    if let Some(index) = ctx.param_positions.get(&hir_id) {
        return Some(*index);
    }
    let rhs = ctx.scalar_defs.get(&hir_id).copied()?;
    if !visiting.insert(hir_id) {
        return None;
    }
    let resolved = resolve_wrapper_param_index(ctx, rhs, visiting);
    visiting.remove(&hir_id);
    resolved
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum WrapperScalarDagStatus {
    Allowed,
    Rejected,
    Inconclusive,
}

fn combine_wrapper_scalar_dag_status(
    left: WrapperScalarDagStatus,
    right: WrapperScalarDagStatus,
) -> WrapperScalarDagStatus {
    match (left, right) {
        (WrapperScalarDagStatus::Rejected, _) | (_, WrapperScalarDagStatus::Rejected) => {
            WrapperScalarDagStatus::Rejected
        }
        (WrapperScalarDagStatus::Allowed, WrapperScalarDagStatus::Allowed) => {
            WrapperScalarDagStatus::Allowed
        }
        _ => WrapperScalarDagStatus::Inconclusive,
    }
}

fn hir_wrapper_scalar_dag_status<'tcx>(
    ctx: &WrapperScalarDagContext<'_, 'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    visiting: &mut FxHashSet<HirId>,
    depth: usize,
) -> WrapperScalarDagStatus {
    if depth > 16 {
        return WrapperScalarDagStatus::Inconclusive;
    }
    let expr = hir_unwrap_casts(expr);
    match expr.kind {
        hir::ExprKind::Lit(..) => WrapperScalarDagStatus::Allowed,
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(hir_id) => {
                if ctx.param_positions.contains_key(&hir_id) {
                    return WrapperScalarDagStatus::Allowed;
                }
                let Some(rhs) = ctx.scalar_defs.get(&hir_id).copied() else {
                    return WrapperScalarDagStatus::Inconclusive;
                };
                if !visiting.insert(hir_id) {
                    return WrapperScalarDagStatus::Inconclusive;
                }
                let admissible = hir_wrapper_scalar_dag_status(ctx, rhs, visiting, depth + 1);
                visiting.remove(&hir_id);
                admissible
            }
            _ => {
                if hir_is_const_like_scalar_path(expr) {
                    WrapperScalarDagStatus::Allowed
                } else {
                    WrapperScalarDagStatus::Rejected
                }
            }
        },
        hir::ExprKind::Unary(hir::UnOp::Neg, inner) => {
            hir_wrapper_scalar_dag_status(ctx, inner, visiting, depth + 1)
        }
        hir::ExprKind::Binary(op, lhs, rhs) => {
            if !matches!(
                op.node,
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Rem
            ) {
                return WrapperScalarDagStatus::Rejected;
            }
            combine_wrapper_scalar_dag_status(
                hir_wrapper_scalar_dag_status(ctx, lhs, visiting, depth + 1),
                hir_wrapper_scalar_dag_status(ctx, rhs, visiting, depth + 1),
            )
        }
        hir::ExprKind::MethodCall(seg, receiver, args, _) => {
            if !matches!(
                seg.ident.name.as_str(),
                "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "wrapping_div" | "wrapping_rem"
            ) {
                return WrapperScalarDagStatus::Rejected;
            }
            let mut status = hir_wrapper_scalar_dag_status(ctx, receiver, visiting, depth + 1);
            for arg in args {
                status = combine_wrapper_scalar_dag_status(
                    status,
                    hir_wrapper_scalar_dag_status(ctx, arg, visiting, depth + 1),
                );
            }
            status
        }
        _ => {
            if hir_is_any_size_of_expr(ctx.tcx, expr)
                || hir_is_allowed_size_query_call(ctx.tcx, expr)
            {
                WrapperScalarDagStatus::Allowed
            } else {
                WrapperScalarDagStatus::Rejected
            }
        }
    }
}

fn ty_supports_raw_bridge_default_expr<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::TyKind::Bool
        | ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_)
        | ty::TyKind::Float(_) => true,
        ty::TyKind::RawPtr(..) => true,
        ty::TyKind::Array(elem, _) => ty_supports_raw_bridge_default_expr(tcx, *elem),
        ty::TyKind::Tuple(elems) => elems
            .iter()
            .all(|elem| ty_supports_raw_bridge_default_expr(tcx, elem)),
        ty::TyKind::Adt(adt_def, args) if adt_def.did().is_local() && adt_def.is_struct() => {
            adt_def
                .all_fields()
                .all(|field| ty_supports_raw_bridge_default_expr(tcx, field.ty(tcx, args)))
        }
        _ => false,
    }
}

fn raw_array_len_expr_from_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    bytes: &hir::Expr<'_>,
) -> Option<String> {
    let bytes = hir_expr_verbatim_snippet(tcx, hir_unwrap_casts(bytes))?;
    let ty = mir_ty_to_string(lhs_inner_ty, tcx);
    Some(format!(
        "((({bytes}) as usize) / std::mem::size_of::<{ty}>())"
    ))
}

fn raw_bridge_info_from_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    name: Symbol,
    args: &[&'tcx hir::Expr<'tcx>],
    scalar_ctx: Option<&WrapperScalarDagContext<'_, 'tcx>>,
) -> Option<RawBridgeInfo> {
    let scalar_arg_rejected = |expr: &'tcx hir::Expr<'tcx>| {
        scalar_ctx.is_some_and(|ctx| {
            hir_expr_uses_any_local(expr)
                && hir_wrapper_scalar_dag_status(ctx, expr, &mut FxHashSet::default(), 0)
                    == WrapperScalarDagStatus::Rejected
        })
    };
    let byte_sized_elem = matches!(
        lhs_inner_ty.kind(),
        ty::TyKind::Int(ty::IntTy::I8) | ty::TyKind::Uint(ty::UintTy::U8)
    );
    if !ty_supports_raw_bridge_default_expr(tcx, lhs_inner_ty) {
        return None;
    }
    let ty_name = mir_ty_to_string(lhs_inner_ty, tcx);
    match (name, args) {
        (name, [bytes]) if name == Symbol::intern("malloc") => {
            if hir_is_exact_size_of_expr(tcx, bytes, &ty_name) {
                Some(RawBridgeInfo::Scalar)
            } else if scalar_arg_rejected(bytes) {
                None
            } else {
                raw_array_len_expr_from_bytes(tcx, lhs_inner_ty, bytes)
                    .map(|len_expr| RawBridgeInfo::Array { len_expr })
            }
        }
        (name, [count, elem_size]) if name == Symbol::intern("calloc") => {
            if hir_is_literal_one(tcx, count) && hir_is_exact_size_of_expr(tcx, elem_size, &ty_name)
            {
                Some(RawBridgeInfo::Scalar)
            } else if scalar_arg_rejected(count) || scalar_arg_rejected(elem_size) {
                None
            } else if hir_is_exact_size_of_expr(tcx, count, &ty_name)
                || (byte_sized_elem && hir_is_exact_c_char_size_of_expr(tcx, count))
            {
                if byte_sized_elem {
                    Some(RawBridgeInfo::Array {
                        len_expr: hir_expr_verbatim_snippet(tcx, hir_unwrap_casts(elem_size))?,
                    })
                } else {
                    None
                }
            } else {
                Some(RawBridgeInfo::Array {
                    len_expr: hir_expr_verbatim_snippet(tcx, hir_unwrap_casts(count))?,
                })
            }
        }
        (name, [ptr, bytes])
            if name == Symbol::intern("realloc") && hir_is_null_like_ptr_arg(tcx, ptr) =>
        {
            if hir_is_exact_size_of_expr(tcx, bytes, &ty_name) {
                Some(RawBridgeInfo::Scalar)
            } else if scalar_arg_rejected(bytes) {
                None
            } else {
                raw_array_len_expr_from_bytes(tcx, lhs_inner_ty, bytes)
                    .map(|len_expr| RawBridgeInfo::Array { len_expr })
            }
        }
        _ => None,
    }
}

fn hir_raw_bridge_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &'tcx hir::Expr<'tcx>,
    alloc_wrappers: Option<&FxHashMap<LocalDefId, AllocWrapperInfo>>,
    scalar_ctx: Option<&WrapperScalarDagContext<'_, 'tcx>>,
) -> Option<RawBridgeInfo> {
    let rhs = hir_unwrap_casts(rhs);
    if let hir::ExprKind::Call(_, args) = rhs.kind
        && let Some(name) = hir_call_name(rhs)
    {
        let arg_refs = args.iter().collect::<Vec<_>>();
        if let Some(info) =
            raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &arg_refs, scalar_ctx)
        {
            return Some(info);
        }
    }

    let Some(alloc_wrappers) = alloc_wrappers else {
        return None;
    };
    let Some(def_id) = hir_called_local_fn(tcx, rhs) else {
        return None;
    };
    let wrapper = alloc_wrappers.get(&def_id)?;
    let hir::ExprKind::Call(_, args) = rhs.kind else {
        return None;
    };
    let arg = |idx: usize| args.get(idx);
    match *wrapper {
        AllocWrapperInfo::Fixed(ref info) => Some(info.clone()),
        AllocWrapperInfo::Bytes { bytes_param } => raw_bridge_info_from_call(
            tcx,
            lhs_inner_ty,
            Symbol::intern("malloc"),
            &[arg(bytes_param)?],
            None,
        ),
        AllocWrapperInfo::CountSize {
            count_param,
            elem_size_param,
        } => raw_bridge_info_from_call(
            tcx,
            lhs_inner_ty,
            Symbol::intern("calloc"),
            &[arg(count_param)?, arg(elem_size_param)?],
            None,
        ),
        AllocWrapperInfo::Realloc {
            ptr_param,
            bytes_param,
        } => raw_bridge_info_from_call(
            tcx,
            lhs_inner_ty,
            Symbol::intern("realloc"),
            &[arg(ptr_param)?, arg(bytes_param)?],
            None,
        ),
    }
}

fn raw_wrapper_info_from_rhs<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &'tcx hir::Expr<'tcx>,
    param_positions: &FxHashMap<HirId, usize>,
    scalar_defs: &FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
) -> Option<AllocWrapperInfo> {
    let rhs = hir_unwrap_casts(rhs);
    let hir::ExprKind::Call(_, args) = rhs.kind else {
        return None;
    };
    let Some(name) = hir_call_name(rhs) else {
        return None;
    };
    let scalar_ctx = WrapperScalarDagContext {
        tcx,
        param_positions,
        scalar_defs,
    };
    let param_index = |expr: &'tcx hir::Expr<'tcx>| {
        resolve_wrapper_param_index(&scalar_ctx, expr, &mut FxHashSet::default())
    };
    let mentions_only_params = |expr: &'tcx hir::Expr<'tcx>| {
        struct LocalUseVisitor {
            locals: Vec<HirId>,
        }
        impl<'tcx> Visitor<'tcx> for LocalUseVisitor {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let Some(hir_id) = hir_unwrapped_local_id(expr) {
                    self.locals.push(hir_id);
                }
                intravisit::walk_expr(self, expr);
            }
        }
        let mut visitor = LocalUseVisitor { locals: Vec::new() };
        visitor.visit_expr(expr);
        visitor
            .locals
            .into_iter()
            .all(|hir_id| param_positions.contains_key(&hir_id))
    };

    match (name, &args[..]) {
        (name, [bytes]) if name == Symbol::intern("malloc") => {
            if let Some(bytes_param) = param_index(bytes) {
                Some(AllocWrapperInfo::Bytes { bytes_param })
            } else if mentions_only_params(bytes) {
                raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &[bytes], None)
                    .map(AllocWrapperInfo::Fixed)
            } else {
                None
            }
        }
        (name, [count, elem_size]) if name == Symbol::intern("calloc") => {
            if let (Some(count_param), Some(elem_size_param)) =
                (param_index(count), param_index(elem_size))
            {
                Some(AllocWrapperInfo::CountSize {
                    count_param,
                    elem_size_param,
                })
            } else if mentions_only_params(count) && mentions_only_params(elem_size) {
                raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &[count, elem_size], None)
                    .map(AllocWrapperInfo::Fixed)
            } else {
                None
            }
        }
        (name, [ptr, bytes]) if name == Symbol::intern("realloc") => {
            if let (Some(ptr_param), Some(bytes_param)) = (param_index(ptr), param_index(bytes)) {
                Some(AllocWrapperInfo::Realloc {
                    ptr_param,
                    bytes_param,
                })
            } else if hir_is_null_like_ptr_arg(tcx, ptr) && param_index(bytes).is_some() {
                raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &[ptr, bytes], None)
                    .map(AllocWrapperInfo::Fixed)
            } else if mentions_only_params(ptr) && mentions_only_params(bytes) {
                raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &[ptr, bytes], None)
                    .map(AllocWrapperInfo::Fixed)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn collect_local_allocator_wrappers(tcx: TyCtxt<'_>) -> FxHashMap<LocalDefId, AllocWrapperInfo> {
    let mut wrappers = FxHashMap::default();
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
        let def_id = item.owner_id.def_id;
        let body = tcx.hir_body(body);
        let typeck = tcx.typeck(def_id);
        let param_positions = body
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                    return None;
                };
                Some((hir_id, idx))
            })
            .collect::<FxHashMap<_, _>>();
        #[derive(Default)]
        struct Candidate {
            info: Option<AllocWrapperInfo>,
            aliases: FxHashSet<HirId>,
            byte_view_aliases: FxHashSet<HirId>,
            returned: bool,
            disqualified: bool,
        }

        struct WrapperVisitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            param_positions: &'a FxHashMap<HirId, usize>,
            typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
            candidates: FxHashMap<HirId, Candidate>,
            root_of: FxHashMap<HirId, HirId>,
            scalar_defs: FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
        }

        impl<'a, 'tcx> WrapperVisitor<'a, 'tcx> {
            fn mark_root(&mut self, hir_id: HirId, info: AllocWrapperInfo) {
                let candidate = self.candidates.entry(hir_id).or_default();
                if let Some(existing) = &candidate.info {
                    if *existing != info {
                        candidate.disqualified = true;
                    }
                } else {
                    candidate.info = Some(info);
                }
                candidate.aliases.insert(hir_id);
                self.root_of.insert(hir_id, hir_id);
            }

            fn mark_alias(&mut self, alias: HirId, source: HirId) {
                let Some(root) = self.root_of.get(&source).copied() else {
                    return;
                };
                self.root_of.insert(alias, root);
                self.candidates
                    .entry(root)
                    .or_default()
                    .aliases
                    .insert(alias);
            }

            fn mark_byte_view_alias(&mut self, alias: HirId, source: HirId) {
                self.mark_alias(alias, source);
                self.candidates
                    .entry(self.root_of[&source])
                    .or_default()
                    .byte_view_aliases
                    .insert(alias);
            }

            fn mark_disqualified(&mut self, hir_id: HirId) {
                if let Some(root) = self.root_of.get(&hir_id).copied() {
                    self.candidates.entry(root).or_default().disqualified = true;
                }
            }

            fn mark_returned(&mut self, hir_id: HirId) {
                if let Some(root) = self.root_of.get(&hir_id).copied() {
                    if self
                        .candidates
                        .get(&root)
                        .is_some_and(|candidate| candidate.byte_view_aliases.contains(&hir_id))
                    {
                        self.candidates.entry(root).or_default().disqualified = true;
                        return;
                    }
                    self.candidates.entry(root).or_default().returned = true;
                }
            }

            fn record_scalar_local(&mut self, hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>) {
                if ty_is_wrapper_scalar_dag_ty(self.typeck.node_type(hir_id)) {
                    self.scalar_defs.insert(hir_id, rhs);
                }
            }
        }

        impl<'tcx> Visitor<'tcx> for WrapperVisitor<'_, 'tcx> {
            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    && let Some(init) = let_stmt.init
                {
                    let lhs_ty = self.typeck.node_type(hir_id);
                    if lhs_ty.is_raw_ptr()
                        && let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty)
                    {
                        if let Some(info) = raw_wrapper_info_from_rhs(
                            self.tcx,
                            lhs_inner_ty,
                            init,
                            self.param_positions,
                            &self.scalar_defs,
                        ) {
                            self.mark_root(hir_id, info);
                        } else if let Some(rhs_hir_id) = hir_unwrapped_local_id(init) {
                            let rhs_ty = self.typeck.node_type(rhs_hir_id);
                            let is_byte_view_alias = hir_is_casted_local(init, rhs_hir_id)
                                && ty_is_byte_sized_raw_inner(lhs_inner_ty)
                                && unwrap_ptr_from_mir_ty(rhs_ty).is_some_and(
                                    |(rhs_inner_ty, _)| ty_is_byte_sized_raw_inner(rhs_inner_ty),
                                )
                                && self
                                    .root_of
                                    .get(&rhs_hir_id)
                                    .and_then(|root| self.candidates.get(root))
                                    .and_then(|candidate| candidate.info.as_ref())
                                    .is_some_and(|info| {
                                        matches!(
                                            info,
                                            AllocWrapperInfo::Fixed(RawBridgeInfo::Array { .. })
                                        )
                                    });
                            if is_byte_view_alias {
                                self.mark_byte_view_alias(hir_id, rhs_hir_id);
                            } else {
                                self.mark_alias(hir_id, rhs_hir_id);
                            }
                        }
                    }
                    self.record_scalar_local(hir_id, init);
                }
                intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                match expr.kind {
                    hir::ExprKind::Assign(lhs, rhs, _) => {
                        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                            && let Res::Local(lhs_hir_id) = path.res
                        {
                            let lhs_ty = self.typeck.expr_ty(lhs);
                            if lhs_ty.is_raw_ptr()
                                && let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty)
                            {
                                if let Some(info) = raw_wrapper_info_from_rhs(
                                    self.tcx,
                                    lhs_inner_ty,
                                    rhs,
                                    self.param_positions,
                                    &self.scalar_defs,
                                ) {
                                    self.mark_root(lhs_hir_id, info);
                                } else if let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) {
                                    let rhs_ty = self.typeck.node_type(rhs_hir_id);
                                    let is_byte_view_alias = hir_is_casted_local(rhs, rhs_hir_id)
                                        && ty_is_byte_sized_raw_inner(lhs_inner_ty)
                                        && unwrap_ptr_from_mir_ty(rhs_ty).is_some_and(
                                            |(rhs_inner_ty, _)| {
                                                ty_is_byte_sized_raw_inner(rhs_inner_ty)
                                            },
                                        )
                                        && self
                                            .root_of
                                            .get(&rhs_hir_id)
                                            .and_then(|root| self.candidates.get(root))
                                            .and_then(|candidate| candidate.info.as_ref())
                                            .is_some_and(|info| {
                                                matches!(
                                                    info,
                                                    AllocWrapperInfo::Fixed(
                                                        RawBridgeInfo::Array { .. }
                                                    )
                                                )
                                            });
                                    if is_byte_view_alias {
                                        self.mark_byte_view_alias(lhs_hir_id, rhs_hir_id);
                                    } else {
                                        self.mark_alias(lhs_hir_id, rhs_hir_id);
                                    }
                                }
                            }
                            self.record_scalar_local(lhs_hir_id, rhs);
                        } else if let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) {
                            self.mark_disqualified(rhs_hir_id);
                        }
                    }
                    hir::ExprKind::Ret(Some(ret)) => {
                        if let Some(hir_id) = hir_unwrapped_local_id(ret) {
                            self.mark_returned(hir_id);
                        }
                    }
                    hir::ExprKind::Call(_, args) => {
                        let is_local_callee = hir_called_local_fn(self.tcx, expr).is_some();
                        for arg in args {
                            if let Some(hir_id) = hir_unwrapped_local_id(arg)
                                && is_local_callee
                            {
                                self.mark_disqualified(hir_id);
                            }
                        }
                    }
                    _ => {}
                }
                intravisit::walk_expr(self, expr);
            }

            fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
                intravisit::walk_body(self, body);
                let mut tail = body.value;
                while let hir::ExprKind::Block(block, _) = tail.kind {
                    let Some(expr) = block.expr else {
                        break;
                    };
                    tail = expr;
                }
                if let Some(hir_id) = hir_unwrapped_local_id(tail) {
                    self.mark_returned(hir_id);
                }
            }
        }

        let mut visitor = WrapperVisitor {
            tcx,
            param_positions: &param_positions,
            typeck,
            candidates: FxHashMap::default(),
            root_of: FxHashMap::default(),
            scalar_defs: FxHashMap::default(),
        };
        visitor.visit_body(body);

        let eligible = visitor
            .candidates
            .into_iter()
            .filter_map(|(_root, candidate)| {
                if candidate.disqualified || !candidate.returned {
                    return None;
                }
                candidate.info
            })
            .collect::<Vec<_>>();
        if eligible.len() == 1 {
            wrappers.insert(def_id, eligible.into_iter().next().unwrap());
        }
    }
    wrappers
}

fn collect_local_free_wrappers(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    fn wrapper_name_allows_free(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
        let name = tcx
            .item_name(def_id.to_def_id())
            .as_str()
            .to_ascii_lowercase();
        name.contains("free") || name.contains("dealloc")
    }

    struct FreeWrapperVisitor {
        target: HirId,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for FreeWrapperVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Call(_, args) = expr.kind
                && args.len() == 1
                && hir_unwrapped_local_id(&args[0]) == Some(self.target)
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut wrappers = FxHashSet::default();
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
        let def_id = item.owner_id.def_id;
        if !wrapper_name_allows_free(tcx, def_id) {
            continue;
        }
        let body = tcx.hir_body(body);
        let [param] = body.params else {
            continue;
        };
        let hir::PatKind::Binding(_, param_hir_id, _, _) = param.pat.kind else {
            continue;
        };
        if !tcx.typeck(def_id).node_type(param_hir_id).is_raw_ptr() {
            continue;
        }
        let mut visitor = FreeWrapperVisitor {
            target: param_hir_id,
            found: false,
        };
        visitor.visit_body(body);
        if visitor.found {
            wrappers.insert(def_id);
        }
    }
    wrappers
}

fn collect_locally_called_fns(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    struct LocalCallVisitor<'a> {
        tcx: TyCtxt<'a>,
        called: FxHashSet<LocalDefId>,
    }

    impl<'tcx> Visitor<'tcx> for LocalCallVisitor<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(def_id) = hir_called_local_fn(self.tcx, expr) {
                self.called.insert(def_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = LocalCallVisitor {
        tcx,
        called: FxHashSet::default(),
    };
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        visitor.visit_body(tcx.hir_body(body));
    }
    visitor.called
}

fn collect_local_raw_free_summaries(
    tcx: TyCtxt<'_>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> FxHashMap<(LocalDefId, usize), LocalRawParamSummary> {
    #[derive(Default)]
    struct ParamFacts {
        direct_free: bool,
        deps: FxHashSet<(LocalDefId, usize)>,
    }

    let crate_hir = tcx.hir_crate(());
    let mut raw_params_by_fn = FxHashMap::<LocalDefId, FxHashMap<HirId, usize>>::default();
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
        let def_id = item.owner_id.def_id;
        let body = tcx.hir_body(body);
        let typeck = tcx.typeck(def_id);
        let raw_params = body
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                    return None;
                };
                typeck
                    .node_type(hir_id)
                    .is_raw_ptr()
                    .then_some((hir_id, idx))
            })
            .collect::<FxHashMap<_, _>>();
        if !raw_params.is_empty() {
            raw_params_by_fn.insert(def_id, raw_params);
        }
    }

    struct RawFreeSummaryVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        raw_params_by_fn: &'a FxHashMap<LocalDefId, FxHashMap<HirId, usize>>,
        current_raw_params: &'a FxHashMap<HirId, usize>,
        facts: FxHashMap<usize, ParamFacts>,
    }

    impl<'tcx> RawFreeSummaryVisitor<'_, 'tcx> {
        fn param_index(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<usize> {
            let hir_id = hir_unwrapped_local_id(expr)?;
            self.current_raw_params.get(&hir_id).copied()
        }

        fn mark_free(&mut self, param_index: usize) {
            self.facts.entry(param_index).or_default().direct_free = true;
        }

        fn add_dep(&mut self, param_index: usize, dep: (LocalDefId, usize)) {
            self.facts.entry(param_index).or_default().deps.insert(dep);
        }
    }

    impl<'tcx> Visitor<'tcx> for RawFreeSummaryVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Call(_, args) = expr.kind {
                let free_arg = hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                    .map(|(hir_id, _)| hir_id);
                let local_callee = hir_called_local_fn(self.tcx, expr);
                for (arg_index, arg) in args.iter().enumerate() {
                    let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                        continue;
                    };
                    let Some(param_index) = self.current_raw_params.get(&hir_id).copied() else {
                        continue;
                    };
                    if Some(hir_id) == free_arg {
                        self.mark_free(param_index);
                        continue;
                    }
                    let Some(local_callee) = local_callee else {
                        continue;
                    };
                    let Some(callee_raw_params) = self.raw_params_by_fn.get(&local_callee) else {
                        continue;
                    };
                    if callee_raw_params.values().any(|idx| *idx == arg_index) {
                        self.add_dep(param_index, (local_callee, arg_index));
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut facts_by_param = FxHashMap::<(LocalDefId, usize), ParamFacts>::default();
    for (def_id, raw_params) in &raw_params_by_fn {
        for index in raw_params.values().copied() {
            facts_by_param.entry((*def_id, index)).or_default();
        }
        let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawFreeSummaryVisitor {
            tcx,
            free_like_wrappers,
            raw_params_by_fn: &raw_params_by_fn,
            current_raw_params: raw_params,
            facts: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (param_index, facts) in visitor.facts {
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .direct_free |= facts.direct_free;
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .deps
                .extend(facts.deps);
        }
    }

    let mut summaries = facts_by_param
        .keys()
        .copied()
        .map(|key| (key, LocalRawParamSummary::BorrowOnly))
        .collect::<FxHashMap<_, _>>();
    loop {
        let mut changed = false;
        for (key, facts) in &facts_by_param {
            let next = if facts.direct_free
                || facts
                    .deps
                    .iter()
                    .any(|dep| summaries.get(dep) != Some(&LocalRawParamSummary::BorrowOnly))
            {
                LocalRawParamSummary::Escapes
            } else {
                LocalRawParamSummary::BorrowOnly
            };
            if summaries.get(key) != Some(&next) {
                summaries.insert(*key, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    summaries
}

fn collect_local_raw_param_summaries(
    tcx: TyCtxt<'_>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> FxHashMap<(LocalDefId, usize), LocalRawParamSummary> {
    #[derive(Default)]
    struct ParamFacts {
        direct_escape: bool,
        deps: FxHashSet<(LocalDefId, usize)>,
    }

    let crate_hir = tcx.hir_crate(());
    let mut raw_params_by_fn = FxHashMap::<LocalDefId, FxHashMap<HirId, usize>>::default();
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
        let def_id = item.owner_id.def_id;
        let body = tcx.hir_body(body);
        let typeck = tcx.typeck(def_id);
        let raw_params = body
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                    return None;
                };
                typeck
                    .node_type(hir_id)
                    .is_raw_ptr()
                    .then_some((hir_id, idx))
            })
            .collect::<FxHashMap<_, _>>();
        if !raw_params.is_empty() {
            raw_params_by_fn.insert(def_id, raw_params);
        }
    }

    struct RawParamSummaryVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        raw_params_by_fn: &'a FxHashMap<LocalDefId, FxHashMap<HirId, usize>>,
        current_raw_params: &'a FxHashMap<HirId, usize>,
        facts: FxHashMap<usize, ParamFacts>,
    }

    impl<'a, 'tcx> RawParamSummaryVisitor<'a, 'tcx> {
        fn param_index(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<usize> {
            let hir_id = hir_unwrapped_local_id(expr)?;
            self.current_raw_params.get(&hir_id).copied()
        }

        fn mark_escape(&mut self, param_index: usize) {
            self.facts.entry(param_index).or_default().direct_escape = true;
        }

        fn add_dep(&mut self, param_index: usize, dep: (LocalDefId, usize)) {
            self.facts.entry(param_index).or_default().deps.insert(dep);
        }
    }

    impl<'tcx> Visitor<'tcx> for RawParamSummaryVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let Some(init) = let_stmt.init
                && let Some(param_index) = self.param_index(init)
            {
                self.mark_escape(param_index);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            match expr.kind {
                hir::ExprKind::Assign(_, rhs, _) => {
                    if let Some(param_index) = self.param_index(rhs) {
                        self.mark_escape(param_index);
                    }
                }
                hir::ExprKind::Ret(Some(ret)) => {
                    if let Some(param_index) = self.param_index(ret) {
                        self.mark_escape(param_index);
                    }
                }
                hir::ExprKind::Call(_, args) => {
                    let free_arg =
                        hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                            .map(|(hir_id, _)| hir_id);
                    let local_callee = hir_called_local_fn(self.tcx, expr);
                    for (arg_index, arg) in args.iter().enumerate() {
                        let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                            continue;
                        };
                        let Some(param_index) = self.current_raw_params.get(&hir_id).copied()
                        else {
                            continue;
                        };
                        if Some(hir_id) == free_arg {
                            self.mark_escape(param_index);
                            continue;
                        }
                        match local_callee {
                            Some(callee) => {
                                let Some(callee_raw_params) = self.raw_params_by_fn.get(&callee)
                                else {
                                    self.mark_escape(param_index);
                                    continue;
                                };
                                if callee_raw_params.values().any(|idx| *idx == arg_index) {
                                    self.add_dep(param_index, (callee, arg_index));
                                } else {
                                    self.mark_escape(param_index);
                                }
                            }
                            None => {
                                if !hir_is_borrow_only_foreign_buffer_arg(self.tcx, expr, arg_index)
                                {
                                    self.mark_escape(param_index);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }

        fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
            intravisit::walk_body(self, body);
            let mut tail = body.value;
            while let hir::ExprKind::Block(block, _) = tail.kind {
                let Some(expr) = block.expr else {
                    break;
                };
                tail = expr;
            }
            if let Some(param_index) = self.param_index(tail) {
                self.mark_escape(param_index);
            }
        }
    }

    let mut facts_by_param = FxHashMap::<(LocalDefId, usize), ParamFacts>::default();
    for (def_id, raw_params) in &raw_params_by_fn {
        for index in raw_params.values().copied() {
            facts_by_param.entry((*def_id, index)).or_default();
        }
        let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawParamSummaryVisitor {
            tcx,
            free_like_wrappers,
            raw_params_by_fn: &raw_params_by_fn,
            current_raw_params: raw_params,
            facts: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (param_index, facts) in visitor.facts {
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .direct_escape |= facts.direct_escape;
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .deps
                .extend(facts.deps);
        }
    }

    let mut summaries = facts_by_param
        .keys()
        .copied()
        .map(|key| (key, LocalRawParamSummary::BorrowOnly))
        .collect::<FxHashMap<_, _>>();
    loop {
        let mut changed = false;
        for (key, facts) in &facts_by_param {
            let next = if facts.direct_escape
                || facts
                    .deps
                    .iter()
                    .any(|dep| summaries.get(dep) != Some(&LocalRawParamSummary::BorrowOnly))
            {
                LocalRawParamSummary::Escapes
            } else {
                LocalRawParamSummary::BorrowOnly
            };
            if summaries.get(key) != Some(&next) {
                summaries.insert(*key, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    summaries
}

fn collect_raw_bridge_bindings(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    alloc_wrappers: &FxHashMap<LocalDefId, AllocWrapperInfo>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
) -> FxHashMap<HirId, RawBridgeInfo> {
    #[derive(Default)]
    struct State {
        bridge: Option<RawBridgeInfo>,
        saw_free: bool,
        saw_return: bool,
        disqualified: bool,
        aliases: FxHashSet<HirId>,
    }

    struct RawBridgeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        alloc_wrappers: &'a FxHashMap<LocalDefId, AllocWrapperInfo>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        local_raw_param_summaries: &'a FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
        wrapper_like_bodies: &'a FxHashSet<LocalDefId>,
        typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
        body_owner: LocalDefId,
        param_positions: FxHashMap<HirId, usize>,
        alias_roots: FxHashMap<HirId, HirId>,
        byte_view_aliases: FxHashSet<HirId>,
        states: FxHashMap<HirId, State>,
        scalar_defs: FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
    }

    impl<'tcx> RawBridgeVisitor<'_, 'tcx> {
        fn mark_root(&mut self, hir_id: HirId, info: RawBridgeInfo) {
            let state = self.states.entry(hir_id).or_default();
            match &state.bridge {
                None => state.bridge = Some(info.clone()),
                Some(existing) if *existing == info => {}
                Some(_) => state.disqualified = true,
            }
            state.aliases.insert(hir_id);
            self.alias_roots.insert(hir_id, hir_id);
        }

        fn mark_alias(&mut self, alias: HirId, source: HirId) {
            let Some(root) = self.alias_roots.get(&source).copied() else {
                return;
            };
            self.alias_roots.insert(alias, root);
            self.states.entry(root).or_default().aliases.insert(alias);
        }

        fn mark_byte_view_alias(&mut self, alias: HirId, source: HirId) {
            self.mark_alias(alias, source);
            self.byte_view_aliases.insert(alias);
        }

        fn state_for_local_mut(&mut self, hir_id: HirId) -> Option<&mut State> {
            let root = self.alias_roots.get(&hir_id).copied().unwrap_or(hir_id);
            self.states.get_mut(&root)
        }

        fn disqualify_local(&mut self, hir_id: HirId) {
            if let Some(state) = self.state_for_local_mut(hir_id) {
                state.disqualified = true;
            }
        }

        fn update_local_from_rhs(
            &mut self,
            lhs_hir_id: HirId,
            rhs: &'tcx hir::Expr<'tcx>,
            lhs_inner_ty: ty::Ty<'tcx>,
        ) {
            if self.byte_view_aliases.contains(&lhs_hir_id)
                && hir_is_byte_view_self_update(lhs_hir_id, rhs)
            {
                return;
            }
            let scalar_ctx = self
                .wrapper_like_bodies
                .contains(&self.body_owner)
                .then_some(WrapperScalarDagContext {
                    tcx: self.tcx,
                    param_positions: &self.param_positions,
                    scalar_defs: &self.scalar_defs,
                });
            if let Some(info) = hir_raw_bridge_info(
                self.tcx,
                lhs_inner_ty,
                rhs,
                Some(self.alloc_wrappers),
                scalar_ctx.as_ref(),
            ) {
                self.mark_root(lhs_hir_id, info);
            } else if let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) {
                if self.byte_view_aliases.contains(&rhs_hir_id) && lhs_hir_id != rhs_hir_id {
                    self.disqualify_local(rhs_hir_id);
                    return;
                }
                let rhs_ty = self.tcx.typeck(rhs_hir_id.owner).node_type(rhs_hir_id);
                let can_mark_byte_view_alias = hir_is_casted_local(rhs, rhs_hir_id)
                    && ty_is_byte_sized_raw_inner(lhs_inner_ty)
                    && unwrap_ptr_from_mir_ty(rhs_ty)
                        .is_some_and(|(rhs_inner_ty, _)| ty_is_byte_sized_raw_inner(rhs_inner_ty))
                    && self
                        .state_for_local_mut(rhs_hir_id)
                        .and_then(|state| state.bridge.as_ref())
                        .is_some_and(|info| matches!(info, RawBridgeInfo::Array { .. }));
                if can_mark_byte_view_alias {
                    self.mark_byte_view_alias(lhs_hir_id, rhs_hir_id);
                    return;
                }
                if self.alloc_wrappers.contains_key(&self.body_owner) {
                    self.mark_alias(lhs_hir_id, rhs_hir_id);
                } else {
                    self.disqualify_local(rhs_hir_id);
                }
            } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                self.disqualify_local(lhs_hir_id);
            }
        }

        fn record_scalar_local(&mut self, hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>) {
            if ty_is_wrapper_scalar_dag_ty(self.typeck.node_type(hir_id)) {
                self.scalar_defs.insert(hir_id, rhs);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for RawBridgeVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                if matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_))) {
                    let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                    if let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) {
                        self.update_local_from_rhs(hir_id, init, lhs_inner_ty);
                    }
                }
                self.record_scalar_local(hir_id, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
            {
                if matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_))) {
                    let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                    if let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) {
                        self.update_local_from_rhs(hir_id, rhs, lhs_inner_ty);
                    }
                }
                self.record_scalar_local(hir_id, rhs);
            }
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs)
                && hir_unwrapped_local_id(lhs).is_none()
            {
                self.disqualify_local(rhs_hir_id);
            }
            if let hir::ExprKind::Call(_, args) = expr.kind {
                let free_arg = hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                    .map(|(hir_id, _)| hir_id);
                let local_callee = hir_called_local_fn(self.tcx, expr);
                let free_arg_is_byte_view =
                    free_arg.is_some_and(|hir_id| self.byte_view_aliases.contains(&hir_id));
                if let Some(hir_id) = free_arg
                    && let Some(state) = self.state_for_local_mut(hir_id)
                {
                    if free_arg_is_byte_view {
                        state.disqualified = true;
                    } else {
                        state.saw_free = true;
                    }
                }
                for (arg_index, arg) in args.iter().enumerate() {
                    if let Some(hir_id) = hir_unwrapped_local_id(arg)
                        && Some(hir_id) != free_arg
                    {
                        if self.byte_view_aliases.contains(&hir_id) {
                            self.disqualify_local(hir_id);
                            continue;
                        }
                        if local_callee.is_none() {
                            continue;
                        }
                        let local_callee = local_callee.unwrap();
                        if self
                            .local_raw_param_summaries
                            .get(&(local_callee, arg_index))
                            != Some(&LocalRawParamSummary::BorrowOnly)
                        {
                            self.disqualify_local(hir_id);
                        }
                    }
                }
            }
            if let hir::ExprKind::Ret(Some(ret)) = expr.kind
                && let Some(hir_id) = hir_unwrapped_local_id(ret)
            {
                if self.byte_view_aliases.contains(&hir_id) {
                    self.disqualify_local(hir_id);
                } else if let Some(state) = self.state_for_local_mut(hir_id) {
                    state.saw_return = true;
                }
            }
            intravisit::walk_expr(self, expr);
        }

        fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
            intravisit::walk_body(self, body);
            if let Some(hir_id) = hir_unwrapped_local_id(body.value) {
                if self.byte_view_aliases.contains(&hir_id) {
                    self.disqualify_local(hir_id);
                } else if let Some(state) = self.state_for_local_mut(hir_id) {
                    state.saw_return = true;
                }
            }
        }
    }

    let mut bindings = FxHashMap::default();
    let wrapper_like_bodies = collect_locally_called_fns(tcx);
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
        let typeck = tcx.typeck(item.owner_id.def_id);
        let mut visitor = RawBridgeVisitor {
            tcx,
            ptr_kinds,
            alloc_wrappers,
            free_like_wrappers,
            local_raw_param_summaries,
            wrapper_like_bodies: &wrapper_like_bodies,
            typeck,
            body_owner: item.owner_id.def_id,
            param_positions: body
                .params
                .iter()
                .enumerate()
                .filter_map(|(idx, param)| {
                    let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                        return None;
                    };
                    Some((hir_id, idx))
                })
                .collect(),
            alias_roots: FxHashMap::default(),
            byte_view_aliases: FxHashSet::default(),
            states: FxHashMap::default(),
            scalar_defs: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (_hir_id, state) in visitor.states {
            let allow_return_bridge =
                state.saw_return && alloc_wrappers.contains_key(&visitor.body_owner);
            if (state.saw_free || allow_return_bridge)
                && !state.disqualified
                && let Some(info) = state.bridge
            {
                for alias in state.aliases {
                    bindings.insert(alias, info.clone());
                }
            }
        }
    }
    bindings
}

fn collect_raw_call_result_bindings(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct RawCallResultVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for RawCallResultVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, ident, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && matches!(
                    hir_callee_output_kind(self.tcx, self.sig_decs, self.ptr_kinds, init),
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
                    hir_callee_output_kind(self.tcx, self.sig_decs, self.ptr_kinds, rhs),
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
            ptr_kinds,
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
    hir_expr: &'tcx hir::Expr<'tcx>,
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
        && hir_callee_output_kind(tcx, sig_decs, ptr_kinds, hir_expr) == Some(target_kind)
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

fn collect_unsupported_box_usage_bindings(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
) -> FxHashSet<HirId> {
    struct UnsupportedBoxUsageVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        local_raw_param_summaries: &'a FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
        byte_view_roots: FxHashMap<HirId, HirId>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> UnsupportedBoxUsageVisitor<'_, 'tcx> {
        fn owning_root_of(&self, hir_id: HirId) -> Option<HirId> {
            if matches!(
                self.ptr_kinds.get(&hir_id),
                Some(PtrKind::OptBox | PtrKind::OptBoxedSlice)
            ) {
                Some(hir_id)
            } else {
                self.byte_view_roots.get(&hir_id).copied()
            }
        }

        fn maybe_mark_byte_view_alias(
            &mut self,
            lhs_hir_id: HirId,
            lhs_ty: ty::Ty<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            if !ty_is_byte_sized_raw_inner(lhs_inner_ty) {
                return;
            }
            let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) else {
                return;
            };
            let Some(root) = self.owning_root_of(rhs_hir_id) else {
                return;
            };
            let rhs_ty = self.tcx.typeck(rhs_hir_id.owner).node_type(rhs_hir_id);
            let Some((rhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(rhs_ty) else {
                return;
            };
            if !ty_is_byte_sized_raw_inner(rhs_inner_ty) || !hir_is_casted_local(rhs, rhs_hir_id) {
                return;
            }
            self.byte_view_roots.insert(lhs_hir_id, root);
            self.bindings.insert(root);
        }

        fn collect_owning_roots_in_expr(&self, expr: &'tcx hir::Expr<'tcx>) -> FxHashSet<HirId> {
            struct RootCollector<'a, 'tcx, 'me> {
                visitor: &'me UnsupportedBoxUsageVisitor<'a, 'tcx>,
                roots: FxHashSet<HirId>,
            }

            impl<'tcx> Visitor<'tcx> for RootCollector<'_, 'tcx, '_> {
                fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                    if let Some(hir_id) = hir_unwrapped_local_id(expr)
                        && let Some(root) = self.visitor.owning_root_of(hir_id)
                    {
                        self.roots.insert(root);
                    }
                    intravisit::walk_expr(self, expr);
                }
            }

            let mut collector = RootCollector {
                visitor: self,
                roots: FxHashSet::default(),
            };
            collector.visit_expr(expr);
            collector.roots
        }
    }

    impl<'tcx> Visitor<'tcx> for UnsupportedBoxUsageVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                self.maybe_mark_byte_view_alias(hir_id, lhs_ty, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(lhs_hir_id) = path.res
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                self.maybe_mark_byte_view_alias(lhs_hir_id, lhs_ty, rhs);
            }

            if let Some(local_callee) = hir_called_local_fn(self.tcx, expr)
                && let hir::ExprKind::Call(_, args) = expr.kind
            {
                for (arg_index, arg) in args.iter().enumerate() {
                    let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                        continue;
                    };
                    let Some(root) = self.owning_root_of(hir_id) else {
                        continue;
                    };
                    if self
                        .local_raw_param_summaries
                        .get(&(local_callee, arg_index))
                        != Some(&LocalRawParamSummary::BorrowOnly)
                    {
                        self.bindings.insert(root);
                    }
                }
            }

            if let Some((hir_id, _)) =
                hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                && let Some(root) = self.owning_root_of(hir_id)
            {
                let is_direct_free = hir_call_matches_foreign_name(self.tcx, expr, "free");
                let direct_box_consume = is_direct_free
                    && hir_id == root
                    && matches!(
                        self.ptr_kinds.get(&hir_id),
                        Some(PtrKind::OptBox | PtrKind::OptBoxedSlice)
                    );
                if !direct_box_consume {
                    self.bindings.insert(root);
                }
            } else if let hir::ExprKind::Call(_, args) = expr.kind
                && (hir_call_matches_foreign_name(self.tcx, expr, "free")
                    || hir_called_local_fn(self.tcx, expr)
                        .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id)))
                && let [arg] = args
            {
                self.bindings.extend(self.collect_owning_roots_in_expr(arg));
            }

            intravisit::walk_expr(self, expr);
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
        let mut visitor = UnsupportedBoxUsageVisitor {
            tcx,
            ptr_kinds,
            free_like_wrappers,
            local_raw_param_summaries,
            byte_view_roots: FxHashMap::default(),
            bindings: FxHashSet::default(),
        };
        visitor.visit_body(body);
        bindings.extend(visitor.bindings);
    }

    bindings
}

fn downgrade_unsupported_allocator_box_kinds(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct BoxDowngradeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        downgraded: FxHashSet<HirId>,
    }

    impl<'tcx> BoxDowngradeVisitor<'_, 'tcx> {
        fn maybe_downgrade(
            &mut self,
            hir_id: HirId,
            lhs_ty: ty::Ty<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            if self.ptr_kinds.get(&hir_id).copied() != Some(PtrKind::OptBox) {
                return;
            }
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

    impl<'tcx> Visitor<'tcx> for BoxDowngradeVisitor<'_, 'tcx> {
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
            ptr_kinds,
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
    Some((
        path.segments.last()?.ident.name,
        pointee_ty,
        &mut closure.body,
    ))
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
    use std::{
        cell::Cell,
        collections::BTreeMap,
        fs,
        path::{Path, PathBuf},
        process::Command,
    };

    use rustc_ast::{Crate, Expr, ItemKind, LocalKind, PatKind, StmtKind};
    use rustc_ast_pretty::pprust;
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::{self as hir, HirId, ItemKind as HirItemKind, OwnerNode};
    use rustc_middle::{
        hir::nested_filter::OnlyBodies,
        ty::{self, TyCtxt},
    };
    use rustc_span::def_id::LocalDefId;

    use super::*;
    use crate::{
        analyses::{self, mir_variable_grouping::SourceVarGroups},
        rewriter::{replace_local_borrows, Config},
        utils::rustc::RustProgram,
    };

    fn synthetic_transform_visitor<'tcx>(tcx: TyCtxt<'tcx>) -> TransformVisitor<'tcx> {
        TransformVisitor {
            tcx,
            sig_decs: SigDecisions {
                data: FxHashMap::default(),
            },
            ptr_kinds: FxHashMap::default(),
            forced_raw_bindings: FxHashSet::default(),
            raw_bridge_bindings: FxHashMap::default(),
            alloc_wrappers: FxHashMap::default(),
            free_like_wrappers: FxHashSet::default(),
            ast_to_hir: AstToHir::default(),
            bytemuck: Cell::new(false),
            slice_cursor: Cell::new(false),
        }
    }

    fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                HirItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                HirItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn build_analysis<'tcx>(tcx: TyCtxt<'tcx>) -> (RustProgram<'tcx>, super::super::Analysis) {
        let arena = typed_arena::Arena::new();
        let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = points_to::andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre_points_to = points_to::andersen::pre_analyze(&andersen_config, &tss, tcx);
        let points_to = points_to::andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
        let aliases = super::super::find_param_aliases(&pre_points_to, &points_to, tcx);

        let input = collect_program(tcx);
        let mutability_result =
            analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
        let output_params =
            analyses::output_params::compute_output_params(&input, &mutability_result, &aliases);
        let ownership_schemes = super::super::maybe_solidified_ownership(
            &super::super::Config::default(),
            &input,
            &output_params,
        );
        let source_var_groups = SourceVarGroups::new(&input);
        let mutables = source_var_groups.postprocess_mut_res(&input, &mutability_result);
        let (mutable_references, shared_references) =
            analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
        let promoted_mut_ref_result =
            source_var_groups.postprocess_promoted_mut_refs(mutable_references);
        let promoted_shared_ref_result =
            source_var_groups.postprocess_promoted_mut_refs(shared_references);
        let fatness_result = analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
        let mut offset_sign_result = analyses::offset_sign::sign::offset_sign_analysis(&input);
        offset_sign_result.access_signs =
            source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
        let analysis = super::super::Analysis {
            promoted_mut_ref_result,
            promoted_shared_ref_result,
            mutability_result,
            fatness_result,
            aliases,
            output_params,
            ownership_schemes,
            offset_sign_result,
        };

        (input, analysis)
    }

    fn b02_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("B02-translated-rust")
    }

    fn b02_project_dirs(root: &Path) -> Vec<PathBuf> {
        let mut projects = Vec::new();
        for category in fs::read_dir(root)
            .unwrap_or_else(|err| panic!("failed to read B02 root `{}`: {err}", root.display()))
        {
            let category = category.unwrap_or_else(|err| {
                panic!("failed to iterate B02 root `{}`: {err}", root.display())
            });
            let category_path = category.path();
            if !category_path.is_dir() {
                continue;
            }

            for project in fs::read_dir(&category_path).unwrap_or_else(|err| {
                panic!(
                    "failed to read B02 category `{}`: {err}",
                    category_path.display()
                )
            }) {
                let project = project.unwrap_or_else(|err| {
                    panic!(
                        "failed to iterate B02 category `{}`: {err}",
                        category_path.display()
                    )
                });
                let project_path = project.path();
                if project_path.is_dir() && project_path.join("Cargo.toml").is_file() {
                    projects.push(project_path);
                }
            }
        }
        projects.sort();
        projects
    }

    fn workspace_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn cargo_bin() -> PathBuf {
        std::env::var_os("CARGO")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("cargo"))
    }

    fn crat_bin_path(workspace_root: &Path) -> PathBuf {
        workspace_root
            .join("target")
            .join("debug")
            .join(format!("crat{}", std::env::consts::EXE_SUFFIX))
    }

    fn ensure_crat_bin_built(workspace_root: &Path) {
        let status = Command::new(cargo_bin())
            .current_dir(workspace_root)
            .args(["build", "--bin", "crat"])
            .status()
            .unwrap_or_else(|err| panic!("failed to build crat binary: {err}"));
        assert!(status.success(), "failed to build crat binary");
    }

    fn reset_temp_dir(path: &Path) {
        if path.exists() {
            fs::remove_dir_all(path).unwrap_or_else(|err| {
                panic!("failed to clear temp dir `{}`: {err}", path.display())
            });
        }
        fs::create_dir_all(path)
            .unwrap_or_else(|err| panic!("failed to create temp dir `{}`: {err}", path.display()));
    }

    #[derive(Debug)]
    struct ProjectCompileRecord {
        project: String,
        translated_dir: PathBuf,
        crat_ok: bool,
        cargo_check_ok: bool,
        failure_output: Option<String>,
    }

    fn trim_command_output(output: &[u8]) -> String {
        let output = String::from_utf8_lossy(output);
        let lines = output.lines().collect::<Vec<_>>();
        let start = lines.len().saturating_sub(40);
        lines[start..].join("\n")
    }

    fn run_b02_pointer_compile_gate(temp_root_name: &str) -> Vec<ProjectCompileRecord> {
        let workspace_root = workspace_root();
        ensure_crat_bin_built(&workspace_root);
        let crat_bin = crat_bin_path(&workspace_root);
        assert!(
            crat_bin.is_file(),
            "expected crat binary at `{}`",
            crat_bin.display()
        );

        let b02_root = b02_root();
        let temp_root = std::env::temp_dir().join(temp_root_name);
        reset_temp_dir(&temp_root);
        let shared_target_dir = temp_root.join("_cargo_target");
        fs::create_dir_all(&shared_target_dir).unwrap_or_else(|err| {
            panic!(
                "failed to create shared cargo target dir `{}`: {err}",
                shared_target_dir.display()
            )
        });

        let mut records = Vec::new();
        for project_dir in b02_project_dirs(&b02_root) {
            let rel_project = project_dir
                .strip_prefix(&b02_root)
                .unwrap_or(project_dir.as_path())
                .to_path_buf();
            let project_name = project_dir
                .file_name()
                .expect("project directory should have a name");
            let output_parent = temp_root.join(rel_project.parent().unwrap_or(Path::new("")));
            fs::create_dir_all(&output_parent).unwrap_or_else(|err| {
                panic!(
                    "failed to create output parent `{}`: {err}",
                    output_parent.display()
                )
            });
            let translated_dir = output_parent.join(project_name);

            let crat_output = Command::new(&crat_bin)
                .current_dir(&workspace_root)
                .args([
                    "--pass",
                    "pointer",
                    "--pass",
                    "check",
                    "--output",
                    output_parent.to_str().expect("utf8 path"),
                    project_dir.to_str().expect("utf8 path"),
                ])
                .output()
                .unwrap_or_else(|err| {
                    panic!(
                        "failed to execute crat for `{}`: {err}",
                        rel_project.display()
                    )
                });

            if !crat_output.status.success() {
                records.push(ProjectCompileRecord {
                    project: rel_project.display().to_string(),
                    translated_dir,
                    crat_ok: false,
                    cargo_check_ok: false,
                    failure_output: Some(trim_command_output(&crat_output.stderr)),
                });
                continue;
            }

            let cargo_check_output = Command::new(cargo_bin())
                .current_dir(&translated_dir)
                .env("CARGO_TARGET_DIR", &shared_target_dir)
                .args(["check", "--offline"])
                .output()
                .unwrap_or_else(|err| {
                    panic!(
                        "failed to run cargo check for `{}`: {err}",
                        rel_project.display()
                    )
                });

            records.push(ProjectCompileRecord {
                project: rel_project.display().to_string(),
                translated_dir,
                crat_ok: true,
                cargo_check_ok: cargo_check_output.status.success(),
                failure_output: (!cargo_check_output.status.success())
                    .then(|| trim_command_output(&cargo_check_output.stderr)),
            });
        }

        records
    }

    #[derive(Clone, Copy, Debug, Default)]
    struct PtrKindCounts {
        opt_box: usize,
        opt_boxed_slice: usize,
        raw: usize,
        opt_ref: usize,
        slice: usize,
        slice_cursor: usize,
        none: usize,
    }

    impl PtrKindCounts {
        fn bump(&mut self, kind: Option<PtrKind>) {
            match kind {
                Some(PtrKind::OptBox) => self.opt_box += 1,
                Some(PtrKind::OptBoxedSlice) => self.opt_boxed_slice += 1,
                Some(PtrKind::Raw(_)) => self.raw += 1,
                Some(PtrKind::OptRef(_)) => self.opt_ref += 1,
                Some(PtrKind::Slice(_)) => self.slice += 1,
                Some(PtrKind::SliceCursor(_)) => self.slice_cursor += 1,
                None => self.none += 1,
            }
        }
    }

    #[derive(Clone, Copy, Debug, Default)]
    struct DowngradeReasonCounts {
        unsupported_allocator_root: usize,
        raw_call_result: usize,
        raw_local_assignment: usize,
        unsupported_target: usize,
        unsupported_usage: usize,
        other: usize,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct BindingKey {
        owner: LocalDefId,
        hir_id: HirId,
    }

    #[derive(Clone, Debug)]
    struct AllocSite {
        hir_id: HirId,
        fn_name: String,
        binding_name: String,
        rhs_snippet: String,
        scalar_rejection_hint: Option<&'static str>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum SafetyAllocKind {
        Scalar,
        Array,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum SafetySiteShape {
        DirectLocalRoot,
        AllocatorWrapperPrincipalLocal,
        NonOutermostLocalRoot,
    }

    #[derive(Clone, Debug)]
    struct TrackedSemanticAllocSite {
        hir_id: HirId,
        fn_name: String,
        binding_name: String,
        rhs_snippet: String,
        kind: SafetyAllocKind,
        outermost: bool,
        shape: SafetySiteShape,
        deref_count: usize,
        free_count: usize,
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct SplitKindCounts {
        scalar: usize,
        array: usize,
    }

    impl SplitKindCounts {
        fn bump(&mut self, kind: SafetyAllocKind) {
            self.bump_by(kind, 1);
        }

        fn bump_by(&mut self, kind: SafetyAllocKind, amount: usize) {
            match kind {
                SafetyAllocKind::Scalar => self.scalar += amount,
                SafetyAllocKind::Array => self.array += amount,
            }
        }

        fn total(self) -> usize {
            self.scalar + self.array
        }
    }

    impl std::ops::AddAssign for SplitKindCounts {
        fn add_assign(&mut self, rhs: Self) {
            self.scalar += rhs.scalar;
            self.array += rhs.array;
        }
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct SafetyBeforeStats {
        allocation_sites: SplitKindCounts,
        dereferences: SplitKindCounts,
        frees: SplitKindCounts,
    }

    impl SafetyBeforeStats {
        fn record_site(&mut self, site: &TrackedSemanticAllocSite) {
            self.allocation_sites.bump(site.kind);
            self.dereferences.bump_by(site.kind, site.deref_count);
            self.frees.bump_by(site.kind, site.free_count);
        }
    }

    impl std::ops::AddAssign for SafetyBeforeStats {
        fn add_assign(&mut self, rhs: Self) {
            self.allocation_sites += rhs.allocation_sites;
            self.dereferences += rhs.dereferences;
            self.frees += rhs.frees;
        }
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct BridgeCallCounts {
        leak: usize,
        from_raw: usize,
        into_raw: usize,
    }

    impl std::ops::AddAssign for BridgeCallCounts {
        fn add_assign(&mut self, rhs: Self) {
            self.leak += rhs.leak;
            self.from_raw += rhs.from_raw;
            self.into_raw += rhs.into_raw;
        }
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct RewrittenUnsafeStats {
        dereferences: usize,
        frees: usize,
        bridge_calls: BridgeCallCounts,
    }

    impl std::ops::AddAssign for RewrittenUnsafeStats {
        fn add_assign(&mut self, rhs: Self) {
            self.dereferences += rhs.dereferences;
            self.frees += rhs.frees;
            self.bridge_calls += rhs.bridge_calls;
        }
    }

    #[derive(Clone, Debug)]
    struct OutermostReasonRecord {
        reason: &'static str,
        example: String,
        usage_subreasons: Vec<&'static str>,
    }

    #[derive(Clone, Debug)]
    struct PointerSafetyProjectRecord {
        project: String,
        before_total: SafetyBeforeStats,
        before_outermost: SafetyBeforeStats,
        safe_box_sites: SplitKindCounts,
        after: RewrittenUnsafeStats,
    }

    #[derive(Clone, Debug)]
    struct PointerSafetyAnalysisResult {
        before_total: SafetyBeforeStats,
        before_outermost: SafetyBeforeStats,
        safe_box_sites: SplitKindCounts,
        tracked_sites: Vec<TrackedSemanticAllocSite>,
        outermost_reasons: Vec<OutermostReasonRecord>,
    }

    #[derive(Clone, Debug, Default)]
    struct TrackedBindingSpecs {
        by_fn: FxHashMap<String, FxHashSet<String>>,
    }

    fn hir_is_direct_allocator_root(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
        let Some(name) = hir_call_name(expr) else {
            return false;
        };
        match (name, hir_unwrap_casts(expr).kind) {
            (name, hir::ExprKind::Call(_, _)) if name == Symbol::intern("malloc") => true,
            (name, hir::ExprKind::Call(_, _)) if name == Symbol::intern("calloc") => true,
            (name, hir::ExprKind::Call(_, args)) if name == Symbol::intern("realloc") => {
                matches!(args, [ptr, _] if hir_is_null_like_ptr_arg(tcx, ptr))
            }
            _ => false,
        }
    }

    fn hir_is_direct_malloc_or_calloc(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
        matches!(
            hir_call_name(expr),
            Some(name) if name == Symbol::intern("malloc") || name == Symbol::intern("calloc")
        ) && !matches!(
            hir_call_name(expr),
            Some(name) if name == Symbol::intern("realloc") && hir_is_null_like_ptr_arg(tcx, expr)
        )
    }

    fn normalized_hir_snippet(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> String {
        tcx.sess
            .source_map()
            .span_to_snippet(expr.span)
            .ok()
            .map(|snippet| snippet.split_whitespace().collect::<Vec<_>>().join(" "))
            .unwrap_or_else(|| "<snippet unavailable>".to_string())
    }

    fn classify_semantic_allocator_kind<'tcx>(
        tcx: TyCtxt<'tcx>,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
    ) -> SafetyAllocKind {
        if hir_supports_scalar_box_allocator_root(tcx, lhs_inner_ty, rhs)
            || matches!(
                hir_raw_bridge_info(tcx, lhs_inner_ty, rhs, None, None),
                Some(RawBridgeInfo::Scalar)
            )
        {
            SafetyAllocKind::Scalar
        } else {
            SafetyAllocKind::Array
        }
    }

    fn root_of_raw_expr(
        expr: &hir::Expr<'_>,
        root_of_local: &FxHashMap<HirId, HirId>,
    ) -> Option<HirId> {
        let expr = hir_unwrap_casts(expr);
        match expr.kind {
            hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => {
                let hir::def::Res::Local(hir_id) = path.res else {
                    return None;
                };
                root_of_local.get(&hir_id).copied()
            }
            hir::ExprKind::MethodCall(seg, receiver, _, _)
                if matches!(
                    seg.ident.name.as_str(),
                    "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
                ) =>
            {
                root_of_raw_expr(receiver, root_of_local)
            }
            _ => None,
        }
    }

    fn unwrap_body_tail<'tcx>(mut expr: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
        while let hir::ExprKind::Block(block, _) = expr.kind {
            let Some(tail) = block.expr else {
                break;
            };
            expr = tail;
        }
        expr
    }

    fn box_bridge_call_kind(expr: &hir::Expr<'_>) -> Option<&'static str> {
        let hir::ExprKind::Call(callee, _) = hir_unwrap_casts(expr).kind else {
            return None;
        };
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind
        else {
            return None;
        };
        let segments = &path.segments;
        if segments.len() < 2 {
            return None;
        }
        let owner = segments[segments.len() - 2].ident.name.as_str();
        let method = segments[segments.len() - 1].ident.name.as_str();
        if owner != "Box" {
            return None;
        }
        match method {
            "leak" => Some("leak"),
            "from_raw" => Some("from_raw"),
            "into_raw" => Some("into_raw"),
            _ => None,
        }
    }

    fn bridge_call_counts_from_source(source: &str) -> BridgeCallCounts {
        BridgeCallCounts {
            leak: source.matches("Box::leak(").count(),
            from_raw: source.matches("Box::from_raw(").count(),
            into_raw: source.matches("Box::into_raw(").count(),
        }
    }

    fn tracked_binding_specs_from_sites(sites: &[TrackedSemanticAllocSite]) -> TrackedBindingSpecs {
        let mut specs = TrackedBindingSpecs::default();
        for site in sites {
            specs
                .by_fn
                .entry(site.fn_name.clone())
                .or_default()
                .insert(site.binding_name.clone());
        }
        specs
    }

    fn collect_rewritten_tracked_unsafe_stats(
        tcx: TyCtxt<'_>,
        tracked_bindings: &TrackedBindingSpecs,
    ) -> RewrittenUnsafeStats {
        struct Visitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
            tracked_bindings: &'a FxHashSet<String>,
            free_like_wrappers: &'a FxHashSet<LocalDefId>,
            root_of_local: FxHashMap<HirId, HirId>,
            stats: RewrittenUnsafeStats,
        }

        impl<'a, 'tcx> Visitor<'a, 'tcx> {
            fn maybe_seed_tracked_binding(&mut self, hir_id: HirId) {
                if !self.typeck.node_type(hir_id).is_raw_ptr() {
                    return;
                }
                let binding_name = self.tcx.hir_name(hir_id).to_string();
                if self.tracked_bindings.contains(&binding_name) {
                    self.root_of_local.insert(hir_id, hir_id);
                }
            }

            fn assign_or_clear_local_alias(
                &mut self,
                lhs_hir_id: HirId,
                lhs_ty: ty::Ty<'tcx>,
                rhs: &'tcx hir::Expr<'tcx>,
            ) {
                if !lhs_ty.is_raw_ptr() {
                    return;
                }
                if let Some(root) = root_of_raw_expr(rhs, &self.root_of_local) {
                    self.root_of_local.insert(lhs_hir_id, root);
                } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                    self.root_of_local.remove(&lhs_hir_id);
                }
            }
        }

        impl<'tcx> hir::intravisit::Visitor<'tcx> for Visitor<'_, 'tcx> {
            type NestedFilter = OnlyBodies;

            fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
                self.tcx
            }

            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                {
                    self.maybe_seed_tracked_binding(hir_id);
                    if let Some(init) = let_stmt.init {
                        let lhs_ty = self.typeck.node_type(hir_id);
                        self.assign_or_clear_local_alias(hir_id, lhs_ty, init);
                    }
                }
                hir::intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let Some(kind) = box_bridge_call_kind(expr) {
                    match kind {
                        "leak" => self.stats.bridge_calls.leak += 1,
                        "from_raw" => self.stats.bridge_calls.from_raw += 1,
                        "into_raw" => self.stats.bridge_calls.into_raw += 1,
                        _ => {}
                    }
                }

                if let hir::ExprKind::Unary(hir::UnOp::Deref, inner) = expr.kind
                    && self.tcx.typeck(expr.hir_id.owner).expr_ty(inner).is_raw_ptr()
                    && root_of_raw_expr(inner, &self.root_of_local).is_some()
                {
                    self.stats.dereferences += 1;
                }

                if let hir::ExprKind::Call(_, args) = expr.kind
                    && args.len() == 1
                    && (hir_call_matches_foreign_name(self.tcx, expr, "free")
                        || hir_called_local_fn(self.tcx, expr)
                            .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id)))
                    && self.tcx.typeck(expr.hir_id.owner).expr_ty(&args[0]).is_raw_ptr()
                    && root_of_raw_expr(&args[0], &self.root_of_local).is_some()
                {
                    self.stats.frees += 1;
                }

                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let hir::def::Res::Local(lhs_hir_id) = path.res
                {
                    let lhs_ty = self.typeck.expr_ty(lhs);
                    self.assign_or_clear_local_alias(lhs_hir_id, lhs_ty, rhs);
                }

                hir::intravisit::walk_expr(self, expr);
            }
        }

        let free_like_wrappers = collect_local_free_wrappers(tcx);
        let mut stats = RewrittenUnsafeStats::default();
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
            let fn_name = tcx.item_name(item.owner_id.def_id.to_def_id()).to_string();
            let Some(fn_tracked_bindings) = tracked_bindings.by_fn.get(&fn_name) else {
                continue;
            };
            let mut visitor = Visitor {
                tcx,
                typeck: tcx.typeck(item.owner_id.def_id),
                tracked_bindings: fn_tracked_bindings,
                free_like_wrappers: &free_like_wrappers,
                root_of_local: FxHashMap::default(),
                stats: RewrittenUnsafeStats::default(),
            };
            visitor.visit_body(tcx.hir_body(body));
            stats += visitor.stats;
        }
        stats
    }

    fn analyze_local_allocator_roots(
        tcx: TyCtxt<'_>,
        did: LocalDefId,
        alloc_wrappers: &FxHashMap<LocalDefId, AllocWrapperInfo>,
        free_like_wrappers: &FxHashSet<LocalDefId>,
    ) -> Vec<TrackedSemanticAllocSite> {
        #[derive(Clone, Debug)]
        struct RootState {
            site: TrackedSemanticAllocSite,
            stored_to_projection: bool,
            returned: bool,
        }

        struct Visitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            did: LocalDefId,
            typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
            free_like_wrappers: &'a FxHashSet<LocalDefId>,
            root_of_local: FxHashMap<HirId, HirId>,
            states: FxHashMap<HirId, RootState>,
        }

        impl<'a, 'tcx> Visitor<'a, 'tcx> {
            fn register_root(&mut self, hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>, lhs_ty: ty::Ty<'tcx>) {
                let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                    return;
                };
                let state = RootState {
                    site: TrackedSemanticAllocSite {
                        hir_id,
                        fn_name: self
                            .tcx
                            .item_name(self.did.to_def_id())
                            .to_string(),
                        binding_name: self.tcx.hir_name(hir_id).to_string(),
                        rhs_snippet: normalized_hir_snippet(self.tcx, rhs),
                        kind: classify_semantic_allocator_kind(self.tcx, lhs_inner_ty, rhs),
                        outermost: false,
                        shape: SafetySiteShape::NonOutermostLocalRoot,
                        deref_count: 0,
                        free_count: 0,
                    },
                    stored_to_projection: false,
                    returned: false,
                };
                self.root_of_local.insert(hir_id, hir_id);
                self.states.insert(hir_id, state);
            }

            fn assign_or_clear_local_alias(
                &mut self,
                lhs_hir_id: HirId,
                lhs_ty: ty::Ty<'tcx>,
                rhs: &'tcx hir::Expr<'tcx>,
            ) {
                if !lhs_ty.is_raw_ptr() {
                    return;
                }
                if let Some(root) = root_of_raw_expr(rhs, &self.root_of_local) {
                    self.root_of_local.insert(lhs_hir_id, root);
                } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                    self.root_of_local.remove(&lhs_hir_id);
                }
            }

            fn mark_projection_escape(&mut self, rhs: &'tcx hir::Expr<'tcx>) {
                if let Some(root) = root_of_raw_expr(rhs, &self.root_of_local)
                    && let Some(state) = self.states.get_mut(&root)
                {
                    state.stored_to_projection = true;
                }
            }

            fn mark_returned(&mut self, expr: &'tcx hir::Expr<'tcx>) {
                if let Some(root) = root_of_raw_expr(expr, &self.root_of_local)
                    && let Some(state) = self.states.get_mut(&root)
                {
                    state.returned = true;
                }
            }

            fn record_raw_deref(&mut self, expr: &'tcx hir::Expr<'tcx>) {
                let hir::ExprKind::Unary(hir::UnOp::Deref, inner) = expr.kind else {
                    return;
                };
                if !self.typeck.expr_ty(inner).is_raw_ptr() {
                    return;
                }
                let Some(root) = root_of_raw_expr(inner, &self.root_of_local) else {
                    return;
                };
                if let Some(state) = self.states.get_mut(&root) {
                    state.site.deref_count += 1;
                }
            }

            fn record_free_like_use(&mut self, expr: &'tcx hir::Expr<'tcx>) {
                let hir::ExprKind::Call(_, args) = expr.kind else {
                    return;
                };
                let [arg] = args else {
                    return;
                };
                let is_free_like = hir_call_matches_foreign_name(self.tcx, expr, "free")
                    || hir_called_local_fn(self.tcx, expr)
                        .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id));
                if !is_free_like {
                    return;
                }
                let Some(root) = root_of_raw_expr(arg, &self.root_of_local) else {
                    return;
                };
                if let Some(state) = self.states.get_mut(&root) {
                    state.site.free_count += 1;
                }
            }
        }

        impl<'tcx> hir::intravisit::Visitor<'tcx> for Visitor<'_, 'tcx> {
            type NestedFilter = OnlyBodies;

            fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
                self.tcx
            }

            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    && let Some(init) = let_stmt.init
                {
                    let lhs_ty = self.typeck.node_type(hir_id);
                    if hir_is_direct_allocator_root(self.tcx, init) {
                        self.register_root(hir_id, init, lhs_ty);
                    } else {
                        self.assign_or_clear_local_alias(hir_id, lhs_ty, init);
                    }
                }
                hir::intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                self.record_raw_deref(expr);
                self.record_free_like_use(expr);

                match expr.kind {
                    hir::ExprKind::Assign(lhs, rhs, _) => {
                        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                            && let hir::def::Res::Local(lhs_hir_id) = path.res
                        {
                            let lhs_ty = self.typeck.expr_ty(lhs);
                            if hir_is_direct_allocator_root(self.tcx, rhs) {
                                self.register_root(lhs_hir_id, rhs, lhs_ty);
                            } else {
                                self.assign_or_clear_local_alias(lhs_hir_id, lhs_ty, rhs);
                            }
                        } else {
                            self.mark_projection_escape(rhs);
                        }
                    }
                    hir::ExprKind::Ret(Some(ret)) => self.mark_returned(ret),
                    _ => {}
                }

                hir::intravisit::walk_expr(self, expr);
            }

            fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
                hir::intravisit::walk_body(self, body);
                self.mark_returned(unwrap_body_tail(body.value));
            }
        }

        let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
            return Vec::new();
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            return Vec::new();
        };
        let body = tcx.hir_body(body);
        let mut visitor = Visitor {
            tcx,
            did,
            typeck: tcx.typeck(did),
            free_like_wrappers,
            root_of_local: FxHashMap::default(),
            states: FxHashMap::default(),
        };
        visitor.visit_body(body);

        let wrapper_principal_root = if alloc_wrappers.contains_key(&did) {
            visitor
                .states
                .iter()
                .find_map(|(hir_id, state)| state.returned.then_some(*hir_id))
        } else {
            None
        };

        let mut sites = visitor
            .states
            .into_iter()
            .map(|(hir_id, mut state)| {
                if Some(hir_id) == wrapper_principal_root {
                    state.site.outermost = true;
                    state.site.shape = SafetySiteShape::AllocatorWrapperPrincipalLocal;
                } else if alloc_wrappers.contains_key(&did) {
                    state.site.outermost = false;
                    state.site.shape = SafetySiteShape::NonOutermostLocalRoot;
                } else if !state.stored_to_projection {
                    state.site.outermost = true;
                    state.site.shape = SafetySiteShape::DirectLocalRoot;
                } else {
                    state.site.outermost = false;
                    state.site.shape = SafetySiteShape::NonOutermostLocalRoot;
                }
                state.site
            })
            .collect::<Vec<_>>();
        sites.sort_by_key(|site| (site.fn_name.clone(), site.binding_name.clone()));
        sites
    }

    fn collect_semantic_allocator_sites(
        tcx: TyCtxt<'_>,
        input: &RustProgram<'_>,
    ) -> Vec<TrackedSemanticAllocSite> {
        let alloc_wrappers = collect_local_allocator_wrappers(tcx);
        let free_like_wrappers = collect_local_free_wrappers(tcx);
        let mut sites = Vec::new();
        for did in &input.functions {
            sites.extend(analyze_local_allocator_roots(
                tcx,
                *did,
                &alloc_wrappers,
                &free_like_wrappers,
            ));
        }
        sites
    }

    fn tracked_site_example(project: &str, site: &TrackedSemanticAllocSite) -> String {
        format!(
            "{project}::{}::{} => {}",
            site.fn_name, site.binding_name, site.rhs_snippet
        )
    }

    fn analyze_pointer_safety_for_program(
        tcx: TyCtxt<'_>,
        project: &str,
    ) -> PointerSafetyAnalysisResult {
        let (input, analysis) = build_analysis(tcx);
        let tracked_sites = collect_semantic_allocator_sites(tcx, &input);
        let initial_ptr_kinds = collect_diffs(&input, &analysis);
        let (_sig_decs, final_ptr_kinds, reason_map, usage_subreason_map) =
            simulate_transform_reasons(tcx, &input, &analysis);

        let mut before_total = SafetyBeforeStats::default();
        let mut before_outermost = SafetyBeforeStats::default();
        let mut safe_box_sites = SplitKindCounts::default();
        let mut outermost_reasons = Vec::new();

        let mir_local_maps = input
            .functions
            .iter()
            .map(|did| (*did, utils::ir::map_thir_to_mir(*did, false, tcx)))
            .collect::<FxHashMap<_, _>>();

        for site in &tracked_sites {
            before_total.record_site(site);
            if site.outermost {
                before_outermost.record_site(site);
            }

            if !site.outermost {
                continue;
            }

            let final_kind = final_ptr_kinds.get(&site.hir_id).copied();
            match final_kind {
                Some(PtrKind::OptBox) => {
                    safe_box_sites.bump(SafetyAllocKind::Scalar);
                    continue;
                }
                Some(PtrKind::OptBoxedSlice) => {
                    safe_box_sites.bump(SafetyAllocKind::Array);
                    continue;
                }
                _ => {}
            }

            let initial_kind = initial_ptr_kinds.get(&site.hir_id).copied();
            let reason = if matches!(initial_kind, Some(PtrKind::Raw(_))) {
                let did = site.hir_id.owner.def_id;
                let hir_to_mir = mir_local_maps
                    .get(&did)
                    .expect("expected THIR->MIR map for tracked site");
                let local = *hir_to_mir
                    .binding_to_local
                    .get(&site.hir_id)
                    .expect("expected tracked site local mapping");
                let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                classify_initial_raw_reason(&analysis, did, local, &body.local_decls[local], tcx)
            } else {
                reason_map
                    .get(&site.hir_id)
                    .and_then(|reasons| reasons.first().copied())
                    .unwrap_or("other")
            };

            outermost_reasons.push(OutermostReasonRecord {
                reason,
                example: tracked_site_example(project, site),
                usage_subreasons: if reason == "unsupported_box_usage" {
                    usage_subreason_map
                        .get(&site.hir_id)
                        .cloned()
                        .unwrap_or_else(|| vec!["unknown_usage"])
                } else {
                    Vec::new()
                },
            });
        }

        PointerSafetyAnalysisResult {
            before_total,
            before_outermost,
            safe_box_sites,
            tracked_sites,
            outermost_reasons,
        }
    }

    fn analyze_pointer_safety_for_code(code: &str) -> (PointerSafetyAnalysisResult, RewrittenUnsafeStats) {
        let result = ::utils::compilation::run_compiler_on_str(code, |tcx| {
            analyze_pointer_safety_for_program(tcx, "<snippet>")
        })
        .unwrap();
        let tracked_bindings = tracked_binding_specs_from_sites(&result.tracked_sites);
        let (rewritten, _) =
            ::utils::compilation::run_compiler_on_str(code, |tcx| {
                replace_local_borrows(&Config::default(), tcx)
            })
            .unwrap();
        let mut after =
            ::utils::compilation::run_compiler_on_str(&rewritten, |tcx| {
                collect_rewritten_tracked_unsafe_stats(tcx, &tracked_bindings)
            })
            .unwrap_or_else(|_| panic!("rewritten snippet failed to compile:\n{rewritten}"));
        after.bridge_calls = bridge_call_counts_from_source(&rewritten);
        (result, after)
    }

    fn classify_scalar_allocator_rejection<'tcx>(
        tcx: TyCtxt<'tcx>,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs: &hir::Expr<'tcx>,
    ) -> &'static str {
        let Some(name) = hir_call_name(rhs) else {
            return "other_scalar_root";
        };
        let ty_name = mir_ty_to_string(lhs_inner_ty, tcx);
        match hir_unwrap_casts(rhs).kind {
            hir::ExprKind::Call(_, args) if name == Symbol::intern("malloc") => {
                let [bytes] = args else {
                    return "other_scalar_root";
                };
                if !hir_is_exact_size_of_expr(tcx, bytes, &ty_name) {
                    "malloc_non_exact_sizeof"
                } else {
                    "other_scalar_root"
                }
            }
            hir::ExprKind::Call(_, args) if name == Symbol::intern("calloc") => {
                let [count, elem_size] = args else {
                    return "other_scalar_root";
                };
                let count_ok = hir_is_literal_one(tcx, count);
                let elem_ok = hir_is_exact_size_of_expr(tcx, elem_size, &ty_name);
                match (count_ok, elem_ok) {
                    (false, false) => "calloc_count_not_one_and_elem_size_not_exact",
                    (false, true) => "calloc_count_not_one",
                    (true, false) => "calloc_elem_size_not_exact",
                    (true, true) => "other_scalar_root",
                }
            }
            _ => "other_scalar_root",
        }
    }

    fn collect_direct_allocator_sites(tcx: TyCtxt<'_>, did: LocalDefId) -> Vec<AllocSite> {
        struct Visitor<'tcx> {
            tcx: TyCtxt<'tcx>,
            sites: Vec<AllocSite>,
        }

        impl<'tcx> hir::intravisit::Visitor<'tcx> for Visitor<'tcx> {
            type NestedFilter = OnlyBodies;

            fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
                self.tcx
            }

            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    && let Some(init) = let_stmt.init
                    && hir_is_direct_malloc_or_calloc(self.tcx, init)
                {
                    let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                    let scalar_rejection_hint = unwrap_ptr_from_mir_ty(lhs_ty)
                        .map(|(inner_ty, _)| {
                            classify_scalar_allocator_rejection(self.tcx, inner_ty, init)
                        })
                        .filter(|reason| *reason != "other_scalar_root");
                    self.sites.push(AllocSite {
                        hir_id,
                        fn_name: self
                            .tcx
                            .item_name(hir_id.owner.def_id.to_def_id())
                            .to_string(),
                        binding_name: self.tcx.hir_name(hir_id).to_string(),
                        rhs_snippet: normalized_hir_snippet(self.tcx, init),
                        scalar_rejection_hint,
                    });
                }
                hir::intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let hir::def::Res::Local(hir_id) = path.res
                    && hir_is_direct_malloc_or_calloc(self.tcx, rhs)
                {
                    let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                    let scalar_rejection_hint = unwrap_ptr_from_mir_ty(lhs_ty)
                        .map(|(inner_ty, _)| {
                            classify_scalar_allocator_rejection(self.tcx, inner_ty, rhs)
                        })
                        .filter(|reason| *reason != "other_scalar_root");
                    self.sites.push(AllocSite {
                        hir_id,
                        fn_name: self
                            .tcx
                            .item_name(hir_id.owner.def_id.to_def_id())
                            .to_string(),
                        binding_name: self.tcx.hir_name(hir_id).to_string(),
                        rhs_snippet: normalized_hir_snippet(self.tcx, rhs),
                        scalar_rejection_hint,
                    });
                }
                hir::intravisit::walk_expr(self, expr);
            }
        }

        let mut visitor = Visitor {
            tcx,
            sites: Vec::new(),
        };
        visitor.visit_body(tcx.hir_body_owned_by(did));
        visitor.sites
    }

    #[derive(Default)]
    struct Bucket {
        count: usize,
        examples: Vec<String>,
    }

    impl Bucket {
        fn push(&mut self, example: String) {
            self.count += 1;
            if self.examples.len() < 3 && !self.examples.contains(&example) {
                self.examples.push(example);
            }
        }
    }

    fn push_bucket(
        buckets: &mut BTreeMap<&'static str, Bucket>,
        key: &'static str,
        example: String,
    ) {
        buckets.entry(key).or_default().push(example);
    }

    fn site_example(project: &str, site: &AllocSite) -> String {
        format!(
            "{project}::{}::{} => {}",
            site.fn_name, site.binding_name, site.rhs_snippet
        )
    }

    fn classify_initial_raw_reason<'tcx>(
        analysis: &super::super::Analysis,
        did: LocalDefId,
        local: rustc_middle::mir::Local,
        decl: &rustc_middle::mir::LocalDecl<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> &'static str {
        let (inner_ty, _) = unwrap_ptr_from_mir_ty(decl.ty).expect("expected pointer local");
        if inner_ty.is_c_void(tcx) || utils::file::contains_file_ty(inner_ty, tcx) {
            return "c_void_or_file";
        }

        let mutable_pointers = analysis
            .mutability_result
            .function_body_facts(did)
            .map(|mutabilities| mutabilities.iter().any(|m| m.is_mutable()))
            .collect::<rustc_index::IndexVec<rustc_middle::mir::Local, _>>();
        let aliases = analysis.aliases.get(&did).and_then(|map| map.get(&local));
        if aliases.is_some_and(|aliases| {
            std::iter::once(local)
                .chain(aliases.iter().copied())
                .any(|alias_local| mutable_pointers[alias_local])
        }) {
            return "alias_cluster";
        }

        let array_pointers = analysis
            .fatness_result
            .function_body_facts(did)
            .map(|fatnesses| fatnesses.iter().next().map(|f| f.is_arr()).unwrap_or(false))
            .collect::<rustc_index::IndexVec<rustc_middle::mir::Local, _>>();
        let needs_cursor = analysis
            .offset_sign_result
            .access_signs
            .get(&did)
            .is_some_and(|signs| signs.contains(local));
        let is_local_struct = matches!(
            inner_ty.kind(),
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
        );
        let owning = analysis
            .ownership_schemes
            .as_ref()
            .expect("ownership analysis should exist")
            .fn_results(&did.to_def_id())
            .local_result(local)
            .first()
            .is_some_and(crate::analyses::ownership::Ownership::is_owning);

        if owning && array_pointers[local] {
            if needs_cursor {
                return "array_needs_cursor";
            }
            if is_local_struct {
                return "array_local_struct";
            }
        }

        if owning
            && matches!(
                inner_ty.kind(),
                ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..)
            )
        {
            return "nested_raw_or_ref";
        }

        "other_initial_raw"
    }

    fn simulate_transform_reasons<'tcx>(
        tcx: TyCtxt<'tcx>,
        input: &RustProgram<'tcx>,
        analysis: &super::super::Analysis,
    ) -> (
        SigDecisions,
        FxHashMap<HirId, PtrKind>,
        FxHashMap<HirId, Vec<&'static str>>,
        FxHashMap<HirId, Vec<&'static str>>,
    ) {
        let mut sig_decs = SigDecisions::new(input, analysis);
        let mut ptr_kinds = collect_diffs(input, analysis);
        let free_like_wrappers = collect_local_free_wrappers(tcx);
        let local_raw_free_summaries = collect_local_raw_free_summaries(tcx, &free_like_wrappers);
        let local_raw_param_summaries =
            collect_local_raw_param_summaries(tcx, &free_like_wrappers);
        let mut reason_map: FxHashMap<HirId, Vec<&'static str>> = FxHashMap::default();
        let mut usage_subreason_map: FxHashMap<HirId, Vec<&'static str>> = FxHashMap::default();
        let mut forced_raw_bindings = downgrade_unsupported_allocator_box_kinds(tcx, &ptr_kinds);
        for hir_id in &forced_raw_bindings {
            reason_map
                .entry(*hir_id)
                .or_default()
                .push("unsupported_allocator_root");
        }
        normalize_forced_raw_bindings(tcx, &mut ptr_kinds, &forced_raw_bindings);

        loop {
            let mut changed = false;
            let (box_input_changed, unsupported_box_input_bindings) =
                downgrade_unsupported_box_inputs(tcx, &mut sig_decs, &local_raw_free_summaries);
            if box_input_changed {
                changed = true;
            }
            if downgrade_unsupported_box_outputs(tcx, &mut sig_decs, &ptr_kinds) {
                changed = true;
            }

            let raw_call_result_bindings =
                collect_raw_call_result_bindings(tcx, &sig_decs, &ptr_kinds);
            let raw_local_assignment_bindings =
                collect_raw_local_assignment_bindings(tcx, &ptr_kinds);
            let unsupported_box_target_bindings =
                collect_unsupported_box_target_bindings(tcx, &sig_decs, &ptr_kinds);
            let unsupported_box_usage_subreasons = collect_unsupported_box_usage_subreasons(
                tcx,
                &ptr_kinds,
                &free_like_wrappers,
                &local_raw_param_summaries,
            );
            let unsupported_box_usage_bindings = collect_unsupported_box_usage_bindings(
                tcx,
                &ptr_kinds,
                &free_like_wrappers,
                &local_raw_param_summaries,
            );

            let mut record_new = |bindings: &FxHashSet<HirId>, reason: &'static str| {
                for hir_id in bindings {
                    if !forced_raw_bindings.contains(hir_id) {
                        reason_map.entry(*hir_id).or_default().push(reason);
                    }
                }
            };
            record_new(&unsupported_box_input_bindings, "unsupported_box_input");
            record_new(&raw_call_result_bindings, "raw_call_result");
            record_new(&raw_local_assignment_bindings, "raw_local_assignment");
            record_new(&unsupported_box_target_bindings, "unsupported_box_target");
            record_new(&unsupported_box_usage_bindings, "unsupported_box_usage");
            for hir_id in &unsupported_box_usage_bindings {
                if forced_raw_bindings.contains(hir_id) {
                    continue;
                }
                let entry = usage_subreason_map.entry(*hir_id).or_default();
                for subreason in unsupported_box_usage_subreasons
                    .get(hir_id)
                    .into_iter()
                    .flatten()
                    .copied()
                {
                    if !entry.contains(&subreason) {
                        entry.push(subreason);
                    }
                }
            }

            let old_len = forced_raw_bindings.len();
            forced_raw_bindings.extend(unsupported_box_input_bindings);
            forced_raw_bindings.extend(raw_call_result_bindings);
            forced_raw_bindings.extend(raw_local_assignment_bindings);
            forced_raw_bindings.extend(unsupported_box_target_bindings);
            forced_raw_bindings.extend(unsupported_box_usage_bindings);
            if forced_raw_bindings.len() != old_len {
                changed = true;
                normalize_forced_raw_bindings(tcx, &mut ptr_kinds, &forced_raw_bindings);
            }

            if !changed {
                break;
            }
        }

        (sig_decs, ptr_kinds, reason_map, usage_subreason_map)
    }

    #[test]
    #[ignore = "expensive B02 pointer translation compile gate"]
    fn b02_corpus_pointer_translation_compile_gate() {
        let records = run_b02_pointer_compile_gate("crat-b02-pointer-compile-gate");
        assert!(!records.is_empty(), "expected at least one B02 project");

        let failures = records
            .iter()
            .filter(|record| !(record.crat_ok && record.cargo_check_ok))
            .collect::<Vec<_>>();

        eprintln!(
            "B02 pointer compile gate across {} projects:",
            records.len()
        );
        for record in &records {
            eprintln!(
                "{}: crat={} cargo_check={} translated_dir={}",
                record.project,
                record.crat_ok,
                record.cargo_check_ok,
                record.translated_dir.display(),
            );
            if let Some(failure_output) = &record.failure_output {
                eprintln!("  failure tail:\n{failure_output}");
            }
        }
        eprintln!(
            "Totals: passed={} failed={}",
            records.len() - failures.len(),
            failures.len(),
        );

        assert!(
            failures.is_empty(),
            "pointer translation compile gate failed for:\n{}",
            failures
                .iter()
                .map(|record| record.project.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    fn collect_unsupported_box_usage_subreasons(
        tcx: TyCtxt<'_>,
        ptr_kinds: &FxHashMap<HirId, PtrKind>,
        free_like_wrappers: &FxHashSet<LocalDefId>,
        local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
    ) -> FxHashMap<HirId, Vec<&'static str>> {
        struct UsageSubreasonVisitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
            free_like_wrappers: &'a FxHashSet<LocalDefId>,
            local_raw_param_summaries: &'a FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
            byte_view_roots: FxHashMap<HirId, HirId>,
            reasons: FxHashMap<HirId, FxHashSet<&'static str>>,
        }

        impl<'tcx> UsageSubreasonVisitor<'_, 'tcx> {
            fn record(&mut self, root: HirId, reason: &'static str) {
                self.reasons.entry(root).or_default().insert(reason);
            }

            fn owning_root_of(&self, hir_id: HirId) -> Option<HirId> {
                if matches!(
                    self.ptr_kinds.get(&hir_id),
                    Some(PtrKind::OptBox | PtrKind::OptBoxedSlice)
                ) {
                    Some(hir_id)
                } else {
                    self.byte_view_roots.get(&hir_id).copied()
                }
            }

            fn maybe_mark_byte_view_alias(
                &mut self,
                lhs_hir_id: HirId,
                lhs_ty: ty::Ty<'tcx>,
                rhs: &'tcx hir::Expr<'tcx>,
            ) {
                let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                    return;
                };
                if !ty_is_byte_sized_raw_inner(lhs_inner_ty) {
                    return;
                }
                let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) else {
                    return;
                };
                let Some(root) = self.owning_root_of(rhs_hir_id) else {
                    return;
                };
                let rhs_ty = self.tcx.typeck(rhs_hir_id.owner).node_type(rhs_hir_id);
                let Some((rhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(rhs_ty) else {
                    return;
                };
                if !ty_is_byte_sized_raw_inner(rhs_inner_ty)
                    || !hir_is_casted_local(rhs, rhs_hir_id)
                {
                    return;
                }
                self.byte_view_roots.insert(lhs_hir_id, root);
                self.record(root, "byte_view_alias");
            }
        }

        impl<'tcx> Visitor<'tcx> for UsageSubreasonVisitor<'_, 'tcx> {
            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    && let Some(init) = let_stmt.init
                {
                    let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                    self.maybe_mark_byte_view_alias(hir_id, lhs_ty, init);
                }
                intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let Res::Local(lhs_hir_id) = path.res
                {
                    let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                    self.maybe_mark_byte_view_alias(lhs_hir_id, lhs_ty, rhs);
                }

                if let Some(local_callee) = hir_called_local_fn(self.tcx, expr)
                    && let hir::ExprKind::Call(_, args) = expr.kind
                {
                    for (arg_index, arg) in args.iter().enumerate() {
                        let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                            continue;
                        };
                        let Some(root) = self.owning_root_of(hir_id) else {
                            continue;
                        };
                        if self
                            .local_raw_param_summaries
                            .get(&(local_callee, arg_index))
                            != Some(&LocalRawParamSummary::BorrowOnly)
                        {
                            self.record(root, "local_callee_non_borrow_only");
                        }
                    }
                }

                if let Some((hir_id, _)) =
                    hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                    && let Some(root) = self.owning_root_of(hir_id)
                {
                    self.record(root, "free_like_wrapper");
                }

                intravisit::walk_expr(self, expr);
            }
        }

        let mut visitor = UsageSubreasonVisitor {
            tcx,
            ptr_kinds,
            free_like_wrappers,
            local_raw_param_summaries,
            byte_view_roots: FxHashMap::default(),
            reasons: FxHashMap::default(),
        };
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
            visitor.visit_body(tcx.hir_body(body));
        }

        let mut out = FxHashMap::default();
        for (hir_id, reasons) in visitor.reasons {
            let mut reasons = reasons.into_iter().collect::<Vec<_>>();
            reasons.sort();
            out.insert(hir_id, reasons);
        }
        out
    }

    #[test]
    #[ignore = "diagnostic B02 ownership-only allocator census"]
    fn b02_corpus_allocator_ownership_census() {
        let root = b02_root();
        let projects = b02_project_dirs(&root);
        assert!(
            !projects.is_empty(),
            "expected B02 projects under `{}`",
            root.display()
        );

        let mut unique_owning_bindings = FxHashSet::default();
        let mut total_owning_sites = 0usize;
        let mut initial_counts = PtrKindCounts::default();
        let mut final_counts = PtrKindCounts::default();
        let mut downgrade_reasons = DowngradeReasonCounts::default();
        let mut immediate_raw_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
        let mut scalar_root_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
        let mut later_reason_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
        let mut authoritative_downgrade_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
        let mut unsupported_usage_subreason_buckets: BTreeMap<&'static str, Bucket> =
            BTreeMap::new();
        let mut unsupported_usage_multi_reason_roots = 0usize;

        for project_dir in projects {
            let rel_project = project_dir
                .strip_prefix(&root)
                .unwrap_or(project_dir.as_path())
                .display()
                .to_string();
            let lib_rel = ::utils::find_lib_path(&project_dir).unwrap();
            let lib_path = project_dir.join(lib_rel);
            ::utils::compilation::run_compiler_on_path(&lib_path, |tcx| {
                let (input, analysis) = build_analysis(tcx);
                let ownership_schemes = analysis
                    .ownership_schemes
                    .as_ref()
                    .expect("ownership analysis should succeed for B02 census");
                let initial_ptr_kinds = collect_diffs(&input, &analysis);
                let (_sig_decs, final_ptr_kinds, reason_map, usage_subreason_map) =
                    simulate_transform_reasons(tcx, &input, &analysis);

                for did in &input.functions {
                    let hir_to_mir = utils::ir::map_thir_to_mir(*did, false, tcx);
                    let fn_results = ownership_schemes.fn_results(&did.to_def_id());
                    let body = tcx.mir_drops_elaborated_and_const_checked(*did).borrow();
                    for site in collect_direct_allocator_sites(tcx, *did) {
                        let Some(&local) = hir_to_mir.binding_to_local.get(&site.hir_id) else {
                            continue;
                        };
                        let is_owning = fn_results
                            .local_result(local)
                            .first()
                            .is_some_and(crate::analyses::ownership::Ownership::is_owning);
                        if !is_owning {
                            continue;
                        }

                        total_owning_sites += 1;
                        let key = BindingKey {
                            owner: site.hir_id.owner.def_id,
                            hir_id: site.hir_id,
                        };
                        if !unique_owning_bindings.insert(key) {
                            continue;
                        }

                        let initial_kind = initial_ptr_kinds.get(&site.hir_id).copied();
                        let final_kind = final_ptr_kinds.get(&site.hir_id).copied();
                        initial_counts.bump(initial_kind);
                        final_counts.bump(final_kind);
                        let example = site_example(&rel_project, &site);

                        match initial_kind {
                            Some(PtrKind::Raw(_)) => {
                                let reason = classify_initial_raw_reason(
                                    &analysis,
                                    *did,
                                    local,
                                    &body.local_decls[local],
                                    tcx,
                                );
                                push_bucket(&mut immediate_raw_buckets, reason, example.clone());
                            }
                            Some(PtrKind::OptBox) if final_kind != Some(PtrKind::OptBox) => {
                                let reason =
                                    site.scalar_rejection_hint.unwrap_or("other_scalar_root");
                                push_bucket(&mut scalar_root_buckets, reason, example.clone());
                            }
                            Some(PtrKind::OptBoxedSlice)
                                if final_kind != Some(PtrKind::OptBoxedSlice) =>
                            {
                                let reason = reason_map
                                    .get(&site.hir_id)
                                    .and_then(|reasons| {
                                        reasons
                                            .iter()
                                            .copied()
                                            .find(|reason| *reason != "unsupported_allocator_root")
                                    })
                                    .unwrap_or("other_late_compatibility");
                                push_bucket(&mut later_reason_buckets, reason, example.clone());
                            }
                            _ => {}
                        }

                        if matches!(initial_kind, Some(PtrKind::OptBox | PtrKind::OptBoxedSlice))
                            && !matches!(final_kind, Some(PtrKind::OptBox | PtrKind::OptBoxedSlice))
                        {
                            let reason = reason_map
                                .get(&site.hir_id)
                                .and_then(|reasons| reasons.first().copied())
                                .unwrap_or("other");
                            push_bucket(
                                &mut authoritative_downgrade_buckets,
                                reason,
                                example.clone(),
                            );
                            if reason == "unsupported_box_usage" {
                                let subreasons = usage_subreason_map
                                    .get(&site.hir_id)
                                    .cloned()
                                    .unwrap_or_else(|| vec!["unknown_usage"]);
                                if subreasons.len() > 1 {
                                    unsupported_usage_multi_reason_roots += 1;
                                }
                                for subreason in subreasons {
                                    push_bucket(
                                        &mut unsupported_usage_subreason_buckets,
                                        subreason,
                                        example.clone(),
                                    );
                                }
                            }
                            match reason {
                                "unsupported_allocator_root" => {
                                    downgrade_reasons.unsupported_allocator_root += 1
                                }
                                "raw_call_result" => downgrade_reasons.raw_call_result += 1,
                                "raw_local_assignment" => {
                                    downgrade_reasons.raw_local_assignment += 1
                                }
                                "unsupported_box_target" => {
                                    downgrade_reasons.unsupported_target += 1
                                }
                                "unsupported_box_usage" => downgrade_reasons.unsupported_usage += 1,
                                _ => downgrade_reasons.other += 1,
                            }
                        }
                    }
                }
            })
            .unwrap();
        }

        eprintln!("B02 ownership-only direct malloc/calloc census:");
        eprintln!("owning allocator assignment sites={total_owning_sites}");
        eprintln!(
            "unique owning allocator bindings={}",
            unique_owning_bindings.len()
        );
        eprintln!(
            "initial decisions: OptBox={}, OptBoxedSlice={}, Raw={}, OptRef={}, Slice={}, SliceCursor={}, None={}",
            initial_counts.opt_box,
            initial_counts.opt_boxed_slice,
            initial_counts.raw,
            initial_counts.opt_ref,
            initial_counts.slice,
            initial_counts.slice_cursor,
            initial_counts.none,
        );
        eprintln!(
            "final decisions: OptBox={}, OptBoxedSlice={}, Raw={}, OptRef={}, Slice={}, SliceCursor={}, None={}",
            final_counts.opt_box,
            final_counts.opt_boxed_slice,
            final_counts.raw,
            final_counts.opt_ref,
            final_counts.slice,
            final_counts.slice_cursor,
            final_counts.none,
        );
        eprintln!(
            "downgraded initially-box bindings: unsupported_allocator_root={}, raw_call_result={}, raw_local_assignment={}, unsupported_target={}, unsupported_usage={}, other={}",
            downgrade_reasons.unsupported_allocator_root,
            downgrade_reasons.raw_call_result,
            downgrade_reasons.raw_local_assignment,
            downgrade_reasons.unsupported_target,
            downgrade_reasons.unsupported_usage,
            downgrade_reasons.other,
        );
        eprintln!("decisionmaker_immediate_raw_breakdown_begin");
        for (reason, bucket) in &immediate_raw_buckets {
            eprintln!("decisionmaker_raw::{reason}={}", bucket.count);
            for example in &bucket.examples {
                eprintln!("  example: {example}");
            }
        }
        eprintln!("decisionmaker_immediate_raw_breakdown_end");
        eprintln!("scalar_allocator_root_breakdown_begin");
        for (reason, bucket) in &scalar_root_buckets {
            eprintln!("scalar_root::{reason}={}", bucket.count);
            for example in &bucket.examples {
                eprintln!("  example: {example}");
            }
        }
        eprintln!("scalar_allocator_root_breakdown_end");
        eprintln!("later_compatibility_breakdown_begin");
        for (reason, bucket) in &later_reason_buckets {
            eprintln!("later::{reason}={}", bucket.count);
            for example in &bucket.examples {
                eprintln!("  example: {example}");
            }
        }
        eprintln!("later_compatibility_breakdown_end");
        eprintln!("authoritative_downgrade_breakdown_begin");
        for (reason, bucket) in &authoritative_downgrade_buckets {
            eprintln!("authoritative::{reason}={}", bucket.count);
            for example in &bucket.examples {
                eprintln!("  example: {example}");
            }
        }
        eprintln!("authoritative_downgrade_breakdown_end");
        eprintln!("unsupported_usage_subreason_breakdown_begin");
        eprintln!("unsupported_usage::multi_reason_roots={unsupported_usage_multi_reason_roots}");
        for (reason, bucket) in &unsupported_usage_subreason_buckets {
            eprintln!("unsupported_usage::{reason}={}", bucket.count);
            for example in &bucket.examples {
                eprintln!("  example: {example}");
            }
        }
        eprintln!("unsupported_usage_subreason_breakdown_end");

        assert!(
            !unique_owning_bindings.is_empty(),
            "expected at least one owning malloc/calloc binding in B02",
        );
    }

    fn fmt_split_counts(counts: SplitKindCounts) -> String {
        format!(
            "scalar={} array={} total={}",
            counts.scalar,
            counts.array,
            counts.total()
        )
    }

    #[test]
    #[ignore = "diagnostic B02 pointer safety before/after stats"]
    fn b02_corpus_pointer_safety_before_after_stats() {
        let root = b02_root();
        let projects = b02_project_dirs(&root);
        assert!(
            !projects.is_empty(),
            "expected B02 projects under `{}`",
            root.display()
        );

        let mut totals_before = SafetyBeforeStats::default();
        let mut totals_before_outermost = SafetyBeforeStats::default();
        let mut totals_after = RewrittenUnsafeStats::default();
        let mut totals_safe_boxes = SplitKindCounts::default();
        let mut reason_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
        let mut usage_subreason_buckets: BTreeMap<&'static str, Bucket> = BTreeMap::new();
        let mut project_records = Vec::with_capacity(projects.len());

        for project_dir in projects {
            let rel_project = project_dir
                .strip_prefix(&root)
                .unwrap_or(project_dir.as_path())
                .display()
                .to_string();
            let lib_rel = ::utils::find_lib_path(&project_dir).unwrap_or_else(|err| {
                panic!("failed to locate lib path for `{rel_project}`: {err}")
            });
            let lib_path = project_dir.join(&lib_rel);

            let analysis = ::utils::compilation::run_compiler_on_path(&lib_path, |tcx| {
                analyze_pointer_safety_for_program(tcx, &rel_project)
            })
            .unwrap_or_else(|_| panic!("failed to analyze `{}`", lib_path.display()));
            let tracked_bindings = tracked_binding_specs_from_sites(&analysis.tracked_sites);
            let (rewritten, _) = ::utils::compilation::run_compiler_on_path(&lib_path, |tcx| {
                replace_local_borrows(&Config::default(), tcx)
            })
            .unwrap_or_else(|_| panic!("failed to rewrite `{}`", lib_path.display()));
            let mut after = ::utils::compilation::run_compiler_on_str(
                &rewritten,
                |tcx| collect_rewritten_tracked_unsafe_stats(tcx, &tracked_bindings),
            )
            .unwrap_or_else(|_| panic!("failed to compile rewritten `{}`", lib_path.display()));
            after.bridge_calls = bridge_call_counts_from_source(&rewritten);

            totals_before += analysis.before_total;
            totals_before_outermost += analysis.before_outermost;
            totals_after += after;
            totals_safe_boxes += analysis.safe_box_sites;

            for reason_record in &analysis.outermost_reasons {
                push_bucket(
                    &mut reason_buckets,
                    reason_record.reason,
                    reason_record.example.clone(),
                );
                if reason_record.reason == "unsupported_box_usage" {
                    for subreason in &reason_record.usage_subreasons {
                        push_bucket(
                            &mut usage_subreason_buckets,
                            subreason,
                            reason_record.example.clone(),
                        );
                    }
                }
            }

            project_records.push(PointerSafetyProjectRecord {
                project: rel_project,
                before_total: analysis.before_total,
                before_outermost: analysis.before_outermost,
                safe_box_sites: analysis.safe_box_sites,
                after,
            });
        }

        eprintln!(
            "B02 pointer safety before/after stats across {} projects:",
            project_records.len()
        );
        eprintln!("before_total_begin");
        eprintln!(
            "before_total::allocation_sites={}",
            fmt_split_counts(totals_before.allocation_sites)
        );
        eprintln!(
            "before_total::unsafe_dereferences={}",
            fmt_split_counts(totals_before.dereferences)
        );
        eprintln!(
            "before_total::unsafe_frees={}",
            fmt_split_counts(totals_before.frees)
        );
        eprintln!("before_total_end");

        eprintln!("before_outermost_begin");
        eprintln!(
            "before_outermost::allocation_sites={}",
            fmt_split_counts(totals_before_outermost.allocation_sites)
        );
        eprintln!(
            "before_outermost::unsafe_dereferences={}",
            fmt_split_counts(totals_before_outermost.dereferences)
        );
        eprintln!(
            "before_outermost::unsafe_frees={}",
            fmt_split_counts(totals_before_outermost.frees)
        );
        eprintln!("before_outermost_end");

        eprintln!("after_begin");
        eprintln!(
            "after::safe_box_sites={}",
            fmt_split_counts(totals_safe_boxes)
        );
        eprintln!(
            "after::unsafe_dereferences_left_from_tracked_sites={}",
            totals_after.dereferences
        );
        eprintln!(
            "after::unsafe_frees_left_from_tracked_sites={}",
            totals_after.frees
        );
        eprintln!(
            "after::bridge_calls=Box::leak:{} Box::from_raw:{} Box::into_raw:{}",
            totals_after.bridge_calls.leak,
            totals_after.bridge_calls.from_raw,
            totals_after.bridge_calls.into_raw,
        );
        eprintln!("after_end");

        eprintln!("outermost_not_safe_reason_breakdown_begin");
        for (reason, bucket) in &reason_buckets {
            eprintln!("outermost_not_safe::{reason}={}", bucket.count);
            for example in &bucket.examples {
                eprintln!("  example: {example}");
            }
        }
        eprintln!("outermost_not_safe_reason_breakdown_end");

        eprintln!("outermost_not_safe_usage_subreasons_begin");
        for (reason, bucket) in &usage_subreason_buckets {
            eprintln!("outermost_not_safe_usage::{reason}={}", bucket.count);
            for example in &bucket.examples {
                eprintln!("  example: {example}");
            }
        }
        eprintln!("outermost_not_safe_usage_subreasons_end");

        eprintln!("per_project_summary_begin");
        for record in &project_records {
            eprintln!(
                "{}: before_total_alloc={} before_outermost_alloc={} safe_boxes={} after_tracked_raw_deref_left={} after_tracked_raw_free_left={} bridge(leak={},from_raw={},into_raw={})",
                record.project,
                fmt_split_counts(record.before_total.allocation_sites),
                fmt_split_counts(record.before_outermost.allocation_sites),
                fmt_split_counts(record.safe_box_sites),
                record.after.dereferences,
                record.after.frees,
                record.after.bridge_calls.leak,
                record.after.bridge_calls.from_raw,
                record.after.bridge_calls.into_raw,
            );
        }
        eprintln!("per_project_summary_end");

        assert!(
            totals_before.allocation_sites.total() > 0,
            "expected at least one tracked allocation site in B02"
        );
        assert!(
            totals_before_outermost.allocation_sites.total() > 0,
            "expected at least one outermost allocation site in B02"
        );
        assert!(
            totals_safe_boxes.total() <= totals_before_outermost.allocation_sites.total(),
            "safe box sites should not exceed outermost allocation sites"
        );
        for bucket in reason_buckets.values() {
            assert!(
                !bucket.examples.is_empty(),
                "non-empty reason bucket should record an example"
            );
        }
        for bucket in usage_subreason_buckets.values() {
            assert!(
                !bucket.examples.is_empty(),
                "non-empty usage-subreason bucket should record an example"
            );
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

    fn find_local_hir_id(tcx: TyCtxt<'_>, fn_name: &str, local_name: &str) -> HirId {
        tcx.hir_crate(())
            .owners
            .iter()
            .filter_map(|maybe_owner| maybe_owner.as_owner())
            .find_map(|owner| {
                let OwnerNode::Item(item) = owner.node() else {
                    return None;
                };
                let HirItemKind::Fn { body, .. } = item.kind else {
                    return None;
                };
                if tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() != fn_name {
                    return None;
                }
                let body = tcx.hir_body(body);
                let hir::ExprKind::Block(block, _) = body.value.kind else {
                    return None;
                };
                block.stmts.iter().find_map(|stmt| {
                    let hir::StmtKind::Let(let_stmt) = stmt.kind else {
                        return None;
                    };
                    let hir::PatKind::Binding(_, hir_id, ident, _) = let_stmt.pat.kind else {
                        return None;
                    };
                    (ident.name.as_str() == local_name).then_some(hir_id)
                })
            })
            .expect("expected matching local hir id")
    }

    #[test]
    fn pointer_safety_stats_count_scalar_outermost_root_and_safe_box_free_consumption() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_scalar() {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    free(p as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(
            analysis.before_total,
            SafetyBeforeStats {
                allocation_sites: SplitKindCounts { scalar: 1, array: 0 },
                dereferences: SplitKindCounts { scalar: 1, array: 0 },
                frees: SplitKindCounts { scalar: 1, array: 0 },
            }
        );
        assert_eq!(analysis.before_outermost, analysis.before_total);
        assert_eq!(
            analysis.safe_box_sites,
            SplitKindCounts { scalar: 1, array: 0 }
        );
        assert_eq!(after.dereferences, 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls, BridgeCallCounts::default());
    }

    #[test]
    fn pointer_safety_stats_count_array_outermost_root_and_safe_boxed_slice_free_consumption() {
        let code = r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_array() {
    let mut p: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    *p.offset(1) = 7;
    free(p as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(
            analysis.before_total,
            SafetyBeforeStats {
                allocation_sites: SplitKindCounts { scalar: 0, array: 1 },
                dereferences: SplitKindCounts { scalar: 0, array: 1 },
                frees: SplitKindCounts { scalar: 0, array: 1 },
            }
        );
        assert_eq!(analysis.before_outermost, analysis.before_total);
        assert_eq!(
            analysis.safe_box_sites,
            SplitKindCounts { scalar: 0, array: 1 }
        );
        assert_eq!(after.dereferences, 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls, BridgeCallCounts::default());
    }

    #[test]
    fn pointer_safety_stats_mark_allocator_wrapper_principal_local_as_outermost() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    let p: *mut i32 = malloc(std::mem::size_of::<i32>());
    p
}
"#;

        let (analysis, _after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.tracked_sites.len(), 1);
        let site = &analysis.tracked_sites[0];
        assert_eq!(site.shape, SafetySiteShape::AllocatorWrapperPrincipalLocal);
        assert!(site.outermost);
        assert_eq!(analysis.before_total.allocation_sites.total(), 1);
        assert_eq!(analysis.before_outermost.allocation_sites.total(), 1);
    }

    #[test]
    fn pointer_safety_stats_mark_field_stored_root_as_non_outermost() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    let data: *mut i32 = malloc(std::mem::size_of::<i32>());
    (*owner).data = data;
}
"#;

        let (analysis, _after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.tracked_sites.len(), 1);
        let site = &analysis.tracked_sites[0];
        assert_eq!(site.shape, SafetySiteShape::NonOutermostLocalRoot);
        assert!(!site.outermost);
        assert_eq!(analysis.before_total.allocation_sites.total(), 1);
        assert_eq!(analysis.before_outermost.allocation_sites.total(), 0);
    }

    #[test]
    fn pointer_safety_stats_capture_scalar_raw_bridge_calls() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_nested() {
    let mut p: *mut *mut i32 =
        malloc(std::mem::size_of::<*mut i32>()) as *mut *mut i32;
    free(p as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.safe_box_sites.total(), 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls.leak, 0);
        assert_eq!(after.bridge_calls.from_raw, 1);
        assert_eq!(after.bridge_calls.into_raw, 1);
    }

    #[test]
    fn pointer_safety_stats_capture_array_raw_bridge_calls() {
        let code = r#"
extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_chars(len: usize) {
    let buf: *mut core::ffi::c_char =
        realloc(std::ptr::null_mut::<core::ffi::c_void>(), len) as *mut core::ffi::c_char;
    free(buf as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.safe_box_sites.total(), 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls.leak, 1);
        assert_eq!(after.bridge_calls.from_raw, 1);
        assert_eq!(after.bridge_calls.into_raw, 0);
    }

    #[test]
    fn pointer_safety_stats_ignore_untracked_remaining_raw_dereferences() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn mixed(arg: *mut i32) -> i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    *arg
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(
            analysis.before_total,
            SafetyBeforeStats {
                allocation_sites: SplitKindCounts { scalar: 1, array: 0 },
                dereferences: SplitKindCounts { scalar: 1, array: 0 },
                frees: SplitKindCounts::default(),
            }
        );
        assert_eq!(after.dereferences, 0);
    }

    #[test]
    fn wrapper_collector_recognizes_returning_local_after_mutation() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn snprintf(dst: *mut core::ffi::c_char, size: usize, fmt: *const core::ffi::c_char, ...);
}

pub unsafe fn create_msg(v: i32) -> *mut core::ffi::c_char {
    let msg: *mut core::ffi::c_char = malloc(64) as *mut core::ffi::c_char;
    if msg.is_null() {
        return std::ptr::null_mut();
    }
    snprintf(msg, 64, b"value=%d\0" as *const u8 as *const core::ffi::c_char, v);
    msg
}
"#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let wrappers = collect_local_allocator_wrappers(tcx);
            let did = tcx
                .hir_crate(())
                .owners
                .iter()
                .filter_map(|maybe_owner| maybe_owner.as_owner())
                .filter_map(|owner| {
                    let OwnerNode::Item(item) = owner.node() else {
                        return None;
                    };
                    let HirItemKind::Fn { .. } = item.kind else {
                        return None;
                    };
                    (tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == "create_msg")
                        .then_some(item.owner_id.def_id)
                })
                .next()
                .expect("create_msg should exist");
            let names = wrappers
                .keys()
                .map(|def_id| tcx.item_name(def_id.to_def_id()).as_str().to_owned())
                .collect::<Vec<_>>();
            assert!(wrappers.contains_key(&did), "{names:?}");
        })
        .unwrap();
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
                None,
                PtrKind::OptBox,
                struct_ty,
            );
            assert_eq!(kind, Some(PtrKind::OptBox));

            let emitted = pprust::expr_to_string(&materialized);
            assert!(emitted.contains("Some(Box::new("), "{emitted}");
            assert!(!emitted.contains("Box::into_raw("), "{emitted}");
            assert!(emitted.contains("crate::StructDefaultProbe {"), "{emitted}");
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

    #[test]
    fn struct_default_materialization_handles_large_array_fields() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct StructArrayDefaultProbe {
    pub name: [i8; 64],
    pub nodes: [*mut i32; 100],
}

pub unsafe fn alloc_struct() {
    let state: *mut StructArrayDefaultProbe =
        malloc(std::mem::size_of::<crate::StructArrayDefaultProbe>()) as *mut crate::StructArrayDefaultProbe;
    let _ = state;
}
"#;

        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut krate = ::utils::ast::expanded_ast(tcx);
            ::utils::ast::remove_unnecessary_items_from_ast(&mut krate);

            let struct_ty = find_struct_ty(tcx, "StructArrayDefaultProbe");
            let init_expr = find_local_init_expr(&krate, "alloc_struct", "state");
            let mut materialized = init_expr.clone();
            let visitor = synthetic_transform_visitor(tcx);

            let kind = visitor.try_materialize_box_allocator_root(
                &mut materialized,
                init_expr,
                None,
                PtrKind::OptBox,
                struct_ty,
            );
            assert_eq!(kind, Some(PtrKind::OptBox));

            let emitted = pprust::expr_to_string(&materialized);
            assert!(emitted.contains("Some(Box::new("), "{emitted}");
            assert!(!emitted.contains("Box::into_raw("), "{emitted}");
            assert!(emitted.contains("name: std::array::from_fn"), "{emitted}");
            assert!(emitted.contains("nodes: std::array::from_fn"), "{emitted}");
            assert!(emitted.contains("std::ptr::null_mut::<i32>()"), "{emitted}");

            let check_code = format!(
                r#"
#[repr(C)]
pub struct StructArrayDefaultProbe {{
    pub name: [i8; 64],
    pub nodes: [*mut i32; 100],
}}

pub fn check() {{
    let _: Option<Box<crate::StructArrayDefaultProbe>> = {emitted};
}}
"#
            );
            ::utils::compilation::run_compiler_on_str(&check_code, ::utils::type_check)
                .expect(&check_code);
        })
        .unwrap();
    }

    #[test]
    fn struct_default_materialization_handles_union_fields() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub union TypeConfusion {
    pub int_val: i32,
    pub float_val: f32,
}

#[repr(C)]
pub struct UnionHolderProbe {
    pub data: TypeConfusion,
    pub value: i32,
}

pub unsafe fn alloc_struct() {
    let state: *mut UnionHolderProbe =
        malloc(std::mem::size_of::<crate::UnionHolderProbe>()) as *mut crate::UnionHolderProbe;
    let _ = state;
}
"#;

        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut krate = ::utils::ast::expanded_ast(tcx);
            ::utils::ast::remove_unnecessary_items_from_ast(&mut krate);

            let struct_ty = find_struct_ty(tcx, "UnionHolderProbe");
            let init_expr = find_local_init_expr(&krate, "alloc_struct", "state");
            let mut materialized = init_expr.clone();
            let visitor = synthetic_transform_visitor(tcx);

            let kind = visitor.try_materialize_box_allocator_root(
                &mut materialized,
                init_expr,
                None,
                PtrKind::OptBox,
                struct_ty,
            );
            assert_eq!(kind, Some(PtrKind::OptBox));

            let emitted = pprust::expr_to_string(&materialized);
            assert!(emitted.contains("Some(Box::new("), "{emitted}");
            assert!(
                emitted.contains("MaybeUninit::<crate::TypeConfusion>::zeroed().assume_init()"),
                "{emitted}"
            );

            let check_code = format!(
                r#"
#[repr(C)]
pub union TypeConfusion {{
    pub int_val: i32,
    pub float_val: f32,
}}

#[repr(C)]
pub struct UnionHolderProbe {{
    pub data: TypeConfusion,
    pub value: i32,
}}

pub fn check() {{
    let _: Option<Box<crate::UnionHolderProbe>> = {emitted};
}}
"#
            );
            ::utils::compilation::run_compiler_on_str(&check_code, ::utils::type_check)
                .expect(&check_code);
        })
        .unwrap();
    }

    #[test]
    fn boxed_slice_materialization_uses_direct_owning_value() {
        let code = r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
}

pub unsafe fn alloc_arr() {
    let data: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    let _ = data;
}
"#;

        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut krate = ::utils::ast::expanded_ast(tcx);
            ::utils::ast::remove_unnecessary_items_from_ast(&mut krate);

            let init_expr = find_local_init_expr(&krate, "alloc_arr", "data");
            let mut materialized = init_expr.clone();
            let visitor = synthetic_transform_visitor(tcx);

            let kind = visitor.try_materialize_box_allocator_root(
                &mut materialized,
                init_expr,
                None,
                PtrKind::OptBoxedSlice,
                tcx.types.i32,
            );
            assert_eq!(kind, Some(PtrKind::OptBoxedSlice));

            let emitted = pprust::expr_to_string(&materialized);
            assert!(
                emitted.contains("Some(std::iter::repeat_with(||"),
                "{emitted}"
            );
            assert!(
                emitted.contains("collect::<Vec<i32>>().into_boxed_slice()"),
                "{emitted}"
            );
            assert!(!emitted.contains("Box::leak("), "{emitted}");
            assert!(!emitted.contains("Box::into_raw("), "{emitted}");

            let check_code = format!(
                r#"
pub fn check() {{
    let _: Option<Box<[i32]>> = {emitted};
}}
"#
            );
            ::utils::compilation::run_compiler_on_str(&check_code, ::utils::type_check)
                .expect(&check_code);
        })
        .unwrap();
    }

    #[test]
    fn boxed_slice_bindings_are_not_preemptively_downgraded_to_raw() {
        let code = r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
}

pub unsafe fn alloc_arr() {
    let data: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    let _ = data;
}
"#;

        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let hir_id = find_local_hir_id(tcx, "alloc_arr", "data");
            let mut ptr_kinds = FxHashMap::default();
            ptr_kinds.insert(hir_id, PtrKind::OptBoxedSlice);

            let downgraded = downgrade_unsupported_allocator_box_kinds(tcx, &ptr_kinds);
            assert!(!downgraded.contains(&hir_id), "{downgraded:?}");
        })
        .unwrap();
    }
}
