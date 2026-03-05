use std::cell::{Cell, RefCell};

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
use thin_vec::ThinVec;
use utils::{
    ast::{unwrap_cast_and_paren, unwrap_cast_and_paren_mut, unwrap_paren, unwrap_paren_mut},
    ir::{AstToHir, mir_ty_to_string},
};

use super::{
    Analysis,
    collector::collect_diffs,
    decision::{DecisionConflict, PtrKind, SigDecisions, SpecPtrClass},
    stats::{AllocatorReason, AllocatorReasonStats, classify_call240_allocator_source_expr},
};
use crate::utils::rustc::RustProgram;

pub(crate) struct TransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    sig_decs: SigDecisions,
    ptr_kinds: FxHashMap<HirId, PtrKind>,
    ast_to_hir: AstToHir,
    conflicts: RefCell<Vec<DecisionConflict>>,
    allocator_reason_stats: RefCell<AllocatorReasonStats>,
    allocator_reason_seen: RefCell<FxHashSet<String>>,
    enable_box_rewrite: bool,
    raw_mutability: bool,
    pub bytemuck: Cell<bool>,
    pub slice_cursor: Cell<bool>,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item(&mut self, item: &mut Item) {
        let node_id = item.id;
        match &mut item.kind {
            ItemKind::Impl(_) => return,
            ItemKind::Fn(box fn_item) => {
                let def_id = self.ast_to_hir.global_map[&node_id];
                let sig_dec = self.sig_decs.data.get(&def_id).unwrap();
                let fn_sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();

                for ((input_ty, input_dec), param) in fn_sig
                    .inputs()
                    .iter()
                    .copied()
                    .zip(&sig_dec.input_decs)
                    .zip(&mut fn_item.sig.decl.inputs)
                {
                    let Some(input_dec) = *input_dec else { continue };
                    let (inner_ty, orig_m) =
                        unwrap_ptr_from_mir_ty(input_ty).unwrap_or_else(|| {
                            panic!("Expected pointer type, got {ty:?}", ty = input_ty)
                        });
                    let mut mapped_dec = self.normalize_slice_kind(input_dec, inner_ty);
                    if !orig_m.is_mut() {
                        mapped_dec = mapped_dec.with_mut(false);
                    } else if !self.raw_mutability {
                        mapped_dec = mapped_dec.with_mut(orig_m.is_mut());
                    }

                    match mapped_dec {
                        PtrKind::Move(_) => {
                            *param.ty = mk_move_ty(inner_ty, self.tcx);
                            if let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind {
                                binding_mode.1 = Mutability::Mut;
                            }
                        }
                        PtrKind::OptRef(m) => {
                            *param.ty = mk_opt_ref_ty(inner_ty, m, self.tcx);
                            if let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind {
                                binding_mode.1 = Mutability::Mut;
                            }
                        }
                        PtrKind::Slice(m) => {
                            *param.ty = mk_slice_ty(inner_ty, m, self.tcx);
                            if m && let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind {
                                binding_mode.1 = Mutability::Mut;
                            }
                        }
                        PtrKind::Raw(m) => {
                            *param.ty = mk_raw_ptr_ty(inner_ty, m, self.tcx);
                        }
                        PtrKind::SliceCursor(m) => {
                            *param.ty = mk_cursor_ty(inner_ty, m, self.tcx);
                            self.slice_cursor.set(true);
                            if m && let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind {
                                binding_mode.1 = Mutability::Mut;
                            }
                        }
                    }

                    if let Some(hir_param) = self.ast_to_hir.get_param(param.id, self.tcx)
                        && let hir::PatKind::Binding(_, hir_id, _, _) = hir_param.pat.kind
                    {
                        self.ptr_kinds.insert(hir_id, mapped_dec);
                    }
                }

                if let Some(output_dec) = sig_dec.output_dec {
                    let output_ty = fn_sig.output();
                    if let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(output_ty)
                        && let FnRetTy::Ty(ret_ty) = &mut fn_item.sig.decl.output
                    {
                        let mut output_dec = output_dec;
                        if let Some((_, orig_m)) = unwrap_ptr_from_mir_ty(output_ty) {
                            if !orig_m.is_mut() {
                                output_dec = output_dec.with_mut(false);
                            } else if !self.raw_mutability {
                                output_dec = output_dec.with_mut(orig_m.is_mut());
                            }
                        }

                        *ret_ty = P(match output_dec {
                            PtrKind::Move(_) => mk_move_ty(inner_ty, self.tcx),
                            PtrKind::Raw(m) => mk_raw_ptr_ty(inner_ty, m, self.tcx),
                            _ => (**ret_ty).clone(),
                        });

                        if let Some(body) = fn_item.body.as_mut()
                            && let Some(last_stmt) = body.stmts.last_mut()
                            && let StmtKind::Expr(tail_expr) = &mut last_stmt.kind
                            && !matches!(tail_expr.kind, ExprKind::Ret(_))
                            && let Some(hir_tail_expr) =
                                self.ast_to_hir.get_expr(tail_expr.id, self.tcx)
                        {
                            self.transform_rhs(tail_expr.as_mut(), hir_tail_expr, output_dec);
                        }
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
            && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
        {
            let typeck = self.tcx.typeck(hir_id.owner);
            let lhs_ty = typeck.node_type(hir_id);
            let Some((lhs_inner_ty, orig_m)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            let mut lhs_kind = self.ptr_kinds.get(&hir_id).copied();
            if let LocalKind::Init(box rhs) | LocalKind::InitElse(box rhs, _) = &local.kind {
                let rhs_source = unwrap_addr_of_deref(unwrap_cast_and_paren(rhs));
                if self.can_force_call240_move(hir_id, rhs_source)
                    && matches!(lhs_kind, None | Some(PtrKind::Raw(_)))
                {
                    lhs_kind = Some(PtrKind::Move(orig_m.is_mut()));
                }
            }
            let Some(mut lhs_kind) = lhs_kind else {
                if let LocalKind::Init(box rhs) | LocalKind::InitElse(box rhs, _) = &local.kind {
                    let rhs_source = unwrap_addr_of_deref(unwrap_cast_and_paren(rhs));
                    if let Some(allocator) = classify_call240_allocator_source_expr(rhs_source)
                        && let Some(hir_rhs) = let_stmt.init
                    {
                        self.record_allocator_reason(
                            hir_rhs,
                            allocator,
                            AllocatorReason::Call250NonMoveRequired,
                        );
                    }
                }
                return;
            };
            lhs_kind = self.normalize_slice_kind(lhs_kind, lhs_inner_ty);
            if !orig_m.is_mut() {
                lhs_kind = lhs_kind.with_mut(false);
            } else if !self.raw_mutability {
                lhs_kind = lhs_kind.with_mut(orig_m.is_mut());
            }
            self.ptr_kinds.insert(hir_id, lhs_kind);

            match lhs_kind {
                PtrKind::Move(_) => {
                    local.ty = Some(P(mk_move_ty(lhs_inner_ty, self.tcx)));
                }
                PtrKind::OptRef(m) => {
                    local.ty = Some(P(mk_opt_ref_ty(lhs_inner_ty, m, self.tcx)));
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

            if matches!(
                lhs_kind,
                PtrKind::Move(_)
                    | PtrKind::OptRef(_)
                    | PtrKind::Slice(true)
                    | PtrKind::SliceCursor(true)
            ) && let PatKind::Ident(binding_mode, ..) = &mut local.pat.kind
            {
                // Rewritten mutable pointer forms use mutable receiver methods.
                binding_mode.1 = Mutability::Mut;
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
                let lhs_kind = if let ExprKind::Path(_, _) = lhs.kind
                    && let Some(hir_id) = self.hir_id_of_path(lhs.id)
                {
                    self.ptr_kinds
                        .get(&hir_id)
                        .copied()
                        .unwrap_or(PtrKind::Raw(m.is_mut()))
                } else {
                    PtrKind::Raw(m.is_mut())
                };

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
                        self.transform_rhs(rhs, hir_rhs, lhs_kind);
                    }
                    PtrKind::Slice(_) | PtrKind::OptRef(_) | PtrKind::Raw(_) | PtrKind::Move(_) => {
                        self.transform_rhs(rhs, hir_rhs, lhs_kind);
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

                // Null-style comparisons on rewritten non-raw pointers become
                // `is_none` / `is_empty` checks.
                if matches!(bin_op.node, BinOpKind::Eq | BinOpKind::Ne) {
                    let is_eq = matches!(bin_op.node, BinOpKind::Eq);
                    let replacement = {
                        let l_is_zero = is_zero_literal_expr(l);
                        let r_is_zero = is_zero_literal_expr(r);
                        if l_is_zero {
                            self.non_raw_null_cmp_rewrite(r, is_eq)
                        } else if r_is_zero {
                            self.non_raw_null_cmp_rewrite(l, is_eq)
                        } else {
                            None
                        }
                    };
                    if let Some(new_expr) = replacement {
                        *expr = new_expr;
                        return;
                    }
                }

                let ty = typeck.expr_ty(hir_l);
                if let Some((_, m)) = unwrap_ptr_from_mir_ty(ty) {
                    let kind = PtrKind::Raw(m.is_mut());
                    self.transform_rhs(l, hir_l, kind);
                    self.transform_rhs(r, hir_r, kind);
                }
            }
            ExprKind::Call(_, args) => {
                let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) else {
                    return;
                };
                let hir::ExprKind::Call(func, hargs) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                if self.is_free_call(func) {
                    let rewritten = {
                        let Some((arg, harg)) = args.iter_mut().zip(hargs.iter()).next() else {
                            return;
                        };
                        let move_arg = self
                            .local_hir_id_from_expr(harg)
                            .and_then(|hir_id| self.ptr_kinds.get(&hir_id).copied())
                            .is_some_and(|kind| matches!(kind, PtrKind::Move(_)));
                        if move_arg {
                            let drop_target = unwrap_addr_of_deref(unwrap_cast_and_paren(arg));
                            Some(utils::expr!("drop({})", pprust::expr_to_string(drop_target)))
                        } else {
                            self.transform_rhs(arg, harg, PtrKind::Raw(true));
                            None
                        }
                    };
                    if let Some(rewritten) = rewritten {
                        *expr = rewritten;
                    }
                    return;
                }
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
                    let param_kind = match param_kind {
                        PtrKind::Move(_) => PtrKind::Raw(m.is_mut()),
                        other => other,
                    };
                    let param_kind = if !m.is_mut() {
                        param_kind.with_mut(false)
                    } else if self.raw_mutability {
                        param_kind
                    } else {
                        param_kind.with_mut(m.is_mut())
                    };
                    let (inner_ty, _) = some_or!(unwrap_ptr_from_mir_ty(ty), continue);
                    let param_kind = self.normalize_slice_kind(param_kind, inner_ty);

                    self.transform_rhs(arg, harg, param_kind);
                }

                hoist_opt_ref_borrow(expr);
                hoist_mut_call_arg_conflicts(expr);
            }
            ExprKind::MethodCall(box MethodCall { seg, receiver, .. })
                if seg.ident.name.as_str() == "is_null" =>
            {
                if matches!(receiver.kind, ExprKind::Path(_, _))
                    && let Some(hir_id) = self.hir_id_of_path(receiver.id)
                    && let Some(ptr_kind) = self.ptr_kinds.get(&hir_id)
                {
                    match ptr_kind {
                        PtrKind::Move(_) | PtrKind::OptRef(_) => {
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
            }) if seg.ident.name.as_str() == "offset_from" => {
                let hir_receiver = self.ast_to_hir.get_expr(receiver.id, self.tcx).unwrap();
                let typeck = self.tcx.typeck(hir_receiver.hir_id.owner);
                let recv_mut = unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(hir_receiver))
                    .map(|(_, m)| m.is_mut())
                    .unwrap_or(true);
                self.transform_ptr(receiver, hir_receiver, PtrCtx::Rhs(PtrKind::Raw(recv_mut)));
                let [arg] = &mut args[..] else { panic!() };
                let hir_arg = self.ast_to_hir.get_expr(arg.id, self.tcx).unwrap();
                let arg_mut = unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(hir_arg))
                    .map(|(_, m)| m.is_mut())
                    .unwrap_or(true);
                self.transform_ptr(arg, hir_arg, PtrCtx::Rhs(PtrKind::Raw(arg_mut)));
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
                    let owner_did = hir_ret.hir_id.owner.def_id;
                    let mut kind = self
                        .sig_decs
                        .data
                        .get(&owner_did)
                        .and_then(|sd| sd.output_dec)
                        .unwrap_or(PtrKind::Raw(m.is_mut()));
                    if !m.is_mut() {
                        kind = kind.with_mut(false);
                    } else if !self.raw_mutability {
                        kind = kind.with_mut(m.is_mut());
                    }
                    self.transform_rhs(ret, hir_ret, kind);
                }
            }
            ExprKind::Unary(UnOp::Deref, e) => {
                let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) else {
                    return;
                };
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
                        && matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::SliceCursor(_)))
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
                            PtrKind::Move(_) | PtrKind::OptRef(_) => {
                                **e = utils::expr!("{}.unwrap()", pprust::expr_to_string(e));
                            }
                            PtrKind::Slice(_) => {
                                let e_no_cast = unwrap_cast_and_paren(e);
                                if let ExprKind::AddrOf(BorrowKind::Ref, _, inner) = &e_no_cast.kind
                                    && {
                                        let inner_unparen = unwrap_paren(inner);
                                        !(matches!(inner_unparen.kind, ExprKind::Path(_, _))
                                            && self.hir_id_of_path(inner_unparen.id).is_none())
                                    }
                                    && !is_range_index_expr(unwrap_paren(inner))
                                    && !self
                                        .hir_id_of_path(unwrap_paren(inner).id)
                                        .and_then(|hir_id| self.ptr_kinds.get(&hir_id).copied())
                                        .is_some_and(|k| {
                                            matches!(k, PtrKind::Slice(_) | PtrKind::SliceCursor(_))
                                        })
                                {
                                    // `*(&mut x)` / `*(&x)` => `x`
                                    *expr = (*unwrap_paren(inner)).clone();
                                } else {
                                    *expr = utils::expr!("({})[0]", pprust::expr_to_string(e));
                                }
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

impl<'tcx> TransformVisitor<'tcx> {
    pub fn new(
        rust_program: &RustProgram<'tcx>,
        analysis: &Analysis,
        ast_to_hir: AstToHir,
    ) -> TransformVisitor<'tcx> {
        let sig_decs = SigDecisions::new(rust_program, analysis); // TODO: Move outside
        let mut conflicts = sig_decs.conflicts.clone();
        let collect_result = collect_diffs(rust_program, analysis); // TODO: Move outside
        conflicts.extend(collect_result.conflicts);

        TransformVisitor {
            tcx: rust_program.tcx,
            sig_decs,
            ptr_kinds: collect_result.ptr_kinds,
            ast_to_hir,
            conflicts: RefCell::new(conflicts),
            allocator_reason_stats: RefCell::new(AllocatorReasonStats::default()),
            allocator_reason_seen: RefCell::new(FxHashSet::default()),
            enable_box_rewrite: analysis.enable_box_rewrite,
            raw_mutability: analysis.raw_mutability,
            bytemuck: Cell::new(false),
            slice_cursor: Cell::new(false),
        }
    }

    pub fn take_conflicts(&mut self) -> Vec<DecisionConflict> {
        std::mem::take(&mut *self.conflicts.borrow_mut())
    }

    pub fn take_allocator_reason_stats(&mut self) -> AllocatorReasonStats {
        std::mem::take(&mut *self.allocator_reason_stats.borrow_mut())
    }

    pub fn synthesize_ty140_defaults(&mut self, krate: &mut Crate, enabled: bool) {
        if !enabled {
            return;
        }
        self.synthesize_ty140_in_items(&mut krate.items);
    }

    fn call240_site(&self, hir_expr: &hir::Expr<'tcx>) -> String {
        let file = self
            .tcx
            .sess
            .source_map()
            .span_to_filename(hir_expr.span)
            .prefer_local()
            .to_string();
        let file = file.rsplit(['/', '\\']).next().unwrap_or(&file).to_owned();
        let line = self
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(hir_expr.span.lo())
            .line;
        let fn_path = self
            .tcx
            .def_path_str(hir_expr.hir_id.owner.def_id.to_def_id());
        format!(
            "{}|{}|hir{:?}|line{}",
            file, fn_path, hir_expr.hir_id.local_id, line
        )
    }

    fn item_site(&self, item: &Item) -> String {
        let file = self
            .tcx
            .sess
            .source_map()
            .span_to_filename(item.span)
            .prefer_local()
            .to_string();
        let file = file.rsplit(['/', '\\']).next().unwrap_or(&file).to_owned();
        let line = self
            .tcx
            .sess
            .source_map()
            .lookup_char_pos(item.span.lo())
            .line;
        let item_path = self
            .ast_to_hir
            .global_map
            .get(&item.id)
            .map(|did| self.tcx.def_path_str(did.to_def_id()))
            .unwrap_or_else(|| "<unmapped-item>".to_owned());
        format!("{}|{}|item{:?}|line{}", file, item_path, item.id, line)
    }

    fn record_allocator_reason(
        &self,
        hir_expr: &hir::Expr<'tcx>,
        allocator: &'static str,
        reason: AllocatorReason,
    ) {
        let key = format!(
            "{}|{}|{}",
            reason.key(),
            allocator,
            self.call240_site(hir_expr)
        );
        if self.allocator_reason_seen.borrow_mut().insert(key) {
            self.allocator_reason_stats
                .borrow_mut()
                .record(reason, allocator);
        }
    }

    fn push_ty140_skip_conflict(&self, item: &Item, note: String) {
        self.conflicts.borrow_mut().push(DecisionConflict {
            rule_id: "TY-140",
            site: self.item_site(item),
            legacy_decision: SpecPtrClass::RawConst,
            spec_decision: SpecPtrClass::Move,
            chosen: SpecPtrClass::RawConst,
            note,
        });
    }

    fn is_low_risk_default_type_for_call240(&self, ty: ty::Ty<'tcx>) -> bool {
        match ty.kind() {
            ty::TyKind::Bool
            | ty::TyKind::Char
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Float(_)
            | ty::TyKind::RawPtr(..)
            | ty::TyKind::Ref(..)
            | ty::TyKind::FnPtr(..) => true,
            ty::TyKind::Array(elem, _) => self.is_low_risk_default_type_for_call240(*elem),
            ty::TyKind::Tuple(elems) => elems
                .iter()
                .all(|elem| self.is_low_risk_default_type_for_call240(elem)),
            _ => false,
        }
    }

    fn synthesize_ty140_in_items(&self, items: &mut ThinVec<P<Item>>) {
        for item in items.iter_mut() {
            if let ItemKind::Mod(_, _, ModKind::Loaded(inner, _, _, _)) = &mut item.kind {
                self.synthesize_ty140_in_items(inner);
            }
        }

        let mut existing_default_impls: FxHashSet<String> = FxHashSet::default();
        for item in items.iter() {
            let ItemKind::Impl(box Impl {
                of_trait: Some(of_trait),
                self_ty,
                ..
            }) = &item.kind
            else {
                continue;
            };
            if !Self::trait_ref_is_default(&of_trait) {
                continue;
            }
            let Some(self_name) = Self::self_ty_name(&self_ty) else {
                continue;
            };
            existing_default_impls.insert(self_name);
        }

        let mut impls_to_append = Vec::new();
        for item in items.iter() {
            let ItemKind::Struct(ident, generics, data) = &item.kind else {
                continue;
            };

            let struct_name = ident.name.as_str().to_owned();
            if existing_default_impls.contains(&struct_name) || Self::has_derive_default(item) {
                continue;
            }
            if !generics.params.is_empty() {
                self.push_ty140_skip_conflict(
                    item,
                    format!(
                        "TY-140 default synthesis skipped for generic struct `{}` (non-generic scope in this patch).",
                        struct_name
                    ),
                );
                continue;
            }
            if let Some(reason) = self.ty140_unsupported_struct_reason(item) {
                self.push_ty140_skip_conflict(item, reason);
                continue;
            }

            let Some(default_body) = Self::ty140_default_body(&data) else {
                self.push_ty140_skip_conflict(
                    item,
                    format!(
                        "TY-140 default synthesis skipped for unsupported struct shape `{}`.",
                        struct_name
                    ),
                );
                continue;
            };

            let impl_item = utils::item!(
                "impl Default for {} {{ fn default() -> Self {{ {} }} }}",
                struct_name,
                default_body
            );
            existing_default_impls.insert(struct_name);
            impls_to_append.push(P(impl_item));
        }

        items.extend(impls_to_append);
    }

    fn trait_ref_is_default(trait_ref: &TraitRef) -> bool {
        trait_ref
            .path
            .segments
            .last()
            .is_some_and(|seg| seg.ident.name.as_str() == "Default")
    }

    fn self_ty_name(ty: &Ty) -> Option<String> {
        let TyKind::Path(None, path) = &ty.kind else {
            return None;
        };
        Some(path.segments.last()?.ident.name.as_str().to_owned())
    }

    fn has_derive_default(item: &Item) -> bool {
        let item_text = pprust::item_to_string(item);
        item_text.contains("derive") && item_text.contains("Default")
    }

    fn ty140_unsupported_struct_reason(&self, item: &Item) -> Option<String> {
        let ItemKind::Struct(ident, _, _) = &item.kind else {
            return None;
        };
        let def_id = self.ast_to_hir.global_map.get(&item.id)?;
        let adt_def = self.tcx.adt_def(def_id.to_def_id());
        for field in adt_def.non_enum_variant().fields.iter() {
            let field_ty = self.tcx.type_of(field.did).instantiate_identity();
            if let Some(reason) = Self::ty140_unsupported_field_kind(field_ty) {
                return Some(format!(
                    "TY-140 default synthesis skipped for `{}`: field `{}` is unsupported ({}).",
                    ident.name.as_str(),
                    field.name,
                    reason
                ));
            }
        }
        None
    }

    fn ty140_unsupported_field_kind(ty: ty::Ty<'tcx>) -> Option<&'static str> {
        match ty.kind() {
            ty::TyKind::Adt(adt, _) => {
                if adt.is_union() {
                    Some("union field type")
                } else {
                    None
                }
            }
            ty::TyKind::RawPtr(inner_ty, _) => {
                if matches!(
                    inner_ty.kind(),
                    ty::TyKind::Foreign(..)
                        | ty::TyKind::Slice(..)
                        | ty::TyKind::Str
                        | ty::TyKind::Dynamic(..)
                ) {
                    Some("raw pointer to unsized/foreign pointee")
                } else {
                    None
                }
            }
            ty::TyKind::Ref(..) => Some("reference field type"),
            ty::TyKind::Array(elem, _) => Self::ty140_unsupported_field_kind(*elem),
            ty::TyKind::Tuple(elems) => elems
                .iter()
                .find_map(|elem| Self::ty140_unsupported_field_kind(elem)),
            ty::TyKind::Foreign(..) => Some("foreign extern field type"),
            ty::TyKind::Slice(..) | ty::TyKind::Str | ty::TyKind::Dynamic(..) => {
                Some("unsized field type")
            }
            _ => None,
        }
    }

    fn ty140_default_body(data: &VariantData) -> Option<String> {
        match data {
            VariantData::Struct { fields, .. } => {
                let mut field_defaults = Vec::with_capacity(fields.len());
                for field in fields {
                    let field_name = field.ident.as_ref()?.name.as_str();
                    field_defaults.push(format!(
                        "{field_name}: {}",
                        Self::ty140_default_expr(&field.ty)
                    ));
                }
                Some(format!("Self {{ {} }}", field_defaults.join(", ")))
            }
            VariantData::Tuple(fields, _) => {
                let tuple_defaults = fields
                    .iter()
                    .map(|field| Self::ty140_default_expr(&field.ty))
                    .collect::<Vec<_>>();
                Some(format!("Self({})", tuple_defaults.join(", ")))
            }
            VariantData::Unit(_) => Some("Self".to_owned()),
        }
    }

    fn ty140_default_expr(ty: &Ty) -> String {
        match &ty.kind {
            TyKind::Array(elem, len) => format!(
                "[{}; {}]",
                Self::ty140_default_expr(elem),
                pprust::expr_to_string(&len.value)
            ),
            _ => "Default::default()".to_owned(),
        }
    }

    fn hir_id_of_path(&self, id: NodeId) -> Option<HirId> {
        let hir_rhs = self.ast_to_hir.get_expr(id, self.tcx)?;
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_rhs.kind else { return None };
        let Res::Local(hir_id) = path.res else { return None };
        Some(hir_id)
    }

    fn owner_returns_raw_pointer(&self, owner: LocalDefId) -> bool {
        let sig = self.tcx.fn_sig(owner).skip_binder().skip_binder();
        matches!(sig.output().kind(), ty::TyKind::RawPtr(..))
    }

    fn can_force_call240_move(&self, local_hir_id: HirId, rhs_source: &Expr) -> bool {
        if !self.enable_box_rewrite {
            return false;
        }
        if self.owner_returns_raw_pointer(local_hir_id.owner.def_id) {
            return false;
        }
        if classify_call240_allocator_source_expr(rhs_source).is_none() {
            return false;
        }
        !self.local_has_call240_blocking_use(local_hir_id)
    }

    fn local_has_call240_blocking_use(&self, local_hir_id: HirId) -> bool {
        fn is_target_local(expr: &hir::Expr<'_>, target: HirId) -> bool {
            let expr = hir_unwrap_addr_of_deref(hir_unwrap_cast(expr));
            if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = expr.kind
                && let Res::Local(hir_id) = path.res
            {
                hir_id == target
            } else {
                false
            }
        }

        struct BlockingUseFinder {
            target: HirId,
            found: bool,
        }

        impl<'tcx> Visitor<'tcx> for BlockingUseFinder {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
                if self.found {
                    return;
                }
                if let hir::ExprKind::MethodCall(seg, receiver, _, _) = expr.kind {
                    let name = seg.ident.name.as_str();
                    if matches!(
                        name,
                        "offset" | "add" | "sub" | "wrapping_add" | "wrapping_sub" | "byte_offset"
                    ) && is_target_local(receiver, self.target)
                    {
                        self.found = true;
                        return;
                    }
                }
                intravisit::walk_expr(self, expr);
            }
        }

        let body = self.tcx.hir_body_owned_by(local_hir_id.owner.def_id);
        let mut finder = BlockingUseFinder {
            target: local_hir_id,
            found: false,
        };
        finder.visit_body(body);
        finder.found
    }

    fn non_raw_null_cmp_rewrite(&self, ptr_expr: &Expr, is_eq: bool) -> Option<Expr> {
        let ptr_expr = unwrap_cast_and_paren(ptr_expr);
        let hir_id = match self.hir_id_of_path(ptr_expr.id) {
            Some(hir_id) => hir_id,
            None => {
                // Some transformed path nodes no longer map to HIR; keep this narrow.
                if let ExprKind::Path(_, _) = ptr_expr.kind
                    && pprust::expr_to_string(ptr_expr) == "str"
                {
                    let pred = format!("({}).is_empty()", pprust::expr_to_string(ptr_expr));
                    let rewritten = if is_eq { pred } else { format!("!({pred})") };
                    return Some(utils::expr!("{}", rewritten));
                }
                return None;
            }
        };
        let ptr_kind = match self.ptr_kinds.get(&hir_id).copied() {
            Some(kind) => kind,
            None => return None,
        };
        let pred = match ptr_kind {
            PtrKind::Move(_) | PtrKind::OptRef(_) => {
                format!("({}).is_none()", pprust::expr_to_string(ptr_expr))
            }
            PtrKind::Slice(_) | PtrKind::SliceCursor(_) => {
                format!("({}).is_empty()", pprust::expr_to_string(ptr_expr))
            }
            PtrKind::Raw(_) => return None,
        };
        let rewritten = if is_eq { pred } else { format!("!({pred})") };
        Some(utils::expr!("{}", rewritten))
    }

    fn normalize_slice_kind(&self, kind: PtrKind, inner_ty: ty::Ty<'tcx>) -> PtrKind {
        match kind {
            PtrKind::SliceCursor(m) => PtrKind::Raw(m),
            PtrKind::Slice(m) if Self::prefer_raw_over_slice(inner_ty) => PtrKind::Raw(m),
            other => other,
        }
    }

    fn is_free_call(&self, hir_func: &hir::Expr<'tcx>) -> bool {
        let hir_func = hir_unwrap_cast(hir_func);
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_func.kind else {
            return false;
        };
        path.segments
            .last()
            .is_some_and(|seg| seg.ident.name.as_str() == "free")
    }

    fn local_hir_id_from_expr(&self, hir_expr: &hir::Expr<'tcx>) -> Option<HirId> {
        let hir_expr = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_expr));
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind else {
            return None;
        };
        let Res::Local(hir_id) = path.res else {
            return None;
        };
        Some(hir_id)
    }

    fn prefer_raw_over_slice(inner_ty: ty::Ty<'tcx>) -> bool {
        matches!(inner_ty.kind(), ty::TyKind::Foreign(..))
    }

    fn transform_rhs(
        &self,
        rhs: &mut Expr,
        hir_rhs: &hir::Expr<'tcx>,
        lhs_kind: PtrKind,
    ) -> PtrKind {
        if !matches!(lhs_kind, PtrKind::Move(_)) {
            let rhs_source = unwrap_addr_of_deref(unwrap_cast_and_paren(rhs));
            if let Some(allocator) = classify_call240_allocator_source_expr(rhs_source) {
                self.record_allocator_reason(
                    hir_rhs,
                    allocator,
                    AllocatorReason::Call250NonMoveRequired,
                );
            }
        }
        self.transform_ptr(rhs, hir_rhs, PtrCtx::Rhs(lhs_kind))
    }

    fn transform_ptr(&self, ptr: &mut Expr, hir_ptr: &hir::Expr<'tcx>, ctx: PtrCtx) -> PtrKind {
        let had_cast_or_paren = matches!(ptr.kind, ExprKind::Cast(..) | ExprKind::Paren(_));
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
            if !matches!(kind1, PtrKind::Raw(_)) && had_cast_or_paren {
                *ptr = (*e).clone();
            }
            return kind1;
        }

        if let ExprKind::Block(block, _) = &mut e.kind {
            let hir::ExprKind::Block(hir_block, _) = hir_e.kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let StmtKind::Expr(inner) = &mut block.stmts.last_mut().unwrap().kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let kind = self.transform_ptr(inner, hir_block.expr.unwrap(), ctx);
            if !matches!(kind, PtrKind::Raw(_)) && had_cast_or_paren {
                *ptr = (*e).clone();
            }
            return kind;
        }

        let e = unwrap_addr_of_deref(unwrap_cast_and_paren(ptr));
        let Some(mut pe) = self.ptr_expr(e, hir_e) else {
            return match ctx {
                PtrCtx::Rhs(kind) => kind,
                PtrCtx::Deref(m) => PtrKind::Raw(m),
            };
        };

        if pe.is_zero() {
            // rhs_ty will be `usize`, not a pointer, so we early return here
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
                PtrCtx::Rhs(PtrKind::Move(m)) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::Move(m);
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

        let typeck = self.tcx.typeck(hir_ptr.hir_id.owner);
        let lhs_ty = typeck.expr_ty_adjusted(hir_ptr);
        let rhs_ty = typeck.expr_ty(hir_unwrap_cast(hir_ptr));

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
        let allocator_source = classify_call240_allocator_source_expr(e);
        if let Some(allocator) = allocator_source
            && let PtrCtx::Rhs(required_kind) = ctx
            && !matches!(required_kind, PtrKind::Move(_))
        {
            self.record_allocator_reason(
                hir_ptr,
                allocator,
                AllocatorReason::Call250NonMoveRequired,
            );
        }

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
                    self.ptr_kinds.get(&hir_id),
                    Some(PtrKind::OptRef(_) | PtrKind::Slice(_) | PtrKind::SliceCursor(_))
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
                    | PtrCtx::Rhs(PtrKind::Move(m))
                    | PtrCtx::Rhs(PtrKind::Slice(m))
                    | PtrCtx::Rhs(PtrKind::SliceCursor(m))
                    | PtrCtx::Deref(m) => m,
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
                            result = if matches!(
                                ctx,
                                PtrCtx::Rhs(PtrKind::Slice(_))
                                    | PtrCtx::Rhs(PtrKind::SliceCursor(_))
                            ) {
                                utils::expr!(
                                    "({})[({}) as usize..]",
                                    pprust::expr_to_string(&result),
                                    pprust::expr_to_string(offset),
                                )
                            } else {
                                utils::expr!(
                                    "({})[({}) as usize]",
                                    pprust::expr_to_string(&result),
                                    pprust::expr_to_string(offset),
                                )
                            };
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
                    PtrCtx::Rhs(PtrKind::Move(_m)) => {
                        // iteration-1: preserve raw/slice semantics in projected addr_of paths
                        let (_, m_lhs) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                        *ptr = self.raw_from_slice_or_cursor(
                            &result,
                            true,
                            m_lhs.is_mut(),
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::Raw(true);
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
                PtrCtx::Rhs(PtrKind::Move(_m)) => {
                    // Avoid introducing unsound conversions from references to owned boxes.
                    // Keep expression as raw pointer for this path in iteration-1.
                    *ptr = utils::expr!(
                        "&raw mut ({}) as *mut {}",
                        pprust::expr_to_string(e),
                        mir_ty_to_string(lhs_inner_ty, self.tcx),
                    );
                    return PtrKind::Raw(true);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    // ref -> cursor
                    self.slice_cursor.set(true);
                    if !need_cast && !ty_updated {
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::from_mut(&mut ({}))",
                                pprust::expr_to_string(e),
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorRef::from_ref(&({}))",
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
                                "crate::slice_cursor::SliceCursor::new(std::slice::from_mut(bytemuck::cast_mut(&mut ({}))))",
                                pprust::expr_to_string(e),
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorRef::new(std::slice::from_ref(bytemuck::cast_ref(&({}))))",
                                pprust::expr_to_string(e),
                            )
                        };
                    } else {
                        let rhs_ty_str = mir_ty_to_string(rhs_inner_ty, self.tcx);
                        let lhs_ty_str = mir_ty_to_string(lhs_inner_ty, self.tcx);
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::from_raw_parts_mut(&raw mut ({0}) as *mut {1}, std::mem::size_of::<{2}>() / std::mem::size_of::<{1}>())",
                                pprust::expr_to_string(e),
                                lhs_ty_str,
                                rhs_ty_str,
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorRef::from_raw_parts(&raw const ({0}) as *const {1}, std::mem::size_of::<{2}>() / std::mem::size_of::<{1}>())",
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
            }
        }

        if pe.as_ptr && self.is_base_not_a_raw_ptr(&pe) {
            match ctx {
                PtrCtx::Rhs(PtrKind::Move(m)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.raw_from_slice_or_cursor(&base, m, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    let base = self.projected_expr(&pe, m, false);
                    if !need_cast {
                        *ptr = utils::expr!(
                            "({}).as_{}ptr()",
                            pprust::expr_to_string(&base),
                            if m { "mut_" } else { "" }
                        );
                    } else {
                        *ptr = utils::expr!(
                            "({}).as_{}ptr() as *{} _",
                            pprust::expr_to_string(&base),
                            if m { "mut_" } else { "" },
                            if m { "mut" } else { "const" },
                        );
                    }
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
                        // can be used for deref, so type must be specified
                        *ptr = utils::expr!(
                            "Some(bytemuck::cast_{}::<_, {}>(&{}({})[0]))",
                            if m { "mut" } else { "ref" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(&base),
                        );
                    } else {
                        // can be used for deref, so type must be specified
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
                    // slice -> cursor
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_from_plain_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    // slice -> slice
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.plain_slice_from_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
            }
        }

        if let PtrExprBaseKind::Path(res) = pe.base_kind
            && let Res::Local(hir_id) = res
            && let Some(rhs_kind) = self.ptr_kinds.get(&hir_id)
        {
            match (ctx, *rhs_kind) {
                (PtrCtx::Rhs(PtrKind::Move(m)), PtrKind::Raw(m1)) => {
                    *ptr = self.move_from_raw(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty, hir_ptr);
                    return PtrKind::Move(m);
                }
                (PtrCtx::Rhs(PtrKind::Move(m)), PtrKind::Move(_m1)) => {
                    return PtrKind::Move(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::Move(_m1)) => {
                    *ptr = self.raw_from_move(pe.base, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m), PtrKind::Move(m1)) => {
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
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::Move(_)) => {
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::Move(_)) => {
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)) | PtrCtx::Deref(m), PtrKind::Raw(m1)) => {
                    if m && !m1 {
                        let inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                        *ptr = utils::expr!("{} as *mut {}", pprust::expr_to_string(ptr), inner_ty);
                    }
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::OptRef(m1)) => {
                    if pe.projs.is_empty() {
                        *ptr = self.raw_from_opt_ref(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    } else {
                        let raw_base =
                            self.raw_from_opt_ref(pe.base, m1, m1, rhs_inner_ty, rhs_inner_ty);
                        let raw_projected = self.apply_raw_projections(raw_base, &pe.projs, m1);
                        *ptr =
                            self.coerce_raw_expr(&raw_projected, m, m1, lhs_inner_ty, rhs_inner_ty);
                    }
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
                (PtrCtx::Deref(m), PtrKind::OptRef(m1)) => {
                    if pe.projs.is_empty() {
                        if m == m1 {
                            *ptr = utils::expr!(
                                "({}).as_deref{}()",
                                pprust::expr_to_string(pe.base),
                                if m { "_mut" } else { "" },
                            );
                        } else {
                            *ptr = self.opt_ref_from_opt_ref(
                                pe.base,
                                m,
                                m1,
                                lhs_inner_ty,
                                rhs_inner_ty,
                                def_id,
                            );
                        }
                    } else {
                        // Project through a raw-pointer view first, then rebuild Option.
                        let raw_base =
                            self.raw_from_opt_ref(pe.base, m1, m1, rhs_inner_ty, rhs_inner_ty);
                        let raw_projected = self.apply_raw_projections(raw_base, &pe.projs, m1);
                        *ptr = self.opt_ref_from_raw(
                            &raw_projected,
                            m,
                            m1,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::OptRef(m1)) => {
                    if pe.projs.is_empty() {
                        // can be used for deref, so type must be specified
                        *ptr = self.opt_ref_from_opt_ref(
                            pe.base,
                            m,
                            m1,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                    } else {
                        // Project through a raw-pointer view first, then rebuild Option.
                        let raw_base =
                            self.raw_from_opt_ref(pe.base, m1, m1, rhs_inner_ty, rhs_inner_ty);
                        let raw_projected = self.apply_raw_projections(raw_base, &pe.projs, m1);
                        *ptr = self.opt_ref_from_raw(
                            &raw_projected,
                            m,
                            m1,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                    }
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
                            format!("({}).{}()", base_str, as_slice)
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
                (PtrCtx::Rhs(PtrKind::Slice(m)) | PtrCtx::Deref(m), PtrKind::Slice(_)) => {
                    let base = self.projected_expr(&pe, m, false);
                    // can be used for deref, so type must be specified
                    *ptr = self.plain_slice_from_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
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
                    *ptr = self.cursor_from_slice_or_cursor_inner(
                        &base,
                        m,
                        lhs_inner_ty,
                        rhs_inner_ty,
                        false,
                    );
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::Raw(m1)) => {
                    self.slice_cursor.set(true);
                    // to keep offsets, we use `e` instead of `pe.base`
                    *ptr = self.cursor_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
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
                        self.cursor_from_slice_or_cursor(&base, m, lhs_inner_ty, rhs_inner_ty);
                    if !m && m1 {
                        result = utils::expr!(
                            "crate::slice_cursor::SliceCursorRef::new(({}).as_slice())",
                            pprust::expr_to_string(&result),
                        );
                    }
                    // need fork only for identity copy (no projections, no cast)
                    if pe.projs.is_empty() && lhs_inner_ty == rhs_inner_ty && !(m1 && !m) {
                        result = utils::expr!("({}).fork()", pprust::expr_to_string(&result));
                    }
                    *ptr = result;
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(_) | PtrKind::Slice(_)), PtrKind::OptRef(_)) => {
                    panic!()
                }
                (PtrCtx::Rhs(PtrKind::Move(m)), _) => {
                    return PtrKind::Move(m);
                }
            }
        }

        if pe.base_kind == PtrExprBaseKind::ByteStr {
            match ctx {
                PtrCtx::Rhs(PtrKind::Move(_)) => {
                    return PtrKind::Raw(false);
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    if m {
                        *ptr = utils::expr!(
                            "({}) as *const _ as *mut {}",
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    if m {
                        let raw = utils::expr!(
                            "({}) as *const _ as *mut {}",
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                        *ptr = self.opt_ref_from_raw(&raw, true, true, lhs_inner_ty, lhs_inner_ty);
                    } else if lhs_inner_ty == self.tcx.types.u8 {
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
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    if m {
                        let raw = utils::expr!(
                            "({}) as *const _ as *mut {}",
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                        *ptr = self.cursor_from_raw(&raw, true, true, lhs_inner_ty, lhs_inner_ty);
                    } else if lhs_inner_ty == self.tcx.types.u8 {
                        *ptr = utils::expr!(
                            "crate::slice_cursor::SliceCursorRef::new({})",
                            pprust::expr_to_string(e)
                        );
                    } else {
                        assert!(lhs_inner_ty.is_numeric());
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "crate::slice_cursor::SliceCursorRef::new(bytemuck::cast_slice({}))",
                            pprust::expr_to_string(e),
                        );
                    }
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    if m {
                        let raw = utils::expr!(
                            "({}) as *const _ as *mut {}",
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                        *ptr = self.slice_from_raw(&raw, true, true, lhs_inner_ty, lhs_inner_ty);
                    } else if lhs_inner_ty == self.tcx.types.u8 {
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

        let m1 = match pe.base_ty.kind() {
            ty::TyKind::RawPtr(_, m) => m.is_mut(),
            ty::TyKind::Array(_, _) => match self.behind_subscripts(pe.hir_base) {
                PathOrDeref::Path => true,
                PathOrDeref::Deref(hir_id) => self
                    .ptr_kinds
                    .get(&hir_id)
                    .copied()
                    .map(|k| k.is_mut())
                    .unwrap_or(true),
                PathOrDeref::Other => {
                    panic!("{}", pprust::expr_to_string(pe.base))
                }
            },
            _ => panic!("{:?}", pe.base_ty),
        };
        // Override m1 if this is a call to a function whose return type was changed
        let m1 = if let hir::ExprKind::Call(func, _) = pe.hir_base.kind
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
            && let Some(PtrKind::Raw(m)) =
                self.sig_decs.data.get(&def_id).and_then(|sd| sd.output_dec)
        {
            let output_ty = self.tcx.fn_sig(def_id).skip_binder().skip_binder().output();
            if let ty::TyKind::RawPtr(_, out_m) = output_ty.kind() {
                if !out_m.is_mut() {
                    false
                } else if self.raw_mutability {
                    m
                } else {
                    out_m.is_mut()
                }
            } else {
                m
            }
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
            PtrCtx::Rhs(PtrKind::Move(m)) => {
                *ptr = self.move_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty, hir_ptr);
                PtrKind::Move(m)
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

    fn raw_from_move(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let into_raw_expr = format!(
            "({}).take().map(|_x| Box::into_raw(_x)).unwrap_or(std::ptr::null_mut())",
            pprust::expr_to_string(e)
        );
        if need_cast {
            utils::expr!(
                "({}) as *{} {}",
                into_raw_expr,
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        } else if m {
            utils::expr!("{}", into_raw_expr)
        } else {
            utils::expr!(
                "({}) as *const {}",
                into_raw_expr,
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn coerce_raw_expr(
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
            utils::expr!("({}){}", pprust::expr_to_string(e), cast_mut)
        } else {
            utils::expr!(
                "({}){} as *{} {}",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn move_from_raw(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        hir_ptr: &hir::Expr<'tcx>,
    ) -> Expr {
        if let Some(callee) = classify_call240_allocator_source_expr(e) {
            self.record_allocator_reason(hir_ptr, callee, AllocatorReason::Call240Applied);
            if !self.is_low_risk_default_type_for_call240(lhs_inner_ty) {
                self.record_allocator_reason(
                    hir_ptr,
                    callee,
                    AllocatorReason::Call240CompileRiskDefaultMissing,
                );
            }
            return utils::expr!(
                "Some(Box::new(<{} as Default>::default()))",
                mir_ty_to_string(lhs_inner_ty, self.tcx)
            );
        }

        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let lhs_inner_ty_str = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let mut ptr_expr = if !need_cast {
            pprust::expr_to_string(e)
        } else {
            format!(
                "({}) as *{} {}",
                pprust::expr_to_string(e),
                if m { "mut" } else { "const" },
                lhs_inner_ty_str,
            )
        };
        if !m1 {
            ptr_expr = format!("({ptr_expr}) as *mut {lhs_inner_ty_str}");
        }
        let boxed_ptr_expr = if m {
            ptr_expr.clone()
        } else {
            format!("({ptr_expr}) as *mut {lhs_inner_ty_str}")
        };
        utils::expr!(
            "{{
                let __ptr_rewriter_raw: *mut {} = {};
                if (__ptr_rewriter_raw).is_null() {{
                    None
                }} else {{
                    Some(Box::from_raw(__ptr_rewriter_raw))
                }}
            }}",
            lhs_inner_ty_str,
            boxed_ptr_expr,
        )
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
            if m == m1 {
                let raw = self.raw_from_opt_ref(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                self.opt_ref_from_raw(&raw, m, m1, lhs_inner_ty, rhs_inner_ty)
            } else {
                utils::expr!(
                    "({}).as_deref{}()",
                    pprust::expr_to_string(e),
                    if m && m1 { "_mut" } else { "" },
                )
            }
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
        if is_null_ptr_call_expr(e) {
            return if m {
                utils::expr!("&mut []")
            } else {
                utils::expr!("&[]")
            };
        }
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
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
        if is_null_ptr_call_expr(e) {
            let cursor_ty = if m {
                "crate::slice_cursor::SliceCursor"
            } else {
                "crate::slice_cursor::SliceCursorRef"
            };
            return utils::expr!("{}::empty()", cursor_ty);
        }
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursor"
        } else {
            "crate::slice_cursor::SliceCursorRef"
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
        pe: &PtrExpr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let base_is_slice_like_local = matches!(
            pe.base_kind,
            PtrExprBaseKind::Path(Res::Local(hir_id))
                if matches!(
                    self.ptr_kinds.get(&hir_id),
                    Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_))
                )
        );
        let get_reference = |use_ref| {
            if use_ref {
                if m { "&mut " } else { "&" }
            } else {
                ""
            }
        };
        if !need_cast {
            let reference =
                get_reference(pe.base_kind != PtrExprBaseKind::Alloca && !base_is_slice_like_local);
            utils::expr!("{}({})", reference, pprust::expr_to_string(e),)
        } else if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
            self.bytemuck.set(true);
            let reference = get_reference(
                !matches!(e.kind, ExprKind::Index(..))
                    && pe.base_kind != PtrExprBaseKind::Alloca
                    && !base_is_slice_like_local,
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

    // slice -> Cursor
    fn cursor_from_plain_slice(
        &self,
        e: &Expr,
        pe: &PtrExpr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let get_reference = |use_ref| {
            if use_ref {
                if m { "&mut " } else { "&" }
            } else {
                ""
            }
        };
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursor"
        } else {
            "crate::slice_cursor::SliceCursorRef"
        };
        if !need_cast {
            let reference = get_reference(pe.base_kind != PtrExprBaseKind::Alloca);
            utils::expr!(
                "{}::new({}{})",
                cursor_ty,
                reference,
                pprust::expr_to_string(e),
            )
        } else if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
            let reference = get_reference(pe.base_kind != PtrExprBaseKind::Alloca);
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

    fn cursor_from_slice_or_cursor(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        self.cursor_from_slice_or_cursor_inner(
            e,
            m,
            lhs_inner_ty,
            rhs_inner_ty,
            is_plain_slice_expr(e),
        )
    }

    fn cursor_from_slice_or_cursor_inner(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        is_plain_slice: bool,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursor"
        } else {
            "crate::slice_cursor::SliceCursorRef"
        };
        if !need_cast {
            e.clone()
        } else if is_plain_slice {
            if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
                self.bytemuck.set(true);
                utils::expr!(
                    "{}::new(bytemuck::cast_slice{}::<_, {}>({}{}))",
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    mir_ty_to_string(lhs_inner_ty, self.tcx),
                    if m { "&mut *" } else { "&*" },
                    pprust::expr_to_string(e),
                )
            } else {
                utils::expr!(
                    "{}::from_raw_parts{}(({}).as_ptr() as *{} {}, ({}).len())",
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    if m { "mut" } else { "const" },
                    mir_ty_to_string(lhs_inner_ty, self.tcx),
                    pprust::expr_to_string(e),
                )
            }
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
                    if matches!(seg.ident.name.as_str(), "offset" | "add") =>
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
                Some(PtrKind::Move(m)) => Some(*m),
                Some(PtrKind::OptRef(m)) => Some(*m),
                Some(PtrKind::Slice(m)) | Some(PtrKind::SliceCursor(m)) => Some(*m),
                Some(PtrKind::Raw(m)) => Some(*m),
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
                    return None;
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
                if name == "offset" || name == "add" {
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    ptr_expr.push_offset(&call.args[0]);
                    Some(ptr_expr)
                } else if name == "as_mut_ptr" || name == "as_ptr" {
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    if ptr_expr.as_ptr {
                        None
                    } else {
                        ptr_expr.as_ptr = true;
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
                    None
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
                PathOrDeref::Deref(hir_id) => self.ptr_kinds.get(&hir_id).is_some_and(|kind| {
                    matches!(
                        kind,
                        PtrKind::OptRef(_) | PtrKind::Slice(_) | PtrKind::SliceCursor(_)
                    )
                }),
                PathOrDeref::Other => pe.base_ty.is_array(),
            },
            _ => false,
        }
    }

    fn apply_raw_projections(&self, mut e: Expr, projs: &[PtrExprProj<'_, 'tcx>], m: bool) -> Expr {
        for proj in projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    e = utils::expr!(
                        "({}).offset(({}) as isize)",
                        pprust::expr_to_string(&e),
                        pprust::expr_to_string(offset),
                    );
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => {
                    e = utils::expr!("({}) as usize", pprust::expr_to_string(&e));
                }
                PtrExprProj::Cast(ty) => {
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty).unwrap();
                    e = utils::expr!(
                        "({}) as *{} {}",
                        pprust::expr_to_string(&e),
                        if m { "mut" } else { "const" },
                        mir_ty_to_string(to_ty, self.tcx),
                    );
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
        }
        e
    }

    fn render_offset_expr(&self, offset: &Expr) -> String {
        let offset_expr = unwrap_paren(offset);
        if let ExprKind::Field(base, ident) = &offset_expr.kind {
            let base = unwrap_paren(base);
            if let ExprKind::Unary(UnOp::Deref, inner) = &base.kind {
                let inner = unwrap_paren(inner);
                if matches!(inner.kind, ExprKind::Path(_, _))
                    && let Some(hir_id) = self.hir_id_of_path(inner.id)
                    && matches!(
                        self.ptr_kinds.get(&hir_id),
                        Some(PtrKind::OptRef(_) | PtrKind::Move(_))
                    )
                {
                    return format!(
                        "(*({}).as_deref().unwrap()).{}",
                        pprust::expr_to_string(inner),
                        ident.name,
                    );
                }
            }
        }
        pprust::expr_to_string(offset)
    }

    fn projected_expr(&self, pe: &PtrExpr<'_, 'tcx>, m: bool, mut is_raw: bool) -> Expr {
        let mut is_plain_slice = if let PtrExprBaseKind::Path(Res::Local(hir_id)) = pe.base_kind {
            matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Slice(_)))
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
        let mut e = pe.base.clone();
        if pe.projs.is_empty() {
            return e;
        }
        let mut from_ty = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx).unwrap();
        let mut is_array = pe.base_ty.is_array();
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    let offset_str = self.render_offset_expr(offset);
                    if is_raw {
                        e = utils::expr!(
                            "({}).offset(({}) as isize)",
                            pprust::expr_to_string(&e),
                            offset_str,
                        );
                    } else if is_data_container || is_plain_slice {
                        // Base is a data container (Vec, array) — return a re-sliced expression.
                        let base_for_offset = if is_plain_slice {
                            if let ExprKind::AddrOf(BorrowKind::Ref, _, inner) =
                                &unwrap_paren(&e).kind
                            {
                                unwrap_paren(inner)
                            } else {
                                &e
                            }
                        } else {
                            &e
                        };
                        let base_str = pprust::expr_to_string(base_for_offset);
                        let needs_explicit_borrow = !is_plain_slice
                            && if let ExprKind::Field(base, _) = &unwrap_paren(&e).kind {
                                matches!(unwrap_paren(base).kind, ExprKind::Unary(UnOp::Deref, _))
                            } else {
                                false
                            };
                        e = if is_plain_slice {
                            utils::expr!(
                                "&{}(({})[({}) as usize..])",
                                if m { "mut " } else { "" },
                                base_str,
                                offset_str,
                            )
                        } else if needs_explicit_borrow {
                            utils::expr!(
                                "&{}(((&{}({}))[({}) as usize..]))",
                                if m { "mut " } else { "" },
                                if m { "mut " } else { "" },
                                base_str,
                                offset_str,
                            )
                        } else {
                            utils::expr!("({})[({}) as usize..]", base_str, offset_str)
                        };
                    } else {
                        e = utils::expr!(
                            "{{ let mut _c = ({}).fork(); _c.seek(({}) as isize); _c }}",
                            pprust::expr_to_string(&e),
                            offset_str,
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
                            if m { "_mut" } else { "" },
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
                            e = self.plain_slice_from_slice(&e, pe, m, to_ty, from_ty);
                            is_plain_slice = true;
                        } else {
                            e = self.cursor_from_slice_or_cursor(&e, m, to_ty, from_ty);
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
fn mk_move_ty<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    utils::ty!("Option<Box<{ty}>>")
}

#[inline]
fn mk_cursor_ty<'tcx>(ty: ty::Ty<'tcx>, mutability: bool, tcx: TyCtxt<'tcx>) -> Ty {
    let ty = mir_ty_to_string(ty, tcx);
    if mutability {
        utils::ty!("crate::slice_cursor::SliceCursor<'_, {ty}>")
    } else {
        utils::ty!("crate::slice_cursor::SliceCursorRef<'_, {ty}>")
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

fn is_range_index_expr(expr: &Expr) -> bool {
    if let ExprKind::Index(_, idx, _) = &unwrap_paren(expr).kind {
        matches!(unwrap_paren(idx).kind, ExprKind::Range(..))
    } else {
        false
    }
}

fn is_zero_literal_expr(expr: &Expr) -> bool {
    match &unwrap_cast_and_paren(expr).kind {
        ExprKind::Lit(lit) => {
            matches!(lit.kind, token::LitKind::Integer) && lit.symbol.as_str() == "0"
        }
        _ => false,
    }
}

fn is_null_ptr_call_expr(expr: &Expr) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    if let ExprKind::Call(func, _) = &expr.kind {
        if let ExprKind::Path(_, path) = &unwrap_paren(func).kind
            && let Some(seg) = path.segments.last()
        {
            matches!(seg.ident.name.as_str(), "null" | "null_mut")
        } else {
            false
        }
    } else {
        false
    }
}

#[derive(Debug, Clone)]
struct SliceElemBorrowArg {
    base: String,
    offset: String,
    is_mut: bool,
}

fn extract_slice_elem_borrow_arg(arg: &Expr) -> Option<SliceElemBorrowArg> {
    let ExprKind::AddrOf(BorrowKind::Ref, mutability, inner) = &unwrap_paren(arg).kind else {
        return None;
    };
    let (base, offset) = extract_slice_elem_projection(inner)?;
    if utils::ast::has_side_effects(base) {
        return None;
    }
    Some(SliceElemBorrowArg {
        base: pprust::expr_to_string(base),
        offset: pprust::expr_to_string(offset),
        is_mut: mutability.is_mut(),
    })
}

fn extract_slice_elem_projection(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let expr = unwrap_paren(expr);
    let ExprKind::Index(base, idx, _) = &expr.kind else {
        return None;
    };
    let base = unwrap_paren(base);
    let idx = unwrap_paren(idx);

    if is_zero_literal_expr(idx)
        && let ExprKind::AddrOf(BorrowKind::Ref, _, inner) = &base.kind
    {
        return extract_slice_offset_projection(inner);
    }

    Some((base, idx))
}

fn extract_slice_offset_projection(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let expr = unwrap_paren(expr);
    let ExprKind::Index(base, idx, _) = &expr.kind else {
        return None;
    };
    let base = unwrap_paren(base);
    let idx = unwrap_paren(idx);

    if let ExprKind::Range(Some(start), None, RangeLimits::HalfOpen) = &idx.kind {
        Some((base, unwrap_paren(start)))
    } else if is_zero_literal_expr(idx) {
        Some((base, idx))
    } else {
        None
    }
}

fn hoist_mut_call_arg_conflicts(expr: &mut Expr) {
    let ExprKind::Call(func, args) = &expr.kind else {
        return;
    };

    let mut grouped: FxHashMap<String, Vec<(usize, SliceElemBorrowArg)>> = FxHashMap::default();
    let mut base_order = Vec::<String>::new();
    for (idx, arg) in args.iter().enumerate() {
        let Some(info) = extract_slice_elem_borrow_arg(arg) else {
            continue;
        };
        if !grouped.contains_key(&info.base) {
            base_order.push(info.base.clone());
        }
        grouped
            .entry(info.base.clone())
            .or_default()
            .push((idx, info));
    }

    let mut lets = String::new();
    let mut new_args = args
        .iter()
        .map(|arg| pprust::expr_to_string(arg))
        .collect::<Vec<_>>();
    let mut conflict_group_count = 0usize;
    for base in &base_order {
        let Some(group) = grouped.get(base) else {
            continue;
        };
        if group.len() <= 1 || !group.iter().any(|(_, arg)| arg.is_mut) {
            continue;
        }

        use std::fmt::Write as _;
        let base_tmp = format!("_pr_base_{conflict_group_count}");
        write!(&mut lets, "let {base_tmp} = ({base}).as_mut_ptr();").unwrap();
        for (arg_idx, info) in group {
            let tmp = format!("_pr_arg_{arg_idx}");
            let ptr = format!("({base_tmp}).add(({}) as usize)", info.offset);
            if info.is_mut {
                write!(&mut lets, "let {tmp}: &mut _ = unsafe {{ &mut *({ptr}) }};").unwrap();
            } else {
                write!(&mut lets, "let {tmp}: &_ = unsafe {{ &*({ptr}) }};").unwrap();
            }
            new_args[*arg_idx] = tmp;
        }
        conflict_group_count += 1;
    }

    if conflict_group_count > 0 {
        let call = format!("{}({})", pprust::expr_to_string(func), new_args.join(", "));
        *expr = utils::expr!("{{ {lets} {call} }}");
        return;
    }

    let Some(first_arg) = args.first() else {
        return;
    };
    let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, inner) = &unwrap_paren(first_arg).kind
    else {
        return;
    };
    let inner = unwrap_paren(inner);
    if !matches!(inner.kind, ExprKind::Path(_, _)) {
        return;
    }
    let borrowed_name = pprust::expr_to_string(inner);

    let mut lets = String::new();
    let mut new_args = Vec::with_capacity(args.len());
    new_args.push(pprust::expr_to_string(first_arg));

    for (idx, arg) in args.iter().enumerate().skip(1) {
        let arg_s = pprust::expr_to_string(arg);
        if arg_s.contains(&borrowed_name) {
            let tmp = format!("_pr_arg_{idx}");
            use std::fmt::Write as _;
            write!(&mut lets, "let {tmp} = {arg_s};").unwrap();
            new_args.push(tmp);
        } else {
            new_args.push(arg_s);
        }
    }

    if lets.is_empty() {
        return;
    }

    let call = format!("{}({})", pprust::expr_to_string(func), new_args.join(", "));
    *expr = utils::expr!("{{ {lets} {call} }}");
}

fn hoist_opt_ref_borrow(expr: &mut Expr) {
    let mut visitor = OptRefBorrowVisitor::default();
    visitor.visit_expr(expr);

    let mut lets = String::new();
    for (name, muts) in &visitor.args {
        if muts.len() <= 1 || muts.iter().all(|m| !*m) {
            break;
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
    args: FxHashMap<Symbol, Vec<bool>>,
}

impl mut_visit::MutVisitor for OptRefBorrowVisitor {
    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        if let ExprKind::Unary(UnOp::Deref, e) = &mut expr.kind
            && let call_expr = unwrap_paren_mut(e)
            && let ExprKind::MethodCall(call) = &mut call_expr.kind
            && call.seg.ident.name == rustc_span::sym::unwrap
            && let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(&mut call.receiver).kind
            && let name = call.seg.ident.name.as_str()
            && let is_deref = name == "as_deref"
            && let is_deref_mut = name == "as_deref_mut"
            && (is_deref || is_deref_mut)
            && let ExprKind::Path(_, path) = &mut unwrap_paren_mut(&mut call.receiver).kind
        {
            let name = path.segments.last().unwrap().ident.name;
            if self.rewrite_targets.is_empty() {
                // Collect mode
                self.args.entry(name).or_default().push(is_deref_mut);
            } else if let Some(new_name) = self.rewrite_targets.get(&name) {
                // Rewrite mode
                *call_expr = utils::expr!("{new_name}");
            }
        }
    }
}
