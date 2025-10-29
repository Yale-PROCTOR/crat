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
use rustc_middle::{ty, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;
use utils::ir::AstToHir;

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

                // Currently intra-procedural borrow inference:
                // skip return type; only consider parameters
                for ((local_decl, input_dec), param) in mir_body
                    .local_decls
                    .iter()
                    .skip(1)
                    .zip(&sig_dec.input_decs)
                    .zip(&mut fn_item.sig.decl.inputs)
                {
                    let Some(PtrKind::OptRef(m)) = input_dec else { continue };
                    let (inner_ty, _) =
                        unwrap_ptr_from_mir_ty(local_decl.ty).unwrap_or_else(|| {
                            panic!(
                                "Expected pointer type, got {ty:?} in {local_decl:?}",
                                ty = local_decl.ty
                            )
                        });
                    *param.ty = mk_opt_ref_ty(inner_ty, *m, self.tcx);
                    if let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind {
                        binding_mode.1 = Mutability::Mut;
                    }
                }
            }
            _ => {}
        }

        mut_visit::walk_item(self, item);
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

            if let PtrKind::OptRef(m) = lhs_kind {
                local.ty = Some(P(mk_opt_ref_ty(lhs_inner_ty, m, self.tcx)));
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
            ExprKind::Unary(UnOp::Deref, e) => {
                if matches!(e.kind, ExprKind::Path(_, _)) {
                    let hir_id = self.hir_id_of_path(e.id).unwrap();
                    let ptr_kind = self.ptr_kinds[&hir_id];
                    if let PtrKind::OptRef(m) = ptr_kind {
                        let m = if m { "_mut" } else { "" };
                        **e =
                            utils::expr!("{}.as_deref{}().unwrap()", pprust::expr_to_string(e), m);
                    }
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
                        .unwrap_or(PtrKind::Raw(m.is_mut()));
                    self.transform_rhs(arg, harg, param_kind);
                }
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
        let mut sig_decs = SigDecisions::new(rust_program, analysis); // TODO: Move outside
        let mut ptr_kinds = collect_diffs(rust_program, analysis); // TODO: Move outside

        // HACK: if `p.offset(..)` is used, `p` remains a raw pointer
        // TODO: use fatness analysis instead
        let mut visitor = OffsetVisitor {
            tcx: rust_program.tcx,
            params: FxHashMap::default(),
            offsets: FxHashSet::default(),
        };
        rust_program
            .tcx
            .hir_visit_all_item_likes_in_crate(&mut visitor);
        for (def_id, dec) in &mut sig_decs.data {
            let params = &visitor.params[def_id];
            for (dec, hir_id) in dec.input_decs.iter_mut().zip(params) {
                if let Some(kind) = dec
                    && visitor.offsets.contains(hir_id)
                {
                    let typeck = rust_program.tcx.typeck(hir_id.owner);
                    let ty = typeck.node_type(*hir_id);
                    let ty::TyKind::RawPtr(_, m) = ty.kind() else { panic!() };
                    *kind = PtrKind::Raw(m.is_mut());
                }
            }
        }
        for (hir_id, kind) in &mut ptr_kinds {
            if visitor.offsets.contains(hir_id) {
                let typeck = rust_program.tcx.typeck(hir_id.owner);
                let ty = typeck.node_type(*hir_id);
                let ty::TyKind::RawPtr(_, m) = ty.kind() else { panic!() };
                *kind = PtrKind::Raw(m.is_mut());
            }
        }

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
            if matches!(lhs_kind, PtrKind::OptRef(_)) {
                *rhs = utils::expr!("None");
            }
            return;
        }

        let typeck = self.tcx.typeck(hir_rhs.hir_id.owner);
        let lhs_ty = typeck.expr_ty_adjusted(hir_rhs);
        let rhs_ty = typeck.expr_ty(unwrap_hir_expr(hir_rhs));
        let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
        let (rhs_inner_ty, _) = unwrap_ptr_from_mir_ty(rhs_ty).unwrap();
        let need_cast = lhs_inner_ty != rhs_inner_ty;
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
                        } else {
                            *rhs = utils::expr!(
                                "({}).as_deref{1}().map_or(std::ptr::null{1}(), |x| x)",
                                pprust::expr_to_string(e),
                                if m { "_mut" } else { "" },
                            );
                        }
                    }
                    (PtrKind::OptRef(m), PtrKind::Raw(_)) => {
                        if need_cast {
                            if *lhs_inner_ty.kind() == ty::TyKind::Int(ty::IntTy::I8) {
                                // special handling for libc::c_char TODO: better solution for char arrays
                                *rhs = utils::expr!(
                                    "(({0}) as *{1} u8 as *{1} libc::c_char).as_{2}()",
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
                    (PtrKind::Raw(_), PtrKind::Raw(_)) => {}
                }
            }
            ExprKind::AddrOf(_, _, e) => {
                // if rhs is `&mut x` and `x`'s type has been updated to `Option<&(mut) T>`,
                // we need a cast
                let ty_updated = if matches!(e.kind, ExprKind::Path(_, _))
                    && let Some(hir_e) = self.ast_to_hir.get_expr(e.id, self.tcx)
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_e.kind
                    && let Res::Local(hir_id) = path.res
                {
                    matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::OptRef(_)))
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
                            *rhs = utils::expr!(
                                "Some(&{}({}))",
                                if m { "mut " } else { "" },
                                pprust::expr_to_string(e)
                            );
                        }
                    }
                    PtrKind::Raw(m) => {
                        if need_cast || ty_updated {
                            let lhs_inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                            *rhs = utils::expr!(
                                "&raw {0} ({1}) as *{0} {2}",
                                if m { "mut" } else { "const" },
                                pprust::expr_to_string(e),
                                lhs_inner_ty,
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
            _ => match lhs_kind {
                PtrKind::OptRef(m) => {
                    if need_cast {
                        if *lhs_inner_ty.kind() == ty::TyKind::Int(ty::IntTy::I8) {
                            // special handling for libc::c_char TODO: better solution for char arrays
                            *rhs = utils::expr!(
                                "(({0}) as *{1} u8 as *{1} libc::c_char).as_{2}()",
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
                PtrKind::Raw(_) => {}
            },
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

#[inline]
fn unwrap_ptr_from_mir_ty(ty: ty::Ty<'_>) -> Option<(ty::Ty<'_>, ty::Mutability)> {
    match ty.kind() {
        ty::TyKind::RawPtr(ty, m) | ty::TyKind::Ref(_, ty, m) => Some((*ty, *m)),
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
fn mir_ty_to_string<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> String {
    let mut buf = String::new();
    format_mir_ty(&mut buf, ty, tcx).unwrap();
    buf
}

fn format_mir_ty<'tcx, W: std::fmt::Write>(
    out: &mut W,
    ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> std::fmt::Result {
    use ty::*;
    match ty.kind() {
        TyKind::Bool => write!(out, "bool"),
        TyKind::Char => write!(out, "char"),
        TyKind::Int(IntTy::Isize) => write!(out, "isize"),
        TyKind::Int(IntTy::I8) => write!(out, "i8"),
        TyKind::Int(IntTy::I16) => write!(out, "i16"),
        TyKind::Int(IntTy::I32) => write!(out, "i32"),
        TyKind::Int(IntTy::I64) => write!(out, "i64"),
        TyKind::Int(IntTy::I128) => write!(out, "i128"),
        TyKind::Uint(UintTy::Usize) => write!(out, "usize"),
        TyKind::Uint(UintTy::U8) => write!(out, "u8"),
        TyKind::Uint(UintTy::U16) => write!(out, "u16"),
        TyKind::Uint(UintTy::U32) => write!(out, "u32"),
        TyKind::Uint(UintTy::U64) => write!(out, "u64"),
        TyKind::Uint(UintTy::U128) => write!(out, "u128"),
        TyKind::Float(FloatTy::F16) => write!(out, "f16"),
        TyKind::Float(FloatTy::F32) => write!(out, "f32"),
        TyKind::Float(FloatTy::F64) => write!(out, "f64"),
        TyKind::Float(FloatTy::F128) => write!(out, "f128"),
        TyKind::Adt(adt_def, args) => {
            write!(out, "crate::{}", tcx.def_path_str(adt_def.did()))?;
            if !args.is_empty() {
                write!(out, "<")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(out, ", ")?;
                    }
                    match arg.kind() {
                        GenericArgKind::Type(ty) => format_mir_ty(out, ty, tcx)?,
                        GenericArgKind::Const(cnst) => write!(out, "{cnst}")?,
                        GenericArgKind::Lifetime(_) => write!(out, "'_")?,
                    }
                }
                write!(out, ">")?;
            }
            Ok(())
        }
        TyKind::Foreign(def_id) => write!(out, "crate::{}", tcx.def_path_str(*def_id)),
        TyKind::Str => write!(out, "str"),
        TyKind::Array(ty, cnst) => {
            write!(out, "[")?;
            format_mir_ty(out, *ty, tcx)?;
            write!(out, "; {cnst}]")
        }
        TyKind::Pat(..) => todo!(),
        TyKind::Slice(ty) => {
            write!(out, "[")?;
            format_mir_ty(out, *ty, tcx)?;
            write!(out, "]")
        }
        TyKind::RawPtr(ty, mutability) => {
            let m = match mutability {
                Mutability::Mut => "mut",
                Mutability::Not => "const",
            };
            write!(out, "*{m} ")?;
            format_mir_ty(out, *ty, tcx)
        }
        TyKind::Ref(_, ty, mutability) => {
            write!(out, "&")?;
            if *mutability == Mutability::Mut {
                write!(out, "mut ")?;
            }
            format_mir_ty(out, *ty, tcx)
        }
        TyKind::FnDef(..) => todo!(),
        TyKind::FnPtr(..) => todo!(),
        TyKind::UnsafeBinder(..) => todo!(),
        TyKind::Dynamic(..) => todo!(),
        TyKind::Closure(..) => todo!(),
        TyKind::CoroutineClosure(..) => todo!(),
        TyKind::Coroutine(..) => todo!(),
        TyKind::CoroutineWitness(..) => todo!(),
        TyKind::Never => todo!(),
        TyKind::Tuple(tys) => {
            write!(out, "(")?;
            for (i, ty) in tys.iter().enumerate() {
                if i > 0 {
                    write!(out, ", ")?;
                }
                format_mir_ty(out, ty, tcx)?;
            }
            write!(out, ")")
        }
        TyKind::Alias(..) => todo!(),
        TyKind::Param(..) => todo!(),
        TyKind::Bound(..) => todo!(),
        TyKind::Placeholder(..) => todo!(),
        TyKind::Infer(..) => todo!(),
        TyKind::Error(..) => panic!(),
    }
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
        if let hir::ExprKind::MethodCall(seg, e, _, _) = expr.kind
            && seg.ident.name == rustc_span::sym::offset
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = unwrap_hir_expr(e).kind
            && let Res::Local(hir_id) = path.res
        {
            self.offsets.insert(hir_id);
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
