use std::{
    cell::RefCell,
    fmt::Write as _,
    ops::{Deref, DerefMut},
};

use etrace::some_or;
use rustc_abi::FieldIdx;
use rustc_ast::{
    ast::*,
    mut_visit::{self, MutVisitor},
    ptr::P,
    token::TokenKind,
    tokenstream::{TokenStream, TokenTree},
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol, def_id::LocalDefId, symbol::Ident};

use super::{
    api_list::{self, Origin, Permission},
    error_analysis::{ErrorPropagation, ExprLoc, Indicator},
    file_analysis::{self, LocId, UnsupportedReason},
    fprintf,
    hir_ctx::{HirCtx, HirLoc},
    mir_loc::MirLoc,
    stream_ty::*,
    transform::LibItem,
};
use crate::{
    bit_set::{BitSet8, BitSet16},
    ir_util,
};

pub(super) struct TransformVisitor<'tcx, 'a, 'b> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) type_arena: &'a TypeArena<'a>,
    pub(super) analysis_res: &'a file_analysis::AnalysisResult<'a>,
    pub(super) hir: &'a HirCtx,

    pub(super) error_returning_fns: &'a FxHashMap<LocalDefId, Vec<(&'a ExprLoc, Indicator)>>,
    pub(super) error_taking_fns: &'a FxHashMap<LocalDefId, Vec<(&'a ExprLoc, Indicator)>>,
    pub(super) tracked_loc_to_index: &'a FxHashMap<&'a ExprLoc, usize>,

    pub(super) hir_loc_to_loc_id: &'a FxHashMap<HirLoc, LocId>,

    /// function parameter to HIR location
    pub(super) param_to_loc: &'a FxHashMap<Parameter, HirLoc>,
    /// HIR location to permissions and origins
    pub(super) loc_to_pot: &'a FxHashMap<HirLoc, Pot<'a>>,
    /// user-defined API functions' signatures' spans
    pub(super) api_ident_spans: &'a FxHashSet<Span>,
    /// uncopiable struct ident span to field indices
    pub(super) uncopiable: &'a FxHashMap<Span, Vec<FieldIdx>>,
    /// spans of projections of manually dropped fields
    pub(super) manually_drop_projections: &'a FxHashSet<Span>,

    /// unsupported expr span to location
    pub(super) unsupported: &'b mut FxHashMap<Span, MirLoc>,
    /// unsupported return fn ids
    pub(super) unsupported_returns: &'a FxHashSet<LocalDefId>,
    /// is stdin unsupported
    pub(super) is_stdin_unsupported: bool,
    /// is stdout unsupported
    pub(super) is_stdout_unsupported: bool,
    /// is stderr unsupported
    pub(super) is_stderr_unsupported: bool,

    /// is this file updated
    pub(super) updated: bool,
    pub(super) tmpfile: bool,
    pub(super) current_fns: Vec<LocalDefId>,
    pub(super) bounds: Vec<TraitBound>,
    pub(super) bound_num: usize,
    pub(super) lib_items: RefCell<Vec<LibItem>>,
    pub(super) parsing_fns: RefCell<Vec<(String, String)>>,
    pub(super) guards: FxHashSet<Symbol>,
    pub(super) foreign_statics: FxHashSet<&'static str>,
    pub(super) unsupported_reasons: Vec<BitSet16<UnsupportedReason>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Parameter {
    pub(super) func: LocalDefId,
    pub(super) index: usize,
}

impl Parameter {
    #[inline]
    pub(super) fn new(func: LocalDefId, index: usize) -> Self {
        Self { func, index }
    }
}

fn remove_cast(expr: &Expr) -> &Expr {
    let ExprKind::Cast(expr, _) = &expr.kind else { return expr };
    remove_cast(expr)
}

impl<'a> TransformVisitor<'_, 'a, '_> {
    fn loc_if_unsupported(&self, expr: &Expr) -> Option<MirLoc> {
        self.unsupported
            .get(&expr.span)
            .or_else(|| self.unsupported.get(&remove_cast(expr).span))
            .or_else(|| {
                let ExprKind::Unary(UnOp::Deref, rhs) = &expr.kind else { return None };
                let ExprKind::MethodCall(box call) = &rhs.kind else { return None };
                self.unsupported.get(&call.receiver.span)
            })
            .copied()
    }

    #[inline]
    fn is_unsupported(&self, expr: &Expr) -> bool {
        self.loc_if_unsupported(expr).is_some()
    }

    #[inline]
    fn param_pot(&self, param: Parameter) -> Option<Pot<'a>> {
        let loc = self.param_to_loc.get(&param)?;
        self.loc_to_pot.get(loc).copied()
    }

    #[inline]
    fn bound_pot(&self, span: Span) -> Option<Pot<'a>> {
        let loc = self.hir.bound_span_to_loc.get(&span)?;
        self.loc_to_pot.get(loc).copied()
    }

    fn bound_expr_pot(&self, expr: &Expr) -> Option<Pot<'a>> {
        match &expr.kind {
            ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e) => {
                let mut pot = self.bound_expr_pot(e)?;
                pot.ty = self.type_arena.ref_(pot.ty);
                Some(pot)
            }
            ExprKind::Unary(UnOp::Deref, e) => {
                let mut pot = self.bound_expr_pot(e)?;
                let (StreamType::Ref(ty) | StreamType::Ptr(ty)) = pot.ty else { panic!() };
                pot.ty = ty;
                Some(pot)
            }
            ExprKind::Paren(e) | ExprKind::Index(e, _, _) => {
                self.bound_pot(expr.span).or_else(|| self.bound_expr_pot(e))
            }
            _ => self.bound_pot(expr.span),
        }
    }

    #[inline]
    fn bound_origins(&self, span: Span) -> Option<BitSet8<Origin>> {
        let hir_loc = self.hir.bound_span_to_loc.get(&span)?;
        let loc_id = self.hir_loc_to_loc_id.get(hir_loc)?;
        Some(self.analysis_res.origins[*loc_id])
    }

    fn bound_expr_origins(&self, expr: &Expr) -> Option<BitSet8<Origin>> {
        match &expr.kind {
            ExprKind::Index(e, _, _)
            | ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e)
            | ExprKind::Unary(UnOp::Deref, e) => self.bound_expr_origins(e),
            ExprKind::Paren(e) => self
                .bound_origins(expr.span)
                .or_else(|| self.bound_expr_origins(e)),
            _ => self.bound_origins(expr.span),
        }
    }

    #[inline]
    fn binding_pot(&self, span: Span) -> Option<Pot<'a>> {
        let loc = self.hir.binding_span_to_loc.get(&span)?;
        self.loc_to_pot.get(loc).copied()
    }

    #[inline]
    fn return_pot(&self, func: LocalDefId) -> Option<Pot<'a>> {
        if self.unsupported_returns.contains(&func) {
            return None;
        }
        self.loc_to_pot.get(&HirLoc::Return(func)).copied()
    }

    #[inline]
    fn current_fn(&self) -> LocalDefId {
        *self.current_fns.last().unwrap()
    }

    fn indicator_check(&self, expr: &Expr) -> IndicatorCheck<'_> {
        if let Some(expr_loc) = self.analysis_res.span_to_expr_loc.get(&expr.span) {
            let name = Some(*expr_loc);
            let func = self.current_fn();
            let mut eof = false;
            let mut error = false;
            if let Some(vars) = self.analysis_res.tracking_fns.get(&func) {
                for (loc, indicator) in vars {
                    if loc == expr_loc {
                        match indicator {
                            Indicator::Eof => eof = true,
                            Indicator::Error => error = true,
                        }
                    }
                }
            }
            IndicatorCheck { name, eof, error }
        } else {
            IndicatorCheck::default()
        }
    }

    #[inline]
    fn indicator_check_std<'s>(&self, _name: &'s str) -> IndicatorCheck<'s> {
        IndicatorCheck::default()
    }

    #[inline]
    fn replace_expr(&mut self, old: &mut Expr, new: Expr) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn replace_ty_with_pot(&mut self, old: &mut Ty, pot: Pot<'_>) {
        if let Some(bound) = pot.ty.get_dyn_bound() {
            self.bound_num += 1;
            self.bounds.push(bound);
        }
        self.replace_ty(old, ty!("{}", pot.ty));
    }

    #[inline]
    fn replace_ty(&mut self, old: &mut Ty, new: Ty) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn replace_ident(&mut self, old: &mut Ident, new: Ident) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn is_non_local(&self, span: Span) -> bool {
        matches!(
            self.hir.bound_span_to_loc.get(&span),
            Some(HirLoc::Global(_) | HirLoc::Field(_, _))
        )
    }

    fn convert_rhs(&mut self, rhs: &mut Expr, lhs_pot: Pot<'_>) {
        let mut consume = lhs_pot.permissions.contains(Permission::Close)
            || matches!(rhs.kind, ExprKind::Call(_, _) | ExprKind::MethodCall(_));
        let rhs_span = rhs.span;
        let is_non_local = self.is_non_local(rhs_span);
        if let Some(rhs_pot) = self.bound_expr_pot(rhs) {
            let rhs_str = pprust::expr_to_string(rhs);
            consume |= rhs_pot.ty.must_std();
            let new_rhs = convert_expr(*lhs_pot.ty, *rhs_pot.ty, &rhs_str, consume, is_non_local);
            let new_rhs = expr!("{}", new_rhs);
            self.replace_expr(rhs, new_rhs);
        } else if let Some(def_id) = self.hir.call_span_to_callee_id.get(&rhs_span) {
            let name = ir_util::def_id_to_symbol(*def_id, self.tcx).unwrap();
            let name = api_list::normalize_api_name(name.as_str());
            let rhs_str = pprust::expr_to_string(rhs);
            let rhs_ty = match name {
                "fopen" | "tmpfile" => StreamType::Option(&FILE_TY),
                "fdopen" => FILE_TY,
                "popen" => StreamType::Option(&CHILD_TY),
                _ => *self.return_pot(*def_id).unwrap().ty,
            };
            consume |= rhs_ty.must_std();
            let new_rhs = convert_expr(*lhs_pot.ty, rhs_ty, &rhs_str, consume, is_non_local);
            let new_rhs = expr!("{}", new_rhs);
            self.replace_expr(rhs, new_rhs);
        } else {
            match &mut rhs.kind {
                ExprKind::If(_, t, Some(f)) => {
                    let StmtKind::Expr(t) = &mut t.stmts.last_mut().unwrap().kind else { panic!() };
                    self.convert_rhs(t, lhs_pot);

                    let ExprKind::Block(f, _) = &mut f.kind else { panic!() };
                    let StmtKind::Expr(f) = &mut f.stmts.last_mut().unwrap().kind else { panic!() };
                    self.convert_rhs(f, lhs_pot);
                }
                ExprKind::Cast(_, _) => {
                    assert!(matches!(remove_cast(rhs).kind, ExprKind::Lit(_)));
                    match lhs_pot.ty {
                        StreamType::Option(_) => {
                            self.replace_expr(rhs, expr!("None"));
                        }
                        StreamType::Ptr(_) => {
                            self.replace_expr(rhs, expr!("std::ptr::null_mut()"));
                        }
                        _ => panic!(),
                    }
                }
                ExprKind::Call(callee, _) => {
                    if let ExprKind::Path(_, path) = &callee.kind {
                        let name = path.segments.last().unwrap().ident;
                        if name.as_str() == "Some" {
                            return;
                        }
                    }
                    panic!("{:?}", rhs.span);
                }
                ExprKind::Path(_, path) => {
                    let name = path.segments.last().unwrap().ident;
                    if name.as_str() == "None" {
                        return;
                    }
                    panic!("{:?}", rhs.span);
                }
                ExprKind::Repeat(rhs, _) => {
                    self.convert_rhs(rhs, lhs_pot);
                    let rhs_str = pprust::expr_to_string(rhs);
                    **rhs = expr!("const {{ {rhs_str} }}");
                }
                _ => panic!("{:?}", rhs.span),
            }
        }
    }

    fn replace_fn_ptr_param_type(&mut self, ty: &mut Ty, pot: Pot<'_>, index: usize) {
        let TyKind::Path(_, path) = &mut ty.kind else { panic!() };
        let seg = path.segments.last_mut().unwrap();
        assert_eq!(seg.ident.as_str(), "Option");
        let args = seg.args.as_mut().unwrap();
        let AngleBracketed(args) = args.deref_mut() else { panic!() };
        let [arg] = &mut args.args[..] else { panic!() };
        let AngleBracketedArg::Arg(arg) = arg else { panic!() };
        let GenericArg::Type(ty) = arg else { panic!() };
        let TyKind::BareFn(fn_ty) = &mut ty.kind else { panic!() };
        let param = &mut fn_ty.decl.inputs[index];
        self.replace_ty_with_pot(&mut param.ty, pot);
    }

    fn replace_array_type(&mut self, ty: &mut Ty, pot: Pot<'_>) -> bool {
        let TyKind::Array(ty, _) = &mut ty.kind else { return false };
        self.replace_ty_with_pot(ty, pot);
        true
    }

    fn can_propagate(
        &self,
        caller: LocalDefId,
        caller_loc: &'a ExprLoc,
        callee: LocalDefId,
        callee_loc: &'a ExprLoc,
    ) -> bool {
        self.analysis_res
            .propagations
            .contains(&ErrorPropagation::new(
                caller, caller_loc, callee, callee_loc,
            ))
    }

    fn stdin_unsuppoted_reasons(&self) -> BitSet16<UnsupportedReason> {
        let loc_id = self.analysis_res.loc_ind_map[&MirLoc::Stdin];
        self.analysis_res.unsupported.get_reasons(loc_id)
    }

    fn stdout_unsuppoted_reasons(&self) -> BitSet16<UnsupportedReason> {
        let loc_id = self.analysis_res.loc_ind_map[&MirLoc::Stdout];
        self.analysis_res.unsupported.get_reasons(loc_id)
    }

    fn stderr_unsuppoted_reasons(&self) -> BitSet16<UnsupportedReason> {
        let loc_id = self.analysis_res.loc_ind_map[&MirLoc::Stderr];
        self.analysis_res.unsupported.get_reasons(loc_id)
    }

    fn get_unsupported_reasons(&self, loc: MirLoc) -> BitSet16<UnsupportedReason> {
        let loc_id = self.analysis_res.loc_ind_map[&loc];
        self.analysis_res.unsupported.get_reasons(loc_id)
    }

    fn should_prevent_drop(&self, lhs: &Expr) -> bool {
        if self.manually_drop_projections.contains(&lhs.span) {
            return true;
        }
        let (ExprKind::Paren(e) | ExprKind::Field(e, _)) = &lhs.kind else { return false };
        self.should_prevent_drop(e)
    }
}

impl MutVisitor for TransformVisitor<'_, '_, '_> {
    fn visit_crate(&mut self, c: &mut Crate) {
        mut_visit::walk_crate(self, c);

        if !self.foreign_statics.is_empty() {
            let foreign_mod = c
                .items
                .iter_mut()
                .find_map(|item| {
                    if let ItemKind::ForeignMod(foreign_mod) = &mut item.kind {
                        Some(foreign_mod)
                    } else {
                        None
                    }
                })
                .unwrap();
            for name in self.foreign_statics.drain() {
                if foreign_mod.items.iter().any(|item| {
                    let ForeignItemKind::Static(box StaticItem { ident, .. }) = item.kind else {
                        return false;
                    };
                    ident.as_str() == name
                }) {
                    continue;
                }
                let item = item!("static mut {}: *mut FILE;", name);
                let ItemKind::Static(static_item) = item.kind else { panic!() };
                let foreign_item = ForeignItem {
                    attrs: item.attrs,
                    id: item.id,
                    span: item.span,
                    vis: item.vis,
                    kind: ForeignItemKind::Static(static_item),
                    tokens: item.tokens,
                };
                foreign_mod.items.push(P(foreign_item));
            }
        }
    }

    fn visit_item(&mut self, item: &mut Item) {
        if let ItemKind::Fn(box Fn { ident, .. }) = item.kind
            && self.api_ident_spans.contains(&ident.span)
        {
            return;
        }

        let is_fn = if let ItemKind::Fn(box Fn { ident, .. }) = item.kind
            && let Some(HirLoc::Global(def_id)) = self.hir.binding_span_to_loc.get(&ident.span)
        {
            self.current_fns.push(*def_id);
            true
        } else {
            false
        };

        mut_visit::walk_item(self, item);

        if is_fn {
            self.current_fns.pop();
        }

        match &mut item.kind {
            ItemKind::Static(box item) => {
                let ident_span = item.ident.span;
                let body = some_or!(&mut item.expr, return);
                if self.unsupported.contains_key(&body.span) {
                    return;
                }
                let loc = self.hir.binding_span_to_loc[&ident_span];
                let pot = some_or!(self.loc_to_pot.get(&loc), return);
                if let Some(index) = pot.file_param_index {
                    // When the variable type is Option<fn(..) -> ..>
                    self.replace_fn_ptr_param_type(&mut item.ty, *pot, index);
                } else if !self.replace_array_type(&mut item.ty, *pot) {
                    self.replace_ty_with_pot(&mut item.ty, *pot);
                    self.convert_rhs(body, *pot);
                }
            }
            ItemKind::Fn(box item) => {
                let ident_span = item.ident.span;
                let HirLoc::Global(def_id) = self.hir.binding_span_to_loc[&ident_span] else {
                    panic!()
                };
                let mut tparams = vec![];
                for (i, param) in item.sig.decl.inputs.iter_mut().enumerate() {
                    if self.unsupported.contains_key(&param.pat.span) {
                        continue;
                    }
                    let p = Parameter::new(def_id, i);
                    let pot = some_or!(self.param_pot(p), continue);
                    if let Some(index) = pot.file_param_index {
                        // When the parameter type is Option<fn(..) -> ..>
                        self.replace_fn_ptr_param_type(&mut param.ty, pot, index);
                    } else if let StreamType::Option(StreamType::Impl(bound)) = pot.ty {
                        self.replace_ty(&mut param.ty, ty!("Option<TT{}>", i));
                        tparams.push((i, *bound));
                    } else if let StreamType::Option(StreamType::Ptr(StreamType::Impl(bound))) =
                        pot.ty
                    {
                        self.replace_ty(&mut param.ty, ty!("Option<*mut TT{}>", i));
                        tparams.push((i, *bound));
                    } else if !self.replace_array_type(&mut param.ty, pot) {
                        self.replace_ty_with_pot(&mut param.ty, pot);
                    }
                    if let PatKind::Ident(BindingMode(_, m), _, _) = &mut param.pat.kind {
                        *m = Mutability::Mut;
                    }
                }
                for (i, bound) in tparams {
                    let tparam = if bound.is_empty() {
                        ty_param!("TT{}", i)
                    } else {
                        ty_param!("TT{}: {}", i, bound)
                    };
                    item.generics.params.push(tparam);
                }
                if let Some(returns) = self.error_returning_fns.get(&def_id) {
                    match &mut item.sig.decl.output {
                        FnRetTy::Ty(ty) => {
                            let mut new_ty = pprust::ty_to_string(ty);
                            for _ in returns {
                                new_ty.push_str(", i32");
                            }
                            let new_ty = ty!("({})", new_ty);
                            self.replace_ty(ty, new_ty);
                        }
                        FnRetTy::Default(_) => {
                            if returns.len() == 1 {
                                let ty = ty!("i32");
                                item.sig.decl.output = FnRetTy::Ty(P(ty));
                            } else {
                                let mut ty = "i32".to_string();
                                for _ in 1..returns.len() {
                                    ty.push_str(", i32");
                                }
                                let ty = ty!("({})", ty);
                                item.sig.decl.output = FnRetTy::Ty(P(ty));
                            }
                            let mut rv = String::new();
                            for (i, (loc, indicator)) in returns.iter().enumerate() {
                                if i != 0 {
                                    rv.push_str(", ");
                                }
                                let ind = self.tracked_loc_to_index[loc];
                                write!(rv, "___v_{ind}_{indicator}").unwrap();
                            }
                            if returns.len() != 1 {
                                rv = format!("({rv})");
                            }
                            let stmt = stmt!("return {};", rv);
                            let stmts = &mut item.body.as_mut().unwrap().stmts;
                            stmts.push(stmt);
                            self.updated = true;
                        }
                    }
                }
                if let Some(params) = self.error_taking_fns.get(&def_id) {
                    for (loc, indicator) in params {
                        let ind = self.tracked_loc_to_index[loc];
                        let param = param!("mut ___v_{}_{}: i32", ind, indicator);
                        item.sig.decl.inputs.push(param);
                        self.updated = true;
                    }
                }
                if let Some(pot) = self.return_pot(def_id) {
                    let FnRetTy::Ty(ty) = &mut item.sig.decl.output else { panic!() };
                    self.replace_ty_with_pot(ty, pot);
                }
                if let Some(vars) = self.analysis_res.tracking_fns.get(&def_id) {
                    let stmts = &mut item.body.as_mut().unwrap().stmts;
                    for var in vars {
                        if self
                            .error_taking_fns
                            .get(&def_id)
                            .is_some_and(|params| params.contains(var))
                        {
                            continue;
                        }
                        let (loc, indicator) = var;
                        let ind = self.tracked_loc_to_index[loc];
                        let stmt = stmt!("let mut ___v_{}_{} = 0;", ind, indicator);
                        stmts.insert(0, stmt);
                    }
                }
                for name in self.guards.drain() {
                    let stmts = &mut item.body.as_mut().unwrap().stmts;
                    let stmt = stmt!("let mut {}_guard;", name);
                    stmts.insert(0, stmt);
                }
            }
            ItemKind::Struct(ident, _, _) | ItemKind::Union(ident, _, _) => {
                if let Some(field_indices) = self.uncopiable.get(&ident.span) {
                    for attr in &mut item.attrs {
                        let AttrKind::Normal(attr) = &mut attr.kind else { continue };
                        let AttrArgs::Delimited(args) = &mut attr.item.args else { continue };
                        let mut tokens = vec![];
                        let mut remove_comma = false;
                        for tree in args.tokens.iter() {
                            if let TokenTree::Token(token, _) = tree {
                                match token.kind {
                                    TokenKind::Ident(symbol, _) => {
                                        let name = symbol.as_str();
                                        if name == "Copy" || name == "Clone" {
                                            remove_comma = true;
                                            continue;
                                        }
                                    }
                                    TokenKind::Comma => {
                                        if remove_comma {
                                            remove_comma = false;
                                            continue;
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            tokens.push(tree.clone());
                        }
                        args.tokens = TokenStream::new(tokens);
                    }
                    if let ItemKind::Union(_, _, vd) = &mut item.kind {
                        let VariantData::Struct { fields, .. } = vd else { panic!() };
                        for i in field_indices {
                            let field = &mut fields[i.as_usize()];
                            if self.binding_pot(field.span).is_some() {
                                continue;
                            }
                            let ty = pprust::ty_to_string(&field.ty);
                            let new_ty = ty!("std::mem::ManuallyDrop<{}>", ty);
                            self.replace_ty(&mut field.ty, new_ty);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_variant_data(&mut self, vd: &mut VariantData) {
        mut_visit::walk_variant_data(self, vd);

        let VariantData::Struct { fields, .. } = vd else { return };
        for f in fields {
            if self.unsupported.contains_key(&f.span) {
                continue;
            }
            let pot = some_or!(self.binding_pot(f.span), continue);
            if let Some(index) = pot.file_param_index {
                // When the file type is Option<fn(..) -> ..>
                self.replace_fn_ptr_param_type(&mut f.ty, pot, index);
            } else if !self.replace_array_type(&mut f.ty, pot) {
                self.replace_ty_with_pot(&mut f.ty, pot);
            }
        }
    }

    fn visit_local(&mut self, local: &mut Local) {
        mut_visit::walk_local(self, local);

        if self.unsupported.contains_key(&local.pat.span) {
            return;
        }
        if let LocalKind::Init(rhs) = &mut local.kind
            && self.is_unsupported(rhs)
        {
            return;
        }

        let mut pot = some_or!(self.binding_pot(local.pat.span), return);
        if let PatKind::Ident(BindingMode(ByRef::Yes(_), _), _, _) = local.pat.kind {
            let StreamType::Ptr(ty) = pot.ty else { panic!() };
            pot.ty = ty;
        }

        if let Some(ty) = local.ty.as_mut() {
            if let Some(index) = pot.file_param_index {
                // When the file type is Option<fn(..) -> ..>
                self.replace_fn_ptr_param_type(ty, pot, index);
            } else if !self.replace_array_type(ty, pot) {
                self.replace_ty_with_pot(ty, pot);
            }
        } else {
            if let Some(bound) = pot.ty.get_dyn_bound() {
                self.bound_num += 1;
                self.bounds.push(bound);
            }
            self.updated = true;
            local.ty = Some(P(ty!("{}", pot.ty)));
        }

        let LocalKind::Init(rhs) = &mut local.kind else { return };
        self.convert_rhs(rhs, pot);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let ExprKind::If(_, t, Some(f)) = &expr.kind
            && let Some(loc) = self.loc_if_unsupported(expr)
        {
            let t = t.stmts.last().unwrap();
            let StmtKind::Expr(t) = &t.kind else { panic!() };
            self.unsupported.insert(t.span, loc);
            self.unsupported.insert(f.span, loc);
        }

        mut_visit::walk_expr(self, expr);

        if let Some(loc) = self.loc_if_unsupported(expr) {
            if let ExprKind::Call(callee, _) = &expr.kind
                && let Some(HirLoc::Global(def_id)) = self.hir.bound_span_to_loc.get(&callee.span)
            {
                let name = ir_util::def_id_to_symbol(*def_id, self.tcx).unwrap();
                let name = name.as_str();
                let name = api_list::normalize_api_name(name);
                if name == "fopen"
                    || name == "fdopen"
                    || name == "tmpfile"
                    || name == "popen"
                    || name == "fmemopen"
                    || name == "open_memstream"
                    || name == "freopen"
                {
                    let reasons = self.get_unsupported_reasons(loc);
                    self.unsupported_reasons.push(reasons);
                }
            }
            return;
        }

        let expr_span = expr.span;
        match &mut expr.kind {
            ExprKind::Call(callee, args) => {
                if let Some(HirLoc::Global(def_id)) = self.hir.bound_span_to_loc.get(&callee.span) {
                    let orig_name = ir_util::def_id_to_symbol(*def_id, self.tcx).unwrap();
                    let orig_name = orig_name.as_str();
                    let name = api_list::normalize_api_name(orig_name);
                    match name {
                        "fopen" => {
                            let new_expr = self.transform_fopen(&args[0], &args[1]);
                            self.replace_expr(expr, new_expr);
                        }
                        "fdopen" => {
                            let new_expr = self.transform_fdopen(&args[0]);
                            self.replace_expr(expr, new_expr);
                        }
                        "tmpfile" => {
                            let new_expr = self.transform_tmpfile();
                            self.replace_expr(expr, new_expr);
                            self.tmpfile = true;
                        }
                        "popen" => {
                            let new_expr = self.transform_popen(&args[0], &args[1]);
                            self.replace_expr(expr, new_expr);
                        }
                        "fmemopen" | "open_memstream" => todo!(),
                        "fclose" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let is_non_local = self.is_non_local(args[0].span);
                            let new_expr = self.transform_fclose(&args[0], *ty, is_non_local);
                            self.replace_expr(expr, new_expr);
                        }
                        "pclose" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let is_non_local = self.is_non_local(args[0].span);
                            let new_expr = self.transform_pclose(&args[0], *ty, is_non_local);
                            self.replace_expr(expr, new_expr);
                        }
                        "scanf" => {
                            if self.is_stdin_unsupported {
                                let reasons = self.stdin_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let stream = StdExpr::stdin();
                            let ic = self.indicator_check(&args[0]);
                            let new_expr = self.transform_fscanf(&stream, &args[0], &args[1..], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "fscanf" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let ic = self.indicator_check(&args[0]);
                            let new_expr = self.transform_fscanf(&stream, &args[1], &args[2..], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "vfscanf" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            todo!()
                        }
                        "fgetc" | "getc" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let ic = self.indicator_check(&args[0]);
                            let new_expr = self.transform_fgetc(&stream, ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "getchar" => {
                            if self.is_stdin_unsupported {
                                let reasons = self.stdin_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let stream = StdExpr::stdin();
                            let ic = self.indicator_check_std("stdin");
                            let new_expr = self.transform_fgetc(&stream, ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "fgets" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[2]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[2]).unwrap().ty;
                            let stream = TypedExpr::new(&args[2], ty);
                            let ic = self.indicator_check(&args[2]);
                            let new_expr = self.transform_fgets(&stream, &args[0], &args[1], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "fread" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[3]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[3]).unwrap().ty;
                            let stream = TypedExpr::new(&args[3], ty);
                            let ic = self.indicator_check(&args[3]);
                            let new_expr =
                                self.transform_fread(&stream, &args[0], &args[1], &args[2], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "getdelim" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[3]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[3]).unwrap().ty;
                            let stream = TypedExpr::new(&args[3], ty);
                            let ic = self.indicator_check(&args[3]);
                            let new_expr =
                                self.transform_getdelim(&stream, &args[0], &args[1], &args[2], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "getline" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[2]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[2]).unwrap().ty;
                            let stream = TypedExpr::new(&args[2], ty);
                            let ic = self.indicator_check(&args[2]);
                            let new_expr = self.transform_getline(&stream, &args[0], &args[1], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "feof" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let name = self.analysis_res.span_to_expr_loc[&args[0].span];
                            let ind = self.tracked_loc_to_index[&name];
                            let new_expr = expr!("___v_{}_eof", ind);
                            self.replace_expr(expr, new_expr);
                        }
                        "ferror" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let origins = self.bound_expr_origins(&args[0]);
                                let (new_expr, rem) =
                                    self.transform_unsupported_ferror(orig_name, &args[0], origins);
                                if rem {
                                    let reasons = self.get_unsupported_reasons(loc);
                                    self.unsupported_reasons.push(reasons);
                                }
                                if let Some(new_expr) = new_expr {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            let name = self.analysis_res.span_to_expr_loc[&args[0].span];
                            let ind = self.tracked_loc_to_index[&name];
                            let new_expr = expr!("___v_{}_error", ind);
                            self.replace_expr(expr, new_expr);
                        }
                        "clearerr" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ic = self.indicator_check(&args[0]);
                            let new_expr = expr!("{}", self.clear(ic));
                            self.replace_expr(expr, new_expr);
                        }
                        "fprintf" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                let origins = self.bound_expr_origins(&args[0]);
                                self.lib_items.borrow_mut().extend(fprintf::FPRINTF_ITEMS);
                                if let Some(new_expr) = self.transform_unsupported(
                                    "rs_fprintf",
                                    orig_name,
                                    &[],
                                    &args[0],
                                    &args[1..],
                                    origins,
                                ) {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let retval_used = self.hir.retval_used_spans.contains(&expr_span);
                            let ic = self.indicator_check(&args[0]);
                            let ctx = fprintf::FprintfCtx {
                                wide: false,
                                retval_used,
                                ic,
                            };
                            let new_expr =
                                self.transform_fprintf(&stream, &args[1], &args[2..], ctx);
                            self.replace_expr(expr, new_expr);
                        }
                        "printf" => {
                            if self.is_stdout_unsupported {
                                let reasons = self.stdout_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let stream = StdExpr::stdout();
                            let retval_used = self.hir.retval_used_spans.contains(&expr_span);
                            let ic = self.indicator_check_std("stdout");
                            let ctx = fprintf::FprintfCtx {
                                wide: false,
                                retval_used,
                                ic,
                            };
                            let new_expr =
                                self.transform_fprintf(&stream, &args[0], &args[1..], ctx);
                            self.replace_expr(expr, new_expr);
                        }
                        "wprintf" => {
                            if self.is_stdout_unsupported {
                                let reasons = self.stdout_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let stream = StdExpr::stdout();
                            let retval_used = self.hir.retval_used_spans.contains(&expr_span);
                            let ic = self.indicator_check_std("stdout");
                            let ctx = fprintf::FprintfCtx {
                                wide: true,
                                retval_used,
                                ic,
                            };
                            let new_expr =
                                self.transform_fprintf(&stream, &args[0], &args[1..], ctx);
                            self.replace_expr(expr, new_expr);
                        }
                        "vfprintf" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                let origins = self.bound_expr_origins(&args[0]);
                                self.lib_items.borrow_mut().extend(fprintf::VFPRINTF_ITEMS);
                                if let Some(new_expr) = self.transform_unsupported(
                                    "rs_vfprintf",
                                    orig_name,
                                    &[],
                                    &args[0],
                                    &args[1..],
                                    origins,
                                ) {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let ic = self.indicator_check(&args[0]);
                            let new_expr = self.transform_vfprintf(&stream, &args[1], &args[2], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "vprintf" => {
                            if self.is_stdout_unsupported {
                                let reasons = self.stdout_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let stream = StdExpr::stdout();
                            let ic = self.indicator_check_std("stdout");
                            let new_expr = self.transform_vfprintf(&stream, &args[0], &args[1], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "fputc" | "putc" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[1]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                let origins = self.bound_expr_origins(&args[1]);
                                self.lib_items.borrow_mut().push(LibItem::Fputc);
                                if let Some(new_expr) = self.transform_unsupported(
                                    "rs_fputc",
                                    orig_name,
                                    &args[0..1],
                                    &args[1],
                                    &[],
                                    origins,
                                ) {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[1]).unwrap().ty;
                            let stream = TypedExpr::new(&args[1], ty);
                            let ic = self.indicator_check(&args[1]);
                            let new_expr = self.transform_fputc(&stream, &args[0], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "putchar" => {
                            if self.is_stdout_unsupported {
                                let reasons = self.stdout_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let stream = StdExpr::stdout();
                            let ic = self.indicator_check_std("stdout");
                            let new_expr = self.transform_fputc(&stream, &args[0], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "fputwc" | "putwc" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[1]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                let origins = self.bound_expr_origins(&args[1]);
                                self.lib_items.borrow_mut().push(LibItem::Fputwc);
                                if let Some(new_expr) = self.transform_unsupported(
                                    "rs_fputwc",
                                    orig_name,
                                    &args[0..1],
                                    &args[1],
                                    &[],
                                    origins,
                                ) {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[1]).unwrap().ty;
                            let stream = TypedExpr::new(&args[1], ty);
                            let ic = self.indicator_check(&args[1]);
                            let new_expr = self.transform_fputwc(&stream, &args[0], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "fputs" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[1]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                let origins = self.bound_expr_origins(&args[1]);
                                self.lib_items.borrow_mut().push(LibItem::Fputs);
                                if let Some(new_expr) = self.transform_unsupported(
                                    "rs_fputs",
                                    orig_name,
                                    &args[0..1],
                                    &args[1],
                                    &[],
                                    origins,
                                ) {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[1]).unwrap().ty;
                            let stream = TypedExpr::new(&args[1], ty);
                            let ic = self.indicator_check(&args[1]);
                            let new_expr = self.transform_fputs(&stream, &args[0], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "puts" => {
                            if self.is_stdout_unsupported {
                                let reasons = self.stdout_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ic = self.indicator_check_std("stdout");
                            let new_expr = self.transform_puts(&args[0], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "perror" => {
                            if self.is_stderr_unsupported {
                                let reasons = self.stderr_unsuppoted_reasons();
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let new_expr = self.transform_perror(&args[0]);
                            self.replace_expr(expr, new_expr);
                        }
                        "fwrite" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[3]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                let origins = self.bound_expr_origins(&args[3]);
                                self.lib_items.borrow_mut().push(LibItem::Fwrite);
                                if let Some(new_expr) = self.transform_unsupported(
                                    "rs_fwrite",
                                    orig_name,
                                    &args[0..3],
                                    &args[3],
                                    &[],
                                    origins,
                                ) {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[3]).unwrap().ty;
                            let stream = TypedExpr::new(&args[3], ty);
                            let ic = self.indicator_check(&args[3]);
                            let new_expr =
                                self.transform_fwrite(&stream, &args[0], &args[1], &args[2], ic);
                            self.replace_expr(expr, new_expr);
                        }
                        "fflush" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                let origins = self.bound_expr_origins(&args[0]);
                                self.lib_items.borrow_mut().push(LibItem::Fflush);
                                if let Some(new_expr) = self.transform_unsupported(
                                    "rs_fflush",
                                    orig_name,
                                    &args[..0],
                                    &args[0],
                                    &[],
                                    origins,
                                ) {
                                    self.replace_expr(expr, new_expr);
                                }
                                return;
                            }
                            if matches!(remove_cast(&args[0]).kind, ExprKind::Lit(_)) {
                                self.replace_expr(expr, expr!("0"));
                            } else {
                                let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                                let stream = TypedExpr::new(&args[0], ty);
                                let ic = self.indicator_check(&args[0]);
                                let new_expr = self.transform_fflush(&stream, ic);
                                self.replace_expr(expr, new_expr);
                            }
                        }
                        "fseek" | "fseeko" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let new_expr = self.transform_fseek(&stream, &args[1], &args[2]);
                            self.replace_expr(expr, new_expr);
                        }
                        "ftell" | "ftello" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let new_expr = self.transform_ftell(&stream);
                            self.replace_expr(expr, new_expr);
                        }
                        "rewind" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let new_expr = self.transform_rewind(&stream);
                            self.replace_expr(expr, new_expr);
                        }
                        "fgetpos" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            todo!()
                        }
                        "fsetpos" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            todo!()
                        }
                        "fileno" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let new_expr = self.transform_fileno(&stream);
                            self.replace_expr(expr, new_expr);
                        }
                        "flockfile" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let name = self.hir.callee_span_to_stream_name[&callee.span];
                            let (new_expr, guard) = self.transform_flockfile(&stream, name);
                            self.replace_expr(expr, new_expr);
                            if guard {
                                self.guards.insert(name);
                            }
                        }
                        "funlockfile" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            let ty = self.bound_expr_pot(&args[0]).unwrap().ty;
                            let stream = TypedExpr::new(&args[0], ty);
                            let name = self.hir.callee_span_to_stream_name[&callee.span];
                            let new_expr = self.transform_funlockfile(&stream, name);
                            self.replace_expr(expr, new_expr);
                        }
                        "rename" => {
                            let new_expr = expr!("crate::stdio::rs_rename");
                            self.lib_items.borrow_mut().push(LibItem::Rename);
                            self.replace_expr(callee, new_expr);
                        }
                        "remove" => {
                            let new_expr = expr!("crate::stdio::rs_remove");
                            self.lib_items.borrow_mut().push(LibItem::Remove);
                            self.replace_expr(callee, new_expr);
                        }
                        "setvbuf" | "setbuf" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[0]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            panic!()
                        }
                        "ungetc" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[1]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            panic!()
                        }
                        "freopen" => {
                            if let Some(loc) = self.loc_if_unsupported(&args[2]) {
                                let reasons = self.get_unsupported_reasons(loc);
                                self.unsupported_reasons.push(reasons);
                                return;
                            }
                            panic!()
                        }
                        _ => {
                            let hir::Node::Item(item) = self.tcx.hir_node_by_def_id(*def_id) else {
                                return;
                            };
                            let hir::ItemKind::Fn { sig, .. } = item.kind else { panic!() };
                            let mut targs = vec![];
                            for (i, arg) in args[..sig.decl.inputs.len()].iter_mut().enumerate() {
                                if self.loc_if_unsupported(arg).is_some() {
                                    continue;
                                }
                                let p = Parameter::new(*def_id, i);
                                let param_pot = some_or!(self.param_pot(p), continue);
                                let is_null = matches!(remove_cast(arg).kind, ExprKind::Lit(_));
                                let permissions = param_pot.permissions;
                                self.convert_rhs(arg, param_pot);
                                if param_pot.ty.contains_impl() {
                                    if is_null {
                                        let targ = if permissions.contains(Permission::BufRead) {
                                            "std::io::BufReader<std::fs::File>"
                                        } else {
                                            "std::fs::File"
                                        };
                                        targs.push(targ);
                                    } else {
                                        targs.push("_");
                                    }
                                }
                            }
                            if targs.iter().any(|targ| *targ != "_") {
                                let c = pprust::expr_to_string(callee);
                                let new_expr = expr!("{}::<{}>", c, targs.join(", "));
                                self.replace_expr(callee, new_expr);
                            }
                            if let Some(params) = self.error_taking_fns.get(def_id) {
                                let curr = self.current_fn();
                                let trackings = &self.analysis_res.tracking_fns[&curr];
                                for (param_loc, param_indicator) in params {
                                    let (loc, indicator) = trackings
                                        .iter()
                                        .find(|(var_loc, var_indicator)| {
                                            param_indicator == var_indicator
                                                && self.can_propagate(
                                                    curr, var_loc, *def_id, param_loc,
                                                )
                                        })
                                        .unwrap();
                                    let ind = self.tracked_loc_to_index[loc];
                                    let arg = expr!("___v_{}_{}", ind, indicator);
                                    args.push(P(arg));
                                    self.updated = true;
                                }
                            }
                            if let Some(returns) = self.error_returning_fns.get(def_id) {
                                let node = self.tcx.hir_node_by_def_id(*def_id);
                                let hir::Node::Item(item) = node else { panic!() };
                                let hir::ItemKind::Fn { sig, .. } = item.kind else { panic!() };
                                let mut vs = String::new();
                                let mut res = "";
                                if matches!(sig.decl.output, hir::FnRetTy::Return(_)) {
                                    vs.push_str("___v");
                                    res = "___v";
                                }
                                let mut multiple = false;
                                for i in 0..returns.len() {
                                    if !vs.is_empty() {
                                        vs.push_str(", ");
                                        multiple = true;
                                    }
                                    write!(vs, "___v{i}").unwrap();
                                }
                                if multiple {
                                    vs = format!("({vs})");
                                }

                                let mut assigns = String::new();
                                let curr = self.current_fn();
                                if let Some(trackings) = self.analysis_res.tracking_fns.get(&curr) {
                                    for (loc0, i0) in trackings {
                                        let ind = self.tracked_loc_to_index[loc0];
                                        for (i, (loc1, i1)) in returns.iter().enumerate() {
                                            if i0 == i1
                                                && self.can_propagate(curr, loc0, *def_id, loc1)
                                            {
                                                write!(assigns, "___v_{ind}_{i0} = ___v{i};")
                                                    .unwrap();
                                            }
                                        }
                                    }
                                }
                                let new_expr = expr!(
                                    "{{ let {} = {}; {} {} }}",
                                    vs,
                                    pprust::expr_to_string(expr),
                                    assigns,
                                    res
                                );
                                self.replace_expr(expr, new_expr);
                            }
                        }
                    }
                } else if let ExprKind::MethodCall(box call) = &callee.kind {
                    if call.seg.ident.as_str() != "unwrap" {
                        return;
                    }
                    let pot = some_or!(self.bound_expr_pot(&call.receiver), return);
                    if let Some(index) = pot.file_param_index {
                        let arg = &mut args[index];
                        if self.is_unsupported(arg) {
                            return;
                        }
                        self.convert_rhs(arg, pot);
                    }
                }
            }
            ExprKind::Path(None, path) => {
                if let [seg] = &path.segments[..] {
                    let name = seg.ident.name.as_str();
                    if (name == "stdin" && !self.is_stdin_unsupported)
                        || name == "stdout"
                        || name == "stderr"
                    {
                        let new_expr = expr!("std::io::{}()", name);
                        self.replace_expr(expr, new_expr);
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall { receiver, seg, .. }) => {
                if seg.ident.as_str() != "is_null" {
                    return;
                }
                if self.is_unsupported(receiver) {
                    return;
                }
                let ty = some_or!(self.bound_expr_pot(receiver), return).ty;
                match ty {
                    StreamType::ManuallyDrop(StreamType::Option(_)) | StreamType::Option(_) => {
                        self.replace_ident(&mut seg.ident, Ident::from_str("is_none"));
                    }
                    StreamType::Ptr(_) => {}
                    _ => panic!(),
                }
            }
            ExprKind::Assign(lhs, rhs, _) => {
                if self.is_unsupported(lhs) || self.is_unsupported(rhs) {
                    return;
                }
                let lhs_pot = some_or!(self.bound_expr_pot(lhs), return);
                self.convert_rhs(rhs, lhs_pot);

                let ic = self.indicator_check(lhs);
                let s = self.clear(ic);

                if self.should_prevent_drop(lhs) {
                    let lhs = pprust::expr_to_string(lhs);
                    let rhs = pprust::expr_to_string(rhs);
                    let new_expr = expr!("std::ptr::write(&mut ({}), {})", lhs, rhs);
                    self.replace_expr(expr, new_expr);
                }

                if s != "()" {
                    let expr_str = pprust::expr_to_string(expr);
                    let new_expr = expr!("{{ {}; {} }}", s, expr_str);
                    self.replace_expr(expr, new_expr);
                }
            }
            ExprKind::Struct(se) => {
                for f in se.fields.iter_mut() {
                    let lhs_pot = some_or!(self.bound_pot(f.ident.span), continue);
                    self.convert_rhs(&mut f.expr, lhs_pot);
                }
            }
            ExprKind::Ret(opt_e) => {
                let curr = self.current_fn();
                if let Some(e) = opt_e
                    && let Some(pot) = self.return_pot(curr)
                {
                    self.convert_rhs(e, pot);
                }
                if let Some(rets) = self.error_returning_fns.get(&curr) {
                    let mut new_v = String::new();
                    if let Some(e) = opt_e {
                        new_v.push_str(&pprust::expr_to_string(e));
                    }
                    for (loc, i) in rets {
                        if !new_v.is_empty() {
                            new_v.push_str(", ");
                        }
                        let ind = self.tracked_loc_to_index[loc];
                        write!(new_v, "___v_{ind}_{i}").unwrap();
                    }
                    let new_expr = expr!("return ({})", new_v);
                    self.replace_expr(expr, new_expr);
                }
            }
            ExprKind::Field(_, _) => {
                if self.manually_drop_projections.contains(&expr_span) {
                    let new_expr = expr!("(*({}))", pprust::expr_to_string(expr));
                    self.replace_expr(expr, new_expr);
                }
            }
            ExprKind::Cast(expr, ty) => {
                let loc = some_or!(self.hir.bound_span_to_loc.get(&expr.span), return);
                let HirLoc::Global(def_id) = loc else { return };
                let TyKind::BareFn(fn_ty) = &mut ty.kind else { return };
                for (i, param) in fn_ty.decl.inputs.iter_mut().enumerate() {
                    let p = Parameter::new(*def_id, i);
                    let pot = some_or!(self.param_pot(p), continue);
                    self.replace_ty_with_pot(&mut param.ty, pot);
                }
            }
            _ => {}
        }
    }
}

impl TransformVisitor<'_, '_, '_> {
    fn transform_unsupported<E: Deref<Target = Expr>>(
        &mut self,
        rs_name: &str,
        c_name: &str,
        before_args: &[E],
        stream: &Expr,
        after_args: &[E],
        origins: Option<BitSet8<Origin>>,
    ) -> Option<Expr> {
        let stdout =
            origins.is_none_or(|o| o.contains(Origin::Stdout)) && !self.is_stdout_unsupported;
        let stderr =
            origins.is_none_or(|o| o.contains(Origin::Stderr)) && !self.is_stderr_unsupported;
        if !stdout && !stderr {
            return None;
        }
        let stream = pprust::expr_to_string(stream);
        let mut new_expr = String::new();
        if stdout {
            self.foreign_statics.insert("stdout");
            if self.analysis_res.unsupported_stdout_errors {
                write!(
                    new_expr,
                    "if {stream} == stdout {{ let (___v, ___error) = crate::stdio::{rs_name}("
                )
                .unwrap();
                write_args(&mut new_expr, before_args, "std::io::stdout()", after_args);
                new_expr.push_str("); crate::stdio::STDOUT_ERROR = ___error; ___v } else ");
            } else {
                write!(
                    new_expr,
                    "if {stream} == stdout {{ crate::stdio::{rs_name}("
                )
                .unwrap();
                write_args(&mut new_expr, before_args, "std::io::stdout()", after_args);
                new_expr.push_str(").0 } else ");
            }
        }
        if stderr {
            self.foreign_statics.insert("stderr");
            if self.analysis_res.unsupported_stderr_errors {
                write!(
                    new_expr,
                    "if {stream} == stderr {{ let (___v, ___error) = crate::stdio::{rs_name}("
                )
                .unwrap();
                write_args(&mut new_expr, before_args, "std::io::stderr()", after_args);
                new_expr.push_str("); crate::stdio::STDERR_ERROR = ___error; ___v } else ");
            } else {
                write!(
                    new_expr,
                    "if {stream} == stderr {{ crate::stdio::{rs_name}("
                )
                .unwrap();
                write_args(&mut new_expr, before_args, "std::io::stderr()", after_args);
                new_expr.push_str(").0 } else ");
            }
        }
        write!(new_expr, "{{ {c_name}(").unwrap();
        write_args(&mut new_expr, before_args, &stream, after_args);
        new_expr.push_str(") }");
        Some(expr!("{}", new_expr))
    }

    fn transform_unsupported_ferror(
        &mut self,
        c_name: &str,
        stream: &Expr,
        origins: Option<BitSet8<Origin>>,
    ) -> (Option<Expr>, bool) {
        let stdout =
            origins.is_none_or(|o| o.contains(Origin::Stdout)) && !self.is_stdout_unsupported;
        let stderr =
            origins.is_none_or(|o| o.contains(Origin::Stderr)) && !self.is_stderr_unsupported;
        if !stdout && !stderr {
            return (None, true);
        }
        let stream = pprust::expr_to_string(stream);
        if stream == "stdout" {
            return (Some(expr!("crate::stdio::STDOUT_ERROR")), false);
        }
        if stream == "stderr" {
            return (Some(expr!("crate::stdio::STDERR_ERROR")), false);
        }
        let mut new_expr = String::new();
        if stdout {
            self.foreign_statics.insert("stdout");
            write!(
                new_expr,
                "if {stream} == stdout {{ crate::stdio::STDOUT_ERROR }} else ",
            )
            .unwrap();
        }
        if stderr {
            self.foreign_statics.insert("stderr");
            write!(
                new_expr,
                "if {stream} == stderr {{ crate::stdio::STDERR_ERROR }} else ",
            )
            .unwrap();
        }
        write!(new_expr, "{{ {c_name}({stream}) }}").unwrap();
        (Some(expr!("{}", new_expr)), true)
    }

    fn clear(&self, ic: IndicatorCheck<'_>) -> String {
        match (ic.eof, ic.error) {
            (true, true) => {
                let ind = self.tracked_loc_to_index[ic.name.unwrap()];
                format!("{{ ___v_{ind}_eof = 0; ___v_{ind}_error = 0; }}")
            }
            (true, false) => {
                let ind = self.tracked_loc_to_index[ic.name.unwrap()];
                format!("{{ ___v_{ind}_eof = 0; }}")
            }
            (false, true) => {
                let ind = self.tracked_loc_to_index[ic.name.unwrap()];
                format!("{{ ___v_{ind}_error = 0; }}")
            }
            (false, false) => "()".to_string(),
        }
    }

    pub(super) fn err_eof_args(&self, ic: IndicatorCheck<'_>) -> String {
        match (ic.error, ic.eof) {
            (true, true) => {
                let ind = self.tracked_loc_to_index[ic.name.unwrap()];
                format!("Some(&mut ___v_{ind}_error), Some(&mut ___v_{ind}_eof)")
            }
            (true, false) => {
                let ind = self.tracked_loc_to_index[ic.name.unwrap()];
                format!("Some(&mut ___v_{ind}_error), None")
            }
            (false, true) => {
                let ind = self.tracked_loc_to_index[ic.name.unwrap()];
                format!("None, Some(&mut ___v_{ind}_eof)")
            }
            (false, false) => "None, None".to_string(),
        }
    }

    pub(super) fn error_handling_no_eof<S: StreamExpr>(
        &self,
        ic: IndicatorCheck<'_>,
        stream: &S,
    ) -> String {
        let mut update = String::new();
        let ty = stream.ty();
        if ty.must_stdout() {
            if self.analysis_res.unsupported_stdout_errors {
                update.push_str("crate::stdio::STDOUT_ERROR = 1;");
            }
        } else if ty.must_stderr() {
            if self.analysis_res.unsupported_stderr_errors {
                update.push_str("crate::stdio::STDERR_ERROR = 1;");
            }
        } else if ty.may_std()
            && (self.analysis_res.unsupported_stdout_errors
                || self.analysis_res.unsupported_stderr_errors)
        {
            let stream = stream.borrow_for(StreamTrait::AsRawFd);
            self.lib_items.borrow_mut().push(LibItem::AsRawFd);
            write!(
                update,
                "{{ let fd = crate::stdio::AsRawFd::as_raw_fd({stream});"
            )
            .unwrap();
            if self.analysis_res.unsupported_stdout_errors {
                update.push_str("if fd == 1 { crate::stdio::STDOUT_ERROR = 1; }");
            }
            if self.analysis_res.unsupported_stderr_errors {
                update.push_str("if fd == 2 { crate::stdio::STDERR_ERROR = 1; }");
            }
            update.push('}');
        }
        if ic.error {
            let ind = self.tracked_loc_to_index[ic.name.unwrap()];
            write!(update, "___v_{ind}_error = 1;").unwrap();
        }
        update
    }

    pub(super) fn update_error_no_eof<S: StreamExpr>(
        &self,
        ic: IndicatorCheck<'_>,
        e: String,
        stream: &S,
    ) -> Expr {
        let mut update = String::new();
        let ty = stream.ty();
        if ty.must_stdout() {
            if self.analysis_res.unsupported_stdout_errors {
                update.push_str("crate::stdio::STDOUT_ERROR = ___error;");
            }
        } else if ty.must_stderr() {
            if self.analysis_res.unsupported_stderr_errors {
                update.push_str("crate::stdio::STDERR_ERROR = ___error;");
            }
        } else if ty.may_std()
            && (self.analysis_res.unsupported_stdout_errors
                || self.analysis_res.unsupported_stderr_errors)
        {
            let stream = stream.borrow_for(StreamTrait::AsRawFd);
            self.lib_items.borrow_mut().push(LibItem::AsRawFd);
            write!(
                update,
                "{{ let fd = crate::stdio::AsRawFd::as_raw_fd({stream});"
            )
            .unwrap();
            if self.analysis_res.unsupported_stdout_errors {
                update.push_str("if fd == 1 { crate::stdio::STDOUT_ERROR = ___error; }");
            }
            if self.analysis_res.unsupported_stderr_errors {
                update.push_str("if fd == 2 { crate::stdio::STDERR_ERROR = ___error; }");
            }
            update.push('}');
        }
        if ic.error {
            let ind = self.tracked_loc_to_index[ic.name.unwrap()];
            write!(update, "___v_{ind}_error = ___error;").unwrap();
        }
        if update.is_empty() {
            expr!("{}.0", e)
        } else {
            expr!("{{ let (___v, ___error) = {}; {}  ___v }}", e, update,)
        }
    }
}

fn write_args<E: Deref<Target = Expr>>(
    new_expr: &mut String,
    before_args: &[E],
    stream: &str,
    after_args: &[E],
) {
    for arg in before_args {
        let arg = pprust::expr_to_string(arg);
        write!(new_expr, "{arg}, ").unwrap();
    }
    new_expr.push_str(stream);
    for arg in after_args {
        let arg = pprust::expr_to_string(arg);
        write!(new_expr, ", {arg}").unwrap();
    }
}

#[derive(Debug, Default, Clone, Copy)]
pub(super) struct IndicatorCheck<'a> {
    name: Option<&'a ExprLoc>,
    eof: bool,
    error: bool,
}

pub(super) const RENAME: &str = r#"
#[inline]
pub(crate) unsafe fn rs_rename(old: *const i8, new: *const i8) -> i32 {
    let old = std::ffi::CStr::from_ptr(old as _).to_str().unwrap();
    let new = std::ffi::CStr::from_ptr(new as _).to_str().unwrap();
    std::fs::rename(old, new).map_or(-1, |_| 0)
}
"#;

pub(super) const REMOVE: &str = r#"
#[inline]
pub(crate) unsafe fn rs_remove(path: *const i8) -> i32 {
    let path = std::ffi::CStr::from_ptr(path as _).to_str().unwrap();
    match std::fs::remove_file(path) {
        Ok(()) => 0,
        Err(e) => {
            if e.kind() == std::io::ErrorKind::IsADirectory {
                std::fs::remove_dir(path).map_or(-1, |_| 0)
            } else {
                -1
            }
        }
    }
}
"#;
