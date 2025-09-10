use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def::DefKind};
use rustc_middle::{
    mir::{
        AggregateKind, Body, CastKind, Location, Place, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, UnOp,
    },
    thir::{self, ExprId, ExprKind, Pat, PatKind, Thir, visit::Visitor as TVisitor},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::{BytePos, Span};
use smallvec::{SmallVec, smallvec};

type Locations = SmallVec<[Location; 1]>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct LoHi {
    lo: BytePos,
    hi: BytePos,
}

impl From<Span> for LoHi {
    #[inline]
    fn from(span: Span) -> Self {
        Self {
            lo: span.lo(),
            hi: span.hi(),
        }
    }
}

impl From<LoHi> for Span {
    #[inline]
    fn from(lohi: LoHi) -> Self {
        Self::with_root_ctxt(lohi.lo, lohi.hi)
    }
}

impl std::fmt::Debug for LoHi {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let span: Span = (*self).into();
        span.fmt(f)
    }
}

pub fn map_thir_to_mir(tcx: TyCtxt<'_>) {
    for def_id in tcx.hir_body_owners() {
        if matches!(tcx.def_kind(def_id), DefKind::AnonConst) {
            continue;
        }
        if super::def_id_to_symbol(def_id, tcx).unwrap().as_str() == "main" {
            continue;
        }

        let (thir, texpr) = tcx.thir_body(def_id).unwrap();
        let thir = thir.borrow();
        let texpr = &thir[texpr];

        let mut visitor = ThirVisitor {
            tcx,
            thir: &thir,
            bindings: FxHashMap::default(),
        };
        for param in &thir.params {
            if let Some(pat) = &param.pat {
                visitor.visit_pat(pat);
            }
        }
        visitor.visit_expr(texpr);

        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body = body.borrow();

        let mut var_to_locals: FxHashMap<_, Vec<_>> = FxHashMap::default();
        for (local, local_decl) in body.local_decls.iter_enumerated() {
            let span = local_decl.source_info.span;
            if let Some(hir_id) = visitor.bindings.get(&span) {
                var_to_locals.entry(*hir_id).or_default().push(local);
            }
        }

        for binding in visitor.bindings.values() {
            let locals = var_to_locals.get(binding);
            if locals.is_none() {
                println!("{binding:?}");
            }
        }

        let mut stmt_span_to_locs: FxHashMap<LoHi, Locations> = FxHashMap::default();
        let mut term_span_to_locs: FxHashMap<LoHi, Locations> = FxHashMap::default();

        for (bb, bbd) in body.basic_blocks.iter_enumerated() {
            for (i, stmt) in bbd.statements.iter().enumerate() {
                if !matches!(stmt.kind, StatementKind::Assign { .. }) {
                    continue;
                }
                let location = Location {
                    block: bb,
                    statement_index: i,
                };
                stmt_span_to_locs
                    .entry(stmt.source_info.span.into())
                    .or_default()
                    .push(location);
            }
            let term = bbd.terminator();
            let location = Location {
                block: bb,
                statement_index: bbd.statements.len(),
            };
            term_span_to_locs
                .entry(term.source_info.span.into())
                .or_default()
                .push(location);
        }

        let mut ctx = Ctx {
            tcx,
            thir: &thir,
            body: &body,
            stmt_span_to_locs: &stmt_span_to_locs,
            term_span_to_locs: &term_span_to_locs,

            rhs_to_assigns: FxHashMap::default(),
            expr_id_to_locs: FxHashMap::default(),
        };

        for (expr_id, expr) in thir.exprs.iter_enumerated() {
            match expr.kind {
                ExprKind::Assign { lhs, rhs } => {
                    if let TyKind::Adt(adt_def, _) = thir[rhs].ty.kind()
                        && super::def_id_to_symbol(adt_def.did(), tcx)
                            .unwrap()
                            .as_str()
                            == "VaListImpl"
                    {
                    } else if let Some(assign) =
                        ctx.find_assign_location(thir[lhs].ty, expr.span.into())
                    {
                        ctx.expr_id_to_locs.insert(expr_id, smallvec![assign.loc]);
                        ctx.rhs_to_assigns
                            .insert(unwrap_scope_and_use(rhs, &thir), assign);
                    } else {
                        ctx.print_debug(expr.span.into());
                    }
                }
                ExprKind::If { cond, .. } => {
                    ctx.print_debug(thir[cond].span.into());
                    // if let Some(locs) = ctx.find_goto_locations(expr_id) {
                    //     ctx.expr_id_to_locs.insert(expr_id, locs);
                    // } else if let Some(loc) =
                    //     ctx.find_assign_ty_location(expr_id, |ty| ty.is_unit())
                    // {
                    //     ctx.expr_id_to_locs.insert(expr_id, smallvec![loc]);
                    // } else {
                    //     let then_expr = &thir[unwrap_scope_and_use(then, &thir)];
                    //     let else_expr_opt = else_opt.map(|e| &thir[unwrap_scope_and_use(e, &thir)]);
                    //     if !(matches!(then_expr.kind, ExprKind::NeverToAny { .. })
                    //         && else_expr_opt
                    //             .is_none_or(|e| matches!(e.kind, ExprKind::NeverToAny { .. })))
                    //     {
                    //         ctx.print_debug(expr.span);
                    //     }
                    // }
                    // let then_expr = &thir[then];
                    // let locs = term_span_to_locs
                    //     .get(&then_expr.span)
                    //     .unwrap_or_else(|| panic!("{:?}", then_expr.span));
                    // _show(expr.span, Some(locs));
                    // let locs = term_span_to_locs
                    //     .get(&expr.span)
                    //     .unwrap_or_else(|| panic!("{:?}", expr.span));
                    // _show(expr.span, Some(locs));
                }
                _ => {}
            }
        }

        for (expr_id, expr) in thir.exprs.iter_enumerated() {
            match expr.kind {
                ExprKind::Scope { .. } => {}
                ExprKind::Box { .. } => panic!(),
                ExprKind::If { .. } => {}
                ExprKind::Call { .. } => {
                    if let Some(loc) = ctx
                        .find_call_location(expr_id)
                        .or_else(|| ctx.find_transmute_location(expr_id))
                    {
                        ctx.expr_id_to_locs.insert(expr_id, smallvec![loc]);
                    } else {
                        ctx.print_debug(expr.span.into());
                    }
                }
                ExprKind::ByUse { .. } => panic!(),
                ExprKind::Deref { .. } => {} // TODO
                ExprKind::Binary { op, .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| {
                        if let Rvalue::BinaryOp(mop, _) = rvalue {
                            *mop == op
                        } else {
                            false
                        }
                    });
                }
                ExprKind::LogicalOp { .. } => {} // TODO
                ExprKind::Unary { op, .. } => match op {
                    UnOp::Neg => {
                        ctx.handle_rvalue(expr_id, |rvalue| {
                            matches!(rvalue, Rvalue::UnaryOp(UnOp::Neg, _))
                        });
                    }
                    UnOp::Not => {} // TODO
                    UnOp::PtrMetadata => panic!(),
                },
                ExprKind::Cast { .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| matches!(rvalue, Rvalue::Cast(..)));
                }
                ExprKind::Use { .. } => {}
                ExprKind::NeverToAny { .. } => {}
                ExprKind::PointerCoercion { .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| {
                        matches!(
                            rvalue,
                            Rvalue::Cast(CastKind::PointerCoercion(..) | CastKind::PtrToPtr, _, _)
                        )
                    });
                }
                ExprKind::Loop { .. } => {}  // TODO
                ExprKind::Let { .. } => {}   // TODO
                ExprKind::Match { .. } => {} // TODO
                ExprKind::Block { .. } => {} // TODO
                ExprKind::Assign { .. } => {}
                ExprKind::AssignOp { lhs, .. } => {
                    if let Some(assign) = ctx.find_assign_location(thir[lhs].ty, expr.span.into()) {
                        ctx.expr_id_to_locs.insert(expr_id, smallvec![assign.loc]);
                    } else {
                        ctx.print_debug(expr.span.into());
                    }
                }
                ExprKind::Field { .. } => {}    // TODO
                ExprKind::Index { .. } => {}    // TODO
                ExprKind::VarRef { .. } => {}   // TODO
                ExprKind::UpvarRef { .. } => {} // TODO
                ExprKind::Borrow { .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| matches!(rvalue, Rvalue::Ref(..)));
                }
                ExprKind::RawBorrow { .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| matches!(rvalue, Rvalue::RawPtr(..)));
                }
                ExprKind::Break { .. } => {
                    if let Some(loc) = ctx
                        .find_goto_location(expr_id)
                        .or_else(|| ctx.find_assign_ty_location(expr_id, |ty| ty.is_unit()))
                    {
                        ctx.expr_id_to_locs.insert(expr_id, smallvec![loc]);
                    } else {
                        ctx.print_debug(expr.span.into());
                    }
                }
                ExprKind::Continue { .. } => {}
                ExprKind::Return { value } => {
                    if let Some(loc) = ctx
                        .find_goto_location(expr_id)
                        .or_else(|| ctx.find_assign_ty_location(expr_id, |ty| ty.is_unit()))
                    {
                        ctx.expr_id_to_locs.insert(expr_id, smallvec![loc]);
                    } else if let Some(value) = value {
                        let value = unwrap_scope_and_use(value, &thir);
                        let value_expr = &thir[value];
                        if let Some(term_loc) = ctx
                            .find_rvalue_location(value, |_| true)
                            .map(|loc| ctx.terminator_of_last_assign(loc).unwrap())
                            .or_else(|| {
                                ctx.find_call_location(value)
                                    .map(|loc| ctx.next_terminator_of_call(loc).unwrap())
                            })
                        {
                            let term = ctx.get_terminator(term_loc);
                            assert!(
                                matches!(
                                    term.kind,
                                    TerminatorKind::Goto { .. }
                                        | TerminatorKind::Return
                                        | TerminatorKind::Drop { .. }
                                ),
                                "{:?}\n{:?}",
                                expr.span,
                                term.kind
                            );
                            ctx.expr_id_to_locs.insert(expr_id, smallvec![term_loc]);
                        } else if let Some(locs) = ctx.find_goto_locations(value) {
                            ctx.expr_id_to_locs.insert(expr_id, locs);
                        } else {
                            ctx.print_debug(value_expr.span.into());
                        }
                    } else {
                        ctx.print_debug(expr.span.into());
                    }
                }
                ExprKind::Become { .. } => todo!(),
                ExprKind::ConstBlock { .. } => {}
                ExprKind::Repeat { .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| matches!(rvalue, Rvalue::Repeat(..)));
                }
                ExprKind::Array { .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| {
                        matches!(rvalue, Rvalue::Aggregate(box AggregateKind::Array(..), _))
                    });
                }
                ExprKind::Tuple { .. } => {
                    ctx.handle_rvalue(expr_id, |rvalue| {
                        matches!(rvalue, Rvalue::Aggregate(box AggregateKind::Tuple, _))
                    });
                }
                ExprKind::Adt(_) => {
                    ctx.handle_rvalue(expr_id, |rvalue| {
                        matches!(rvalue, Rvalue::Aggregate(box AggregateKind::Adt(..), _))
                    });
                }
                ExprKind::PlaceTypeAscription { .. } => panic!(),
                ExprKind::ValueTypeAscription { .. } => panic!(),
                ExprKind::PlaceUnwrapUnsafeBinder { .. } => panic!(),
                ExprKind::ValueUnwrapUnsafeBinder { .. } => panic!(),
                ExprKind::WrapUnsafeBinder { .. } => panic!(),
                ExprKind::Closure(_) => todo!(),
                ExprKind::Literal { .. } => {}
                ExprKind::NonHirLiteral { .. } => {}
                ExprKind::ZstLiteral { .. } => {}
                ExprKind::NamedConst { .. } => {}
                ExprKind::ConstParam { .. } => {}
                ExprKind::StaticRef { .. } => {}
                ExprKind::InlineAsm(_) => {}
                ExprKind::OffsetOf { .. } => todo!(),
                ExprKind::ThreadLocalRef(_) => {}
                ExprKind::Yield { .. } => todo!(),
            }
        }
    }
}

fn unwrap_scope_and_use(mut expr_id: ExprId, thir: &Thir<'_>) -> ExprId {
    loop {
        let expr = &thir[expr_id];
        match expr.kind {
            ExprKind::Scope { value, .. } => {
                expr_id = value;
            }
            ExprKind::Use { source } => {
                expr_id = source;
            }
            _ => {
                return expr_id;
            }
        }
    }
}

struct Assign<'a, 'tcx> {
    ty: Ty<'tcx>,
    rvalue: &'a Rvalue<'tcx>,
    loc: Location,
    span: LoHi,
}

struct Ctx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    body: &'a Body<'tcx>,
    stmt_span_to_locs: &'a FxHashMap<LoHi, Locations>,
    term_span_to_locs: &'a FxHashMap<LoHi, Locations>,

    rhs_to_assigns: FxHashMap<ExprId, Assign<'a, 'tcx>>,
    expr_id_to_locs: FxHashMap<ExprId, Locations>,
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    /// When `Some` is returned, it is guaranteed to be non-empty.
    #[inline]
    fn find_locations<P: Fn(Location) -> bool>(
        &self,
        expr_id: ExprId,
        span_to_locs: &FxHashMap<LoHi, Locations>,
        pred: P,
    ) -> Option<Locations> {
        let expr = &self.thir[expr_id];
        let locs = span_to_locs.get(&expr.span.into())?;
        let locs: Locations = locs.iter().copied().filter(|loc| pred(*loc)).collect();
        if locs.is_empty() { None } else { Some(locs) }
    }

    #[inline]
    fn find_stmt_locations<P: Fn(&Place<'tcx>, &Rvalue<'tcx>) -> bool>(
        &self,
        expr_id: ExprId,
        pred: P,
    ) -> Option<Locations> {
        self.find_locations(expr_id, self.stmt_span_to_locs, |loc| {
            let stmt = self.get_statement(loc);
            let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else { panic!() };
            pred(lhs, rhs)
        })
    }

    #[inline]
    fn find_stmt_location<P: Fn(&Place<'tcx>, &Rvalue<'tcx>) -> bool>(
        &self,
        expr_id: ExprId,
        unique: bool,
        pred: P,
    ) -> Option<Location> {
        let locs = self.find_stmt_locations(expr_id, pred)?;
        if unique && locs.len() != 1 {
            None
        } else {
            Some(locs[0])
        }
    }

    #[inline]
    fn find_term_locations<P: Fn(&TerminatorKind<'tcx>) -> bool>(
        &self,
        expr_id: ExprId,
        pred: P,
    ) -> Option<Locations> {
        self.find_locations(expr_id, self.term_span_to_locs, |loc| {
            let term = self.get_terminator(loc);
            pred(&term.kind)
        })
    }

    #[inline]
    fn find_term_location<P: Fn(&TerminatorKind<'tcx>) -> bool>(
        &self,
        expr_id: ExprId,
        unique: bool,
        pred: P,
    ) -> Option<Location> {
        let locs = self.find_term_locations(expr_id, pred)?;
        if unique && locs.len() != 1 {
            None
        } else {
            Some(locs[0])
        }
    }

    fn find_goto_location(&self, expr_id: ExprId) -> Option<Location> {
        self.find_term_location(expr_id, true, |k| matches!(k, TerminatorKind::Goto { .. }))
    }

    fn find_goto_locations(&self, expr_id: ExprId) -> Option<Locations> {
        self.find_term_locations(expr_id, |k| matches!(k, TerminatorKind::Goto { .. }))
    }

    fn find_assign_ty_location<P: Fn(Ty<'tcx>) -> bool>(
        &self,
        expr_id: ExprId,
        pred: P,
    ) -> Option<Location> {
        self.find_stmt_location(expr_id, false, |lhs, _| {
            pred(lhs.ty(&self.body.local_decls, self.tcx).ty)
        })
    }

    fn find_call_location(&self, expr_id: ExprId) -> Option<Location> {
        self.find_term_location(expr_id, true, |k| {
            let TerminatorKind::Call { destination, .. } = k else { return false };
            destination.ty(&self.body.local_decls, self.tcx).ty == self.thir[expr_id].ty
        })
    }

    fn find_transmute_location(&self, expr_id: ExprId) -> Option<Location> {
        self.find_stmt_location(expr_id, true, |lhs, rhs| {
            matches!(rhs, Rvalue::Cast(CastKind::Transmute, _, _))
                && lhs.ty(&self.body.local_decls, self.tcx).ty == self.thir[expr_id].ty
        })
    }

    fn find_rvalue_location<P: Fn(&Rvalue<'tcx>) -> bool>(
        &self,
        expr_id: ExprId,
        pred: P,
    ) -> Option<Location> {
        self.find_stmt_location(expr_id, false, |lhs, rhs| {
            lhs.ty(&self.body.local_decls, self.tcx).ty == self.thir[expr_id].ty && pred(rhs)
        })
    }

    fn handle_rvalue<P: Fn(&Rvalue<'tcx>) -> bool>(&mut self, expr_id: ExprId, pred: P) {
        let expr = &self.thir[expr_id];
        if let Some(loc) = self.find_rvalue_location(expr_id, &pred) {
            self.expr_id_to_locs.insert(expr_id, smallvec![loc]);
        } else if let Some(assign) = self.rhs_to_assigns.get(&expr_id) {
            if expr.ty == assign.ty && pred(assign.rvalue) {
                self.expr_id_to_locs.insert(expr_id, smallvec![assign.loc]);
            } else {
                self.print_debug(assign.span);
            }
        } else {
            self.print_debug(expr.span.into());
        }
    }

    fn find_assign_location(&self, ty: Ty<'tcx>, span: LoHi) -> Option<Assign<'a, 'tcx>> {
        let locs = self.stmt_span_to_locs.get(&span)?;
        for (i, loc) in locs.iter().enumerate() {
            let stmt = self.get_statement(*loc);
            let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else { panic!() };
            if i < locs.len() - 1 {
                if !matches!(rhs, Rvalue::CopyForDeref(_)) {
                    break;
                }
            } else {
                let lhs_ty = lhs.ty(&self.body.local_decls, self.tcx).ty;
                if lhs_ty == ty {
                    let assign = Assign {
                        ty,
                        rvalue: rhs,
                        loc: *loc,
                        span,
                    };
                    return Some(assign);
                }
            }
        }
        None
    }

    fn terminator_of_last_assign(&self, loc: Location) -> Option<Location> {
        let bbd = &self.body.basic_blocks[loc.block];
        for stmt in bbd.statements.iter().skip(loc.statement_index + 1) {
            if matches!(stmt.kind, StatementKind::Assign { .. }) {
                return None;
            }
        }
        Some(Location {
            block: loc.block,
            statement_index: bbd.statements.len(),
        })
    }

    fn next_terminator_of_call(&self, loc: Location) -> Option<Location> {
        let term = self.get_terminator(loc);
        let TerminatorKind::Call { target, .. } = &term.kind else { return None };
        let block = (*target)?;
        let bbd = &self.body.basic_blocks[block];
        for stmt in &bbd.statements {
            if matches!(stmt.kind, StatementKind::Assign { .. }) {
                return None;
            }
        }
        Some(Location {
            block,
            statement_index: bbd.statements.len(),
        })
    }

    #[inline]
    fn get_statement(&self, loc: Location) -> &'a Statement<'tcx> {
        &self.body.basic_blocks[loc.block].statements[loc.statement_index]
    }

    #[inline]
    fn get_terminator(&self, loc: Location) -> &'a Terminator<'tcx> {
        let bbd = &self.body.basic_blocks[loc.block];
        assert_eq!(loc.statement_index, bbd.statements.len());
        bbd.terminator()
    }

    fn write_debug<W: std::io::Write>(&self, mut w: W, span: LoHi) {
        writeln!(w, "{span:?}").unwrap();
        if let Some(locs) = self.stmt_span_to_locs.get(&span) {
            for loc in locs {
                let stmt = self.get_statement(*loc);
                writeln!(w, "  {loc:?}: {stmt:?}").unwrap();
            }
        }
        if let Some(locs) = self.term_span_to_locs.get(&span) {
            for loc in locs {
                let term = self.get_terminator(*loc);
                writeln!(w, "  {loc:?}: {:?}", term.kind).unwrap();
            }
        }
    }

    #[inline]
    fn print_debug(&self, span: LoHi) {
        self.write_debug(std::io::stdout(), span);
    }

    #[allow(unused)]
    #[inline]
    fn mk_debug_str(&self, span: LoHi) -> String {
        let mut v = vec![];
        self.write_debug(&mut v, span);
        String::from_utf8(v).unwrap()
    }
}

struct ThirVisitor<'a, 'tcx> {
    #[allow(unused)]
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    bindings: FxHashMap<Span, HirId>,
}

impl<'a, 'tcx> TVisitor<'a, 'tcx> for ThirVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_pat(&mut self, pat: &'a Pat<'tcx>) {
        if let PatKind::Binding { var, .. } = pat.kind {
            let old = self.bindings.insert(pat.span, var.0);
            if let Some(old) = old {
                let old = self.tcx.hir_name(old);
                let var = self.tcx.hir_name(var.0);
                println!("{old} {var}");
            }
        }
        thir::visit::walk_pat(self, pat);
    }
}
