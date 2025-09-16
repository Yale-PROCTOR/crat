use etrace::some_or;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def::DefKind};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, CastKind, Location, Place, Rvalue, Statement,
        StatementKind, SwitchTargets, Terminator, TerminatorKind, UnOp,
    },
    thir::{
        self, Expr, ExprId, ExprKind, LogicalOp, Pat, PatKind, Thir, visit::Visitor as TVisitor,
    },
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

        let mut visitor = BindingVisitor {
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
                    let conds = cond_dest(cond, &thir);
                    let mut true_targets = vec![];
                    let mut false_targets = vec![];
                    for cond in &conds {
                        if let Some(targets) = ctx.find_switch_int(cond.expr_id) {
                            let when_true = targets.otherwise();
                            let when_false = targets.target_for_value(0);
                            match cond.when_true {
                                None => {}
                                Some(true) => true_targets.push(when_true),
                                Some(false) => false_targets.push(when_true),
                            }
                            match cond.when_false {
                                None => {}
                                Some(true) => true_targets.push(when_false),
                                Some(false) => false_targets.push(when_false),
                            }
                        } else {
                            ctx.print_debug(thir[cond.expr_id].span.into());
                        }
                    }
                    let find_target = |targets: &[BasicBlock]| match targets {
                        [] => panic!(),
                        [bb] => *bb,
                        _ => {
                            let mut targets: Vec<_> = targets
                                .iter()
                                .map(|bb| {
                                    let term = body.basic_blocks[*bb].terminator();
                                    if let TerminatorKind::Goto { target } = term.kind {
                                        vec![*bb, target]
                                    } else {
                                        vec![*bb]
                                    }
                                })
                                .collect();
                            let mut target = targets.pop().unwrap();
                            for target1 in targets {
                                target.retain(|bb| target1.contains(bb));
                            }
                            assert!(target.len() == 1, "{target:?}");
                            target[0]
                        }
                    };
                    let true_target = find_target(&true_targets);
                    let false_target = find_target(&false_targets);
                    assert_ne!(true_target, false_target);
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
                ExprKind::Deref { .. } => {}
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
                ExprKind::Loop { .. } => {}
                ExprKind::Let { .. } => {}   // TODO
                ExprKind::Match { .. } => {} // TODO
                ExprKind::Block { .. } => {}
                ExprKind::Assign { .. } => {}
                ExprKind::AssignOp { lhs, .. } => {
                    if let Some(assign) = ctx.find_assign_location(thir[lhs].ty, expr.span.into()) {
                        ctx.expr_id_to_locs.insert(expr_id, smallvec![assign.loc]);
                    } else {
                        ctx.print_debug(expr.span.into());
                    }
                }
                ExprKind::Field { .. } => {}
                ExprKind::Index { .. } => {}
                ExprKind::VarRef { .. } => {}
                ExprKind::UpvarRef { .. } => {}
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

        for block in thir.blocks.iter() {
            let expr_id = some_or!(block.expr, continue);
            let expr_id = unwrap_scope_and_use(expr_id, &thir);
            if is_place(&thir[expr_id]) {
                ctx.handle_rvalue(expr_id, |rvalue| matches!(rvalue, Rvalue::Use(_)))
            }

            let mut visitor = ExprVisitor {
                tcx,
                thir: &thir,
                exprs: FxHashSet::default(),
            };
            visitor.visit_block(block);
            let bbs = ctx.collect_basic_blocks(visitor.exprs.into_iter());
            if bbs.is_empty() {
                println!("{:?}", block.span);
            }
        }

        for (_expr_id, expr) in thir.exprs.iter_enumerated() {
            match expr.kind {
                ExprKind::Loop { body: _body } => {}
                ExprKind::If {
                    then: _then,
                    else_opt: _else_opt,
                    ..
                } => {}
                ExprKind::Match { .. } => {} // TODO
                _ => {}
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

#[derive(Debug, Clone, Copy)]
struct CondWithDest {
    expr_id: ExprId,
    when_true: Option<bool>,
    when_false: Option<bool>,
}

fn cond_dest(expr_id: ExprId, thir: &Thir<'_>) -> Vec<CondWithDest> {
    let expr_id = unwrap_scope_and_use(expr_id, thir);
    match thir[expr_id].kind {
        ExprKind::LogicalOp { op, lhs, rhs } => {
            let mut l = cond_dest(lhs, thir);
            let r = cond_dest(rhs, thir);
            match op {
                LogicalOp::And => {
                    for c in &mut l {
                        c.when_true = c.when_true.filter(|b| !*b);
                        c.when_false = c.when_false.filter(|b| !*b);
                    }
                }
                LogicalOp::Or => {
                    for c in &mut l {
                        c.when_true = c.when_true.filter(|b| *b);
                        c.when_false = c.when_false.filter(|b| *b);
                    }
                }
            }
            l.extend(r);
            l
        }
        ExprKind::Unary { op: UnOp::Not, arg } => {
            let mut v = cond_dest(arg, thir);
            for c in &mut v {
                c.when_true = c.when_true.map(|b| !b);
                c.when_false = c.when_false.map(|b| !b);
            }
            v
        }
        _ => {
            vec![CondWithDest {
                expr_id,
                when_true: Some(true),
                when_false: Some(false),
            }]
        }
    }
}

#[inline]
fn is_place(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::Literal { .. }
            | ExprKind::Deref { .. }
            | ExprKind::Field { .. }
            | ExprKind::Index { .. }
            | ExprKind::VarRef { .. }
            | ExprKind::UpvarRef { .. }
    )
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

    fn find_switch_int(&self, expr_id: ExprId) -> Option<&'a SwitchTargets> {
        let loc = self.find_term_location(expr_id, true, |k| {
            matches!(k, TerminatorKind::SwitchInt { .. })
        })?;
        let term = self.get_terminator(loc);
        let TerminatorKind::SwitchInt { targets, .. } = &term.kind else { unreachable!() };
        Some(targets)
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

    #[inline]
    fn collect_basic_blocks(&self, exprs: impl Iterator<Item = ExprId>) -> FxHashSet<BasicBlock> {
        let mut bbs = FxHashSet::default();
        for expr in exprs {
            let locs = some_or!(self.expr_id_to_locs.get(&expr), continue);
            for loc in locs {
                bbs.insert(loc.block);
            }
        }
        bbs
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

struct BindingVisitor<'a, 'tcx> {
    #[allow(unused)]
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    bindings: FxHashMap<Span, HirId>,
}

impl<'a, 'tcx> TVisitor<'a, 'tcx> for BindingVisitor<'a, 'tcx> {
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

struct ExprVisitor<'a, 'tcx> {
    #[allow(unused)]
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    exprs: FxHashSet<ExprId>,
}

impl<'a, 'tcx> TVisitor<'a, 'tcx> for ExprVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a thir::Expr<'tcx>) {
        if let ExprKind::Scope { value, .. }
        | ExprKind::Use { source: value }
        | ExprKind::NeverToAny { source: value } = expr.kind
        {
            self.exprs.insert(value);
        }
        thir::visit::walk_expr(self, expr);
    }
}
