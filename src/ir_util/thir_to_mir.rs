use std::fmt::Write;

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def::DefKind};
use rustc_middle::{
    mir::{AggregateKind, Body, Location, Operand, Rvalue, StatementKind, UnOp},
    thir::{self, ExprId, ExprKind, Pat, PatKind, Thir, visit::Visitor as TVisitor},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::Span;

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

        let mut stmt_span_to_locs: FxHashMap<Span, Vec<_>> = FxHashMap::default();
        let mut term_span_to_locs: FxHashMap<Span, Vec<_>> = FxHashMap::default();

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
                    .entry(stmt.source_info.span)
                    .or_default()
                    .push(location);
            }
            let term = bbd.terminator();
            let location = Location {
                block: bb,
                statement_index: bbd.statements.len(),
            };
            term_span_to_locs
                .entry(term.source_info.span)
                .or_default()
                .push(location);
        }

        let mk_debug_str = |span: Span| {
            let mut s = String::new();
            writeln!(s, "{span:?}").unwrap();
            if let Some(locs) = stmt_span_to_locs.get(&span) {
                for loc in locs {
                    let stmt = &body.basic_blocks[loc.block].statements[loc.statement_index];
                    writeln!(s, "  {loc:?}: {stmt:?}").unwrap();
                }
            }
            if let Some(locs) = term_span_to_locs.get(&span) {
                for loc in locs {
                    let term = body.basic_blocks[loc.block].terminator();
                    writeln!(s, "  {loc:?}: {:?}", term.kind).unwrap();
                }
            }
            s
        };

        let ctx = Ctx {
            tcx,
            thir: &thir,
            body: &body,
            stmt_span_to_locs: &stmt_span_to_locs,
            term_span_to_locs: &term_span_to_locs,
        };

        let mut rhs_to_assigns = FxHashMap::default();
        let mut expr_id_to_loc = FxHashMap::default();
        for (expr_id, expr) in thir.exprs.iter_enumerated() {
            match expr.kind {
                ExprKind::Assign { rhs, .. } => {
                    rhs_to_assigns.insert(unwrap_scope(rhs, &thir), expr_id);
                    let rhs = &thir[rhs];
                    if let TyKind::Adt(adt_def, _) = rhs.ty.kind()
                        && super::def_id_to_symbol(adt_def.did(), tcx)
                            .unwrap()
                            .as_str()
                            == "VaListImpl"
                    {
                    } else {
                        let locs = stmt_span_to_locs
                            .get(&expr.span)
                            .unwrap_or_else(|| panic!("{:?}", expr.span));
                        validate_assign_locs(locs, expr.span, &body);
                        expr_id_to_loc.insert(expr_id, *locs.last().unwrap());
                    }
                }
                ExprKind::If { .. } => {
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
                ExprKind::Call { .. } => {} // TODO
                ExprKind::ByUse { .. } => panic!(),
                ExprKind::Deref { .. } => {} // TODO
                ExprKind::Binary { op, .. } => {
                    if !rhs_to_assigns.contains_key(&expr_id) {
                        let loc = ctx.find_rvalue_location(expr.span, expr.ty, |rvalue| {
                            if let Rvalue::BinaryOp(mop, _) = rvalue {
                                *mop == op
                            } else {
                                false
                            }
                        });
                        if let Some(loc) = loc {
                            expr_id_to_loc.insert(expr_id, loc);
                        } else {
                            println!("{}", mk_debug_str(expr.span));
                        }
                    }
                }
                ExprKind::LogicalOp { .. } => {} // TODO
                ExprKind::Unary { op, .. } => {
                    if !rhs_to_assigns.contains_key(&expr_id) && matches!(op, UnOp::Neg) {
                        let loc = ctx.find_rvalue_location(expr.span, expr.ty, |rvalue| {
                            if let Rvalue::UnaryOp(mop, _) = rvalue {
                                *mop == op
                            } else {
                                false
                            }
                        });
                        if let Some(loc) = loc {
                            expr_id_to_loc.insert(expr_id, loc);
                        } else {
                            println!("{}", mk_debug_str(expr.span));
                        }
                    }
                    // TODO: Not
                }
                ExprKind::Cast { .. } => {}            // TODO
                ExprKind::Use { .. } => {}             // TODO
                ExprKind::NeverToAny { .. } => {}      // TODO
                ExprKind::PointerCoercion { .. } => {} // TODO
                ExprKind::Loop { .. } => {}            // TODO
                ExprKind::Let { .. } => {}             // TODO
                ExprKind::Match { .. } => {}           // TODO
                ExprKind::Block { .. } => {}           // TODO
                ExprKind::Assign { .. } => {}
                ExprKind::AssignOp { .. } => {
                    let locs = stmt_span_to_locs
                        .get(&expr.span)
                        .unwrap_or_else(|| panic!("{:?}", expr.span));
                    validate_assign_locs(locs, expr.span, &body);
                    expr_id_to_loc.insert(expr_id, *locs.last().unwrap());
                }
                ExprKind::Field { .. } => {}    // TODO
                ExprKind::Index { .. } => {}    // TODO
                ExprKind::VarRef { .. } => {}   // TODO
                ExprKind::UpvarRef { .. } => {} // TODO
                ExprKind::Borrow { .. } => {
                    if !rhs_to_assigns.contains_key(&expr_id) {
                        let loc = ctx.find_rvalue_location(expr.span, expr.ty, |rvalue| {
                            matches!(rvalue, Rvalue::Ref(..))
                        });
                        if let Some(loc) = loc {
                            expr_id_to_loc.insert(expr_id, loc);
                        } else {
                            println!("{}", mk_debug_str(expr.span));
                        }
                    }
                }
                ExprKind::RawBorrow { .. } => {
                    if !rhs_to_assigns.contains_key(&expr_id) {
                        let loc = ctx.find_rvalue_location(expr.span, expr.ty, |rvalue| {
                            matches!(rvalue, Rvalue::RawPtr(..))
                        });
                        if let Some(loc) = loc {
                            expr_id_to_loc.insert(expr_id, loc);
                        } else {
                            println!("{}", mk_debug_str(expr.span));
                        }
                    }
                }
                ExprKind::Break { .. } => {}    // TODO
                ExprKind::Continue { .. } => {} // TODO
                ExprKind::Return { .. } => {}
                ExprKind::Become { .. } => todo!(),
                ExprKind::ConstBlock { .. } => {} // TODO
                ExprKind::Repeat { .. } => {
                    if !rhs_to_assigns.contains_key(&expr_id) {
                        let loc = ctx.find_rvalue_location(expr.span, expr.ty, |rvalue| {
                            matches!(rvalue, Rvalue::Repeat(..))
                        });
                        if let Some(loc) = loc {
                            expr_id_to_loc.insert(expr_id, loc);
                        } else {
                            println!("{}", mk_debug_str(expr.span));
                        }
                    }
                }
                ExprKind::Array { .. } => {
                    if !rhs_to_assigns.contains_key(&expr_id) {
                        let loc = ctx.find_rvalue_location(expr.span, expr.ty, |rvalue| {
                            matches!(rvalue,
                                Rvalue::Aggregate(box AggregateKind::Array(..), _) |
                                Rvalue::Use(Operand::Constant(_))
                            )
                        });
                        if let Some(loc) = loc {
                            expr_id_to_loc.insert(expr_id, loc);
                        } else {
                            println!("{}", mk_debug_str(expr.span));
                        }
                    }
                }
                ExprKind::Tuple { .. } => todo!(),
                ExprKind::Adt(_) => {
                    if !rhs_to_assigns.contains_key(&expr_id) {
                        let loc = ctx.find_rvalue_location(expr.span, expr.ty, |rvalue| {
                            matches!(rvalue, Rvalue::Aggregate(box AggregateKind::Adt(..), _))
                        });
                        if let Some(loc) = loc {
                            expr_id_to_loc.insert(expr_id, loc);
                        } else {
                            println!("{}", mk_debug_str(expr.span));
                        }
                    }
                }
                ExprKind::PlaceTypeAscription { .. } => panic!(),
                ExprKind::ValueTypeAscription { .. } => panic!(),
                ExprKind::PlaceUnwrapUnsafeBinder { .. } => panic!(),
                ExprKind::ValueUnwrapUnsafeBinder { .. } => panic!(),
                ExprKind::WrapUnsafeBinder { .. } => panic!(),
                ExprKind::Closure(_) => {} // TODO
                ExprKind::Literal { .. } => {}
                ExprKind::NonHirLiteral { .. } => {} // TODO
                ExprKind::ZstLiteral { .. } => {}
                ExprKind::NamedConst { .. } => {} // TODO
                ExprKind::ConstParam { .. } => {} // TODO
                ExprKind::StaticRef { .. } => {}
                ExprKind::InlineAsm(_) => {}      // TODO
                ExprKind::OffsetOf { .. } => {}   // TODO
                ExprKind::ThreadLocalRef(_) => {} // TODO
                ExprKind::Yield { .. } => todo!(),
            }
        }
    }
}

fn unwrap_scope(mut expr_id: ExprId, thir: &Thir<'_>) -> ExprId {
    loop {
        let expr = &thir[expr_id];
        if let ExprKind::Scope { value, .. } = expr.kind {
            expr_id = value;
        } else {
            return expr_id;
        }
    }
}

struct Ctx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    #[allow(unused)]
    thir: &'a Thir<'tcx>,
    body: &'a Body<'tcx>,
    stmt_span_to_locs: &'a FxHashMap<Span, Vec<Location>>,
    #[allow(unused)]
    term_span_to_locs: &'a FxHashMap<Span, Vec<Location>>,
}

impl<'tcx> Ctx<'_, 'tcx> {
    fn find_rvalue_location<P: Fn(&Rvalue<'_>) -> bool>(
        &self,
        span: Span,
        ty: Ty<'tcx>,
        pat: P,
    ) -> Option<Location> {
        let locs = self.stmt_span_to_locs.get(&span)?;
        let locs: Vec<_> = locs
            .iter()
            .copied()
            .filter(|loc| {
                let stmt = &self.body.basic_blocks[loc.block].statements[loc.statement_index];
                let StatementKind::Assign(box (_, rhs)) = &stmt.kind else { panic!() };
                rhs.ty(&self.body.local_decls, self.tcx) == ty && pat(rhs)
            })
            .collect();
        let [loc] = locs.as_slice() else { return None };
        Some(*loc)
    }
}

fn validate_assign_locs(locs: &[Location], span: Span, body: &Body<'_>) {
    for (i, loc) in locs.iter().enumerate() {
        let stmt = body.stmt_at(*loc).left().unwrap();
        let StatementKind::Assign(box (_, rhs)) = &stmt.kind else {
            panic!("{span:?}");
        };
        if i < locs.len() - 1 {
            assert!(matches!(rhs, Rvalue::CopyForDeref(_)), "{span:?}");
        }
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
