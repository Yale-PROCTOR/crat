//! N1 (nested lane, R436-1) — the **per-parameter inner-construction
//! substitution**. The pair rule re-reads the whole function body and admits a
//! function only when every depth-2 table of it is a flat slice; N1 admits a
//! single table on its own, leaves every sibling byte-identical, and re-reads
//! nothing but that table's own uses.
//!
//! The rule. A depth-2 parameter `t` is admitted when
//!   (a) its outer level is already delivered as an immutable flat slice and
//!       its depth-1 slot is `Ref` (the analysis' own verdict, not ours);
//!   (b) EVERY use of the binding `t` in the body is the receiver of
//!       `*t.offset(k)` at a constant `k`, and that deref is the initializer
//!       of a `let` in the block's leading `let` run;
//!   (c) each such `let` binds a subject whose slice construction is already
//!       planned, not held, not nullable, and carries the FABRICATED extent —
//!       a constant, so relocating it to the wrapper cannot change what it
//!       means (an evidence-backed length may name a helper-local and is
//!       therefore not relocated by this arm);
//!   (d) every statement before the last admitted row load is a `let` whose
//!       initializer is inert: no call, assignment, branch, index, address-of
//!       or loop, so moving the loads above them preserves both the order of
//!       effects and the values read;
//!   (e) the rows of `t` project 0..n at one mutability, and neither `t` nor
//!       its rows carry a raw-boundary atom group.
//!
//! What it emits: `t` is re-typed `&[&[T]]` / `&mut [&mut [T]]`, each row's
//! construction becomes a reborrow of the element (`t[k]`, `&mut *t[k]`), and
//! the construction itself moves to the exposure wrapper with the SAME length
//! expression. The wrapper's own fabricated table extent is replaced by an
//! exact descriptor array, so the fabricated-extent count falls by one per
//! delivered table and the inner fabrications are relocated, not removed.
//!
//! Soundness (conditional on a UB-free input, §28). The descriptor array is
//! fresh local storage in the wrapper: the C pointer table is neither cast nor
//! written back. `&'o [&'i [T]]` carries `'i: 'o`, so the borrow of the array
//! cannot outlive the rows in it; the mutable side extracts with an explicit
//! reborrow and never moves out of borrowed storage. (d) is what makes the
//! relocation order-preserving, and no count guard is emitted, so the helper
//! still runs its own early returns at a non-positive count. Null at either
//! level stays `Option::None`'s business (§29): this arm changes no kind.

use rustc_hash::FxHashSet;
use rustc_hir::{
    Expr, ExprKind, HirId, QPath, StmtKind, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    DecisionTable, Hold, Parameter, Plan, Prelude, Row, SubjectKind, binding, flat_slice,
    inherited_pair, integer, named, offset, peel, prelude,
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::plan::ClassFinalization,
};

/// Every path expression that names one of `targets`, with its own id.
struct Uses<'a> {
    targets: &'a FxHashSet<HirId>,
    seen: Vec<(HirId, HirId)>,
}
impl<'tcx> Visitor<'tcx> for Uses<'_> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let ExprKind::Path(QPath::Resolved(_, path)) = e.kind
            && let Res::Local(id) = path.res
            && self.targets.contains(&id)
        {
            self.seen.push((id, e.hir_id));
        }
        intravisit::walk_expr(self, e);
    }
}

/// Reads, casts and arithmetic only — clause (d). A row load may be hoisted
/// above an inert initializer without changing effects, values or divergence.
struct Inert<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    valid: bool,
}
impl<'tcx> Visitor<'tcx> for Inert<'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        match e.kind {
            ExprKind::Lit(_)
            | ExprKind::Path(_)
            | ExprKind::Cast(..)
            | ExprKind::Unary(..)
            | ExprKind::Binary(..)
            | ExprKind::Field(..)
            | ExprKind::DropTemps(_) => {}
            ExprKind::MethodCall(..) if offset(self.tcx, self.owner, e).is_some() => {}
            _ => {
                self.valid = false;
                return;
            }
        }
        intravisit::walk_expr(self, e);
    }
}

struct Candidate {
    hir: HirId,
    index: usize,
    name: String,
}

pub(super) fn inspect<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    table: &DecisionTable,
    slots: &CrateSlots,
    model: &rustc_hash::FxHashMap<SlotRef, SlotKind>,
    ready: &ClassFinalization,
) -> Result<Plan, Hold> {
    let Prelude {
        block,
        count,
        count_name,
        signature,
    } = prelude(tcx, owner, table, ready)?;
    let subjects = table
        .entries
        .iter()
        .filter(|(s, _)| s.fn_did == owner)
        .collect::<Vec<_>>();

    // (a) Candidate tables. A sibling that does not qualify is SKIPPED here —
    // that is the whole difference from the pair rule, which holds on it.
    let mut candidates = Vec::new();
    for (s, d) in &subjects {
        if s.ptr_depth != 2 {
            continue;
        }
        let SubjectKind::Param { hir_index } = s.kind else { continue };
        if !flat_slice(d).is_some_and(|(mutable, _)| !mutable) {
            continue;
        }
        let Some(spelling) = s
            .pointee_span
            .and_then(|span| tcx.sess.source_map().span_to_snippet(span).ok())
        else {
            continue;
        };
        if !spelling.trim_start().starts_with("*const ")
            && !spelling.trim_start().starts_with("*mut ")
        {
            continue;
        }
        let Some(slot) = slots.fn_local_slots[&owner].slot_for_local_depth(s.local, 1) else {
            continue;
        };
        if model.get(&SlotRef::Local(owner, slot)) != Some(&SlotKind::Ref) {
            continue;
        }
        let TyKind::RawPtr(inner, _) = signature.inputs()[hir_index].kind() else { continue };
        let TyKind::RawPtr(element, _) = inner.kind() else { continue };
        if element.to_string() != "f64" {
            continue;
        }
        let Some(name) = s.param_name.clone() else { continue };
        candidates.push(Candidate {
            hir: s.hir_id,
            index: hir_index,
            name,
        });
    }
    if candidates.is_empty() {
        return Err(Hold::NullableLevelUnbuilt);
    }
    candidates.sort_by_key(|c| c.index);
    let targets = candidates.iter().map(|c| c.hir).collect::<FxHashSet<_>>();

    // (b) + (c) The leading `let` run, in body order.
    let mut rows = Vec::new();
    let mut admitted_receivers = FxHashSet::default();
    let mut row_statement = Vec::new();
    for (position, stmt) in block.stmts.iter().enumerate() {
        let StmtKind::Let(local) = stmt.kind else { break };
        let Some((id, name)) = named(local.pat) else { continue };
        if name.starts_with("__crat_nested_") {
            return Err(Hold::DeclarationUnbuilt);
        }
        let Some(init) = local.init else { continue };
        let ExprKind::Unary(UnOp::Deref, operand) = peel(init).kind else { continue };
        let Some((receiver, argument)) = offset(tcx, owner, operand) else { continue };
        let Some(parameter) = binding(receiver).filter(|p| targets.contains(p)) else { continue };
        let Some(projection) = integer(argument) else { continue };
        let Some((_, decision)) = subjects.iter().find(|(s, _)| s.hir_id == id) else { continue };
        let Some((mutable, _)) = flat_slice(decision) else { continue };
        if inherited_pair(
            table
                .arm_requirements
                .get(&(owner, id))
                .copied()
                .unwrap_or_default(),
        )
        .is_err()
        {
            continue;
        }
        let Some(construction) = table
            .slice_constructions
            .iter()
            .find(|c| c.node == (owner, id))
        else {
            continue;
        };
        if construction.init_hir != init.hir_id
            || construction.mutable != mutable
            || tcx
                .typeck(owner)
                .expr_ty(init)
                .builtin_deref(true)
                .is_none()
            || construction.hold_reason.is_some()
            || construction.replacement.is_none()
            || construction.nullable
            // Only a fabricated extent is known to be a constant, and only a
            // constant is known to mean the same thing in the wrapper.
            || !construction.length.is_fallback()
        {
            continue;
        }
        admitted_receivers.insert(peel(receiver).hir_id);
        row_statement.push(position);
        rows.push(Row {
            parameter,
            local: id,
            init: construction.init_hir,
            index: projection,
            mutable,
            was_fallback: true,
            length: construction.length.expression.clone(),
            raw_name: format!("__crat_nested_{}_raw", id.local_id.as_u32()),
            view_name: format!("__crat_nested_{}_view", id.local_id.as_u32()),
        });
    }

    // (b) A table with any other use keeps its frame form; a lexical miss is
    // not permitted to look like an absent use.
    let mut uses = Uses {
        targets: &targets,
        seen: Vec::new(),
    };
    // The prelude has already refused a block with a tail expression.
    for stmt in block.stmts {
        uses.visit_stmt(stmt);
    }
    let rejected = uses
        .seen
        .iter()
        .filter(|(_, expression)| !admitted_receivers.contains(expression))
        .map(|(parameter, _)| *parameter)
        .collect::<FxHashSet<_>>();
    let keep = (0..rows.len())
        .filter(|i| !rejected.contains(&rows[*i].parameter))
        .collect::<Vec<_>>();
    row_statement = keep.iter().map(|i| row_statement[*i]).collect();
    rows = keep.into_iter().map(|i| rows[i].clone()).collect();
    if rows.is_empty() {
        return Err(Hold::IntervalChanged);
    }

    // (d) The relocation crosses only inert declarations.
    let last = *row_statement.iter().max().expect("a row was admitted");
    for stmt in block.stmts.iter().take(last) {
        let StmtKind::Let(local) = stmt.kind else { return Err(Hold::IntervalChanged) };
        let Some(init) = local.init else { return Err(Hold::IntervalChanged) };
        let mut inert = Inert {
            tcx,
            owner,
            valid: true,
        };
        inert.visit_expr(init);
        if !inert.valid {
            return Err(Hold::IntervalChanged);
        }
    }

    // (e) Contiguous projections at one mutability per admitted table.
    let mut parameters = Vec::new();
    for candidate in &candidates {
        let group = rows
            .iter()
            .filter(|r| r.parameter == candidate.hir)
            .collect::<Vec<_>>();
        if group.is_empty() {
            continue;
        }
        if group.iter().enumerate().any(|(i, r)| r.index != i as u64) {
            return Err(Hold::StorageUnproved);
        }
        let mutable = group[0].mutable;
        if group.iter().any(|r| r.mutable != mutable) {
            return Err(Hold::StorageUnproved);
        }
        parameters.push(Parameter {
            hir: candidate.hir,
            index: candidate.index,
            name: candidate.name.clone(),
            descriptor_name: format!("__crat_nested_{}_rows", candidate.hir.local_id.as_u32()),
            mutable,
        });
    }
    if parameters.is_empty() {
        return Err(Hold::NullableLevelUnbuilt);
    }
    // THE LANE BOUNDARY. N1 is the arm for a function the pair rule cannot
    // deliver WHOLE. Where every depth-2 table of the owner would deliver, the
    // function is the pair rule's: N1 stands off and that rule's own hold —
    // and its own premises about the count, the loop and the accumulator —
    // remain the only verdict on it.
    let tables = subjects
        .iter()
        .filter(|(s, _)| s.ptr_depth == 2 && matches!(s.kind, SubjectKind::Param { .. }))
        .count();
    if parameters.len() >= tables {
        return Err(Hold::PairRequired);
    }
    rows.retain(|r| parameters.iter().any(|p| p.hir == r.parameter));
    if rows
        .iter()
        .map(|r| r.local)
        .chain(parameters.iter().map(|p| p.hir))
        .any(|hir| {
            table
                .seams
                .raw_boundary_atom_groups
                .get(&(owner, hir))
                .is_some_and(|v| !v.is_empty())
        })
    {
        return Err(Hold::RawBoundaryUnbuilt);
    }
    Ok(Plan {
        owner,
        count,
        count_name,
        accumulator: None,
        conditional_updates: Vec::new(),
        rows,
        parameters,
        count_guard: false,
    })
}
