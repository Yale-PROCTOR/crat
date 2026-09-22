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
//!   (c) each such `let` binds a subject that is either a planned slice
//!       construction — not held, not nullable — or (N2, the cursor seam) a
//!       cursor whose base is this table's element; either way it carries the
//!       FABRICATED extent —
//!       a constant, so relocating it to the wrapper cannot change what it
//!       means (an evidence-backed length may name a helper-local and is
//!       therefore not relocated by this arm);
//!   (d) every statement before the last admitted row load is a `let` whose
//!       initializer is inert: no call, assignment, branch, index, address-of
//!       or loop, so moving the loads above them preserves both the order of
//!       effects and the values read;
//!   (e) the rows of `t` project 0..n at one mutability, and neither `t` nor
//!       its rows carry a raw-boundary atom group;
//!   (f) (R500-6 (b)) a table admitted through (c)'s CURSOR branch stands off
//!       any owner that has a table admissible from slice rows alone. The plan
//!       is per-owner, so the two share one fate, and report 015 measured the
//!       price: the cursor rows delivered nothing and cost five tables N1
//!       already delivered. Standing off leaves exactly the plan the slice-only
//!       arm would have made, so the seam can only ever add; the stood-off
//!       table is named in the plan's `stood_off` and counted in the receipt;
//!   (g) (R501-4 (iv)) a table is flipped only when EVERY row of it has a
//!       construction for `promote` to rewrite, so where this arm cannot type
//!       the flip it does not make one and the emitted tree is untouched. A
//!       cursor row has no construction — its constructor belongs to the cursor
//!       family and is rebuilt only after the flip — and report 016 measured
//!       the gap as 61 of tulipindicators' 68 `SliceCursor` constructions
//!       reverting to raw pointers. The planner agrees: the `Return`-stage
//!       transaction carrying such a flip is withdrawn class-level and the next
//!       `Return` pass re-derives without it. Phrased over constructions rather
//!       than over cursors, so it releases itself the day a cursor row is
//!       constructed before the flip.
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
    super::cursor_native::DeliveredBaseProvider, Decision, DecisionTable, Hold, Parameter, Plan,
    Prelude, Row, SubjectKind, binding, flat_slice, inherited_pair, integer, named, offset, peel,
    prelude,
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
    // Positionally parallel to `rows`: which of them the N2 cursor arm
    // admitted. Kept beside the row rather than inside it so the pair rule's
    // `Row` — a shared type — does not grow a field only this arm reads. Its
    // one reader is the per-owner precondition below.
    let mut row_is_cursor: Vec<bool> = Vec::new();
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
        if tcx
            .typeck(owner)
            .expr_ty(init)
            .builtin_deref(true)
            .is_none()
        {
            continue;
        }
        let (mutable, length, from_cursor) = match decision {
            // The row becomes a plain slice local.
            Decision::Slice { mutable, .. } => {
                let Some(construction) = table
                    .slice_constructions
                    .iter()
                    .find(|c| c.node == (owner, id))
                else {
                    continue;
                };
                if construction.init_hir != init.hir_id
                    || construction.mutable != *mutable
                    || construction.hold_reason.is_some()
                    || construction.replacement.is_none()
                    || construction.nullable
                    // Only a fabricated extent is known to be a constant, and
                    // only a constant is known to mean the same thing in the
                    // wrapper.
                    || !construction.length.is_fallback()
                {
                    continue;
                }
                (*mutable, construction.length.expression.clone(), false)
            }
            // N2 (the cursor seam, relay 002 §2). The row becomes a cursor
            // over the inner slice. The cursor VERDICT and the runtime type are
            // the cursor family's; only the constructor at the use site is
            // ours, and it becomes `new(t[k])` — which takes no length, so this
            // seam fabricates NOTHING. The row's one fabricated extent is the
            // one this arm relocates to the wrapper, and it keeps the single
            // receipt the cursor plan already carries for it.
            Decision::Cursor { mutable, plan } => {
                let Some(base) = plan.delivered_base.as_ref() else { continue };
                if !matches!(base.provider, DeliveredBaseProvider::TableElement)
                    // `DeliveredBase::initializer` names the TABLE's own
                    // construction, not this row's; the row correspondence is
                    // the subject lookup above (`s.hir_id == id`).
                    || base.binding != parameter
                    // Only the fallback-receipted base is a bare element load;
                    // an evidence-backed one is a different construction.
                    || !plan.fallback
                    // A derived or re-pointed cursor has bases that are not the
                    // element, and this arm cannot speak for them.
                    || plan.parent_cursor.is_some()
                    || !plan.peer_bases.is_empty()
                    || plan
                        .uses
                        .iter()
                        .filter(|u| u.bridge_kind == "cursor-constructor")
                        .count()
                        != 1
                {
                    continue;
                }
                // `plan.fallback` is the cursor family's own receipt that this
                // base took the named fabricated extent; the wrapper rebuilds
                // the row's view with the same one.
                (*mutable, "crate::FALLBACK_SLICE_EXTENT".to_owned(), true)
            }
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        admitted_receivers.insert(peel(receiver).hir_id);
        row_statement.push(position);
        row_is_cursor.push(from_cursor);
        rows.push(Row {
            parameter,
            local: id,
            init: init.hir_id,
            index: projection,
            mutable,
            was_fallback: true,
            length,
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
    row_is_cursor = keep.iter().map(|i| row_is_cursor[*i]).collect();
    rows = keep.into_iter().map(|i| rows[i].clone()).collect();
    if rows.is_empty() {
        return Err(Hold::IntervalChanged);
    }

    // **R500-6 (b) — the per-owner precondition.** A `Plan` is per-OWNER, so
    // every parameter in it shares one fate: a clause that fails below, or an
    // emission that does not type, takes the whole owner down. The N2 cursor
    // arm is the only admission that can put a parameter here whose row is
    // another family's, and report 015 measured what that costs — five
    // tulipindicators tables N1 already delivered (`ti_crossany`,
    // `ti_crossover`, `ti_decay`, `ti_edecay`, `ti_tr`) were withdrawn,
    // each of them the SIBLING of a cursor row, and the cursor rows
    // themselves delivered nothing.
    //
    // So where the owner has a table admissible from slice rows ALONE, the
    // cursor arm stands off it. The rows that remain are exactly the rows the
    // slice-only arm would have collected, so the owner's plan is the one it
    // had before this seam existed and the seam can only ever add. Where the
    // owner has no such table there is nothing to protect and the arm is left
    // free. The stood-off parameters are named in the plan, so the decision is
    // typed and counted rather than a silent skip.
    let mut stood_off = Vec::new();
    let cursor_parameters = rows
        .iter()
        .zip(&row_is_cursor)
        .filter(|(_, from_cursor)| **from_cursor)
        .map(|(r, _)| r.parameter)
        .collect::<FxHashSet<_>>();
    if !cursor_parameters.is_empty()
        && rows
            .iter()
            .any(|r| !cursor_parameters.contains(&r.parameter))
    {
        stood_off = cursor_parameters.iter().copied().collect::<Vec<_>>();
        stood_off.sort_by_key(|hir| hir.local_id.as_u32());
        let keep = (0..rows.len())
            .filter(|i| !cursor_parameters.contains(&rows[*i].parameter))
            .collect::<Vec<_>>();
        // Non-empty by the condition above: at least one row is not a cursor's.
        row_statement = keep.iter().map(|i| row_statement[*i]).collect();
        rows = keep.into_iter().map(|i| rows[i].clone()).collect();
    }

    // **R501-4 (iv) — (b′), tree-neutrality by construction.** A table may be
    // flipped only when EVERY one of its rows has a construction for `promote`
    // to rewrite. A cursor row has none: its constructor belongs to the cursor
    // family and is rebuilt only AFTER the flip, so in between the table's type
    // has changed and the row's base text has not. That gap is not hypothetical
    // — report 016 measured it as 61 of tulipindicators' 68 `SliceCursor`
    // constructions turning back into raw pointers, and the instrument above it
    // shows the consequence in the planner: the Return-stage transaction
    // carrying such a flip is WITHDRAWN (class-level, `withdrawn=[Return]`) and
    // the next `Return` pass — the emitting one — re-derives without it.
    //
    // So where the arm cannot type the flip it does not make it, and the seam
    // costs the tree nothing. This is deliberately phrased over constructions
    // rather than over cursor rows: the day the cursor family constructs a row
    // before the flip, the condition starts passing on its own and (b) above
    // becomes the operative gate again.
    let unconstructed = rows
        .iter()
        .filter(|row| {
            !table
                .slice_constructions
                .iter()
                .any(|c| c.node == (owner, row.local))
        })
        .map(|row| row.parameter)
        .collect::<FxHashSet<_>>();
    if !unconstructed.is_empty() {
        stood_off.extend(unconstructed.iter().copied());
        stood_off.sort_by_key(|hir| hir.local_id.as_u32());
        stood_off.dedup();
        let keep = (0..rows.len())
            .filter(|i| !unconstructed.contains(&rows[*i].parameter))
            .collect::<Vec<_>>();
        row_statement = keep.iter().map(|i| row_statement[*i]).collect();
        rows = keep.into_iter().map(|i| rows[i].clone()).collect();
    }
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
    // The pair rule still LEADS — `inspect` only reaches this arm where it
    // held — but it does not reserve a function. R445-3 dropped the boundary
    // that stood N1 off wherever every table would deliver: a function whose
    // tables all qualify is delivered here too, and the pair rule's own
    // premises about the count, the loop and the accumulator keep their force
    // over the plan it would have made, not over this one.
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
        stood_off,
    })
}
