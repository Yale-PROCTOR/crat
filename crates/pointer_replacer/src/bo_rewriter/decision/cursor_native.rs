//! Native cursor decisions and compiler-bound admission receipts. The observer
//! reports candidate-stage facts; terminal delivery remains custody-owned.

use std::{collections::BTreeMap, fs::OpenOptions, io::Write, path::Path};

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};

use super::{Ctx, Decision, DegradeReason, Subject};
use crate::analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef};

#[path = "cursor/admission.rs"]
mod admission;
#[path = "cursor/delivered.rs"]
mod delivered;
#[path = "cursor/emission.rs"]
mod emission;
#[path = "cursor/foreign.rs"]
pub(crate) mod foreign;
#[path = "cursor/wrapper.rs"]
pub(crate) mod wrapper;
#[path = "cursor/wrapper_ast.rs"]
pub(crate) mod wrapper_ast;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorPlan {
    pub(crate) parent_cursor: Option<rustc_hir::HirId>,
    pub(crate) wrapper: bool,
    pub(crate) parameter: bool,
    pub(crate) optional: bool,
    pub(crate) fallback: bool,
    pub(crate) uses: Vec<super::emitability::UseEdit>,
    pub(crate) use_hirs: Vec<rustc_hir::HirId>,
    pub(crate) base: Local,
    pub(crate) component: Vec<Local>,
    pub(crate) extent: u64,
    pub(crate) delivered_base: Option<DeliveredBase>,
    pub(crate) bridges: Vec<CursorBridge>,
    pub(crate) local_bridges: Vec<CursorLocalBridge>,
    /// Outer-subject use edits composed into the constructor text; the AST
    /// pass applies the constructor at that span and skips these.
    pub(crate) composed_edit_spans: Vec<rustc_span::Span>,
    /// The cursor type to declare on an untyped local (`let mut q = …`), emitted
    /// through the explicit-declaration site.
    pub(crate) explicit_declaration: Option<String>,
    /// The bases this cursor is re-pointed to after initialisation (`p = q`,
    /// `p = Some(q.offset(k))`): a parent cursor or another family's delivered
    /// local. The cursor stands only while every one of them is admitted.
    pub(crate) peer_bases: Vec<rustc_hir::HirId>,
    /// Peer cursor candidates a use of this cursor was left to (the peer's
    /// initialiser or re-point owns the edit): both are cursors of this family
    /// or neither is emitted.
    pub(crate) peer_cursors: Vec<rustc_hir::HirId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeliveredBase {
    pub(crate) binding: rustc_hir::HirId,
    pub(crate) window_binding: rustc_hir::HirId,
    pub(crate) initializer: Option<rustc_hir::HirId>,
    pub(crate) provider: DeliveredBaseProvider,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DeliveredBaseProvider {
    OriginalSlice,
    Slice {
        producer: super::construction::SliceConstructionPlan,
    },
    Box {
        producer: super::box_facts::BoxPlan,
        elements: u64,
    },
    /// The binding is a delivered outer table whose loaded element is the
    /// cursor's raw base; the base is fallback-receipted, the link carries the
    /// outer's revert dependency only.
    TableElement,
    /// The binding is a delivered slice PARAMETER (`p: &[T]` at the safe body);
    /// the window is the binding's runtime length.
    SliceParameter,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorLocalBridge {
    pub(crate) destination: rustc_hir::HirId,
    pub(crate) initializer: rustc_hir::HirId,
    pub(crate) access: rustc_hir::HirId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorBridge {
    pub(crate) call_hir: rustc_hir::HirId,
    pub(crate) callee: LocalDefId,
    pub(crate) argument_span: rustc_span::Span,
    pub(crate) argument_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CursorHold {
    SourceUnavailable,
    UseUnbuilt,
    IndexRangeMissing,
    WindowMissing,
    BaseMissing,
    BaseModelRaw,
    LayoutUnbuilt,
    ScheduleMissing,
    RawBoundaryUnbuilt,
    DeclarationUnbuilt,
    OptionalUnbuilt,
    RefMissing,
    ComponentAliasUnbuilt,
    BorrowedElementUnbuilt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorReceipt {
    pub(crate) owner: LocalDefId,
    pub(crate) hir_id: rustc_hir::HirId,
    pub(crate) local: Local,
    pub(crate) disposition: Result<(), CursorHold>,
}

/// **R452-6.** A cursor whose base is a table element (`*t.offset(k)`) is
/// planned while `t` is still a flat slice of pointers. When `t` later delivers
/// its inner level (nested's N1), the element becomes a slice VALUE and the
/// constructor becomes `new(t[k])` — no length, nothing fabricated. That base
/// is this family's, so the plan is REBUILT here through the family's own
/// producer: a post-hoc rewrite of a finalised plan costs the cursor entirely
/// (nested 007's A/B). The caller flips the table first and calls this after.
///
/// A rebuild that holds leaves its entry untouched and is reported, so the
/// caller can withdraw the flip that made this necessary rather than emit a
/// cursor whose base text no longer types.
pub(crate) fn replan_delivered_table_elements(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
) -> Vec<CursorReceipt> {
    let targets = entries
        .iter()
        .enumerate()
        .filter(|(_, (subject, decision))| {
            // S3.0: a `Decision` is consumed through an EXHAUSTIVE match, so a
            // new disposition is a compile error here rather than a silent
            // `false` that drops the row. Both arms below are spelled out for
            // that reason and must not be collapsed to a wildcard.
            let plan = match decision {
                Decision::Cursor { plan, .. } => plan,
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => return false,
            };
            let Some(base) = plan.delivered_base.as_ref() else {
                return false;
            };
            matches!(base.provider, DeliveredBaseProvider::TableElement)
                && entries.iter().any(|(table, table_decision)| {
                    table.fn_did == subject.fn_did
                        && table.hir_id == base.binding
                        && match table_decision {
                            Decision::NestedSlice { .. } => true,
                            Decision::Cursor { .. }
                            | Decision::Ref { .. }
                            | Decision::InferredRef { .. }
                            | Decision::Slice { .. }
                            | Decision::Opt { .. }
                            | Decision::Box(_)
                            | Decision::Degraded(_) => false,
                        }
                })
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let mut receipts = Vec::new();
    for index in targets {
        let subject = entries[index].0.clone();
        // **R512-4 / slicecursor 064 §3, 068.** Since nested's transaction,
        // `promote` asks `plan_with(.., Some(&prospective))` BEFORE it writes,
        // so a row whose table has flipped was already built against the
        // delivered base and this re-build is a no-op: `table_element_base`
        // takes the `NestedSlice` arm either way and returns the same
        // `new(t[k])` with `fallback == false`.
        //
        // A target still carrying a FALLBACK plan is the opposite: a plan built
        // against the flat form whose table flipped afterwards, which is the
        // stale-plan case this pass exists to repair and which the transaction
        // is supposed to have made unreachable. It stays a repair rather than a
        // deletion, because "no other producer can flip a table later" is a
        // cross-family ordering claim and is not provable locally — but it is
        // now loud. The auditable count is this function's own receipt vector.
        //
        // S3.0: the `Decision` read is exhaustive.
        let stale = match &entries[index].1 {
            Decision::Cursor { plan, .. } => plan.fallback,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => false,
        };
        debug_assert!(
            !stale,
            "cursor-replan-after-flip: {:?} kept a fabricated window after its \
             table delivered its inner level — `promote` must ask \
             `plan_with(.., Some(..))` before it writes",
            subject.label
        );
        // `None`: this consumer re-plans AFTER a flip that already happened, so
        // there is no prospective table to tell the planner about — the flip is
        // in `entries`. R513-5 replaces this repair with an assert; the
        // assembler applies that patch when composing onto a frame that has
        // this function.
        let rebuilt = wrapper::build(ctx, &subject, entries, None);
        receipts.push(CursorReceipt {
            owner: subject.fn_did,
            hir_id: subject.hir_id,
            local: subject.local,
            disposition: rebuilt.as_ref().map(|_| ()).map_err(|e| *e),
        });
        if let Ok(plan) = rebuilt {
            entries[index].1 = Decision::Cursor {
                mutable: subject.mutable,
                plan,
            };
        }
    }
    receipts
}

pub(crate) fn promote(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
) -> Vec<CursorReceipt> {
    if !matches!(
        ctx.family_policy.stage,
        super::super::additive::FamilyStage::Return
            | super::super::additive::FamilyStage::Ownership
    ) {
        return vec![];
    }
    let proposals = entries
        .iter()
        .enumerate()
        .filter_map(|(index, (subject, decision))| {
            if !ctx.family_policy.enabled_for(
                (subject.fn_did, subject.hir_id),
                super::super::additive::FamilyStage::Return,
            ) {
                return None;
            }
            if let Some(plan) = wrapper::plan(ctx, subject, decision, entries) {
                return Some((index, plan));
            }
            let proposed = match decision {
                Decision::Degraded(record) => {
                    if is_cursor_reason(&record.reason) {
                        Some(
                            delivered::plan(ctx, subject, entries)
                                .unwrap_or_else(|| emission::plan(ctx, subject, entries)),
                        )
                    } else if matches!(
                        record.reason,
                        DegradeReason::KindRaw | DegradeReason::RawPointerOperation { .. }
                    ) {
                        // An original typed slice is already a reference capability.
                        // The closed administrative rewrite does not fabricate a Ref
                        // model verdict or license a raw base construction.
                        delivered::plan(ctx, subject, entries)
                    } else {
                        None
                    }
                }
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. } => None,
            };
            proposed.map(|plan| (index, plan))
        })
        .collect::<Vec<_>>();
    let mut receipts = Vec::new();
    let mut committed = Vec::new();
    for (index, proposed) in proposals {
        let (subject, decision) = &mut entries[index];
        receipts.push(CursorReceipt {
            owner: subject.fn_did,
            hir_id: subject.hir_id,
            local: subject.local,
            disposition: proposed.as_ref().map(|_| ()).map_err(|e| *e),
        });
        if proposed.is_ok() {
            committed.push((index, receipts.len() - 1, decision.clone()));
        }
        if proposed == Err(CursorHold::BaseModelRaw)
            && let Decision::Degraded(record) = decision
        {
            record.reason = DegradeReason::CursorBaseModelRaw;
        }
        if proposed == Err(CursorHold::BaseMissing)
            && let Decision::Degraded(record) = decision
        {
            record.reason = DegradeReason::CursorBaseUnavailable;
        }
        if let Ok(plan) = proposed {
            *decision = Decision::Cursor {
                mutable: subject.mutable,
                plan,
            };
        }
    }
    // A caller's whole-cursor argument admits only once its local callee's
    // parameter is a cursor; that is decided in the same pass, so a boundary
    // hold is re-planned against the committed entries, to a bounded fixpoint.
    for _round in 0..4 {
        let retry = receipts
            .iter()
            .enumerate()
            .filter(|(_, receipt)| receipt.disposition == Err(CursorHold::RawBoundaryUnbuilt))
            .filter_map(|(slot, receipt)| {
                entries
                    .iter()
                    .position(|(subject, _)| {
                        subject.fn_did == receipt.owner && subject.hir_id == receipt.hir_id
                    })
                    .map(|index| (slot, index))
            })
            .collect::<Vec<_>>();
        let mut progressed = false;
        for (slot, index) in retry {
            let (subject, decision) = &entries[index];
            let Some(Ok(plan)) = wrapper::plan(ctx, subject, decision, entries) else {
                continue;
            };
            let prior = decision.clone();
            receipts[slot].disposition = Ok(());
            committed.push((index, slot, prior));
            entries[index].1 = Decision::Cursor {
                mutable: entries[index].0.mutable,
                plan,
            };
            progressed = true;
        }
        if !progressed {
            break;
        }
    }
    // A derived cursor stands only on a parent that admitted: withdraw any
    // committed cursor whose parent is not itself a committed cursor, to a
    // fixpoint, so the family never emits a child over a raw parent.
    loop {
        let orphan = committed
            .iter()
            .position(|&(index, _, _)| match &entries[index].1 {
                Decision::Cursor { plan, .. } => {
                    plan.parent_cursor
                        .iter()
                        .chain(&plan.peer_bases)
                        .chain(&plan.peer_cursors)
                        .any(|&base| {
                            // A base that is no subject at all (an original
                            // safe binding) has nothing to withdraw.
                            entries.iter().any(|(other, decision)| {
                                other.fn_did == entries[index].0.fn_did
                                    && other.hir_id == base
                                    && !match decision {
                                        Decision::Cursor { plan, .. } => plan.wrapper,
                                        // A delivered peer another family owns
                                        // (`data = start`): admitted as long as
                                        // that family's decision stands.
                                        Decision::Slice { .. }
                                        | Decision::NestedSlice { .. }
                                        | Decision::Opt { .. } => {
                                            plan.peer_bases.contains(&base)
                                                && !plan.peer_cursors.contains(&base)
                                        }
                                        Decision::Ref { .. }
                                        | Decision::InferredRef { .. }
                                        | Decision::Box(_)
                                        | Decision::Degraded(_) => false,
                                    }
                            })
                        })
                }
                Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Opt { .. }
                | Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => false,
            });
        let Some(slot) = orphan else { break };
        let (index, receipt, prior) = committed.remove(slot);
        entries[index].1 = prior;
        receipts[receipt].disposition = Err(CursorHold::UseUnbuilt);
    }
    compose_nested_uses(ctx, entries, &committed, &mut receipts);
    receipts
}

/// **R512-4 / nested 018 STOP 1.** One bit the cursor family does not have at
/// plan time: *this table is about to deliver its inner level*. `promote` hands
/// it in before it writes anything, so `entries` stays pre-flip and is a single
/// source of truth for the whole query; the family answers with a constructed
/// `CursorPlan` or a `CursorHold`, and the caller commits the parameter only if
/// every row came back constructed.
///
/// Asked, not installed: report 061 measured what installing a decision before
/// its dependents are known good costs — a committed cursor beside a sibling
/// that did not deliver, and `SliceCursor.offset(..)` in the emitted text
/// (E0599). Rolling that back means unwinding the `uses` the flip wrote and
/// everything else that read the variant in the same pass.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ProspectiveTable {
    /// The table being flipped.
    pub(crate) binding: rustc_hir::HirId,
    /// The element's mutability after the flip.
    pub(crate) inner_mutable: bool,
}

/// Explicit declaration sites for untyped cursor locals (one hook in `mod.rs`).
pub(crate) fn explicit_declarations(
    table: &super::DecisionTable,
) -> Vec<super::seam::ExplicitDeclarationSite> {
    use crate::bo_rewriter::bridge_receipt::SignatureClassId;
    // One explicit declaration per node: a site another producer already
    // registered for this subject is not duplicated (the AST pass refuses
    // duplicates). The cursor's site exists only for a `Cursor` decision.
    let declared = table
        .seams
        .explicit_declarations
        .iter()
        .filter(|site| site.category == "local")
        .filter_map(|site| site.node)
        .collect::<rustc_hash::FxHashSet<_>>();
    table
        .entries
        .iter()
        .filter(|(subject, _)| !declared.contains(&(subject.fn_did, subject.hir_id)))
        .filter_map(|(subject, decision)| match decision {
            Decision::Cursor { plan, .. } => {
                plan.explicit_declaration.as_ref().map(|emitted_type| {
                    super::seam::ExplicitDeclarationSite {
                        owner_class: SignatureClassId::of(subject.fn_did),
                        caller: subject.fn_did,
                        node: Some((subject.fn_did, subject.hir_id)),
                        span: Some(subject.binding_span),
                        category: "local",
                        emitted_type: emitted_type.clone(),
                        replacement: None,
                        arm: "surface",
                    }
                })
            }
            Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => None,
        })
        .collect()
}

fn use_edits_mut(decision: &mut Decision) -> Option<&mut Vec<super::emitability::UseEdit>> {
    match decision {
        Decision::Slice { uses, .. }
        | Decision::NestedSlice { uses, .. }
        | Decision::Opt { uses, .. } => Some(uses),
        Decision::Cursor { plan, .. } => Some(&mut plan.uses),
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => None,
    }
}

/// A cursor use nested inside another subject's use edit (`*f.offset(*w.offset(k)
/// as isize)` with `w` the cursor) is composed the way the slice family composes
/// two nested slices: the outer edit's replacement, rendered from source text,
/// takes the cursor's rendered text in place of the inner's original text, and
/// the inner edit is dropped. An inner whose text is not found exactly once in
/// the outer keeps the subject's prior degraded decision.
fn compose_nested_uses(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
    committed: &[(usize, usize, Decision)],
    receipts: &mut [CursorReceipt],
) {
    let source_map = ctx.tcx.sess.source_map();
    let contains = |outer: rustc_span::Span, inner: rustc_span::Span| {
        let (outer, inner) = (outer.source_callsite(), inner.source_callsite());
        outer.lo() <= inner.lo() && inner.hi() <= outer.hi() && outer != inner
    };
    for &(index, receipt, ref prior) in committed {
        let owner = entries[index].0.fn_did;
        let uses = match &entries[index].1 {
            Decision::Cursor { plan, .. } => plan.uses.clone(),
            Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        // (inner use index, outer entry index, outer edit index, new outer text)
        let mut splices = Vec::new();
        let mut failed = false;
        for (k, inner) in uses.iter().enumerate() {
            let Some((j, o)) = entries
                .iter()
                .enumerate()
                .find_map(|(j, (other, decision))| {
                    if j == index || other.fn_did != owner {
                        return None;
                    }
                    let outer = match decision {
                        Decision::Slice { uses, .. }
                        | Decision::NestedSlice { uses, .. }
                        | Decision::Opt { uses, .. } => uses,
                        Decision::Cursor { plan, .. } => &plan.uses,
                        Decision::Ref { .. }
                        | Decision::InferredRef { .. }
                        | Decision::Box(_)
                        | Decision::Degraded(_) => return None,
                    };
                    outer
                        .iter()
                        .position(|edit| contains(edit.span, inner.span))
                        .map(|o| (j, o))
                })
            else {
                continue;
            };
            let Ok(text) = source_map.span_to_snippet(inner.span) else {
                failed = true;
                break;
            };
            let replacement = match &entries[j].1 {
                Decision::Slice { uses, .. }
                | Decision::NestedSlice { uses, .. }
                | Decision::Opt { uses, .. } => uses[o].replacement.clone(),
                Decision::Cursor { plan, .. } => plan.uses[o].replacement.clone(),
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => unreachable!("outer edit came from a use list"),
            };
            if replacement.matches(text.as_str()).count() != 1 {
                failed = true;
                break;
            }
            splices.push((k, j, o, replacement.replacen(&text, &inner.replacement, 1)));
        }
        if failed {
            entries[index].1 = prior.clone();
            receipts[receipt].disposition = Err(CursorHold::UseUnbuilt);
            continue;
        }
        // The reverse nesting: a cursor edit (a constructor or an advance)
        // that CONTAINS another subject's use edit takes that inner's rendered
        // text in place of the inner's original text and records the inner
        // span, which the AST pass then skips.
        let mut contained = Vec::new();
        {
            let uses = match &entries[index].1 {
                Decision::Cursor { plan, .. } => plan.uses.clone(),
                Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Opt { .. }
                | Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => Vec::new(),
            };
            for (k, outer) in uses.iter().enumerate() {
                if !matches!(outer.bridge_kind, "cursor-constructor" | "cursor-advance") {
                    continue;
                }
                let mut text = outer.replacement.clone();
                let mut spans = Vec::new();
                for (j, (other, decision)) in entries.iter().enumerate() {
                    if j == index || other.fn_did != owner {
                        continue;
                    }
                    let inner_uses = match decision {
                        Decision::Slice { uses, .. }
                        | Decision::NestedSlice { uses, .. }
                        | Decision::Opt { uses, .. } => uses,
                        Decision::Cursor { .. }
                        | Decision::Ref { .. }
                        | Decision::InferredRef { .. }
                        | Decision::Box(_)
                        | Decision::Degraded(_) => continue,
                    };
                    for inner in inner_uses
                        .iter()
                        .filter(|inner| contains(outer.span, inner.span))
                    {
                        let Ok(original) = source_map.span_to_snippet(inner.span) else {
                            failed = true;
                            break;
                        };
                        if text.matches(original.as_str()).count() != 1 {
                            failed = true;
                            break;
                        }
                        text = text.replacen(&original, &inner.replacement, 1);
                        spans.push(inner.span);
                    }
                }
                if !spans.is_empty() {
                    contained.push((k, text, spans));
                }
            }
        }
        if failed {
            entries[index].1 = prior.clone();
            receipts[receipt].disposition = Err(CursorHold::UseUnbuilt);
            continue;
        }
        match &mut entries[index].1 {
            Decision::Cursor { plan, .. } => {
                for (k, text, spans) in contained {
                    plan.uses[k].replacement = text;
                    plan.composed_edit_spans.extend(spans);
                }
            }
            Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => unreachable!("committed cursor entry"),
        }
        if splices.is_empty() {
            continue;
        }
        for &(_, j, o, ref text) in &splices {
            if let Some(outer) = use_edits_mut(&mut entries[j].1) {
                outer[o].replacement = text.clone();
            }
        }
        let dropped = splices.iter().map(|s| s.0).collect::<Vec<_>>();
        match &mut entries[index].1 {
            Decision::Cursor { plan, .. } => {
                let mut k = 0;
                plan.uses.retain(|_| {
                    k += 1;
                    !dropped.contains(&(k - 1))
                });
                let mut k = 0;
                plan.use_hirs.retain(|_| {
                    k += 1;
                    !dropped.contains(&(k - 1))
                });
            }
            Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => unreachable!("committed cursor entry"),
        }
    }
}

pub(crate) fn inspect_subject(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    subject: &Subject,
) -> admission::Admission {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(subject.fn_did)
        .borrow();
    let kinds = model_kinds(subject.fn_did, body.local_decls.indices(), slots, model);
    admission::inspect(
        tcx,
        subject.fn_did,
        &body,
        admission::Candidate {
            local: subject.local,
            slot_depth: usize::from(subject.ptr_depth.saturating_sub(1)),
            model_kind: kinds
                .get(&subject.local)
                .copied()
                .unwrap_or(admission::ModelKind::Missing),
        },
        &kinds,
    )
}

fn model_kinds(
    owner: LocalDefId,
    locals: impl Iterator<Item = Local>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> BTreeMap<Local, admission::ModelKind> {
    locals
        .map(|local| {
            let kind = slots
                .fn_local_slots
                .get(&owner)
                .and_then(|universe| universe.slot_for_local_depth(local, 0))
                .and_then(|slot| model.get(&SlotRef::Local(owner, slot)));
            let kind = match kind {
                Some(SlotKind::Ref) => admission::ModelKind::Ref,
                Some(SlotKind::Raw) => admission::ModelKind::Raw,
                Some(SlotKind::Owning) => admission::ModelKind::Owning,
                None => admission::ModelKind::Missing,
            };
            (local, kind)
        })
        .collect()
}

/// The archive belongs to one program at one source frame. A second worker for
/// the same pair (a census bisect probe, a retry) may write into it; a row from
/// another program or frame may not.
fn custody_matches(prior: &serde_json::Value, program: &str, frame: &str) -> bool {
    prior.get("program").and_then(serde_json::Value::as_str) == Some(program)
        && prior.get("frame").and_then(serde_json::Value::as_str) == Some(frame)
}

pub(crate) fn observe(
    ctx: &Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    receipts: &[CursorReceipt],
) {
    let Some(directory) = std::env::var_os("CRAT_CURSOR_ADMISSION_OUTPUT") else { return };
    if ctx.raw_boundary.is_none()
        || !matches!(
            ctx.family_policy.stage,
            super::super::additive::FamilyStage::Return
                | super::super::additive::FamilyStage::Ownership
        )
    {
        return;
    }
    // A cache-only corpus worker has one compiler session and one model. The
    // archive belongs to one worker/frame. Repeated family passes replace a
    // provisional row so the last candidate includes the settled owner stage.
    // Terminal placement/recovery remains a separate custody observation.
    // The archive is a DIAGNOSTIC of this lane: it must never abort the run that
    // carries it. A census re-enters a program in a second worker process (a
    // bisect probe, a retry) and exports `CRAT_CURSOR_ADMISSION_OUTPUT` to every
    // child, so a missing pin, a foreign role or a second pid is a reason to
    // skip the archive, never to panic.
    let Ok(program) = std::env::var("CRAT_ERA5_PROGRAM") else { return };
    if std::env::var("CRAT_ERA5_EXECUTION_ROLE").as_deref() != Ok("cache-only") {
        return;
    }
    if program.is_empty()
        || !program
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || "._-".contains(ch))
    {
        return;
    }
    let Ok(frame) = std::env::var("CRAT_RAW_BOUNDARY_CODE_FRAME") else { return };
    let root = Path::new(&directory).join(&program);
    if std::fs::create_dir_all(&root).is_err() {
        return;
    }
    let custody =
        serde_json::json!({"program": program, "frame": frame, "pid": std::process::id()});
    let guard = root.join("custody.json");
    match OpenOptions::new().write(true).create_new(true).open(&guard) {
        Ok(mut file) => {
            if writeln!(file, "{custody}").is_err() {
                return;
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            // The archive's identity is the program AND the source frame; the
            // worker's pid is provenance, not identity. A row for another frame
            // would mix two programs' readings, so that archive is left alone.
            let prior = std::fs::read(&guard)
                .ok()
                .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(&bytes).ok());
            if !prior.is_some_and(|prior| custody_matches(&prior, &program, &frame)) {
                return;
            }
        }
        Err(_) => return,
    }
    for (subject, decision) in entries {
        let path = root.join(format!(
            "{}-{}.json",
            subject.fn_did.local_def_index.as_u32(),
            subject.hir_id.local_id.as_u32()
        ));
        // Collect all named identities, not a docs-derived admission allowlist.
        // The later market join selects 70/44 and the newly routed population.
        let sign = ctx.sign.render(subject.fn_did, subject.local);
        let fat = ctx.fat.is_array(subject.fn_did, subject.local);
        let cursor_reason = match decision {
            Decision::Degraded(d) => is_cursor_reason(&d.reason),
            Decision::Ref { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => false,
        };
        let is_candidate = cursor_reason || (fat && sign == "neg-or-unknown");
        let row = if is_candidate {
            Some(inspect_subject(ctx.tcx, ctx.slots, ctx.model, subject))
        } else {
            None
        };
        let owner = ctx.tcx.def_path_str(subject.fn_did.to_def_id());
        let receipt = serde_json::json!({
            "schema": "cursor-admission-native-v1", "program": program,
            "subject_key": subject.identity_key(&owner), "owner_fn": owner,
            "owner": subject.fn_did.local_def_index.as_u32(), "hir": subject.hir_id.local_id.as_u32(),
            "mir_local": subject.local.index(), "ptr_depth": subject.ptr_depth,
            "candidate": is_candidate, "sign": sign, "fat_array": fat,
            "admission": row.as_ref().map(|r| format!("{:?}", r.status)),
            "shape": row.as_ref().map(|r| format!("{:?}", r.shape)),
            "predicates": row.as_ref().map(|r| r.findings.iter().map(|f| serde_json::json!({
                "predicate": format!("{:?}", f.predicate), "outcome": format!("{:?}", f.outcome),
                "root": f.root.map(|l| l.index()), "site": f.site.map(|s| [s.block, s.statement]),
            })).collect::<Vec<_>>()),
            "component": row.as_ref().map(|r| r.component.iter().map(|l| l.index()).collect::<Vec<_>>()),
            "native_outcome": receipts.iter().find(|r| r.owner == subject.fn_did && r.hir_id == subject.hir_id).map(|r| format!("{:?}", r.disposition)),
            "emission": match decision { Decision::Cursor { .. } => "planned-cursor", Decision::NestedSlice { .. } | Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Slice { .. } | Decision::Opt { .. } | Decision::Box(_) | Decision::Degraded(_) => "unchanged" },
            "delivered_base": match decision {
                Decision::Cursor { plan, .. } => plan.delivered_base.as_ref().map(|base| serde_json::json!({
                    "binding_hir": base.binding.local_id.as_u32(), "window_hir": base.window_binding.local_id.as_u32(),
                    "initializer_hir": base.initializer.map(|hir| hir.local_id.as_u32()),
                    "provider": format!("{:?}", base.provider), "window": "binding.len()",
                })),
                Decision::NestedSlice { .. } | Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Slice { .. }
                | Decision::Opt { .. } | Decision::Box(_) | Decision::Degraded(_) => None,
            },
            "stage": "candidate-pre-finalization", "source_frame": frame,
        });
        let Ok(mut file) = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&path)
        else {
            return;
        };
        if writeln!(file, "{receipt}").is_err() {
            return;
        }
    }
}

pub(super) fn is_cursor_reason(reason: &DegradeReason) -> bool {
    matches!(
        reason,
        DegradeReason::SliceNegOrUnknownOffset
            | DegradeReason::SliceCursorUse
            | DegradeReason::SliceUseUnsupported
    )
}

#[cfg(test)]
#[path = "cursor/native_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "cursor/delivered_tests.rs"]
mod delivered_tests;

#[cfg(test)]
#[path = "cursor/custody_tests.rs"]
mod custody_tests;

#[cfg(test)]
#[path = "cursor/wrapper_tests.rs"]
mod wrapper_tests;
