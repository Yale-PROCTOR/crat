//! **The settled-table holds' callers (relay 297; main 186 §5).** A hold on the
//! settled table (the pending hold, R857-2's backstop; era-5c's retained-access
//! check when its line composes) can make a LOCAL formal raw after co-conversion
//! has read the classes:
//! the callers that hand it one of their own bindings whole still carry the form
//! the ladder gave that binding. A `&T` then coerces into the raw formal silently
//! (the co-conversion hazard the ladder blocks as `flows-into-raw-param`), and an
//! `Option<&T>` or a slice does not coerce at all (`E0308`: json.h
//! `json_extract_value_ex::value` into the held `json_extract_copy_value::value`).
//! So the caller's binding is decided raw too, `held:into-held-formal`, in the
//! same fixpoint: the ladder's rule for a binding flowing into a parameter that
//! stays raw, applied to the parameters the holds made raw.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Decision, DecisionTable, DegradeReason, SubjectKind,
    emitability::{ArgShape, EmitabilityFacts},
};

/// Is this decision a settled-table hold (relay 297)? Exhaustive by rule
/// (`import_denylist`).
pub(crate) fn is_settled_hold(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(record) => match record.reason {
            DegradeReason::PairNotShownDisjoint { .. }
            | DegradeReason::ReleasedThroughIndirectCall { .. }
            | DegradeReason::IntoHeldFormal { .. } => true,
            _ => false,
        },
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Opt { .. }
        | Decision::Box(_) => false,
    }
}

/// The callers' bindings handed whole to a formal in `forced`.
///
/// Only formals the raw boundary's hypothesis (`hypothesis`) reads safe: there the
/// boundary planned no bridge for their callers. A formal already raw in the
/// hypothesis has its callers' bridges planned (wave-6o's `OptSliceToRaw` into
/// glibc's local `stat`), and a hold on it is a relabel.
pub(crate) fn into_held_formals(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    facts: &EmitabilityFacts,
    table: &DecisionTable,
    hypothesis: &DecisionTable,
    forced: &FxHashMap<(LocalDefId, HirId), DegradeReason>,
) -> Vec<((LocalDefId, HirId), DegradeReason)> {
    let raw_in_hypothesis: FxHashSet<(LocalDefId, HirId)> = hypothesis
        .entries
        .iter()
        .filter(|(_, decision)| match decision {
            Decision::Degraded(_) => true,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => false,
        })
        .map(|(subject, _)| (subject.fn_did, subject.hir_id))
        .collect();
    // Each held formal, with whether the raw boundary's hypothesis already read
    // it raw (the stand-in review round 3, F3: that plans a bridge only for a
    // caller binding the hypothesis read safe, so the skip is per argument).
    let held_formals: FxHashMap<(LocalDefId, usize), bool> = table
        .entries
        .iter()
        .filter(|(subject, _)| forced.contains_key(&(subject.fn_did, subject.hir_id)))
        .filter_map(|(subject, _)| match subject.kind {
            SubjectKind::Param { hir_index } => Some((
                (subject.fn_did, hir_index),
                raw_in_hypothesis.contains(&(subject.fn_did, subject.hir_id)),
            )),
            _ => None,
        })
        .collect();
    // Exhaustive by rule (`import_denylist`): a new disposition is classified
    // here, never dropped by a bypass shape. A `Box` is an owner the call moves
    // through its own transfer, never a view the formal coerces.
    let delivered: FxHashSet<(LocalDefId, HirId)> = table
        .entries
        .iter()
        .filter(|(_, decision)| match decision {
            Decision::Degraded(_) | Decision::Box(_) => false,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Opt { .. } => true,
        })
        .map(|(subject, _)| (subject.fn_did, subject.hir_id))
        .collect();
    // Every held subject, whatever the hypothesis read (the stand-in review
    // round 2, N2: a relaxation can deliver a binding the hypothesis left raw).
    let held_bindings: Vec<(LocalDefId, HirId, rustc_middle::mir::Local)> = {
        let mut nodes: Vec<_> = table
            .entries
            .iter()
            .filter(|(subject, _)| forced.contains_key(&(subject.fn_did, subject.hir_id)))
            .map(|(subject, _)| (subject.fn_did, subject.hir_id, subject.local))
            .collect();
        nodes.sort_by_key(|(function, binding, _)| {
            (function.local_def_index.as_u32(), binding.local_id.as_u32())
        });
        nodes.dedup();
        nodes
    };
    let by_local: FxHashMap<(LocalDefId, rustc_middle::mir::Local), HirId> = table
        .entries
        .iter()
        .map(|(subject, _)| ((subject.fn_did, subject.local), subject.hir_id))
        .collect();
    let mut out = Vec::new();
    let mut seen = FxHashSet::default();
    // **Within the function (the stand-in review's M4; relay 297).** The model
    // keeps `B = A` in one kind (kind-equate); a hold forces `B` raw after it, and
    // a delivered `A` assigned or initialized into the held `B` then coerces
    // silently (`&mut T` into `*mut T`), the ladder's hazard with no compiler
    // backstop. `A` is decided raw too.
    for (function, binding, local) in &held_bindings {
        for source in locals_flowing_into(tcx, *function, *local) {
            let Some(&source) = by_local.get(&(*function, source)) else {
                continue;
            };
            let node = (*function, source);
            if !delivered.contains(&node) || forced.contains_key(&node) || !seen.insert(node) {
                continue;
            }
            out.push((
                node,
                DegradeReason::IntoHeldFormal {
                    detail: format!(
                        "into-held-binding:{}::{}",
                        tcx.def_path_str(function.to_def_id()),
                        tcx.hir_name(*binding)
                    ),
                },
            ));
        }
    }
    let mut held: Vec<_> = held_formals.into_iter().collect();
    held.sort_by_key(|((callee, index), _)| (callee.local_def_index.as_u32(), *index));
    for ((callee, index), formal_raw_in_hypothesis) in held {
        for call in facts.call_args.get(&callee).into_iter().flatten() {
            for argument in call.args.iter().filter(|argument| argument.index == index) {
                // The ladder's three rules (`co_conversion`): the binding whole
                // (`flows-into-raw-param`), cast (`cast-of-converting-local`), or
                // borrowed (`borrowed-into-raw-param`, `&mut *r` / `&mut (*r).f`:
                // the raw pointer the callee may keep outlives the reborrow; the
                // stand-in review's M4).
                let binding = match argument.shape {
                    ArgShape::BareLocal(binding)
                    | ArgShape::CastOfLocal { binding, .. }
                    | ArgShape::AddrOf {
                        base: Some(binding),
                        ..
                    } => binding,
                    _ => continue,
                };
                let node = (call.caller, binding);
                // The bridge is planned when the hypothesis read the formal raw
                // and this binding safe.
                if formal_raw_in_hypothesis && !raw_in_hypothesis.contains(&node) {
                    continue;
                }
                if !delivered.contains(&node) || forced.contains_key(&node) || !seen.insert(node) {
                    continue;
                }
                out.push((
                    node,
                    DegradeReason::IntoHeldFormal {
                        detail: format!(
                            "into-held-formal:{}#{}",
                            tcx.def_path_str(callee.to_def_id()),
                            index + 1
                        ),
                    },
                ));
            }
        }
    }
    out
}

/// The MIR locals of `function` whose pointer value reaches `target` (the stand-in
/// review round 2, N1): copies and casts through any temporaries (a C2Rust
/// ternary's arms, a block's tail), calls returning a pointer from their pointer
/// arguments (the pointer steps, `strchr`, a local helper), and addresses of
/// places reached through a dereference of the local (`&mut (*a).f`,
/// `&mut *a`). A load through
/// a dereference (`b = (*s).p`) is the pointee's value, not the local's, and is
/// no flow.
fn locals_flowing_into(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    function: LocalDefId,
    target: rustc_middle::mir::Local,
) -> Vec<rustc_middle::mir::Local> {
    use rustc_middle::mir::{
        BinOp, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    };
    fn whole(operand: &Operand<'_>) -> Option<Local> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let mut sources: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (place, rvalue) = &**assign;
            if !place.projection.is_empty() {
                continue;
            }
            let from = match rvalue {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => whole(operand),
                Rvalue::BinaryOp(BinOp::Offset, operands) => whole(&operands.0),
                Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed)
                    if borrowed.projection.first() == Some(&ProjectionElem::Deref) =>
                {
                    Some(borrowed.local)
                }
                _ => None,
            };
            if let Some(from) = from {
                sources.entry(place.local).or_default().push(from);
            }
        }
        // A call whose result is a pointer may return one of its pointer
        // arguments (the pointer steps, `strchr`, `memcpy`, a local
        // `skip_ws(p)`; the stand-in review round 3, F2): read as a flow from
        // each, which over-holds for yield only.
        if let Some(terminator) = &block.terminator
            && let TerminatorKind::Call {
                args, destination, ..
            } = &terminator.kind
            && destination.projection.is_empty()
            && body.local_decls[destination.local].ty.is_any_ptr()
        {
            for from in args.iter().filter_map(|argument| whole(&argument.node)) {
                if body.local_decls[from].ty.is_any_ptr() {
                    sources.entry(destination.local).or_default().push(from);
                }
            }
        }
    }
    let mut seen = FxHashSet::default();
    let mut work = vec![target];
    while let Some(local) = work.pop() {
        for &from in sources.get(&local).into_iter().flatten() {
            if from != target && seen.insert(from) {
                work.push(from);
            }
        }
    }
    let mut out: Vec<Local> = seen.into_iter().collect();
    out.sort();
    out
}

/// One settled-table hold's receipt: the predicate (its reason's key), the
/// subject, the reason's detail. A subject two predicates name has two.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SettledHoldReceipt {
    pub(crate) predicate: &'static str,
    pub(crate) node: (LocalDefId, HirId),
    pub(crate) detail: String,
}

impl SettledHoldReceipt {
    pub(crate) fn of(node: (LocalDefId, HirId), reason: &DegradeReason) -> Self {
        Self {
            predicate: reason.key(),
            node,
            detail: reason.detail(),
        }
    }
}

/// `<p>.raw-boundary-settled-holds.tsv`: `predicate`, `subject` (the census's
/// subject key), `detail`.
pub(crate) fn receipts_tsv(tcx: rustc_middle::ty::TyCtxt<'_>, table: &DecisionTable) -> String {
    let mut out = String::from("predicate\tsubject\tdetail\n");
    for receipt in &table.settled_hold_receipts {
        let subject = table
            .entries
            .iter()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == receipt.node)
            .map(|(subject, _)| subject.identity_key(&tcx.def_path_str(subject.fn_did.to_def_id())))
            .unwrap_or_else(|| "-".to_owned());
        out += &format!("{}\t{subject}\t{}\n", receipt.predicate, receipt.detail);
    }
    out
}
