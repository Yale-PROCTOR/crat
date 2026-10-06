//! **The settled-table holds' callers (relay 297; main 186 §5).** A hold on the
//! settled table (the pending hold, R857-2's backstop, era-5c's retained-access
//! check) can make a LOCAL formal raw after co-conversion has read the classes:
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
pub(crate) fn into_held_formals(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    facts: &EmitabilityFacts,
    table: &DecisionTable,
    forced: &FxHashMap<(LocalDefId, HirId), DegradeReason>,
) -> Vec<((LocalDefId, HirId), DegradeReason)> {
    let held_formals: FxHashSet<(LocalDefId, usize)> = table
        .entries
        .iter()
        .filter(|(subject, _)| forced.contains_key(&(subject.fn_did, subject.hir_id)))
        .filter_map(|(subject, _)| match subject.kind {
            SubjectKind::Param { hir_index } => Some((subject.fn_did, hir_index)),
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
    let mut out = Vec::new();
    let mut seen = FxHashSet::default();
    let mut held: Vec<_> = held_formals.into_iter().collect();
    held.sort_by_key(|(callee, index)| (callee.local_def_index.as_u32(), *index));
    for (callee, index) in held {
        for call in facts.call_args.get(&callee).into_iter().flatten() {
            for argument in call.args.iter().filter(|argument| argument.index == index) {
                let binding = match argument.shape {
                    ArgShape::BareLocal(binding) | ArgShape::CastOfLocal { binding, .. } => binding,
                    _ => continue,
                };
                let node = (call.caller, binding);
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
