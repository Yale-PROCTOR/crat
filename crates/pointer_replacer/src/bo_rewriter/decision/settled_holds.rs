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
    let held_formals: FxHashSet<(LocalDefId, usize)> = table
        .entries
        .iter()
        .filter(|(subject, _)| {
            let node = (subject.fn_did, subject.hir_id);
            forced.contains_key(&node) && !raw_in_hypothesis.contains(&node)
        })
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
    let held_bindings: Vec<(LocalDefId, HirId)> = {
        let mut nodes: Vec<_> = table
            .entries
            .iter()
            .map(|(subject, _)| (subject.fn_did, subject.hir_id))
            .filter(|node| forced.contains_key(node) && !raw_in_hypothesis.contains(node))
            .collect();
        nodes.sort_by_key(|(function, binding)| {
            (function.local_def_index.as_u32(), binding.local_id.as_u32())
        });
        nodes.dedup();
        nodes
    };
    let mut out = Vec::new();
    let mut seen = FxHashSet::default();
    // **Within the function (the stand-in review's M4; relay 297).** The model
    // keeps `B = A` in one kind (kind-equate); a hold forces `B` raw after it, and
    // a delivered `A` assigned or initialized into the held `B` then coerces
    // silently (`&mut T` into `*mut T`), the ladder's hazard with no compiler
    // backstop. `A` is decided raw too.
    for (function, binding) in &held_bindings {
        for source in flows_into_binding(tcx, *function, *binding) {
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
    held.sort_by_key(|(callee, index)| (callee.local_def_index.as_u32(), *index));
    for (callee, index) in held {
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

/// The bindings of `function` assigned or initialized into `binding` whole,
/// cast, or borrowed (`B = A`, `let B = A as *mut T`, `B = &mut *A`): the ladder's
/// argument shapes, read on the right-hand side.
fn flows_into_binding(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    function: LocalDefId,
    binding: HirId,
) -> Vec<HirId> {
    use rustc_hir::{Expr, ExprKind, LetStmt, PatKind, QPath, def::Res, intravisit};
    struct Find<'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        binding: HirId,
        sources: Vec<HirId>,
    }
    impl<'tcx> Find<'tcx> {
        fn take(&mut self, value: &'tcx Expr<'tcx>) {
            match super::emitability::classify_arg(self.tcx, value) {
                ArgShape::BareLocal(source)
                | ArgShape::CastOfLocal {
                    binding: source, ..
                }
                | ArgShape::AddrOf {
                    base: Some(source), ..
                } if source != self.binding => self.sources.push(source),
                _ => {}
            }
        }
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Find<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let ExprKind::Path(QPath::Resolved(None, path)) = lhs.kind
                && path.res == Res::Local(self.binding)
            {
                self.take(rhs);
            }
            intravisit::walk_expr(self, expr);
        }

        fn visit_local(&mut self, local: &'tcx LetStmt<'tcx>) {
            if let PatKind::Binding(_, id, ..) = local.pat.kind
                && id == self.binding
                && let Some(init) = local.init
            {
                self.take(init);
            }
            intravisit::walk_local(self, local);
        }
    }
    let mut find = Find {
        tcx,
        binding,
        sources: Vec::new(),
    };
    intravisit::Visitor::visit_body(&mut find, tcx.hir_body_owned_by(function));
    find.sources
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
