//! Narrow the planning-time dependency closure (relay wave-6k/008 §2(ii)).
//!
//! A caller whose call-argument ADAPTER is owned by a callee's signature class
//! depends on that class. When the callee is held, its adapter edits leave the
//! plan with it and the caller's argument renders in its own form against the
//! callee's raw signature — the same path the verify loop takes when a callee
//! class is reverted, where callers keep their deliveries. Holding the caller
//! as `dependency-class-held` for such an edge withholds deliveries the raw
//! bridge would have kept. An edge that also carries an interface, generated
//! item, option-call, inferred-lifetime or return-receiver dependency is NOT a
//! bare adapter edge and keeps its hold.

use std::collections::BTreeSet;

use super::{bridge_receipt::SignatureClassId, decision::DecisionTable, plan::Plan};

pub(crate) type Edge = (SignatureClassId, SignatureClassId);

/// `(dependent, dependency)` pairs that exist ONLY as call-site adapter edges.
pub(crate) fn call_adapter_only_edges(
    table: &DecisionTable,
    other_edges: impl IntoIterator<Item = Edge>,
) -> BTreeSet<Edge> {
    use super::decision::Decision;
    let mut adapter = BTreeSet::new();
    for edit in &table.seams.edits {
        let dependent = SignatureClassId::of(edit.bridge.caller);
        if dependent != edit.owner_class {
            adapter.insert((dependent, edit.owner_class));
        }
    }
    let mut structural = BTreeSet::new();
    // wave-5d2's class split decides which interface dependencies bind at all
    // (`plan::class_split::keeps_interface_dependency`); an edge it drops is
    // not a structural explanation here either, or a pair that is BOTH an
    // adapter edge and a dropped interface edge would keep a hold neither
    // rule intends (relay 015: the composed seam at `445f55be`).
    structural.extend(
        table
            .seams
            .interface_dependencies
            .iter()
            .copied()
            .filter(|&edge| super::plan::class_split::keeps_interface_dependency(table, edge)),
    );
    structural.extend(table.seams.generated_item_dependencies.iter().copied());
    for (subject, decision) in &table.entries {
        match decision {
            Decision::InferredRef { callee, .. } => {
                structural.insert((
                    SignatureClassId::of(subject.fn_did),
                    SignatureClassId::of(*callee),
                ));
            }
            Decision::Cursor { .. }
            | Decision::Ref { .. }
            | Decision::NestedSlice { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => {}
        }
    }
    for receiver in table.return_receivers.plans.values() {
        structural.insert((
            SignatureClassId::of(receiver.node.0),
            SignatureClassId::of(receiver.callee),
        ));
    }
    structural.extend(other_edges);
    adapter.difference(&structural).copied().collect()
}

/// The planner's one hook: drop the bare call-adapter edges from the
/// finalization dependency list and record them on the plan for the atom
/// closure. Every other edge passes through unchanged.
pub(crate) fn narrow(table: &DecisionTable, edges: Vec<Edge>, planned: &mut Plan) -> Vec<Edge> {
    let adapter = table
        .seams
        .edits
        .iter()
        .map(|edit| (SignatureClassId::of(edit.bridge.caller), edit.owner_class))
        .collect::<BTreeSet<_>>();
    let narrowed = call_adapter_only_edges(
        table,
        edges.iter().copied().filter(|edge| !adapter.contains(edge)),
    );
    let (dropped, kept): (Vec<_>, Vec<_>) =
        edges.into_iter().partition(|edge| narrowed.contains(edge));
    planned.narrowed_dependency_edges.extend(dropped);
    kept
}
