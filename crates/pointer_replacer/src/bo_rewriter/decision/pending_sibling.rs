//! R419-3 / R304-2: a pending sibling-overlap site is a STATED HOLD, read at
//! decision time.
//!
//! The sibling-overlap instrument (`sibling_overlap.rs`) marks a T1 foreign
//! site `t1-sibling-overlap:pending` when its SOURCE is delivered as a borrowed
//! form while another argument of the same call — a sibling — may alias it and
//! writes (`risky_sibling`: an A5 verdict that is not `Clear`, and a contract
//! access `Write` / `Lifecycle` or an unmodeled position). The custody
//! comparator then protects the source binding's declaration. A family that
//! delivers such a source has delivered a held subject (main 039 §2, §5); it
//! consults this inventory BEFORE deciding and refuses with the typed reason.
//!
//! This is the instrument's premise read from the call facts alone, without
//! the verdict term: at decision time a caller LOCAL that is a literal or a
//! null-initialized binding has no frozen-graph array a proof could separate
//! from its sibling, so its verdict is never `Clear`. The read is therefore
//! exactly `risky_sibling` for the population it is consulted for, and
//! conservative for any other.

use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    emitability::EmitabilityFacts,
    raw_boundary_contracts::{PointeeAccess, classify_contract},
};

/// The first foreign site at which `node` is the source and a sibling argument
/// is risky: `(callee path, node's argument index, the sibling's index)`.
pub(crate) fn pending_site(
    facts: &EmitabilityFacts,
    node: (LocalDefId, HirId),
) -> Option<(String, usize, usize)> {
    facts
        .foreign_call_args
        .iter()
        .filter(|fact| fact.caller == node.0 && fact.direct_subject_root() == Some(node.1))
        .find_map(|fact| {
            facts
                .foreign_call_args
                .iter()
                .filter(|sibling| {
                    sibling.caller == fact.caller
                        && sibling.call_span == fact.call_span
                        && sibling.argument_index != fact.argument_index
                })
                .find(|sibling| {
                    match classify_contract(
                        &sibling.callee,
                        sibling.argument_index,
                        &sibling.target,
                    ) {
                        Ok(contract) => matches!(
                            contract.access,
                            PointeeAccess::Write | PointeeAccess::Lifecycle
                        ),
                        Err(_) => true,
                    }
                })
                .map(|sibling| {
                    (
                        fact.callee.path.clone(),
                        fact.argument_index,
                        sibling.argument_index,
                    )
                })
        })
}
