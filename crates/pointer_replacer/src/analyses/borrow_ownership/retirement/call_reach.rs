//! R304-7 row (a): which of a caller's cells a callee can reach.
//!
//! A callee cannot name a caller's MIR local. It can only write memory it can
//! reach -- through its arguments, through globals, and through anything
//! transitively reachable from those. A caller's local is reachable from a
//! callee exactly when its own storage address escaped, and in MIR the only
//! forms that take that address are `Rvalue::Ref` and `Rvalue::RawPtr` over a
//! place rooted at the local with no leading `Deref`. A leading `Deref` takes
//! the address of memory *behind* the pointer, not of the local itself.
//!
//! The set is deliberately coarse in the safe direction: it is flow-insensitive
//! (an address taken anywhere in the body counts everywhere) and an aggregate
//! field address (`&local.field`) counts as taking the local's address.

use rustc_hash::FxHashSet;
use rustc_middle::mir::{Body, Local, ProjectionElem, Rvalue, StatementKind};

/// Locals of one body whose own storage address escapes somewhere in it.
#[derive(Clone, Debug, Default)]
pub(crate) struct EscapeFacts {
    address_taken: FxHashSet<Local>,
}

impl EscapeFacts {
    pub(crate) fn of_body(body: &Body<'_>) -> Self {
        let mut address_taken = FxHashSet::default();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (_, value)) = &statement.kind else {
                    continue;
                };
                let (Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)) = value else {
                    continue;
                };
                if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                    address_taken.insert(place.local);
                }
            }
        }
        Self { address_taken }
    }

    /// True when a callee could reach this local's own storage.
    pub(crate) fn escapes(&self, local: Local) -> bool {
        self.address_taken.contains(&local)
    }

    #[cfg(test)]
    pub(crate) fn escaping_locals(&self) -> usize {
        self.address_taken.len()
    }
}
