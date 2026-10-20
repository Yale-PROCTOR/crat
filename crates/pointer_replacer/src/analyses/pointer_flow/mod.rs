//! reusable pointer flow graph (PFG) infrastructure extracted from
//! `array_local_provenance`: slot tables, flow graph and provenance solving,
//! interprocedural function summaries, and the MIR collector.

use rustc_hash::FxHashMap;
use rustc_middle::mir::Location;

pub mod builtin;
pub mod collector;
pub mod field_access;
pub mod graph;
pub mod slots;
pub mod summary;
#[cfg(test)]
mod tests;

pub use collector::pointer_flow_analysis;
use field_access::{FieldAccess, FieldAccessReject};
use graph::{PointerFlowGraph, ProvenanceResult};
use slots::SlotTable;
use summary::CallEffects;

#[derive(Clone, Debug)]
pub struct PointerFlowResult {
    pub slot_table: SlotTable,
    pub graph: PointerFlowGraph,
    pub provenance: ProvenanceResult,
    pub(crate) call_effects: FxHashMap<Location, CallEffects>,
    pub field_accesses: Vec<FieldAccess>,
    pub field_rejects: Vec<FieldAccessReject>,
}
