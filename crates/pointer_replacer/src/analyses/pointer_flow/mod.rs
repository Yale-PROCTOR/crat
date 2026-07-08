//! reusable pointer flow graph (PFG) infrastructure extracted from
//! `array_local_provenance`: slot tables, flow graph and provenance solving,
//! interprocedural function summaries, and the MIR collector.

pub mod builtin;
pub mod collector;
pub mod graph;
pub mod slots;
pub mod summary;
