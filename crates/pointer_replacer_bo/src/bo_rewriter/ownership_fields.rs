//! Ownership/field emission components prepared under R244.
//!
//! Registered by the native decision intake. Positive admission still needs
//! complete compiler-session identities and accepted evidence, never name joins.
//! The independent test target also imports this module. No module here reads
//! a model cache or runs an analysis; native producers live in decision/.

/// A local-definition index transported from one compiler session.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OwnerId(pub u32);

/// An exact occurrence index, assigned by the compiler-side site inventory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SiteId {
    pub owner: OwnerId,
    pub occurrence: u32,
}

#[path = "ownership_fields_lifecycle.rs"]
pub mod lifecycle;

/// Identity tuple for an obligation in the frozen input/model and rendering.
/// `configuration` identifies the exact target/helper/panic configuration;
/// generation IDs are not allocation addresses or static allocation sites.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EvidenceKey {
    pub model: [u8; 32],
    pub configuration: [u8; 32],
    pub site: SiteId,
    pub generation: u64,
}

#[path = "ownership_fields_hoist.rs"]
pub mod hoist;

#[path = "ownership_fields_emission.rs"]
pub mod emission;

#[path = "ownership_fields_boundary.rs"]
pub mod boundary;

#[path = "ownership_fields_free.rs"]
pub mod free_sites;

#[path = "ownership_fields_depth.rs"]
pub mod drop_depth;

#[path = "ownership_fields_export.rs"]
pub mod export;

#[path = "ownership_fields_adapter.rs"]
pub mod adapter;

#[path = "ownership_fields_held_report.rs"]
pub mod held_report;

#[path = "ownership_fields_model_adapter.rs"]
pub mod model_adapter;

#[path = "ownership_fields_lend.rs"]
pub mod lend;
