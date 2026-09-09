//! Ownership/field emission components prepared under R244.
//!
//! Not registered in the production pipeline yet. Integration must provide
//! compiler-session identities and accepted evidence, never source-name joins.
//! The independent test target imports this module without changing shared
//! main-lane files. No module here reads a model cache or runs an analysis.

#[path = "ownership_fields_transaction.rs"]
pub mod transaction;

/// A local-definition index transported from one compiler session.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OwnerId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldClassId {
    pub owner: OwnerId,
    pub field: u32,
}

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

#[path = "ownership_fields_declaration.rs"]
pub mod declaration;

#[path = "ownership_fields_custody.rs"]
pub mod custody;

#[path = "ownership_fields_uses.rs"]
pub mod field_uses;

#[path = "ownership_fields_boundary.rs"]
pub mod boundary;

#[path = "ownership_fields_free.rs"]
pub mod free_sites;

#[path = "ownership_fields_depth.rs"]
pub mod drop_depth;

#[path = "ownership_fields_copy.rs"]
pub mod struct_copy;

#[path = "ownership_fields_apply.rs"]
pub mod application;

#[path = "ownership_fields_recovery.rs"]
pub mod recovery;

#[path = "ownership_fields_raw_audit.rs"]
pub mod raw_audit;
