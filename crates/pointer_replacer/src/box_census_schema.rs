//! Box census worker/parent wire keys.
//!
//! Worker and every aggregate consumer name these constants, never serialized
//! strings. Renaming an identifier is therefore a compile-time migration;
//! changing its value moves both ends atomically.

pub(crate) const CODE_FRAME: &str = "box_code_frame";
pub(crate) const LAUNCH_PROFILE: &str = "box_launch_profile";
pub(crate) const RESOURCE_CONFIGURED_MIB: &str = "box_resource_bound_configured_mib";
pub(crate) const RESOURCE_EFFECTIVE_MIB: &str = "box_resource_bound_effective_mib";
pub(crate) const DROP_STATUS: &str = "box_drop_status";
pub(crate) const ROWS: &str = "box_rows";
pub(crate) const BRIDGE_ROWS: &str = "box_bridge_rows";
pub(crate) const BRIDGE_RESOLVED: &str = "box_bridge_resolved";
pub(crate) const DEFAULT_FILL_CANDIDATES: &str = "box_default_fill_candidates";
pub(crate) const FLEXIBLE_TAIL_EVIDENCE_ROWS: &str = "box_flexible_tail_evidence_rows";
pub(crate) const PLANNED: &str = "box_planned";
pub(crate) const PARAM_PLANNED: &str = "box_param_planned";
pub(crate) const DEPTH2_ROWS: &str = "box_depth2_rows";
pub(crate) const DEPTH2_PLANNED: &str = "box_depth2_planned";
pub(crate) const FABRICATED_EXTENT: &str = "box_fabricated_extent";
pub(crate) const WAIVER_OVERWRITE: &str = "box_waiver_overwrite";
pub(crate) const WAIVER_SCOPE_EXIT: &str = "box_waiver_scope_exit";
pub(crate) const WAIVER_UNWIND: &str = "box_waiver_unwind";
pub(crate) const FLEXIBLE_TAIL_HELD: &str = "box_flexible_tail_held";
pub(crate) const DEFAULT_FILL: &str = "box_default_fill";
pub(crate) const RECEIPT_WALL_S: &str = "box_receipt_wall_s";

pub(crate) const ALL: &[&str] = &[
    CODE_FRAME,
    LAUNCH_PROFILE,
    RESOURCE_CONFIGURED_MIB,
    RESOURCE_EFFECTIVE_MIB,
    DROP_STATUS,
    ROWS,
    BRIDGE_ROWS,
    BRIDGE_RESOLVED,
    DEFAULT_FILL_CANDIDATES,
    FLEXIBLE_TAIL_EVIDENCE_ROWS,
    PLANNED,
    PARAM_PLANNED,
    DEPTH2_ROWS,
    DEPTH2_PLANNED,
    FABRICATED_EXTENT,
    WAIVER_OVERWRITE,
    WAIVER_SCOPE_EXIT,
    WAIVER_UNWIND,
    FLEXIBLE_TAIL_HELD,
    DEFAULT_FILL,
    RECEIPT_WALL_S,
];
