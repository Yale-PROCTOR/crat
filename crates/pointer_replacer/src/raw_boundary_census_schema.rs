//! Raw-boundary wave-1 worker/parent wire keys.
//!
//! Every shared producer/consumer names these identifiers. A migration changes
//! one authority and lets stale consumers fail at compile time.

pub(crate) const CORPUS: &str = "raw_boundary_corpus";
pub(crate) const ANALYSIS_FRAME: &str = "raw_boundary_analysis_frame";
pub(crate) const CODE_FRAME: &str = "raw_boundary_code_frame";
pub(crate) const WAVE: &str = "raw_boundary_wave";
pub(crate) const DATA: &str = "raw_boundary_data";
pub(crate) const BUILD_PROFILE: &str = "raw_boundary_build_profile";
pub(crate) const LAUNCH_PROFILE: &str = "raw_boundary_launch_profile";
pub(crate) const RESOURCE_CONFIGURED_MIB: &str = "raw_boundary_resource_configured_mib";
pub(crate) const RESOURCE_EFFECTIVE_MIB: &str = "raw_boundary_resource_effective_mib";
pub(crate) const CACHE_STATUS: &str = "raw_boundary_cache_status";
pub(crate) const CACHE_FINGERPRINT: &str = "raw_boundary_cache_fingerprint";
pub(crate) const CACHE_MODEL_SHA256: &str = "raw_boundary_cache_model_sha256";
pub(crate) const SOLVE_WALL_S: &str = "raw_boundary_solve_wall_s";
pub(crate) const WAIVER_ID: &str = "raw_boundary_waiver_id";
pub(crate) const WAIVER_CONFIRMED: &str = "raw_boundary_waiver_confirmed";
pub(crate) const WAIVER_TEXT_SHA256: &str = "raw_boundary_waiver_text_sha256";
pub(crate) const SITE_ROWS: &str = "raw_boundary_site_rows";
pub(crate) const SUBJECT_ROWS: &str = "raw_boundary_subject_rows";
pub(crate) const T1_CANDIDATE_SITES: &str = "raw_boundary_t1_candidate_sites";
pub(crate) const T2_CANDIDATE_SITES: &str = "raw_boundary_t2_candidate_sites";
pub(crate) const T2_WAIVER_SITES: &str = "raw_boundary_t2_waiver_sites";
pub(crate) const BLOCKED_SITES: &str = "raw_boundary_blocked_sites";
pub(crate) const OWNED_BY_OTHER_ARM_SITES: &str = "raw_boundary_owned_by_other_arm_sites";
pub(crate) const ZERO_SYNTAX_SITES: &str = "raw_boundary_zero_syntax_sites";
pub(crate) const EXPLICIT_BRIDGE_SITES: &str = "raw_boundary_explicit_bridge_sites";
pub(crate) const LIFECYCLE_SITES: &str = "raw_boundary_lifecycle_sites";
pub(crate) const T1_COMPILER_SURVIVING: &str = "raw_boundary_t1_compiler_surviving";
pub(crate) const T2_COMPILER_SURVIVING: &str = "raw_boundary_t2_compiler_surviving";
pub(crate) const T1_REALIZED_SUBJECTS: &str = "raw_boundary_t1_realized_subjects";
pub(crate) const T2_REALIZED_SUBJECTS: &str = "raw_boundary_t2_realized_subjects";
pub(crate) const MASKED_SECONDARY: &str = "raw_boundary_masked_secondary";
pub(crate) const ADDRESS_OBSERVATION_EDITS: &str = "raw_boundary_address_observation_edits";
pub(crate) const ATOM_ATTEMPTS: &str = "raw_boundary_atom_attempts";
pub(crate) const ATOM_SUCCESSES: &str = "raw_boundary_atom_successes";
pub(crate) const ATOM_AMBIGUOUS: &str = "raw_boundary_atom_ambiguous";
pub(crate) const ATOM_SECOND_VERIFY: &str = "raw_boundary_atom_second_verify";
pub(crate) const ATOM_FUNCTION_FALLBACK: &str = "raw_boundary_atom_function_fallback";
pub(crate) const ARM_B_ROWS: &str = "raw_boundary_arm_b_rows";
pub(crate) const ARM_B_BOX_ROWS: &str = "raw_boundary_arm_b_box_rows";
pub(crate) const ARM_B_CROWN_ROWS: &str = "raw_boundary_arm_b_crown_rows";
pub(crate) const CONTROL_LIBC_SUBJECTS: &str = "raw_boundary_control_libc_subjects";
pub(crate) const CONTROL_LIBC_EDGES: &str = "raw_boundary_control_libc_edges";
pub(crate) const CONTROL_FREE_ROWS: &str = "raw_boundary_control_free_rows";
pub(crate) const CONTROL_T2_ROWS: &str = "raw_boundary_control_t2_rows";
pub(crate) const CONTROL_BOX_ROWS: &str = "raw_boundary_control_box_rows";
pub(crate) const CONTROL_CROWN_ROWS: &str = "raw_boundary_control_crown_rows";
pub(crate) const CONTROL_DIAGNOSTIC_ROWS: &str = "raw_boundary_control_diagnostic_rows";
pub(crate) const CONTROL_DIVERGENCES: &str = "raw_boundary_control_divergences";
pub(crate) const SITE_DERIVATION_WALL_S: &str = "raw_boundary_site_derivation_wall_s";
pub(crate) const RETENTION_FIXPOINT_WALL_S: &str = "raw_boundary_retention_fixpoint_wall_s";
pub(crate) const CERTIFICATE_REPLAY_WALL_S: &str = "raw_boundary_certificate_replay_wall_s";
pub(crate) const DECISION_WALL_S: &str = "raw_boundary_decision_wall_s";
pub(crate) const RENDER_WALL_S: &str = "raw_boundary_render_wall_s";
pub(crate) const RECEIPT_WALL_S: &str = "raw_boundary_receipt_wall_s";
pub(crate) const INITIAL_VERIFY_WALL_S: &str = "raw_boundary_initial_verify_wall_s";
pub(crate) const ATOM_REVERIFY_WALL_S: &str = "raw_boundary_atom_reverify_wall_s";
pub(crate) const STATUS: &str = "raw_boundary_status";

pub(crate) const ALL: &[&str] = &[
    CORPUS,
    ANALYSIS_FRAME,
    CODE_FRAME,
    WAVE,
    DATA,
    BUILD_PROFILE,
    LAUNCH_PROFILE,
    RESOURCE_CONFIGURED_MIB,
    RESOURCE_EFFECTIVE_MIB,
    CACHE_STATUS,
    CACHE_FINGERPRINT,
    CACHE_MODEL_SHA256,
    SOLVE_WALL_S,
    WAIVER_ID,
    WAIVER_CONFIRMED,
    WAIVER_TEXT_SHA256,
    SITE_ROWS,
    SUBJECT_ROWS,
    T1_CANDIDATE_SITES,
    T2_CANDIDATE_SITES,
    T2_WAIVER_SITES,
    BLOCKED_SITES,
    OWNED_BY_OTHER_ARM_SITES,
    ZERO_SYNTAX_SITES,
    EXPLICIT_BRIDGE_SITES,
    LIFECYCLE_SITES,
    T1_COMPILER_SURVIVING,
    T2_COMPILER_SURVIVING,
    T1_REALIZED_SUBJECTS,
    T2_REALIZED_SUBJECTS,
    MASKED_SECONDARY,
    ADDRESS_OBSERVATION_EDITS,
    ATOM_ATTEMPTS,
    ATOM_SUCCESSES,
    ATOM_AMBIGUOUS,
    ATOM_SECOND_VERIFY,
    ATOM_FUNCTION_FALLBACK,
    ARM_B_ROWS,
    ARM_B_BOX_ROWS,
    ARM_B_CROWN_ROWS,
    CONTROL_LIBC_SUBJECTS,
    CONTROL_LIBC_EDGES,
    CONTROL_FREE_ROWS,
    CONTROL_T2_ROWS,
    CONTROL_BOX_ROWS,
    CONTROL_CROWN_ROWS,
    CONTROL_DIAGNOSTIC_ROWS,
    CONTROL_DIVERGENCES,
    SITE_DERIVATION_WALL_S,
    RETENTION_FIXPOINT_WALL_S,
    CERTIFICATE_REPLAY_WALL_S,
    DECISION_WALL_S,
    RENDER_WALL_S,
    RECEIPT_WALL_S,
    INITIAL_VERIFY_WALL_S,
    ATOM_REVERIFY_WALL_S,
    STATUS,
];
