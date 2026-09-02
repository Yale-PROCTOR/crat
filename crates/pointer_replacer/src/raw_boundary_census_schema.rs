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
pub(crate) const SOLVER_INVOCATIONS: &str = "raw_boundary_solver_invocations";
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
pub(crate) const EXPOSURE_CONFIGURED_MATCHES: &str = "raw_boundary_exposure_configured_matches";
pub(crate) const EXPOSURE_ADDRESS_ROOTS: &str = "raw_boundary_exposure_address_roots";
pub(crate) const EXPOSURE_BOTH: &str = "raw_boundary_exposure_both";
pub(crate) const EXPOSURE_SEED_UNION: &str = "raw_boundary_exposure_seed_union";
pub(crate) const EXPOSURE_INPUT_SHA256: &str = "raw_boundary_exposure_input_sha256";
pub(crate) const EXPOSURE_MANIFEST_SHA256: &str = "raw_boundary_exposure_manifest_sha256";
pub(crate) const SURFACE_ENTRY_SHIMS: &str = "raw_boundary_surface_entry_shims";
pub(crate) const SURFACE_WEB_WRAPPERS: &str = "raw_boundary_surface_web_wrappers";
pub(crate) const SURFACE_CLOSED_DIRECT: &str = "raw_boundary_surface_closed_direct";
pub(crate) const SURFACE_NOT_APPLICABLE: &str = "raw_boundary_surface_not_applicable";
pub(crate) const UNIFIED_CONTROL_ROWS: &str = "raw_boundary_unified_control_rows";
pub(crate) const UNIFIED_PRODUCTION_MATCHED: &str = "raw_boundary_unified_production_matched";
pub(crate) const UNIFIED_CONTROL_UNMATCHED: &str = "raw_boundary_unified_control_unmatched";
pub(crate) const UNIFIED_PRODUCTION_UNMATCHED: &str = "raw_boundary_unified_production_unmatched";
pub(crate) const ARM_OUTCOME_ROWS: &str = "raw_boundary_arm_outcome_rows";
pub(crate) const ARM_SURFACE_REQUIRED: &str = "raw_boundary_arm_surface_required";
pub(crate) const ARM_D4_REQUIRED: &str = "raw_boundary_arm_d4_required";
pub(crate) const ARM_C_REQUIRED: &str = "raw_boundary_arm_c_required";
pub(crate) const ARM_PAIR_REQUIRED: &str = "raw_boundary_arm_pair_required";
pub(crate) const ARM_GLUE_REQUIRED: &str = "raw_boundary_arm_glue_required";
pub(crate) const ARM_ADDR_REQUIRED: &str = "raw_boundary_arm_addr_required";
pub(crate) const ARM_PLANNED_UNIQUE: &str = "raw_boundary_arm_planned_unique";
pub(crate) const ARM_BLOCKED_UNIQUE: &str = "raw_boundary_arm_blocked_unique";
pub(crate) const PAIR_CLEAR: &str = "raw_boundary_pair_clear";
pub(crate) const PAIR_OVERLAPPING: &str = "raw_boundary_pair_overlapping";
pub(crate) const PAIR_UNDETERMINABLE: &str = "raw_boundary_pair_undeterminable";
pub(crate) const PAIR_PRIMARY: &str = "raw_boundary_pair_primary";
pub(crate) const PAIR_RAW_VIEW: &str = "raw_boundary_pair_raw_view";
pub(crate) const PAIR_T1: &str = "raw_boundary_pair_t1";
pub(crate) const PAIR_T2: &str = "raw_boundary_pair_t2";
pub(crate) const PAIR_BLOCKED: &str = "raw_boundary_pair_blocked";
pub(crate) const GLUE_PLACED: &str = "raw_boundary_glue_placed";
pub(crate) const GLUE_BLOCKED: &str = "raw_boundary_glue_blocked";
pub(crate) const ADDR_VALUE_ONLY: &str = "raw_boundary_addr_value_only";
pub(crate) const ADDR_ACCESS_ONLY: &str = "raw_boundary_addr_access_only";
pub(crate) const ADDR_BOTH: &str = "raw_boundary_addr_both";
pub(crate) const ADDR_NEITHER: &str = "raw_boundary_addr_neither";
pub(crate) const ATOM_KEYED_EDITS: &str = "raw_boundary_atom_keyed_edits";
pub(crate) const ATOM_BISECT_ATTEMPTS: &str = "raw_boundary_atom_bisect_attempts";
pub(crate) const DIAGNOSTIC_CONTROL_MATCHED: &str = "raw_boundary_diagnostic_control_matched";
pub(crate) const R1_CLASS_BLOCKED: &str = "raw_boundary_r1_class_blocked";
pub(crate) const R1_ARG_STAYS_RAW: &str = "raw_boundary_r1_arg_stays_raw";
pub(crate) const R1_DUPLICATE_PLACE_ROOT: &str = "raw_boundary_r1_duplicate_place_root";
pub(crate) const R1_FLOWS_INTO_RAW_PARAM: &str = "raw_boundary_r1_flows_into_raw_param";
pub(crate) const R1_FLOWS_INTO_OTHER_FORM: &str = "raw_boundary_r1_flows_into_other_form";
pub(crate) const R1_BORROWED_INTO_RAW_PARAM: &str = "raw_boundary_r1_borrowed_into_raw_param";
pub(crate) const R1_PTR_COMPARISON: &str = "raw_boundary_r1_ptr_comparison";
pub(crate) const R1_ESCAPES_VIA_FOREIGN_ARG: &str = "raw_boundary_r1_escapes_via_foreign_arg";
pub(crate) const R1_OTHER: &str = "raw_boundary_r1_other";
pub(crate) const ATOM_ATTEMPTS: &str = "raw_boundary_atom_attempts";
pub(crate) const ATOM_SUCCESSES: &str = "raw_boundary_atom_successes";
pub(crate) const ATOM_AMBIGUOUS: &str = "raw_boundary_atom_ambiguous";
pub(crate) const ATOM_SECOND_VERIFY: &str = "raw_boundary_atom_second_verify";
pub(crate) const ATOM_FUNCTION_FALLBACK: &str = "raw_boundary_atom_function_fallback";
pub(crate) const ARM_B_ROWS: &str = "raw_boundary_arm_b_rows";
pub(crate) const ARM_B_BOX_ROWS: &str = "raw_boundary_arm_b_box_rows";
pub(crate) const ARM_B_CROWN_ROWS: &str = "raw_boundary_arm_b_crown_rows";
pub(crate) const FREE_ARM_B_ROWS: &str = "raw_boundary_free_arm_b_rows";
pub(crate) const CONTROL_LIBC_SUBJECTS: &str = "raw_boundary_control_libc_subjects";
pub(crate) const CONTROL_LIBC_EDGES: &str = "raw_boundary_control_libc_edges";
pub(crate) const CONTROL_FREE_ROWS: &str = "raw_boundary_control_free_rows";
pub(crate) const CONTROL_T2_ROWS: &str = "raw_boundary_control_t2_rows";
pub(crate) const CONTROL_BOX_ROWS: &str = "raw_boundary_control_box_rows";
pub(crate) const CONTROL_CROWN_ROWS: &str = "raw_boundary_control_crown_rows";
pub(crate) const CONTROL_DIAGNOSTIC_ROWS: &str = "raw_boundary_control_diagnostic_rows";
pub(crate) const CONTROL_PAIR_SUBJECT_ROWS: &str = "raw_boundary_control_pair_subject_rows";
pub(crate) const CONTROL_PAIR_SITE_ROWS: &str = "raw_boundary_control_pair_site_rows";
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
    SOLVER_INVOCATIONS,
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
    EXPOSURE_CONFIGURED_MATCHES,
    EXPOSURE_ADDRESS_ROOTS,
    EXPOSURE_BOTH,
    EXPOSURE_SEED_UNION,
    EXPOSURE_INPUT_SHA256,
    EXPOSURE_MANIFEST_SHA256,
    SURFACE_ENTRY_SHIMS,
    SURFACE_WEB_WRAPPERS,
    SURFACE_CLOSED_DIRECT,
    SURFACE_NOT_APPLICABLE,
    UNIFIED_CONTROL_ROWS,
    UNIFIED_PRODUCTION_MATCHED,
    UNIFIED_CONTROL_UNMATCHED,
    UNIFIED_PRODUCTION_UNMATCHED,
    ARM_OUTCOME_ROWS,
    ARM_SURFACE_REQUIRED,
    ARM_D4_REQUIRED,
    ARM_C_REQUIRED,
    ARM_PAIR_REQUIRED,
    ARM_GLUE_REQUIRED,
    ARM_ADDR_REQUIRED,
    ARM_PLANNED_UNIQUE,
    ARM_BLOCKED_UNIQUE,
    PAIR_CLEAR,
    PAIR_OVERLAPPING,
    PAIR_UNDETERMINABLE,
    PAIR_PRIMARY,
    PAIR_RAW_VIEW,
    PAIR_T1,
    PAIR_T2,
    PAIR_BLOCKED,
    GLUE_PLACED,
    GLUE_BLOCKED,
    ADDR_VALUE_ONLY,
    ADDR_ACCESS_ONLY,
    ADDR_BOTH,
    ADDR_NEITHER,
    ATOM_KEYED_EDITS,
    ATOM_BISECT_ATTEMPTS,
    DIAGNOSTIC_CONTROL_MATCHED,
    R1_CLASS_BLOCKED,
    R1_ARG_STAYS_RAW,
    R1_DUPLICATE_PLACE_ROOT,
    R1_FLOWS_INTO_RAW_PARAM,
    R1_FLOWS_INTO_OTHER_FORM,
    R1_BORROWED_INTO_RAW_PARAM,
    R1_PTR_COMPARISON,
    R1_ESCAPES_VIA_FOREIGN_ARG,
    R1_OTHER,
    ATOM_ATTEMPTS,
    ATOM_SUCCESSES,
    ATOM_AMBIGUOUS,
    ATOM_SECOND_VERIFY,
    ATOM_FUNCTION_FALLBACK,
    ARM_B_ROWS,
    ARM_B_BOX_ROWS,
    ARM_B_CROWN_ROWS,
    FREE_ARM_B_ROWS,
    CONTROL_LIBC_SUBJECTS,
    CONTROL_LIBC_EDGES,
    CONTROL_FREE_ROWS,
    CONTROL_T2_ROWS,
    CONTROL_BOX_ROWS,
    CONTROL_CROWN_ROWS,
    CONTROL_DIAGNOSTIC_ROWS,
    CONTROL_PAIR_SUBJECT_ROWS,
    CONTROL_PAIR_SITE_ROWS,
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
