//! **Phase 3 — apply.** Plan in, rewritten AST out. **Analysis-blind.**
//!
//! This phase imports plan structs and the AST, and nothing else. It performs
//! no lookup, no inference, and no decision: if a question arises here that the
//! plan does not already answer, that is a plan defect, not a reason to import
//! an analysis.
//!
//! The import-denylist test enforces exactly that — see
//! [`super::import_denylist`]. `apply/` may not name `crate::analyses`,
//! the export, or `super::decision`.
//!
//! # Status
//!
//! S0 lands the phase boundary and the denylist rule. The applier arrives in S1.
