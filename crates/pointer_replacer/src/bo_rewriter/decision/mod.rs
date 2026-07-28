//! **Phase 1 — decision.** Analysis in, decision table out. No AST mutation.
//!
//! Everything that reads BO output or an auxiliary analysis happens here and
//! nowhere else. The table this phase produces is **immutable and complete
//! before any edit is planned**: A1 emitability, A2 degradation closure, and
//! the owning-reachable fixpoint all live here, so no later phase ever has to
//! ask an analysis a question.
//!
//! # E1 state visibility
//!
//! This phase may read `crate::analyses::*` (read-only, §2 precedence rule) and
//! the `BoExport`. It hands [`crate::bo_rewriter::plan`] a finished table by
//! value. It holds no back-pointer to a later phase, and no later phase holds
//! one to it.
//!
//! # Status
//!
//! S0 lands the phase boundary only. The table, A1/A2, the owning-reachable
//! fixpoint and the envelope-demotion counters arrive in S1 (G01 arm) and S2
//! (breadth).
