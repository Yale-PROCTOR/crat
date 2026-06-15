//! opt-in decision trace for the array-local index rewrite pass. deliberately
//! separate from `diagnostics::DecisionDiagnostics` (the main pass's
//! framework); see the rewrite-decision-trace design spec. disabled by default
//! and a no-op when disabled.

use rustc_hir::def_id::LocalDefId;

/// the subject of a decision: a whole group (labelled by its base), a member
/// cursor (by source name), or a base cursor (by name).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TraceSubject {
    Group(String),
    Member(String),
    Base(String),
}

/// the pass stage at which a decision was made.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TraceStage {
    Selection,
    Plan,
    AstRefine,
    Prune,
    Representation,
    Apply,
}

/// the outcome recorded for a subject at a stage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TraceDecision {
    Kept,
    Dropped,
    Rewritten,
    Skipped,
}

/// one recorded decision.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TraceEvent {
    pub fn_def_id: LocalDefId,
    pub subject: TraceSubject,
    pub stage: TraceStage,
    pub decision: TraceDecision,
    pub reason: String,
}

/// collects decision events for the array-local index rewrite. when disabled
/// (the default), `record` is a no-op and no reason strings are built.
#[derive(Clone, Debug)]
pub(crate) struct RewriteTrace {
    enabled: bool,
    events: Vec<TraceEvent>,
}

/// the environment variable that enables the trace.
const ENV_VAR: &str = "CRAT_ARRAY_LOCAL_TRACE";

impl RewriteTrace {
    /// enabled iff `CRAT_ARRAY_LOCAL_TRACE` is set to a non-empty, non-"0",
    /// non-"false" value.
    pub(crate) fn from_env() -> Self {
        let enabled = std::env::var(ENV_VAR).is_ok_and(|v| {
            let v = v.trim();
            !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false")
        });
        Self {
            enabled,
            events: Vec::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn for_test(enabled: bool) -> Self {
        Self {
            enabled,
            events: Vec::new(),
        }
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// records an event. no-op when disabled; the `reason` closure is invoked
    /// only when enabled, so reason strings cost nothing in the default path.
    pub(crate) fn record(
        &mut self,
        fn_def_id: LocalDefId,
        subject: TraceSubject,
        stage: TraceStage,
        decision: TraceDecision,
        reason: impl FnOnce() -> String,
    ) {
        if !self.enabled {
            return;
        }
        self.events.push(TraceEvent {
            fn_def_id,
            subject,
            stage,
            decision,
            reason: reason(),
        });
    }

    pub(crate) fn events(&self) -> &[TraceEvent] {
        &self.events
    }

    #[cfg(test)]
    pub(crate) fn into_events(self) -> Vec<TraceEvent> {
        self.events
    }

    /// dumps the events to stderr, grouped by function. no-op when disabled.
    pub(crate) fn emit(&self, tcx: rustc_middle::ty::TyCtxt<'_>) {
        if !self.enabled {
            return;
        }
        let mut by_fn: rustc_hash::FxHashMap<LocalDefId, Vec<&TraceEvent>> =
            rustc_hash::FxHashMap::default();
        for event in &self.events {
            by_fn.entry(event.fn_def_id).or_default().push(event);
        }
        let mut fns: Vec<_> = by_fn.keys().copied().collect();
        fns.sort_by_key(|did| did.local_def_index.as_u32());
        for did in fns {
            eprintln!(
                "[array-local-trace] fn {}",
                tcx.def_path_str(did.to_def_id())
            );
            for event in &by_fn[&did] {
                eprintln!(
                    "[array-local-trace]   {:?} {:?} {:?} {} :: {}",
                    event.stage,
                    event.decision,
                    subject_kind(&event.subject),
                    subject_label(&event.subject),
                    event.reason,
                );
            }
        }
    }
}

fn subject_kind(subject: &TraceSubject) -> &'static str {
    match subject {
        TraceSubject::Group(_) => "group",
        TraceSubject::Member(_) => "member",
        TraceSubject::Base(_) => "base",
    }
}

fn subject_label(subject: &TraceSubject) -> &str {
    match subject {
        TraceSubject::Group(s) | TraceSubject::Member(s) | TraceSubject::Base(s) => s,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn did() -> LocalDefId {
        rustc_hir::def_id::CRATE_DEF_ID
    }

    #[test]
    fn disabled_trace_records_nothing_and_builds_no_reason() {
        let mut trace = RewriteTrace::for_test(false);
        let mut built = false;
        trace.record(
            did(),
            TraceSubject::Member("q".into()),
            TraceStage::Prune,
            TraceDecision::Dropped,
            || {
                built = true;
                "should not run".into()
            },
        );
        assert!(!trace.is_enabled());
        assert!(trace.events().is_empty());
        assert!(!built, "reason closure must not run when disabled");
    }

    #[test]
    fn enabled_trace_records_event_with_reason() {
        let mut trace = RewriteTrace::for_test(true);
        trace.record(
            did(),
            TraceSubject::Member("q".into()),
            TraceStage::Prune,
            TraceDecision::Dropped,
            || "q = b\"x\\0\"".into(),
        );
        assert_eq!(trace.events().len(), 1);
        let e = &trace.events()[0];
        assert_eq!(e.subject, TraceSubject::Member("q".into()));
        assert_eq!(e.stage, TraceStage::Prune);
        assert_eq!(e.decision, TraceDecision::Dropped);
        assert_eq!(e.reason, "q = b\"x\\0\"");
    }
}
