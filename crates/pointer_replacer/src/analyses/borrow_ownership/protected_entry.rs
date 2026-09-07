//! BO-owned parameter-entry obligations, separate from legacy Loan/CallArg IDs.
//! Incoming target identity is independent of later source-local assignments.

use std::{cell::RefCell, sync::Arc};

use rustc_hash::FxHashSet;
use rustc_middle::mir::{Local, Location};
use rustc_span::def_id::LocalDefId;

use super::{crate_slots::CrateSlots, solver::SlotRef, source_events::SourcePhase};
use crate::utils::rustc::RustProgram;

pub(crate) mod evidence;
mod flow;
mod validate;
pub(crate) use validate::Fact as EntryFact;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EntryKey {
    pub(crate) function: LocalDefId,
    pub(crate) parameter: Local,
    pub(crate) depth: u8,
    pub(crate) slot: SlotRef,
}

/// Rooted in the value received at entry, never in the current mutable binding.
/// `dereferences == entry.depth + 1`: d0 protects *entry(p), d1 **entry(p).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct IncomingTarget {
    pub(crate) entry: EntryKey,
    pub(crate) dereferences: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum EntryCondition {
    /// None creates no reference; a possible nonnull incoming value still does.
    IfNonNull,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum EntryRepresentation {
    /// A BO-owned obligation supplies the absent entry loan. This is not a
    /// fabricated legacy loan, an empty-loan certificate, or a CallArg revival.
    MissingLegacyLoan,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EntryObligation {
    pub(crate) key: EntryKey,
    pub(crate) target: IncomingTarget,
    pub(crate) condition: EntryCondition,
    pub(crate) representation: EntryRepresentation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CurrentBinding {
    Incoming(IncomingTarget),
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum EntryMoment {
    AtEvent,
    /// Sentinel after a Return/Unwind event; protection must have ended.
    AfterExit,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EntryObservation {
    pub(crate) entry: EntryKey,
    pub(crate) target: IncomingTarget,
    pub(crate) location: Location,
    pub(crate) phase: SourcePhase,
    pub(crate) moment: EntryMoment,
    pub(crate) live: bool,
    /// Immutable entry owner, independent of the current source-local binding.
    pub(crate) demand: Option<EntryKey>,
    pub(crate) current_binding: CurrentBinding,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct EntryAnalysis {
    pub(crate) entries: Vec<EntryObligation>,
    pub(crate) observations: Vec<EntryObservation>,
    /// Sparse known input-origin descendants. An absent row means Unknown,
    /// never disjointness or a proof that the pointer has no protected origin.
    pub(crate) binding_facts: Vec<BindingFact>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BindingFact {
    pub(crate) function: LocalDefId,
    pub(crate) local: Local,
    pub(crate) depth: u8,
    pub(crate) location: Location,
    pub(crate) phase: SourcePhase,
    pub(crate) moment: EntryMoment,
    pub(crate) target: IncomingTarget,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum AccessMode {
    Read,
    Write,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum AccessExtent {
    Shallow,
    Deep,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum AccessCause {
    Ordinary,
    DeallocationCandidate,
}

/// Original source access before any ordinary-loan or mutability filter.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SourceAccess {
    pub(crate) function: LocalDefId,
    pub(crate) location: Location,
    pub(crate) phase: SourcePhase,
    pub(crate) place: super::export::PlaceKey,
    pub(crate) extent: AccessExtent,
    pub(crate) mode: AccessMode,
    pub(crate) cause: AccessCause,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum EntryCoverageError {
    MissingEntry(EntryKey),
    MissingPoint(EntryKey, Location),
    InconsistentDemand(EntryKey, Location),
}

impl EntryAnalysis {
    /// Intersect an already matched invalidation with effective entry liveness
    /// and demand. Object overlap/retirement matching is a separate premise.
    pub(crate) fn repair_target_for_invalidation(
        &self,
        entry: EntryKey,
        location: Location,
        phase: SourcePhase,
        moment: EntryMoment,
    ) -> Result<Option<SlotRef>, EntryCoverageError> {
        let Some(obligation) = self.entries.iter().find(|row| row.key == entry) else {
            return Err(EntryCoverageError::MissingEntry(entry));
        };
        let mut matching = self.observations.iter().filter(|row| {
            row.entry == entry
                && row.location == location
                && row.phase == phase
                && row.moment == moment
        });
        let Some(point) = matching.next() else {
            return Err(EntryCoverageError::MissingPoint(entry, location));
        };
        if matching.next().is_some() || point.target != obligation.target {
            return Err(EntryCoverageError::InconsistentDemand(entry, location));
        }
        match (point.live, point.demand, moment) {
            (true, Some(owner), EntryMoment::AtEvent) if owner == entry => Ok(Some(owner.slot)),
            (false, None, EntryMoment::AfterExit) => Ok(None),
            _ => Err(EntryCoverageError::InconsistentDemand(entry, location)),
        }
    }
}

pub(crate) fn analyze(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
) -> EntryAnalysis {
    flow::analyze(program, slots, is_ref)
}

thread_local! {
    static CARRIED: RefCell<Option<Arc<EntryAnalysis>>> = const { RefCell::new(None) };
    static ACCESSES: RefCell<Option<(Vec<SourceAccess>, FxHashSet<SourceAccess>)>> = const { RefCell::new(None) };
}

pub(crate) fn current() -> Option<Arc<EntryAnalysis>> {
    CARRIED.with(|facts| facts.borrow().clone())
}

pub(crate) fn record_access(access: SourceAccess) {
    ACCESSES.with(|capture| {
        if let Some((rows, seen)) = capture.borrow_mut().as_mut() {
            if seen.insert(access.clone()) {
                rows.push(access);
            }
        }
    });
}

pub(crate) fn current_accesses() -> Vec<SourceAccess> {
    ACCESSES.with(|capture| {
        capture
            .borrow()
            .as_ref()
            .map(|(rows, _)| rows.clone())
            .unwrap_or_default()
    })
}

pub(crate) struct EntryScope {
    previous: Option<Arc<EntryAnalysis>>,
    accesses: Option<(Vec<SourceAccess>, FxHashSet<SourceAccess>)>,
}

impl Drop for EntryScope {
    fn drop(&mut self) {
        let accesses = ACCESSES.with(|capture| capture.replace(self.accesses.take()));
        if let Some((rows, _)) = accesses {
            super::export::record(|export| export.entry_accesses = rows);
        }
        CARRIED.with(|facts| *facts.borrow_mut() = self.previous.take());
    }
}

pub(crate) fn for_model(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
) -> EntryScope {
    let facts = Arc::new(analyze(program, slots, &is_ref));
    let checked = validate::check(program, slots, is_ref, &facts);
    assert!(
        checked.is_ok(),
        "protected-entry fact conformance: {checked:?}"
    );
    super::export::record(|export| {
        export.entry_protection = Some(facts.clone());
        export.entry_fact_witnesses = evidence::derive(program, &facts);
    });
    EntryScope {
        previous: CARRIED.with(|carried| carried.replace(Some(facts))),
        accesses: ACCESSES
            .with(|capture| capture.replace(Some((Vec::new(), FxHashSet::default())))),
    }
}

#[cfg(test)]
mod tests {
    mod coverage;
    use rustc_hir::{ItemKind, OwnerNode};

    use super::*;
    use crate::analyses::mir::{CallKind, TerminatorExt};

    struct Fixture {
        analysis: EntryAnalysis,
        parameters: Vec<EntryKey>,
        calls: Vec<(String, Location)>,
        exits: Vec<(Location, SourcePhase)>,
        legacy_loans: Vec<(usize, bool, usize)>,
        delta_checks: Vec<(&'static str, bool)>,
        replayed_accesses: Vec<SourceAccess>,
        receipts: Vec<evidence::FactWitness>,
        named_locals: Vec<(String, Local)>,
    }

    fn fixture(code: &str, name: &str, selected: &[(u32, u8)]) -> Fixture {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut functions = Vec::new();
            let mut structs = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else { continue };
                let OwnerNode::Item(item) = owner.node() else { continue };
                match item.kind {
                    ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                    ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                    _ => {}
                }
            }
            let function = *functions
                .iter()
                .find(|function| tcx.item_name(function.to_def_id()).as_str() == name)
                .expect("fixture function");
            let program = RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = CrateSlots::build(&program);
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let named_locals = body
                .var_debug_info
                .iter()
                .filter_map(|info| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => {
                        Some((info.name.to_string(), place.local))
                    }
                    _ => None,
                })
                .collect();
            let mut parameters = Vec::new();
            for index in 1..=body.arg_count {
                let parameter = Local::from_usize(index);
                for depth in 0..super::super::crate_slots::MAX_SLOT_DEPTH {
                    if let Some(slot) =
                        slots.fn_local_slots[&function].slot_for_local_depth(parameter, depth)
                    {
                        parameters.push(EntryKey {
                            function,
                            parameter,
                            depth,
                            slot: SlotRef::Local(function, slot),
                        });
                    }
                }
            }
            let selected: Vec<_> = parameters
                .iter()
                .filter(|entry| selected.contains(&(entry.parameter.as_u32(), entry.depth)))
                .map(|entry| entry.slot)
                .collect();
            let analysis = analyze(&program, &slots, |slot| selected.contains(&slot));
            let mut calls = Vec::new();
            let mut exits = Vec::new();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let location = Location {
                    block,
                    statement_index: data.statements.len(),
                };
                use rustc_middle::mir::{TerminatorKind, UnwindAction};
                match data.terminator().kind {
                    TerminatorKind::Return => exits.push((location, SourcePhase::Return)),
                    TerminatorKind::UnwindResume => exits.push((location, SourcePhase::Unwind)),
                    _ => {}
                }
                if matches!(
                    data.terminator().kind,
                    TerminatorKind::Call {
                        unwind: UnwindAction::Continue,
                        ..
                    } | TerminatorKind::Drop {
                        unwind: UnwindAction::Continue,
                        ..
                    } | TerminatorKind::Assert {
                        unwind: UnwindAction::Continue,
                        ..
                    } | TerminatorKind::InlineAsm {
                        unwind: UnwindAction::Continue,
                        ..
                    }
                ) {
                    exits.push((location, SourcePhase::Unwind));
                }
                if let Some(call) = data.terminator().as_call(tcx) {
                    let name = match call.func {
                        CallKind::LibC(name) => name.to_string(),
                        CallKind::FreeStanding(function) => {
                            tcx.item_name(function.to_def_id()).to_string()
                        }
                        CallKind::RustLib(function) => tcx.item_name(function).to_string(),
                        _ => continue,
                    };
                    calls.push((name, location));
                }
            }
            let legacy_loans = super::super::borrow_engine::loan_liveness_census(
                &program,
                |_| |_| true,
                |_| |_| true,
            )[&function]
                .clone();
            let validation =
                validate::check(&program, &slots, |slot| selected.contains(&slot), &analysis);
            assert!(
                validation.is_ok(),
                "unmodified fixture fact mismatch: {validation:?}"
            );
            let mut delta_checks = vec![("unmodified", validation.is_ok())];
            if !analysis.entries.is_empty()
                && !analysis.observations.is_empty()
                && !analysis.binding_facts.is_empty()
            {
                let mut mutants = Vec::new();
                let mut changed = analysis.clone();
                changed.entries.remove(0);
                mutants.push(("missing entry", changed));
                let mut changed = analysis.clone();
                changed.entries.push(changed.entries[0].clone());
                mutants.push(("duplicate entry", changed));
                let mut changed = analysis.clone();
                changed.observations.remove(0);
                mutants.push(("missing point", changed));
                let mut changed = analysis.clone();
                changed.observations[0].live = false;
                changed.observations[0].demand = None;
                mutants.push(("early protection end", changed));
                let mut changed = analysis.clone();
                changed.observations[0].target.dereferences += 1;
                mutants.push(("wrong target depth", changed));
                let mut changed = analysis.clone();
                changed.binding_facts.remove(0);
                mutants.push(("missing descendant", changed));
                let mut changed = analysis.clone();
                let mut extra = changed.binding_facts[0].clone();
                extra.moment = EntryMoment::AfterExit;
                changed.binding_facts.push(extra);
                mutants.push(("binding survives exit", changed));
                for (name, changed) in mutants {
                    delta_checks.push((
                        name,
                        validate::check(
                            &program,
                            &slots,
                            |slot| selected.contains(&slot),
                            &changed,
                        )
                        .is_err(),
                    ));
                }
            }
            let (_, replayed) = super::super::export::with_bo_export(|| {
                super::super::borrow_verify::revalidate_replaying(
                    &program,
                    &slots,
                    |slot| selected.contains(&slot),
                    |slot| !selected.contains(&slot),
                    true,
                )
            });
            assert_eq!(
                replayed.entry_protection.as_deref(),
                Some(&analysis),
                "replay must carry the validated entry facts"
            );
            Fixture {
                analysis,
                parameters,
                calls,
                exits,
                legacy_loans,
                delta_checks,
                replayed_accesses: replayed.entry_accesses,
                receipts: replayed.entry_fact_witnesses,
                named_locals,
            }
        })
        .unwrap_or_else(|error| error.raise())
    }

    fn key(fixture: &Fixture, parameter: u32, depth: u8) -> EntryKey {
        *fixture
            .parameters
            .iter()
            .find(|entry| entry.parameter.as_u32() == parameter && entry.depth == depth)
            .expect("actual parameter slot")
    }

    fn obligation(fixture: &Fixture, key: EntryKey) -> &EntryObligation {
        fixture
            .analysis
            .entries
            .iter()
            .find(|entry| entry.key == key)
            .expect("Ref parameter needs a BO-owned entry obligation")
    }

    fn observation(
        fixture: &Fixture,
        entry: EntryKey,
        location: Location,
        phase: SourcePhase,
        moment: EntryMoment,
    ) -> &EntryObservation {
        fixture
            .analysis
            .observations
            .iter()
            .find(|point| {
                point.entry == entry
                    && point.location == location
                    && point.phase == phase
                    && point.moment == moment
            })
            .expect("entry liveness/demand must include this original source phase")
    }

    #[test]
    fn e5_p_live_last_source_use_does_not_end_incoming_protection() {
        let fixture = fixture(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn last_use(p: *mut u8, alias: *mut u8) -> u8 { let value = *p; free(alias); value }",
            "last_use",
            &[(1, 0)],
        );
        let entry = key(&fixture, 1, 0);
        let target = IncomingTarget {
            entry,
            dereferences: 1,
        };
        assert_eq!(obligation(&fixture, entry).target, target);
        assert_eq!(
            fixture.analysis.entries.len(),
            1,
            "Raw alias is not an entry protector"
        );
        let free = fixture
            .calls
            .iter()
            .find(|(name, _)| name == "free")
            .unwrap()
            .1;
        let point = observation(
            &fixture,
            entry,
            free,
            SourcePhase::Call,
            EntryMoment::AtEvent,
        );
        assert!(point.live);
        assert_eq!(point.demand, Some(entry));
        assert_eq!(point.target, target);
    }

    #[test]
    fn e5_p_live_rebind_changes_binding_but_not_incoming_target() {
        let fixture = fixture(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn rebound(mut p: *mut u8, replacement: *mut u8) -> u8 { let alias = p; let value = *p; p = replacement; free(alias); value + *p }",
            "rebound",
            &[(1, 0)],
        );
        let entry = key(&fixture, 1, 0);
        let replacement = key(&fixture, 2, 0);
        let original = IncomingTarget {
            entry,
            dereferences: 1,
        };
        assert_eq!(obligation(&fixture, entry).target, original);
        assert_eq!(fixture.analysis.entries.len(), 1);
        let free = fixture
            .calls
            .iter()
            .find(|(name, _)| name == "free")
            .unwrap()
            .1;
        let point = observation(
            &fixture,
            entry,
            free,
            SourcePhase::Call,
            EntryMoment::AtEvent,
        );
        assert!(point.live);
        assert_eq!(point.demand, Some(entry));
        assert_eq!(point.target, original);
        assert_eq!(
            point.current_binding,
            CurrentBinding::Incoming(IncomingTarget {
                entry: replacement,
                dereferences: 1
            })
        );
    }

    #[test]
    fn e5_p_live_covers_exit_microevent_and_ends_after_exit() {
        for (code, name, phase) in [
            (
                "pub unsafe fn returned(p: *const u8) -> u8 { *p }",
                "returned",
                SourcePhase::Return,
            ),
            (
                "pub unsafe fn unwound(p: *const u8) { let value = *p; core::hint::black_box(value); panic!(\"source fixture\"); }",
                "unwound",
                SourcePhase::Unwind,
            ),
        ] {
            let fixture = fixture(code, name, &[(1, 0)]);
            let entry = key(&fixture, 1, 0);
            let exits: Vec<_> = fixture
                .exits
                .iter()
                .filter(|(_, found)| *found == phase)
                .collect();
            assert!(
                !exits.is_empty(),
                "original MIR must contain the source exit"
            );
            for &&(location, phase) in &exits {
                let during = observation(&fixture, entry, location, phase, EntryMoment::AtEvent);
                assert!(during.live);
                assert_eq!(during.demand, Some(entry));
                let after = observation(&fixture, entry, location, phase, EntryMoment::AfterExit);
                assert!(!after.live);
                assert_eq!(after.demand, None);
            }
        }
    }

    #[test]
    fn e5_p_live_nullable_parameter_keeps_conditional_entry_obligation() {
        let fixture = fixture(
            "pub unsafe fn nullable(p: *const u8) -> u8 { if p.is_null() { 0 } else { *p } }",
            "nullable",
            &[(1, 0)],
        );
        let entry = key(&fixture, 1, 0);
        assert_eq!(
            obligation(&fixture, entry).condition,
            EntryCondition::IfNonNull
        );
        assert_eq!(fixture.analysis.entries.len(), 1);
    }

    #[test]
    fn e5_p_live_entry_is_owned_even_without_a_legacy_loan() {
        let fixture = fixture(
            "pub unsafe fn read(p: *const u8) -> u8 { *p }",
            "read",
            &[(1, 0)],
        );
        assert!(
            fixture.legacy_loans.is_empty(),
            "this witness has no legacy loan to extend"
        );
        let entry = key(&fixture, 1, 0);
        assert_eq!(
            obligation(&fixture, entry).representation,
            EntryRepresentation::MissingLegacyLoan
        );
        assert_eq!(fixture.analysis.entries.len(), 1);
    }

    #[test]
    fn e5_p_live_raw_parameters_create_no_ref_protector() {
        let fixture = fixture("pub unsafe fn read(p: *const u8) -> u8 { *p }", "read", &[]);
        assert!(fixture.analysis.entries.is_empty());
        assert!(fixture.analysis.observations.is_empty());
    }

    #[test]
    fn e5_p_live_independent_validator_rejects_missing_extra_and_wrong_depth_facts() {
        let fixture = fixture(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn copied(p: *mut u8) -> u8 { let q = p; let value = *q; free(q); value }",
            "copied",
            &[(1, 0)],
        );
        assert_eq!(
            fixture.delta_checks.len(),
            8,
            "all nonvacuous fact mutations must be exercised"
        );
        for (name, correct) in fixture.delta_checks {
            assert!(
                correct,
                "independent raw-CFG/entry/kill validator failed: {name}"
            );
        }
    }

    #[test]
    fn e5_p_live_loanless_accesses_reach_the_entry_fact_carrier() {
        let fixture = fixture(
            "pub unsafe fn accessed(p: *mut u8) -> u8 { *p = 3; *p }",
            "accessed",
            &[(1, 0)],
        );
        assert!(
            fixture.legacy_loans.is_empty(),
            "source access must not depend on a legacy loan"
        );
        let entry = key(&fixture, 1, 0);
        for mode in [AccessMode::Read, AccessMode::Write] {
            assert!(
                fixture
                    .replayed_accesses
                    .iter()
                    .any(|access| access.function == entry.function
                        && access.place.local == entry.parameter
                        && access.place.proj == [super::super::export::ProjKey::Deref]
                        && access.mode == mode
                        && access.cause == AccessCause::Ordinary),
                "the unfiltered {mode:?} must reach entry invalidation/extraction"
            );
        }
    }

    #[test]
    fn e5_p_live_error_intersection_keeps_the_source_dead_entry_owner() {
        let fixture = fixture(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn last_use(p: *mut u8, alias: *mut u8) -> u8 { let value = *p; free(alias); value }",
            "last_use",
            &[(1, 0)],
        );
        let entry = key(&fixture, 1, 0);
        let free = fixture
            .calls
            .iter()
            .find(|(name, _)| name == "free")
            .unwrap()
            .1;
        assert_eq!(
            fixture.analysis.repair_target_for_invalidation(
                entry,
                free,
                SourcePhase::Call,
                EntryMoment::AtEvent
            ),
            Ok(Some(entry.slot))
        );
        for &(exit, phase) in &fixture.exits {
            assert_eq!(
                fixture.analysis.repair_target_for_invalidation(
                    entry,
                    exit,
                    phase,
                    EntryMoment::AfterExit
                ),
                Ok(None)
            );
        }
    }

    #[test]
    fn e5_p_live_witness_receipts_cover_every_new_fact_and_exit_phase() {
        let fixture = fixture(
            "pub unsafe fn copied(p: *mut u8) -> u8 { let q = p; *q }",
            "copied",
            &[(1, 0)],
        );
        let expected: FxHashSet<_> = fixture
            .analysis
            .entries
            .iter()
            .cloned()
            .map(validate::Fact::Entry)
            .chain(
                fixture
                    .analysis
                    .observations
                    .iter()
                    .cloned()
                    .map(validate::Fact::Observation),
            )
            .chain(
                fixture
                    .analysis
                    .binding_facts
                    .iter()
                    .cloned()
                    .map(validate::Fact::Binding),
            )
            .collect();
        assert_eq!(fixture.receipts.len(), expected.len());
        assert_eq!(
            fixture
                .receipts
                .iter()
                .map(|row| row.fact.clone())
                .collect::<FxHashSet<_>>(),
            expected
        );
        assert!(fixture.receipts.iter().any(|row| matches!(&row.fact, validate::Fact::Binding(binding) if binding.local != binding.target.entry.parameter) && !row.predecessors.is_empty()), "copied descendants need located witnesses");
        for row in &fixture.receipts {
            if let validate::Fact::Observation(point) = &row.fact
                && point.moment == EntryMoment::AfterExit
            {
                assert_eq!(
                    row.predecessors,
                    vec![evidence::SourcePoint {
                        function: point.entry.function,
                        location: point.location,
                        phase: point.phase,
                        moment: EntryMoment::AtEvent
                    }]
                );
            }
        }
    }
}
