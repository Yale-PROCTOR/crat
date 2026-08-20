#[cfg(test)]
use std::cell::Cell;
use std::time::{Duration, Instant};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{
    Body, Local, Location, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind,
    visit::{PlaceContext, Visitor},
};
use rustc_mir_dataflow::Analysis;
use rustc_span::def_id::LocalDefId;

#[cfg(test)]
use super::coherence::add_coherence_tagging_uses;
use super::{
    BoOwnEmissionStats, CrateCtxt, SlotKind,
    borrow_verify::{
        verify_to_fixpoint_counting_with_flows,
        verify_to_fixpoint_counting_with_flows_and_copy_lends,
    },
    boundary_table::{self, Matcher, Role},
    coherence::{
        CopyLendPair, add_coherence, add_coherence_removal_only, add_coherence_with_copy_lends,
    },
    crate_slots::CrateSlots,
    emit_crate_ownership_constraints, emit_crate_ownership_constraints_with_copy_lends,
    l2::{MirLocationKey, SlotKey},
    mutability_facts::MutFacts,
    origin_flow::OriginFlowResults,
    origin_summary::OriginSummaries,
    resolve::{ResolvedSlot, resolve_place},
    slots::SlotOwner,
    solver::{KindSolver, Selectors, SlotRef},
};
use crate::{
    analyses::{
        liveness::MaybeLiveLocals,
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

pub(crate) const COPY_LEND_MODE_ENV: &str = "CRAT_BO_COPY_LEND_MODE";

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum CopyLendMode {
    #[default]
    Baseline,
    RemovalOnly,
    LendArm,
}

impl CopyLendMode {
    pub(crate) fn current() -> Self {
        #[cfg(test)]
        if let Some(mode) = COPY_LEND_MODE_OVERRIDE.with(Cell::get) {
            return mode;
        }
        match std::env::var(COPY_LEND_MODE_ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("baseline") => Self::Baseline,
            Ok("removal_only") => Self::RemovalOnly,
            Ok("lend_arm") => Self::LendArm,
            Ok(other) => panic!(
                "{COPY_LEND_MODE_ENV} must be baseline, removal_only, or lend_arm; got {other:?}"
            ),
            Err(error) => panic!("{COPY_LEND_MODE_ENV} is not valid Unicode: {error}"),
        }
    }

    #[cfg(test)]
    pub(crate) fn with_override<T>(self, f: impl FnOnce() -> T) -> T {
        struct Restore(Option<CopyLendMode>);
        impl Drop for Restore {
            fn drop(&mut self) {
                COPY_LEND_MODE_OVERRIDE.with(|slot| slot.set(self.0));
            }
        }
        let _restore = Restore(COPY_LEND_MODE_OVERRIDE.with(|slot| slot.replace(Some(self))));
        f()
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::RemovalOnly => "removal_only",
            Self::LendArm => "lend_arm",
        }
    }
}

#[cfg(test)]
thread_local! {
    static COPY_LEND_MODE_OVERRIDE: Cell<Option<CopyLendMode>> = const { Cell::new(None) };
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CopyLendEligibility {
    pub(crate) pairs: FxHashSet<CopyLendPair>,
    pub(crate) sites: Vec<CopyLendSite>,
}

pub(crate) struct BoConstruction {
    pub(crate) mode: CopyLendMode,
    pub(crate) selectors: Selectors,
    pub(crate) eligibility: CopyLendEligibility,
    pub(crate) stats: BoOwnEmissionStats,
    pub(crate) eligibility_elapsed: Duration,
    pub(crate) emit_elapsed: Duration,
    pub(crate) coherence_elapsed: Duration,
}

pub(crate) fn construct_bo_into(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    mut_facts: &MutFacts,
    solver: &KindSolver,
    mode: CopyLendMode,
) -> anyhow::Result<BoConstruction> {
    let crate_ctxt = CrateCtxt::new(program);
    let t = Instant::now();
    let eligibility = if mode == CopyLendMode::LendArm {
        analyze_copy_lend_eligibility(program, slots, mut_facts, origins.native_flows())
    } else {
        CopyLendEligibility::default()
    };
    let eligibility_elapsed = t.elapsed();
    let t = Instant::now();
    let (stats, selectors) = match mode {
        CopyLendMode::LendArm => emit_crate_ownership_constraints_with_copy_lends(
            &crate_ctxt,
            slots,
            origins,
            solver,
            &eligibility.pairs,
        )?,
        CopyLendMode::Baseline | CopyLendMode::RemovalOnly => {
            emit_crate_ownership_constraints(&crate_ctxt, slots, origins, solver)?
        }
    };
    let emit_elapsed = t.elapsed();
    let t = Instant::now();
    if let Some(tracker) = solver.tracker() {
        tracker.set_context("coherence");
    }
    for &fn_did in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        match mode {
            CopyLendMode::Baseline => add_coherence(solver, slots, fn_did, &body),
            CopyLendMode::RemovalOnly => add_coherence_removal_only(solver, slots, fn_did, &body),
            CopyLendMode::LendArm => {
                add_coherence_with_copy_lends(solver, slots, fn_did, &body, &eligibility.pairs)
            }
        }
    }
    let coherence_elapsed = t.elapsed();
    Ok(BoConstruction {
        mode,
        selectors,
        eligibility,
        stats,
        eligibility_elapsed,
        emit_elapsed,
        coherence_elapsed,
    })
}

/// D1-authorized parked-census migration: shared construction, baseline mode, with the harness's
/// existing Use-family tracking preserved exactly. No eligibility or lend behavior is reachable.
#[cfg(test)]
pub(crate) fn construct_tracked_census_baseline(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
) -> anyhow::Result<BoConstruction> {
    let crate_ctxt = CrateCtxt::new(program);
    let t = Instant::now();
    let (stats, selectors) = emit_crate_ownership_constraints(&crate_ctxt, slots, origins, solver)?;
    let emit_elapsed = t.elapsed();
    let t = Instant::now();
    solver
        .tracker()
        .expect("tracked census construction")
        .set_context("coherence");
    for &fn_did in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        add_coherence_tagging_uses(solver, slots, fn_did, &body);
    }
    Ok(BoConstruction {
        mode: CopyLendMode::Baseline,
        selectors,
        eligibility: CopyLendEligibility::default(),
        stats,
        eligibility_elapsed: Duration::ZERO,
        emit_elapsed,
        coherence_elapsed: t.elapsed(),
    })
}

pub(crate) fn verify_bo_construction(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    verify_bo_construction_counting(program, slots, origins, solver, construction, mut_facts).0
}

/// Verify a shared construction against an explicitly supplied flow graph. This is reserved for
/// diagnostic constructions that deliberately substitute the origin summaries while replaying the
/// production flow facts; the construction mode still owns emission/coherence selection.
pub(crate) fn verify_bo_construction_with_flows(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    assert_ne!(
        construction.mode,
        CopyLendMode::LendArm,
        "a lend-arm construction must replay the same native flows that produced eligibility"
    );
    verify_to_fixpoint_counting_with_flows(
        program,
        slots,
        origin_flows,
        solver,
        &construction.selectors,
        mut_facts,
    )
    .0
}

pub(crate) fn verify_bo_construction_counting(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &OriginSummaries,
    solver: &KindSolver,
    construction: &BoConstruction,
    mut_facts: &MutFacts,
) -> (
    Option<FxHashMap<SlotRef, SlotKind>>,
    super::borrow_verify::RoundStats,
) {
    match construction.mode {
        CopyLendMode::LendArm => verify_to_fixpoint_counting_with_flows_and_copy_lends(
            program,
            slots,
            origins.native_flows(),
            solver,
            &construction.selectors,
            mut_facts,
            &construction.eligibility.pairs,
        ),
        CopyLendMode::Baseline | CopyLendMode::RemovalOnly => {
            verify_to_fixpoint_counting_with_flows(
                program,
                slots,
                origins.native_flows(),
                solver,
                &construction.selectors,
                mut_facts,
            )
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CopyLendSite {
    pub(crate) fn_did: LocalDefId,
    pub(crate) location: MirLocationKey,
    pub(crate) lhs: SlotRef,
    pub(crate) rhs: SlotRef,
    pub(crate) lhs_local: Local,
    pub(crate) rhs_local: Local,
}

impl CopyLendSite {
    fn sort_key(self) -> (u32, MirLocationKey, SlotKey, SlotKey) {
        (
            self.fn_did.local_def_index.as_u32(),
            self.location,
            SlotKey::of(self.lhs),
            SlotKey::of(self.rhs),
        )
    }
}

pub(crate) fn analyze_copy_lend_eligibility(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    mut_facts: &MutFacts,
    origin_flows: &OriginFlowResults,
) -> CopyLendEligibility {
    let mut eligible = CopyLendEligibility::default();
    for &fn_did in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let candidates = collect_copy_sites(slots, fn_did, &body);
        if candidates.is_empty() {
            continue;
        }
        let mut by_pair: FxHashMap<CopyLendPair, Vec<CopyLendSite>> = FxHashMap::default();
        for site in candidates {
            by_pair
                .entry(CopyLendPair::new(site.lhs, site.rhs))
                .or_default()
                .push(site);
        }
        let flows = origin_flows
            .get(&fn_did)
            .unwrap_or_else(|| panic!("missing origin flow for {fn_did:?}"));
        let value_flows = flows.body.depth0_value_flows();
        let live_before = live_before_by_location(program.tcx, &body);

        for (pair, mut sites) in by_pair {
            sites.sort_by_key(|site| site.sort_key());
            let lhs_local = sites[0].lhs_local;
            if mut_facts.is_mutable(fn_did, lhs_local) {
                continue;
            }
            let closure = owner_closure(
                [
                    SlotOwner::Local(sites[0].lhs_local),
                    SlotOwner::Local(sites[0].rhs_local),
                ],
                &value_flows,
            );
            let destination_flow =
                owner_closure([SlotOwner::Local(sites[0].lhs_local)], &value_flows);
            if closure
                .iter()
                .any(|owner| matches!(owner, SlotOwner::Field(_)))
                || destination_flows_to_deallocator(program.tcx, &body, &destination_flow)
                || has_live_outward_event(program, slots, fn_did, &body, &closure, &live_before)
            {
                continue;
            }
            eligible.pairs.insert(pair);
            eligible.sites.extend(sites);
        }
    }
    eligible.sites.sort_by_key(|site| site.sort_key());
    eligible
}

fn collect_copy_sites(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'_>,
) -> Vec<CopyLendSite> {
    let mut sites = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(box (lhs_place, rvalue)) = &statement.kind else {
                continue;
            };
            let rhs_place = match rvalue {
                Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                | Rvalue::CopyForDeref(rhs) => rhs,
                _ => continue,
            };
            let (Some(ResolvedSlot::Local(lhs_slot)), Some(ResolvedSlot::Local(rhs_slot))) = (
                resolve_place(slots, fn_did, body, *lhs_place, 0, None),
                resolve_place(slots, fn_did, body, *rhs_place, 0, None),
            ) else {
                continue;
            };
            let universe = slots
                .fn_local_slots
                .get(&fn_did)
                .unwrap_or_else(|| panic!("missing local slots for {fn_did:?}"));
            let lhs_data = universe.slot(lhs_slot);
            let rhs_data = universe.slot(rhs_slot);
            if lhs_data.depth != 0
                || rhs_data.depth != 0
                || lhs_data.owner != SlotOwner::Local(lhs_place.local)
                || rhs_data.owner != SlotOwner::Local(rhs_place.local)
            {
                continue;
            }
            sites.push(CopyLendSite {
                fn_did,
                location: MirLocationKey::new(block.as_u32(), statement_index),
                lhs: SlotRef::Local(fn_did, lhs_slot),
                rhs: SlotRef::Local(fn_did, rhs_slot),
                lhs_local: lhs_place.local,
                rhs_local: rhs_place.local,
            });
        }
    }
    sites
}

fn owner_closure(
    roots: impl IntoIterator<Item = SlotOwner>,
    value_flows: &[(SlotOwner, SlotOwner)],
) -> FxHashSet<SlotOwner> {
    let mut closure: FxHashSet<_> = roots.into_iter().collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &(source, target) in value_flows {
            if closure.contains(&source) {
                changed |= closure.insert(target);
            }
        }
    }
    closure
}

fn live_before_by_location<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> FxHashMap<Location, DenseBitSet<Local>> {
    let mut cursor = MaybeLiveLocals
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);
    let mut answer = FxHashMap::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let count = data.statements.len() + data.terminator.is_some() as usize;
        for statement_index in 0..count {
            let location = Location {
                block,
                statement_index,
            };
            cursor.seek_before_primary_effect(location);
            answer.insert(location, cursor.get().clone());
        }
    }
    answer
}

fn closure_live(closure: &FxHashSet<SlotOwner>, live: &DenseBitSet<Local>) -> bool {
    closure
        .iter()
        .any(|owner| matches!(owner, SlotOwner::Local(local) if live.contains(*local)))
}

fn rvalue_mentions_closure(
    rvalue: &Rvalue<'_>,
    location: Location,
    closure: &FxHashSet<SlotOwner>,
) -> bool {
    struct ClosureUse<'a> {
        closure: &'a FxHashSet<SlotOwner>,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for ClosureUse<'_> {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            self.found |= self.closure.contains(&SlotOwner::Local(place.local));
            self.super_place(place, context, location);
        }
    }

    let mut visitor = ClosureUse {
        closure,
        found: false,
    };
    visitor.visit_rvalue(rvalue, location);
    visitor.found
}

fn known_deallocator(call: &crate::analyses::mir::terminator::MirFunctionCall<'_, '_>) -> bool {
    let CallKind::LibC(name) = &call.func else {
        return false;
    };
    boundary_table::lookup(name.as_str(), Matcher::ForeignC)
        .is_some_and(|entry| entry.roles.contains(&Role::Sink))
}

fn exact_free(call: &crate::analyses::mir::terminator::MirFunctionCall<'_, '_>) -> bool {
    let CallKind::LibC(name) = &call.func else {
        return false;
    };
    boundary_table::lookup(name.as_str(), Matcher::ForeignC)
        .is_some_and(|entry| entry.roles == [Role::Sink])
}

fn destination_flows_to_deallocator<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    destination_flow: &FxHashSet<SlotOwner>,
) -> bool {
    body.basic_blocks.iter().any(|data| {
        let Some(terminator) = data.terminator.as_ref() else {
            return false;
        };
        let Some(call) = terminator.as_call(tcx) else {
            return false;
        };
        known_deallocator(&call)
            && call.args.first().is_some_and(|arg| {
                arg.node
                    .place()
                    .is_some_and(|place| destination_flow.contains(&SlotOwner::Local(place.local)))
            })
    })
}

fn boundary_call(call: &crate::analyses::mir::terminator::MirFunctionCall<'_, '_>) -> bool {
    match call.func {
        CallKind::FreeStanding(_) | CallKind::Impl(_) => true,
        CallKind::LibC(_) => !exact_free(call),
        CallKind::RustLib(_) | CallKind::Closure | CallKind::Dynamic => true,
    }
}

fn has_live_outward_event<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    closure: &FxHashSet<SlotOwner>,
    live_before: &FxHashMap<Location, DenseBitSet<Local>>,
) -> bool {
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if !closure_live(closure, &live_before[&location]) {
                continue;
            }
            let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                continue;
            };
            if !rvalue.ty(body, program.tcx).is_any_ptr()
                && !matches!(rvalue, Rvalue::Aggregate(..))
            {
                continue;
            }
            if !rvalue_mentions_closure(rvalue, location, closure) {
                continue;
            }
            if matches!(rvalue, Rvalue::Aggregate(..)) {
                return true;
            }
            if lhs
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Field(..)))
            {
                return true;
            }
            if lhs.local == RETURN_PLACE {
                return true;
            }
            match resolve_place(slots, fn_did, body, *lhs, 0, None) {
                Some(ResolvedSlot::Local(_)) => {}
                Some(ResolvedSlot::Field(_)) | None => return true,
            }
        }
        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        if !closure_live(closure, &live_before[&location]) {
            continue;
        }
        let Some(call) = terminator.as_call(program.tcx) else {
            continue;
        };
        if boundary_call(&call)
            && call.args.iter().any(|arg| {
                arg.node
                    .place()
                    .is_some_and(|place| closure.contains(&SlotOwner::Local(place.local)))
            })
        {
            return true;
        }
    }
    false
}
