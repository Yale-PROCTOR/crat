//! Source-retirement review, separate from ordinary loan invalidation matrices.
//! All object identities are abstractions; no static site proves a dynamic epoch.

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::Location;
use rustc_mir_dataflow::points::PointIndex;
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::CrateSlots,
    export::PlaceKey,
    protected_entry::{self, EntryAnalysis, EntryCoverageError, EntryKey, EntryMoment},
    slot_key,
    slots::{SlotId, SlotOwner},
    solver::SlotRef,
    source_events::{self, Coverage, SourceEventKey, SourceEvents, SourcePhase, SourceRole},
};
use crate::{
    analyses::borrow::{BorrowInferenceResults, Loan, ProvenanceOwner, StructFieldSlot},
    utils::rustc::RustProgram,
};

pub(crate) mod call_reach;
pub(crate) mod local_outcome;
#[cfg(test)]
mod local_outcome_tests;
mod objects;
mod return_origin;
mod routes;
#[cfg(test)]
mod tests_return_origin;

use objects::{ObjectFacts, ObjectRoot, ObjectSet};
use routes::{FrameEvent, RoutedEvents};
pub(crate) use routes::{RouteProblem, RouteReason, RouteStep};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OverlapReason {
    SameAbstractRoot,
    PossibleInputAlias,
    UnknownObjects,
    UnresolvedInvocation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LoanIdentity {
    /// Diagnostic index only; reservation/place/owners retain the actual witness.
    pub(crate) index: usize,
    pub(crate) reservation: Location,
    pub(crate) borrowed: PlaceKey,
    pub(crate) owners: Vec<ProvenanceOwner>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetirementConflict {
    pub(crate) function: LocalDefId,
    pub(crate) target: SlotRef,
    pub(crate) target_key: String,
    pub(crate) source: SourceEventKey,
    pub(crate) phase: SourcePhase,
    pub(crate) location: Location,
    pub(crate) route: Vec<RouteStep>,
    pub(crate) loan: Option<LoanIdentity>,
    pub(crate) entry: Option<EntryKey>,
    pub(crate) overlap: OverlapReason,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum UnresolvedReason {
    Route(RouteProblem),
    MissingEntryFacts,
    DifferentEntryFacts,
    Entry(EntryCoverageError),
    MissingOwner {
        loan: usize,
        owner: Option<ProvenanceOwner>,
    },
    MissingInnerLoan {
        slot: SlotRef,
        depth: u8,
    },
    MissingSlotKey(SlotRef),
    MissingContext,
    DuplicateContext,
    UnexpectedContext,
    MissingSourceEvent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetirementUnresolved {
    pub(crate) source: Option<SourceEventKey>,
    pub(crate) function: Option<LocalDefId>,
    pub(crate) location: Option<Location>,
    pub(crate) phase: Option<SourcePhase>,
    pub(crate) route: Vec<RouteStep>,
    pub(crate) reason: UnresolvedReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CoverageDisposition {
    Unreachable,
    Null,
    InactiveStorage,
    UnaddressedStorage,
    IrrelevantNoSafeHolder,
    /// All currently represented obligations were examined. A conflict or
    /// unresolved row still prevents acceptance; this is not a soundness proof.
    Checked,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContextCoverage {
    pub(crate) source: SourceEventKey,
    pub(crate) function: LocalDefId,
    pub(crate) location: Location,
    pub(crate) phase: SourcePhase,
    pub(crate) route: Vec<RouteStep>,
    pub(crate) disposition: CoverageDisposition,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RetirementReview {
    pub(crate) conflicts: Vec<RetirementConflict>,
    pub(crate) demotions: Vec<local_outcome::Demotion>,
    pub(crate) unresolved: Vec<RetirementUnresolved>,
    pub(crate) coverage: Vec<ContextCoverage>,
    /// Actual ordinary error points, kept separate from the loan inventory.
    pub(crate) ordinary_error_points: usize,
    pub(crate) terminal: BTreeMap<SourceEventKey, EventDisposition>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EventDisposition {
    Irrelevant,
    CheckedWithoutConflict,
    Conflict,
    Unresolved,
}

impl RetirementReview {
    pub(crate) fn targets(&self) -> Vec<SlotRef> {
        self.conflicts
            .iter()
            .map(|row| (row.target_key.clone(), row.target))
            .collect::<BTreeMap<_, _>>()
            .into_values()
            .collect()
    }
}

fn residual(event: &FrameEvent, reason: UnresolvedReason) -> RetirementUnresolved {
    RetirementUnresolved {
        source: Some(event.source.key.clone()),
        function: Some(event.frame),
        location: Some(event.location),
        phase: Some(event.phase),
        route: event.route.clone(),
        reason,
    }
}

fn overlap(
    left: &ObjectSet,
    right: &ObjectSet,
    frame: LocalDefId,
    heap_only: bool,
) -> Option<OverlapReason> {
    if (!left.unknown && left.roots.is_empty()) || (!right.unknown && right.roots.is_empty()) {
        return None;
    }
    // Under P0, free/realloc cannot retire a known stack object. A set with an
    // unknown alternative is not a known-stack-only set.
    if heap_only
        && ((!left.unknown
            && left
                .roots
                .iter()
                .all(|root| matches!(root, ObjectRoot::Stack { .. })))
            || (!right.unknown
                && right
                    .roots
                    .iter()
                    .all(|root| matches!(root, ObjectRoot::Stack { .. }))))
    {
        return None;
    }
    if left.unknown || right.unknown {
        return Some(OverlapReason::UnknownObjects);
    }
    let mut reason = None;
    for a in &left.roots {
        for b in &right.roots {
            if heap_only
                && (matches!(a, ObjectRoot::Stack { .. }) || matches!(b, ObjectRoot::Stack { .. }))
            {
                continue;
            }
            if a == b {
                return Some(OverlapReason::SameAbstractRoot);
            }
            let pair = match (*a, *b) {
                (ObjectRoot::Stack { .. }, ObjectRoot::Stack { .. }) => None,
                (
                    ObjectRoot::Fresh { frame: born, .. },
                    ObjectRoot::Input { .. } | ObjectRoot::Stack { .. },
                )
                | (
                    ObjectRoot::Input { .. } | ObjectRoot::Stack { .. },
                    ObjectRoot::Fresh { frame: born, .. },
                ) if born == frame => None,
                (ObjectRoot::Fresh { frame: a, .. }, ObjectRoot::Fresh { frame: b, .. })
                    if a == frame && b == frame =>
                {
                    None
                }
                // Concrete Stack roots here are created in this invocation or a
                // routed callee. A valid incoming reference precedes that storage;
                // an incoming pointer is never concretized to an ancestor's Stack
                // label by ObjectFacts. This is a frame relation, not name inequality.
                (ObjectRoot::Input { .. }, ObjectRoot::Stack { .. })
                | (ObjectRoot::Stack { .. }, ObjectRoot::Input { .. }) => None,
                (ObjectRoot::Input { .. }, ObjectRoot::Input { .. }) => {
                    Some(OverlapReason::PossibleInputAlias)
                }
                _ => Some(OverlapReason::UnresolvedInvocation),
            };
            // Choose the same conservative explanation independent of hash order.
            if pair == Some(OverlapReason::PossibleInputAlias) {
                reason = pair;
            } else if reason.is_none() {
                reason = pair;
            }
        }
    }
    reason
}

struct Context {
    source: Arc<SourceEvents>,
    entries: Arc<EntryAnalysis>,
    objects: ObjectFacts,
    routed: RoutedEvents,
    functions: Vec<LocalDefId>,
    keys: FxHashMap<SlotRef, String>,
    locals: FxHashMap<(LocalDefId, ProvenanceOwner), SlotRef>,
    fields: FxHashMap<StructFieldSlot, SlotRef>,
    refs: FxHashSet<SlotRef>,
    safe_holders: Vec<(SlotRef, Option<(LocalDefId, rustc_middle::mir::Local)>, u8)>,
    copy_graph: FxHashMap<SlotRef, Vec<SlotRef>>,
    exact_kinds: bool,
    unrepresented_inner: Vec<(SlotRef, Option<(LocalDefId, rustc_middle::mir::Local)>, u8)>,
    entry_consistent: bool,
    latest: FxHashMap<LocalDefId, RetirementReview>,
}

thread_local! {
    static CURRENT: RefCell<Option<Context>> = const { RefCell::new(None) };
    static MODEL: RefCell<Option<FxHashMap<SlotRef, super::SlotKind>>> = const { RefCell::new(None) };
}
pub(crate) struct ModelScope(Option<FxHashMap<SlotRef, super::SlotKind>>);
impl Drop for ModelScope {
    fn drop(&mut self) {
        MODEL.with(|model| model.replace(self.0.take()));
    }
}
pub(crate) fn model_scope(model: &FxHashMap<SlotRef, super::SlotKind>) -> ModelScope {
    ModelScope(MODEL.with(|current| current.replace(Some(model.clone()))))
}

pub(crate) struct RetirementScope {
    previous: Option<Context>,
    source_scope: Option<source_events::InventoryScope>,
    entry_scope: Option<protected_entry::EntryScope>,
    active: bool,
}

impl Drop for RetirementScope {
    fn drop(&mut self) {
        if self.active {
            CURRENT.with(|current| {
                current.replace(self.previous.take());
            });
        }
        self.entry_scope.take();
        self.source_scope.take();
    }
}

pub(crate) fn begin(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origin_flows: &crate::analyses::borrow_ownership::origin_flow::OriginFlowResults,
    is_ref: impl Fn(SlotRef) -> bool,
) -> RetirementScope {
    let source = source_events::for_construction(program);
    let source_scope = source_events::enter_inventory(&source);
    let entry_scope = protected_entry::current()
        .is_none()
        .then(|| protected_entry::for_model(program, slots, &is_ref));
    let entries = protected_entry::current().expect("validated parameter-entry scope");
    let objects = ObjectFacts::analyze(program, slots, &source, origin_flows);
    let routed = routes::expand(program, &source, &objects);
    let exact = MODEL.with(|current| current.borrow().clone());
    let mut context = Context {
        source,
        entries,
        objects,
        routed,
        functions: program.functions.clone(),
        keys: FxHashMap::default(),
        locals: FxHashMap::default(),
        fields: FxHashMap::default(),
        refs: FxHashSet::default(),
        safe_holders: Vec::new(),
        copy_graph: local_outcome::copy_graph(program, slots),
        exact_kinds: exact.is_some(),
        unrepresented_inner: Vec::new(),
        entry_consistent: true,
        latest: FxHashMap::default(),
    };
    let mut expected_entries = FxHashSet::default();
    for (&function, universe) in &slots.fn_local_slots {
        let argument_count = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow()
            .arg_count;
        for index in 0..universe.len() {
            let id = SlotId::from_usize(index);
            let slot = universe.slot(id);
            let SlotOwner::Local(local) = slot.owner else { continue };
            let reference = SlotRef::Local(function, id);
            context.keys.insert(
                reference,
                slot_key::local_key(program.tcx, function, local.as_usize(), slot.depth),
            );
            if slot.depth == 0 {
                context
                    .locals
                    .insert((function, ProvenanceOwner::Local(local)), reference);
            }
            // R251: only Ref carriers hold loans; Owning is handled by the ledger.
            let safe = is_ref(reference);
            if safe {
                context
                    .safe_holders
                    .push((reference, Some((function, local)), slot.depth));
            }
            if is_ref(reference) {
                context.refs.insert(reference);
                if local.as_usize() > 0 && local.as_usize() <= argument_count {
                    expected_entries.insert(reference);
                } else if slot.depth > 0 {
                    context.unrepresented_inner.push((
                        reference,
                        Some((function, local)),
                        slot.depth,
                    ));
                }
            }
        }
    }
    context.entry_consistent = expected_entries
        == context
            .entries
            .entries
            .iter()
            .map(|entry| entry.key.slot)
            .collect();
    for index in 0..slots.field_slots.len() {
        let id = SlotId::from_usize(index);
        let slot = slots.field_slots.slot(id);
        let SlotOwner::Field(field) = slot.owner else { continue };
        let reference = SlotRef::Field(id);
        context.keys.insert(
            reference,
            slot_key::field_key(program.tcx, field.struct_did, field.field_index, slot.depth),
        );
        if slot.depth == 0 {
            context.fields.insert(
                StructFieldSlot {
                    struct_did: field.struct_did,
                    field_index: field.field_index,
                },
                reference,
            );
        }
        // R251: only Ref carriers hold loans; Owning is handled by the ledger.
        let safe = is_ref(reference);
        if safe {
            context.safe_holders.push((reference, None, slot.depth));
        }
        if is_ref(reference) {
            context.refs.insert(reference);
            if slot.depth > 0 {
                context
                    .unrepresented_inner
                    .push((reference, None, slot.depth));
            }
        }
    }
    RetirementScope {
        previous: CURRENT.with(|current| current.replace(Some(context))),
        source_scope: Some(source_scope),
        entry_scope,
        active: true,
    }
}

impl Context {
    fn owner(&self, function: LocalDefId, owner: ProvenanceOwner) -> Option<SlotRef> {
        match owner {
            ProvenanceOwner::Local(_) => self.locals.get(&(function, owner)).copied(),
            ProvenanceOwner::Field(field) => self.fields.get(&field).copied(),
        }
    }

    fn conflict(
        &self,
        review: &mut RetirementReview,
        event: &FrameEvent,
        target: SlotRef,
        loan: Option<LoanIdentity>,
        entry: Option<EntryKey>,
        overlap: OverlapReason,
    ) {
        let Some(target_key) = self.keys.get(&target) else {
            review
                .unresolved
                .push(residual(event, UnresolvedReason::MissingSlotKey(target)));
            return;
        };
        review.conflicts.push(RetirementConflict {
            function: event.frame,
            target,
            target_key: target_key.clone(),
            source: event.source.key.clone(),
            phase: event.phase,
            location: event.location,
            route: event.route.clone(),
            loan,
            entry,
            overlap,
        });
    }

    fn review_function(
        &self,
        function: LocalDefId,
        facts: &BorrowInferenceResults<'_>,
        entry_facts: Option<&EntryAnalysis>,
        owners_at: impl Fn(Loan, PointIndex) -> Vec<ProvenanceOwner>,
    ) -> RetirementReview {
        let mut review = RetirementReview::default();
        review.ordinary_error_points = facts
            .errors
            .rows()
            .filter(|&point| {
                facts
                    .errors
                    .row(point)
                    .is_some_and(|loans| !loans.is_empty())
            })
            .count();
        for event in self.routed.frames.get(&function).into_iter().flatten() {
            let skip = if event.unreachable {
                Some(CoverageDisposition::Unreachable)
            } else {
                match event.source.coverage {
                    Coverage::IrrelevantNull => Some(CoverageDisposition::Null),
                    Coverage::IrrelevantInactiveStorage => {
                        Some(CoverageDisposition::InactiveStorage)
                    }
                    // The inventory assigns PointerStorage's irrelevant tag
                    // only when this cell is unaddressed. Addressed pointer
                    // cells carry UnresolvedStorage and must still be checked.
                    Coverage::IrrelevantPointerStorage | Coverage::IrrelevantUnaddressedStorage => {
                        Some(CoverageDisposition::UnaddressedStorage)
                    }
                    _ if !event.objects.unknown && event.objects.roots.is_empty() => {
                        Some(CoverageDisposition::Null)
                    }
                    _ => None,
                }
            };
            let heap_only = matches!(
                event.source.key.role,
                SourceRole::Free | SourceRole::ReallocOld
            );
            let holders = self.overlapping_holders(function, event, heap_only);
            let skip = skip.or_else(|| {
                (self.exact_kinds && !heap_only && holders.is_empty())
                    .then_some(CoverageDisposition::IrrelevantNoSafeHolder)
            });
            review.coverage.push(ContextCoverage {
                source: event.source.key.clone(),
                function,
                location: event.location,
                phase: event.phase,
                route: event.route.clone(),
                disposition: skip.unwrap_or(CoverageDisposition::Checked),
            });
            if skip.is_some() {
                continue;
            }
            // No new Ref materialization in this frame means no retirement
            // obligation here; caller protectors are checked in their routed
            // contexts. Unknown lifecycle identity alone is not a Ref conflict.
            if holders.is_empty() {
                continue;
            }
            let heap_only = matches!(
                event.source.key.role,
                SourceRole::Free | SourceRole::ReallocOld
            );
            // Native loan owners carry only the outer provenance. A deeper
            // non-entry Ref can keep an inner target live through Raw copies,
            // even after its source local's last use. Until that demand has an
            // exact loan/depth witness, possible retirement overlap demotes that holder.
            // Field instance flow is unrepresented here and remains Unknown.
            for &(slot, owner, depth) in &self.unrepresented_inner {
                let target = if let Some((owner_function, local)) = owner {
                    if owner_function != function {
                        continue;
                    }
                    self.objects.pointer_at(
                        function,
                        event.location,
                        &PlaceKey::from_place(rustc_middle::mir::Place::from(local)),
                        depth,
                    )
                } else {
                    ObjectSet::default()
                };
                if overlap(&target, &event.objects, function, heap_only).is_some() {
                    self.demote(
                        &mut review,
                        event,
                        slot,
                        local_outcome::Reason::InnerLoanMissing { depth },
                    );
                }
            }
            let active_entries: Vec<_> = self
                .entries
                .entries
                .iter()
                .filter(|entry| entry.key.function == function)
                .collect();
            if !active_entries.is_empty() {
                match entry_facts {
                    None => review
                        .unresolved
                        .push(residual(event, UnresolvedReason::MissingEntryFacts)),
                    Some(provided)
                        if !std::ptr::eq(provided, self.entries.as_ref())
                            && provided != self.entries.as_ref() =>
                    {
                        review
                            .unresolved
                            .push(residual(event, UnresolvedReason::DifferentEntryFacts))
                    }
                    _ => {}
                }
            }
            for entry in active_entries {
                let target = ObjectSet {
                    roots: FxHashSet::from_iter([ObjectRoot::Input {
                        function,
                        parameter: entry.key.parameter,
                        depth: entry.key.depth,
                    }]),
                    unknown: false,
                };
                let Some(reason) = overlap(&target, &event.objects, function, heap_only) else {
                    continue;
                };
                match self.entries.repair_target_for_invalidation(
                    entry.key,
                    event.location,
                    event.phase,
                    EntryMoment::AtEvent,
                ) {
                    Ok(Some(slot)) if self.refs.contains(&slot) => {
                        self.conflict(&mut review, event, slot, None, Some(entry.key), reason)
                    }
                    Ok(_) => review
                        .unresolved
                        .push(residual(event, UnresolvedReason::DifferentEntryFacts)),
                    Err(error) => review
                        .unresolved
                        .push(residual(event, UnresolvedReason::Entry(error))),
                }
            }
            let point = facts.location_map.point_from_location(event.location);
            for loan in facts
                .loan_liveness
                .row(point)
                .into_iter()
                .flat_map(|live| live.iter())
            {
                let data = &facts.borrow_set.loans[loan];
                let borrowed = PlaceKey::from_place(data.borrowed);
                // Resolve the value at reservation, never through a later rebinding.
                let target = self
                    .objects
                    .storage_at(function, data.location(), &borrowed);
                let Some(reason) = overlap(&target, &event.objects, function, heap_only) else {
                    continue;
                };
                let owners = owners_at(loan, point);
                if owners.is_empty() {
                    review.unresolved.push(residual(
                        event,
                        UnresolvedReason::MissingOwner {
                            loan: loan.index(),
                            owner: None,
                        },
                    ));
                    continue;
                }
                let mut candidates = BTreeMap::new();
                for &owner in &owners {
                    match self.owner(function, owner) {
                        None => review.unresolved.push(residual(
                            event,
                            UnresolvedReason::MissingOwner {
                                loan: loan.index(),
                                owner: Some(owner),
                            },
                        )),
                        Some(slot) if self.refs.contains(&slot) => {
                            if let Some(key) = self.keys.get(&slot) {
                                candidates.insert(key.clone(), slot);
                            } else {
                                review
                                    .unresolved
                                    .push(residual(event, UnresolvedReason::MissingSlotKey(slot)));
                            }
                        }
                        Some(_) => {}
                    }
                }
                if let Some((_, slot)) = candidates.into_iter().next() {
                    self.conflict(
                        &mut review,
                        event,
                        slot,
                        Some(LoanIdentity {
                            index: loan.index(),
                            reservation: data.location(),
                            borrowed,
                            owners,
                        }),
                        None,
                        reason,
                    );
                }
            }
        }
        review
    }
}

pub(crate) fn record_function(
    function: LocalDefId,
    facts: &BorrowInferenceResults<'_>,
    entry_facts: Option<&EntryAnalysis>,
    owners_at: impl Fn(Loan, PointIndex) -> Vec<ProvenanceOwner>,
) {
    CURRENT.with(|current| {
        if let Some(context) = current.borrow_mut().as_mut() {
            let review = context.review_function(function, facts, entry_facts, owners_at);
            // Raw-loan replay may revisit a function: only its latest facts count.
            context.latest.insert(function, review);
        }
    });
}

/// Snapshot before record_function borrows the scope. The native extraction
/// adapter uses it to preserve the existing A′ live-requirer priority.
pub(crate) fn owner_ref_status(function: LocalDefId) -> FxHashMap<ProvenanceOwner, bool> {
    CURRENT.with(|current| {
        let current = current.borrow();
        let Some(context) = current.as_ref() else { return FxHashMap::default() };
        context
            .locals
            .iter()
            .filter_map(|((owner, place), slot)| {
                (*owner == function).then_some((*place, context.refs.contains(slot)))
            })
            .chain(
                context.fields.iter().map(|(field, slot)| {
                    (ProvenanceOwner::Field(*field), context.refs.contains(slot))
                }),
            )
            .collect()
    })
}

type ContextKey = (
    SourceEventKey,
    u32,
    u32,
    usize,
    SourcePhase,
    Vec<(u32, u32, u32, usize)>,
);
fn context_key(
    source: &SourceEventKey,
    function: LocalDefId,
    location: Location,
    phase: SourcePhase,
    route: &[RouteStep],
) -> ContextKey {
    (
        source.clone(),
        function.local_def_index.as_u32(),
        location.block.as_u32(),
        location.statement_index,
        phase,
        route
            .iter()
            .map(|step| {
                (
                    step.caller.local_def_index.as_u32(),
                    step.callee.local_def_index.as_u32(),
                    step.location.block.as_u32(),
                    step.location.statement_index,
                )
            })
            .collect(),
    )
}

impl RetirementScope {
    pub(crate) fn finish(mut self) -> RetirementReview {
        let mut context = CURRENT
            .with(|current| current.replace(self.previous.take()))
            .expect("active retirement scope");
        self.active = false;
        let mut review = RetirementReview::default();
        if !context.entry_consistent {
            review.unresolved.push(RetirementUnresolved {
                source: None,
                function: None,
                location: None,
                phase: None,
                route: Vec::new(),
                reason: UnresolvedReason::DifferentEntryFacts,
            });
        }
        for problem in &context.routed.problems {
            review.unresolved.push(RetirementUnresolved {
                source: problem.source.as_ref().map(|row| row.key.clone()),
                function: None,
                location: None,
                phase: None,
                route: Vec::new(),
                reason: UnresolvedReason::Route(problem.clone()),
            });
        }
        let expected: BTreeSet<_> = context
            .routed
            .frames
            .values()
            .flatten()
            .map(|event| {
                context_key(
                    &event.source.key,
                    event.frame,
                    event.location,
                    event.phase,
                    &event.route,
                )
            })
            .collect();
        let mut seen = BTreeSet::new();
        let mut sources = BTreeSet::new();
        for function in &context.functions {
            let Some(mut latest) = context.latest.remove(function) else { continue };
            for row in &latest.coverage {
                let key = context_key(
                    &row.source,
                    row.function,
                    row.location,
                    row.phase,
                    &row.route,
                );
                let reason = if !expected.contains(&key) {
                    Some(UnresolvedReason::UnexpectedContext)
                } else if !seen.insert(key) {
                    Some(UnresolvedReason::DuplicateContext)
                } else {
                    None
                };
                if let Some(reason) = reason {
                    review.unresolved.push(RetirementUnresolved {
                        source: Some(row.source.clone()),
                        function: Some(row.function),
                        location: Some(row.location),
                        phase: Some(row.phase),
                        route: row.route.clone(),
                        reason,
                    });
                }
                sources.insert(row.source.clone());
            }
            review.ordinary_error_points += latest.ordinary_error_points;
            review.conflicts.append(&mut latest.conflicts);
            review.demotions.append(&mut latest.demotions);
            review.unresolved.append(&mut latest.unresolved);
            review.coverage.append(&mut latest.coverage);
        }
        for &function in context.latest.keys() {
            review.unresolved.push(RetirementUnresolved {
                source: None,
                function: Some(function),
                location: None,
                phase: None,
                route: Vec::new(),
                reason: UnresolvedReason::UnexpectedContext,
            });
        }
        for event in context.routed.frames.values().flatten() {
            if !seen.contains(&context_key(
                &event.source.key,
                event.frame,
                event.location,
                event.phase,
                &event.route,
            )) {
                review
                    .unresolved
                    .push(residual(event, UnresolvedReason::MissingContext));
            }
        }
        for source in context.source.retirements.keys() {
            if !sources.contains(source) {
                review.unresolved.push(RetirementUnresolved {
                    source: Some(source.clone()),
                    function: None,
                    location: None,
                    phase: None,
                    route: Vec::new(),
                    reason: UnresolvedReason::MissingSourceEvent,
                });
            }
        }
        for source in context.source.retirements.keys() {
            let disposition =
                if review
                    .unresolved
                    .iter()
                    .any(|row| row.source.as_ref().is_none_or(|key| key == source))
                {
                    EventDisposition::Unresolved
                } else if review.conflicts.iter().any(|row| &row.source == source)
                    || review.demotions.iter().any(|row| &row.source == source)
                {
                    EventDisposition::Conflict
                } else if review.coverage.iter().any(|row| {
                    &row.source == source && row.disposition == CoverageDisposition::Checked
                }) {
                    EventDisposition::CheckedWithoutConflict
                } else {
                    EventDisposition::Irrelevant
                };
            review.terminal.insert(source.clone(), disposition);
        }
        review
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use rustc_hash::FxHashMap;
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::mir::Local;

    use crate::{
        analyses::borrow_ownership::{
            SlotKind, borrow_verify, crate_slots::CrateSlots, export, slots::SlotId,
            solver::SlotRef, source_events,
        },
        utils::rustc::RustProgram,
    };

    /// Build an explicit candidate; no ownership solver is constructed. All
    /// nonselected slots, including wrapper parameters and aliases, stay Raw.
    pub(super) fn accepts(code: &str, selected: &[(&str, u32, u8)]) -> bool {
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
            let program = RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = CrateSlots::build(&program);
            let mut model = FxHashMap::default();
            for index in 0..slots.field_slots.len() {
                model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Raw);
            }
            for (&function, universe) in &slots.fn_local_slots {
                for index in 0..universe.len() {
                    model.insert(
                        SlotRef::Local(function, SlotId::from_usize(index)),
                        SlotKind::Raw,
                    );
                }
            }
            assert_eq!(
                model.len(),
                slots.field_slots.len()
                    + slots
                        .fn_local_slots
                        .values()
                        .map(|universe| universe.len())
                        .sum::<usize>()
            );
            for &(name, parameter, depth) in selected {
                let functions: Vec<_> = program
                    .functions
                    .iter()
                    .copied()
                    .filter(|function| tcx.item_name(function.to_def_id()).as_str() == name)
                    .collect();
                assert_eq!(functions.len(), 1, "exact selected function {name}");
                let function = functions[0];
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                assert!(
                    parameter > 0 && parameter as usize <= body.arg_count,
                    "selection must name an actual source parameter"
                );
                let slot = slots.fn_local_slots[&function]
                    .slot_for_local_depth(Local::from_u32(parameter), depth)
                    .expect("registered parameter depth");
                assert_eq!(
                    model.insert(SlotRef::Local(function, slot), SlotKind::Ref),
                    Some(SlotKind::Raw),
                    "selection must replace exactly one registered Raw slot"
                );
            }
            assert_eq!(
                model
                    .values()
                    .filter(|kind| **kind == SlotKind::Ref)
                    .count(),
                selected.len()
            );
            let inventory = Arc::new(source_events::collect(&program));
            assert!(!export::capturing(), "model_accepts is an unarmed probe");
            source_events::with_inventory(&inventory, || {
                borrow_verify::model_accepts(&program, &slots, &model, false)
            })
        })
        .unwrap_or_else(|error| error.raise())
    }

    #[test]
    fn e5_p_imm_direct_copied_void_alias_retirement_rejects_shared_entry() {
        const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
pub unsafe fn direct(p: *const u8) -> u8 {
    let value = *p;
    let alias = p as *mut u8;
    let copied = alias;
    free(copied as *mut core::ffi::c_void);
    value
}
"#;
        assert!(
            !accepts(CODE, &[("direct", 1, 0)]),
            "the shared incoming reference remains protected after its last read and through whole-object free"
        );
    }

    #[test]
    fn e5_p_imm_two_hop_raw_wrappers_route_retirement_to_shared_caller_entry() {
        const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
unsafe fn release_once(raw: *mut u8) {
    free(raw as *mut core::ffi::c_void);
}
unsafe fn release_twice(raw: *mut u8) {
    release_once(raw);
}
pub unsafe fn caller(p: *const u8) -> u8 {
    let value = *p;
    release_twice(p as *mut u8);
    value
}
"#;
        assert!(
            !accepts(CODE, &[("caller", 1, 0)]),
            "Raw wrapper parameters cannot hide the caller's live incoming reference from the body free"
        );
    }

    #[test]
    fn e5_p_object_interior_base_overlap_rejects_but_fresh_allocation_is_disjoint() {
        const DISJOINT: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn unrelated(entry: *const u8) -> u8 {
    let value = *entry;
    let fresh = malloc(8);
    free(fresh);
    value
}
"#;
        const INTERIOR: &str = r#"
#[repr(C)]
pub struct Pair { first: u8, second: u8 }
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
pub unsafe fn interior(view: *const u8, base: *mut Pair) -> u8 {
    let value = *view;
    free(base as *mut core::ffi::c_void);
    value
}
pub unsafe fn call_interior(base: *mut Pair) -> u8 {
    let view = &raw const (*base).second;
    interior(view, base)
}
"#;
        let disjoint_accepted = accepts(DISJOINT, &[("unrelated", 1, 0)]);
        let interior_accepted = accepts(INTERIOR, &[("interior", 1, 0)]);
        assert!(
            disjoint_accepted,
            "freeing a fresh allocation cannot invalidate the unrelated live incoming object"
        );
        assert!(
            !interior_accepted,
            "distinct parameter names and a c_void free do not prove an interior view disjoint from its allocation"
        );
    }

    #[test]
    fn e5_p_ordinary_shared_reads_and_nonretiring_local_free_remain_accepted() {
        const READS: &str = r#"
pub unsafe fn reads(p: *const u8, q: *const u8) -> u16 {
    (*p as u16) + (*q as u16)
}
"#;
        const LOCAL_NAME: &str = r#"
unsafe fn free(raw: *mut core::ffi::c_void) { let _ = raw; }
pub unsafe fn same_name(p: *const u8) -> u8 {
    let value = *p;
    free(p as *mut core::ffi::c_void);
    value
}
"#;
        assert!(
            accepts(READS, &[("reads", 1, 0), ("reads", 2, 0)]),
            "ordinary shared/shared reads remain compatible"
        );
        assert!(
            accepts(LOCAL_NAME, &[("same_name", 1, 0)]),
            "a nonretiring local body named free is not the ForeignC retirement primitive"
        );
    }
}

#[cfg(test)]
mod tests_rounds;

#[cfg(test)]
mod tests_edges;

#[cfg(test)]
mod tests_recursion;

#[cfg(test)]
mod tests_routes_edges;

#[cfg(test)]
mod tests_routes_inherent;

#[cfg(test)]
mod tests_call_reach;

#[cfg(test)]
mod tests_loans;

#[cfg(test)]
mod tests_coverage;

#[cfg(test)]
mod tests_indirect;

#[cfg(test)]
mod tests_consumer_receipts;

#[cfg(test)]
mod tests_analysis_receipts;

#[cfg(test)]
mod tests_call_targets;

#[cfg(test)]
mod tests_library_drop;

#[cfg(test)]
mod tests_owner_guards;
