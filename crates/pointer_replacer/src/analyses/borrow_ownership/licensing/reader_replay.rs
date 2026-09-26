//! Normative reader replay expectations, independent of optional export.

use std::{cell::RefCell, rc::Rc};

use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;
use serde::{Deserialize, Serialize};

use super::{
    super::{
        coherence::SelectedCopyLendLoan,
        crate_slots::CrateSlots,
        export::{BorrowerKind, OwnerKey, PlaceKey, ProjKey},
        l2::MirLocationKey,
        ownership_occurrence::Availability,
        slots::SlotOwner,
        solver::SlotRef,
    },
    facts::Facts,
    readers::Candidate,
    ref_effects,
};

#[derive(Clone, Debug)]
pub(crate) enum Root {
    Parameter(Candidate),
    OwnedCell(ref_effects::Candidate),
}

#[derive(Clone, Debug)]
pub(crate) struct Expected {
    pub(crate) identity: SelectedCopyLendLoan,
    pub(crate) field: crate::analyses::borrow::StructFieldSlot,
    pub(crate) root: Root,
    pub(crate) target: SlotRef,
    pub(crate) field_target: SlotRef,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Receipt {
    pub(crate) candidate: Option<Candidate>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) owned_cell: Option<ref_effects::Candidate>,
    pub(crate) matched_loans: usize,
    pub(crate) origin_linked: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FailureReason {
    MissingFrozenFacts,
    MissingTarget,
    InvalidTarget,
    MissingField,
    InvalidField,
    DuplicateExpected,
    MatchCount,
    OriginUnlinked,
    InvalidOwnedCell,
    TraversalLoan,
}

#[derive(Clone, Debug)]
pub(crate) struct Failure {
    pub(crate) candidate: Option<Candidate>,
    /// Matching failures always carry the reader target. A missing target or
    /// frozen construction cannot manufacture a SlotRef for repair.
    pub(crate) target: Option<SlotRef>,
    pub(crate) field_target: Option<SlotRef>,
    pub(crate) reason: FailureReason,
}

#[derive(Default)]
pub(crate) struct RoundResult {
    pub(crate) receipts: Vec<Receipt>,
    pub(crate) failures: Vec<Failure>,
    pub(crate) traversal_receipts: Vec<super::traversal_replay::Receipt>,
}

struct Observed {
    function: LocalDefId,
    expected: Expected,
    matched_loans: usize,
    origin_linked: bool,
}

#[derive(Default)]
struct Round {
    rows: Vec<Observed>,
    failures: Vec<Failure>,
}

thread_local! {
    static FACTS: RefCell<Option<Rc<Facts>>> = const { RefCell::new(None) };
    static ROUND: RefCell<Option<Round>> = const { RefCell::new(None) };
}

pub(crate) struct FactsScope(Option<Rc<Facts>>);

impl Drop for FactsScope {
    fn drop(&mut self) {
        FACTS.with(|facts| *facts.borrow_mut() = self.0.take());
    }
}

pub(crate) fn enter_facts(facts: Option<Rc<Facts>>) -> FactsScope {
    FactsScope(FACTS.with(|current| current.replace(facts)))
}

pub(crate) fn selected_owned_cells() -> Option<(Rc<Facts>, Vec<ref_effects::Candidate>)> {
    let facts = FACTS.with(|facts| facts.borrow().clone())?;
    let selected = ROUND.with(|round| {
        round.borrow().as_ref().map(|round| {
            round
                .rows
                .iter()
                .filter_map(|row| match &row.expected.root {
                    Root::OwnedCell(effect) => Some(effect.clone()),
                    Root::Parameter(_) => None,
                })
                .collect()
        })
    })?;
    Some((facts, selected))
}

pub(crate) struct RoundScope {
    previous: Option<Round>,
    active: bool,
    traversal: Option<super::traversal_replay::Scope>,
}

impl Drop for RoundScope {
    fn drop(&mut self) {
        if self.active {
            ROUND.with(|round| *round.borrow_mut() = self.previous.take());
        }
    }
}

impl RoundScope {
    pub(crate) fn finish(mut self) -> RoundResult {
        let round = ROUND
            .with(|round| round.replace(self.previous.take()))
            .expect("active reader replay round");
        self.active = false;
        let mut result = RoundResult {
            receipts: Vec::new(),
            failures: round.failures,
            traversal_receipts: Vec::new(),
        };
        let (receipts, failures) = self
            .traversal
            .take()
            .expect("traversal replay scope")
            .finish();
        result.traversal_receipts = receipts;
        result
            .failures
            .extend(failures.into_iter().map(|target| Failure {
                candidate: None,
                target,
                field_target: None,
                reason: FailureReason::TraversalLoan,
            }));
        for row in round.rows {
            let (candidate, owned_cell) = match row.expected.root {
                Root::Parameter(candidate) => (Some(candidate), None),
                Root::OwnedCell(candidate) => (None, Some(candidate)),
            };
            let reason = if row.matched_loans != 1 {
                Some(FailureReason::MatchCount)
            } else if !row.origin_linked {
                Some(FailureReason::OriginUnlinked)
            } else {
                None
            };
            if let Some(reason) = reason {
                result.failures.push(Failure {
                    candidate: candidate.clone(),
                    target: Some(row.expected.target),
                    field_target: Some(row.expected.field_target),
                    reason,
                });
            }
            result.receipts.push(Receipt {
                candidate,
                owned_cell,
                matched_loans: row.matched_loans,
                origin_linked: row.origin_linked,
            });
        }
        result
    }
}

pub(crate) fn begin_round(
    slots: &CrateSlots,
    is_ref: &impl Fn(SlotRef) -> bool,
    is_raw: &impl Fn(SlotRef) -> bool,
) -> RoundScope {
    let facts = FACTS.with(|facts| facts.borrow().clone());
    let traversal = super::traversal_replay::begin(facts.clone(), slots, is_ref);
    let mut round = Round::default();
    if let Some(facts) = facts {
        if let Some(frozen) = &facts.licensing {
            for proof in &frozen.reader_transfers {
                if !matches!(proof.coverage, Availability::Present(_)) {
                    continue;
                }
                let candidate = &proof.candidate;
                let key = format!(
                    "{}::_{}@d0",
                    candidate.function, candidate.destination.local
                );
                let target = facts.slot_refs.get(&key).copied();
                let field_target = facts.slot_refs.get(&candidate.field_key).copied();
                let failure = |reason| Failure {
                    candidate: Some(candidate.clone()),
                    target,
                    field_target,
                    reason,
                };
                let Some(target) = target else {
                    round.failures.push(failure(FailureReason::MissingTarget));
                    continue;
                };
                let SlotRef::Local(function, local_id) = target else {
                    round.failures.push(failure(FailureReason::InvalidTarget));
                    continue;
                };
                let valid_local = slots.fn_local_slots.get(&function).is_some_and(|universe| {
                    local_id.as_usize() < universe.len()
                        && universe.slot(local_id).depth == 0
                        && universe.slot(local_id).owner
                            == SlotOwner::Local(Local::from_u32(candidate.destination.local))
                });
                if !valid_local || !candidate.destination.projection.is_empty() {
                    round.failures.push(failure(FailureReason::InvalidTarget));
                    continue;
                }
                if !is_ref(target) {
                    continue;
                }
                let Some(field_ref) = field_target else {
                    round.failures.push(failure(FailureReason::MissingField));
                    continue;
                };
                let SlotRef::Field(field_id) = field_ref else {
                    round.failures.push(failure(FailureReason::InvalidField));
                    continue;
                };
                if field_id.as_usize() >= slots.field_slots.len() {
                    round.failures.push(failure(FailureReason::InvalidField));
                    continue;
                }
                let field_slot = slots.field_slots.slot(field_id);
                let SlotOwner::Field(field) = field_slot.owner else {
                    round.failures.push(failure(FailureReason::InvalidField));
                    continue;
                };
                if field_slot.depth != 0 || slots.field_slots.is_array_slot(field_id) {
                    round.failures.push(failure(FailureReason::InvalidField));
                    continue;
                }
                if is_ref(field_ref) || is_raw(field_ref) {
                    continue;
                }
                let mut projection = candidate.source.projection.clone();
                projection.push(ProjKey::Deref);
                let identity = SelectedCopyLendLoan {
                    location: MirLocationKey::new(candidate.block, candidate.statement),
                    borrowed: PlaceKey {
                        local: Local::from_u32(candidate.source.local),
                        proj: projection,
                    },
                    borrower: BorrowerKind::Assign {
                        owner: OwnerKey::Local(candidate.destination.local),
                    },
                };
                if round
                    .rows
                    .iter()
                    .any(|row| row.function == function && row.expected.identity == identity)
                {
                    round
                        .failures
                        .push(failure(FailureReason::DuplicateExpected));
                    continue;
                }
                round.rows.push(Observed {
                    function,
                    expected: Expected {
                        identity,
                        field: crate::analyses::borrow::StructFieldSlot {
                            struct_did: field.struct_did,
                            field_index: field.field_index,
                        },
                        root: Root::Parameter(candidate.clone()),
                        target,
                        field_target: field_ref,
                    },
                    matched_loans: 0,
                    origin_linked: false,
                });
            }
            let checked_effects = ref_effects::Plan::build(&facts);
            for effect in &frozen.reference_effects.candidates {
                let views: Vec<_> = facts
                    .consumes
                    .iter()
                    .filter(|row| {
                        row.point.construction == effect.construction
                            && row.ordinal == effect.scalar_view_consume
                            && row.point.function.as_ref() == Some(&effect.function)
                    })
                    .collect();
                let target = views
                    .first()
                    .and_then(|view| {
                        facts
                            .slot_refs
                            .get(&format!("{}::_{}@d0", effect.function, view.local))
                    })
                    .copied();
                let field_target = facts.slot_refs.get(&effect.field_key).copied();
                let failure = |reason| Failure {
                    candidate: None,
                    target,
                    field_target,
                    reason,
                };
                let Some(target @ SlotRef::Local(function, local_id)) = target else {
                    round.failures.push(failure(FailureReason::MissingTarget));
                    continue;
                };
                if !is_ref(target) {
                    continue;
                }
                let Some(field_ref @ SlotRef::Field(field_id)) = field_target else {
                    round.failures.push(failure(FailureReason::MissingField));
                    continue;
                };
                if is_ref(field_ref) || is_raw(field_ref) {
                    continue;
                }
                if views.len() != 1 || !checked_effects.candidates.contains(effect) {
                    round
                        .failures
                        .push(failure(FailureReason::InvalidOwnedCell));
                    continue;
                }
                let view = views[0];
                let valid_local = slots.fn_local_slots.get(&function).is_some_and(|universe| {
                    local_id.as_usize() < universe.len()
                        && universe.slot(local_id).depth == 0
                        && universe.slot(local_id).owner
                            == SlotOwner::Local(Local::from_u32(view.local))
                });
                if !valid_local || !view.projection.is_empty() || view.point != effect.scalar_read {
                    round.failures.push(failure(FailureReason::InvalidTarget));
                    continue;
                }
                if field_id.as_usize() >= slots.field_slots.len() {
                    round.failures.push(failure(FailureReason::InvalidField));
                    continue;
                }
                let field_slot = slots.field_slots.slot(field_id);
                let SlotOwner::Field(field) = field_slot.owner else {
                    round.failures.push(failure(FailureReason::InvalidField));
                    continue;
                };
                if field_slot.depth != 0 || slots.field_slots.is_array_slot(field_id) {
                    round.failures.push(failure(FailureReason::InvalidField));
                    continue;
                }
                let cells: Vec<_> = facts
                    .consumes
                    .iter()
                    .filter(|row| {
                        row.point == effect.scalar_read
                            && row.ordinal == effect.scalar_consume
                            && row.local == effect.cell_place.local
                    })
                    .collect();
                let [cell] = cells.as_slice() else {
                    round
                        .failures
                        .push(failure(FailureReason::InvalidOwnedCell));
                    continue;
                };
                let (Some(block), Some(statement)) =
                    (effect.scalar_read.block, effect.scalar_read.statement)
                else {
                    round
                        .failures
                        .push(failure(FailureReason::InvalidOwnedCell));
                    continue;
                };
                let mut projection = cell.projection.clone();
                projection.push(ProjKey::Deref);
                let identity = SelectedCopyLendLoan {
                    location: MirLocationKey::new(block, statement),
                    borrowed: PlaceKey {
                        local: Local::from_u32(cell.local),
                        proj: projection,
                    },
                    borrower: BorrowerKind::Assign {
                        owner: OwnerKey::Local(view.local),
                    },
                };
                if round
                    .rows
                    .iter()
                    .any(|row| row.function == function && row.expected.identity == identity)
                {
                    round
                        .failures
                        .push(failure(FailureReason::DuplicateExpected));
                    continue;
                }
                round.rows.push(Observed {
                    function,
                    expected: Expected {
                        identity,
                        field: crate::analyses::borrow::StructFieldSlot {
                            struct_did: field.struct_did,
                            field_index: field.field_index,
                        },
                        root: Root::OwnedCell(effect.clone()),
                        target,
                        field_target: field_ref,
                    },
                    matched_loans: 0,
                    origin_linked: false,
                });
            }
        } else {
            round.failures.push(Failure {
                candidate: None,
                target: None,
                field_target: None,
                reason: FailureReason::MissingFrozenFacts,
            });
        }
    }
    RoundScope {
        previous: ROUND.with(|current| current.replace(Some(round))),
        active: true,
        traversal: Some(traversal),
    }
}

pub(crate) fn expected(function: LocalDefId) -> Vec<Expected> {
    ROUND.with(|round| {
        round
            .borrow()
            .as_ref()
            .map(|round| {
                round
                    .rows
                    .iter()
                    .filter(|row| row.function == function)
                    .map(|row| row.expected.clone())
                    .collect()
            })
            .unwrap_or_default()
    })
}

/// An inner inference may restart. Only its latest complete pass is evidence.
pub(crate) fn begin_function(function: LocalDefId) {
    ROUND.with(|round| {
        if let Some(round) = round.borrow_mut().as_mut() {
            for row in round.rows.iter_mut().filter(|row| row.function == function) {
                row.matched_loans = 0;
                row.origin_linked = false;
            }
        }
    });
}

pub(crate) fn record_match(
    function: LocalDefId,
    identity: &SelectedCopyLendLoan,
    origin_linked: bool,
) {
    ROUND.with(|round| {
        if let Some(round) = round.borrow_mut().as_mut() {
            for row in round
                .rows
                .iter_mut()
                .filter(|row| row.function == function && &row.expected.identity == identity)
            {
                row.origin_linked = if row.matched_loans == 0 {
                    origin_linked
                } else {
                    row.origin_linked && origin_linked
                };
                row.matched_loans += 1;
            }
        }
    });
}
