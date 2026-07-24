//! L2 context-conditioned single-literal commit planning.
//!
//! This module is an inert RED-phase contract. Nothing in the production
//! borrow-verification or solver paths calls it yet. The tests below pin the
//! approved guard, lifecycle, termination, and deterministic-diagnostic
//! behavior before that wiring is implemented.

use rustc_hash::FxHashMap;

use super::{SlotKind, solver::SlotRef};

pub(crate) const GUARDED_COMMIT_CORE_FAMILY: &str = "l2-guarded-commit";
pub(crate) const RECURRENCE_ESCALATION_CORE_FAMILY: &str = "l2-recurrence-escalation";

/// Stable owning-function identity (`LocalDefId::local_def_index`) captured by
/// the read-only conflict adapter.
pub(crate) type FnKey = u32;

/// Feature switch resolved once by the future `verify_to_fixpoint_counting`
/// integration. There is intentionally no production caller in the RED phase.
pub(crate) fn enabled_from_env() -> bool {
    match std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref() {
        Err(std::env::VarError::NotPresent) | Ok("0") => false,
        Ok("1") => true,
        Ok(other) => panic!("CRAT_BO_L2_GUARDED_COMMITS must be 0 or 1, got {other:?}"),
        Err(error) => panic!("CRAT_BO_L2_GUARDED_COMMITS is not valid Unicode: {error}"),
    }
}

/// A residual borrow-conflict edge translated wholly into BO slots.
///
/// `target` is the unchanged Mode-A A′ representative. `issuer` and
/// `requirers` retain the complete edge attribution; the planner derives the
/// guard from the participants that are `Ref` in `model`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ConflictObservation {
    pub(crate) fn_key: FnKey,
    pub(crate) target: SlotRef,
    pub(crate) issuer: Option<SlotRef>,
    pub(crate) requirers: Vec<SlotRef>,
}

impl ConflictObservation {
    pub(crate) fn new(
        fn_key: FnKey,
        target: SlotRef,
        issuer: Option<SlotRef>,
        requirers: Vec<SlotRef>,
    ) -> Self {
        Self {
            fn_key,
            target,
            issuer,
            requirers,
        }
    }
}

/// Stable total-order form of `SlotRef`, suitable for action ordering and
/// machine-parseable diagnostic keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct SlotKey {
    pub(crate) variant: u8,
    pub(crate) owner: u32,
    pub(crate) slot: usize,
}

impl SlotKey {
    pub(crate) fn of(slot: SlotRef) -> Self {
        match slot {
            SlotRef::Field(slot) => Self {
                variant: 0,
                owner: 0,
                slot: slot.index(),
            },
            SlotRef::Local(did, slot) => Self {
                variant: 1,
                owner: did.local_def_index.as_u32(),
                slot: slot.index(),
            },
        }
    }

    fn diagnostic(self) -> String {
        match self.variant {
            0 => format!("field:{}", self.slot),
            1 => format!("local:{}:{}", self.owner, self.slot),
            variant => panic!("invalid canonical SlotRef variant {variant}"),
        }
    }
}

/// Canonical identity of the conflict edge that spawned a commit.
///
/// The function key is required even for field-only fixtures: the same field
/// edge observed while validating two functions is not the same attribution.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct EdgeKey {
    pub(crate) fn_key: FnKey,
    pub(crate) issuer: Option<SlotKey>,
    pub(crate) requirers: Vec<SlotKey>,
}

/// Canonical R7 diagnostic identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct DiagnosticKey {
    pub(crate) target: SlotKey,
    pub(crate) peers: Vec<SlotKey>,
    pub(crate) edge: EdgeKey,
}

/// A forbid-only L2 clause.
///
/// Every member denotes a negative `¬ref(slot)` literal. The target is stored
/// last, after the canonical peer literals, so this representation cannot
/// express a positive safety claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForbidClause {
    pub(crate) forbidden_refs: Vec<SlotRef>,
}

impl ForbidClause {
    pub(crate) fn is_satisfied_by(&self, model: &FxHashMap<SlotRef, SlotKind>) -> bool {
        self.forbidden_refs.iter().any(|slot| {
            *model
                .get(slot)
                .unwrap_or_else(|| panic!("forbid-clause model is missing {slot:?}"))
                != SlotKind::Ref
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Lifecycle {
    Unseen,
    Guarded,
    Permanent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CommitActionKind {
    GuardedCommit,
    UnconditionalCommit,
    RecurrenceEscalation,
}

impl CommitActionKind {
    fn diagnostic(self) -> &'static str {
        match self {
            Self::GuardedCommit => "guarded",
            Self::UnconditionalCommit => "unconditional",
            Self::RecurrenceEscalation => "escalation",
        }
    }
}

/// One solver assertion planned after an entire validation round has been
/// collected and canonicalized.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CommitAction {
    pub(crate) target: SlotRef,
    /// Canonical edge-local peer set. For escalation this records the
    /// reappearing context for R7 even though the emitted assertion is
    /// unconditional.
    pub(crate) peers: Vec<SlotRef>,
    pub(crate) clause: ForbidClause,
    pub(crate) edge: EdgeKey,
    pub(crate) kind: CommitActionKind,
    pub(crate) core_family: &'static str,
    pub(crate) diagnostic_key: DiagnosticKey,
    pub(crate) diagnostic_label: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SolverOutcome {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SolverDecline {
    Unsat,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DeclineReason {
    Solver(SolverDecline),
    ValidationCap { cap: usize, attempted_round: usize },
    ParticipantNotRef { slot: SlotRef },
    PermanentRetarget { target: SlotRef },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RoundPlan {
    Accept {
        validation_round: usize,
    },
    Continue {
        validation_round: usize,
        actions: Vec<CommitAction>,
    },
    Decline {
        validation_round: usize,
        reason: DeclineReason,
    },
}

/// Per-fixpoint-invocation L2 state. Its future implementation must advance
/// every selected slot monotonically through `Unseen → Guarded → Permanent`.
pub(crate) struct Planner {
    slot_count: usize,
    validation_rounds: usize,
    lifecycle: FxHashMap<SlotRef, Lifecycle>,
}

impl Planner {
    pub(crate) fn new(slot_count: usize) -> Self {
        Self {
            slot_count,
            validation_rounds: 0,
            lifecycle: FxHashMap::default(),
        }
    }

    pub(crate) fn validation_cap(&self) -> usize {
        self.slot_count
            .checked_mul(2)
            .and_then(|rank_bound| rank_bound.checked_add(1))
            .expect("L2 validation-round cap overflow")
    }

    pub(crate) fn validation_rounds(&self) -> usize {
        self.validation_rounds
    }

    pub(crate) fn lifecycle(&self, slot: SlotRef) -> Lifecycle {
        self.lifecycle
            .get(&slot)
            .copied()
            .unwrap_or(Lifecycle::Unseen)
    }

    /// Plan one post-solve validation round.
    ///
    /// RED-phase contract only: GREEN fills this body without changing the test
    /// assertions below, then the integration phase may call it from Mode-A's
    /// feature-on branch.
    pub(crate) fn plan_round(
        &mut self,
        _solver_outcome: SolverOutcome,
        _observations: &[ConflictObservation],
        _model: &FxHashMap<SlotRef, SlotKind>,
    ) -> RoundPlan {
        unimplemented!("L2 RED contract: round planning is not implemented")
    }
}

#[cfg(test)]
mod tests {
    use rustc_span::def_id::{DefIndex, LocalDefId};

    use super::*;
    use crate::analyses::borrow_ownership::slots::SlotId;

    fn field(index: usize) -> SlotRef {
        SlotRef::Field(SlotId::from_usize(index))
    }

    fn local(owner: u32, index: usize) -> SlotRef {
        SlotRef::Local(
            LocalDefId {
                local_def_index: DefIndex::from_u32(owner),
            },
            SlotId::from_usize(index),
        )
    }

    fn ref_model(slots: &[SlotRef]) -> FxHashMap<SlotRef, SlotKind> {
        slots
            .iter()
            .copied()
            .map(|slot| (slot, SlotKind::Ref))
            .collect()
    }

    fn continue_actions(plan: RoundPlan) -> Vec<CommitAction> {
        match plan {
            RoundPlan::Continue { actions, .. } => actions,
            other => panic!("expected L2 to continue with commits, got {other:?}"),
        }
    }

    fn assert_accept(plan: RoundPlan) {
        assert!(
            matches!(plan, RoundPlan::Accept { .. }),
            "expected a conflict-free validation round to accept, got {plan:?}"
        );
    }

    #[test]
    fn l2_red_guard_uses_exact_edge_peers_and_empty_guard_is_unconditional() {
        let (target, outside, peer_a, peer_b, peer_c) =
            (field(1), field(99), field(4), field(3), field(2));
        let model = ref_model(&[target, outside, peer_a, peer_b, peer_c]);
        let observation = ConflictObservation::new(
            17,
            target,
            Some(peer_a),
            vec![target, peer_b, peer_a, target, peer_c, peer_b],
        );
        let mut planner = Planner::new(100);

        let actions =
            continue_actions(planner.plan_round(SolverOutcome::Sat, &[observation], &model));
        assert_eq!(actions.len(), 1);
        assert_eq!(actions[0].target, target);
        assert_eq!(
            actions[0].peers,
            vec![peer_c, peer_b, peer_a],
            "guard is exactly the sorted, duplicate-free edge participants minus target"
        );
        assert!(
            !actions[0].peers.contains(&outside),
            "model facts outside the spawning edge must never enter the guard"
        );
        assert_eq!(actions[0].kind, CommitActionKind::GuardedCommit);
        assert_eq!(actions[0].core_family, GUARDED_COMMIT_CORE_FAMILY);
        assert_eq!(
            actions[0].clause.forbidden_refs,
            vec![peer_c, peer_b, peer_a, target],
            "the clause is exactly ¬peer_c ∨ ¬peer_b ∨ ¬peer_a ∨ ¬target"
        );
        let all_raw = actions[0]
            .clause
            .forbidden_refs
            .iter()
            .copied()
            .map(|slot| (slot, SlotKind::Raw))
            .collect();
        assert!(
            actions[0].clause.is_satisfied_by(&all_raw),
            "the all-Raw assignment must satisfy every forbid-only L2 clause"
        );
        assert_eq!(planner.lifecycle(target), Lifecycle::Guarded);

        let (issuerless_target, issuerless_a, issuerless_b) = (field(7), field(8), field(9));
        let mut issuerless_planner = Planner::new(100);
        let issuerless_actions = continue_actions(issuerless_planner.plan_round(
            SolverOutcome::Sat,
            &[ConflictObservation::new(
                18,
                issuerless_target,
                None,
                vec![
                    issuerless_b,
                    issuerless_target,
                    issuerless_a,
                    issuerless_b,
                ],
            )],
            &ref_model(&[issuerless_target, issuerless_a, issuerless_b]),
        ));
        assert_eq!(issuerless_actions.len(), 1);
        assert_eq!(
            issuerless_actions[0].peers,
            vec![issuerless_a, issuerless_b],
            "an issuer-less edge derives its guard exactly from its other requirers"
        );
        assert_eq!(
            issuerless_actions[0].clause.forbidden_refs,
            vec![issuerless_a, issuerless_b, issuerless_target]
        );
        assert_eq!(
            issuerless_actions[0].edge,
            EdgeKey {
                fn_key: 18,
                issuer: None,
                requirers: vec![
                    SlotKey::of(issuerless_target),
                    SlotKey::of(issuerless_a),
                    SlotKey::of(issuerless_b),
                ],
            },
            "issuer absence remains explicit in the canonical edge attribution"
        );

        let lone_target = field(6);
        let mut empty_guard_planner = Planner::new(100);
        let actions = continue_actions(empty_guard_planner.plan_round(
            SolverOutcome::Sat,
            &[ConflictObservation::new(
                17,
                lone_target,
                None,
                vec![lone_target, lone_target],
            )],
            &ref_model(&[lone_target]),
        ));
        assert_eq!(actions.len(), 1);
        assert!(actions[0].peers.is_empty());
        assert_eq!(actions[0].kind, CommitActionKind::UnconditionalCommit);
        assert_eq!(actions[0].core_family, GUARDED_COMMIT_CORE_FAMILY);
        assert_eq!(actions[0].clause.forbidden_refs, vec![lone_target]);
        assert_eq!(
            empty_guard_planner.lifecycle(lone_target),
            Lifecycle::Permanent
        );

        for non_ref_kind in [SlotKind::Raw, SlotKind::Owning] {
            let mut fail_closed = Planner::new(2);
            let non_ref_model = [(target, SlotKind::Ref), (peer_a, non_ref_kind)]
                .into_iter()
                .collect();
            assert_eq!(
                fail_closed.plan_round(
                    SolverOutcome::Sat,
                    &[ConflictObservation::new(
                        17,
                        target,
                        Some(peer_a),
                        vec![target],
                    )],
                    &non_ref_model,
                ),
                RoundPlan::Decline {
                    validation_round: 1,
                    reason: DeclineReason::ParticipantNotRef { slot: peer_a },
                },
                "a mapped non-Ref edge participant must fail closed"
            );
        }

        for non_ref_kind in [SlotKind::Raw, SlotKind::Owning] {
            let mut fail_closed = Planner::new(3);
            let non_ref_model = [
                (target, SlotKind::Ref),
                (peer_a, SlotKind::Ref),
                (peer_b, non_ref_kind),
            ]
            .into_iter()
            .collect();
            assert_eq!(
                fail_closed.plan_round(
                    SolverOutcome::Sat,
                    &[ConflictObservation::new(
                        17,
                        target,
                        Some(peer_a),
                        vec![target, peer_b],
                    )],
                    &non_ref_model,
                ),
                RoundPlan::Decline {
                    validation_round: 1,
                    reason: DeclineReason::ParticipantNotRef { slot: peer_b },
                },
                "a mapped non-Ref requirer must fail closed"
            );
        }

        let mut missing_participant = Planner::new(2);
        assert_eq!(
            missing_participant.plan_round(
                SolverOutcome::Sat,
                &[ConflictObservation::new(
                    17,
                    target,
                    Some(peer_a),
                    vec![target],
                )],
                &ref_model(&[target]),
            ),
            RoundPlan::Decline {
                validation_round: 1,
                reason: DeclineReason::ParticipantNotRef { slot: peer_a },
            },
            "a participant missing from the solved model must fail closed"
        );
    }

    #[test]
    fn l2_red_same_round_batches_one_epoch_and_later_retarget_escalates() {
        let (target, peer_a, peer_b, peer_c) = (field(10), field(11), field(12), field(13));
        let model = ref_model(&[target, peer_a, peer_b, peer_c]);
        let edge_a = ConflictObservation::new(4, target, Some(peer_a), vec![target]);
        let edge_a_same_clause = ConflictObservation::new(
            5,
            target,
            Some(peer_a),
            vec![peer_a, target, peer_a],
        );
        let edge_b = ConflictObservation::new(4, target, Some(peer_b), vec![target]);
        let observations = vec![
            edge_b.clone(),
            edge_a_same_clause,
            edge_a.clone(),
            edge_a.clone(),
        ];
        let mut planner = Planner::new(14);
        let mut reverse_planner = Planner::new(14);

        let first_actions =
            continue_actions(planner.plan_round(SolverOutcome::Sat, &observations, &model));
        let reverse_actions = continue_actions(reverse_planner.plan_round(
            SolverOutcome::Sat,
            &observations.iter().cloned().rev().collect::<Vec<_>>(),
            &model,
        ));
        assert_eq!(
            first_actions.len(),
            2,
            "distinct peer sets emit separate implications; duplicates are removed"
        );
        assert!(
            first_actions
                .iter()
                .all(|action| action.kind == CommitActionKind::GuardedCommit),
            "same-model conflicts share the first guarded epoch"
        );
        assert_eq!(
            first_actions, reverse_actions,
            "duplicate-clause attribution must not depend on input order"
        );
        assert_eq!(
            first_actions
                .iter()
                .find(|action| action.peers == vec![peer_a])
                .expect("peer-a guarded clause")
                .edge
                .fn_key,
            4,
            "deduplication retains the lexicographically smallest edge attribution"
        );
        assert_eq!(planner.lifecycle(target), Lifecycle::Guarded);

        let retargeted_model = [
            (target, SlotKind::Ref),
            (peer_a, SlotKind::Raw),
            (peer_b, SlotKind::Raw),
            (peer_c, SlotKind::Ref),
        ]
        .into_iter()
        .collect();
        let retargeted = ConflictObservation::new(6, target, Some(peer_c), vec![target]);
        let recurrence_actions = continue_actions(planner.plan_round(
            SolverOutcome::Sat,
            &[retargeted],
            &retargeted_model,
        ));
        assert_eq!(
            recurrence_actions.len(),
            1,
            "one slot-level recurrence emits one unconditional escalation"
        );
        assert_eq!(
            recurrence_actions[0].kind,
            CommitActionKind::RecurrenceEscalation
        );
        assert_eq!(
            recurrence_actions[0].core_family,
            RECURRENCE_ESCALATION_CORE_FAMILY
        );
        assert_eq!(planner.lifecycle(target), Lifecycle::Permanent);
    }

    #[test]
    fn l2_red_deactivation_accepts_only_when_hazard_disappears_otherwise_escalates() {
        let (target, issuer, replacement) = (field(20), field(21), field(22));
        let conflict = ConflictObservation::new(7, target, Some(issuer), vec![target]);
        let first_model = ref_model(&[target, issuer]);

        let mut discharged = Planner::new(23);
        let first = continue_actions(discharged.plan_round(
            SolverOutcome::Sat,
            std::slice::from_ref(&conflict),
            &first_model,
        ));
        assert_eq!(first[0].kind, CommitActionKind::GuardedCommit);
        let discharged_model = [(target, SlotKind::Ref), (issuer, SlotKind::Raw)]
            .into_iter()
            .collect();
        assert_accept(discharged.plan_round(SolverOutcome::Sat, &[], &discharged_model));
        assert_eq!(
            discharged.lifecycle(target),
            Lifecycle::Guarded,
            "acceptance validates the recovered Ref; it need not pin the slot"
        );

        let mut persistent = Planner::new(23);
        continue_actions(persistent.plan_round(
            SolverOutcome::Sat,
            std::slice::from_ref(&conflict),
            &first_model,
        ));
        let retargeted =
            ConflictObservation::new(8, target, Some(replacement), vec![target, replacement, target]);
        let recurrence_model = [
            (target, SlotKind::Ref),
            (issuer, SlotKind::Raw),
            (replacement, SlotKind::Ref),
        ]
        .into_iter()
        .collect();
        let recurrence = continue_actions(persistent.plan_round(
            SolverOutcome::Sat,
            std::slice::from_ref(&retargeted),
            &recurrence_model,
        ));
        assert_eq!(
            recurrence[0].kind,
            CommitActionKind::RecurrenceEscalation,
            "a false guard release is repaired by an unconditional target pin"
        );
        assert_eq!(persistent.lifecycle(target), Lifecycle::Permanent);
        assert_eq!(
            recurrence[0].diagnostic_key,
            DiagnosticKey {
                target: SlotKey::of(target),
                peers: vec![SlotKey::of(replacement)],
                edge: EdgeKey {
                    fn_key: 8,
                    issuer: Some(SlotKey::of(replacement)),
                    requirers: vec![SlotKey::of(target), SlotKey::of(replacement)],
                },
            },
            "an escalation records the canonical reappearing (target, peers, edge) key"
        );
        assert_eq!(
            recurrence[0].diagnostic_label,
            "event=l2_commit|kind=escalation|target=field:20|peers=field:22|edge_fn=8|edge_issuer=field:22|edge_requirers=field:20,field:22",
            "the escalation diagnostic is stable and machine-parseable"
        );
        let escalated_model = [
            (target, SlotKind::Raw),
            (issuer, SlotKind::Raw),
            (replacement, SlotKind::Ref),
        ]
            .into_iter()
            .collect();
        assert_accept(persistent.plan_round(SolverOutcome::Sat, &[], &escalated_model));
    }

    #[test]
    fn l2_red_two_s_plus_one_cap_and_solver_declines_are_fail_closed() {
        let (target, peer) = (field(30), field(31));
        let initial = ConflictObservation::new(30, target, Some(peer), vec![target]);
        let retargeted = ConflictObservation::new(31, target, Some(target), vec![target]);
        let first_model = ref_model(&[target, peer]);
        let retargeted_model = [(target, SlotKind::Ref), (peer, SlotKind::Raw)]
            .into_iter()
            .collect();
        let final_model = [(target, SlotKind::Raw), (peer, SlotKind::Raw)]
            .into_iter()
            .collect();

        let mut planner = Planner::new(2);
        assert_eq!(planner.validation_cap(), 5, "cap is exactly 2S + 1");
        continue_actions(planner.plan_round(
            SolverOutcome::Sat,
            std::slice::from_ref(&initial),
            &first_model,
        ));
        continue_actions(planner.plan_round(
            SolverOutcome::Sat,
            std::slice::from_ref(&retargeted),
            &retargeted_model,
        ));
        assert_eq!(planner.lifecycle(target), Lifecycle::Permanent);
        for expected_round in 3..=5 {
            assert_accept(planner.plan_round(SolverOutcome::Sat, &[], &final_model));
            assert_eq!(planner.validation_rounds(), expected_round);
        }
        assert_eq!(
            planner.plan_round(SolverOutcome::Sat, &[], &final_model),
            RoundPlan::Decline {
                validation_round: 6,
                reason: DeclineReason::ValidationCap {
                    cap: 5,
                    attempted_round: 6,
                },
            },
            "a positive-slot lifecycle must decline beyond exactly 2S + 1 validations"
        );

        let mut impossible_retarget = Planner::new(2);
        continue_actions(impossible_retarget.plan_round(
            SolverOutcome::Sat,
            std::slice::from_ref(&initial),
            &first_model,
        ));
        continue_actions(impossible_retarget.plan_round(
            SolverOutcome::Sat,
            std::slice::from_ref(&retargeted),
            &retargeted_model,
        ));
        assert_eq!(
            impossible_retarget.plan_round(
                SolverOutcome::Sat,
                std::slice::from_ref(&retargeted),
                &retargeted_model,
            ),
            RoundPlan::Decline {
                validation_round: 3,
                reason: DeclineReason::PermanentRetarget { target },
            },
            "observing a permanently pinned target is impossible and must fail closed"
        );

        let no_conflicts = FxHashMap::default();
        for (outcome, expected) in [
            (SolverOutcome::Unsat, SolverDecline::Unsat),
            (SolverOutcome::Unknown, SolverDecline::Unknown),
        ] {
            let mut solver_decline = Planner::new(1);
            assert_eq!(
                solver_decline.plan_round(outcome, &[], &no_conflicts),
                RoundPlan::Decline {
                    validation_round: 0,
                    reason: DeclineReason::Solver(expected),
                },
                "a non-model solver result fails closed without validation"
            );
        }
    }

    #[test]
    fn l2_red_permuted_conflicts_have_identical_canonical_actions_and_labels() {
        let observations = vec![
            ConflictObservation::new(9, field(8), Some(field(3)), vec![field(8), field(7)]),
            ConflictObservation::new(2, field(1), Some(field(5)), vec![field(1)]),
            ConflictObservation::new(1, field(1), Some(field(4)), vec![field(1)]),
        ];
        let model = ref_model(&[field(1), field(3), field(4), field(5), field(7), field(8)]);
        let mut forward = Planner::new(9);
        let mut reverse = Planner::new(9);

        let forward_actions =
            continue_actions(forward.plan_round(SolverOutcome::Sat, &observations, &model));
        let reverse_actions = continue_actions(reverse.plan_round(
            SolverOutcome::Sat,
            &observations.iter().cloned().rev().collect::<Vec<_>>(),
            &model,
        ));
        assert_eq!(
            forward_actions, reverse_actions,
            "input/hash insertion order must not affect canonical actions"
        );
        assert_eq!(
            forward_actions
                .iter()
                .map(|action| action.diagnostic_label.as_str())
                .collect::<Vec<_>>(),
            vec![
                "event=l2_commit|kind=guarded|target=field:1|peers=field:4|edge_fn=1|edge_issuer=field:4|edge_requirers=field:1",
                "event=l2_commit|kind=guarded|target=field:1|peers=field:5|edge_fn=2|edge_issuer=field:5|edge_requirers=field:1",
                "event=l2_commit|kind=guarded|target=field:8|peers=field:3,field:7|edge_fn=9|edge_issuer=field:3|edge_requirers=field:7,field:8",
            ],
            "R7 diagnostic labels are a stable machine-parseable contract"
        );
        assert!(
            forward_actions
                .windows(2)
                .all(|pair| { pair[0].diagnostic_key <= pair[1].diagnostic_key }),
            "actions sort by canonical (target, peers, edge) key"
        );

        let (local_a, local_b, field_peer) = (local(7, 2), local(8, 2), field(40));
        let local_observations = vec![
            ConflictObservation::new(12, local_b, Some(field_peer), vec![local_b]),
            ConflictObservation::new(12, local_a, Some(field_peer), vec![local_a]),
        ];
        let local_model = ref_model(&[local_a, local_b, field_peer]);
        let mut local_forward = Planner::new(41);
        let mut local_reverse = Planner::new(41);
        let local_forward_actions = continue_actions(local_forward.plan_round(
            SolverOutcome::Sat,
            &local_observations,
            &local_model,
        ));
        let local_reverse_actions = continue_actions(local_reverse.plan_round(
            SolverOutcome::Sat,
            &local_observations.iter().cloned().rev().collect::<Vec<_>>(),
            &local_model,
        ));
        assert_eq!(
            local_forward_actions, local_reverse_actions,
            "local owner identity participates in deterministic ordering"
        );
        assert_eq!(
            local_forward_actions
                .iter()
                .map(|action| action.diagnostic_label.as_str())
                .collect::<Vec<_>>(),
            vec![
                "event=l2_commit|kind=guarded|target=local:7:2|peers=field:40|edge_fn=12|edge_issuer=field:40|edge_requirers=local:7:2",
                "event=l2_commit|kind=guarded|target=local:8:2|peers=field:40|edge_fn=12|edge_issuer=field:40|edge_requirers=local:8:2",
            ],
            "different function owners cannot collide in the R7 local-slot identity"
        );
    }
}
