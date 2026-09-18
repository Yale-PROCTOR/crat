//! RED-first R220 family preservation controls.

use std::collections::BTreeSet;

use super::{
    additive::{self, FamilyPolicy, FamilyStage, SoundnessWithdrawal, StageSnapshot},
    bridge_receipt::{BridgeCalleeId, SignatureClassId},
    decision::{Arm, Decision, DecisionTable, Degradation, DegradeReason, RequiredArmSet},
    plan::{self, ClassInput, ClassSite, Plan},
};

const BASELINE: &str = r#"
unsafe fn earlier_callee(callee_value: *const i32) -> i32 { *callee_value.offset(0) }
pub unsafe fn reference(reference_value: *const i32) -> i32 { *reference_value }
pub unsafe fn slice(slice_values: *const i32) -> i32 { *slice_values.offset(1) }
pub unsafe fn caller(caller_value: *const i32) -> i32 { earlier_callee(caller_value) }
"#;

fn with_baseline(test: impl FnOnce(StageSnapshot) + Send) {
    let rendered = super::emit_tests::ast_emitted_source_of(BASELINE).expect("prior rendering");
    assert!(rendered.contains("reference_value: &i32"), "{rendered}");
    assert!(rendered.contains("slice_values: &[i32]"), "{rendered}");
    assert!(
        super::verify::type_checks_str(&rendered),
        "prior rendering must type/borrow-check"
    );
    ::utils::compilation::run_compiler_on_str(BASELINE, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx(tcx).expect("prior decisions");
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("prior terminal plan");
        let prior = StageSnapshot {
            table,
            plan: emission.plan,
        };
        for binding in [
            "reference_value",
            "slice_values",
            "callee_value",
            "caller_value",
        ] {
            assert!(
                prior.plan.class_finalization.classes[&owner(&prior, binding)].is_ready(),
                "{binding} must be previously delivered"
            );
        }
        assert!(matches!(
            subject(&prior, "reference_value").1,
            Decision::Ref { .. }
        ));
        assert!(matches!(
            subject(&prior, "slice_values").1,
            Decision::Slice { .. }
        ));
        test(prior);
    })
    .expect("baseline compiler identities");
}

fn subject<'a>(
    snapshot: &'a StageSnapshot,
    binding: &str,
) -> &'a (super::decision::Subject, Decision) {
    snapshot
        .table
        .entries
        .iter()
        .find(|(subject, _)| subject.param_name.as_deref() == Some(binding))
        .unwrap_or_else(|| panic!("fixture binding {binding}"))
}

fn owner(snapshot: &StageSnapshot, binding: &str) -> SignatureClassId {
    SignatureClassId::of(subject(snapshot, binding).0.fn_did)
}

fn class_inputs(snapshot: &StageSnapshot) -> Vec<ClassInput> {
    snapshot
        .plan
        .class_finalization
        .classes
        .values()
        .map(|class| ClassInput {
            id: class.id,
            required_arms: class.required_arms,
            sites: class.sites.clone(),
            depends_on: class.depends_on.clone(),
            block_reasons: class.hold_reasons().to_vec(),
        })
        .collect()
}

fn candidate(prior: &StageSnapshot, inputs: Vec<ClassInput>) -> StageSnapshot {
    let mut candidate = prior.clone();
    candidate.plan.class_finalization = plan::finalize_class_inputs(inputs);
    let ready = candidate
        .plan
        .class_finalization
        .classes
        .values()
        .filter(|class| class.is_ready())
        .map(|class| class.id)
        .collect::<BTreeSet<_>>();
    candidate.plan.by_file.retain(|_, edits| {
        edits.retain(|edit| edit.owner_class.is_none_or(|owner| ready.contains(&owner)));
        !edits.is_empty()
    });
    candidate
}

/// **035 clause (3).** The owners the loop RECORDED as unresolved: it saw the
/// terminal, found no candidate whose own sites participate in it, and declined
/// to widen. These rows retire nothing, which is the whole point of them.
fn unresolved_owners(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    stage: FamilyStage,
    soundness: &[SoundnessWithdrawal],
) -> BTreeSet<SignatureClassId> {
    additive::withdrawals(prior, candidate, &FamilyPolicy::at(stage), soundness)
        .into_iter()
        .filter(|withdrawal| withdrawal.unresolved)
        .map(|withdrawal| {
            assert!(
                withdrawal.cause.starts_with("interface-path-unresolved:"),
                "an unresolved row carries the typed cause: {}",
                withdrawal.cause
            );
            assert!(
                withdrawal.subjects.is_empty(),
                "an unresolved row retires nothing"
            );
            withdrawal.owner
        })
        .collect()
}

fn requested_owners(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    stage: FamilyStage,
    soundness: &[SoundnessWithdrawal],
) -> BTreeSet<SignatureClassId> {
    additive::withdrawals(prior, candidate, &FamilyPolicy::at(stage), soundness)
        .into_iter()
        // 035 clause (3): an unresolved row retires nothing, so it is not a
        // requested owner. It is recorded and read, never acted on.
        .filter(|withdrawal| !withdrawal.unresolved)
        .map(|withdrawal| {
            assert!(
                !withdrawal.cause.is_empty(),
                "every family rollback needs attribution"
            );
            withdrawal.owner
        })
        .collect()
}

fn unsatisfied_family(stage: FamilyStage, kind: &str) {
    with_baseline(|prior| {
        let observed = ["reference_value", "slice_values"].map(|binding| {
            let owner = owner(&prior, binding);
            let mut inputs = class_inputs(&prior);
            inputs
                .iter_mut()
                .find(|input| input.id == owner)
                .unwrap()
                .sites
                .push(ClassSite::dropped(
                    owner,
                    owner,
                    Arm::Surface,
                    kind,
                    "r220-new-family-site-unbuilt",
                ));
            let candidate = candidate(&prior, inputs);
            assert!(!candidate.plan.class_finalization.classes[&owner].is_ready());
            // **035 (R453-2).** The terminal names no participant — the
            // anchor moved nothing of its own — so under clause (1) there is
            // nothing this rule may retire, and under clause (3) the loop
            // records it instead of dropping the owner's whole family. The
            // control's claim is unchanged in substance: the prior safe
            // disposition is not forced Raw. What changed is HOW: by retiring
            // nothing rather than by withdrawing the owner.
            // 035 (R453-2): a DROPPED SITE of this class is named by the
            // terminal, so the class's own mechanics are the participant and
            // clause (1) retires them. The rule removes the widening, not this.
            (
                (
                    requested_owners(&prior, &candidate, stage, &[]),
                    unresolved_owners(&prior, &candidate, stage, &[]),
                ),
                (BTreeSet::from([owner]), BTreeSet::new()),
            )
        });
        for (actual, expected) in observed {
            assert_eq!(
                actual, expected,
                "{stage:?} must restore the prior safe disposition, not force it Raw"
            );
        }
    });
}

#[test]
fn r220_slice_construction_failure_preserves_prior_ref_and_slice() {
    unsatisfied_family(FamilyStage::SliceConstruction, "slice-local-construction");
}

#[test]
fn r220_slice_use_failure_preserves_prior_ref_and_slice() {
    unsatisfied_family(FamilyStage::SliceUse, "slice-use-adapter");
}

#[test]
fn r220_option_failure_preserves_prior_ref_and_slice() {
    unsatisfied_family(FamilyStage::Option, "option-presentation");
}

#[test]
fn r220_previously_safe_callee_does_not_make_a_new_receipt_required() {
    with_baseline(|prior| {
        let caller = owner(&prior, "caller_value");
        let callee = owner(&prior, "callee_value");
        let mut inputs = class_inputs(&prior);
        let mut failed = ClassSite::dropped(
            caller,
            caller,
            Arm::C,
            "slice-use-adapter",
            "slice-use-existing-c-interface-carrier-unmapped",
        );
        failed.key.callee = BridgeCalleeId::Local(callee.local_def_id());
        inputs
            .iter_mut()
            .find(|input| input.id == caller)
            .unwrap()
            .sites
            .push(failed);
        let candidate = candidate(&prior, inputs);
        assert!(
            candidate.plan.class_finalization.classes[&callee].is_ready(),
            "callee stays safe in both stages"
        );
        assert!(!candidate.plan.class_finalization.classes[&caller].is_ready());
        assert_eq!(
            requested_owners(&prior, &candidate, FamilyStage::SliceUse, &[]),
            BTreeSet::from([caller]),
            "the pre-existing safe interface is not a new-family consistency requirement"
        );
    });
}

#[test]
fn r220_collision_yields_the_new_site_independently_of_order_and_class_ids() {
    with_baseline(|prior| {
        let a = owner(&prior, "reference_value");
        let b = owner(&prior, "slice_values");
        for (older, newer) in [(a, b), (b, a)] {
            let old_site = prior.plan.class_finalization.classes[&older]
                .sites
                .iter()
                .find(|site| {
                    site.edit_key != "-" && site.key.file != "-" && site.key.lo < site.key.hi
                })
                .expect("prior applied text site")
                .clone();
            for reverse in [false, true] {
                let mut inputs = class_inputs(&prior);
                let new_site = ClassSite::edit(
                    newer,
                    older,
                    Arm::Surface,
                    &old_site.key.file,
                    old_site.key.lo,
                    old_site.key.hi,
                    "subject-use",
                );
                let new_key = new_site.edit_key.clone();
                inputs
                    .iter_mut()
                    .find(|input| input.id == newer)
                    .unwrap()
                    .sites
                    .push(new_site);
                if reverse {
                    inputs.reverse();
                }
                let candidate = candidate(&prior, inputs);
                assert!(
                    candidate
                        .plan
                        .class_finalization
                        .collisions
                        .iter()
                        .any(|collision| {
                            (collision.left_edit_key == old_site.edit_key
                                && collision.right_edit_key == new_key)
                                || (collision.right_edit_key == old_site.edit_key
                                    && collision.left_edit_key == new_key)
                        }),
                    "the collision must name the exact old and added edit keys"
                );
                assert_eq!(
                    requested_owners(&prior, &candidate, FamilyStage::Option, &[]),
                    BTreeSet::from([newer]),
                    "newer transaction yields; class order is not provenance (reverse={reverse})"
                );
                // 035 (R453-2): the OLDER class is anchored by the same
                // collision but the terminal names no site of its own, so it is
                // recorded and retires nothing — the half of this control that
                // used to be carried by it not being requested.
                assert!(
                    !unresolved_owners(&prior, &candidate, FamilyStage::Option, &[])
                        .contains(&newer),
                    "the participating class is retired, not recorded"
                );
            }
        }
    });
}

#[test]
fn r220_unwitnessed_new_refusal_rolls_back_its_root_not_the_delivered_dependent() {
    with_baseline(|prior| {
        let root = owner(&prior, "callee_value");
        let dependent = owner(&prior, "caller_value");
        let mut inputs = class_inputs(&prior);
        inputs
            .iter_mut()
            .find(|input| input.id == root)
            .unwrap()
            .block_reasons
            .push("blocked-subject:slice-cursor-use".to_owned());
        // wave-6k narrowing (R217-2(a) migration): the caller's dependency on
        // the callee is a bare call-adapter edge, which the planning-time hold
        // no longer propagates over — the edge is recorded as narrowed and the
        // delivered dependent stays READY while the root is held.
        let dependency = inputs
            .iter_mut()
            .find(|input| input.id == dependent)
            .unwrap();
        assert!(
            !dependency.depends_on.contains(&root),
            "a bare call-adapter edge is narrowed, not a dependency"
        );
        assert!(
            prior
                .plan
                .narrowed_dependency_edges
                .contains(&(dependent, root)),
            "the narrowed edge is recorded"
        );
        let mut candidate = candidate(&prior, inputs);
        let (subject, decision) = candidate
            .table
            .entries
            .iter_mut()
            .find(|(subject, _)| subject.param_name.as_deref() == Some("callee_value"))
            .unwrap();
        *decision = Decision::Degraded(Degradation {
            subject: subject.identity_key("earlier_callee"),
            site: "R220 exact callee binding".to_owned(),
            reason: DegradeReason::SliceCursorUse,
        });
        assert!(!candidate.plan.class_finalization.classes[&root].is_ready());
        assert!(candidate.plan.class_finalization.classes[&dependent].is_ready());
        assert_eq!(
            requested_owners(&prior, &candidate, FamilyStage::SliceUse, &[]),
            BTreeSet::from([root]),
            "a new refusal label without a soundness witness cannot erase either prior delivery"
        );
    });
}

#[test]
fn r220_new_dependency_on_an_already_held_class_rolls_back_the_edge_owner() {
    with_baseline(|baseline| {
        let edge_owner = owner(&baseline, "reference_value");
        let old_held = owner(&baseline, "slice_values");
        let mut inputs = class_inputs(&baseline);
        inputs
            .iter_mut()
            .find(|input| input.id == old_held)
            .unwrap()
            .block_reasons
            .push("pre-existing-held-class".to_owned());
        let prior = candidate(&baseline, inputs);
        assert!(prior.plan.class_finalization.classes[&edge_owner].is_ready());
        assert!(!prior.plan.class_finalization.classes[&old_held].is_ready());
        assert!(
            !prior.plan.class_finalization.classes[&edge_owner]
                .depends_on
                .contains(&old_held)
        );

        let mut inputs = class_inputs(&prior);
        inputs
            .iter_mut()
            .find(|input| input.id == edge_owner)
            .unwrap()
            .depends_on
            .push(old_held);
        let candidate = candidate(&prior, inputs);
        assert!(!candidate.plan.class_finalization.classes[&edge_owner].is_ready());
        assert_eq!(
            prior.table.entries, candidate.table.entries,
            "the new edge is the only decision-level change"
        );
        assert_eq!(
            prior.plan.class_finalization.classes[&edge_owner].sites,
            candidate.plan.class_finalization.classes[&edge_owner].sites,
            "no changed subject or edit may accidentally identify the culprit"
        );
        assert_eq!(
            requested_owners(&prior, &candidate, FamilyStage::SliceUse, &[]),
            BTreeSet::from([edge_owner]),
            "the new dependency yields; its already-held target has no new transaction to withdraw"
        );
    });
}

fn with_null_ref_history(
    two_bindings: bool,
    test: impl FnOnce(StageSnapshot, StageSnapshot, SoundnessWithdrawal, SignatureClassId) + Send,
) {
    let extra = if two_bindings {
        "let other: *const i32 = 0 as *const i32; let _ = other.is_null();"
    } else {
        ""
    };
    let input = format!(
        "pub unsafe fn null_history() -> bool {{ let bad: *const i32 = 0 as *const i32; {extra} bad.is_null() }}"
    );
    assert!(
        super::verify::type_checks_str(&input),
        "the input itself has no null dereference"
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, ctx) =
            super::decide_table_with_ctx(tcx).expect("null-history compiler identities");
        let entries = table
            .entries
            .into_iter()
            .filter_map(|(subject, _)| {
                matches!(subject.param_name.as_deref(), Some("bad" | "other"))
                    .then_some((subject, Decision::Ref { mutable: false }))
            })
            .collect::<Vec<_>>();
        assert_eq!(entries.len(), if two_bindings { 2 } else { 1 });
        assert!(entries.iter().all(|(subject, _)| subject.null_init));
        let bad = entries
            .iter()
            .find(|(subject, _)| subject.param_name.as_deref() == Some("bad"))
            .unwrap()
            .0
            .clone();
        let owner = SignatureClassId::of(bad.fn_did);
        let null_construction = ctx.constructions.init_spans[&(bad.fn_did, bad.hir_id)];
        assert!(super::decision::emitability::is_zero_literal(
            tcx.hir_node(ctx.constructions.init_hirs[&(bad.fn_did, bad.hir_id)])
                .expect_expr()
        ));
        let mut arms = RequiredArmSet::default();
        arms.insert(Arm::Surface);
        let mut old = ClassInput::new(owner, arms);
        // Deliberately reconstruct a bad historical emission verdict, not an
        // analysis/model value: the UB-free input only tests these nulls.
        for (subject, _) in &entries {
            let span = subject.ty_span.expect("explicit raw declaration");
            let mut site = ClassSite::edit(
                owner,
                owner,
                Arm::Surface,
                "null-history.rs",
                span.lo().0,
                span.hi().0,
                "historical-ref-declaration",
            );
            site.expected_form = "ref-shared".to_owned();
            site.found_form = "raw".to_owned();
            old.sites.push(site);
        }
        let prior = StageSnapshot {
            table: DecisionTable {
                entries,
                ..DecisionTable::default()
            },
            plan: Plan {
                class_finalization: plan::finalize_class_inputs(vec![old.clone()]),
                ..Plan::default()
            },
        };
        assert!(prior.plan.class_finalization.classes[&owner].is_ready());
        let mut candidate = candidate(&prior, vec![old.blocked("blocked-subject:null-init")]);
        candidate
            .table
            .entries
            .iter_mut()
            .find(|(subject, _)| subject.hir_id == bad.hir_id)
            .unwrap()
            .1 = Decision::Degraded(Degradation {
            subject: bad.identity_key("null_history"),
            site: tcx
                .sess
                .source_map()
                .span_to_diagnostic_string(null_construction),
            reason: DegradeReason::NullInit,
        });
        let witness = SoundnessWithdrawal::null_required_reference(
            tcx,
            &ctx.constructions,
            &prior,
            (bad.fn_did, bad.hir_id),
        )
        .expect("the exact null initializer proves the old required-reference error");
        test(prior, candidate, witness, owner);
    })
    .expect("null-history parser context");
}

#[test]
fn r220_exact_null_ref_soundness_witness_permits_its_own_withdrawal() {
    with_null_ref_history(false, |prior, candidate, witness, _| {
        assert!(
            requested_owners(&prior, &candidate, FamilyStage::Option, &[witness]).is_empty(),
            "a matching witness may reject the genuinely bad prior Ref at null"
        );
    });
}

#[test]
fn r220_one_soundness_witness_does_not_exempt_another_lost_binding() {
    with_null_ref_history(true, |prior, candidate, witness, owner| {
        let rows = additive::withdrawals(
            &prior,
            &candidate,
            &FamilyPolicy::at(FamilyStage::Option),
            &[witness],
        );
        assert_eq!(
            rows.iter()
                .filter(|row| !row.unresolved)
                .map(|row| row.owner)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([owner]),
            "the other old Ref still needs delivery protection despite a sibling's witness"
        );
    });
}

#[test]
fn r220_null_ref_witness_cannot_exempt_a_later_valid_optional_prior() {
    with_null_ref_history(false, |mut prior, candidate, witness, owner| {
        // The private factory validated this witness against the historical
        // Ref. A subsequent predecessor has fixed that error by using Option.
        prior.table.entries[0].1 = Decision::Opt {
            mutable: false,
            slice: false,
            uses: Vec::new(),
        };
        for site in &mut prior
            .plan
            .class_finalization
            .classes
            .get_mut(&owner)
            .unwrap()
            .sites
        {
            site.expected_form = "opt-ref-shared".to_owned();
        }
        assert!(prior.plan.class_finalization.classes[&owner].is_ready());
        let rows = additive::withdrawals(
            &prior,
            &candidate,
            &FamilyPolicy::at(FamilyStage::Option),
            &[witness],
        );
        assert_eq!(
            rows.iter()
                .filter(|row| !row.unresolved)
                .map(|row| row.owner)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([owner]),
            "a proof about the old required Ref does not justify losing a valid Option declaration"
        );
    });
}

#[test]
fn r220_later_carrier_retries_and_restores_the_exact_predecessor_profile() {
    with_baseline(|prior| {
        let class = owner(&prior, "reference_value");
        let did = class.local_def_id();
        let mut policy = FamilyPolicy::at(FamilyStage::SliceConstruction);
        policy
            .withdrawn
            .insert((FamilyStage::SliceConstruction, class));
        assert!(!policy.enabled(did, FamilyStage::SliceConstruction));
        policy.stage = FamilyStage::SliceUse;
        assert!(
            policy.enabled(did, FamilyStage::SliceConstruction),
            "a new carrier may complete the earlier constructor"
        );
        policy.withdrawn.insert((FamilyStage::SliceUse, class));
        assert!(
            !policy.enabled(did, FamilyStage::SliceConstruction),
            "a failed retry restores the old constructor refusal"
        );
        assert!(!policy.enabled(did, FamilyStage::SliceUse));
        assert!(
            policy.enabled(
                owner(&prior, "slice_values").local_def_id(),
                FamilyStage::SliceUse
            ),
            "another owner's transaction is independent"
        );
    });
}

/// **Relay 043 (wave-6o 016 STOP 1, R397-6(a)) — the retirement arm.**
///
/// wave-6s2's `computed-suffix-raw-view` carries the evidence
/// `body-local-raw-alias-schedule-unproved`, premised on the destination
/// staying RAW. When the Option family takes that destination the receipt
/// layer drops the adapter as `slice-use-evidence-held`, and the exclusion
/// re-derivation used to read that drop as a family site that failed — which
/// falls the WHOLE owner back to the predecessor's mechanics, one stage before
/// wave-6o's own arm runs (their report 016 claims 3–5, five rows).
///
/// The site is SUPERSEDED, not unsatisfied. Pinned both ways on one input: with
/// the destination moving to the Option family nothing is requested; without
/// that move the same drop still requests, so the exception cannot widen into
/// "a dropped slice-use adapter never counts".
#[test]
fn r397_6a_a_superseded_slice_use_adapter_is_not_an_unsatisfied_family_site() {
    with_baseline(|prior| {
        let owner = owner(&prior, "slice_values");
        let dropped = |from: &StageSnapshot| {
            let mut inputs = class_inputs(from);
            inputs
                .iter_mut()
                .find(|input| input.id == owner)
                .unwrap()
                .sites
                .push(ClassSite::dropped(
                    owner,
                    owner,
                    Arm::Surface,
                    "slice-use-adapter",
                    "slice-use-evidence-held",
                ));
            candidate(from, inputs)
        };

        // (1) The destination does not move: the drop is an unsatisfied family
        //     site and the owner falls back, exactly as before this arm.
        // 035 (R453-2): the drop names no participant, so it is recorded and
        // retires nothing. What this half of the control pins is that the loop
        // still SEES it — the supersession below removes the row entirely.
        let bare = dropped(&prior);
        assert_eq!(
            requested_owners(&prior, &bare, FamilyStage::Option, &[]),
            BTreeSet::from([owner]),
            "without the destination move the drop must still request"
        );

        // (2) The destination moves to the Option family — wave-6o's shape,
        //     where it was `degraded:null-init` in the predecessor and becomes
        //     `Option<&[u8]>` here. The adapter is superseded, not failed.
        let mut before = prior.clone();
        for (subject, decided) in &mut before.table.entries {
            if SignatureClassId::of(subject.fn_did) == owner {
                *decided = Decision::Degraded(Degradation {
                    subject: subject.label.clone(),
                    site: "<the destination, still raw>".to_owned(),
                    reason: DegradeReason::KindRaw,
                });
            }
        }
        let mut composed = dropped(&before);
        for (subject, decided) in &mut composed.table.entries {
            if SignatureClassId::of(subject.fn_did) == owner {
                *decided = Decision::Opt {
                    mutable: false,
                    slice: true,
                    uses: Vec::new(),
                };
            }
        }
        assert!(
            requested_owners(&before, &composed, FamilyStage::Option, &[]).is_empty(),
            "a superseded adapter must not fall the owner back"
        );
        assert!(
            unresolved_owners(&before, &composed, FamilyStage::Option, &[]).is_empty(),
            "a superseded adapter leaves no row at all, not even an unresolved one"
        );
    });
}

/// **035 clause (2), protection (a) — a candidate PLACED at the predecessor
/// frame is not retired by a terminal that names no site of its own.**
///
/// The shape wave-6s 020 and slicecursor 030 measured: a neighbour's row moves
/// into or out of a family, an anchor appears, and candidates that were placed
/// a frame ago — heman's `edt::{w,z}` and `edt_with_payload::{w,z}`, wave-6s's
/// twelve — are retired by proximity although none of them participates in the
/// terminal. Placement IS the statement that the previous frame's interface was
/// consistent with the candidate; a change that does not touch its interval
/// cannot have made it inconsistent.
///
/// The control is the second half: a candidate that is NOT placed at the
/// predecessor still yields, so this is a protection and not a refusal to
/// retire anything.
#[test]
fn r453_2_a_candidate_placed_at_the_predecessor_is_not_retired_by_proximity() {
    with_baseline(|prior| {
        let subject_class = owner(&prior, "slice_values");
        // A terminal on this class that names no site of its own: a dropped
        // site whose caller is ANOTHER class, so `own_site` is false and the
        // candidate path decides.
        let other_class = owner(&prior, "reference_value");
        let mut inputs = class_inputs(&prior);
        inputs
            .iter_mut()
            .find(|input| input.id == subject_class)
            .unwrap()
            .sites
            .push(ClassSite::dropped(
                other_class,
                other_class,
                Arm::Surface,
                "slice-use-adapter",
                "r220-new-family-site-unbuilt",
            ));
        let mut candidate = candidate(&prior, inputs);
        // Move the candidate: its decision differs from the predecessor's.
        for (subject, decided) in &mut candidate.table.entries {
            if SignatureClassId::of(subject.fn_did) == subject_class {
                *decided = Decision::Opt {
                    mutable: false,
                    slice: true,
                    uses: Vec::new(),
                };
            }
        }
        let rows = additive::withdrawals(
            &prior,
            &candidate,
            &FamilyPolicy::at(FamilyStage::Option),
            &[],
        );
        let retired = rows
            .iter()
            .filter(|row| !row.unresolved)
            .flat_map(|row| row.subjects.clone())
            .collect::<Vec<_>>();
        assert!(
            retired.is_empty(),
            "a placed candidate was retired by a terminal it does not participate in: {rows:#?}"
        );
    });
}

/// **R459-5 (wave-5d2 029 §3) — a degraded subject whose emitted declaration
/// another subject's plan renders is not a blocker of its class.**
///
/// heman's `transform_to_*` views `f` / `d` are degraded `copy-source-coupled`
/// while the OWNER's plan renders their declarations as exact suffixes. R456-8's
/// counter already calls such a row delivered whichever plan rendered it; until
/// this predicate the class hold still read it as a blocker, so the two
/// consumers disagreed about one row.
///
/// Pinned on both halves of the predicate: an edit of ANOTHER subject covering
/// the degraded subject's declaration puts it in the set, and the same edit
/// carrying the subject's OWN identity tail does not — a subject never
/// discharges itself.
#[test]
fn r459_5_a_declaration_rendered_by_another_plan_is_not_a_blocker() {
    with_baseline(|prior| {
        let (degraded, _) = subject(&prior, "slice_values").clone();
        let owner = SignatureClassId::of(degraded.fn_did);
        let tail = format!(
            "::{}#{}",
            degraded.param_name.as_deref().unwrap(),
            degraded.local.as_u32()
        );
        let mut table = prior.table.clone();
        for (subject, decision) in &mut table.entries {
            if subject.hir_id == degraded.hir_id {
                *decision = Decision::Degraded(Degradation {
                    subject: subject.label.clone(),
                    site: "<the derived view>".to_owned(),
                    reason: DegradeReason::KindRaw,
                });
            }
        }
        // The declaration range this fake locator reports for every subject.
        let locate = |_: rustc_span::Span| {
            Ok((
                plan::FileKey::Virtual("main.rs".to_owned()),
                100usize,
                120usize,
            ))
        };
        let covering = |subject_id: &str| {
            let mut planned = prior.plan.clone();
            let mut edit = planned
                .by_file
                .values()
                .flatten()
                .next()
                .expect("the baseline plans at least one edit")
                .clone();
            edit.lo = 90;
            edit.hi = 130;
            edit.edit_kind = "subject-declaration";
            edit.owner_class = Some(owner);
            edit.subject_id = subject_id.to_owned();
            planned.by_file.clear();
            planned
                .by_file
                .insert(plan::FileKey::Virtual("main.rs".to_owned()), vec![edit]);
            plan::declarations_rendered_by_another_plan(&planned, &table, locate)
                .contains(&(degraded.fn_did, degraded.hir_id))
        };
        assert!(
            covering("some_other::owner_value#7"),
            "another subject's declaration edit covers this one"
        );
        assert!(
            !covering(&format!("slice{tail}")),
            "a subject must not discharge itself"
        );
    });
}
