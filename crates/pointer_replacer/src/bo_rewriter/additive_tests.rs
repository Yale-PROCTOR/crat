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

fn requested_owners(
    prior: &StageSnapshot,
    candidate: &StageSnapshot,
    stage: FamilyStage,
    soundness: &[SoundnessWithdrawal],
) -> BTreeSet<SignatureClassId> {
    additive::withdrawals(prior, candidate, &FamilyPolicy::at(stage), soundness)
        .into_iter()
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
            (
                requested_owners(&prior, &candidate, stage, &[]),
                BTreeSet::from([owner]),
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
        let dependency = inputs
            .iter_mut()
            .find(|input| input.id == dependent)
            .unwrap();
        assert!(
            dependency.depends_on.contains(&root),
            "the delivered caller already depends on this callee"
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
        assert!(!candidate.plan.class_finalization.classes[&dependent].is_ready());
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
        assert_eq!(
            requested_owners(&prior, &candidate, FamilyStage::Option, &[witness]),
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
        assert_eq!(
            requested_owners(&prior, &candidate, FamilyStage::Option, &[witness]),
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
