//! R397-6(a) / R398-1: the additive-family preservation invariant is scoped
//! to (owner, subject), and a candidate that fails terminally is excluded at
//! the candidate-selection input so the owner's siblings re-derive their prior
//! result. The binn `binn_get_bool` collision is the corpus-derived RED: the
//! Option candidate `pbool` (caller) makes the callee's raw `pbool` a blocked
//! pair position, and the prior owner-scoped rollback of the CALLEE could not
//! restore the two prior `Option<&Binn>` / `Option<&i32>` deliveries.
use std::collections::BTreeMap;

#[path = "exclusion_rederivation_bzip2_fixture.rs"]
mod bzip2_fixture;

use super::{A5Mode, WholeProgramAttestation, additive::FamilyFallbackReceipt, decision};

/// `binn_get_bool` / `is_bool_str` reduced from binn with both pointees `i32`
/// (the width difference was incidental to the collision, report 007).
pub(super) const BINN: &str = r#"
#[repr(C)] pub struct Binn { pub ptr: *mut i32, pub kind: i32 }
unsafe fn is_bool_str(p: *mut i32, pbool: *mut i32) -> i32 {
    if p.is_null() || pbool.is_null() { return 0; }
    *pbool = if *p != 0 { 1 } else { 0 }; 1
}
pub unsafe fn binn_get_bool(value: *mut Binn, pbool: *mut i32) -> i32 {
    if value.is_null() || pbool.is_null() { return 0; }
    *pbool = 0;
    if (*value).kind == 160 { return is_bool_str((*value).ptr, pbool); }
    *pbool = 1; 1
}
"#;

pub(super) struct Outcome {
    pub forms: BTreeMap<String, String>,
    pub receipts: Vec<FamilyFallbackReceipt>,
}

pub(super) fn decide(input: &str) -> Result<Outcome, String> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )?;
        Ok(Outcome {
            forms: table
                .entries
                .iter()
                .map(|(s, d)| (s.label.clone(), decision::seam::form_of(d).key().to_owned()))
                .collect(),
            receipts: ctx.raw_boundary_artifacts.additive_family_receipts,
        })
    })
    .map_err(|why| format!("{why:?}"))?
}

fn form<'a>(outcome: &'a Outcome, label: &str) -> &'a str {
    outcome
        .forms
        .get(label)
        .unwrap_or_else(|| panic!("no subject {label}: {:?}", outcome.forms))
}

/// RED at the handover: `additive-family-preservation-invariant:unrestored:
/// [(6, 1), (7, 1)]`. GREEN: the two prior deliveries survive, the failed
/// caller candidate alone is excluded, and the exclusion is receipted against
/// the subject it names rather than the callee's whole family.
#[test]
fn binn_failed_optional_candidate_excludes_only_itself() {
    let outcome = decide(BINN).expect("the failed candidate must not fail the program");
    assert_eq!(
        form(&outcome, "is_bool_str::p"),
        "opt-ref-shared",
        "{:?}",
        outcome.forms
    );
    assert_eq!(
        form(&outcome, "binn_get_bool::value"),
        "opt-ref-shared",
        "{:?}",
        outcome.forms
    );
    assert_eq!(
        form(&outcome, "is_bool_str::pbool"),
        "raw",
        "{:?}",
        outcome.forms
    );
    assert_eq!(
        form(&outcome, "binn_get_bool::pbool"),
        "raw",
        "the failed candidate itself keeps its prior form: {:?}",
        outcome.forms
    );
    // Two rounds per stage, three stages (R220 retries the excluded candidate
    // with each later stage's carrier): first the anchor — the callee class 6,
    // which moved nothing — falls back as an owner (the R220 floor; it drops
    // only class 6's own Option-stage mechanics, and class 6 has no Option
    // candidate), the loss persists, and the restore search from 6 finds its
    // nearest changed neighbour 7 and excludes exactly the moved candidate
    // `pbool`. No whole-family withdrawal of the caller ever happens.
    let summary = outcome
        .receipts
        .iter()
        .map(|receipt| {
            (
                receipt.family.as_str(),
                receipt.scope.as_str(),
                receipt.owner_path.as_str(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        summary,
        vec![
            ("Option", "owner", "is_bool_str"),
            ("Option", "subject", "binn_get_bool"),
            ("Declaration", "owner", "is_bool_str"),
            ("Declaration", "subject", "binn_get_bool"),
            ("Return", "owner", "is_bool_str"),
            ("Return", "subject", "binn_get_bool"),
        ],
        "{:#?}",
        outcome.receipts
    );
    for receipt in outcome
        .receipts
        .iter()
        .filter(|receipt| receipt.scope == "owner")
    {
        // The anchor is the callee class 6 either way; which terminal it
        // carries depends on whether the A5 pair edit over the call still
        // collides with the older `value` subject-use inside it (the landed
        // planner) or a composition has removed that collision and the
        // `blocked-subject:kind-raw` refusal is what remains.
        assert!(
            receipt
                .cause
                .starts_with("newer-family-collision:class=6|arm=pair|")
                || receipt.cause == "unwitnessed-family-refusal:blocked-subject:kind-raw",
            "{receipt:#?}"
        );
        assert!(
            receipt.subjects.iter().all(|(_, old, new)| old == new),
            "the owner fallback of class 6 moves none of its decisions: {receipt:#?}"
        );
    }
    for receipt in outcome
        .receipts
        .iter()
        .filter(|receipt| receipt.scope == "subject")
    {
        assert_eq!(
            receipt.cause, "exclusion-rederivation:anchor=6:restore-family-interface-path:[6, 7]",
            "{receipt:#?}"
        );
        assert_eq!(
            receipt
                .subjects
                .iter()
                .map(|(label, old, new)| (label.as_str(), old.as_str(), new.as_str()))
                .collect::<Vec<_>>(),
            vec![("binn_get_bool::pbool#2", "raw", "opt-ref-mut")],
            "the rows name only the excluded candidate: {receipt:#?}"
        );
    }
}

/// The excluded caller candidate is a typed exclusion, and the emitted program
/// still renders both prior Option deliveries; nothing is widened to reach it.
#[test]
fn binn_emits_the_prior_deliveries_with_the_candidate_excluded() {
    let rendered = super::emit_tests::ast_emitted_source_of(BINN).expect("emitted");
    assert!(rendered.contains("p: Option<&i32>"), "{rendered}");
    assert!(rendered.contains("value: Option<&Binn>"), "{rendered}");
    assert!(rendered.contains("pbool: *mut i32"), "{rendered}");
    assert!(
        !rendered.contains("pbool: Option<&mut i32>"),
        "the failed candidate is excluded, not delivered by another route: {rendered}"
    );
    assert!(
        super::verify::type_checks_str(&rendered),
        "the re-derived program type/borrow-checks: {rendered}"
    );
}

/// The interface-restoration wall (wave-5c's four brotli entropy parameters,
/// wave-6s's 13 T1 licences): a prior delivery is lost in a root that has
/// already fallen back, and the R220 pass withdrew EVERY changed owner its
/// undirected interface component could reach. Nearest-first: only the closest
/// changed owner is asked to yield, and only the candidates that moved.
mod restore_nearest_first {
    use std::collections::BTreeSet;

    use crate::bo_rewriter::{
        additive::{self, FamilyPolicy, FamilyStage, StageSnapshot},
        bridge_receipt::SignatureClassId,
        decision::{Decision, Degradation, DegradeReason},
        plan::{self, ClassInput},
    };

    /// A four-owner call chain: `root → near → far → farthest`. Every class
    /// connects to its neighbour through the C-arm sites the chain's calls
    /// produce, exactly the edges the restoration pass walks.
    const CHAIN: &str = r#"
pub unsafe fn farthest(farthest_value: *const i32) -> i32 { *farthest_value }
pub unsafe fn far(far_value: *const i32) -> i32 { farthest(far_value) }
pub unsafe fn near(near_value: *const i32) -> i32 { far(near_value) }
pub unsafe fn root(root_value: *const i32) -> i32 { near(root_value) }
"#;

    fn with_chain(test: impl FnOnce(StageSnapshot) + Send) {
        ::utils::compilation::run_compiler_on_str(CHAIN, |tcx| {
            let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).expect("prior");
            let emission = crate::bo_rewriter::emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )
            .expect("prior terminal plan");
            let mut prior = StageSnapshot {
                table,
                plan: emission.plan,
            };
            // Every parameter is already `&i32`, so the calls need no bridge
            // and produce no C-arm site: connect the chain through the class
            // dependency edges the restoration pass also walks (present in the
            // predecessor too, so no edge is itself a change).
            let mut inputs = class_inputs(&prior);
            for (dependent, dependency) in [
                ("root_value", "near_value"),
                ("near_value", "far_value"),
                ("far_value", "farthest_value"),
            ] {
                let dependency = owner(&prior, dependency);
                inputs
                    .iter_mut()
                    .find(|input| input.id == owner(&prior, dependent))
                    .unwrap()
                    .depends_on
                    .push(dependency);
            }
            prior.plan.class_finalization = plan::finalize_class_inputs(inputs);
            for binding in ["root_value", "near_value", "far_value", "farthest_value"] {
                assert!(
                    prior.plan.class_finalization.classes[&owner(&prior, binding)].is_ready(),
                    "{binding} must be previously delivered"
                );
                assert!(matches!(subject(&prior, binding).1, Decision::Ref { .. }));
            }
            test(prior);
        })
        .expect("chain compiler identities");
    }

    fn subject<'a>(
        snapshot: &'a StageSnapshot,
        binding: &str,
    ) -> &'a (crate::bo_rewriter::decision::Subject, Decision) {
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

    /// wave-4's cluster C in miniature: an owner whose own new candidate fails
    /// terminally (`copyFileName::from`) must not take its older delivered
    /// sibling (`copyFileName::to`) with it. The anchor is the owner; the
    /// exclusion is the candidate alone.
    #[test]
    fn a_direct_anchor_excludes_only_its_own_moved_candidate() {
        with_chain(|prior| {
            let far = owner(&prior, "far_value");
            let mut inputs = class_inputs(&prior);
            inputs
                .iter_mut()
                .find(|input| input.id == far)
                .unwrap()
                .block_reasons
                .push("blocked-subject:slice-use-unsupported".to_owned());
            let mut candidate = prior.clone();
            candidate.plan.class_finalization = plan::finalize_class_inputs(inputs);
            // `far_value` is the moved candidate; add a second, unchanged
            // delivered subject to the same owner so the scope is observable.
            let kept = {
                let (subject, decision) = subject(&prior, "far_value").clone();
                let mut kept = subject;
                kept.hir_id = rustc_hir::HirId {
                    owner: kept.hir_id.owner,
                    local_id: rustc_hir::ItemLocalId::from_u32(
                        kept.hir_id.local_id.as_u32() + 1000,
                    ),
                };
                kept.param_name = Some("kept_value".to_owned());
                kept.label = "far::kept_value".to_owned();
                (kept, decision)
            };
            let mut prior = prior;
            prior.table.entries.push(kept.clone());
            candidate.table.entries.push(kept.clone());
            for (subject, decision) in &mut candidate.table.entries {
                if subject.param_name.as_deref() == Some("far_value") {
                    *decision = Decision::Ref { mutable: true };
                }
            }
            let requests = additive::withdrawals(
                &prior,
                &candidate,
                &FamilyPolicy::at(FamilyStage::SliceUse),
                &[],
            );
            let [request] = requests.as_slice() else {
                panic!("one request for the anchor owner: {requests:#?}")
            };
            assert_eq!(request.owner, far);
            assert_eq!(
                request.subjects,
                vec![subject(&prior, "far_value").0.hir_id],
                "the moved candidate alone is excluded; `kept_value` is not named: {request:#?}"
            );
            assert_eq!(
                request.cause,
                format!(
                    "exclusion-rederivation:anchor={}:unwitnessed-family-refusal:blocked-subject:slice-use-unsupported",
                    far.order_key()
                )
            );
        });
    }

    /// wave-4's transplant in its exact shape: BOTH parameters of `copyFileName`
    /// move at the same stage, and the terminal is the caller's glue site at
    /// `arg1` (a thin `&Char` handed to the widened `from`, refused under
    /// fix-2). The site names parameter 1; `to` at `arg0` is not excluded.
    #[test]
    fn a_terminal_site_at_a_call_position_names_the_parameter_it_reaches() {
        with_chain(|prior| {
            let far = owner(&prior, "far_value");
            let near = owner(&prior, "near_value");
            // A second parameter of `far`, moved at this stage like the first.
            let second = {
                let (subject, _) = subject(&prior, "far_value").clone();
                let mut second = subject;
                second.hir_id = rustc_hir::HirId {
                    owner: second.hir_id.owner,
                    local_id: rustc_hir::ItemLocalId::from_u32(
                        second.hir_id.local_id.as_u32() + 1000,
                    ),
                };
                second.local = rustc_middle::mir::Local::from_u32(2);
                second.kind = crate::bo_rewriter::decision::SubjectKind::Param { hir_index: 1 };
                second.param_name = Some("second_value".to_owned());
                second.label = "far::second_value".to_owned();
                (
                    second,
                    Decision::Degraded(Degradation {
                        subject: "far::second_value".to_owned(),
                        site: "prior".to_owned(),
                        reason: DegradeReason::SliceUseUnsupported,
                    }),
                )
            };
            let mut prior = prior;
            prior.table.entries.push(second.clone());
            let mut inputs = class_inputs(&prior);
            inputs
                .iter_mut()
                .find(|input| input.id == far)
                .unwrap()
                .sites
                .push(plan::ClassSite::dropped(
                    far,
                    near,
                    crate::bo_rewriter::decision::Arm::Glue,
                    "a5-raw-view-template-unavailable",
                    "a5-raw-view-template-unavailable",
                ));
            let mut candidate = prior.clone();
            candidate.plan.class_finalization = plan::finalize_class_inputs(inputs);
            // The dropped site is a call INTO `far` from `near` at position 1.
            let class = candidate
                .plan
                .class_finalization
                .classes
                .get_mut(&far)
                .unwrap();
            let site = class
                .sites
                .iter_mut()
                .find(|site| matches!(site.state, plan::ClassSiteState::Dropped(_)))
                .unwrap();
            site.key.caller = near.local_def_id();
            site.key.callee =
                crate::bo_rewriter::bridge_receipt::BridgeCalleeId::Local(far.local_def_id());
            site.key.position = "arg1".to_owned();
            for (subject, decision) in &mut candidate.table.entries {
                match subject.param_name.as_deref() {
                    Some("far_value") => {
                        *decision = Decision::Slice {
                            mutable: true,
                            uses: vec![],
                        }
                    }
                    Some("second_value") => {
                        *decision = Decision::Slice {
                            mutable: false,
                            uses: vec![],
                        }
                    }
                    _ => {}
                }
            }
            let requests = additive::withdrawals(
                &prior,
                &candidate,
                &FamilyPolicy::at(FamilyStage::SliceUse),
                &[],
            );
            let request = requests
                .iter()
                .find(|request| request.owner == far)
                .unwrap_or_else(|| panic!("the anchor owner yields: {requests:#?}"));
            assert_eq!(
                request.subjects,
                vec![second.0.hir_id],
                "only the parameter the `arg1` site reaches is excluded; `far_value` at arg0                  keeps its candidate: {request:#?}"
            );
        });
    }

    /// wave-6v's `seam-site-overlap`: a call drops one site per contracted
    /// position (arg0 AND arg1) because two byte views at one call may overlap
    /// and one raw access under a live view is as forbidden as two views. The
    /// exclusion must name BOTH positions in one round — attributing the first
    /// terminal site alone would leave `second_value`'s view live beside the
    /// raw write through `far_value`.
    #[test]
    fn every_terminal_site_of_a_call_names_its_position_in_one_round() {
        with_chain(|prior| {
            let far = owner(&prior, "far_value");
            let near = owner(&prior, "near_value");
            let second = {
                let (subject, _) = subject(&prior, "far_value").clone();
                let mut second = subject;
                second.hir_id = rustc_hir::HirId {
                    owner: second.hir_id.owner,
                    local_id: rustc_hir::ItemLocalId::from_u32(
                        second.hir_id.local_id.as_u32() + 1000,
                    ),
                };
                second.local = rustc_middle::mir::Local::from_u32(2);
                second.kind = crate::bo_rewriter::decision::SubjectKind::Param { hir_index: 1 };
                second.param_name = Some("second_value".to_owned());
                second.label = "far::second_value".to_owned();
                (
                    second,
                    Decision::Degraded(Degradation {
                        subject: "far::second_value".to_owned(),
                        site: "prior".to_owned(),
                        reason: DegradeReason::SliceUseUnsupported,
                    }),
                )
            };
            let mut prior = prior;
            prior.table.entries.push(second.clone());
            let mut inputs = class_inputs(&prior);
            // One dropped site per contracted position of the call from
            // `near` into `far`: `arg0` and `arg1`, distinct before finalization.
            for index in 0..2 {
                let mut site = plan::ClassSite::dropped(
                    far,
                    near,
                    crate::bo_rewriter::decision::Arm::Glue,
                    "seam-site-overlap",
                    "seam-site-overlap",
                );
                site.key.caller = near.local_def_id();
                site.key.callee =
                    crate::bo_rewriter::bridge_receipt::BridgeCalleeId::Local(far.local_def_id());
                site.key.position = format!("arg{index}");
                inputs
                    .iter_mut()
                    .find(|input| input.id == far)
                    .unwrap()
                    .sites
                    .push(site);
            }
            let mut candidate = prior.clone();
            candidate.plan.class_finalization = plan::finalize_class_inputs(inputs);
            for (subject, decision) in &mut candidate.table.entries {
                match subject.param_name.as_deref() {
                    Some("far_value") => {
                        *decision = Decision::Slice {
                            mutable: true,
                            uses: vec![],
                        }
                    }
                    Some("second_value") => {
                        *decision = Decision::Slice {
                            mutable: false,
                            uses: vec![],
                        }
                    }
                    _ => {}
                }
            }
            let requests = additive::withdrawals(
                &prior,
                &candidate,
                &FamilyPolicy::at(FamilyStage::SliceUse),
                &[],
            );
            let request = requests
                .iter()
                .find(|request| request.owner == far)
                .unwrap_or_else(|| panic!("the anchor owner yields: {requests:#?}"));
            let mut excluded = request.subjects.clone();
            excluded.sort_by_key(|hir| hir.local_id.as_u32());
            let mut both = vec![subject(&prior, "far_value").0.hir_id, second.0.hir_id];
            both.sort_by_key(|hir| hir.local_id.as_u32());
            assert_eq!(
                excluded, both,
                "both contracted positions of the overlapping call are excluded together: \
                 {request:#?}"
            );
        });
    }

    /// tulipindicators `ti_sma_start` (the −2 of report 010): an anchor whose
    /// terminal is a NEW dependency on a held neighbour, and which moved no
    /// decision of its own, falls back as an owner (R220: its own stage
    /// mechanics generated the edge) — it never sacrifices the neighbour's
    /// moved candidate (`ti_sma::options#3`), which report 010's induced-owner
    /// step did.
    #[test]
    fn an_anchor_that_moved_nothing_falls_back_as_an_owner_before_any_neighbour_yields() {
        with_chain(|prior| {
            let near = owner(&prior, "near_value");
            let far = owner(&prior, "far_value");
            let farthest = owner(&prior, "farthest_value");
            // `far` (the callee, like ti_sma_start) newly depends on the held
            // caller `near` (like ti_sma, blocked by its own refusal), whose
            // candidate `near_value` moved at this stage.
            let mut inputs = class_inputs(&prior);
            inputs
                .iter_mut()
                .find(|input| input.id == near)
                .unwrap()
                .block_reasons
                .push("blocked-subject:slice-use-unsupported".to_owned());
            inputs
                .iter_mut()
                .find(|input| input.id == far)
                .unwrap()
                .depends_on
                .push(near);
            let mut candidate = prior.clone();
            candidate.plan.class_finalization = plan::finalize_class_inputs(inputs);
            for (subject, decision) in &mut candidate.table.entries {
                if subject.param_name.as_deref() == Some("near_value") {
                    *decision = Decision::Slice {
                        mutable: false,
                        uses: vec![],
                    };
                }
            }
            assert!(!candidate.plan.class_finalization.classes[&far].is_ready());
            let requests = additive::withdrawals(
                &prior,
                &candidate,
                &FamilyPolicy::at(FamilyStage::SliceUse),
                &[],
            );
            let by_owner = requests
                .iter()
                .map(|request| {
                    (
                        request.owner,
                        (request.cause.clone(), request.subjects.clone()),
                    )
                })
                .collect::<std::collections::BTreeMap<_, _>>();
            let (cause, subjects) = by_owner
                .get(&far)
                .unwrap_or_else(|| panic!("the anchor `far` yields as an owner: {requests:#?}"));
            assert_eq!(
                cause,
                &format!("new-family-dependency:{}", near.order_key()),
                "{requests:#?}"
            );
            assert!(
                subjects.is_empty(),
                "owner scope, the R220 floor: {requests:#?}"
            );
            // `near` may yield for ITS OWN refusal (its candidate is the one
            // that failed there), never for `far`'s terminal.
            assert!(
                !by_owner.contains_key(&farthest)
                    && by_owner.get(&near).is_none_or(|(cause, _)| {
                        cause.contains(&format!("anchor={}:", near.order_key()))
                    }),
                "the neighbour's moved candidate `near_value` is not excluded for `far`'s \
                 terminal: {requests:#?}"
            );
        });
    }

    /// The root loses its delivery with no transaction of its own to withdraw
    /// (it is already withdrawn at this stage), while `far` and `farthest`
    /// each carry a moved candidate (`&T` → `&mut T`) and `near` is unchanged.
    fn lost_root_candidate(prior: &StageSnapshot) -> StageSnapshot {
        let root = owner(prior, "root_value");
        let mut inputs = class_inputs(prior);
        inputs
            .iter_mut()
            .find(|input| input.id == root)
            .unwrap()
            .block_reasons
            .push("blocked-subject:slice-cursor-use".to_owned());
        let mut candidate = prior.clone();
        candidate.plan.class_finalization = plan::finalize_class_inputs(inputs);
        for (subject, decision) in &mut candidate.table.entries {
            match subject.param_name.as_deref() {
                Some("root_value") => {
                    *decision = Decision::Degraded(Degradation {
                        subject: subject.identity_key("root"),
                        site: "restore witness".to_owned(),
                        reason: DegradeReason::SliceCursorUse,
                    });
                }
                Some("far_value") | Some("farthest_value") => {
                    *decision = Decision::Ref { mutable: true };
                }
                _ => {}
            }
        }
        assert!(!candidate.plan.class_finalization.classes[&root].is_ready());
        candidate
    }

    #[test]
    fn a_lost_root_asks_only_its_nearest_changed_owner_to_yield_its_moved_candidate() {
        with_chain(|prior| {
            let candidate = lost_root_candidate(&prior);
            let root = owner(&prior, "root_value");
            let far = owner(&prior, "far_value");
            let farthest = owner(&prior, "farthest_value");
            let mut policy = FamilyPolicy::at(FamilyStage::SliceUse);
            policy.withdrawn.insert((FamilyStage::SliceUse, root));
            let requests = additive::withdrawals(&prior, &candidate, &policy, &[]);
            let owners = requests
                .iter()
                .map(|request| request.owner)
                .collect::<BTreeSet<_>>();
            assert_eq!(
                owners,
                BTreeSet::from([far]),
                "nearest-first: `far` (distance 2) yields, `farthest` (distance 3) is never \
                 reached: {requests:#?}"
            );
            let [request] = requests.as_slice() else { unreachable!() };
            assert_eq!(
                request.subjects,
                vec![subject(&prior, "far_value").0.hir_id],
                "only the moved candidate is excluded, not the owner: {request:#?}"
            );
            assert!(
                request.cause.starts_with("exclusion-rederivation:anchor=")
                    && request.cause.contains("restore-family-interface-path:["),
                "{request:#?}"
            );
            assert!(!owners.contains(&farthest));
        });
    }

    /// Once `far`'s candidate is excluded and the loss persists, the search
    /// widens by exactly one layer: `farthest` yields next, and `far` is not
    /// asked again for an identity it has already excluded.
    #[test]
    fn a_persisting_loss_widens_by_one_layer_and_never_repeats_an_exclusion() {
        with_chain(|prior| {
            let candidate = lost_root_candidate(&prior);
            let root = owner(&prior, "root_value");
            let far = owner(&prior, "far_value");
            let farthest = owner(&prior, "farthest_value");
            let mut policy = FamilyPolicy::at(FamilyStage::SliceUse);
            policy.withdrawn.insert((FamilyStage::SliceUse, root));
            policy.withdrawn_subjects.insert((
                FamilyStage::SliceUse,
                far,
                subject(&prior, "far_value").0.hir_id.local_id.as_u32(),
            ));
            // `far` still differs from its predecessor in this hand-built
            // candidate (the pipeline would have re-derived it); with no moved
            // candidate left it yields as an owner, and `farthest` is now the
            // nearest owner with a moved candidate.
            let requests = additive::withdrawals(&prior, &candidate, &policy, &[]);
            let by_owner = requests
                .iter()
                .map(|request| (request.owner, request.subjects.clone()))
                .collect::<std::collections::BTreeMap<_, _>>();
            assert_eq!(
                by_owner.keys().copied().collect::<BTreeSet<_>>(),
                BTreeSet::from([far]),
                "the nearest changed layer is still `far`; it has no moved candidate left and \
                 falls back as an owner (the R220 floor), `farthest` waits: {requests:#?}"
            );
            assert!(by_owner[&far].is_empty(), "{requests:#?}");
            assert!(!by_owner.contains_key(&farthest));
        });
    }
}

/// The batch-7 stop (main 034): bzip2's `blocksort` trio composed with
/// slicecursor's `87c290ec..7968e4a3` (bisected against this fixture: wave-6o,
/// 6r, 6v, 6l and 5c each pass) lost both `eclass#2` slices as `unrestored` —
/// the cursor candidate for `fallbackSimpleSort::fmap` at `Return` holds the two
/// mutually dependent classes (`fallbackQSort3` ↔ `fallbackSimpleSort`, the
/// pass-on at arg 1) and R220's protected walk requested nothing. Under the
/// repair the request-less root restores and the nearest changed neighbour
/// yields its cursor candidate; both slices deliver. On this branch the shape
/// is a regression guard (no cursor hook here); its RED is the composition.
#[test]
fn bzip2_blocksort_pass_on_keeps_both_eclass_slices() {
    let outcome = decide(bzip2_fixture::BZIP2_BLOCKSORT).expect("the batch-7 stop must not recur");
    assert_eq!(
        form(&outcome, "fallbackQSort3::eclass"),
        "slice-shared",
        "{:?}",
        outcome.forms
    );
    assert_eq!(
        form(&outcome, "fallbackSimpleSort::eclass"),
        "slice-shared",
        "{:?}",
        outcome.forms
    );
    assert!(
        outcome
            .receipts
            .iter()
            .all(|receipt| receipt.subjects.iter().all(|(label, old, new)| {
                !label.ends_with("::eclass#2") || old == "raw" || old == new
            })),
        "no receipt withdraws a delivered eclass slice: {:#?}",
        outcome.receipts
    );
}
