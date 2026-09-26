use super::*;

// Actual accepted traversal model, prepared only in memory. No cache disk IO.
fn with_traversal_activation_entry(
    check: impl FnOnce(
        &CompleteEntry,
        &super::super::origin_evidence::OriginEvidence,
        &super::super::portable_export::PortableExport,
    ) + Send,
) {
    with_traversal_entry(None, check);
}

fn with_traversal_entry(
    code: Option<&str>,
    check: impl FnOnce(
        &CompleteEntry,
        &super::super::origin_evidence::OriginEvidence,
        &super::super::portable_export::PortableExport,
    ) + Send,
) {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::super::{
        a5_overlap::{A5Mode, WholeProgramAttestation},
        construction,
        crate_slots::CrateSlots,
        export, model_cache,
        mutability_facts::MutFacts,
        origin_evidence::OriginEvidence,
        origins::compute_origins,
        portable_export::PortableExport,
    };
    const CODE: &str = r#"
unsafe extern "C" {fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node {left:*mut Node,right:*mut Node,value:i32}
pub unsafe fn minimum(mut node:*mut Node)->*mut Node {
    while !(*node).left.is_null(){node=(*node).left;}
    node
}
pub unsafe fn caller()->i32 {
    let root=malloc(core::mem::size_of::<Node>()) as *mut Node;
    (*root).left=0 as *mut Node;(*root).right=0 as *mut Node;(*root).value=7;
    let result=minimum(root);let value=(*result).value;
    free(root as *mut core::ffi::c_void);value
}
"#;
    ::utils::compilation::run_compiler_on_str(code.unwrap_or(CODE), move |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mutability = MutFacts::from_program(&program);
        let attestation = Some(WholeProgramAttestation::FrozenBenchmarkGraph);
        let (verified, captured) = export::with_bo_export(|| {
            construction::solve_bo_a5_config_reporting(
                &program,
                &slots,
                &origins,
                &mutability,
                A5Mode::PreciseReplay,
                attestation,
            )
            .expect("actual activated traversal model")
        });
        let inputs =
            model_cache::semantic_inputs(&program, A5Mode::PreciseReplay, attestation).unwrap();
        let key = semantic_key(&inputs).unwrap();
        model_cache::prepare(
            &program,
            &slots,
            &origins,
            &verified,
            &captured,
            A5Mode::PreciseReplay,
            attestation,
        );
        let entry = model_cache::prepared_entry(&key).unwrap_or_else(|| {
            panic!(
                "accepted in-memory traversal envelope: {:?}",
                model_cache::prepare_error()
            )
        });
        entry.validate().unwrap();
        let original: OriginEvidence = serde_json::from_value(entry.origin.clone()).unwrap();
        let portable: PortableExport = serde_json::from_value(entry.exports.clone()).unwrap();
        let accepted = original.stack_entry_final.as_ref().unwrap();
        assert_eq!(accepted.traversal_guards.len(), 1);
        assert!(
            accepted.traversal_guards[0].1,
            "actual selected traversal predicate"
        );
        let snapshot = original
            .licensing
            .as_ref()
            .unwrap()
            .iter()
            .find(|s| s.offset == accepted.snapshot_offset)
            .unwrap();
        let proof = snapshot.traversal_correspondences[0].as_ref().unwrap();
        let root = super::super::licensing::traversal_call::input_target(
            &snapshot.metadata.facts(),
            proof,
        )
        .unwrap()
        .kind_key;
        assert_eq!(entry.model.get(&root).map(String::as_str), Some("owning"));
        check(&entry, &original, &portable);
        model_cache::reset_for_test();
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn c08_projected_traversal_cache_preserves_exact_field_target() {
    use super::super::{
        licensing::{self, stack_export},
        portable_export::ExportFamily,
    };
    with_traversal_entry(
        Some(licensing::traversal_projected::CODE),
        |entry, original, portable| {
            assert_eq!(
                original.stack_entry_final.as_ref().unwrap().traversal_loans[0]
                    .target
                    .projection
                    .len(),
                2
            );
            let mut changed = original.clone();
            let accepted = changed.stack_entry_final.as_mut().unwrap();
            accepted.traversal_loans[0].target.projection.remove(0);
            let mut mirrored = portable.clone();
            mirrored
                .families
                .get_mut(&ExportFamily::RetirementFinal)
                .unwrap()
                .records[0]
                .fields
                .insert("stack_entry_acceptance".into(), accepted.stamp());
            let error = stack_export::validate(&changed, &mirrored, &entry.model)
                .expect_err("whole-parent target substitution must reject");
            assert_eq!(error, "returned-loan target/receiver differs");
        },
    );
}

#[test]
fn c07_traversal_cache_returned_loan_origin_target_and_liveness_are_required() {
    use super::super::{licensing::stack_export, portable_export::ExportFamily};
    with_traversal_activation_entry(|entry, original, portable| {
        let mut accepted_faults = Vec::new();
        for fault in [
            "omit",
            "target",
            "receiver",
            "origin",
            "live",
            "endpoints",
            "duplicate",
        ] {
            let mut changed = original.clone();
            let accepted = changed.stack_entry_final.as_mut().unwrap();
            assert_eq!(accepted.traversal_loans.len(), 1);
            match fault {
                "omit" => accepted.traversal_loans.clear(),
                "target" => accepted.traversal_loans[0].target.local += 1,
                "receiver" => accepted.traversal_loans[0].receiver.local += 1,
                "origin" => accepted.traversal_loans[0].origin.native.caller_value_flow = false,
                "live" => accepted.traversal_loans[0].live_points.clear(),
                "endpoints" => accepted.traversal_loans[0].live_endpoints.clear(),
                "duplicate" => accepted
                    .traversal_loans
                    .push(accepted.traversal_loans[0].clone()),
                _ => unreachable!(),
            }
            let mut mirrored = portable.clone();
            mirrored
                .families
                .get_mut(&ExportFamily::RetirementFinal)
                .unwrap()
                .records[0]
                .fields
                .insert("stack_entry_acceptance".into(), accepted.stamp());
            if stack_export::validate(&changed, &mirrored, &entry.model).is_ok() {
                accepted_faults.push(fault);
            }
        }
        assert!(
            accepted_faults.is_empty(),
            "returned-loan faults accepted: {accepted_faults:?}"
        );
    });
}

#[test]
fn c07_traversal_cache_rejects_joint_false_guard_with_unchanged_owning_model() {
    use super::super::{licensing::stack_export, portable_export::ExportFamily};
    with_traversal_activation_entry(|entry, original, portable| {
        let mut changed = original.clone();
        let accepted = changed.stack_entry_final.as_mut().unwrap();
        let guard = accepted.traversal_guards[0].0;
        accepted.traversal_guards[0].1 = false;
        let mut mirrored = portable.clone();
        mirrored
            .families
            .get_mut(&ExportFamily::RetirementFinal)
            .unwrap()
            .records[0]
            .fields
            .insert("stack_entry_acceptance".into(), accepted.stamp());
        let error = stack_export::validate(&changed, &mirrored, &entry.model).expect_err(
            "jointly changed copies must not replace the actual selected SSA valuation",
        );
        assert!(
            error.contains("traversal legacy argument valuation mismatch"),
            "exact false-arm rejection for {guard:?}: {error}"
        );
        let mut broken = entry.clone();
        broken.origin = serde_json::to_value(changed).unwrap();
        broken.exports = serde_json::to_value(mirrored).unwrap();
        assert!(
            broken.validate().is_err(),
            "complete entry cannot accept that same joint guard fault: {guard:?}"
        );
    });
}

#[test]
fn c07_traversal_cache_selected_export_authenticates_full_admission_surface() {
    use super::super::{licensing::stack_export, origin_evidence::SourceSite};
    with_traversal_activation_entry(|entry, original, portable| {
        let offset = original.stack_entry_final.as_ref().unwrap().snapshot_offset;
        let mut accepted_faults = Vec::new();
        for fault in [
            "raw-head",
            "argument-tail",
            "receiver-tail",
            "missing-candidate-call",
        ] {
            let mut broken = original.clone();
            let snapshot = broken
                .licensing
                .as_mut()
                .unwrap()
                .iter_mut()
                .find(|s| s.offset == offset)
                .unwrap();
            let proof = snapshot.traversal_correspondences[0]
                .as_ref()
                .unwrap()
                .clone();
            let candidate = &proof.candidate;
            let actual = snapshot
                .metadata
                .consumes
                .iter()
                .find(|c| {
                    c.point.construction == candidate.call.construction
                        && Some(c.ordinal) == proof.argument_consume
                })
                .unwrap()
                .clone();
            match fault {
                "raw-head" => {
                    let before = snapshot.metadata.raw_pointer_heads.len();
                    snapshot
                        .metadata
                        .raw_pointer_heads
                        .retain(|h| h.function != candidate.call.caller || h.local != actual.local);
                    assert_eq!(snapshot.metadata.raw_pointer_heads.len() + 1, before);
                }
                "argument-tail" | "receiver-tail" => {
                    let ordinal = if fault == "argument-tail" {
                        candidate.argument_boundary
                    } else {
                        candidate.receiver_boundary
                    };
                    let row = snapshot
                        .metadata
                        .boundaries
                        .iter_mut()
                        .find(|b| {
                            b.point.construction == candidate.call.construction
                                && b.ordinal == ordinal
                        })
                        .unwrap();
                    row.unmatched_actual_vars.push(u32::MAX);
                }
                _ => {
                    let calls = &mut snapshot
                        .metadata
                        .caller_coverage
                        .as_mut()
                        .unwrap()
                        .local_calls;
                    assert!(
                        calls.insert(super::super::licensing::caller_coverage::LocalCall {
                            site: SourceSite {
                                function: candidate.call.caller.clone(),
                                block: candidate.call.block,
                                statement: candidate.call.statement.checked_add(1).unwrap()
                            },
                            target: candidate.call.callee.clone(),
                        })
                    );
                }
            }
            // Direct validation isolates selected-export obligations; generic
            // snapshot shape validation must not mask a missing admission check.
            match stack_export::validate(&broken, portable, &entry.model) {
                Ok(()) => accepted_faults.push(fault),
                Err(error) => assert!(error.contains("traversal"), "{fault}: {error}"),
            }
        }
        assert!(
            accepted_faults.is_empty(),
            "selected traversal export accepted admission faults: {accepted_faults:?}"
        );
    });
}

#[test]
fn c07_traversal_cache_requires_complete_same_model_ownership_subset() {
    use super::super::{licensing::stack_export, portable_export::ExportFamily};
    with_traversal_activation_entry(|entry, original, portable| {
        assert!(
            !original
                .stack_entry_final
                .as_ref()
                .unwrap()
                .traversal_owns
                .is_empty()
        );
        for fault in ["missing", "duplicate", "namespace", "value"] {
            let mut wrong = original.clone();
            let accepted = wrong.stack_entry_final.as_mut().unwrap();
            match fault {
                "missing" => {
                    accepted.traversal_owns.pop();
                }
                "duplicate" => accepted.traversal_owns.push(accepted.traversal_owns[0]),
                "namespace" => accepted.traversal_owns[0].0.construction += 1,
                _ => accepted.traversal_owns[0].1 = !accepted.traversal_owns[0].1,
            }
            let mut mirrored = portable.clone();
            mirrored
                .families
                .get_mut(&ExportFamily::RetirementFinal)
                .unwrap()
                .records[0]
                .fields
                .insert("stack_entry_acceptance".into(), accepted.stamp());
            let error = stack_export::validate(&wrong, &mirrored, &entry.model)
                .expect_err("corrupt same-model ownership subset");
            assert!(error.contains("traversal"), "{fault}: {error}");
        }
    });
}

fn inputs() -> SemanticInputs {
    SemanticInputs {
        program: "fixture".into(),
        files: BTreeMap::from([("src/lib.rs".into(), "1".repeat(64))]),
        analysis: "2".repeat(64),
        toolchain: "3".repeat(64),
        dependencies: "4".repeat(64),
        configuration: "5".repeat(64),
    }
}

#[test]
fn c05_stack_export_final_applied_proof_has_exact_round_and_snapshot_namespace() {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::super::{
        a5_overlap::{A5Mode, WholeProgramAttestation},
        construction,
        crate_slots::CrateSlots,
        export, model_cache,
        mutability_facts::MutFacts,
        origin_evidence,
        origins::compute_origins,
    };
    const CODE: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: *mut H) { free((*h).ptr as *mut core::ffi::c_void); }
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 1;
    let mut h = H { ptr: owner };
    let before = *h.ptr;
    release(&mut h);
    before
}
"#;
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
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
        let program = crate::utils::rustc::RustProgram { tcx, functions, structs };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mutability = MutFacts::from_program(&program);
        let attestation = Some(WholeProgramAttestation::FrozenBenchmarkGraph);
        let (verified, captured) = export::with_bo_export(|| construction::solve_bo_a5_config_reporting(
            &program, &slots, &origins, &mutability, A5Mode::PreciseReplay, attestation,
        ).expect("attested OL07 accepted model"));
        let final_review = captured.source_retirement.as_ref().unwrap();
        assert!(!final_review.known_stack_entries.is_empty(), "the final replay actually used the stack proof");
        let inputs = model_cache::semantic_inputs(&program, A5Mode::PreciseReplay, attestation).unwrap();
        let key = semantic_key(&inputs).unwrap();
        // In-memory preparation only: no new cache directory or disk write.
        model_cache::prepare(&program, &slots, &origins, &verified, &captured, A5Mode::PreciseReplay, attestation);
        let entry = model_cache::prepared_entry(&key).unwrap_or_else(|| {
            panic!(
                "complete accepted synthetic envelope: {:?}",
                model_cache::prepare_error()
            )
        });
        let final_proof = &entry.origin["stack_entry_final"];
        assert!(final_proof.is_object(), "accepted P1 exception needs durable final-round evidence");
        assert_eq!(final_proof["retirement_round"], serde_json::json!(captured.retirement_rounds.len() - 1));
        assert_eq!(final_proof["proofs"], serde_json::to_value(&final_review.known_stack_entries).unwrap());
        let offset = final_proof["snapshot_offset"].as_u64().expect("explicit construction namespace");
        let snapshots = entry.origin["licensing"].as_array().unwrap();
        let snapshot = snapshots.iter().find(|row| row["offset"] == offset).expect("actual referenced snapshot");
        assert!(snapshot["reference_effects"]["candidates"].as_array().is_some_and(|rows| !rows.is_empty()));
        entry.validate().unwrap();
        for fault in ["missing", "snapshot", "round", "free", "caller"] {
            let mut broken = entry.clone();
            match fault {
                "missing" => broken.origin["stack_entry_final"] = serde_json::Value::Null,
                "snapshot" => broken.origin["stack_entry_final"]["snapshot_offset"] = serde_json::json!(u32::MAX),
                "round" => broken.origin["stack_entry_final"]["retirement_round"] = serde_json::json!(captured.retirement_rounds.len()),
                "free" => broken.origin["stack_entry_final"]["proofs"][0]["free"]["ordinal"] = serde_json::json!(usize::MAX),
                _ => broken.origin["stack_entry_final"]["proofs"][0]["callers"][0]["call"]["statement"] = serde_json::json!(usize::MAX),
            }
            assert!(broken.validate().is_err(), "cache accepted corrupted final stack proof: {fault}");
        }
        // Existing construction identity is not authenticated by matching
        // metadata alone; the portable accepted branch stamps its namespace.
        let previous_offset = snapshots.iter().filter_map(|row| row["offset"].as_u64()).find(|other| *other != offset).expect("A5 baseline and refined constructions");
        let mut historical_namespace = entry.clone();
        historical_namespace.origin["stack_entry_final"]["snapshot_offset"] = serde_json::json!(previous_offset);
        let error = historical_namespace.validate().unwrap_err();
        assert!(error.contains("namespace/branch stamp"), "namespace must be rejected before a structural correspondence comparison: {error}");

        // Independent completeness: removing all duplicated lists must not
        // remove the obligation of the still-selected reference/field role.
        for missing_stamp in [false, true] {
            let mut omitted = entry.clone();
            if missing_stamp { omitted.origin["stack_entry_final"] = serde_json::Value::Null; }
            else { omitted.origin["stack_entry_final"]["proofs"] = serde_json::json!([]); }
            let mut portable: super::super::portable_export::PortableExport = serde_json::from_value(omitted.exports.clone()).unwrap();
            for family in [super::super::portable_export::ExportFamily::RetirementFinal, super::super::portable_export::ExportFamily::RetirementRounds] {
                for row in &mut portable.families.get_mut(&family).unwrap().records {
                    row.fields.insert("known_stack_entries".into(), serde_json::json!([]));
                }
            }
            omitted.exports = serde_json::to_value(portable).unwrap();
            assert!(omitted.validate().is_err(), "joint omission of selected stack-entry obligation accepted; missing_stamp={missing_stamp}");
        }
        // Retaining a historical applied proof cannot populate the final list.
        let mut historical_only = captured.clone();
        historical_only.source_retirement.as_mut().unwrap().known_stack_entries.clear();
        let historical = origin_evidence::collect(&program, &slots, &origins, Some(&historical_only));
        let historical: serde_json::Value = serde_json::from_str(&historical.canonical_json()).unwrap();
        assert!(historical["stack_entry_final"].is_null(),
            "inconsistent final review cannot be replaced by historical accepted evidence");
    }).unwrap_or_else(|error| error.raise());
}
// This fixture is compiler input only. Preparation below is in memory.
#[test]
fn c04_chain_export_rejects_put_only_guard_and_joint_proof_omission() {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::super::{
        a5_overlap::{A5Mode, WholeProgramAttestation},
        construction,
        crate_slots::CrateSlots,
        export,
        licensing::stack_export,
        model_cache,
        mutability_facts::MutFacts,
        origin_evidence::OriginEvidence,
        origins::compute_origins,
        portable_export::{ExportFamily, PortableExport},
    };
    const CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Cell{ptr:*mut i32}
pub unsafe fn make()->*mut i32{let value=malloc(core::mem::size_of::<i32>()) as *mut i32;*value=5;value}
pub unsafe fn put(cell:*mut Cell,value:*mut i32){(*cell).ptr=value;}
pub unsafe fn take(cell:*mut Cell)->*mut i32{let value=(*cell).ptr;(*cell).ptr=0 as *mut i32;value}
pub unsafe fn release(cell:*mut Cell){let value=take(cell);free(value as *mut core::ffi::c_void);}
pub unsafe fn f(){let owner=make();let mut cell=Cell{ptr:0 as *mut i32};put(&mut cell,owner);release(&mut cell);}
"#;
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
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
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mutability = MutFacts::from_program(&program);
        let attestation = Some(WholeProgramAttestation::FrozenBenchmarkGraph);
        let (verified, captured) = export::with_bo_export(|| {
            construction::solve_bo_a5_config_reporting(
                &program,
                &slots,
                &origins,
                &mutability,
                A5Mode::PreciseReplay,
                attestation,
            )
            .unwrap()
        });
        let inputs =
            model_cache::semantic_inputs(&program, A5Mode::PreciseReplay, attestation).unwrap();
        let key = semantic_key(&inputs).unwrap();
        model_cache::prepare(
            &program,
            &slots,
            &origins,
            &verified,
            &captured,
            A5Mode::PreciseReplay,
            attestation,
        );
        let entry =
            model_cache::prepared_entry(&key).unwrap_or_else(|| {
                panic!(
                    "accepted complete-chain synthetic envelope: {:?}",
                    model_cache::prepare_error()
                )
            });
        entry.validate().unwrap();
        let original: OriginEvidence = serde_json::from_value(entry.origin.clone()).unwrap();
        let portable: PortableExport = serde_json::from_value(entry.exports.clone()).unwrap();
        let accepted = original.stack_entry_final.as_ref().unwrap();
        let snapshot = original
            .licensing
            .as_ref()
            .unwrap()
            .iter()
            .find(|s| s.offset == accepted.snapshot_offset)
            .unwrap();
        let chain = &snapshot.complete_chains[0];
        assert_eq!(
            entry.model.get(&chain.put.field_key).map(String::as_str),
            Some("owning")
        );
        assert_eq!(accepted.proofs.len(), 1);
        let mirror = |origin: &OriginEvidence, portable: &mut PortableExport| {
            let acceptance = origin.stack_entry_final.as_ref().unwrap();
            for family in [
                ExportFamily::RetirementFinal,
                ExportFamily::RetirementRounds,
            ] {
                for row in &mut portable.families.get_mut(&family).unwrap().records {
                    if family == ExportFamily::RetirementFinal
                        || row.fields.get("round").and_then(serde_json::Value::as_u64)
                            == Some(acceptance.retirement_round as u64)
                    {
                        row.fields.insert(
                            "known_stack_entries".into(),
                            serde_json::to_value(&acceptance.proofs).unwrap(),
                        );
                    }
                    if family == ExportFamily::RetirementFinal {
                        row.fields
                            .insert("stack_entry_acceptance".into(), acceptance.stamp());
                    }
                }
            }
        };
        // Preserve every mirrored copy so these checks authenticate the
        // required semantic identity, rather than just duplicate agreement.
        for fault in ["free", "caller", "source", "formation", "guard", "namespace", "round"] {
            let mut broken=original.clone();let a=broken.stack_entry_final.as_mut().unwrap();
            match fault {
                "free"=>a.proofs[0].free.ordinal+=1,
                "caller"=>a.proofs[0].callers[0].call.statement+=1,
                "source"=>a.proofs[0].callers[0].source.endpoint.ordinal+=1,
                "formation"=>a.proofs[0].callers[0].formation.statement=Some(usize::MAX),
                "guard"=>a.proofs[0].callers[0].original_cell_guard=Some(chain.put_guard),
                "namespace"=>a.snapshot_offset=u32::MAX,
                _=>a.retirement_round+=1,
            }
            let mut mirrored=portable.clone();mirror(&broken,&mut mirrored);
            assert!(stack_export::validate(&broken,&mirrored,&entry.model).is_err(),"corrupt exact chain evidence accepted: {fault}; free={:?}",chain.free);
        }
        for function in [&chain.put.call.callee,&chain.release.call.callee,&chain.effects.field_load.function] {
            let parameter=snapshot.metadata.boundaries.iter().find(|b|b.role==super::super::ownership_boundary::Role::Entry && b.point.function.as_ref()==Some(function) && b.argument_index==Some(0)).unwrap().formal_local.unwrap();
            let slot=format!("{function}::_{parameter}@d0");
            assert_eq!(entry.model.get(&slot).map(String::as_str),Some("ref"));
            let mut changed=entry.model.clone();changed.insert(slot.clone(),"raw".into());
            assert!(stack_export::validate(&original,&portable,&changed).is_err(),"selected chain lost required Ref parent: {slot}; put={:?}, release={:?}, free={:?}",chain.put_guard,chain.release_guard,chain.free);
        }
        let mut omitted = original.clone();
        omitted.stack_entry_final.as_mut().unwrap().proofs.clear();
        let mut omitted_portable = portable.clone();
        mirror(&omitted, &mut omitted_portable);
        let error = stack_export::validate(&omitted, &omitted_portable, &entry.model).unwrap_err();
        assert!(
            error.contains("incomplete selected stack-entry"),
            "joint omission: {error}; free={:?}",
            chain.free
        );

        // Local validator branch control, not an accepted-model claim: provide
        // consistent held role values on actual compiler metadata, then corrupt
        // only put and its duplicate stamp. Full cache validation is separate.
        let mut held_model = entry.model.clone();
        held_model.insert(chain.put.field_key.clone(), "raw".into());
        let mut held = omitted;
        for (_, value) in &mut held
            .stack_entry_final
            .as_mut()
            .unwrap()
            .original_cell_guards
        {
            *value = false;
        }
        let mut held_portable = portable.clone();
        mirror(&held, &mut held_portable);
        stack_export::validate(&held, &held_portable, &held_model).unwrap();
        let guard = held
            .stack_entry_final
            .as_mut()
            .unwrap()
            .original_cell_guards
            .iter_mut()
            .find(|(id, _)| *id == chain.put_guard)
            .unwrap();
        guard.1 = true;
        mirror(&held, &mut held_portable);
        let result = stack_export::validate(&held, &held_portable, &held_model);
        assert!(
            result.is_err(),
            "held put-only guard accepted: put={:?}, release={:?}, source={:?}, free={:?}",
            chain.put_guard,
            chain.release_guard,
            chain.source,
            chain.free
        );
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_i_cache_key_is_portable_and_every_semantic_input_is_keyed() {
    let left = logical_files(
        Path::new("/sender/tree"),
        &[(PathBuf::from("/sender/tree/src/lib.rs"), "1".repeat(64))],
    )
    .unwrap();
    let right = logical_files(
        Path::new("/receiver/other"),
        &[(PathBuf::from("/receiver/other/src/lib.rs"), "1".repeat(64))],
    )
    .unwrap();
    assert_eq!(left, right);
    assert_eq!(left.keys().cloned().collect::<Vec<_>>(), vec!["src/lib.rs"]);
    let base = inputs();
    let key = semantic_key(&base).unwrap();
    assert_eq!(key.len(), 64);
    for index in 0..6 {
        let mut changed = base.clone();
        match index {
            0 => changed.program = "other".into(),
            1 => {
                changed.files.insert("src/lib.rs".into(), "6".repeat(64));
            }
            2 => changed.analysis = "6".repeat(64),
            3 => changed.toolchain = "6".repeat(64),
            4 => changed.dependencies = "6".repeat(64),
            _ => changed.configuration = "6".repeat(64),
        }
        assert_ne!(semantic_key(&changed).unwrap(), key);
    }
}
#[test]
fn e5_i_cache_logical_paths_reject_escape_duplicate_and_missing_inputs() {
    let root = Path::new("/sender/tree");
    assert!(
        logical_files(
            root,
            &[(PathBuf::from("/sender/outside.rs"), "1".repeat(64))]
        )
        .is_err()
    );
    assert!(
        logical_files(
            root,
            &[
                (root.join("x.rs"), "1".repeat(64)),
                (root.join("x.rs"), "1".repeat(64))
            ]
        )
        .is_err()
    );
    let mut missing = inputs();
    missing.toolchain.clear();
    assert!(semantic_key(&missing).is_err());
}
#[test]
fn e5_i_cache_old_schema_and_missing_required_exports_never_validate() {
    let mut entry = CompleteEntry {
        schema: "bo-model-cache-v2".into(),
        key: "a".repeat(64),
        inputs: inputs(),
        functions: vec!["f".into()],
        universe: vec!["f::_1@d0".into()],
        model: BTreeMap::from([("f::_1@d0".into(), "raw".into())]),
        baseline: BTreeMap::from([("f::_1@d0".into(), "raw".into())]),
        receipt: "status=ok\n".into(),
        exports: serde_json::json!({}),
        origin: serde_json::json!({}),
    };
    assert!(
        entry.validate().is_err(),
        "old payload cannot be relabelled"
    );
    entry.schema = SCHEMA.into();
    assert!(
        entry.validate().is_err(),
        "all required exports must actually exist"
    );
}

#[test]
fn e5_i_actual_cache_requires_complete_payload_and_cache_only_never_falls_back() {
    use super::super::{
        execution_guard::{self, ExecutionRole},
        model_cache,
    };
    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = Directory(
        std::env::temp_dir().join(format!("era5a-cache-contract-{}", std::process::id())),
    );
    let _ = std::fs::remove_dir_all(&directory.0);
    std::fs::create_dir_all(&directory.0).unwrap();
    ::utils::compilation::run_compiler_on_str("pub unsafe fn read(p:*const i32)->i32{*p}", |tcx| {
        model_cache::reset_for_test();
        let first = model_cache::with_test_config(false, &directory.0, || {
            crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
        })
        .expect("fresh accepted model");
        let provenance = model_cache::last_solve().unwrap();
        let path = PathBuf::from(provenance.cache_entry.expect("complete fresh entry"));
        let body = std::fs::read(&path).unwrap();
        let mut document: serde_json::Value =
            serde_json::from_slice(&body).expect("new era5a complete JSON envelope");
        assert_eq!(document["schema"], SCHEMA);
        assert!(document.get("exports").is_some());
        assert!(document.get("origin").is_some());
        let mut missing_equations = document.clone();
        missing_equations["origin"]["functions"][0]["ownership"]["equations"] =
            serde_json::json!({"state": "missing", "value": "ownership-equations-not-exported"});
        let incomplete_recording: CompleteEntry =
            serde_json::from_value(missing_equations).unwrap();
        assert!(
            incomplete_recording.validate().is_err(),
            "a complete era5b cache requires the equation recorder"
        );
        let mut wrong_window = document.clone();
        let rows = wrong_window["origin"]["functions"][0]["ownership"]["consumes"]["value"].as_array_mut().unwrap();
        let row = rows.first_mut().expect("actual recorded consume attempt");
        row["base"] = serde_json::json!({"state":"present","value":{"use_start":2,"use_end":1,"def_start":3,"def_end":4}});
        let wrong_window: CompleteEntry = serde_json::from_value(wrong_window).unwrap();
        assert!(wrong_window.validate().is_err(), "invalid source occurrence windows cannot enter a complete cache");

        // Reuse this one real payload for corruption controls. In particular,
        // the read fixture's consume attempts need not have present windows.
        let mut accepted_corruptions = Vec::new();
        let mut reject_corruption = |label: &str, value: serde_json::Value| {
            let entry: CompleteEntry = serde_json::from_value(value)
                .unwrap_or_else(|error| panic!("{label}: corruption must remain deserializable: {error}"));
            if entry.validate().is_ok() {
                accepted_corruptions.push(label.to_owned());
            }
        };
        assert!(document["origin"]["licensing"].as_array().is_some_and(|rows| !rows.is_empty()),
            "T14 requires a real captured construction snapshot before corruption");
        let mut missing = document.clone();
        missing["origin"]["licensing"] = serde_json::Value::Null;
        reject_corruption("missing-licensing-snapshots", missing);
        let mut wrong_offset = document.clone();
        wrong_offset["origin"]["licensing"][0]["offset"] = serde_json::json!(1);
        reject_corruption("wrong-construction-offset", wrong_offset);
        let mut duplicate = document.clone();
        let rows = duplicate["origin"]["licensing"].as_array_mut().unwrap();
        rows.push(rows[0].clone());
        reject_corruption("duplicate-construction-snapshot", duplicate);
        let mut missing_body = document.clone();
        missing_body["origin"]["licensing"][0]["metadata"]["bodies"] = serde_json::json!([]);
        reject_corruption("missing-independent-body-rosters", missing_body);
        let mut wrong_slots = document.clone();
        wrong_slots["origin"]["licensing"][0]["metadata"]["slot_keys"] = serde_json::json!([]);
        reject_corruption("wrong-snapshot-slot-universe", wrong_slots);
        let mut wrong_route = document.clone();
        let pairs = wrong_route["origin"]["licensing"][0]["matched"]["functions"].as_array_mut().unwrap();
        assert!(!pairs.is_empty(), "the read function has a matched port graph");
        pairs.clear();
        reject_corruption("wrong-matched-function-graph", wrong_route);

        let mut uncovered = document.clone();
        let consumes = uncovered["origin"]["functions"][0]["ownership"]["consumes"]["value"].as_array_mut().unwrap();
        let mut extra = consumes.first().expect("real consume available for namespace fault").clone();
        extra["point"]["construction"] = serde_json::json!(1000);
        extra["ordinal"] = serde_json::json!(1000);
        consumes.push(extra);
        reject_corruption("uncovered-flat-consume-construction", uncovered);

        let mut unknown_function = document.clone();
        let consumes = unknown_function["origin"]["licensing"][0]["metadata"]["consumes"].as_array_mut().unwrap();
        let mut extra = consumes.first().expect("metadata consume for function-membership fault").clone();
        extra["point"]["function"] = serde_json::json!("unrecorded_function");
        extra["ordinal"] = serde_json::json!(1000);
        consumes.push(extra);
        reject_corruption("unknown-metadata-function", unknown_function);

        for (family, missing) in [
            ("boundary_substitutions", "ownership-boundary-substitutions-not-recorded"),
            ("call_arg_registrations", "call-arg-registrations-not-recorded"),
            ("terminals", "ownership-terminals-not-recorded"),
        ] {
            assert_eq!(
                document["origin"]["functions"][0]["ownership"][family]["state"],
                "present",
                "the real producer must record {family} before its availability can be corrupted"
            );
            let mut missing_family = document.clone();
            missing_family["origin"]["functions"][0]["ownership"][family] =
                serde_json::json!({"state":"missing","value":missing});
            reject_corruption(&format!("missing-{family}"), missing_family);
        }

        let boundary_rows = document["origin"]["functions"][0]["ownership"]
            ["boundary_substitutions"]["value"].as_array().unwrap();
        let entry_index = boundary_rows.iter().position(|row| {
            row["role"] == "entry"
                && row["actual"]["state"] == "present"
                && row["actual"]["value"]["kind"] == "single"
                && row["matched"].as_array().is_some_and(|pairs| {
                    pairs.first().is_some_and(|pair| pair["actual"]["kind"] == "single")
                })
        }).expect("the pointer parameter has an actual recorded entry matcher pair");

        let mut duplicate_boundary = document.clone();
        let rows = duplicate_boundary["origin"]["functions"][0]["ownership"]
            ["boundary_substitutions"]["value"].as_array_mut().unwrap();
        let duplicate = rows[entry_index].clone();
        rows.push(duplicate);
        reject_corruption("duplicate-boundary-id", duplicate_boundary);

        let mut bad_match = document.clone();
        bad_match["origin"]["functions"][0]["ownership"]["boundary_substitutions"]
            ["value"][entry_index]["matched"][0]["actual"]["var"] =
            serde_json::json!(u32::MAX);
        reject_corruption("entry-match-outside-actual-window", bad_match);

        let mut bad_tail = document.clone();
        bad_tail["origin"]["functions"][0]["ownership"]["boundary_substitutions"]
            ["value"][entry_index]["unmatched_actual_vars"]
            .as_array_mut().unwrap().push(serde_json::json!(u32::MAX));
        reject_corruption("fabricated-unmatched-entry-tail", bad_tail);

        let terminal_rows = document["origin"]["functions"][0]["ownership"]
            ["terminals"]["value"].as_array().unwrap();
        let terminal_index = terminal_rows.iter().position(|row| row["role"] == "return-output")
            .expect("the real function has a recorded return terminal, even for a scalar result");
        let mut duplicate_terminal = document.clone();
        let rows = duplicate_terminal["origin"]["functions"][0]["ownership"]
            ["terminals"]["value"].as_array_mut().unwrap();
        let duplicate = rows[terminal_index].clone();
        rows.push(duplicate);
        reject_corruption("duplicate-terminal-id", duplicate_terminal);

        let mut bad_terminal_role = document.clone();
        bad_terminal_role["origin"]["functions"][0]["ownership"]["terminals"]
            ["value"][terminal_index]["role"] = serde_json::json!("invented-terminal-role");
        reject_corruption("invalid-terminal-role", bad_terminal_role);
        let entry=&boundary_rows[entry_index];
        let pair=&entry["matched"][0];
        let mut lost_equation=document.clone();
        let equations=lost_equation["origin"]["functions"][0]["ownership"]["equations"]["value"].as_array_mut().unwrap();
        let index=equations.iter().position(|eq|eq["point"]==entry["point"] && eq["operation"]=="equal" && eq["variables"]==serde_json::json!([pair["actual"]["var"],pair["formal"]["var"]])).expect("actual entry equality");
        equations.remove(index);
        reject_corruption("missing-witnessed-entry-equation",lost_equation);
        let mut wrong_terminal=document.clone();
        let terminals=wrong_terminal["origin"]["functions"][0]["ownership"]["terminals"]["value"].as_array_mut().unwrap();
        let parameter=terminals.iter_mut().find(|row|row["role"]=="parameter-output" && row["values"]["state"]=="present" && row["values"]["value"].as_array().is_some_and(|v|!v.is_empty())).expect("pointer parameter terminal");
        parameter["values"]["value"][0]["var"]=serde_json::json!(u32::MAX);
        reject_corruption("terminal-output-var-mismatch",wrong_terminal);
        assert!(
            accepted_corruptions.is_empty(),
            "complete cache accepted malformed boundary/terminal payloads: {accepted_corruptions:?}"
        );

        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let loaded = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        })
        .expect("cache-only complete readback");
        assert_eq!(loaded, first);
        assert_eq!(execution_guard::model_entries(), before);
        assert_eq!(model_cache::last_solve().unwrap().source, "cache");
        document.as_object_mut().unwrap().remove("exports");
        let incomplete = serde_json::to_vec(&document).unwrap();
        std::fs::write(&path, &incomplete).unwrap();
        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let refused = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        });
        assert!(
            refused.is_err(),
            "missing required export must refuse without a solver fallback"
        );
        assert_eq!(execution_guard::model_entries(), before);
        assert_eq!(
            std::fs::read(&path).unwrap(),
            incomplete,
            "refusal must not overwrite the entry"
        );
        // Coordinated deletion must not make two incomplete lists validate
        // each other while losing the compiler's actual function evidence.
        let mut missing_functions: serde_json::Value = serde_json::from_slice(&body).unwrap();
        missing_functions["functions"] = serde_json::json!([]);
        missing_functions["origin"]["functions"] = serde_json::json!([]);
        std::fs::write(&path, serde_json::to_vec(&missing_functions).unwrap()).unwrap();
        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let refused = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        });
        assert!(
            refused.is_err(),
            "actual compiler function evidence cannot be co-deleted"
        );
        assert_eq!(execution_guard::model_entries(), before);
        model_cache::reset_for_test();
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_i_cache_publish_is_atomic_idempotent_and_never_overwrites() {
    use super::super::portable_export::{
        self, CaptureAvailability, PortableExport, PortableFamily, ScopeGap,
    };
    // Integrity-only synthetic empty model; no claim that a model was solved.
    let mut exports = PortableExport {
        schema: portable_export::SCHEMA.into(),
        licensing_deferred: true,
        identities: Default::default(),
        scope_gaps: [
            ScopeGap::OwnershipOccurrenceConstructionNotRecorded,
            ScopeGap::OwnershipValuesAreLatestSuppliedValuation,
        ]
        .into_iter()
        .collect(),
        families: portable_export::REQUIRED_FAMILIES
            .into_iter()
            .map(|f| {
                (
                    f,
                    PortableFamily {
                        availability: CaptureAvailability::Captured,
                        source_rows: 0,
                        records: vec![],
                    },
                )
            })
            .collect(),
        diagnostics: vec![],
    };
    use portable_export::{ExportFamily, PortableRecord};
    for (family, value) in [
        (
            ExportFamily::RetirementFinal,
            serde_json::json!({"conflicts":[],"unresolved":[],"coverage":[],"ordinary_error_points":0,"terminal":[]}),
        ),
        (
            ExportFamily::DemandEvidence,
            serde_json::from_str(
                &super::super::demand_evidence::DemandEvidence::default()
                    .canonical_json()
                    .unwrap(),
            )
            .unwrap(),
        ),
        (
            ExportFamily::ProofEvidence,
            serde_json::to_value(super::super::proof_evidence::ProofEvidence::default()).unwrap(),
        ),
    ] {
        let key = format!("{family:?}/{{}}");
        exports.identities.insert(key.clone());
        let row = PortableRecord {
            key,
            references: vec![],
            fields: value
                .as_object()
                .unwrap()
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        };
        exports.families.insert(
            family,
            PortableFamily {
                availability: CaptureAvailability::Captured,
                source_rows: 1,
                records: vec![row],
            },
        );
    }
    let inputs = inputs();
    let key = semantic_key(&inputs).unwrap();
    let entry = CompleteEntry {
        schema: SCHEMA.into(),
        key,
        inputs,
        functions: vec![],
        universe: vec![],
        model: BTreeMap::new(),
        baseline: BTreeMap::new(),
        receipt: "status=ok\ndata=true\n".into(),
        exports: serde_json::to_value(exports).unwrap(),
        origin: serde_json::json!({"functions":[], "licensing":[]}),
    };
    entry
        .validate()
        .expect("well-formed synthetic integrity envelope");
    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = Directory(
        std::env::temp_dir().join(format!("era5a-atomic-contract-{}", std::process::id())),
    );
    let _ = std::fs::remove_dir_all(&directory.0);
    let path = publish(&directory.0, &entry).expect("atomic complete publication");
    let original = std::fs::read(&path).unwrap();
    assert_eq!(
        publish(&directory.0, &entry).unwrap(),
        path,
        "identical repeated publication is idempotent"
    );
    let mut collision = entry.clone();
    collision.receipt.push_str("different-receipt=true\n");
    assert!(
        publish(&directory.0, &collision).is_err(),
        "same semantic address cannot overwrite a different completed body"
    );
    assert_eq!(std::fs::read(&path).unwrap(), original);
    let decoded: CompleteEntry = serde_json::from_slice(&original).unwrap();
    decoded.validate().unwrap();
    assert_eq!(decoded, entry);

    // R281 W01/W06/W09/W10: exercise the new bounded transport against this
    // independently constructed frozen CompleteEntry and its exact encodings.
    let exports_path = directory.0.join("exports.json");
    std::fs::write(&exports_path, serde_json::to_vec(&entry.exports).unwrap()).unwrap();
    let metadata = stream::Metadata::try_from(entry.clone()).unwrap();
    let staged = stage_streamed(&directory.0, metadata.clone(), &exports_path).unwrap();
    assert_eq!(
        std::fs::read(&staged.path).unwrap(),
        entry.canonical_json().unwrap()
    );
    let hashes = staged.hashes.as_ref().unwrap();
    use sha2::Digest;
    let payload = serde_json::to_vec(&(&entry.model, &entry.baseline, &entry.receipt)).unwrap();
    let exports = serde_json::to_vec(&(&entry.exports, &entry.origin)).unwrap();
    assert_eq!(
        hashes.payload,
        format!("{:x}", sha2::Sha256::digest(&payload))
    );
    assert_eq!(
        hashes.exports,
        format!("{:x}", sha2::Sha256::digest(&exports))
    );
    let readback = validate_file(&staged.path).unwrap();
    let read_hashes = readback.canonical_file_hashes(&staged.path).unwrap();
    assert_eq!(read_hashes.entry, hashes.entry);
    assert_eq!(read_hashes.payload, hashes.payload);
    assert_eq!(read_hashes.exports, hashes.exports);
    assert_eq!(publish_streamed(&directory.0, &staged).unwrap(), path);
    let stream_root = directory.0.join("stream-publication");
    let stream_path = publish_streamed(&stream_root, &staged).unwrap();
    assert!(equal_files(&path, &stream_path).unwrap());
    assert_eq!(
        publish_streamed(&stream_root, &staged).unwrap(),
        stream_path
    );
    let mut collision_metadata = metadata.clone();
    collision_metadata
        .receipt
        .push_str("different-receipt=true\n");
    let different =
        stage_streamed(&directory.0, collision_metadata.clone(), &exports_path).unwrap();
    assert!(publish_streamed(&stream_root, &different).is_err());
    // W09: a start barrier exercises concurrent contenders, but does not
    // claim to force both through the internal pre-link check simultaneously.
    let identical = stage_streamed(&directory.0, metadata.clone(), &exports_path).unwrap();
    let same_root = directory.0.join("concurrent-same");
    let start = std::sync::Barrier::new(2);
    let (left, right) = std::thread::scope(|scope| {
        let left = scope.spawn(|| {
            start.wait();
            publish_streamed(&same_root, &staged)
        });
        let right = scope.spawn(|| {
            start.wait();
            publish_streamed(&same_root, &identical)
        });
        (left.join().unwrap(), right.join().unwrap())
    });
    let same_path = left.expect("first same-body contender");
    assert_eq!(right.expect("second same-body contender"), same_path);
    assert!(equal_files(&same_path, &staged.path).unwrap());
    assert_eq!(std::fs::read_dir(&same_root).unwrap().count(), 1);

    let different_root = directory.0.join("concurrent-different");
    let start = std::sync::Barrier::new(2);
    let (left, right) = std::thread::scope(|scope| {
        let left = scope.spawn(|| {
            start.wait();
            publish_streamed(&different_root, &staged)
        });
        let right = scope.spawn(|| {
            start.wait();
            publish_streamed(&different_root, &different)
        });
        (left.join().unwrap(), right.join().unwrap())
    });
    let (winner, expected, loser) = match (left, right) {
        (Ok(path), Err(_)) => (path, &staged, &different),
        (Err(_), Ok(path)) => (path, &different, &staged),
        other => panic!("different-body contenders need exactly one winner: {other:?}"),
    };
    assert!(equal_files(&winner, &expected.path).unwrap());
    assert!(publish_streamed(&different_root, loser).is_err());
    assert!(
        equal_files(&winner, &expected.path).unwrap(),
        "loser cannot overwrite winner"
    );
    assert_eq!(std::fs::read_dir(&different_root).unwrap().count(), 1);

    // Staged corruption is rejected before a new destination is linked.
    let broken = stage_streamed(&directory.0, metadata.clone(), &exports_path).unwrap();
    std::fs::write(&broken.path, b"{").unwrap();
    let refused_root = directory.0.join("refused-publication");
    assert!(publish_streamed(&refused_root, &broken).is_err());
    assert!(!refused_root.join(format!("{}.json", entry.key)).exists());

    // Separate semantic readback from redundant hash protection. A corrupted
    // but self-consistently hashed stage must still fail full family validation.
    let mut malformed = entry.clone();
    malformed.exports["families"]["loans"]["source_rows"] = serde_json::json!(1);
    let invalid_exports = directory.0.join("invalid-exports.json");
    std::fs::write(
        &invalid_exports,
        serde_json::to_vec(&malformed.exports).unwrap(),
    )
    .unwrap();
    let stage_error = stage_streamed(&directory.0, metadata.clone(), &invalid_exports)
        .err()
        .expect("W06 staging must validate complete families");
    assert!(
        stage_error.contains("incomplete portable family"),
        "{stage_error}"
    );
    let mut rehashed = stage_streamed(&directory.0, metadata.clone(), &exports_path).unwrap();
    std::fs::write(&rehashed.path, serde_json::to_vec(&malformed).unwrap()).unwrap();
    rehashed.hashes.as_mut().unwrap().entry = file_sha256(&rehashed.path).unwrap();
    let readback_root = directory.0.join("semantic-readback-refused");
    let publish_error = publish_streamed(&readback_root, &rehashed)
        .err()
        .expect("W06 publication must validate despite a matching body hash");
    assert!(
        publish_error.contains("incomplete portable family"),
        "{publish_error}"
    );
    assert!(!readback_root.join(format!("{}.json", entry.key)).exists());
    let owned_path = staged.path.clone();
    drop(staged);
    assert!(!owned_path.exists());
    assert_eq!(std::fs::read(&stream_path).unwrap(), original);
}

#[test]
fn e5_i_actual_cache_transports_between_distinct_source_roots_without_solving() {
    use super::super::{
        execution_guard::{self, ExecutionRole},
        model_cache,
    };
    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let root =
        Directory(std::env::temp_dir().join(format!("era5a-cross-root-{}", std::process::id())));
    let _ = std::fs::remove_dir_all(&root.0);
    let source =
        "pub struct Holder{pub items:[*mut u8;2]} pub unsafe fn read(p:*const i32)->i32{*p}";
    let left = root.0.join("sender/src/lib.rs");
    let right = root.0.join("receiver/src/lib.rs");
    for path in [&left, &right] {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, source).unwrap();
    }
    let cache = root.0.join("cache");
    let first = ::utils::compilation::run_compiler_on_path(&left, |tcx| {
        model_cache::reset_for_test();
        let receipt = model_cache::with_test_config(false, &cache, || {
            crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
        })
        .expect("sender model");
        let provenance = model_cache::last_solve().unwrap();
        assert!(
            provenance.cache_entry.is_some(),
            "sender complete entry: {:?}",
            model_cache::prepare_error()
        );
        (receipt, provenance.fingerprint, provenance.model_sha256)
    })
    .unwrap_or_else(|error| error.raise());
    ::utils::compilation::run_compiler_on_path(&right, |tcx| {
        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let receipt = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &cache, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        })
        .expect("receiver cache-only readback");
        let provenance = model_cache::last_solve().unwrap();
        assert_eq!(receipt, first.0);
        assert_eq!(provenance.fingerprint, first.1);
        assert_eq!(provenance.model_sha256, first.2);
        assert_eq!(provenance.source, "cache");
        assert_eq!(execution_guard::model_entries(), before);
        model_cache::reset_for_test();
    })
    .unwrap_or_else(|error| error.raise());
}
