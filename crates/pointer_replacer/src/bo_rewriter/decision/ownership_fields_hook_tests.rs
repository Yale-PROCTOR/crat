//! Synthetic validator controls over compiler-provided IDs, slots and spans.
//! The grants, T1/A5, construction, lifetime and close proofs are constructed
//! premises. These tests neither install native positive bundles nor derive
//! analysis evidence, run the source fixture, or consume a model cache.

use owned::{
    OwnerId,
    emission::{Grant, GrantStatus, Kind, OwnCallFacts, ReferenceInterval, Span as EventSpan},
    export::{Digest, FactFamily, FactRef, ProgramId, RecordKey, SourceFrame},
};
use rustc_hir::{
    Expr, ExprKind,
    intravisit::{self, Visitor},
};
use rustc_middle::mir::Local;

use super::{
    super::box_facts::{BoxExprEdit, BoxShape},
    *,
};
use crate::{analyses::borrow_ownership::crate_slots::CrateSlots, utils::rustc::RustProgram};

const SOURCE: &str = r#"
#![allow(dead_code, unused_variables)]
#[repr(C)] struct Node { next: *mut Node }
unsafe extern "C" { fn free(p: *mut Node); }
unsafe fn lend_only(p: *mut Node, q: *mut Node) {}
unsafe fn consumes(p: *mut Node) { unsafe { free(p); } }
unsafe fn fixture(p: *mut Node, q: *mut Node, choose: bool) {
    unsafe { lend_only(p, q); if choose { free(p); } else { free(p); } }
}
unsafe fn raw_return(p: *mut Node, q: *mut Node) -> *mut Node {
    unsafe { lend_only(p, q); } p
}
unsafe fn consuming_boundary(p: *mut Node, q: *mut Node) {
    unsafe { lend_only(p, q); consumes(p); }
}
unsafe fn leaked(p: *mut Node, q: *mut Node) { unsafe { lend_only(p, q); } }
"#;

#[derive(Default)]
struct Calls<'tcx>(Vec<&'tcx Expr<'tcx>>);
impl<'tcx> Visitor<'tcx> for Calls<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if matches!(expr.kind, ExprKind::Call(..)) {
            self.0.push(expr);
        }
        intravisit::walk_expr(self, expr);
    }
}

fn native_site(hir: HirId) -> SiteId {
    SiteId {
        owner: OwnerId(hir.owner.def_id.local_def_index.as_u32()),
        occurrence: hir.local_id.as_u32(),
    }
}
fn synthetic_grant(key: EvidenceKey) -> Grant {
    Grant {
        key,
        kind: Kind::Owning,
        status: GrantStatus::Selected,
        transport: Some(key),
    }
}
fn synthetic_call(key: EvidenceKey) -> OwnCallFacts {
    let span = EventSpan { start: 50, end: 60 };
    OwnCallFacts {
        key,
        call: span,
        protector: span,
        whole_payload: true,
        references: vec![],
        reference_inventory: Some(key),
        helper_lowering: Some(key),
        permission: Some(key),
        transfer_cleanup: Some(key),
    }
}
fn synthetic_lend(edge: lend::EdgeKey, place: &str) -> lend::LendSite {
    let payload = lend::Payload::Sized("Node".into());
    lend::LendSite {
        edge,
        grant: synthetic_grant(edge.actual),
        place: place.into(),
        payload: payload.clone(),
        requested: lend::RequestedUse::Lend,
        formal: Ok(lend::Formal {
            edge,
            kind: Kind::Raw,
            form: lend::FormalForm::MutableRaw,
            payload,
        }),
        stable_place: Ok(edge),
        non_consuming: Ok(edge),
        retention: Ok(lend::RetentionProof {
            edge,
            outcome: lend::Retention::T1NoRetention,
        }),
        view: EventSpan { start: 10, end: 30 },
        call_span: EventSpan { start: 20, end: 30 },
        protector: EventSpan { start: 20, end: 30 },
        references: Ok(vec![]),
        reference_inventory: Ok(edge),
        peer_inventory: Ok(edge),
        permission: Ok(edge),
        continuation_inventory: Ok(edge),
        continuation: Ok(vec![]),
    }
}
fn synthetic_free(sink: EvidenceKey, owner: EvidenceKey) -> free_sites::FreeSite {
    free_sites::FreeSite {
        sink,
        owner,
        expression: "p".into(),
        optional_storage: false,
        casts: vec![free_sites::CastKind::IdentityPointer],
        exact_owner_relation: Some((owner, sink)),
        allocation_base: Some(sink),
        allocator_layout: Some(sink),
        grant: synthetic_grant(sink),
        call: synthetic_call(sink),
    }
}
fn with_fixture(name: &str, check: impl FnOnce(Bundle, OwnerId) + Send + Sync) {
    ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(SOURCE),
        |tcx| {
            let functions: Vec<_> = tcx.hir_body_owners().collect();
            let function = |name: &str| {
                *functions
                    .iter()
                    .find(|id| tcx.item_name(id.to_def_id()).as_str() == name)
                    .unwrap()
            };
            let did = function(name);
            let target = function("lend_only");
            let body = tcx.hir_body(tcx.hir_node_by_def_id(did).body_id().unwrap());
            let target_body = tcx.hir_body(tcx.hir_node_by_def_id(target).body_id().unwrap());
            let mut calls = Calls::default();
            calls.visit_body(body);
            let first = calls.0[0];
            let ExprKind::Call(callee, args) = first.kind else { unreachable!() };
            assert_eq!(
                tcx.sess.source_map().span_to_snippet(callee.span).unwrap(),
                "lend_only"
            );
            let payload = tcx
                .type_of(did)
                .skip_binder()
                .fn_sig(tcx)
                .skip_binder()
                .inputs()[0];
            let rustc_middle::ty::TyKind::RawPtr(pointee, _) = payload.kind() else {
                unreachable!()
            };
            let rustc_middle::ty::TyKind::Adt(adt, _) = pointee.kind() else { unreachable!() };
            let payload = OwnerId(adt.did().expect_local().local_def_index.as_u32());
            let program = RustProgram {
                tcx,
                functions,
                structs: vec![],
            };
            let slots = CrateSlots::build(&program);
            let local = Local::from_u32(1);
            let slot = SlotRef::Local(
                did,
                slots.fn_local_slots[&did]
                    .slot_for_local_depth(local, 0)
                    .unwrap(),
            );
            let frame = model_adapter::ModelFrame {
                source_frame: SourceFrame::L01DoublePrime,
                producer_source: "synthetic-validator-producer".into(),
                analyses_tree: "synthetic-validator-analyses".into(),
                analysis_digest: Digest([1; 32]),
                configuration_digest: Digest([2; 32]),
                substrate_digest: Digest([3; 32]),
                manifest_digest: Digest([4; 32]),
                program: ProgramId("synthetic-hook".into()),
                fingerprint: Digest([5; 32]),
                cache_root: "synthetic-cache-never-opened".into(),
                namespace: "era5a-model-cache-v1".into(),
                entry_path: "synthetic-entry".into(),
                entry_sha256: Digest([6; 32]),
                payload_sha256: Digest([7; 32]),
                export_sha256: Digest([8; 32]),
                toolchain_digest: Digest([9; 32]),
                dependency_digest: Digest([10; 32]),
                launch_digest: Digest([11; 32]),
            };
            let key = EvidenceKey {
                model: frame.entry_sha256.0,
                configuration: [12; 32],
                site: native_site(args[0].hir_id),
                generation: 9001,
            };
            let subject = model_adapter::ModelSlot {
                owner: key.site.owner,
                local: local.as_u32(),
                depth: 1,
            };
            let record = RecordKey {
                artifact: Digest([13; 32]),
                row: 0,
            };
            let inputs = model_adapter::AcceptedInputs {
                frame: Ok(frame.clone()),
                entry_accepted: Ok(true),
                model: Ok(BTreeMap::from([(subject, Kind::Owning)])),
                required_bindings: Ok(BTreeSet::from([key.site])),
                bindings: Ok(vec![model_adapter::Binding {
                    subject,
                    key,
                    generation_recipe: Ok(FactRef::new(record)),
                    transport: Ok(key),
                }]),
                records: BTreeMap::from([(record, FactFamily::GenerationRecipe)]),
                emission_configuration: Digest(key.configuration),
            };
            let pins = model_adapter::ConsumptionPins {
                role: model_adapter::ExecutionRole::CacheOnly,
                toolchain_digest: frame.toolchain_digest,
                dependency_digest: frame.dependency_digest,
                launch_digest: frame.launch_digest,
                program: frame.program.clone(),
            };
            let sites: Vec<_> = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let actual = EvidenceKey {
                        site: native_site(arg.hir_id),
                        generation: key.generation + index as u64,
                        ..key
                    };
                    let formal = EvidenceKey {
                        site: native_site(target_body.params[index].pat.hir_id),
                        ..actual
                    };
                    let edge = lend::EdgeKey {
                        call: native_site(first.hir_id),
                        target: formal.site.owner,
                        argument: index as u32,
                        actual,
                        formal,
                    };
                    synthetic_lend(
                        edge,
                        &tcx.sess.source_map().span_to_snippet(arg.span).unwrap(),
                    )
                })
                .collect();
            let mut edits: Vec<_> = args
                .iter()
                .zip(&sites)
                .map(|(arg, site)| BoxExprEdit {
                    span: arg.span,
                    replacement: format!("core::ptr::from_mut(&mut *({}))", site.place),
                    receipt: "synthetic-lend-projection",
                })
                .collect();
            let lend = LendBatch {
                inventory: lend::CallInventory {
                    call: native_site(first.hir_id),
                    targets: BTreeSet::from([sites[0].edge.target]),
                    arguments: BTreeSet::from([0, 1]),
                    disjoint_pairs: Ok(BTreeSet::from([(sites[0].edge, sites[1].edge)])),
                },
                sites,
                argument_spans: args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| (i as u32, arg.span))
                    .collect(),
            };
            let mut frees = FreeBatch {
                required: BTreeSet::new(),
                sites: vec![],
                spans: BTreeMap::new(),
            };
            for call in calls.0.iter().skip(1) {
                let ExprKind::Call(callee, _) = call.kind else { unreachable!() };
                if tcx.sess.source_map().span_to_snippet(callee.span).unwrap() != "free" {
                    continue;
                }
                let sink = EvidenceKey {
                    site: native_site(call.hir_id),
                    ..key
                };
                frees.required.insert(sink);
                frees.sites.push(synthetic_free(sink, key));
                frees.spans.insert(sink, call.span);
                edits.push(BoxExprEdit {
                    span: call.span,
                    replacement: "drop(p)".into(),
                    receipt: "synthetic-free-projection",
                });
            }
            let has_sink = !frees.required.is_empty();
            check(
                Bundle {
                    slot,
                    model_subject: subject,
                    model_site: key.site,
                    expected_frame: frame,
                    model_inputs: inputs,
                    consumption_pins: Ok(pins),
                    construction: Ok(BoxPlan {
                        shape: BoxShape::Sized,
                        optional: false,
                        expr_edits: edits,
                        delete_statements: vec![],
                        receipts: vec![],
                        fabricated_extent: false,
                        pointee_override: None,
                        inferred_binding: false,
                        overwrite_spans: vec![],
                        retained_sink: has_sink,
                        implicit_scope_close: !has_sink,
                    }),
                    construction_proof: Ok(key),
                    boundary_inventory: Ok(key),
                    lends: Ok(vec![lend]),
                    frees: Ok(frees),
                    closes: Ok(vec![]),
                    close_inventory: Ok(key),
                    source_projection: Ok(key),
                    final_interface: Ok(key),
                },
                payload,
            );
        },
    )
    .expect("synthetic hook input compiles; its source is never executed");
}

fn assert_missing(result: Result<BoxPlan, Hold>, wanted: &Missing) {
    assert!(matches!(result, Err(Hold::Missing(ref found)) if found == wanted));
}

#[test]
fn synthetic_hook_baseline_preserves_native_projection_cardinality() {
    with_fixture("fixture", |bundle, _| {
        let output = validate(&bundle).expect("constructed validator premises");
        assert_eq!(
            output.expr_edits,
            bundle.construction.as_ref().unwrap().expr_edits
        );
        assert_eq!(
            output
                .receipts
                .iter()
                .filter(|r| r.starts_with("box-free-identity"))
                .count(),
            2
        );
        assert_eq!(
            output
                .receipts
                .iter()
                .filter(|r| r.starts_with("box-lend-t1"))
                .count(),
            2
        );
        assert_eq!(
            output
                .receipts
                .iter()
                .filter(|r| r.starts_with("model-owning-grant"))
                .count(),
            1
        );
    });
}

#[test]
fn synthetic_hook_rejects_wrong_model_frame_and_foreign_lend_batch() {
    with_fixture("fixture", |bundle, _| {
        assert!(validate(&bundle).is_ok());
        let mut wrong = bundle.clone();
        wrong.expected_frame.entry_sha256 = Digest([99; 32]);
        assert!(matches!(
            validate(&wrong),
            Err(Hold::Missing(Missing {
                reason: MissingReason::Frame("model_manifest"),
                ..
            }))
        ));
        let mut foreign = bundle;
        let call = &mut foreign.lends.as_mut().unwrap()[0];
        for site in &mut call.sites {
            let mut edge = site.edge;
            edge.actual.model = [99; 32];
            edge.formal.model = [99; 32];
            *site = synthetic_lend(edge, &site.place);
        }
        call.inventory.disjoint_pairs =
            Ok(BTreeSet::from([(call.sites[0].edge, call.sites[1].edge)]));
        assert!(
            lend::plan_call(&call.inventory, &call.sites).is_ok(),
            "the foreign batch is internally consistent"
        );
        assert!(matches!(validate(&foreign), Err(Hold::Identity)));
    });
}

#[test]
fn synthetic_hook_rejects_foreign_free_frame() {
    with_fixture("fixture", |mut bundle, _| {
        assert!(validate(&bundle).is_ok());
        let free = bundle.frees.as_mut().unwrap();
        let old = free.sites[0].clone();
        let sink = EvidenceKey {
            model: [99; 32],
            ..old.sink
        };
        let owner = EvidenceKey {
            model: [99; 32],
            ..old.owner
        };
        let span = free.spans.remove(&old.sink).unwrap();
        free.required.remove(&old.sink);
        free.required.insert(sink);
        free.spans.insert(sink, span);
        free.sites[0] = synthetic_free(sink, owner);
        assert!(free_sites::plan_frees(&free.required, &free.sites).is_ok());
        assert!(matches!(validate(&bundle), Err(Hold::Identity)));
    });
}

#[test]
fn synthetic_hook_two_native_free_identities_cannot_claim_one_span() {
    with_fixture("fixture", |mut bundle, _| {
        assert!(validate(&bundle).is_ok());
        let free = bundle.frees.as_mut().unwrap();
        assert_eq!(free.required.len(), 2);
        let keys: Vec<_> = free.required.iter().copied().collect();
        let first = free.spans[&keys[0]];
        let second = free.spans.insert(keys[1], first).unwrap();
        assert_ne!(first, second);
        bundle
            .construction
            .as_mut()
            .unwrap()
            .expr_edits
            .retain(|edit| edit.span != second);
        assert!(matches!(validate(&bundle), Err(Hold::Projection)));
    });
}

#[test]
fn synthetic_hook_rejects_mixed_lend_call_spans() {
    with_fixture("fixture", |mut bundle, _| {
        assert!(validate(&bundle).is_ok());
        let site = &mut bundle.lends.as_mut().unwrap()[0].sites[1];
        site.call_span.end = 25;
        site.protector.end = 25;
        site.view.end = 25;
        site.references = Ok(vec![ReferenceInterval {
            generation: site.edge.actual.generation,
            live: EventSpan { start: 26, end: 29 },
            protected: None,
        }]);
        assert!(matches!(
            validate(&bundle),
            Err(Hold::Lend(lend::LendHold::Span))
        ));
    });
}

#[test]
fn synthetic_hook_missing_nonconsuming_pair_and_lifetime_evidence_stays_missing() {
    with_fixture("fixture", |bundle, _| {
        assert!(validate(&bundle).is_ok());
        for field in [
            "transitive-nonconsuming",
            "disjoint-pair",
            "reference-lifetime-inventory",
        ] {
            let mut missing_bundle = bundle.clone();
            let why = Missing {
                owner: EvidenceOwner::Emission,
                reason: MissingReason::Field(field),
            };
            let call = &mut missing_bundle.lends.as_mut().unwrap()[0];
            match field {
                "transitive-nonconsuming" => call.sites[0].non_consuming = Err(why.clone()),
                "disjoint-pair" => call.inventory.disjoint_pairs = Err(why.clone()),
                _ => call.sites[0].references = Err(why.clone()),
            }
            assert!(
                matches!(validate(&missing_bundle), Err(Hold::Lend(lend::LendHold::Missing(ref found))) if found == &why),
                "{field}"
            );
        }
        let mut missing_bundle = bundle;
        let why = Missing {
            owner: EvidenceOwner::Emission,
            reason: MissingReason::Field("whole-interface-lifetimes"),
        };
        missing_bundle.final_interface = Err(why.clone());
        assert_missing(validate(&missing_bundle), &why);
    });
}

#[test]
fn synthetic_hook_a_valid_lend_does_not_cover_raw_return_or_consuming_boundary() {
    for name in ["raw_return", "consuming_boundary"] {
        with_fixture(name, |mut bundle, _| {
            let call = &bundle.lends.as_ref().unwrap()[0];
            assert!(lend::plan_call(&call.inventory, &call.sites).is_ok());
            let why = Missing {
                owner: EvidenceOwner::NativeIdentity,
                reason: MissingReason::Field(name),
            };
            bundle.boundary_inventory = Err(why.clone());
            assert_missing(validate(&bundle), &why);
        });
    }
}

#[test]
fn synthetic_hook_recursive_close_requires_suppression_lowering() {
    with_fixture("leaked", |mut bundle, payload| {
        let key = bundle.construction_proof.as_ref().copied().unwrap();
        let kind = lifecycle::CloseKind::ScopeExit;
        bundle.closes = Ok(vec![CloseSite {
            key,
            kind,
            payload,
            graph: BTreeMap::from([(payload, lifecycle::DropShape::Fields(vec![payload]))]),
            graph_revision: [20; 32],
            depth: None,
            proofs: lifecycle::CloseProofs {
                event: Some((key, kind)),
                all_roots: Some(key),
                continuation: Some(key),
                no_live_reference: Some(key),
                no_protector: Some(key),
                allocator_layout: Some(key),
                target_permission: Some(key),
            },
        }]);
        assert!(matches!(validate(&bundle), Err(Hold::RecursiveSuppression)));
    });
}
