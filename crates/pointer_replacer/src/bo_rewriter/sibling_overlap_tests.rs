//! R233 controls use actual fixture models; no corpus or cache write entry.

use super::decision::{
    SubjectKind,
    a5_site_proof::A5SiteProofVerdict,
    seam::Form,
    sibling_overlap::{
        self, LocalPostCallEvidence, SiblingAccess, SiblingInventory, SiblingPotential,
        SourceBridgeCoverage, SourceBridgeEvidence, TerminalSiteState,
    },
};

const PARAMETER_CASE: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
        update((*holder).data, src);\n\
    }\n\
    pub unsafe fn entry() {\n\
        let mut value = 1;\n\
        let holder = Holder { data: &mut value };\n\
        caller(&holder, &value);\n\
    }\n";

fn potentials(input: &str, source_label: &str) -> Vec<SiblingPotential> {
    inventory(input, source_label).potentials
}

fn inventory(input: &str, source_label: &str) -> SiblingInventory {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("R233 real fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("R233 fixture solve receipt ({source_label}): {solve:#?}");
        assert!(solve.is_some(), "fixture evidence must carry its actual solve receipt");
        let subject = ctx.subjects.iter().find(|subject| subject.label == source_label)
            .expect("R233 source must be a real collected subject");
        let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)))
            .copied();
        assert_eq!(kind, Some(super::SlotKind::Ref),
            "R233 source premise must be frozen model-Ref: {source_label}");
        let inventory = sibling_overlap::collect_inventory(tcx, &ctx);
        if input == local_case("0") {
            print_dead_local_mir(tcx, &ctx, source_site(&inventory.potentials, source_label));
        }
        inventory
    }).expect("R233 fixture compiles")
}

fn print_dead_local_mir(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    ctx: &super::DecideCtx,
    source: &SiblingPotential,
) {
    use rustc_middle::mir::{BasicBlock, Location, Rvalue, StatementKind};
    use rustc_mir_dataflow::Analysis;

    use crate::analyses::{borrow_ownership::slots::SlotOwner, liveness::MaybeLiveLocals};

    let body = tcx
        .mir_drops_elaborated_and_const_checked(source.caller)
        .borrow();
    let flow = &ctx
        .analysis
        .origins
        .as_ref()
        .and_then(|origins| origins.try_native_flows())
        .and_then(|flows| flows.get(&source.caller))
        .expect("existing dead-local flow export")
        .body;
    let edges = flow.depth0_value_flows();
    let mut component = rustc_hash::FxHashSet::from_iter([SlotOwner::Local(
        source
            .source
            .declared()
            .expect("banked declared source")
            .local,
    )]);
    let mut frontier = vec![SlotOwner::Local(
        source
            .source
            .declared()
            .expect("banked declared source")
            .local,
    )];
    while let Some(owner) = frontier.pop() {
        for &(from, to) in &edges {
            let peer = if from == owner {
                Some(to)
            } else if to == owner {
                Some(from)
            } else {
                None
            };
            if let Some(peer) = peer
                && component.insert(peer)
            {
                frontier.push(peer);
            }
        }
    }
    let locals = component
        .iter()
        .filter_map(|owner| match owner {
            SlotOwner::Local(local) => Some(*local),
            SlotOwner::Field(_) => None,
        })
        .collect::<std::collections::BTreeSet<_>>();
    let call = Location {
        block: BasicBlock::from_u32(source.site.block),
        statement_index: source.site.statement_index as usize,
    };
    let mut cursor = MaybeLiveLocals
        .iterate_to_fixpoint(tcx, &body, None)
        .into_results_cursor(&body);
    cursor.seek_before_primary_effect(call);
    println!(
        "R233 dead-local READ: source={:?}, call={call:?}, component={component:?}",
        source
            .source
            .declared()
            .expect("banked declared source")
            .local
    );
    for local in &locals {
        println!(
            "R233 dead-local READ local={local:?}, type={:?}, live_on_call_exit={}",
            body.local_decls[*local].ty,
            cursor.get().contains(*local)
        );
    }
    for &(from, to) in &edges {
        if component.contains(&from) && component.contains(&to) {
            println!("R233 dead-local READ exported edge={from:?}->{to:?}");
        }
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (destination, rvalue) = &**assignment;
            let place = match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                    if locals.contains(&place.local) =>
                {
                    place
                }
                _ => continue,
            };
            let exported_flow = destination.as_local().is_some_and(|local| {
                edges.contains(&(SlotOwner::Local(place.local), SlotOwner::Local(local)))
            });
            println!(
                "R233 dead-local READ matched guard at {:?}: {destination:?} = {rvalue:?}; base_type={:?}; place_type={:?}; destination_type={:?}; exported_base_to_destination={exported_flow}",
                Location {
                    block,
                    statement_index
                },
                body.local_decls[place.local].ty,
                place.ty(&*body, tcx).ty,
                destination.ty(&*body, tcx).ty
            );
        }
    }
}

fn source_site<'a>(potentials: &'a [SiblingPotential], label: &str) -> &'a SiblingPotential {
    let sites = potentials
        .iter()
        .filter(|potential| {
            potential.source.label() == label && potential.site.callee.symbol == "update"
        })
        .collect::<Vec<_>>();
    assert_eq!(
        sites.len(),
        1,
        "one exact source-to-update site: {potentials:#?}"
    );
    sites[0]
}

fn raw_terminal(_: &SiblingPotential) -> TerminalSiteState {
    TerminalSiteState {
        source_form: Form::Ref { mutable: false },
        target_form: Form::Raw,
        source_delivered: true,
    }
}

#[test]
fn sibling_r233_parameter_pending_keeps_paired_frozen_evidence() {
    let potentials = potentials(PARAMETER_CASE, "caller::src");
    let source = source_site(&potentials, "caller::src");
    assert!(matches!(
        source
            .source
            .declared()
            .expect("banked declared source")
            .kind,
        SubjectKind::Param { hir_index: 1 }
    ));
    assert_eq!(
        source.local_post_call,
        LocalPostCallEvidence::ParameterProtected
    );
    let sibling = source
        .siblings
        .iter()
        .find(|sibling| sibling.argument_index == 0)
        .expect("the writing destination is the exact sibling");
    assert_ne!(sibling.proof.verdict, A5SiteProofVerdict::Clear);
    assert!(
        matches!(
            sibling.access,
            SiblingAccess::Foster {
                mutable: true,
                defaulted: false,
                ..
            }
        ),
        "the sibling write must come from the actual Foster fact: {sibling:?}"
    );
    let pending = sibling_overlap::select_pending(std::slice::from_ref(source), raw_terminal);
    assert_eq!(
        pending.len(),
        1,
        "explicitly held/raw terminal callee keeps a pending source receipt"
    );
    assert_eq!(pending[0].reason, sibling_overlap::PENDING_REASON);
    assert_eq!(pending[0].tier, "T2-pending");
    assert_eq!(
        pending[0].waiver,
        "c-aliasing-semantics-at-unsafe-bridges/v2-pending"
    );
    assert_eq!(pending[0].potential.site, source.site);
    assert!(!pending[0].site_id().is_empty());
}

#[test]
fn sibling_r233_field_loaded_raw_pointer_is_not_a_holder_pointee_bridge() {
    let potentials = potentials(PARAMETER_CASE, "caller::src");
    let source = source_site(&potentials, "caller::src");
    assert_eq!(
        source.site.argument_index, 1,
        "the direct source is the bridged argument"
    );
    assert!(
        !potentials.iter().any(|potential| {
            potential.source.label() == "caller::holder" && potential.site.callee.symbol == "update"
        }),
        "the Holder root does not denote the field-loaded raw pointer's pointee: {potentials:#?}"
    );
}

#[test]
fn sibling_r233_terminal_safe_target_or_reverted_source_has_no_pending_receipt() {
    let potentials = potentials(PARAMETER_CASE, "caller::src");
    let source = source_site(&potentials, "caller::src");
    for terminal in [
        TerminalSiteState {
            target_form: Form::Ref { mutable: false },
            ..raw_terminal(source)
        },
        TerminalSiteState {
            source_delivered: false,
            ..raw_terminal(source)
        },
        TerminalSiteState {
            source_form: Form::Raw,
            ..raw_terminal(source)
        },
    ] {
        assert!(
            sibling_overlap::select_pending(std::slice::from_ref(source), |_| terminal).is_empty()
        );
    }
}

fn local_case(after: &str) -> String {
    format!(
        "#![allow(dead_code, unused_unsafe)]\n\
        pub struct Holder {{ data: *mut i32 }}\n\
        pub unsafe fn update(dst: *mut i32, src: *const i32) {{ *dst = *src + 1; }}\n\
        pub unsafe fn caller() -> i32 {{\n\
            let mut value = 1;\n\
            let holder = Holder {{ data: &mut value }};\n\
            let src: *const i32 = &value;\n\
            update(holder.data, src);\n\
            {after}\n\
        }}\n"
    )
}

#[test]
fn sibling_r233_local_without_post_call_use_requires_complete_dead_evidence() {
    let potentials = potentials(&local_case("0"), "caller::src");
    let source = source_site(&potentials, "caller::src");
    assert!(matches!(
        source
            .source
            .declared()
            .expect("banked declared source")
            .kind,
        SubjectKind::Local
    ));
    assert!(
        matches!(&source.local_post_call,
        LocalPostCallEvidence::DeadUnprotected { checked_locals } if checked_locals.contains(&source.source.declared().expect("banked declared source").local)),
        "a genuine local exception has explicit, complete MIR/protector evidence: {source:?}"
    );
    assert!(sibling_overlap::select_pending(std::slice::from_ref(source), raw_terminal).is_empty());
}

#[test]
fn sibling_r233_live_local_with_an_exported_clear_pair_has_no_pending_waiver() {
    let potentials = potentials(&local_case("*src"), "caller::src");
    let source = source_site(&potentials, "caller::src");
    assert!(
        matches!(&source.local_post_call, LocalPostCallEvidence::Live { locals }
        if locals.contains(&source.source.declared().expect("banked declared source").local)),
        "actual post-call read remains live: {source:?}"
    );
    assert!(
        source
            .siblings
            .iter()
            .any(|sibling| sibling.proof.verdict == A5SiteProofVerdict::Clear
                && matches!(
                    sibling.access,
                    SiblingAccess::Foster {
                        mutable: true,
                        defaulted: false,
                        ..
                    }
                )),
        "the sealed gate observed an actual clear writing pair independently of liveness: {source:#?}"
    );
    assert!(
        sibling_overlap::select_pending(std::slice::from_ref(source), raw_terminal).is_empty(),
        "a live local does not override its actual exported disjointness: {source:#?}"
    );
}

#[test]
fn sibling_r233_local_copy_of_a_parameter_keeps_the_parameter_protector() {
    let input = PARAMETER_CASE.replace(
        "update((*holder).data, src);",
        "let local: *const i32 = src; update((*holder).data, local);",
    );
    let potentials = potentials(&input, "caller::local");
    let source = source_site(&potentials, "caller::local");
    assert!(matches!(
        source
            .source
            .declared()
            .expect("banked declared source")
            .kind,
        SubjectKind::Local
    ));
    assert!(
        matches!(&source.local_post_call, LocalPostCallEvidence::ParameterOrigin { parameters }
        if parameters.contains(&2)),
        "the dead local still aliases parameter MIR _2: {source:?}"
    );
    assert_eq!(
        sibling_overlap::select_pending(std::slice::from_ref(source), raw_terminal).len(),
        1
    );
}

#[test]
fn sibling_r233_cleared_writing_pair_has_no_pending_waiver() {
    let potentials = potentials(PARAMETER_CASE, "caller::src");
    let mut source = source_site(&potentials, "caller::src").clone();
    assert!(
        source.siblings.iter().any(|sibling| matches!(
            sibling.access,
            SiblingAccess::Foster {
                mutable: true,
                defaulted: false,
                ..
            }
        )),
        "the control preserves a real writing sibling"
    );
    assert_eq!(
        sibling_overlap::select_pending(std::slice::from_ref(&source), raw_terminal).len(),
        1,
        "the unchanged risky pair must first mint its pending receipt"
    );
    // Controlled selector input: only the typed pair verdict changes. This
    // does not claim that the fixture's actual A5 audit proved disjointness.
    for sibling in &mut source.siblings {
        sibling.proof.verdict = A5SiteProofVerdict::Clear;
        sibling.proof.reason = "selector-control-proven-disjoint";
    }
    assert!(
        sibling_overlap::select_pending(std::slice::from_ref(&source), raw_terminal).is_empty()
    );
}

#[test]
fn sibling_r233_sealed_read_only_sibling_does_not_mint_pending_write_waiver() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        extern \"C\" { fn strcmp(a: *const i8, b: *const i8) -> i32; }\n\
        pub unsafe fn caller(src: *const i8, peer: *const i8) -> i32 {\n\
            strcmp(src, peer)\n\
        }\n";
    let potentials = potentials(input, "caller::src");
    let sites = potentials
        .iter()
        .filter(|potential| {
            potential.source.label() == "caller::src" && potential.site.callee.symbol == "strcmp"
        })
        .collect::<Vec<_>>();
    assert_eq!(
        sites.len(),
        1,
        "one real source-to-strcmp site: {potentials:#?}"
    );
    let source = sites[0];
    assert_eq!(source.siblings.len(), 1);
    assert!(
        matches!(
            source.siblings[0].access,
            SiblingAccess::Contract {
                access: super::decision::raw_boundary_contracts::PointeeAccess::Read,
                ..
            }
        ),
        "the sibling access comes from the actual sealed contract: {source:?}"
    );
    let terminal = TerminalSiteState {
        source_form: Form::Ref { mutable: true },
        ..raw_terminal(source)
    };
    assert!(
        sibling_overlap::select_pending(std::slice::from_ref(source), |_| terminal).is_empty(),
        "a read-only sibling cannot mint the sibling-write waiver; this is not a soundness certificate"
    );
}

fn covered<'a>(
    inventory: &'a SiblingInventory,
    label: &str,
    callee: &str,
    index: usize,
) -> &'a SourceBridgeCoverage {
    let records = inventory
        .coverage
        .iter()
        .filter(|record| {
            record.potential.source.label() == label
                && record.potential.site.callee.symbol == callee
                && record.potential.site.argument_index == index
        })
        .collect::<Vec<_>>();
    assert_eq!(
        records.len(),
        1,
        "one exact custody classification for {label} -> {callee} arg {index}: {inventory:#?}"
    );
    records[0]
}

#[test]
fn sibling_r233_coverage_reborrow_of_the_referent_is_an_actual_bridge() {
    let input = PARAMETER_CASE.replace(
        "update((*holder).data, src);",
        "update((*holder).data, &*src);",
    );
    let inventory = inventory(&input, "caller::src");
    let record = covered(&inventory, "caller::src", "update", 1);
    assert!(
        matches!(
            record.evidence,
            SourceBridgeEvidence::ProjectedReferent { .. }
        ),
        "{record:?}"
    );
    assert!(
        inventory
            .potentials
            .iter()
            .any(|potential| potential.site == record.potential.site),
        "the actual reborrow must enter potential sibling-risk evaluation"
    );
}

#[test]
fn sibling_r233_coverage_projected_scalar_and_loaded_pointer_stay_distinct() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        pub struct Holder { data: *mut i32, scalar: i32 }\n\
        pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
        pub unsafe fn caller(holder: *const Holder) {\n\
            update((*holder).data, &(*holder).scalar);\n\
        }\n\
        pub unsafe fn entry() {\n\
            let mut value = 1; let holder = Holder { data: &mut value, scalar: 2 }; caller(&holder);\n\
        }\n";
    let inventory = inventory(input, "caller::holder");
    let projected = covered(&inventory, "caller::holder", "update", 1);
    assert!(
        matches!(
            projected.evidence,
            SourceBridgeEvidence::ProjectedReferent { .. }
        ),
        "{projected:?}"
    );
    let loaded = covered(&inventory, "caller::holder", "update", 0);
    assert_eq!(loaded.evidence, SourceBridgeEvidence::RawFieldValue);
    assert!(
        !inventory
            .potentials
            .iter()
            .any(|potential| potential.site == loaded.potential.site),
        "loading a stored pointer does not bridge the aggregate's reference pointee"
    );
}

#[test]
fn sibling_r233_coverage_slice_offset_keeps_its_exact_view_identity() {
    let input = PARAMETER_CASE.replace(
        "update((*holder).data, src);",
        "let _value = *src.offset(1); update((*holder).data, src.offset(0));",
    );
    let inventory = inventory(&input, "caller::src");
    let record = covered(&inventory, "caller::src", "update", 1);
    assert!(
        matches!(record.evidence, SourceBridgeEvidence::TypedView { .. }),
        "{record:?}"
    );
    assert!(
        inventory
            .potentials
            .iter()
            .any(|potential| potential.site == record.potential.site),
        "an exact typed pointer view must not disappear because it is classified raw-expr"
    );
}

#[test]
fn sibling_r233_coverage_pointer_binding_storage_is_not_its_referent() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        pub unsafe fn update_slot(dst: *mut *const i32, src: *const i32) { *dst = src; }\n\
        pub unsafe fn caller(value: *const i32) -> i32 {\n\
            let mut slot: *const i32 = value; update_slot(&mut slot, value); *slot\n\
        }\n";
    let inventory = inventory(input, "caller::slot");
    let record = covered(&inventory, "caller::slot", "update_slot", 0);
    assert_eq!(record.evidence, SourceBridgeEvidence::BindingStorage);
    assert!(
        !inventory
            .potentials
            .iter()
            .any(|potential| potential.site == record.potential.site),
        "borrowing a pointer binding's storage is a distinct depth-two operation"
    );
}

#[test]
fn sibling_r233_coverage_native_mutable_reference_sibling_has_actual_access_evidence() {
    let input = PARAMETER_CASE
        .replace(
            "update(dst: *mut i32, src: *const i32)",
            "update(dst: &mut i32, src: *const i32)",
        )
        .replace(
            "update((*holder).data, src);",
            "update(&mut *(*holder).data, src);",
        );
    let potentials = potentials(&input, "caller::src");
    let source = source_site(&potentials, "caller::src");
    let sibling = source
        .siblings
        .iter()
        .find(|sibling| sibling.argument_index == 0)
        .expect("a native reference parameter is a pointer-access sibling");
    assert!(
        matches!(
            sibling.access,
            SiblingAccess::Foster {
                mutable: true,
                defaulted: false,
                ..
            }
        ),
        "access must use the actual callee MIR parameter fact, not &mut spelling: {sibling:?}"
    );
}

#[test]
fn sibling_r233_coverage_unknown_rooted_wrapper_is_explicit_and_terminal_filtered() {
    // Consumer-only constructed record. The attempted trait-method fixture
    // reached an unsupported analysis surface; no analysis behavior is changed
    // or claimed here. The underlying canonical site remains a real fixture.
    let inventory = inventory(PARAMETER_CASE, "caller::src");
    let mut record = covered(&inventory, "caller::src", "update", 1).clone();
    record.evidence = SourceBridgeEvidence::UnknownShape("constructed-unresolved-wrapper-control");
    let gaps = sibling_overlap::select_coverage_gaps(std::slice::from_ref(&record), raw_terminal);
    assert_eq!(
        gaps.len(),
        1,
        "unknown rooted source custody must be reported for a delivered raw-boundary site"
    );
    assert_eq!(gaps[0].potential.site, record.potential.site);
    assert_eq!(gaps[0].reason, "sibling-source-bridge-custody-unresolved");
    // **R291-1** — the gap carries the shape it could not seal. The receipt
    // used to discard it, so every corpus site arrived under one name with no
    // partition to design the source-bridge row contract on.
    assert_eq!(gaps[0].shape, "constructed-unresolved-wrapper-control");
    for terminal in [
        TerminalSiteState {
            source_delivered: false,
            ..raw_terminal(&record.potential)
        },
        TerminalSiteState {
            target_form: Form::Ref { mutable: false },
            ..raw_terminal(&record.potential)
        },
    ] {
        assert!(
            sibling_overlap::select_coverage_gaps(std::slice::from_ref(&record), |_| terminal)
                .is_empty()
        );
    }
}

#[test]
fn sibling_r233_unmodeled_memcmp_contract_remains_explicitly_unknown() {
    // Same declaration/cast form as the existing GREEN PAIR memcmp witness.
    // That witness proves the const-void endpoint, not an access-table row:
    // classify_contract has no memcmp row and must return PositionUnmodeled.
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        extern \"C\" { fn memcmp(left: *const core::ffi::c_void, right: *const core::ffi::c_void, count: usize) -> i32; }\n\
        pub unsafe fn caller(src: *const i8) -> i32 { memcmp(src as *const _, src as *const _, 1) }\n";
    let inventory = inventory(input, "caller::src");
    let record = covered(&inventory, "caller::src", "memcmp", 0);
    assert!(
        matches!(
            record.potential.siblings[0].access,
            SiblingAccess::Unknown("sibling-library-access-unresolved")
        ),
        "a missing sealed access contract remains unknown: {record:?}"
    );
}

#[test]
fn sibling_r233_live_local_ancestor_prevents_the_dead_local_exception() {
    use rustc_middle::mir::{BasicBlock, Location};
    use rustc_mir_dataflow::Analysis;

    use crate::analyses::{borrow_ownership::slots::SlotOwner, liveness::MaybeLiveLocals};

    let input = local_case("*orig").replace(
        "let src: *const i32 = &value;",
        "let orig: *const i32 = &value; let src: *const i32 = orig;",
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("ancestor fixture uses the actual decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("R233 ancestor-live fixture solve receipt: {solve:#?}");
        assert!(solve.is_some(), "actual fixture solve receipt is mandatory");
        let original = ctx.subjects.iter().find(|subject| subject.label == "caller::orig")
            .expect("actual named local ancestor");
        let copied = ctx.subjects.iter().find(|subject| subject.label == "caller::src")
            .expect("actual named local copy");
        for subject in [original, copied] {
            let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)))
                .copied();
            assert_eq!(kind, Some(super::SlotKind::Ref),
                "the ancestor and copied source must both be actual model-Ref: {}", subject.label);
            assert!(matches!(subject.kind, SubjectKind::Local),
                "this control is independent of parameter protectors");
        }
        let flows = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&copied.fn_did)).expect("existing frozen native body flows");
        assert!(flows.body.depth0_value_flows().contains(&(
            SlotOwner::Local(original.local), SlotOwner::Local(copied.local),
        )), "the ancestor -> copy relation must be exported, not inferred from names");
        let inventory = sibling_overlap::collect_inventory(tcx, &ctx);
        let source = source_site(&inventory.potentials, "caller::src");
        let body = tcx.mir_drops_elaborated_and_const_checked(copied.fn_did).borrow();
        let call = Location { block: BasicBlock::from_u32(source.site.block),
            statement_index: source.site.statement_index as usize };
        let mut cursor = MaybeLiveLocals.iterate_to_fixpoint(tcx, &body, None).into_results_cursor(&body);
        cursor.seek_before_primary_effect(call);
        assert!(cursor.get().contains(original.local), "the actual ancestor is live on call exit");
        assert!(!cursor.get().contains(copied.local), "the copied source itself is dead on call exit");
        println!("R233 ancestor-live exact evidence: ancestor={:?}, source={:?}, call={call:?}, siblings={:?}",
            original.local, copied.local, source.siblings);
        // No A5 override or non-Clear assertion: the local lifetime proof must
        // remain truthful independently of whether this particular pair is risky.
        assert!(matches!(&source.local_post_call, LocalPostCallEvidence::Live { locals }
            if locals.contains(&original.local)),
            "a surviving local ancestor forbids DeadUnprotected: {source:#?}");
    }).expect("actual-flow ancestor fixture compiles");
}

#[test]
fn sibling_r233_unknown_shape_with_a_cleared_writing_pair_has_no_scope_gap() {
    let inventory = inventory(PARAMETER_CASE, "caller::src");
    let mut record = covered(&inventory, "caller::src", "update", 1).clone();
    record.evidence = SourceBridgeEvidence::UnknownShape("consumer-control-unknown-source-shape");
    assert_eq!(
        sibling_overlap::select_coverage_gaps(std::slice::from_ref(&record), raw_terminal).len(),
        1,
        "the original non-clear writing pair has an unresolved source-custody gap"
    );
    assert!(record.potential.siblings.iter().any(|sibling| matches!(
        sibling.access,
        SiblingAccess::Foster {
            mutable: true,
            defaulted: false,
            ..
        }
    )));
    // Consumer-only contrast: change the typed verdict while retaining the
    // exact site and actual write evidence; no claim about the fixture's A5.
    for sibling in &mut record.potential.siblings {
        sibling.proof.verdict = A5SiteProofVerdict::Clear;
        sibling.proof.reason = "consumer-control-proven-disjoint";
    }
    assert!(
        sibling_overlap::select_coverage_gaps(std::slice::from_ref(&record), raw_terminal)
            .is_empty(),
        "a cleared pair is outside the R233 sibling-write exposure predicate"
    );
}

#[test]
fn sibling_r233_unknown_shape_with_actual_sealed_read_only_sibling_has_no_scope_gap() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        extern \"C\" { fn strcmp(a: *const i8, b: *const i8) -> i32; }\n\
        pub unsafe fn caller(src: *const i8, peer: *const i8) -> i32 { strcmp(src, peer) }\n";
    let inventory = inventory(input, "caller::src");
    let mut record = covered(&inventory, "caller::src", "strcmp", 0).clone();
    assert_eq!(record.potential.siblings.len(), 1);
    assert!(
        matches!(
            record.potential.siblings[0].access,
            SiblingAccess::Contract {
                access: super::decision::raw_boundary_contracts::PointeeAccess::Read,
                ..
            }
        ),
        "the read-only access must be the actual sealed contract"
    );
    // Only source-shape custody is a constructed consumer input. The canonical
    // call and its sibling contract remain the compiler-observed evidence.
    record.evidence = SourceBridgeEvidence::UnknownShape("consumer-control-unknown-source-shape");
    let terminal = TerminalSiteState {
        source_form: Form::Ref { mutable: true },
        ..raw_terminal(&record.potential)
    };
    assert!(
        sibling_overlap::select_coverage_gaps(std::slice::from_ref(&record), |_| terminal)
            .is_empty(),
        "read-only sibling access is outside the pending-write waiver, without a soundness claim"
    );
}
