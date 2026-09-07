//! Compiler-backed H07 export REDs, separate from ownership/conservation proofs.

use std::collections::BTreeSet;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Local, Operand, RETURN_PLACE, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;

use super::*;
use crate::analyses::{
    borrow_ownership::{
        construction::{CopyLendMode, construct_bo_into},
        export,
        mutability_facts::MutFacts,
        origin_summary::{SignatureRoot, SignatureSlot},
        origins::compute_origins,
        slot_key,
        solver::KindSolver,
    },
    mir::{CallKind, TerminatorExt},
};

fn inspect(
    source: &str,
    check: impl FnOnce(&RustProgram<'_>, &CrateSlots, &OriginSummaries) + Send + Sync,
) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
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
        let origins = compute_origins(&program);
        check(&program, &slots, &origins);
    })
    .unwrap_or_else(|error| error.raise());
}

fn did(program: &RustProgram<'_>, name: &str) -> LocalDefId {
    let found: Vec<_> = program
        .functions
        .iter()
        .copied()
        .filter(|did| program.tcx.item_name(did.to_def_id()).as_str() == name)
        .collect();
    assert_eq!(found.len(), 1);
    found[0]
}

fn key(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    function: LocalDefId,
    signature: SignatureSlot,
) -> SignatureKey {
    let root = match signature.place.root {
        SignatureRoot::Return => RETURN_PLACE,
        SignatureRoot::Arg(local) => local,
    };
    assert!(
        signature.place.field.is_none(),
        "these controls use exact non-field signature paths"
    );
    let kind_slot = if slots.fn_local_slots[&function]
        .slot_for_local_depth(root, signature.depth)
        .is_some()
    {
        OriginAvailability::Present(slot_key::local_key(
            program.tcx,
            function,
            root.as_usize(),
            signature.depth,
        ))
    } else {
        OriginAvailability::Missing(OriginMissing::KindSlotUnmapped)
    };
    SignatureKey {
        root: slot_key::local_key(program.tcx, function, root.as_usize(), 0),
        root_dereferences: signature.place.deref_depth,
        field: None,
        depth: signature.depth,
        kind_slot,
    }
}

fn function<'a>(facts: &'a OriginEvidence, name: &str) -> &'a FunctionEvidence {
    let rows: Vec<_> = facts
        .functions
        .iter()
        .filter(|row| row.function == name)
        .collect();
    assert_eq!(
        rows.len(),
        1,
        "one canonical origin-evidence function {name}"
    );
    rows[0]
}

fn present<T>(value: &OriginAvailability<T>) -> &T {
    match value {
        OriginAvailability::Present(value) => value,
        OriginAvailability::Missing(_) => panic!("existing supplied evidence must be present"),
    }
}

fn gaps(row: &FunctionEvidence) {
    assert_eq!(
        row.ownership.equations,
        OriginMissing::OwnershipEquationsNotExported
    );
    assert_eq!(
        row.ownership.dynamic_epochs,
        OriginMissing::DynamicEpochNotRepresented
    );
    assert_eq!(
        row.ownership.partner_free,
        OriginMissing::PartnerFreeCorrespondenceNotExported
    );
    assert_eq!(
        row.ownership.conservation,
        OriginMissing::ConservationNotProved
    );
}

#[test]
fn e5_l_origin_native_value_and_storage_relations_stay_separate() {
    inspect(
        "pub unsafe fn forward(out: *mut *mut i32) -> *mut *mut i32 { out }",
        |program, slots, origins| {
            let function_id = did(program, "forward");
            let native = &origins.native_flows()[&function_id].summary;
            let index = |root, depth| {
                native
                    .slots
                    .iter_enumerated()
                    .find_map(|(id, slot)| {
                        (slot.place.root == root
                            && slot.place.field.is_none()
                            && slot.depth == depth)
                            .then_some(id)
                    })
                    .unwrap()
            };
            let argument = SignatureRoot::Arg(Local::from_usize(1));
            let a0 = index(argument, 0);
            let r0 = index(SignatureRoot::Return, 0);
            let a1 = index(argument, 1);
            let r1 = index(SignatureRoot::Return, 1);
            assert!(
                native.value_flows.contains(a0, r0),
                "actual value-flow precondition"
            );
            assert!(
                native.storage_aliases.contains(a1, r1) && native.storage_aliases.contains(r1, a1),
                "actual symmetric storage-alias precondition"
            );
            let facts = collect(program, slots, origins, None);
            let row = function(&facts, "forward");
            for (matrix, actual) in [
                (&native.value_flows, &row.value_flows),
                (&native.storage_aliases, &row.storage_aliases),
            ] {
                let mut expected = BTreeSet::new();
                for source in matrix.rows() {
                    for target in matrix
                        .row(source)
                        .into_iter()
                        .flat_map(|targets| targets.iter())
                    {
                        expected.insert(OriginRelation {
                            source: key(program, slots, function_id, native.slots[source]),
                            target: key(program, slots, function_id, native.slots[target]),
                        });
                    }
                }
                assert_eq!(
                    present(actual),
                    &expected.into_iter().collect::<Vec<_>>(),
                    "exact native relation transport"
                );
            }
            assert!(
                present(&row.value_flows)
                    .iter()
                    .any(|edge| edge.source.depth == 0 && edge.target.depth == 0)
            );
            assert!(
                present(&row.storage_aliases)
                    .iter()
                    .any(|edge| edge.source.depth == 1 && edge.target.depth == 1)
            );
            gaps(row);
            // This existing API deliberately retains summaries without native matrices.
            let without_native: OriginSummaries = origins
                .iter()
                .map(|(&did, summary)| (did, summary.clone()))
                .collect();
            assert!(without_native.try_native_flows().is_none());
            let missing = collect(program, slots, &without_native, None);
            let missing = function(&missing, "forward");
            assert_eq!(
                missing.value_flows,
                OriginAvailability::Missing(OriginMissing::NativeFlowsNotAvailable)
            );
            assert_eq!(
                missing.storage_aliases,
                OriginAvailability::Missing(OriginMissing::NativeFlowsNotAvailable)
            );
        },
    );
}

#[test]
fn e5_l_origin_unknown_is_may_no_borrow_origin_not_exclusive_opacity() {
    inspect(
        r#"
unsafe extern "C" { fn malloc(bytes: usize) -> *mut i32; fn opaque() -> *mut i32; }
pub unsafe fn known(p: *mut i32) -> *mut i32 { p }
pub unsafe fn fresh() -> *mut i32 { malloc(4) }
pub unsafe fn unknown() -> *mut i32 { opaque() }
pub unsafe fn mixed(p: *mut i32, choose: bool) -> *mut i32 { if choose { p } else { opaque() } }
"#,
        |program, slots, origins| {
            let evidence = collect(program, slots, origins, None);
            let bytes = evidence.canonical_json();
            assert_eq!(
                serde_json::from_str::<OriginEvidence>(&bytes).unwrap(),
                evidence
            );
            let mut reversed = evidence.clone();
            reversed.functions.reverse();
            assert_eq!(reversed.canonical_json(), bytes);
            for name in ["known", "fresh", "unknown", "mixed"] {
                let function_id = did(program, name);
                let native = &origins.native_flows()[&function_id].summary;
                let summary = &origins[&function_id];
                let row = function(&evidence, name);
                let expected: BTreeSet<_> = summary
                    .unknown
                    .iter()
                    .map(|id| key(program, slots, function_id, summary.slots[id]))
                    .collect();
                assert_eq!(
                    row.no_borrow_origin,
                    expected.into_iter().collect::<Vec<_>>()
                );
                let unknown: BTreeSet<_> = native
                    .unknown_targets
                    .iter()
                    .map(|id| key(program, slots, function_id, native.slots[id]))
                    .collect();
                assert_eq!(
                    present(&row.native_unknown_targets),
                    &unknown.into_iter().collect::<Vec<_>>()
                );
                let ret = native
                    .slots
                    .iter()
                    .find(|slot| {
                        slot.place.root == SignatureRoot::Return
                            && slot.depth == 0
                            && slot.place.field.is_none()
                    })
                    .unwrap();
                let returned = key(program, slots, function_id, *ret);
                assert_eq!(row.no_borrow_origin.contains(&returned), name != "known");
                if name == "mixed" {
                    assert!(
                        present(&row.value_flows).iter().any(
                            |edge| edge.target == returned && edge.source.root != returned.root
                        ),
                        "modeled flow and no-borrow-origin must coexist"
                    );
                }
                gaps(row);
            }
        },
    );
}

#[test]
fn e5_l_origin_source_and_supplied_version_occurrences_are_not_equation_proofs() {
    inspect(
        r#"
pub unsafe fn identity(p: *mut i32) -> *mut i32 { p }
pub unsafe fn occurrences(p: *mut i32) -> *mut i32 { let q = p; let r = identity(q); r }
"#,
        |program, slots, origins| {
            let function_id = did(program, "occurrences");
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function_id)
                .borrow();
            let before = collect(program, slots, origins, None);
            let row = function(&before, "occurrences");
            assert_eq!(
                row.ownership.versions,
                OriginAvailability::Missing(OriginMissing::OwnershipVersionsNotSupplied)
            );
            let local_key =
                |local: Local| slot_key::local_key(program.tcx, function_id, local.as_usize(), 0);
            let mut assignments = 0;
            let mut calls = 0;
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for (statement, instruction) in data.statements.iter().enumerate() {
                    if let StatementKind::Assign(box (
                        destination,
                        Rvalue::Use(Operand::Copy(source) | Operand::Move(source)),
                    )) = &instruction.kind
                        && let (Some(destination), Some(source)) =
                            (destination.as_local(), source.as_local())
                        && slots.fn_local_slots[&function_id]
                            .slot_for_local_depth(destination, 0)
                            .is_some()
                        && slots.fn_local_slots[&function_id]
                            .slot_for_local_depth(source, 0)
                            .is_some()
                    {
                        assignments += 1;
                        let site = SourceSite {
                            function: "occurrences".to_owned(),
                            block: block.as_u32(),
                            statement,
                        };
                        assert!(
                            row.occurrences
                                .iter()
                                .any(|occurrence| occurrence.site == site
                                    && occurrence.kind == OccurrenceKind::Assignment
                                    && occurrence.destination
                                        == OriginAvailability::Present(local_key(destination))
                                    && occurrence.arguments
                                        == vec![OriginAvailability::Present(local_key(source))])
                        );
                    }
                }
                if let Some(call) = data.terminator().as_call(program.tcx)
                    && let CallKind::FreeStanding(callee) = call.func
                {
                    calls += 1;
                    let site = SourceSite {
                        function: "occurrences".to_owned(),
                        block: block.as_u32(),
                        statement: data.statements.len(),
                    };
                    let argument = call.args[0].node.place().unwrap().as_local().unwrap();
                    assert!(
                        row.occurrences
                            .iter()
                            .any(|occurrence| occurrence.site == site
                                && occurrence.kind == OccurrenceKind::Call
                                && occurrence.callee
                                    == Some(SourceCallee::Local(
                                        program.tcx.def_path_str(callee.to_def_id())
                                    ))
                                && occurrence.arguments
                                    == vec![OriginAvailability::Present(local_key(argument))])
                    );
                }
            }
            assert!(
                assignments > 0 && calls == 1,
                "real MIR assignment/call occurrence preconditions"
            );
            let mutability = MutFacts::from_program(program);
            let solver = KindSolver::new(slots);
            let (_, captured) = export::with_bo_export(|| {
                construct_bo_into(
                    program,
                    slots,
                    origins,
                    &mutability,
                    &solver,
                    CopyLendMode::Baseline,
                )
                .expect("actual ownership-emission occurrences")
            });
            assert!(
                !captured.version_sites.is_empty(),
                "existing E-R2 producer must supply real VersionSites"
            );
            let with_versions = collect(program, slots, origins, Some(&captured));
            for &function_id in &program.functions {
                let name = program.tcx.def_path_str(function_id.to_def_id());
                let row = function(&with_versions, &name);
                let mut expected: Vec<_> = captured
                    .version_sites
                    .iter()
                    .filter(|site| site.fn_did == function_id)
                    .map(|site| OwnershipVersionOccurrence {
                        site: SourceSite {
                            function: name.clone(),
                            block: site.location.block,
                            statement: site.location.statement_index,
                        },
                        local: slot_key::local_key(
                            program.tcx,
                            function_id,
                            site.local.as_usize(),
                            0,
                        ),
                        diagnostic_use_var: site.use_var.map(|var| var.as_u32()),
                        diagnostic_def_var: site.def_var.map(|var| var.as_u32()),
                    })
                    .collect();
                expected.sort();
                assert_eq!(
                    present(&row.ownership.versions),
                    &expected,
                    "same-capture occurrence transport, not a cross-run Var join"
                );
                gaps(row);
            }
        },
    );
}
