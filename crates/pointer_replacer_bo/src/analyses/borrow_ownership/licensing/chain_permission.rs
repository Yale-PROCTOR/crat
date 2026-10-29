//! Exact complete original-cell chain evidence. Permission is installed separately.
use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use super::{
    cell_effects,
    facts::{EquationId, Facts},
    field_support::{FieldProof, Pending},
    matched::{SourceLineage, TerminalTarget},
    transport::Node,
};
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Proof {
    pub(crate) put: cell_effects::Candidate,
    pub(crate) release: cell_effects::Candidate,
    pub(crate) put_guard: EquationId,
    pub(crate) release_guard: EquationId,
    pub(crate) source: EquationId,
    pub(crate) free: EquationId,
    pub(crate) store: EquationId,
    pub(crate) middle: Node,
    pub(crate) effects: super::chain_effects::Effects,
}
pub(crate) fn certify(
    facts: &Facts,
    field: &FieldProof,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Option<Proof> {
    if !facts.frame_attested
        || super::caller_coverage::assess(facts) != super::caller_coverage::Status::Complete
        || facts.constructions != 1
        || !field.stores.is_empty()
        || field.input_stores.len() != 1
        || field
            .holds
            .iter()
            .any(|h| h.reason != Pending::CallerCoverageC)
    {
        return None;
    }
    let store = &field.input_stores[0];
    let [app] = store.applications.as_slice() else { return None };
    let [alt] = app.alternatives.as_slice() else { return None };
    let SourceLineage::Exact(source_path) = &alt.free.source.lineage else { return None };
    let [make] = source_path.as_slice() else { return None };
    let SourceLineage::Exact(free_path) = &alt.free.terminal.lineage else { return None };
    let [release_call] = free_path.as_slice() else { return None };
    let TerminalTarget::Free(free) = alt.free.terminal.target else { return None };
    let [returned] = alt.forwarded_returns.as_slice() else { return None };
    if !alt.pending_outputs.is_empty()
        || returned.continuation != alt.free
        || returned.call.caller != release_call.callee
        || returned.call_path != vec![release_call.clone(), returned.call.clone()]
        || make.caller != app.application.call.caller
        || release_call.caller != make.caller
    {
        return None;
    }
    let candidates = cell_effects::discover(facts);
    if candidates.len() != 2 {
        return None;
    }
    let put = candidates.iter().find(|c| c.call == app.application.call)?;
    let release = candidates.iter().find(|c| &c.call == release_call)?;
    if put.cell != release.cell
        || put.field_key != field.field_key
        || release.field_key != field.field_key
    {
        return None;
    }
    let arm = |c: &cell_effects::Candidate| {
        let b = facts
            .boundary_substitutions
            .iter()
            .find(|b| b.point.construction == c.call.construction && b.ordinal == c.boundary)?;
        cell_effects::call_arm(facts, b, aliases)
    };
    let put_arm = arm(put)?;
    let release_arm = arm(release)?;
    if put_arm.original.1 != release_arm.original.0
        || put_arm.guard == release_arm.guard
        || [put_arm.guard, release_arm.guard]
            .iter()
            .any(|g| alt.free.guards.permissive().get(g) != Some(&true))
    {
        return None;
    }
    let effects = super::chain_effects::effects(facts, put, release, field)?;
    Some(Proof {
        put: put.clone(),
        release: release.clone(),
        put_guard: put_arm.guard,
        release_guard: release_arm.guard,
        source: alt.free.source.endpoint,
        free,
        store: store.equation,
        middle: Node {
            construction: put.call.construction,
            var: put_arm.original.1,
        },
        effects,
    })
}
#[cfg(test)]
mod tests {
    //! Complete original-cell chain witnesses; embedded programs are never run.
    use super::super::{
        super::SlotKind,
        tests::{inspect, inspect_attested_frame},
    };
    const CODE: &str = r#"
unsafe extern "C" {fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Cell {ptr:*mut i32}
pub unsafe fn make()->*mut i32 {let value=malloc(4) as *mut i32;*value=5;value}
pub unsafe fn put(cell:*mut Cell,value:*mut i32){(*cell).ptr=value;}
pub unsafe fn take(cell:*mut Cell)->*mut i32 {let value=(*cell).ptr;(*cell).ptr=0 as *mut i32;value}
pub unsafe fn release(cell:*mut Cell){let value=take(cell);free(value as *mut core::ffi::c_void);}
pub unsafe fn f(){let owner=make();let mut cell=Cell{ptr:0 as *mut i32};put(&mut cell,owner);release(&mut cell);}
"#;
    /// Under the lend the cell formals are lent: the cell's field is a reference, the
    /// payload stays raw, and no snapshot carries a complete chain.
    #[test]
    fn c04_under_the_lend_the_ol06_chain_takes_no_certificate() {
        let fixture = inspect_attested_frame(CODE);
        for (key, kind) in [
            ("Cell.ptr", SlotKind::Ref),
            ("make::value", SlotKind::Raw),
            ("make::_0", SlotKind::Raw),
            ("f::owner", SlotKind::Raw),
            ("put::value", SlotKind::Ref),
            ("take::value", SlotKind::Ref),
            ("take::_0", SlotKind::Ref),
            ("release::value", SlotKind::Raw),
            ("put::cell", SlotKind::Ref),
            ("take::cell", SlotKind::Ref),
            ("release::cell", SlotKind::Ref),
        ] {
            fixture.assert_kind(key, kind);
        }
        assert!(
            fixture
                .export
                .ownership_licensing
                .as_ref()
                .unwrap()
                .iter()
                .all(|s| s.complete_chains.is_empty())
        );
    }
    #[test]
    fn c04_complete_chain_holds_unattested_and_partner_free() {
        inspect(CODE).assert_not_owning("Cell.ptr");
        let partner = CODE.replace(
            "release(&mut cell);",
            "release(&mut cell);free(owner as *mut core::ffi::c_void);",
        );
        inspect_attested_frame(&partner).assert_not_owning("Cell.ptr");
    }

    /// Under the lend the chain's structural certificate forms on none of the variants.
    #[test]
    fn c04_complete_chain_certificate_forms_on_no_variant_under_the_lend() {
        use super::super::{
            field_support, graph_tests::with_facts, matched::MatchedTransport,
            value_origins::ValueOrigins,
        };
        let check = |code: &str, expected: bool| {
            with_facts(code, move |original| {
                let mut facts = original.clone();
                facts.frame_attested = true;
                let matched = MatchedTransport::build(&facts);
                let origins = ValueOrigins::build(&facts);
                let fields =
                    field_support::audit(&facts, &facts.field_support_inputs, &matched, &origins);
                let field = fields
                    .iter()
                    .find(|f| f.field_key == "Cell::field0@d0")
                    .unwrap();
                let proof = super::certify(&facts, field, matched.guard_aliases());
                assert_eq!(
                    proof.is_some(),
                    expected,
                    "chain structural certificate: {field:#?}"
                );
                if let Some(proof) = proof {
                    assert_ne!(proof.put_guard, proof.release_guard);
                    assert_eq!(proof.put.cell, proof.release.cell);
                    for guard in [proof.put_guard, proof.release_guard] {
                        assert_eq!(
                            field.input_stores[0].applications[0].alternatives[0]
                                .free
                                .guards
                                .permissive()
                                .get(&guard),
                            Some(&true)
                        );
                    }
                    let mut corrupt = facts.clone();
                    corrupt
                        .source_occurrences
                        .get_mut("take")
                        .unwrap()
                        .retain(|r| r.syntax.destination.projection.is_empty());
                    assert!(
                        super::certify(&corrupt, field, matched.guard_aliases()).is_none(),
                        "missing reset source occurrence must not reuse cached evidence"
                    );
                    let mut corrupt = field.clone();
                    corrupt.input_stores[0].applications[0].alternatives[0]
                        .free
                        .guards
                        .exact_mut()
                        .remove(&proof.release_guard);
                    corrupt.input_stores[0].applications[0].alternatives[0].forwarded_returns[0]
                        .continuation
                        .guards
                        .exact_mut()
                        .remove(&proof.release_guard);
                    assert!(
                        super::certify(&facts, &corrupt, matched.guard_aliases()).is_none(),
                        "release guard premise is mandatory: guard={:?}, source={:?}, free={:?}",
                        proof.release_guard,
                        proof.source,
                        proof.free
                    );
                }
            })
        };
        check(CODE, false);
        check(
            &CODE.replace(
                "release(&mut cell);",
                "release(&mut cell);free(owner as *mut core::ffi::c_void);",
            ),
            false,
        );
        check(&CODE.replace("(*cell).ptr=0 as *mut i32;", ""), false);
        check(&CODE.replace("pub unsafe fn take(cell:*mut Cell)->*mut i32 {","unsafe extern \"C\" {fn unknown(p:*mut Cell); } pub unsafe fn take(cell:*mut Cell)->*mut i32 {unknown(cell);"),false);
    }
    /// Under the lend no snapshot carries a complete chain whose effect obligations it
    /// could rebuild.
    #[test]
    fn c04_no_snapshot_carries_a_complete_chain_under_the_lend() {
        let fixture = inspect_attested_frame(CODE);
        let snapshots = fixture.export.ownership_licensing.as_ref().unwrap();
        assert!(snapshots.iter().all(|s| s.complete_chains.is_empty()));
    }
    fn certify_code(code: &str, expected: bool) {
        super::super::graph_tests::with_facts(code, move |facts| {
            let mut facts = facts.clone();
            facts.frame_attested = true;
            let matched = super::super::matched::MatchedTransport::build(&facts);
            let origins = super::super::value_origins::ValueOrigins::build(&facts);
            let fields = super::super::field_support::audit(
                &facts,
                &facts.field_support_inputs,
                &matched,
                &origins,
            );
            let proof = fields
                .iter()
                .find_map(|field| super::certify(&facts, field, matched.guard_aliases()));
            assert_eq!(proof.is_some(), expected, "complete-chain effect boundary");
        });
    }
    #[test]
    fn c04_complete_chain_requires_initialization_before_consuming_copy() {
        certify_code(
            &CODE.replace("*value=5;value", "let alias=value;*value=5;alias"),
            false,
        );
    }
    #[test]
    fn c04_complete_chain_with_a_size_of_intrinsic_is_not_certified_under_the_lend() {
        certify_code(
            &CODE.replace("malloc(4)", "malloc(core::mem::size_of::<i32>())"),
            false,
        );
    }
    /// With the copy-lend baseline construction this fixture's late hard constraints and
    /// original endpoints are unsatisfiable before the borrow replay under the record.
    #[test]
    fn c04_complete_chain_original_endpoints_are_hard_unsat_under_the_record() {
        use rustc_hir::{ItemKind, OwnerNode};

        use super::super::super::{
            construction::{CopyLendMode, construct_bo_into},
            crate_slots::CrateSlots,
            mutability_facts::MutFacts,
            origins::compute_origins,
            param_overlap::WholeProgramAttestation,
            solver::KindSolver,
        };
        let code = CODE.replace("malloc(4)", "malloc(core::mem::size_of::<i32>())");
        ::utils::compilation::run_compiler_on_str(&code, |tcx| {
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
            let _world = super::super::stack_entry::enter_world(Some(
                WholeProgramAttestation::FrozenBenchmarkGraph,
            ));
            let solver = KindSolver::new_tracked(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &mutability,
                &solver,
                CopyLendMode::Baseline,
            )
            .unwrap();
            super::super::super::coherence::constrain_field_ownership(&solver, &slots, &program);
            let tracker = solver.tracker().unwrap();
            let mut assumptions = tracker.tracks();
            assumptions.extend_from_slice(construction.selectors.sources());
            assumptions.extend_from_slice(construction.selectors.sinks());
            let outcome = solver.check_with_assumptions(&assumptions);
            if outcome == z3::SatResult::Unsat {
                let labels: Vec<_> = solver
                    .optimize()
                    .get_unsat_core()
                    .iter()
                    .map(|literal| {
                        tracker
                            .label_of(literal)
                            .unwrap_or_else(|| literal.to_string())
                    })
                    .collect();
                eprintln!(
                    "C04_CHAIN_HARD_CORE={}",
                    serde_json::to_string(&labels).unwrap()
                );
            }
            assert_eq!(outcome, z3::SatResult::Unsat);
        })
        .unwrap_or_else(|error| error.raise());
    }
    #[test]
    fn c04_complete_chain_holds_extra_callers_shared_reference_and_retention() {
        for code in [
            format!("{CODE}\npub unsafe fn other(cell:*mut Cell){{release(cell);}}"),
            format!("{CODE}\npub unsafe fn other(){{let p=malloc(core::mem::size_of::<Cell>()) as *mut Cell;release(p);free(p as *mut core::ffi::c_void);}}"),
            CODE.replace("put(&mut cell,owner)","put(&cell as *const Cell as *mut Cell,owner)"),
            CODE.replace("pub unsafe fn release(cell:*mut Cell){","static mut SAVED:*mut Cell=0 as *mut Cell;pub unsafe fn release(cell:*mut Cell){SAVED=cell;"),
            format!("{CODE}\npub unsafe fn other(){{let mut n=9;let mut cell=Cell{{ptr:0 as *mut i32}};put(&mut cell,&mut n);}}"),
        ] {
            let fixture=inspect_attested_frame(&code);
            fixture.assert_not_owning("Cell.ptr");
            assert!(fixture.export.ownership_licensing.as_ref().unwrap().iter().all(|s|s.complete_chains.is_empty()),"unsupported effect/caller must have no chain certificate");
        }
    }
}
