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
            .any(|g| alt.free.guards.get(g) != Some(&true))
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
        tests::{inspect, inspect_era5_frame},
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
    #[test]
    fn c04_complete_chain_attested_ol06_keeps_original_free_and_nonowning_parents() {
        let fixture = inspect_era5_frame(CODE);
        eprintln!(
            "C04_CHAIN_EVIDENCE={}",
            serde_json::json!({"licensing":fixture.export.ownership_licensing,"origin":fixture.origin_json,"commit_trace":fixture.commit_trace})
        );
        for key in [
            "Cell.ptr",
            "make::value",
            "make::_0",
            "f::owner",
            "put::value",
            "take::value",
            "take::_0",
            "release::value",
        ] {
            fixture.assert_kind(key, SlotKind::Owning);
        }
        for key in ["put::cell", "take::cell", "release::cell"] {
            fixture.assert_kind(key, SlotKind::Ref);
        }
        let accepted = fixture
            .export
            .stack_entry_final
            .as_ref()
            .expect("accepted chain selection/entry receipt");
        let snapshot = fixture
            .export
            .ownership_licensing
            .as_ref()
            .unwrap()
            .iter()
            .find(|s| s.offset == accepted.snapshot_offset)
            .unwrap();
        let chain = &snapshot.complete_chains[0];
        let selected: std::collections::BTreeMap<_, _> =
            accepted.original_cell_guards.iter().copied().collect();
        assert_eq!(selected.get(&chain.put_guard), Some(&true));
        assert_eq!(selected.get(&chain.release_guard), Some(&true));
        assert_eq!(
            accepted.proofs.len(),
            1,
            "one exact original-free entry comparison"
        );
        let aliases = snapshot.metadata.guard_aliases.iter().copied().collect();
        assert_eq!(
            super::super::chain_entry::expected(&snapshot.metadata.facts(), chain, &aliases)
                .as_ref(),
            accepted.proofs.first()
        );
        let facts = snapshot.metadata.facts();
        let owns = fixture.export.version_owns.as_ref().unwrap();
        use super::super::super::ssa::constraint::Var;
        for (candidate, input, output) in [(&chain.put, false, true), (&chain.release, true, false)]
        {
            let boundary = facts
                .boundary_substitutions
                .iter()
                .find(|b| {
                    b.point.construction == candidate.call.construction
                        && b.ordinal == candidate.boundary
                })
                .unwrap();
            let arm = super::super::cell_effects::call_arm(&facts, boundary, &aliases).unwrap();
            assert_eq!(owns[Var::from_u32(arm.formal.0)], input);
            assert_eq!(owns[Var::from_u32(arm.formal.1)], output);
            assert!(!owns[Var::from_u32(arm.legacy.0)]);
            assert!(!owns[Var::from_u32(arm.legacy.1)]);
            assert_eq!(owns[Var::from_u32(arm.original.0)], input);
            assert_eq!(owns[Var::from_u32(arm.original.1)], output);
        }
    }
    #[test]
    fn c04_complete_chain_holds_unattested_and_partner_free() {
        inspect(CODE).assert_not_owning("Cell.ptr");
        let partner = CODE.replace(
            "release(&mut cell);",
            "release(&mut cell);free(owner as *mut core::ffi::c_void);",
        );
        inspect_era5_frame(&partner).assert_not_owning("Cell.ptr");
    }

    #[test]
    fn c04_complete_chain_certificate_requires_both_exact_cells_and_all_effects() {
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
                        .remove(&proof.release_guard);
                    corrupt.input_stores[0].applications[0].alternatives[0].forwarded_returns[0]
                        .continuation
                        .guards
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
        check(CODE, true);
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
    #[test]
    fn c04_complete_chain_snapshot_rebuilds_effect_obligations() {
        let fixture = inspect_era5_frame(CODE);
        let snapshots = fixture.export.ownership_licensing.as_ref().unwrap();
        let snapshot = snapshots
            .iter()
            .find(|s| !s.complete_chains.is_empty())
            .expect("actual attested chain effect export");
        assert_eq!(snapshot.complete_chains.len(), 1);
        snapshot.validate().unwrap();
        let decoded: super::super::snapshot::Snapshot =
            serde_json::from_slice(&serde_json::to_vec(snapshot).unwrap()).unwrap();
        decoded.validate().unwrap();
        let mut missing = decoded.clone();
        missing.complete_chains.clear();
        assert!(
            missing.validate().is_err(),
            "omitted whole-chain proof must be detected"
        );
        let mut wrong = decoded.clone();
        wrong.complete_chains[0].release_guard = wrong.complete_chains[0].put_guard;
        assert!(
            wrong.validate().is_err(),
            "distinct native occurrences cannot share a forged guard"
        );
        let mut wrong = decoded.clone();
        wrong.complete_chains[0].effects.field_reset.statement += 1;
        assert!(
            wrong.validate().is_err(),
            "field reset occurrence must be authenticated"
        );
        assert_eq!(
            decoded
                .first_permissions
                .iter()
                .filter(|p| p.complete_chain.is_some())
                .count(),
            2,
            "the one complete chain supplies both native dispositions"
        );
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
    fn c04_complete_chain_accepts_ol06_size_of_intrinsic() {
        certify_code(
            &CODE.replace("malloc(4)", "malloc(core::mem::size_of::<i32>())"),
            true,
        );
    }
    #[test]
    fn c04_complete_chain_original_endpoints_are_hard_satisfiable() {
        use rustc_hir::{ItemKind, OwnerNode};

        use super::super::super::{
            a5_overlap::WholeProgramAttestation,
            construction::{CopyLendMode, construct_bo_into},
            crate_slots::CrateSlots,
            mutability_facts::MutFacts,
            origins::compute_origins,
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
            assert_eq!(
                outcome,
                z3::SatResult::Sat,
                "complete chain with all late hard constraints and original endpoints before borrow replay"
            );
            let facts=solver.ownership_facts().unwrap();
            let chain=&facts.licensing.as_ref().unwrap().complete_chains[0];
            let field=facts.slot_refs[&chain.put.field_key];
            let owning=solver.owning_literal(field);
            for id in [chain.put_guard,chain.release_guard] {
                let guard=facts.guards.iter().find(|g|g.equation==id).unwrap().predicate.clone();
                for endpoint in [chain.source,chain.free] {
                    let dependency=facts.guards.iter().find(|g|g.equation==endpoint).unwrap().predicate.clone();
                    let mut withdrawn=tracker.tracks();withdrawn.push(guard.clone());withdrawn.push(!dependency);
                    assert_eq!(solver.check_with_assumptions(&withdrawn),z3::SatResult::Unsat,
                        "selected guard survives withdrawn original endpoint: {id:?} / {endpoint:?}");
                }
                let mut converse=tracker.tracks();converse.push(owning.clone());converse.push(!guard);
                assert_eq!(solver.check_with_assumptions(&converse),z3::SatResult::Unsat,
                    "owning field requires exact native guard even with T2 endpoints free: {id:?}");
            }
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
            let fixture=inspect_era5_frame(&code);
            fixture.assert_not_owning("Cell.ptr");
            assert!(fixture.export.ownership_licensing.as_ref().unwrap().iter().all(|s|s.complete_chains.is_empty()),"unsupported effect/caller must have no chain certificate");
        }
    }
}
