//! First native original-cell permission: an exact put and caller-local free.
//! Every other memory/effect shape remains held.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::{
    super::{
        origin_evidence::SourceCallee,
        ownership_access::{Expression, OperandSyntax, PlaceSyntax},
    },
    cell_effects,
    facts::{EquationId, Facts},
    field_support::{CallerCoverage, FieldProof, Pending},
    matched::{CallKey, TerminalTarget},
    transport::Node,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Proof {
    pub(crate) candidate: cell_effects::Candidate,
    pub(crate) source: EquationId,
    pub(crate) free: EquationId,
    pub(crate) store: EquationId,
    pub(crate) parameter_slot: String,
    pub(crate) formal_output: Node,
    pub(crate) legacy_output: Node,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Decision {
    pub(crate) guard: EquationId,
    pub(crate) proof: Option<Proof>,
    pub(crate) complete_chain: Option<Box<super::chain_permission::Proof>>,
}

fn place(operand: &OperandSyntax) -> Option<&PlaceSyntax> {
    match operand {
        OperandSyntax::Copy { place } | OperandSyntax::Move { place } => Some(place),
        _ => None,
    }
}
fn inputs(expression: &Expression) -> Vec<&PlaceSyntax> {
    match expression {
        Expression::Value { operand } | Expression::Cast { operand, .. } => {
            place(operand).into_iter().collect()
        }
        Expression::Borrow { place, .. }
        | Expression::RawAddress { place, .. }
        | Expression::CopyForDeref { place } => vec![place],
        Expression::Aggregate { operands, .. } | Expression::Call { operands } => {
            operands.iter().filter_map(place).collect()
        }
        Expression::Unrepresented { .. } => Vec::new(),
    }
}
fn straight(facts: &Facts, function: &str) -> bool {
    let rows: Vec<_> = facts
        .body_rosters
        .iter()
        .filter(|b| b.point.function.as_deref() == Some(function))
        .collect();
    let [body] = rows.as_slice() else { return false };
    if !body.phis.is_empty() || body.return_width != 0 {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut next = 0;
    loop {
        let Some(block) = body.blocks.iter().find(|b| b.block == next && b.reachable) else {
            return false;
        };
        if !seen.insert(next) {
            return false;
        }
        match block.successors.as_slice() {
            [] if block.return_statement.is_some() => break,
            [n] => next = *n,
            _ => return false,
        }
    }
    seen.len() == body.blocks.iter().filter(|b| b.reachable).count()
}
fn effect(
    facts: &Facts,
    candidate: &cell_effects::Candidate,
    field: &FieldProof,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Option<Proof> {
    if !facts.frame_attested
        || super::caller_coverage::assess(facts) != super::caller_coverage::Status::Complete
        || facts.source_occurrences.len() != 2
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
    let [application] = store.applications.as_slice() else { return None };
    if application.application.call != candidate.call || application.alternatives.len() != 1 {
        return None;
    }
    let alternative = &application.alternatives[0];
    if !alternative.pending_outputs.is_empty() || !alternative.forwarded_returns.is_empty() {
        return None;
    }
    let TerminalTarget::Free(free) = alternative.free.terminal.target else { return None };
    if !matches!(&alternative.free.terminal.lineage,super::matched::SourceLineage::Exact(path) if path.is_empty())
    {
        return None;
    }
    let source = alternative.free.source.endpoint;
    let source_eq = facts
        .equations
        .iter()
        .find(|e| e.point.construction == source.construction && e.ordinal == source.ordinal)?;
    let free_eq = facts
        .equations
        .iter()
        .find(|e| e.point.construction == free.construction && e.ordinal == free.ordinal)?;
    if source_eq.point.function.as_ref() != Some(&candidate.call.caller)
        || free_eq.point.function.as_ref() != Some(&candidate.call.caller)
        || source_eq.endpoint.as_ref()?.callee != "calloc"
        || free_eq.endpoint.as_ref()?.callee != "free"
    {
        return None;
    }
    let caller = facts
        .reader_inputs
        .bodies
        .iter()
        .find(|b| b.function == candidate.call.caller)?;
    let callee = facts
        .reader_inputs
        .bodies
        .iter()
        .find(|b| b.function == candidate.call.callee)?;
    if caller.argument_count != 0
        || callee.argument_count != 2
        || !caller.complete_operations
        || !callee.complete_operations
        || !straight(facts, &caller.function)
        || !straight(facts, &callee.function)
    {
        return None;
    }
    let boundary = facts.boundary_substitutions.iter().find(|b| {
        b.point.construction == candidate.call.construction && b.ordinal == candidate.boundary
    })?;
    let outer = boundary.formal_local?;
    for body in [caller, callee] {
        for local in &body.pointer_locals {
            if body
                .occurrences
                .iter()
                .flat_map(|o| inputs(&o.syntax.expression))
                .filter(|p| p.local == *local)
                .count()
                > 1
            {
                return None;
            }
        }
    }
    let mut writes = 0;
    for row in &callee.occurrences {
        if row.callee.is_some() {
            return None;
        }
        if !row.syntax.destination.projection.is_empty() {
            if row.site.block != store.site.block
                || row.site.statement != store.site.statement
                || row.syntax.destination != store.site.place
            {
                return None;
            }
            writes += 1;
        }
        match &row.syntax.expression {
            Expression::Value { operand } => {
                if place(operand).is_some_and(|p| p.local == outer || !p.projection.is_empty()) {
                    return None;
                }
            }
            _ => return None,
        }
    }
    if writes != 1 {
        return None;
    }
    let mut calls = 0;
    let mut aggregates = 0;
    for row in &caller.occurrences {
        if !row.syntax.destination.projection.is_empty() {
            return None;
        }
        if let Some(target) = &row.callee {
            let at = |point: &super::super::ownership_evidence::Point| {
                point.block == Some(row.site.block) && point.statement == Some(row.site.statement)
            };
            if !((target == &SourceCallee::ForeignC("calloc".into()) && at(&source_eq.point))
                || (target == &SourceCallee::ForeignC("free".into()) && at(&free_eq.point))
                || (target == &SourceCallee::Local(candidate.call.callee.clone())
                    && row.site.block == candidate.call.block
                    && row.site.statement == candidate.call.statement))
            {
                return None;
            }
            calls += 1;
            continue;
        }
        match &row.syntax.expression {
            Expression::Borrow { .. }
                if candidate.formation.block == Some(row.site.block)
                    && candidate.formation.statement == Some(row.site.statement) => {}
            Expression::RawAddress { .. }
                if candidate.address.block == Some(row.site.block)
                    && candidate.address.statement == Some(row.site.statement) => {}
            Expression::Aggregate { .. } if row.syntax.destination == candidate.cell => {
                aggregates += 1;
            }
            Expression::Cast { cast, .. }
                if cast == "PtrToPtr"
                    || row.syntax.immediate_origin
                        == super::super::ownership_access::ImmediateOrigin::Null => {}
            Expression::Value { .. } => {}
            _ => return None,
        }
        for value in inputs(&row.syntax.expression) {
            if !value.projection.is_empty()
                && !(value.local == candidate.cell.local
                    && value.projection == store.site.place.projection[1..])
                && !matches!(row.syntax.expression, Expression::RawAddress { .. })
            {
                return None;
            }
            if value.local == candidate.cell.local
                && value.projection.is_empty()
                && !matches!(row.syntax.expression, Expression::Borrow { .. })
            {
                return None;
            }
        }
    }
    if calls != 3
        || aggregates != 1
        || field.null_stores.len() != 1
        || field.null_stores[0].place.local != candidate.cell.local
    {
        return None;
    }
    let arm = cell_effects::call_arm(facts, boundary, aliases)?;
    Some(Proof {
        candidate: candidate.clone(),
        source,
        free,
        store: store.equation,
        parameter_slot: format!("{}::_{}@d0", candidate.call.callee, outer),
        formal_output: Node {
            construction: candidate.call.construction,
            var: arm.formal.1,
        },
        legacy_output: Node {
            construction: candidate.call.construction,
            var: arm.legacy.1,
        },
    })
}

pub(crate) fn plan(
    facts: &Facts,
    fields: &mut [FieldProof],
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Vec<Decision> {
    let candidates = cell_effects::discover(facts);
    let chains: Vec<_> = fields
        .iter()
        .filter_map(|field| super::chain_permission::certify(facts, field, aliases))
        .collect();
    let mut result = Vec::new();
    for frame in facts
        .equations
        .iter()
        .filter(|e| e.operation == "guarded-original-cell-frame")
    {
        let guard = EquationId {
            construction: frame.point.construction,
            ordinal: frame.ordinal,
        };
        let proof = candidates
            .iter()
            .find(|c| c.formation == frame.point)
            .and_then(|c| {
                fields
                    .iter()
                    .find(|f| f.field_key == c.field_key)
                    .and_then(|f| effect(facts, c, f, aliases))
            });
        if let Some(proof) = &proof {
            let field = fields
                .iter_mut()
                .find(|f| f.field_key == proof.candidate.field_key)
                .unwrap();
            field.holds.retain(|h| h.reason != Pending::CallerCoverageC);
            field.input_stores[0].caller_coverage = CallerCoverage::CertifiedFirst;
        }
        let complete_chain = if proof.is_none() {
            chains
                .iter()
                .find(|chain| chain.put_guard == guard || chain.release_guard == guard)
                .cloned()
                .map(Box::new)
        } else {
            None
        };
        if let Some(chain) = &complete_chain {
            let field = fields
                .iter_mut()
                .find(|field| field.field_key == chain.put.field_key)
                .unwrap();
            field
                .holds
                .retain(|hold| hold.reason != Pending::CallerCoverageC);
            field.input_stores[0].caller_coverage = CallerCoverage::CertifiedChain;
        }
        result.push(Decision {
            guard,
            proof,
            complete_chain,
        });
    }
    result
}

#[cfg(test)]
mod tests {
    use super::super::{
        super::{SlotKind, ssa::constraint::Var},
        tests::{inspect, inspect_era5_frame},
    };
    const CODE: &str = r#"
unsafe extern "C" {fn calloc(n:usize,size:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Cell {ptr:*mut i32}
pub unsafe fn put(cell:*mut Cell,value:*mut i32){(*cell).ptr=value;}
pub unsafe fn f(){let owner=calloc(1,4) as *mut i32;let mut cell=Cell{ptr:0 as *mut i32};put(&mut cell,owner);free(cell.ptr as *mut core::ffi::c_void);}
"#;
    #[test]
    fn c04_first_permission_accepts_one_source_original_cell_and_caller_free() {
        let fixture = inspect_era5_frame(CODE);
        if fixture.kinds.get("Cell.ptr") != Some(&SlotKind::Owning) {
            eprintln!(
                "C04_PERMISSION_DIAGNOSTIC={}",
                serde_json::json!({
                    "origin":fixture.origin_json,"commit_trace":fixture.commit_trace,
                    "retirement":format!("{:?}",fixture.export.retirement_rounds),
                })
            );
        }
        for key in ["Cell.ptr", "f::owner", "put::value"] {
            fixture.assert_kind(key, SlotKind::Owning);
        }
        fixture.assert_kind("put::cell", SlotKind::Ref);
        let offset = fixture.origin_json["stack_entry_final"]["snapshot_offset"]
            .as_u64()
            .unwrap();
        let snapshot = fixture
            .export
            .ownership_licensing
            .as_ref()
            .unwrap()
            .iter()
            .find(|s| s.offset as u64 == offset)
            .unwrap();
        let facts = snapshot.metadata.facts();
        let candidate = super::super::cell_effects::discover(&facts)
            .into_iter()
            .next()
            .unwrap();
        let boundary = facts
            .boundary_substitutions
            .iter()
            .find(|b| {
                b.point.construction == candidate.call.construction
                    && b.ordinal == candidate.boundary
            })
            .unwrap();
        let arm = super::super::cell_effects::call_arm(
            &facts,
            boundary,
            snapshot.matched.guard_aliases(),
        )
        .unwrap();
        let owns = fixture.export.version_owns.as_ref().unwrap();
        assert!(owns[Var::from_u32(arm.formal.1)]);
        assert!(
            !owns[Var::from_u32(arm.legacy.1)],
            "native temporary final zero stays intact"
        );
        // The retained !g=>formal_out=legacy_out equation makes this contrast
        // an exact selected-g witness in this accepted model, without a solve.
        assert!(owns[Var::from_u32(arm.original.1)]);
    }
    #[test]
    fn c04_first_permission_holds_unattested_shared_partner_and_unknown_effect() {
        let fixture = inspect(CODE);
        fixture.assert_not_owning("Cell.ptr");
        for code in [
            CODE.replace("put(&mut cell,owner)","put(&cell as *const Cell as *mut Cell,owner)"),
            CODE.replace("free(cell.ptr as *mut core::ffi::c_void);","free(cell.ptr as *mut core::ffi::c_void);free(owner as *mut core::ffi::c_void);"),
            CODE.replace("pub unsafe fn put(cell:*mut Cell,value:*mut i32){","unsafe extern \"C\"{fn unknown(p:*mut i32);}\npub unsafe fn put(cell:*mut Cell,value:*mut i32){unknown(value);"),
            CODE.replace("pub unsafe fn put(cell:*mut Cell,value:*mut i32){","static mut KEEP:*mut i32=0 as *mut i32;\npub unsafe fn put(cell:*mut Cell,value:*mut i32){KEEP=value;"),
            format!("{CODE}\npub unsafe fn other(){{let mut n=2;let p=&mut n as *mut i32;let mut c=Cell{{ptr:0 as *mut i32}};put(&mut c,p);}}"),
        ] {inspect_era5_frame(&code).assert_not_owning("Cell.ptr");}
    }
    #[test]
    fn c04_first_permission_original_endpoints_are_hard_satisfiable() {
        use rustc_hir::{ItemKind, OwnerNode};

        use super::super::super::{
            a5_overlap::WholeProgramAttestation,
            construction::{CopyLendMode, construct_bo_into},
            crate_slots::CrateSlots,
            mutability_facts::MutFacts,
            origins::compute_origins,
            solver::KindSolver,
        };
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
                    "C04_FIRST_HARD_CORE={}",
                    serde_json::to_string(&labels).unwrap()
                );
            }
            assert_eq!(
                outcome,
                z3::SatResult::Sat,
                "all original endpoints before borrow replay"
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    fn with_permission(
        check: impl FnOnce(&super::super::facts::Facts, &super::super::super::solver::KindSolver) + Send,
    ) {
        use rustc_hir::{ItemKind, OwnerNode};

        use super::super::super::{
            a5_overlap::WholeProgramAttestation,
            construction::{CopyLendMode, construct_bo_into},
            crate_slots::CrateSlots,
            mutability_facts::MutFacts,
            origins::compute_origins,
            solver::KindSolver,
        };
        ::utils::compilation::run_compiler_on_str(CODE, move |tcx| {
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
            let solver = KindSolver::new(&slots);
            construct_bo_into(
                &program,
                &slots,
                &origins,
                &mutability,
                &solver,
                CopyLendMode::Baseline,
            )
            .unwrap();
            super::super::super::coherence::constrain_field_ownership(&solver, &slots, &program);
            let facts = solver.ownership_facts().unwrap();
            check(&facts, &solver);
        })
        .unwrap_or_else(|error| error.raise());
    }
    #[test]
    fn c04_first_permission_requires_current_endpoint_coordinates_despite_cached_proof() {
        with_permission(|facts, solver| {
            let decision = facts
                .licensing
                .as_ref()
                .unwrap()
                .first_permissions
                .iter()
                .find(|row| row.proof.is_some())
                .unwrap();
            let proof = decision.proof.as_ref().unwrap();
            solver.constrain_first_permissions(facts).unwrap();
            for endpoint in [proof.source, proof.free] {
                let mut broken = facts.clone();
                let row = broken
                    .equations
                    .iter_mut()
                    .find(|row| {
                        row.point.construction == endpoint.construction
                            && row.ordinal == endpoint.ordinal
                    })
                    .unwrap();
                row.variables[0] = proof.legacy_output.var;
                assert!(
                    solver.constrain_first_permissions(&broken).is_err(),
                    "retained cached permission accepted changed endpoint {endpoint:?}"
                );
            }
        });
    }
    #[test]
    fn c04_first_permission_withdraws_with_either_original_endpoint() {
        with_permission(|facts, solver| {
            let decision = facts
                .licensing
                .as_ref()
                .unwrap()
                .first_permissions
                .iter()
                .find(|row| row.proof.is_some())
                .unwrap();
            let proof = decision.proof.as_ref().unwrap();
            let predicate = |id| {
                facts
                    .guards
                    .iter()
                    .find(|row| row.equation == id)
                    .unwrap()
                    .predicate
                    .clone()
            };
            let guard = predicate(decision.guard);
            assert_eq!(
                solver.check_with_assumptions(&[
                    guard.clone(),
                    predicate(proof.source),
                    predicate(proof.free)
                ]),
                z3::SatResult::Sat
            );
            for endpoint in [proof.source, proof.free] {
                assert_eq!(
                    solver.check_with_assumptions(&[guard.clone(), !predicate(endpoint)]),
                    z3::SatResult::Unsat,
                    "withdrawn endpoint still permits its original-cell grant"
                );
            }
        });
    }
}
