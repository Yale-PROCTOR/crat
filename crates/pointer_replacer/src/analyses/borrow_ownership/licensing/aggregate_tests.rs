//! Aggregate transport laws over real construction facts, without solving.

use std::collections::BTreeSet;

use rustc_hir::{ItemKind, OwnerNode};

use super::{
    super::{
        construction::{CopyLendMode, construct_bo_into},
        crate_slots::CrateSlots,
        execution_guard,
        export::{self, ProjKey},
        mutability_facts::MutFacts,
        origins::compute_origins,
        ownership_access::{Expression, OperandSyntax},
        ownership_occurrence::{self, Availability, Binding, PathStep},
        solver::KindSolver,
    },
    facts::Facts,
};
use crate::utils::rustc::RustProgram;

fn present<T>(value: &Availability<T>) -> &T {
    match value {
        Availability::Present(value) => value,
        Availability::Missing(reason) => panic!("required aggregate correspondence: {reason}"),
    }
}

fn check_binding(facts: &Facts, binding: &Binding) {
    let consume = facts
        .consumes
        .iter()
        .find(|row| row.ordinal == binding.consume)
        .expect("binding identifies an actual consume");
    assert_eq!(binding.local, consume.local);
    assert_eq!(binding.projection, consume.projection);
    assert_eq!(binding.ssa_use, consume.ssa_use);
    assert_eq!(binding.ssa_def, consume.ssa_def);
    assert!(binding.ssa_use.is_some());
    assert!(binding.ssa_def.is_some());
    let base = present(&consume.base);
    let projected = present(&consume.projected);
    assert!(projected.use_start <= binding.use_var && binding.use_var < projected.use_end);
    assert!(projected.def_start <= binding.def_var && binding.def_var < projected.def_end);
    let offset = binding.use_var - base.use_start;
    assert_eq!(offset, binding.def_var - base.def_start);
    assert_eq!(
        present(&consume.pointer_paths)[offset as usize],
        binding.path
    );
}

#[test]
fn t07_struct_aggregate_transfers_each_field_without_framing_its_sibling() {
    ::utils::compilation::run_compiler_on_str(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub struct Holder { left: *mut i32, right: *mut i32 }
pub unsafe fn release(h: *mut Holder) {
    free((*h).left);
    free((*h).right);
}
pub unsafe fn run() {
    let p = malloc(4);
    let q = malloc(4);
    let mut h = Holder { left: p, right: q };
    release(&mut h);
}
"#,
        |tcx| {
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
            let program = RustProgram { tcx, functions, structs };
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let mutability = MutFacts::from_program(&program);
            let model_entries = execution_guard::model_entries();
            assert!(!export::capturing());
            let solver = KindSolver::new(&slots);
            construct_bo_into(
                &program, &slots, &origins, &mutability, &solver, CopyLendMode::Baseline,
            ).expect("actual aggregate construction");
            assert_eq!([
                solver.check_sat_count(), solver.hard_check_count(),
                solver.optimize_materialization_count(), solver.lazy_plain_hard_check_count(),
                solver.lazy_tracked_recheck_count(), solver.lazy_plain_materialization_count(),
            ], [0; 6]);
            assert_eq!(execution_guard::model_entries(), model_entries);
            assert!(!export::capturing());
            let facts = solver.ownership_facts().expect("actual ownership facts");
            assert_eq!(facts.constructions, 1);
            assert_eq!(facts.equations.iter().filter(|row| row.operation == "source").count(), 2);
            assert_eq!(facts.equations.iter().filter(|row| row.operation == "sink").count(), 2);

            let aggregates: Vec<_> = facts.source_occurrences.values().flatten().filter(|row| {
                matches!(&row.syntax.expression,
                    Expression::Aggregate { structure: Some(name), .. } if name == "Holder")
            }).collect();
            assert_eq!(aggregates.len(), 1, "one exact Holder initializer");
            let aggregate = aggregates[0];
            let Expression::Aggregate { operands, .. } = &aggregate.syntax.expression else {
                unreachable!()
            };
            assert_eq!(operands.len(), 2);
            let equations: Vec<_> = facts.equations.iter().filter(|row| {
                row.point.function.as_deref() == Some(aggregate.site.function.as_str())
                    && row.point.block == Some(aggregate.site.block)
                    && row.point.statement == Some(aggregate.site.statement)
            }).collect();
            let transfers: BTreeSet<_> = equations.iter()
                .filter_map(|row| row.transfer.as_ref()).collect();
            assert_eq!(transfers.len(), 2,
                "both aggregate fields need real transfer laws, not consume-only observations; syntax={:?}; consumes={:?}; registrations={:?}; statements={:?}",aggregate.syntax,
                facts.consumes.iter().filter(|row|row.point.function.as_deref()==Some(aggregate.site.function.as_str()) && row.point.block==Some(aggregate.site.block) && row.point.statement==Some(aggregate.site.statement)).collect::<Vec<_>>(),
                facts.call_arg_registrations.iter().filter(|r|r.point.function.as_deref()==Some("run")).collect::<Vec<_>>(),facts.source_occurrences.get("run"));

            let mut destination_uses = BTreeSet::new();
            let mut destination_defs = BTreeSet::new();
            let mut source_uses = BTreeSet::new();
            let mut destination_ssa = None;
            for (index, name) in ["left", "right"].into_iter().enumerate() {
                let path = vec![PathStep::Field {
                    structure: "Holder".into(), index: index as u32, name: name.into(),
                }];
                let transfer = transfers.iter().copied().find(|transfer| {
                    matches!(&transfer.destination, Availability::Present(binding) if binding.path == path)
                }).unwrap_or_else(|| panic!("missing exact {name} aggregate field transfer"));
                let destination = present(&transfer.destination);
                let source = present(&transfer.source);
                check_binding(&facts, destination);
                check_binding(&facts, source);
                assert_eq!(destination.local, aggregate.syntax.destination.local);
                let mut projection = aggregate.syntax.destination.projection.clone();
                projection.push(ProjKey::Field(index as u32));
                assert_eq!(destination.projection, projection);
                assert_eq!(destination.pointer_depth, 0);
                assert_eq!(destination.use_var, transfer.destination_use);
                assert_eq!(destination.def_var, transfer.destination_def);
                assert_eq!(source.use_var, transfer.source_use);
                assert_eq!(source.def_var, transfer.source_def);
                let ssa = (destination.ssa_use, destination.ssa_def);
                if let Some(previous) = destination_ssa { assert_eq!(ssa, previous); }
                destination_ssa = Some(ssa);
                let (operand, by_move) = match &operands[index] {
                    OperandSyntax::Copy { place } => (place, false),
                    OperandSyntax::Move { place } => (place, true),
                    OperandSyntax::Constant { .. } => panic!("allocation operand must be a place"),
                };
                // T07 correction: these MIR temporaries have ordinary SSA.
                // The missing consumes came from skipped aggregate operand
                // visits in initial definitions, not call-proxy elimination.
                assert_eq!(source.local, operand.local);
                assert_eq!(source.projection, operand.projection);
                let source_consume = facts.consumes.iter().find(|row| row.ordinal == source.consume).unwrap();
                assert_eq!(source_consume.point, equations[0].point);
                assert!(!facts.call_arg_registrations.iter().any(|row| {
                    row.point.construction == source_consume.point.construction
                        && row.point.function == source_consume.point.function
                        && row.proxy_local == operand.local
                }), "aggregate operands must use direct SSA, with zero call-proxy registrations");
                assert_eq!(transfer.by_move, by_move);
                assert!(destination_uses.insert(transfer.destination_use));
                assert!(destination_defs.insert(transfer.destination_def));
                assert!(source_uses.insert(transfer.source_use));
                let has = |operation: &str, variables: &[u32], value: Option<bool>| {
                    equations.iter().any(|row| row.operation == operation
                        && row.variables == variables && row.value == value
                        && row.transfer.as_ref() == Some(transfer))
                };
                assert!(has("assume", &[transfer.destination_use], Some(false)),
                    "destination old-value-zero must remain for {name}");
                if by_move {
                    assert!(has("equal", &[transfer.destination_def, transfer.source_use], None));
                    assert!(has("assume", &[transfer.source_def], Some(false)));
                } else {
                    assert!(has("linear", &[
                        transfer.destination_def, transfer.source_def, transfer.source_use,
                    ], None));
                }
                assert!(!equations.iter().any(|row| row.operation == "equal"
                    && (row.variables == [transfer.destination_use, transfer.destination_def]
                        || row.variables == [transfer.destination_def, transfer.destination_use])),
                    "initializing the sibling must not frame {name}'s old zero onto its new owner");
            }
            let function = aggregate.site.function.as_str();
            let consumes: Vec<_> = facts.consumes.iter().filter(|row| row.point.function.as_deref() == Some(function)).cloned().collect();
            let function_equations: Vec<_> = facts.equations.iter().filter(|row| row.point.function.as_deref() == Some(function)).cloned().collect();
            ownership_occurrence::validate(function, &consumes, &function_equations)
                .expect("aggregate transfer uses exact same-site SSA consumes");
        },
    ).unwrap_or_else(|error| error.raise());
}
