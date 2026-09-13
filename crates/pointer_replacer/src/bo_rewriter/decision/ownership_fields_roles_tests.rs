//! R365 native role witnesses reuse the two existing heman reductions exactly.
//! The caller and formal kinds come from the same real compiler/solver result.
//! Admission REDs established actual Owning formals. Their terminal raw form
//! now licenses the first-rule interface while preserving the model label.

use std::collections::BTreeSet;

use bo::ownership_fields::{emission::Kind, lend::FormalForm};
use rustc_middle::mir::Local;

use super::ownership_fields_hook::{Hold, native_lend_formal};
use crate::bo_rewriter as bo;

fn require_owning_formal_lend(callee_name: &str, calls: &str, expected_calls: usize) {
    let source = bo::ownership_fields_native_tests::native_fixture_source(callee_name, calls);
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let (table, ctx) = bo::decide_table_with_ctx_config(
            tcx,
            Some((
                bo::A5Mode::PreciseReplay,
                Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("real native fixture model, no injected kinds");
        let program = bo::collect_program(tcx);
        let prepared = bo::prepare_plan_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans).unwrap();
        let definition = |name: &str| {
            let matches: Vec<_> = program.functions.iter().copied()
                .filter(|function| tcx.def_path_str(function.to_def_id()) == name)
                .collect();
            assert_eq!(matches.len(), 1, "exact fixture definition {name}");
            matches[0]
        };
        let caller = definition("transform_to_coordfield");
        let callee = definition(callee_name);
        let mut observations = Vec::new();
        for site in &ctx.raw_boundary_sites.sites {
            if site.callee_local != Some(callee) {
                continue;
            }
            assert_eq!(site.key.caller, tcx.def_path_str(caller.to_def_id()));
            assert_eq!(site.key.callee.path, tcx.def_path_str(callee.to_def_id()));
            let node = site.node.expect("exact native source root");
            assert_eq!(node.0, caller);
            let subjects: Vec<_> = table.entries.iter()
                .filter(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
                .collect();
            assert_eq!(subjects.len(), 1, "unique subject for captured argument");
            let subject = &subjects[0].0;
            let argument = site.key.argument_index;
            assert!(argument < 2, "the reused reduction has two formals");
            assert_eq!(subject.param_name.as_deref(), Some(if argument == 0 { "pl1" } else { "pl2" }));
            let actual_slot = ctx.slots.fn_local_slots[&caller]
                .slot_for_local_depth(subject.local, 0).expect("actual pointer slot");
            let formal_local = Local::from_usize(argument + 1);
            let formal_slot = ctx.slots.fn_local_slots[&callee]
                .slot_for_local_depth(formal_local, 0).expect("exact formal pointer slot");
            let actual = ctx.model.get(&bo::SlotRef::Local(caller, actual_slot)).copied();
            let formal = ctx.model.get(&bo::SlotRef::Local(callee, formal_slot)).copied();
            observations.push((site.key.block, site.key.statement_index, argument, subject.local.as_u32(), formal_local.as_u32(), actual_slot, formal_slot, actual, formal));
        }
        observations.sort_by_key(|row| (row.0, row.1, row.2));
        let mut seen = BTreeSet::new();
        for row in &observations {
            let (block, statement, argument, actual_local, formal_local, actual_slot, formal_slot, actual, formal) = row;
            let emitted = super::ownership_fields_formal::resolve(tcx, &ctx.slots, &ctx.model, &table, &prepared.plan.class_finalization, callee, *argument).unwrap();
            let disposition = emitted.emitted();
            println!("OWNFIELDS-ROLE caller={} call=bb{block}:s{statement} callee={} argument={argument} actual_local={actual_local} actual_slot={actual_slot:?} actual_kind={actual:?} formal_local={formal_local} formal_slot={formal_slot:?} formal_kind={formal:?} emitted={disposition:?}", tcx.def_path_str(caller.to_def_id()), tcx.def_path_str(callee.to_def_id()));
            assert!(seen.insert((*block, *statement, *argument)), "duplicate native edge");
            assert_eq!(*actual, Some(bo::SlotKind::Owning), "existing caller premise remains real");
            assert_eq!(*formal, Some(bo::SlotKind::Owning), "measured formal kind, never overridden");
            assert_eq!(emitted.emitted(), FormalForm::MutableRaw);
            assert!(matches!(native_lend_formal(tcx, &ctx.slots, &ctx.model, callee, *argument, &emitted), Ok(Kind::Owning)), "model label is recorded while the emitted raw formal is lendable");
        }
        assert_eq!(observations.len(), expected_calls * 2, "complete two-buffer edge inventory");
        let call_sites: BTreeSet<_> = seen.iter().map(|(block, statement, _)| (*block, *statement)).collect();
        assert_eq!(call_sites.len(), expected_calls);
        for (block, statement) in call_sites {
            assert!(seen.contains(&(block, statement, 0)) && seen.contains(&(block, statement, 1)));
        }
        // Native effects remain separate from terminal form and model kind.
        let effects = super::ownership_fields_effects::NativeEffects::derive(&program);
        for argument in 0..2 {
            assert!(effects.certify(callee, argument).is_ok());
        }
        let emitted = super::ownership_fields_formal::resolve(tcx, &ctx.slots, &ctx.model, &table, &prepared.plan.class_finalization, callee, 0).unwrap();
        assert!(matches!(native_lend_formal(tcx, &ctx.slots, &ctx.model, callee, usize::MAX, &emitted), Err(Hold::Identity)));
    }).expect("native role fixture compiles");
}

#[test]
fn native_two_buffer_lend_uses_actual_raw_formal_and_records_owning_kind() {
    require_owning_formal_lend("edt_with_payload", "edt_with_payload(pl1,pl2);", 1);
}

#[test]
fn native_repeated_call_lend_uses_actual_raw_formal_and_records_owning_kind() {
    require_owning_formal_lend("edt", "edt(pl1,pl2);*pl1=*pl2;edt(pl1,pl2);", 2);
}
