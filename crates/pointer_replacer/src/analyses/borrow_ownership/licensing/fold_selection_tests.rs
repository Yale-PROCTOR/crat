//! Pending fold custody in an actual synthetic model. The input is never executed.

use std::rc::Rc;

use rustc_hir::{ItemKind, OwnerNode};

use super::{
    super::{
        a5_overlap::WholeProgramAttestation, coherence,
        construction::construct_bo_into_a16_refined, crate_slots::CrateSlots, export,
        mutability_facts::MutFacts, origins::compute_origins, solver::KindSolver,
    },
    model_selection::Selection,
};

#[test]
fn gf07_pending_fold_is_held_and_selected_from_the_same_model_without_export() {
    const CODE: &str = r#"
pub struct Node { child: *mut Node }
pub unsafe fn identity(node: *mut Node) -> *mut Node { node }
pub unsafe fn caller(node: *mut Node) -> *mut Node { identity((*node).child) }
"#;
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
        let _world =
            super::stack_entry::enter_world(Some(WholeProgramAttestation::FrozenBenchmarkGraph));
        assert!(!export::capturing(), "selection must not require BoExport");
        let solver = KindSolver::new(&slots);
        let (construction, _) =
            construct_bo_into_a16_refined(&program, &slots, &origins, &mutability, &solver)
                .expect("synthetic fold construction");
        coherence::constrain_field_ownership(&solver, &slots, &program);
        let facts = solver.ownership_facts().expect("this solver's facts");
        let [declaration] = facts
            .fold_declarations
            .as_deref()
            .expect("explicit fold declaration inventory")
        else {
            panic!("exactly one projected child-call declaration")
        };
        let guard = declaration.guard;
        let bindings: Vec<_> = facts
            .guards
            .iter()
            .filter(|g| g.equation == guard)
            .collect();
        let [binding] = bindings.as_slice() else {
            panic!("one actual predicate for the declared guard")
        };
        assert_eq!(
            solver.check_with_assumptions(&[binding.predicate.clone()]),
            z3::SatResult::Unsat,
            "caller closure is pending, so forcing the fold must fail"
        );
        assert_eq!(
            solver.check_with_assumptions(&[!&binding.predicate]),
            z3::SatResult::Sat,
            "the held fold retains a satisfiable ordinary model"
        );
        solver
            .model_kinds_relaxing_reporting(&construction.selectors)
            .expect("ordinary model with the pending fold held false");
        let selected = solver
            .original_cell_selection()
            .expect("selection from the actual successful model read");
        let equal_but_distinct = Rc::new((*facts).clone());
        assert_eq!(
            selected.value(&equal_but_distinct, guard),
            None,
            "equal metadata does not establish construction identity"
        );
        let unavailable = Selection::from_model(facts.clone(), |_| None);
        assert_eq!(
            unavailable.value(&facts, guard),
            None,
            "missing evaluation must not default to false"
        );
        assert!(!export::capturing());
        assert_eq!(
            selected.value(&facts, guard),
            Some(false),
            "capture the actual held-fold value from this model"
        );
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn gf07_accepting_round_exports_the_same_model_pending_fold_value() {
    let fixture = super::tests::inspect_era5_frame(
        r#"
pub struct Node{child:*mut Node}
pub unsafe fn identity(node:*mut Node)->*mut Node{node}
pub unsafe fn caller(node:*mut Node)->*mut Node{identity((*node).child)}
"#,
    );
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    let accepted = fixture
        .export
        .stack_entry_final
        .as_ref()
        .expect("actual accepting round");
    let stamp = accepted.stamp();
    let values = stamp["fold_guards"]
        .as_array()
        .expect("same-model fold selection stamp");
    assert_eq!(values.len(), 1);
    assert_eq!(values[0][1], false);
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == accepted.snapshot_offset)
        .unwrap();
    let declaration = &snapshot.metadata.fold_declarations.as_ref().unwrap()[0];
    assert_eq!(
        values[0][0],
        serde_json::to_value(declaration.guard).unwrap()
    );
}

#[test]
fn gf07_native_accepted_export_rejects_missing_and_forged_fold_selections() {
    use std::collections::BTreeMap;

    use super::super::{
        SlotKind,
        a5_overlap::A5Mode,
        construction::solve_bo_a5_config_reporting,
        origin_evidence,
        portable_export::{self, ExportFamily},
        slot_key,
        slots::SlotOwner,
        solver::SlotRef,
    };

    const CODE: &str = r#"
pub struct Node { child: *mut Node }
pub unsafe fn identity(node: *mut Node) -> *mut Node { node }
pub unsafe fn caller(node: *mut Node) -> *mut Node { identity((*node).child) }
"#;
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
        let (verified, captured) = export::with_bo_export(|| {
            solve_bo_a5_config_reporting(
                &program,
                &slots,
                &origins,
                &mutability,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("accepted synthetic analysis with pending folds")
        });
        let origin = origin_evidence::collect(&program, &slots, &origins, Some(&captured));
        let portable = portable_export::collect(&program, &slots, &captured)
            .expect("native portable export from this analysis");
        let model: BTreeMap<String, String> = verified
            .model
            .iter()
            .map(|(&slot, &kind)| {
                let key = match slot {
                    SlotRef::Local(function, id) => {
                        let slot = slots.fn_local_slots[&function].slot(id);
                        let SlotOwner::Local(local) = slot.owner else {
                            panic!("local slot owner")
                        };
                        slot_key::local_key(tcx, function, local.as_usize(), slot.depth)
                    }
                    SlotRef::Field(id) => {
                        let slot = slots.field_slots.slot(id);
                        let SlotOwner::Field(field) = slot.owner else {
                            panic!("field slot owner")
                        };
                        slot_key::field_key(tcx, field.struct_did, field.field_index, slot.depth)
                    }
                };
                let kind = match kind {
                    SlotKind::Raw => "raw",
                    SlotKind::Ref => "ref",
                    SlotKind::Owning => "owning",
                };
                (key, kind.to_owned())
            })
            .collect();
        let accepted = origin
            .stack_entry_final
            .as_ref()
            .expect("actual accepting round");
        let pending = accepted
            .fold_guards
            .as_ref()
            .expect("new-frame fold selections");
        assert_eq!(pending.len(), 1);
        assert!(!pending[0].1, "the actual selected fold remains held");
        assert_eq!(
            super::stack_export::validate(&origin, &portable, &model),
            Ok(())
        );

        for (forge_true, expected) in [
            (false, "fold selection coverage differs"),
            (true, "pending fold selected without closure"),
        ] {
            let mut changed = origin.clone();
            let accepted = changed.stack_entry_final.as_mut().unwrap();
            let selections = accepted.fold_guards.as_mut().unwrap();
            if forge_true {
                selections[0].1 = true;
            } else {
                selections.clear();
            }
            let mut mirrored = portable.clone();
            mirrored
                .families
                .get_mut(&ExportFamily::RetirementFinal)
                .expect("retirement final family")
                .records[0]
                .fields
                .insert("stack_entry_acceptance".into(), accepted.stamp());
            assert_eq!(
                super::stack_export::validate(&changed, &mirrored, &model),
                Err(expected.to_owned()),
                "mirroring the stamp must not authenticate altered fold custody"
            );
        }
        let mut changed = origin.clone();
        let accepted = changed.stack_entry_final.as_mut().unwrap();
        accepted.fold_values = None;
        let mut mirrored = portable.clone();
        mirrored
            .families
            .get_mut(&ExportFamily::RetirementFinal)
            .unwrap()
            .records[0]
            .fields
            .insert("stack_entry_acceptance".into(), accepted.stamp());
        assert_eq!(
            super::stack_export::validate(&changed, &mirrored, &model),
            Err("fold custody availability differs".into()),
            "mirrored acceptance cannot omit the new-frame custody inventory"
        );
    })
    .unwrap_or_else(|error| error.raise());
}
