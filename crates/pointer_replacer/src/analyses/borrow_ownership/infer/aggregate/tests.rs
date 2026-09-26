//! Constructed emission obligations, not observed real-program defects.
//! Rust lowers `*out = Outer { inner }` through a local aggregate with a valid
//! transfer. These tests deliberately supply narrower or absent destination
//! ranges to exercise the helper's held branches using real compiler types.

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Rvalue, StatementKind};

use super::*;
use crate::{
    analyses::borrow_ownership::{
        BO_PRECISION, BoOwnershipProbe, CrateCtxt,
        crate_slots::CrateSlots,
        execution_guard, initial_crate_inter_ctxt,
        licensing::facts,
        ownership_evidence,
        solver::{BoOwnDatabase, KindSolver},
    },
    utils::rustc::RustProgram,
};

fn check_held_source_frames(destination_present: bool) {
    ::utils::compilation::run_compiler_on_str(
        r#"
pub struct Inner { payload: *mut i32 }
pub struct Outer { inner: *mut Inner }
pub unsafe fn initialize(out: *mut Outer, inner: *mut Inner) {
    *out = Outer { inner };
}
"#,
        move |tcx| {
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
            let function = functions[0];
            let program = RustProgram {
                tcx,
                functions,
                structs,
            };
            let body_ref = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let body = &*body_ref;
            let (block, statement, kind, operand) = body
                .basic_blocks
                .iter_enumerated()
                .find_map(|(block, data)| {
                    data.statements
                        .iter()
                        .enumerate()
                        .find_map(|(index, statement)| {
                            let StatementKind::Assign(box (_, Rvalue::Aggregate(kind, operands))) =
                                &statement.kind
                            else {
                                return None;
                            };
                            let AggregateKind::Adt(did, ..) = kind.as_ref() else { return None };
                            (tcx.item_name(*did).as_str() == "Outer").then(|| {
                                (block, index, kind.as_ref(), operands.iter().next().unwrap())
                            })
                        })
                })
                .expect("real compiler Outer aggregate");
            let out = body.args_iter().next().expect("out parameter");
            let destination_place = Place::from(out).project_deeper(&[PlaceElem::Deref], tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let mut database = BoOwnDatabase::new(solver.optimize(), solver.tracker());
            let _facts_scope = database.activate_facts();
            let _construction_scope = ownership_evidence::construction();
            let mut var_gen = Gen::new();
            let global = GlobalAssumptions::new(&crate_ctxt, &mut var_gen, &mut database);
            let inter = initial_crate_inter_ctxt(&crate_ctxt, &mut var_gen, &mut database);

            // These are explicit test ranges, allocated by the real database.
            // They are not asserted to be this body's emitted SSA consumes.
            let source = Consume {
                r#use: database.new_vars(&mut var_gen, 2),
                def: database.new_vars(&mut var_gen, 2),
            };
            let destination = destination_present.then(|| Consume {
                r#use: database.new_vars(&mut var_gen, 1),
                def: database.new_vars(&mut var_gen, 1),
            });
            let copy_lend_guards = FxHashMap::default();
            let _function_scope = ownership_evidence::function(|| tcx.def_path_str(function));
            let mut inference = InferCtxt::<BoOwnershipProbe>::new(
                &crate_ctxt,
                BO_PRECISION,
                body,
                &mut database,
                &mut var_gen,
                &inter,
                &global,
                &copy_lend_guards,
            );
            let _location_scope =
                ownership_evidence::location("statement", block.as_u32(), Some(statement));
            let first_equation = facts::read(|facts| facts.equations.len()).unwrap();
            let model_entries = execution_guard::model_entries();
            inference.aggregate(
                body,
                destination_place,
                kind,
                destination,
                &[(operand, Some(source.clone()))],
            );
            let equations =
                facts::read(|facts| facts.equations[first_equation..].to_vec()).unwrap();
            for (before, after) in source.r#use.zip(source.def) {
                assert!(
                    equations
                        .iter()
                        .any(|equation| equation.operation == "equal"
                            && (equation.variables == [before.as_u32(), after.as_u32()]
                                || equation.variables == [after.as_u32(), before.as_u32()])),
                    "held aggregate must frame consumed source {before:?} -> {after:?}"
                );
            }
            assert!(
                equations.iter().all(|equation| equation.transfer.is_none()),
                "held emission must not claim a completed field transfer"
            );
            assert_eq!(
                [
                    solver.check_sat_count(),
                    solver.hard_check_count(),
                    solver.optimize_materialization_count(),
                    solver.lazy_plain_hard_check_count(),
                    solver.lazy_tracked_recheck_count(),
                    solver.lazy_plain_materialization_count(),
                ],
                [0; 6]
            );
            assert_eq!(execution_guard::model_entries(), model_entries);
        },
    )
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn t07_constructed_width_hold_frames_every_consumed_source_depth() {
    check_held_source_frames(true);
}

#[test]
fn t07_constructed_missing_destination_frames_every_consumed_source_depth() {
    check_held_source_frames(false);
}
