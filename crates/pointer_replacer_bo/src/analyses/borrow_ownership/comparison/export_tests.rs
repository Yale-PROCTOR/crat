//! Compiled Phase-E export controls: occurrences and actual eager guards.

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{BinOp, RETURN_PLACE, Rvalue, StatementKind};

use super::{ComparisonDisposition, ComparisonOperand, ComparisonSite, GuardRule};
use crate::{
    analyses::borrow_ownership::{
        construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
        crate_slots::CrateSlots,
        export::{self, BoExport, PlaceKey},
        mutability_facts::MutFacts,
        origins::compute_origins,
        resolve::{ResolvedSlot, resolve_place},
        slot_key,
        slots::SlotOwner,
        solver::{KindSolver, SlotRef},
    },
    utils::rustc::RustProgram,
};

fn canonical(program: &RustProgram<'_>, slots: &CrateSlots, reference: SlotRef) -> String {
    match reference {
        SlotRef::Local(function, id) => {
            let slot = slots.fn_local_slots[&function].slot(id);
            let SlotOwner::Local(local) = slot.owner else { unreachable!() };
            slot_key::local_key(program.tcx, function, local.as_usize(), slot.depth)
        }
        SlotRef::Field(id) => {
            let slot = slots.field_slots.slot(id);
            let SlotOwner::Field(field) = slot.owner else { unreachable!() };
            slot_key::field_key(program.tcx, field.struct_did, field.field_index, slot.depth)
        }
    }
}

fn inspect(code: &str, check: impl Fn(&RustProgram<'_>, &CrateSlots, &BoExport) + Sync) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
        let facts = MutFacts::from_program(&program);
        let run = || {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("shared construction");
            let model = verify_bo_construction_counting(
                &program,
                &slots,
                &origins,
                &solver,
                &construction,
                &facts,
            )
            .0
            .expect("accepted comparison export fixture");
            (
                model,
                construction.stats,
                construction.selectors.keys().to_vec(),
            )
        };
        assert!(!export::capturing());
        let plain = run();
        let (captured, ledger) = export::with_bo_export(run);
        assert!(!export::capturing());
        assert_eq!(
            captured.0, plain.0,
            "capture must preserve the whole final model"
        );
        assert_eq!(
            captured.1, plain.1,
            "capture must preserve ownership emission statistics"
        );
        assert_eq!(
            captured.2, plain.2,
            "capture must preserve exact T2 selector keys"
        );
        check(&program, &slots, &ledger);
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_cmp_export_records_exact_equality_operands_without_a_comparison_cause() {
    inspect(
        "pub unsafe fn f(p: *const u8, q: *const u8) -> bool { p == q }",
        |program, slots, export| {
            let function = *program
                .functions
                .iter()
                .find(|function| program.tcx.item_name(function.to_def_id()).as_str() == "f")
                .unwrap();
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let mut actual = Vec::new();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for (statement, statement_data) in data.statements.iter().enumerate() {
                    let StatementKind::Assign(box (_, Rvalue::BinaryOp(BinOp::Eq, operands))) =
                        &statement_data.kind
                    else {
                        continue;
                    };
                    if !operands.0.ty(&*body, program.tcx).is_any_ptr()
                        || !operands.1.ty(&*body, program.tcx).is_any_ptr()
                    {
                        continue;
                    }
                    let operands = [&operands.0, &operands.1]
                        .into_iter()
                        .map(|operand| {
                            let place = operand.place();
                            let slot = place
                                .and_then(|place| {
                                    resolve_place(slots, function, &body, place, 0, None)
                                })
                                .map(|resolved| {
                                    canonical(
                                        program,
                                        slots,
                                        match resolved {
                                            ResolvedSlot::Local(id) => SlotRef::Local(function, id),
                                            ResolvedSlot::Field(id) => SlotRef::Field(id),
                                        },
                                    )
                                });
                            ComparisonOperand {
                                place: place.map(PlaceKey::from_place),
                                slot,
                            }
                        })
                        .collect();
                    actual.push(ComparisonSite {
                        function: program.tcx.def_path_str(function.to_def_id()),
                        block: block.as_u32(),
                        statement,
                        operator: "Eq".to_owned(),
                        operands,
                    });
                }
            }
            assert_eq!(actual.len(), 1, "one real pointer equality in original MIR");
            assert_eq!(actual[0].operands.len(), 2);
            assert!(
                actual[0]
                    .operands
                    .iter()
                    .all(|operand| operand.place.is_some() && operand.slot.is_some())
            );
            let recorded = export
                .comparisons
                .as_ref()
                .expect("comparison ledger captured");
            assert_eq!(
                recorded.sites, actual,
                "site, operator, operand order and canonical keys"
            );
            assert_eq!(
                recorded.disposition,
                ComparisonDisposition::NoComparisonCauseIdentified
            );
            assert!(
                recorded.guards.is_empty(),
                "pointer equality does not create an eager Ref guard"
            );
        },
    );
}

#[test]
fn e5_cmp_export_opaque_return_records_its_actual_no_borrow_origin_guard() {
    const CODE: &str = r#"
unsafe extern "C" { fn op(p: *mut u8) -> *mut u8; }
pub unsafe fn f(p: *mut u8) -> *mut u8 {
    let q = op(p);
    let _comparison = q == p;
    q
}
"#;
    inspect(CODE, |program, slots, export| {
        let function = *program
            .functions
            .iter()
            .find(|function| program.tcx.item_name(function.to_def_id()).as_str() == "f")
            .unwrap();
        let id = slots.fn_local_slots[&function]
            .slot_for_local_depth(RETURN_PLACE, 0)
            .expect("registered pointer return");
        let return_key = canonical(program, slots, SlotRef::Local(function, id));
        let recorded = export
            .comparisons
            .as_ref()
            .expect("comparison ledger captured");
        assert_eq!(recorded.sites.len(), 1);
        assert_eq!(
            recorded.sites[0].function,
            program.tcx.def_path_str(function.to_def_id())
        );
        assert_eq!(recorded.sites[0].operator, "Eq");
        assert_eq!(
            recorded.disposition,
            ComparisonDisposition::NoComparisonCauseIdentified
        );
        assert_eq!(
            recorded
                .guards
                .iter()
                .filter(|guard| guard.slot == return_key && guard.rule == GuardRule::NoBorrowOrigin)
                .count(),
            1,
            "the opaque return's actual eager guard is independent of its comparison"
        );
    });
}

#[test]
fn e5_cmp_export_distinguishes_opaque_field_guards_from_null_evidence() {
    const PREFIX: &str = "#[repr(C)] pub struct Holder { pub value: *mut u8 } unsafe extern \"C\" { fn op() -> *mut u8; }";
    for (value, opaque) in [("op()", true), ("core::ptr::null_mut()", false)] {
        let code =
            format!("{PREFIX} pub unsafe fn f(out: *mut Holder) {{ (*out).value = {value}; }}");
        inspect(&code, |program, slots, export| {
            assert_eq!(slots.field_slots.len(), 1, "one actual pointer field");
            let structure = program
                .structs
                .iter()
                .copied()
                .find(|structure| program.tcx.item_name(structure.to_def_id()).as_str() == "Holder")
                .unwrap();
            let field = program
                .tcx
                .adt_def(structure)
                .all_fields()
                .enumerate()
                .find(|(_, field)| field.name.as_str() == "value")
                .unwrap()
                .0;
            let field_key = slot_key::field_key(program.tcx, structure, field, 0);
            let recorded = export
                .comparisons
                .as_ref()
                .expect("guard ledger captured without a comparison");
            assert!(recorded.sites.is_empty());
            assert_eq!(
                recorded.disposition,
                ComparisonDisposition::NoComparisonCauseIdentified
            );
            if opaque {
                for rule in [GuardRule::FieldOpaque, GuardRule::NoBorrowOrigin] {
                    assert_eq!(
                        recorded
                            .guards
                            .iter()
                            .filter(|guard| guard.slot == field_key && guard.rule == rule)
                            .count(),
                        1,
                        "the opaque field must retain the actual {rule:?} guard"
                    );
                }
            } else {
                assert!(
                    !recorded.guards.iter().any(|guard| guard.slot == field_key),
                    "null field evidence cannot become an eager Ref rejection"
                );
            }
        });
    }
}
