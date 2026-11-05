//! Compiler-backed array summary controls; no fixture code executes.
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{ProjectionElem, Rvalue, StatementKind, VarDebugInfoContents};

use super::*;
use crate::analyses::borrow_ownership::{
    SlotKind,
    coherence::{add_coherence, constrain_field_ownership},
    nullability,
    resolve::{ResolvedSlot, resolve_place},
    slot_key,
    slots::{SlotId, StructFieldSlot},
    solver::SlotRef,
};

fn inspect(code: &str, check: impl FnOnce(&RustProgram<'_>, &CrateSlots) + Send + Sync) {
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
        check(&program, &slots);
    })
    .unwrap_or_else(|error| error.raise());
}
fn field(program: &RustProgram<'_>, name: &str, index: usize) -> StructFieldSlot {
    let ds: Vec<_> = program
        .structs
        .iter()
        .copied()
        .filter(|d| program.tcx.item_name(d.to_def_id()).as_str() == name)
        .collect();
    assert_eq!(ds.len(), 1);
    StructFieldSlot {
        struct_did: ds[0],
        field_index: index,
    }
}
fn keys(program: &RustProgram<'_>, slots: &CrateSlots, field: StructFieldSlot) -> Vec<String> {
    let range = slots
        .field_slots
        .slots_for_field(field)
        .expect("array declaration must be registered");
    (range.start.as_usize()..range.end.as_usize())
        .map(|i| {
            let d = slots.field_slots.slot(SlotId::from_usize(i)).depth;
            slot_key::field_key(program.tcx, field.struct_did, field.field_index, d)
        })
        .collect()
}
fn constrained(program: &RustProgram<'_>, slots: &CrateSlots) -> ArrayFieldFacts {
    let solver = KindSolver::new(slots);
    let mut nullable = nullability::analyze(program.tcx, &program.functions, slots);
    let facts = constrain(program, slots, &solver, &mut nullable);
    assert_eq!(solver.check(), z3::SatResult::Sat);
    let model = solver.model_kinds().unwrap();
    for row in &facts.rows {
        assert!(row.holds.contains(&HoldReason::ElementBorrowNotRepresented));
        assert!(
            row.holds
                .contains(&HoldReason::ElementOwnershipNotRepresented)
        );
        for i in 0..slots.field_slots.len() {
            let id = SlotId::from_usize(i);
            let s = slots.field_slots.slot(id);
            let crate::analyses::borrow_ownership::slots::SlotOwner::Field(f) = s.owner else {
                unreachable!()
            };
            if row.slot_keys.contains(&slot_key::field_key(
                program.tcx,
                f.struct_did,
                f.field_index,
                s.depth,
            )) {
                assert_eq!(model[&SlotRef::Field(id)], SlotKind::Raw);
            }
        }
    }
    facts
}
#[test]
fn e5_x_array_five_declarations_have_uniform_element_identity() {
    let padding44 = (0..44).map(|i| format!("p{i}:u8,")).collect::<String>();
    let padding8 = (0..8).map(|i| format!("p{i}:u8,")).collect::<String>();
    let code = format!(
        "pub struct LodePNGInfo{{{padding44}unknown_chunks_data:[*mut u8;3]}} pub struct ColorTree{{children:[*mut ColorTree;16]}} pub struct ti_indicator_info{{{padding8}input_names:[*mut i8;10],option_names:[*mut i8;10],output_names:[*mut i8;10]}} pub struct Scalar{{p:*mut u8}} "
    );
    inspect(&code, |program, slots| {
        for (name, index) in [
            ("LodePNGInfo", 44),
            ("ColorTree", 0),
            ("ti_indicator_info", 8),
            ("ti_indicator_info", 9),
            ("ti_indicator_info", 10),
        ] {
            let f = field(program, name, index);
            let k = keys(program, slots, f);
            assert_eq!(
                k,
                vec![format!(
                    "{}::field{index}::element@d0",
                    program.tcx.def_path_str(f.struct_did.to_def_id())
                )]
            );
        }
        assert_eq!(
            slots.field_slots.len(),
            6,
            "five summaries plus one scalar, not array lengths"
        );
        let f = field(program, "Scalar", 0);
        assert_eq!(keys(program, slots, f), vec!["Scalar::field0@d0"]);
        assert_eq!(constrained(program, slots).rows.len(), 5);
    });
}
#[test]
fn e5_x_array_index_selects_wrapper_without_adding_pointer_depth() {
    inspect(
        "pub struct H{a:[*mut *mut u8;2]} pub unsafe fn f(h:*mut H,p:*mut *mut u8,i:usize)->*mut u8{(*h).a[i]=p; *(*h).a[0]}",
        |program, slots| {
            let f = field(program, "H", 0);
            assert_eq!(
                keys(program, slots, f),
                vec!["H::field0::element@d0", "H::field0::element@d1"]
            );
            let did = program.functions[0];
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();
            let mut count = 0;
            for data in body.basic_blocks.iter() {
                for stmt in &data.statements {
                    let StatementKind::Assign(box (lhs, rv)) = &stmt.kind else { continue };
                    let candidates = [
                        Some(*lhs),
                        match rv {
                            Rvalue::Use(o) => o.place(),
                            Rvalue::CopyForDeref(p)
                            | Rvalue::Ref(_, _, p)
                            | Rvalue::RawPtr(_, p) => Some(*p),
                            _ => None,
                        },
                    ];
                    for p in candidates.into_iter().flatten() {
                        if let Some(index) = p.projection.iter().position(|x| {
                            matches!(
                                x,
                                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                            )
                        }) {
                            if !p.projection[..index]
                                .iter()
                                .any(|x| matches!(x, ProjectionElem::Field(..)))
                            {
                                continue;
                            }
                            let ResolvedSlot::Field(id) =
                                resolve_place(slots, did, &body, p, 0, None)
                                    .expect("indexed element")
                            else {
                                panic!("field")
                            };
                            assert_eq!(slots.field_slots.slot(id).depth, 0);
                            let whole = rustc_middle::mir::Place {
                                local: p.local,
                                projection: program.tcx.mk_place_elems(&p.projection[..index]),
                            };
                            assert!(
                                resolve_place(slots, did, &body, whole, 0, None).is_none(),
                                "whole array is not element value"
                            );
                            let ResolvedSlot::Field(inner) =
                                resolve_place(slots, did, &body, p, 1, None).unwrap()
                            else {
                                panic!("inner")
                            };
                            assert_eq!(slots.field_slots.slot(inner).depth, 1);
                            count += 1;
                        }
                    }
                }
            }
            if count < 2 {
                eprintln!("array fixture MIR: {body:#?}");
            }
            assert!(
                count >= 2,
                "store and indexed load/access must actually be visited"
            );
        },
    );
}
#[test]
fn e5_x_array_aggregate_repeat_copy_and_index_keep_value_sources() {
    inspect(
        "pub struct H{a:[*mut u8;3]} pub unsafe fn f(out:*mut H,p:*mut u8){let a=[p,core::ptr::null_mut(),p];let b=a;let h=H{a:b};(*out).a=h.a;(*out).a[1]=p;let repeat=[p;3];(*out).a=repeat;let q=(*out).a[0];let _=q;}",
        |program, slots| {
            let facts = constrained(program, slots);
            assert_eq!(facts.rows.len(), 1);
            let row = &facts.rows[0];
            assert!(!row.source_slots.is_empty());
            assert!(row.null_literal);
            assert!(!row.opaque);
            assert_eq!(row.field, "H::field0::element");
        },
    );
}
#[test]
fn e5_x_array_opaque_and_integer_elements_are_not_erased_by_null() {
    inspect(
        "pub struct H{a:[*mut u8;3]} unsafe extern \"C\"{fn op()->*mut u8;} pub unsafe fn f(out:*mut H){(*out).a=[core::ptr::null_mut(),op(),1usize as *mut u8];}",
        |program, slots| {
            let facts = constrained(program, slots);
            assert_eq!(facts.rows.len(), 1);
            let row = &facts.rows[0];
            assert!(row.null_literal);
            assert!(row.opaque);
            assert!(row.holds.contains(&HoldReason::OpaqueElement));
        },
    );
}
#[test]
fn e5_x_array_unknown_alias_mutation_has_an_explicit_hold() {
    inspect(
        "pub struct H{a:[*mut u8;3]} unsafe extern \"C\"{fn clobber(p:*mut *mut u8);} pub unsafe fn f(out:*mut H,p:*mut u8){(*out).a=[p;3];clobber(&raw mut (*out).a[0]);}",
        |program, slots| {
            let facts = constrained(program, slots);
            assert_eq!(facts.rows.len(), 1);
            assert!(facts.rows[0].unknown);
            assert!(facts.rows[0].holds.contains(&HoldReason::UnknownValue));
        },
    );
}
#[test]
fn e5_x_array_raw_summary_adds_no_reverse_ownership_demand() {
    inspect(
        "pub struct H{a:[*mut u8;2]} pub unsafe fn f(out:*mut H,p:*mut u8){(*out).a[0]=p;}",
        |program, slots| {
            let did = program.functions[0];
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();
            let p = body
                .var_debug_info
                .iter()
                .find_map(|v| {
                    if v.name.as_str() != "p" {
                        return None;
                    };
                    let VarDebugInfoContents::Place(p) = v.value else { return None };
                    p.as_local()
                })
                .unwrap();
            let source = SlotRef::Local(
                did,
                slots.fn_local_slots[&did]
                    .slot_for_local_depth(p, 0)
                    .unwrap(),
            );
            let arr = field(program, "H", 0);
            let target = SlotRef::Field(
                slots
                    .field_slots
                    .slot_for_field_depth(arr, 0)
                    .expect("registered array"),
            );
            let solver = KindSolver::new(slots);
            solver.assume(source, SlotKind::Owning);
            add_coherence(&solver, slots, did, &body);
            constrain_field_ownership(&solver, slots, program);
            let mut n = nullability::analyze(program.tcx, &program.functions, slots);
            let _ = constrain(program, slots, &solver, &mut n);
            assert_eq!(
                solver.check(),
                z3::SatResult::Sat,
                "array no-own cannot back-propagate through scalar R-FIELD-OWN"
            );
            let m = solver.model_kinds().unwrap();
            assert_eq!(m[&source], SlotKind::Owning);
            assert_eq!(m[&target], SlotKind::Raw);
            solver.assume(target, SlotKind::Owning);
            assert_eq!(
                solver.check(),
                z3::SatResult::Unsat,
                "no unlicensed array owner"
            );
        },
    );
}

#[test]
fn e5_x_array_shared_construction_carries_raw_holds_and_exact_qualifier_keys() {
    inspect(
        "pub struct H{a:[*mut u8;2]} pub unsafe fn f(h:*mut H,p:*mut u8)->*mut u8{(*h).a=[p,core::ptr::null_mut()];(*h).a[0]}",
        |program, slots| {
            use crate::analyses::borrow_ownership::{
                construction::{CopyLendMode, construct_bo_into},
                export,
                mutability_facts::MutFacts,
                origins::compute_origins,
            };
            let origins = compute_origins(program);
            let mutability = MutFacts::from_program(program);
            let run = || {
                let solver = KindSolver::new(slots);
                let c = construct_bo_into(
                    program,
                    slots,
                    &origins,
                    &mutability,
                    &solver,
                    CopyLendMode::Baseline,
                )
                .unwrap();
                assert_eq!(
                    c.array_fields.rows.len(),
                    1,
                    "shared construction must carry array value facts"
                );
                assert_eq!(solver.check(), z3::SatResult::Sat);
                (c, solver.model_kinds().unwrap())
            };
            let (plain, model) = run();
            let ((captured, other), exports) = export::with_bo_export(run);
            assert_eq!(model, other);
            assert_eq!(plain.array_fields, captured.array_fields);
            assert_eq!(plain.stats, captured.stats);
            assert_eq!(plain.selectors.keys(), captured.selectors.keys());
            assert_eq!(exports.array_fields.as_ref(), Some(&captured.array_fields));
            let row = &captured.array_fields.rows[0];
            assert!(row.null_literal);
            assert!(!row.loaded_slots.is_empty());
            for key in &row.slot_keys {
                let q: Vec<_> = captured
                    .qualifier_facts
                    .rows
                    .iter()
                    .filter(|r| &r.slot == key)
                    .collect();
                assert_eq!(q.len(), 1);
                assert_eq!(q[0].depth, 0);
                assert!(q[0].null_literal);
            }
            for i in 0..slots.field_slots.len() {
                let id = SlotId::from_usize(i);
                assert_eq!(model[&SlotRef::Field(id)], SlotKind::Raw);
            }
        },
    );
}

#[test]
fn e5_x_array_alias_load_carries_null_without_holding_unrelated_array_parameter() {
    inspect(
        "pub struct H{a:[*mut u8;2]} pub unsafe fn f(out:*mut H,p:*mut u8){(*out).a=[p,core::ptr::null_mut()];let a=&raw mut (*out).a;let b=a;let q=(*b)[0];let _=q.is_null();} pub unsafe fn unrelated(a:*mut [*mut u8;2])->*mut u8{(*a)[0]}",
        |program, slots| {
            let solver = KindSolver::new(slots);
            let mut nullable = nullability::analyze(program.tcx, &program.functions, slots);
            let facts = constrain(program, slots, &solver, &mut nullable);
            assert_eq!(facts.rows.len(), 1);
            let did = *program
                .functions
                .iter()
                .find(|d| program.tcx.item_name(d.to_def_id()).as_str() == "f")
                .unwrap();
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();
            let q = body
                .var_debug_info
                .iter()
                .find_map(|v| {
                    if v.name.as_str() != "q" {
                        return None;
                    };
                    let VarDebugInfoContents::Place(p) = v.value else { return None };
                    p.as_local()
                })
                .unwrap();
            let q = SlotRef::Local(
                did,
                slots.fn_local_slots[&did]
                    .slot_for_local_depth(q, 0)
                    .unwrap(),
            );
            assert!(
                nullable.null_literal.contains(&q),
                "null element evidence must reach a known alias load"
            );
            let f = field(program, "H", 0);
            let field = SlotRef::Field(slots.field_slots.slot_for_field_depth(f, 0).unwrap());
            assert!(nullable.is_null_use.contains(&field));
            let other = *program
                .functions
                .iter()
                .find(|d| program.tcx.item_name(d.to_def_id()).as_str() == "unrelated")
                .unwrap();
            let other = SlotRef::Local(
                other,
                slots.fn_local_slots[&other]
                    .slot_for_local_depth(rustc_middle::mir::RETURN_PLACE, 0)
                    .unwrap(),
            );
            solver.assume(other, SlotKind::Ref);
            assert_eq!(solver.check(), z3::SatResult::Sat);
            let model = solver.model_kinds().unwrap();
            assert_eq!(model[&q], SlotKind::Raw);
            assert_eq!(model[&other], SlotKind::Ref);
        },
    );
}

#[test]
fn e5_x_array_alias_load_holds_every_real_pointer_depth() {
    inspect(
        "pub struct H{a:[*mut *mut i32;1]} pub unsafe fn f(h:*mut H)->i32{let cells=&(*h).a;let q=cells[0];**q}",
        |program, slots| {
            let solver = KindSolver::new(slots);
            let mut n = nullability::analyze(program.tcx, &program.functions, slots);
            let facts = constrain(program, slots, &solver, &mut n);
            let did = program.functions[0];
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();
            let q = body
                .var_debug_info
                .iter()
                .find_map(|v| {
                    if v.name.as_str() != "q" {
                        return None;
                    };
                    let VarDebugInfoContents::Place(p) = v.value else { return None };
                    p.as_local()
                })
                .unwrap();
            assert_eq!(solver.check(), z3::SatResult::Sat);
            let model = solver.model_kinds().unwrap();
            for depth in [0, 1] {
                let slot = SlotRef::Local(
                    did,
                    slots.fn_local_slots[&did]
                        .slot_for_local_depth(q, depth)
                        .unwrap(),
                );
                assert_eq!(
                    model[&slot],
                    SlotKind::Raw,
                    "known array alias load depth {depth} must keep its summary hold"
                );
                assert!(facts.rows[0].loaded_slots.contains(&slot_key::local_key(
                    program.tcx,
                    did,
                    q.as_usize(),
                    depth
                )));
            }
        },
    );
}

#[test]
fn e5_x_array_reborrow_preserves_storage_alias_loads_and_opaque_stores() {
    inspect(
        "pub struct H{a:[*mut u8;2]} unsafe extern \"C\"{fn op()->*mut u8;} pub unsafe fn f(out:*mut H,p:*mut u8){(*out).a=[p;2];let a=&mut (*out).a;let b=&mut *a;b[0]=op();let q=b[1];let _=q;}",
        |program, slots| {
            let solver = KindSolver::new(slots);
            let mut n = nullability::analyze(program.tcx, &program.functions, slots);
            let facts = constrain(program, slots, &solver, &mut n);
            assert_eq!(facts.rows.len(), 1);
            assert!(
                facts.rows[0].opaque,
                "opaque write through transparent array-storage reborrow must reach summary"
            );
            let did = program.functions[0];
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();
            let q = body
                .var_debug_info
                .iter()
                .find_map(|v| {
                    if v.name.as_str() != "q" {
                        return None;
                    };
                    let VarDebugInfoContents::Place(p) = v.value else { return None };
                    p.as_local()
                })
                .unwrap();
            let slot = SlotRef::Local(
                did,
                slots.fn_local_slots[&did]
                    .slot_for_local_depth(q, 0)
                    .unwrap(),
            );
            assert_eq!(solver.check(), z3::SatResult::Sat);
            assert_eq!(solver.model_kinds().unwrap()[&slot], SlotKind::Raw);
            assert!(facts.rows[0].loaded_slots.contains(&slot_key::local_key(
                program.tcx,
                did,
                q.as_usize(),
                0
            )));
        },
    );
}
