//! Phase-E controls distinguish comparison occurrence from existing causes.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::{BinOp, RETURN_PLACE, Rvalue, StatementKind, VarDebugInfoContents},
    ty::TyCtxt,
};

use crate::{
    analyses::borrow_ownership::{
        SlotKind, coherence,
        construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
        crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
        mutability_facts::MutFacts,
        origins::{self, compute_origins},
        slot_key,
        slots::{SlotId, SlotOwner},
        solver::{KindSolver, SlotRef},
    },
    utils::rustc::RustProgram,
};

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    kinds: BTreeMap<String, SlotKind>,
    nullable: BTreeSet<String>,
    no_borrow_origin: BTreeSet<String>,
    positive_opaque: BTreeSet<String>,
    field_evidence: BTreeMap<String, (usize, usize, usize, usize)>,
    locals: BTreeMap<String, String>,
    returns: Vec<String>,
}

fn canonical(tcx: TyCtxt<'_>, slots: &CrateSlots, reference: SlotRef) -> String {
    match reference {
        SlotRef::Local(function, id) => {
            let slot = slots.fn_local_slots[&function].slot(id);
            let SlotOwner::Local(local) = slot.owner else { unreachable!() };
            slot_key::local_key(tcx, function, local.as_usize(), slot.depth)
        }
        SlotRef::Field(id) => {
            let slot = slots.field_slots.slot(id);
            let SlotOwner::Field(field) = slot.owner else { unreachable!() };
            slot_key::field_key(tcx, field.struct_did, field.field_index, slot.depth)
        }
    }
}

fn snapshot(code: &str, requested_locals: &[&str]) -> (Snapshot, usize) {
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
        let solver = KindSolver::new(&slots);
        let construction = construct_bo_into(
            &program,
            &slots,
            &origins,
            &facts,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("ordinary comparison-control construction");
        let (model, stats) = verify_bo_construction_counting(
            &program,
            &slots,
            &origins,
            &solver,
            &construction,
            &facts,
        );
        let model = model.expect("comparison-control model");
        assert!(stats.source_retirement_decline.is_empty());
        // These fixtures have no allocation/free endpoint. A BinaryOp must not
        // silently introduce a new T2 ownership assertion.
        assert!(construction.selectors.keys().is_empty());
        let mut selected = Vec::new();
        let mut locals = BTreeMap::new();
        let mut returns = Vec::new();
        let mut comparisons = 0;
        for &function in &program.functions {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let universe = &slots.fn_local_slots[&function];
            let mut selected_locals: BTreeSet<_> = body.args_iter().chain([RETURN_PLACE]).collect();
            for &name in requested_locals {
                let found: BTreeSet<_> = body
                    .var_debug_info
                    .iter()
                    .filter_map(|info| {
                        if info.name.as_str() != name {
                            return None;
                        }
                        let VarDebugInfoContents::Place(place) = info.value else { return None };
                        place.as_local()
                    })
                    .collect();
                assert_eq!(found.len(), 1, "exact source local {name}");
                let local = *found.iter().next().unwrap();
                selected_locals.insert(local);
                let id = universe
                    .slot_for_local_depth(local, 0)
                    .expect("requested pointer local");
                locals.insert(
                    name.to_owned(),
                    canonical(tcx, &slots, SlotRef::Local(function, id)),
                );
            }
            for local in selected_locals {
                for depth in 0..MAX_SLOT_DEPTH {
                    if let Some(id) = universe.slot_for_local_depth(local, depth) {
                        let reference = SlotRef::Local(function, id);
                        if local == RETURN_PLACE {
                            returns.push(canonical(tcx, &slots, reference));
                        }
                        selected.push(reference);
                    }
                }
            }
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    if let StatementKind::Assign(box (
                        _,
                        Rvalue::BinaryOp(
                            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
                            operands,
                        ),
                    )) = &statement.kind
                    {
                        if operands.0.ty(&*body, tcx).is_any_ptr()
                            && operands.1.ty(&*body, tcx).is_any_ptr()
                        {
                            comparisons += 1;
                        }
                    }
                }
            }
        }
        selected.extend(
            (0..slots.field_slots.len()).map(|index| SlotRef::Field(SlotId::from_usize(index))),
        );
        let originless = origins::collect_no_borrow_origin_slots(&origins, &slots);
        let opaque =
            coherence::positive_opaque_return_slots(&slots, &program, origins.native_flows());
        let kinds = selected
            .iter()
            .map(|reference| {
                (
                    canonical(tcx, &slots, *reference),
                    *model
                        .get(reference)
                        .expect("selected canonical slot is present"),
                )
            })
            .collect();
        let selected_set = |contains: &dyn Fn(SlotRef) -> bool| {
            selected
                .iter()
                .copied()
                .filter(|reference| contains(*reference))
                .map(|reference| canonical(tcx, &slots, reference))
                .collect()
        };
        let field_evidence = construction
            .field_ref_plan
            .rows
            .iter()
            .map(|row| {
                (
                    canonical(tcx, &slots, row.field),
                    (
                        row.opaque,
                        row.unresolved_unresolvable,
                        row.nullable,
                        row.safe,
                    ),
                )
            })
            .collect();
        (
            Snapshot {
                kinds,
                nullable: selected_set(&|reference| construction.nullability.contains(&reference)),
                no_borrow_origin: selected_set(&|reference| originless.contains(&reference)),
                positive_opaque: selected_set(&|reference| opaque.contains(&reference)),
                field_evidence,
                locals,
                returns,
            },
            comparisons,
        )
    })
    .unwrap_or_else(|error| error.raise())
}

fn compare_twins(without: &str, with: &str, locals: &[&str]) -> Snapshot {
    let (baseline, absent) = snapshot(without, locals);
    let (comparison, present) = snapshot(with, locals);
    assert_eq!(absent, 0, "baseline must contain no pointer comparison");
    assert_eq!(
        present, 1,
        "the comparison must survive as an actual pointer BinaryOp"
    );
    assert_eq!(
        comparison, baseline,
        "comparison occurrence must not erase or invent selected kind/cause facts"
    );
    comparison
}

#[test]
fn e5_n_cmp_equality_and_ordering_preserve_parameter_kind_facts() {
    for operator in ["==", "<"] {
        compare_twins(
            "pub unsafe fn f(p: *const u8, q: *const u8) -> bool { false }",
            &format!("pub unsafe fn f(p: *const u8, q: *const u8) -> bool {{ p {operator} q }}"),
            &[],
        );
    }
}

#[test]
fn e5_n_cmp_opaque_return_keeps_its_independent_origin_cause() {
    const PREFIX: &str = "unsafe extern \"C\" { fn op(p: *mut u8) -> *mut u8; }";
    let found = compare_twins(
        &format!("{PREFIX} pub unsafe fn f(p: *mut u8) -> *mut u8 {{ let q = op(p); q }}"),
        &format!(
            "{PREFIX} pub unsafe fn f(p: *mut u8) -> *mut u8 {{ let q = op(p); let _cmp = q == p; q }}"
        ),
        &["q"],
    );
    assert_eq!(found.returns.len(), 1);
    assert!(found.no_borrow_origin.contains(&found.returns[0]));
    assert_eq!(found.kinds[&found.returns[0]], SlotKind::Raw);
    assert!(found.positive_opaque.contains(&found.locals["q"]));
}

#[test]
fn e5_n_cmp_integer_reconstruction_keeps_independent_facts() {
    let found = compare_twins(
        "pub unsafe fn f(p: *mut u8) -> *mut u8 { let address = p as usize; let q = address as *mut u8; q }",
        "pub unsafe fn f(p: *mut u8) -> *mut u8 { let address = p as usize; let q = address as *mut u8; let _cmp = q == p; q }",
        &["q"],
    );
    println!("E5 integer-reconstruction comparison twin: {found:?}");
}

#[test]
fn e5_n_cmp_offset_return_preserves_existing_facts_without_a_raw_promise() {
    let found = compare_twins(
        "pub unsafe fn f(p: *mut u8, n: isize) -> *mut u8 { let q = p.offset(n); q }",
        "pub unsafe fn f(p: *mut u8, n: isize) -> *mut u8 { let q = p.offset(n); let _cmp = q == p; q }",
        &["q"],
    );
    println!("E5 offset comparison twin: {found:?}");
}

const FIELD_PREFIX: &str = "#[repr(C)] pub struct Holder { pub value: *mut u8 } unsafe extern \"C\" { fn op() -> *mut u8; }";

#[test]
fn e5_n_null_local_and_field_controls_keep_null_separate_from_opacity() {
    for (name, expression, expected_field) in [
        ("null", "core::ptr::null_mut()", Some(SlotKind::Ref)),
        ("opaque", "op()", Some(SlotKind::Raw)),
        ("nonzero", "1usize as *mut u8", None),
    ] {
        let code = format!(
            "{FIELD_PREFIX} pub unsafe fn f(out: *mut Holder) {{ let local: *mut u8 = {expression}; (*out).value = local; }}"
        );
        let (found, _) = snapshot(&code, &["local"]);
        assert_eq!(found.field_evidence.len(), 1);
        let (field, &(opaque, _, nullable, _)) = found.field_evidence.iter().next().unwrap();
        if let Some(expected) = expected_field {
            assert_eq!(found.kinds[field], expected, "{name} field control");
        }
        match name {
            "null" => {
                assert!(found.nullable.contains(&found.locals["local"]));
                assert!(nullable > 0);
                assert_eq!(opaque, 0);
            }
            "opaque" => {
                assert!(found.positive_opaque.contains(&found.locals["local"]));
                assert!(opaque > 0);
            }
            _ => assert!(!found.nullable.contains(&found.locals["local"])),
        }
        println!("E5 {name} local/field observation: {found:?}");
    }
}

#[test]
fn e5_n_null_then_opaque_field_preserves_both_observed_evidence_sets() {
    let found = compare_twins(
        &format!(
            "{FIELD_PREFIX} pub unsafe fn f(out: *mut Holder, p: *mut u8) {{ let mut local: *mut u8 = core::ptr::null_mut(); local = op(); (*out).value = local; }}"
        ),
        &format!(
            "{FIELD_PREFIX} pub unsafe fn f(out: *mut Holder, p: *mut u8) {{ let mut local: *mut u8 = core::ptr::null_mut(); local = op(); let _cmp = local == p; (*out).value = local; }}"
        ),
        &["local"],
    );
    assert!(found.nullable.contains(&found.locals["local"]));
    assert!(found.positive_opaque.contains(&found.locals["local"]));
    // Report the current field disposition. No new comparison-derived cause
    // or blanket null/opacity policy is inferred from this mixed evidence.
    println!("E5 null-then-opaque field observation: {found:?}");
}
