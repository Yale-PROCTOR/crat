//! First activated traversal-call model witness. Embedded programs are never run.

use super::{
    super::{SlotKind, ssa::constraint::Var},
    tests::{Fixture, inspect_era5_frame},
};

const CODE: &str = r#"
unsafe extern "C" {
    fn malloc(size:usize)->*mut core::ffi::c_void;
    fn free(pointer:*mut core::ffi::c_void);
}
pub struct Node {left:*mut Node,right:*mut Node,value:i32}
pub unsafe fn minimum(mut node:*mut Node)->*mut Node {
    while !(*node).left.is_null() {node=(*node).left;}
    node
}
pub unsafe fn caller()->i32 {
    let root=malloc(core::mem::size_of::<Node>()) as *mut Node;
    (*root).left=0 as *mut Node;
    (*root).right=0 as *mut Node;
    (*root).value=7;
    let result=minimum(root);
    let value=(*result).value;
    free(root as *mut core::ffi::c_void);
    value
}
"#;

fn assert_original_endpoints_kept(fixture: &Fixture) {
    assert!(
        fixture.accepted,
        "accepted model required: {:?}",
        fixture.construction_error
    );
    let accepted = fixture
        .export
        .stack_entry_final
        .as_ref()
        .expect("accepted model snapshot namespace");
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|snapshot| snapshot.offset == accepted.snapshot_offset)
        .expect("the accepted construction's ownership evidence");
    let owns = fixture
        .export
        .version_owns
        .as_ref()
        .expect("accepted ownership valuation");
    for (operation, callee) in [("source", "malloc"), ("sink", "free")] {
        let rows: Vec<_> = snapshot
            .metadata
            .equations
            .iter()
            .filter(|row| row.operation == operation)
            .collect();
        assert_eq!(
            rows.len(),
            1,
            "one original {operation} in accepted construction"
        );
        let row = rows[0];
        let endpoint = row
            .endpoint
            .as_ref()
            .expect("exact original endpoint coordinates");
        assert_eq!(endpoint.function, "caller");
        assert_eq!(endpoint.callee, callee);
        assert_eq!(row.point.function.as_ref(), Some(&endpoint.function));
        assert_eq!(row.point.block, Some(endpoint.block));
        assert_eq!(row.point.statement, Some(endpoint.statement));
        assert_eq!(row.variables.len(), 1);
        assert!(
            owns[Var::from_u32(row.variables[0])],
            "original endpoint responsibility retained: {operation}, {:?}/{}",
            row.point,
            row.ordinal
        );
    }
}

#[test]
fn c07_traversal_activation_borrows_return_and_retains_original_owner_free() {
    let fixture = inspect_era5_frame(CODE);
    let expected = [
        ("caller::root", SlotKind::Owning),
        ("caller::result", SlotKind::Ref),
        ("minimum::node", SlotKind::Ref),
        ("minimum::_0", SlotKind::Ref),
    ];
    if !fixture.accepted
        || expected
            .iter()
            .any(|(key, kind)| fixture.kinds.get(*key) != Some(kind))
    {
        eprintln!(
            "C07_TRAVERSAL_ACTIVATION_RED={}",
            serde_json::json!({
                "accepted": fixture.accepted,
                "construction_error": fixture.construction_error,
                "origin": fixture.origin_json,
                "commit_trace": fixture.commit_trace,
                "licensing": fixture.export.ownership_licensing,
            })
        );
    }
    for (key, kind) in expected {
        fixture.assert_kind(key, kind);
    }
    assert_original_endpoints_kept(&fixture);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    assert_eq!(accepted.traversal_guards.len(), 1);
    assert!(
        accepted.traversal_guards[0].1,
        "the actual accepted model selects the traversal guard"
    );
    assert!(
        !accepted.traversal_owns.is_empty(),
        "same-model call ownership subset is exported"
    );
}

#[test]
fn c07_traversal_activation_fresh_identity_return_keeps_owning_transfer() {
    let fixture = inspect_era5_frame(
        r#"
unsafe extern "C" {
    fn malloc(size:usize)->*mut core::ffi::c_void;
    fn free(pointer:*mut core::ffi::c_void);
}
pub unsafe fn identity(pointer:*mut i32)->*mut i32 {pointer}
pub unsafe fn caller()->i32 {
    let root=malloc(core::mem::size_of::<i32>()) as *mut i32;
    *root=7;
    let result=identity(root);
    let value=*result;
    free(result as *mut core::ffi::c_void);
    value
}
"#,
    );
    for key in [
        "caller::root",
        "caller::result",
        "identity::pointer",
        "identity::_0",
    ] {
        fixture.assert_kind(key, SlotKind::Owning);
    }
    assert_original_endpoints_kept(&fixture);
    assert!(
        fixture
            .export
            .ownership_licensing
            .as_ref()
            .unwrap()
            .iter()
            .all(|snapshot| snapshot.traversal_calls.is_empty()),
        "an ordinary identity return must retain its ownership-transfer role"
    );
}

#[test]
fn c07_traversal_activation_all_original_endpoints_hard_sat() {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::super::{
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
        let _world =
            super::stack_entry::enter_world(Some(WholeProgramAttestation::FrozenBenchmarkGraph));
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
        super::super::coherence::constrain_field_ownership(&solver, &slots, &program);
        let tracker = solver.tracker().unwrap();
        let mut assumptions = tracker.tracks();
        assumptions.extend_from_slice(construction.selectors.sources());
        assumptions.extend_from_slice(construction.selectors.sinks());
        let result = solver.check_with_assumptions(&assumptions);
        if result == z3::SatResult::Unsat {
            let labels: Vec<_> = solver
                .optimize()
                .get_unsat_core()
                .iter()
                .map(|b| tracker.label_of(b).unwrap_or_else(|| b.to_string()))
                .collect();
            eprintln!(
                "C07_ACTIVATION_HARD_CORE={}",
                serde_json::to_string(&labels).unwrap()
            );
        }
        assert_eq!(
            result,
            z3::SatResult::Sat,
            "complete late hard constraints retain original source and free"
        );
    })
    .unwrap_or_else(|e| e.raise());
}

#[test]
fn c07_traversal_activation_holds_open_world_retention_with_cast_premise_control() {
    let open = super::tests::inspect(CODE);
    assert!(open.accepted);
    assert!(
        open.export
            .stack_entry_final
            .as_ref()
            .unwrap()
            .traversal_guards
            .iter()
            .all(|(_, selected)| !*selected)
    );
    let retained=CODE.replace("pub unsafe fn minimum(mut node:*mut Node)->*mut Node {","static mut SAVED:*mut Node=0 as *mut Node;pub unsafe fn minimum(mut node:*mut Node)->*mut Node {SAVED=node;");
    let retained = inspect_era5_frame(&retained);
    assert!(retained.accepted);
    assert!(
        retained
            .export
            .ownership_licensing
            .as_ref()
            .unwrap()
            .iter()
            .all(|s| s.traversal_calls.is_empty()),
        "retention is not a certified reader"
    );
    let raw = format!(
        "{CODE}\npub unsafe fn raw_caller(address:usize)->i32{{let node=address as *mut Node;let result=minimum(node);(*result).value}}"
    );
    let raw = inspect_era5_frame(&raw);
    assert!(raw.accepted);
    eprintln!("R284_RAW_ACTUAL_KINDS={:?}", raw.kinds);
    // R284 attribution: an integer cast alone is Ref in this frame, so it
    // cannot witness propagation from an actual Raw kind.
    raw.assert_kind("raw_caller::node", SlotKind::Ref);
    assert!(
        raw.export
            .stack_entry_final
            .as_ref()
            .unwrap()
            .traversal_guards
            .windows(2)
            .all(|rows| rows[0].1 == rows[1].1),
        "Ref cast actual is not a Raw premise; shared-callee guards still agree"
    );
}
#[test]
fn c07_traversal_activation_raw_write_before_borrow_use_remains_held() {
    // UB-free input shape: aliasing raw pointers allow this intervening write.
    // A retained shared Ref result would require a checked lifetime across it.
    let code = CODE.replace(
        "let value=(*result).value;",
        "(*root).value=9;let value=(*result).value;",
    );
    let fixture = inspect_era5_frame(&code);
    assert!(fixture.accepted);
    assert!(
        fixture
            .export
            .stack_entry_final
            .as_ref()
            .unwrap()
            .traversal_guards
            .iter()
            .all(|(_, selected)| !*selected),
        "raw write across returned borrow must be rejected by native replay: {:?}",
        fixture.kinds
    );
}

#[test]
fn c07_traversal_activation_exports_returned_loan() {
    let fixture = inspect_era5_frame(CODE);
    fixture.assert_kind("caller::root", SlotKind::Owning);
    fixture.assert_kind("caller::result", SlotKind::Ref);
    let accepted =
        serde_json::to_value(fixture.export.stack_entry_final.as_ref().unwrap()).unwrap();
    let loans = accepted["traversal_loans"]
        .as_array()
        .expect("accepted returned-loan receipts");
    assert_eq!(loans.len(), 1);
    assert!(
        loans[0]["live_points"]
            .as_array()
            .is_some_and(|points| !points.is_empty())
    );
    assert!(
        loans[0]["origin"]["native"]["caller_value_flow"]
            .as_bool()
            .unwrap()
    );
}

#[test]
fn c07_traversal_activation_owner_write_after_last_use_grants() {
    let code = CODE.replace("free(root as", "(*root).value=9;free(root as");
    let fixture = inspect_era5_frame(&code);
    fixture.assert_kind("caller::root", SlotKind::Owning);
    fixture.assert_kind("caller::result", SlotKind::Ref);
    assert!(
        fixture
            .export
            .stack_entry_final
            .as_ref()
            .unwrap()
            .traversal_guards
            .iter()
            .any(|(_, selected)| *selected)
    );
}

#[test]
fn c07_traversal_activation_copy_keeps_the_returned_loan_live() {
    let code = CODE.replace(
        "let value=(*result).value;",
        "let copy=result;(*root).value=9;let value=(*copy).value;",
    );
    let fixture = inspect_era5_frame(&code);
    assert!(fixture.accepted);
    assert!(
        fixture
            .export
            .stack_entry_final
            .as_ref()
            .unwrap()
            .traversal_guards
            .iter()
            .all(|(_, selected)| !*selected),
        "a copied receiver still requires the returned loan"
    );
}
