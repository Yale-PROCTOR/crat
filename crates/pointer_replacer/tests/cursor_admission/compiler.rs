use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::VarDebugInfoContents;

use super::admission::{
    self, Admission, Candidate, ModelKind, Need, Outcome, Predicate, Shape, Status,
};

fn inspect(code: &str) -> Admission {
    inspect_as(code, ModelKind::Ref, 0, false)
}

fn inspect_as(
    code: &str,
    model_kind: ModelKind,
    slot_depth: usize,
    missing_component: bool,
) -> Admission {
    utils::compilation::run_compiler_on_str(code, |tcx| {
        let owner = tcx
            .hir_crate(())
            .owners
            .iter()
            .filter_map(|o| o.as_owner())
            .find_map(|o| {
                let OwnerNode::Item(item) = o.node() else { return None };
                (matches!(item.kind, ItemKind::Fn { .. })
                    && tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == "witness")
                    .then_some(item.owner_id.def_id)
            })
            .unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(owner).borrow();
        let local = body
            .var_debug_info
            .iter()
            .find_map(|var| {
                if var.name.as_str() != "p" {
                    return None;
                }
                match var.value {
                    VarDebugInfoContents::Place(place) => place.as_local(),
                    _ => None,
                }
            })
            .unwrap();
        // Supplied BO prerequisite is intentionally separate from compiler
        // derivation. These fixtures do not run the BO solver.
        let mut kinds = body
            .local_decls
            .indices()
            .map(|local| (local, ModelKind::Ref))
            .collect::<std::collections::BTreeMap<_, _>>();
        if missing_component {
            kinds.clear();
            kinds.insert(local, ModelKind::Ref);
        }
        let result = admission::inspect(
            tcx,
            owner,
            &body,
            Candidate {
                local,
                slot_depth,
                model_kind,
            },
            &kinds,
        );
        if std::env::var_os("CURSOR_ADMISSION_DUMP_MIR").is_some() {
            eprintln!("{body:#?}");
        }
        result
    })
    .unwrap()
}

#[test]
fn a06_aggregate_and_raw_address_descendants_cannot_hide_retention() {
    for initializer in [
        "let hidden = (p,); retain(hidden.0);",
        "let hidden = [p; 2]; retain(hidden[0]);",
    ] {
        let row = inspect(&format!(
            "unsafe extern \"C\" {{ fn retain(p: *mut i32); }} pub unsafe fn witness() -> i32 {{ let mut a = [1_i32; 4]; let p = a.as_mut_ptr(); {initializer} *p }}"
        ));
        assert_eq!(
            outcome(&row, Predicate::FullRegionSchedule),
            Outcome::Missing(Need::Schedule),
            "{initializer}: {row:#?}"
        );
    }
}

#[test]
fn a06b_raw_address_descendant_cannot_hide_retention() {
    let row = inspect(
        "unsafe extern \"C\" { fn retain(p: *mut i32); } pub unsafe fn witness() -> i32 { let mut a = [1_i32; 4]; let p = a.as_mut_ptr(); let hidden = &raw mut *p; retain(hidden); *p }",
    );
    assert_eq!(
        outcome(&row, Predicate::FullRegionSchedule),
        Outcome::Missing(Need::Schedule)
    );
}

#[test]
fn a07_mixed_base_descendant_cannot_join_one_base_component() {
    let row = inspect(
        "pub unsafe fn witness(flag: bool, other: *mut i32) -> i32 { let mut a = [1_i32; 4]; let p = a.as_mut_ptr(); let q = if flag { p } else { other }; *q = 2; *p }",
    );
    assert_eq!(row.shape, Shape::LocalArray);
    assert_eq!(
        outcome(&row, Predicate::GenerationWindow),
        Outcome::Missing(Need::Generation)
    );
    assert_eq!(row.status, Status::NeedsFact);
}

#[test]
fn a08_index_only_copy_and_loop_keep_one_full_array() {
    let row = inspect(
        "pub unsafe fn witness() -> i32 { let a = [1_i32; 4]; let mut p = a.as_ptr(); let end = p.add(4); let saved = p; let mut sum = 0; while p != end { sum += *p; p = p.add(1); } sum + *saved }",
    );
    assert_eq!(row.status, Status::DecisionOnly, "{row:#?}");
    assert!(row.component.len() > 3);
    assert_eq!(row.base_elements, Some(4));
}

#[test]
fn a09_null_is_an_orthogonal_present_branch_obligation() {
    let row = inspect(
        "pub unsafe fn witness(flag: bool) -> i32 { let a = [1_i32; 4]; let mut p: *const i32 = core::ptr::null(); if flag { p = a.as_ptr(); } if p.is_null() { 0 } else { *p } }",
    );
    assert_eq!(row.shape, Shape::LocalArray);
    assert!(row.nullable);
    assert_eq!(row.status, Status::DecisionOnly, "{row:#?}");
    let absent =
        inspect("pub fn witness() -> bool { let p: *const i32 = core::ptr::null(); p.is_null() }");
    assert_eq!(absent.shape, Shape::NullOnly);
    assert!(absent.nullable);
    assert_ne!(
        outcome(&absent, Predicate::RetainedBase),
        Outcome::Missing(Need::RefAdmission)
    );
}

#[test]
fn a10_frozen_model_and_component_prerequisites_are_not_invented() {
    let code = "pub unsafe fn witness() -> i32 { let a = [1_i32; 4]; let p = a.as_ptr(); let q = p.add(1); *q + *p }";
    for kind in [ModelKind::Raw, ModelKind::Owning, ModelKind::Missing] {
        let row = inspect_as(code, kind, 0, false);
        assert_eq!(
            outcome(&row, Predicate::RetainedBase),
            Outcome::Missing(Need::RefAdmission)
        );
    }
    let row = inspect_as(code, ModelKind::Ref, 0, true);
    assert_eq!(
        outcome(&row, Predicate::RetainedBase),
        Outcome::Missing(Need::RefAdmission)
    );
    let depth = inspect_as(code, ModelKind::Ref, 1, false);
    assert_eq!(depth.status, Status::OutOfScope);
}

#[test]
fn a11_recreated_storage_and_reassigned_root_are_not_one_generation() {
    for code in [
        "pub unsafe fn witness(n: usize) -> i32 { let mut sum = 0; for _ in 0..n { let a = [1_i32; 4]; let p = a.as_ptr(); sum += *p; } sum }",
        "pub unsafe fn witness() -> i32 { let mut a = [1_i32; 4]; let p = a.as_ptr(); a = [2_i32; 4]; *p }",
    ] {
        let row = inspect(code);
        assert_eq!(
            outcome(&row, Predicate::GenerationWindow),
            Outcome::Missing(Need::Generation)
        );
    }
}

#[test]
fn a12_layout_and_wrapping_are_outside_the_instrument_vocabulary() {
    for code in [
        "pub unsafe fn witness() -> bool { let a = [(); 4]; let p = a.as_ptr(); p.is_null() }",
        "pub unsafe fn witness() -> u8 { let a = [1_i32; 4]; let p = a.as_ptr() as *const u8; *p }",
        "pub unsafe fn witness() -> bool { let a = [1_i32; 4]; let p = a.as_ptr(); p.wrapping_add(100).is_null() }",
    ] {
        let row = inspect(code);
        assert_eq!(row.status, Status::OutOfScope, "{row:#?}");
    }
}

#[test]
fn a13_element_reference_and_raw_return_keep_schedule_holds() {
    for code in [
        "pub unsafe fn witness() -> i32 { let mut a = [1_i32; 4]; let p = a.as_mut_ptr(); let r = &mut *p.add(2); *p = 9; *r }",
        // This is a conservative lifecycle/control fixture, not a soundness
        // counterexample to the UB-free-input claim.
        "pub unsafe fn witness() -> *const i32 { let a = [1_i32; 4]; let p = a.as_ptr(); p }",
    ] {
        let row = inspect(code);
        assert_eq!(
            outcome(&row, Predicate::FullRegionSchedule),
            Outcome::Missing(Need::Schedule)
        );
    }
}

#[test]
fn a14_shape_counts_are_over_compiler_rows_not_predicted_corpus_yield() {
    let rows = [
        inspect("pub unsafe fn witness() -> i32 { let a = [1_i32; 4]; let p = a.as_ptr(); *p }"),
        inspect(
            "pub unsafe fn witness(inputs: *const *const f64, i: isize) -> f64 { let p = *inputs.add(1); *p.offset(i) }",
        ),
    ];
    let counts = admission::counts(&rows);
    assert_eq!(
        counts.get(&(Shape::LocalArray, Status::DecisionOnly)),
        Some(&1)
    );
    assert_eq!(
        counts.get(&(Shape::PointerTableLoad, Status::NeedsFact)),
        Some(&1)
    );
    println!("synthetic compiler rows by shape/status: {counts:?}");
}

#[test]
fn a15_schedule_anchor_precedes_both_branch_origins() {
    let row = inspect(
        "pub unsafe fn witness(flag: bool) -> i32 { let a = [1_i32; 4]; let p = if flag { a.as_ptr() } else { a.as_ptr().add(1) }; *p }",
    );
    assert_eq!(row.status, Status::DecisionOnly, "{row:#?}");
    let schedule = row
        .findings
        .iter()
        .find(|f| f.predicate == Predicate::FullRegionSchedule)
        .unwrap();
    assert_eq!(
        schedule.site.unwrap().block,
        0,
        "formation anchor must dominate both branches"
    );
}

#[test]
fn a16_pointer_storage_address_cannot_hide_reassignment() {
    let row = inspect(
        "pub unsafe fn witness(other: *mut i32) -> i32 { let mut a = [1_i32; 4]; let mut p = a.as_mut_ptr(); let address = &mut p; *address = other; *p }",
    );
    assert_eq!(
        outcome(&row, Predicate::FullRegionSchedule),
        Outcome::Unsupported(admission::Unsupported::EscapedStorage)
    );
    assert_eq!(row.status, Status::OutOfScope);
}

#[test]
fn a17_field_load_and_pointer_table_are_distinct_compiler_shapes() {
    let row = inspect(
        "pub struct Holder { pub pointer: *const f64 } pub unsafe fn witness(h: *const Holder) -> f64 { let p = (*h).pointer; *p }",
    );
    // RED against the initial collector: every projected pointer load was
    // incorrectly called PointerTableLoad, which would contaminate CP counts.
    assert_eq!(row.shape, Shape::ProjectionLoad);
    assert_eq!(row.status, Status::NeedsFact);
}

#[test]
fn a18_symbolic_and_empty_array_lengths_are_not_missing_origin() {
    for code in [
        "pub fn witness<const N: usize>() -> bool { let a = [1_i32; N]; let p = a.as_ptr(); p.is_null() }",
        "pub fn witness() -> bool { let a = [1_i32; 0]; let p = a.as_ptr(); p.is_null() }",
    ] {
        let row = inspect(code);
        assert_eq!(row.status, Status::DecisionOnly, "{row:#?}");
        assert_eq!(row.shape, Shape::LocalArray);
    }
}

#[test]
fn a19_literal_zero_and_is_null_use_are_exported_orthogonally() {
    let row = inspect(
        "pub unsafe fn witness(flag: bool) -> i32 { let a = [1_i32; 4]; let mut p = 0 as *const i32; if flag { p = a.as_ptr(); } if p.is_null() { 0 } else { *p } }",
    );
    assert!(row.nullable, "literal null evidence lost: {row:#?}");
    assert_eq!(row.status, Status::DecisionOnly);
    let raw = inspect("pub fn witness(p: *const i32) -> bool { p.is_null() }");
    assert!(
        raw.nullable,
        "construction absence does not erase use-site null evidence"
    );
    assert_eq!(raw.shape, Shape::RawParameter);
    assert_eq!(raw.status, Status::NeedsFact);
}

fn outcome(row: &Admission, predicate: Predicate) -> Outcome {
    row.findings
        .iter()
        .find(|f| f.predicate == predicate)
        .unwrap()
        .outcome
}

#[test]
fn a01_retained_local_array_and_backward_step_are_derived() {
    let row = inspect(
        "pub unsafe fn witness() -> i32 { let mut a = [1_i32, 2, 3, 4]; let p = a.as_mut_ptr().add(2); *p.offset(-1) = 7; *p }",
    );
    assert_eq!(row.shape, Shape::LocalArray);
    assert_eq!(row.status, Status::DecisionOnly, "{row:#?}");
    assert!(
        row.findings
            .iter()
            .all(|f| f.outcome == Outcome::Proven && f.root.is_some() && f.site.is_some())
    );
}

#[test]
fn a02_pointer_table_load_needs_base_and_prefix_facts() {
    let row = inspect(
        "pub unsafe fn witness(inputs: *const *const f64, i: isize) -> f64 { let p = *inputs; *p.offset(i) + *p.offset(i - 1) }",
    );
    assert_eq!(row.shape, Shape::PointerTableLoad);
    assert_eq!(
        outcome(&row, Predicate::RetainedBase),
        Outcome::Missing(Need::BaseOrigin)
    );
    assert_eq!(
        outcome(&row, Predicate::RawEntryPrefix),
        Outcome::Missing(Need::Prefix)
    );
    assert_eq!(row.status, Status::NeedsFact);
}

#[test]
fn a03_raw_entry_and_slice_window_are_not_full_array_proofs() {
    let raw = inspect("pub unsafe fn witness(p: *const i32) -> i32 { *p.offset(-1) }");
    assert_eq!(raw.shape, Shape::RawParameter);
    assert_eq!(raw.status, Status::NeedsFact);
    let slice =
        inspect("pub unsafe fn witness(a: &[i32]) -> i32 { let p = a.as_ptr(); *p.offset(-1) }");
    assert_eq!(slice.shape, Shape::BorrowedSlice);
    assert_eq!(
        outcome(&slice, Predicate::GenerationWindow),
        Outcome::Missing(Need::WindowCoverage)
    );
}

#[test]
fn a04_distinct_reaching_arrays_do_not_share_a_generation() {
    let row = inspect(
        "pub unsafe fn witness(flag: bool) -> i32 { let a = [1_i32; 4]; let b = [2_i32; 4]; let p = if flag { a.as_ptr() } else { b.as_ptr() }; *p }",
    );
    assert_eq!(row.shape, Shape::MultipleRoots);
    assert_eq!(
        outcome(&row, Predicate::GenerationWindow),
        Outcome::Missing(Need::Generation)
    );
    assert_eq!(row.status, Status::NeedsFact);
}

#[test]
fn a05_retained_region_conflict_and_escape_do_not_get_element_proofs() {
    let conflict = inspect(
        "pub unsafe fn witness() -> i32 { let mut a = [1_i32; 4]; let p = a.as_mut_ptr(); a[3] = 9; *p }",
    );
    assert_eq!(conflict.shape, Shape::LocalArray);
    assert_eq!(
        outcome(&conflict, Predicate::FullRegionSchedule),
        Outcome::Missing(Need::Schedule)
    );
    let escape = inspect(
        "unsafe extern \"C\" { fn retain(p: *const i32); } pub unsafe fn witness() -> i32 { let a = [1_i32; 4]; let p = a.as_ptr(); retain(p); *p }",
    );
    assert_ne!(escape.status, Status::DecisionOnly);
    assert_eq!(
        outcome(&escape, Predicate::FullRegionSchedule),
        Outcome::Missing(Need::Schedule)
    );
}
