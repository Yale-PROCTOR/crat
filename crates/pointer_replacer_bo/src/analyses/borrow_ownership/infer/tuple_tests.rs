use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::Local;

use super::*;
use crate::utils::rustc::RustProgram;

fn program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
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
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

#[test]
fn tuple_layout_tracks_nested_structs_arrays_and_scalar_offsets() {
    ::utils::compilation::run_compiler_on_str(
        r#"
pub struct Outer { embedded: (usize, [Inner; 2]), behind: *mut (*mut Inner, *mut i32) }
pub struct Inner { first: *mut i32, second: *mut *mut i32 }
pub fn types(value: (usize, (*mut Inner, *mut *mut i32), [*mut i32; 2], ())) {}
"#,
        |tcx| {
            let program = program(tcx);
            let structs: Vec<_> = program.structs.iter().map(|did| did.to_def_id()).collect();
            let mut layout = StructCtxt::new(tcx, &structs);
            let outer = *structs
                .iter()
                .find(|did| tcx.item_name(**did).as_str() == "Outer")
                .unwrap();
            let outer_ty = tcx.type_of(outer).instantiate_identity();
            let body = tcx
                .mir_drops_elaborated_and_const_checked(program.functions[0])
                .borrow();
            let tuple = body.local_decls[Local::from_usize(1)].ty;
            for (precision, tuple_width, outer_width, array_offset) in
                [(1, 3, 3, 2), (2, 6, 6, 5), (3, 7, 8, 6)]
            {
                while layout.max_ptr_chased() < precision {
                    layout.increase_precision(tcx);
                }
                assert_eq!(layout.measure(tuple, 0), tuple_width);
                assert_eq!(layout.measure(outer_ty, 0), outer_width);
                assert_eq!(layout.field_offset(tuple, 0, 0), 0);
                assert_eq!(layout.field_offset(tuple, 1, 0), 0);
                assert_eq!(layout.field_offset(tuple, 2, 0), array_offset);
                assert_eq!(layout.field_offset(tuple, 3, 0), tuple_width);
            }
            let restricted = layout.with_max_precision(1);
            assert_eq!(restricted.measure(tuple, 0), 3);
            assert_eq!(restricted.field_offset(tuple, 2, 0), 2);
            assert_eq!(restricted.measure(outer_ty, 0), 3);
        },
    )
    .unwrap();
}

#[test]
fn tuple_precision_matching_preserves_sibling_identity_and_complete_tails() {
    ::utils::compilation::run_compiler_on_str(
        r#"
pub struct Inner { left: *mut i32, right: *mut i32 }
pub struct Outer { tuple: (*mut Inner, *mut i32), tail: *mut i32 }
pub fn types(first: (u8, *mut Inner, *mut i32), second: (*mut *mut *mut i32, *mut i32),
    third: *mut (*mut Inner, *mut i32), fourth: Outer) {}
"#,
        |tcx| {
            let program = program(tcx);
            let structs: Vec<_> = program.structs.iter().map(|did| did.to_def_id()).collect();
            let mut layout = StructCtxt::new(tcx, &structs);
            layout.increase_precision(tcx);
            layout.increase_precision(tcx);
            let body = tcx
                .mir_drops_elaborated_and_const_checked(program.functions[0])
                .borrow();
            for (argument, low, high, expected) in [
                (1, 1, 2, vec![(0, 0), (1, 3)]),
                (2, 2, 3, vec![(0, 0), (1, 1), (2, 3)]),
                (3, 2, 3, vec![(0, 0), (1, 1), (2, 4)]),
                (4, 1, 2, vec![(0, 0), (1, 3), (2, 4)]),
            ] {
                let ty = body.local_decls[Local::from_usize(argument)].ty;
                let lower = layout.with_max_precision(low).measure(ty, 0);
                let higher = layout.with_max_precision(high).measure(ty, 0);
                let mut pairs = Vec::new();
                matcher(
                    ty,
                    0..lower,
                    0..higher,
                    &layout,
                    &mut pairs,
                    |left, right, pairs| pairs.push((left, right)),
                );
                assert_eq!(pairs, expected);
                let mut reversed = Vec::new();
                matcher(
                    ty,
                    0..higher,
                    0..lower,
                    &layout,
                    &mut reversed,
                    |left, right, pairs| pairs.push((right, left)),
                );
                assert_eq!(reversed, expected);
            }
        },
    )
    .unwrap();
}

#[test]
fn tuple_scalar_and_native_container_fields_analyze_without_panicking() {
    for source in [
        "pub fn update(values: &mut (usize, usize)) { values.1 += 1; }",
        "pub fn update(values: &mut (Vec<i32>, Vec<i32>)) { values.0.push(1); values.1.push(2); }",
        r#"pub fn update(values: &mut (Vec<i32>, Vec<i32>)) -> i32 {
            let mut result = 0;
            for (index, (first, second)) in values.0.iter().zip(&values.1).enumerate() {
                result += index as i32 + *first + *second;
            }
            result
        }"#,
    ] {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            crate::analyze_pointers(tcx).expect("native tuple fields must be analyzable");
        })
        .unwrap();
    }
}

#[test]
fn tuple_null_vacuity_covers_only_the_selected_nested_element() {
    use crate::analyses::borrow_ownership::null_paths::{NullPlace, Proj, vacuous_components_with};
    ::utils::compilation::run_compiler_on_str(
        "pub struct Opaque<T> { value: T, tail: *mut i32 }
         pub fn types(value: *mut (usize, (*mut *mut i32, usize), *mut i32), opaque: *mut Opaque<*mut i32>, pair: (*mut *mut i32, *mut i32)) {}",
        |tcx| {
            let program = program(tcx);
            let body = tcx
                .mir_drops_elaborated_and_const_checked(program.functions[0])
                .borrow();
            let local = Local::from_usize(1);
            let ty = body.local_decls[local].ty;
            let structs: Vec<_> = program.structs.iter().map(|did| did.to_def_id()).collect();
            let mut layout = StructCtxt::new(tcx, &structs);
            layout.increase_precision(tcx);
            layout.increase_precision(tcx);
            let facts = [NullPlace {
                local,
                proj: smallvec::smallvec![Proj::Deref, Proj::Field(1), Proj::Field(0)],
            }];
            assert_eq!(
                vacuous_components_with(tcx, &layout, ty, 4, &facts),
                [false, true, true, false]
            );
            let restricted = layout.with_max_precision(1);
            assert_eq!(
                vacuous_components_with(tcx, &restricted, ty, 1, &facts),
                [false]
            );
            let local = Local::from_usize(2);
            let opaque = body.local_decls[local].ty;
            for (field, expected) in [(0, [false, false]), (1, [false, true])] {
                let facts = [NullPlace { local, proj: smallvec::smallvec![Proj::Deref, Proj::Field(field)] }];
                assert_eq!(vacuous_components_with(tcx, &layout, opaque, 2, &facts), expected);
            }
            let local = Local::from_usize(3);
            let pair = body.local_decls[local].ty;
            let facts = [NullPlace {
                local,
                proj: smallvec::smallvec![Proj::Field(0), Proj::Deref],
            }];
            assert_eq!(vacuous_components_with(tcx, &restricted, pair, 2, &facts), [false, false]);
        },
    )
    .unwrap();
}

#[test]
fn tuple_aggregate_copy_call_and_return_keep_exact_component_transfers() {
    use crate::analyses::borrow_ownership::{
        licensing::graph_tests::with_facts,
        ownership_boundary::Role,
        ownership_occurrence::{Availability, PathStep},
    };
    with_facts(
        r#"
pub unsafe fn identity(pair: (u8, *mut *mut i32, (bool, *mut i32)))
    -> (u8, *mut *mut i32, (bool, *mut i32)) { pair }
pub unsafe fn use_pair(first: *mut *mut i32, second: *mut i32) -> *mut i32 {
    let nested = (false, second);
    let pair = (7u8, first, nested);
    let copy = pair;
    let result = identity(copy);
    result.2.1
}

"#,
        |facts| {
            let transfers: std::collections::BTreeSet<_> = facts
                .equations
                .iter()
                .filter_map(|equation| equation.transfer.as_ref())
                .collect();
            let tuple_transfers: Vec<_> = transfers
                .iter()
                .copied()
                .filter(|transfer| {
                    matches!(&transfer.destination, Availability::Present(binding)
                if binding.path.iter().any(|step| matches!(step, PathStep::TupleElement { .. })))
                })
                .collect();
            assert!(
                tuple_transfers.len() >= 4,
                "tuple initialization/copy must transfer represented components"
            );
            for transfer in tuple_transfers {
                assert!(matches!(&transfer.source, Availability::Present(_)));
                let laws: Vec<_> = facts
                    .equations
                    .iter()
                    .filter(|equation| equation.transfer.as_ref() == Some(transfer))
                    .collect();
                assert!(laws.iter().any(
                    |equation| equation.operation == "linear" || equation.operation == "equal"
                ));
                assert!(laws.iter().any(|equation| equation.operation == "assume"
                    && equation.variables == [transfer.destination_use]
                    && equation.value == Some(false)));
            }
            for role in [Role::CallArgument, Role::ReturnReceiver] {
                assert!(
                    facts
                        .boundary_substitutions
                        .iter()
                        .any(|boundary| boundary.role == role
                            && boundary.callee.as_deref() == Some("identity")
                            && boundary.matched.len() == 3),
                    "tuple boundary must align all pointer components"
                );
            }
        },
    );
}
