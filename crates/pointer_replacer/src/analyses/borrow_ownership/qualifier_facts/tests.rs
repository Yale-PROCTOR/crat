//! F01–F03 compiler-backed export witnesses. No fixture is executed.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::{Local, RETURN_PLACE, VarDebugInfoContents},
    ty::TyKind,
};
use rustc_span::def_id::LocalDefId;

use super::*;
use crate::{
    analyses::borrow_ownership::{
        nullability, slot_key,
        slots::{SlotId, SlotOwner},
        solver::SlotRef,
    },
    utils::rustc::RustProgram,
};

fn inspect(
    source: &str,
    check: impl FnOnce(&RustProgram<'_>, &CrateSlots, &MutFacts, &NullabilityFacts, &QualifierFacts)
    + Sync
    + Send,
) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
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
        let mutability = MutFacts::from_program(&program);
        let nullable = nullability::analyze(tcx, &program.functions, &slots);
        let facts = collect(&program, &slots, &mutability, &nullable);
        check(&program, &slots, &mutability, &nullable, &facts);
    })
    .unwrap_or_else(|error| error.raise());
}

fn function(program: &RustProgram<'_>, name: &str) -> LocalDefId {
    let found: Vec<_> = program
        .functions
        .iter()
        .copied()
        .filter(|did| program.tcx.item_name(did.to_def_id()).as_str() == name)
        .collect();
    assert_eq!(found.len(), 1, "exact function {name}");
    found[0]
}

fn local(program: &RustProgram<'_>, name: &str, binding: &str) -> (LocalDefId, Local) {
    let did = function(program, name);
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(did)
        .borrow();
    let found: BTreeSet<_> = body
        .var_debug_info
        .iter()
        .filter_map(|info| {
            if info.name.as_str() != binding {
                return None;
            }
            let VarDebugInfoContents::Place(place) = info.value else { return None };
            place.as_local()
        })
        .collect();
    assert_eq!(found.len(), 1, "exact source local {name}::{binding}");
    (did, *found.iter().next().unwrap())
}

fn local_key(program: &RustProgram<'_>, name: &str, binding: &str, depth: u8) -> String {
    let (did, local) = local(program, name, binding);
    slot_key::local_key(program.tcx, did, local.as_usize(), depth)
}

fn field_key(program: &RustProgram<'_>, name: &str, field: &str, depth: u8) -> String {
    let found: Vec<_> = program
        .structs
        .iter()
        .copied()
        .filter(|did| program.tcx.item_name(did.to_def_id()).as_str() == name)
        .collect();
    assert_eq!(found.len(), 1);
    let did = found[0];
    let TyKind::Adt(definition, _) = program.tcx.type_of(did).skip_binder().kind() else {
        panic!("fixture struct");
    };
    let fields: Vec<_> = definition
        .all_fields()
        .enumerate()
        .filter_map(|(index, definition)| (definition.name.as_str() == field).then_some(index))
        .collect();
    assert_eq!(fields.len(), 1);
    slot_key::field_key(program.tcx, did, fields[0], depth)
}

fn row<'a>(facts: &'a QualifierFacts, key: &str) -> &'a SlotFacts {
    let found: Vec<_> = facts.rows.iter().filter(|row| row.slot == key).collect();
    assert_eq!(found.len(), 1, "exact canonical availability row {key}");
    found[0]
}

fn catalog(program: &RustProgram<'_>, slots: &CrateSlots) -> BTreeMap<String, SlotRef> {
    let mut rows = BTreeMap::new();
    for (&did, universe) in &slots.fn_local_slots {
        for index in 0..universe.len() {
            let id = SlotId::from_usize(index);
            let slot = universe.slot(id);
            let SlotOwner::Local(local) = slot.owner else { panic!("local universe") };
            assert!(
                rows.insert(
                    slot_key::local_key(program.tcx, did, local.as_usize(), slot.depth),
                    SlotRef::Local(did, id)
                )
                .is_none()
            );
        }
    }
    for index in 0..slots.field_slots.len() {
        let id = SlotId::from_usize(index);
        let slot = slots.field_slots.slot(id);
        let SlotOwner::Field(field) = slot.owner else { panic!("field universe") };
        assert!(
            rows.insert(
                slot_key::field_key(program.tcx, field.struct_did, field.field_index, slot.depth),
                SlotRef::Field(id)
            )
            .is_none()
        );
    }
    rows
}

#[test]
fn e5_x_facts_raw_reference_levels_and_field_local_keys_are_exact() {
    inspect(
        r#"
pub struct Holder<'a> { raw: *mut *const i32, ref_inner: *mut &'a i32 }
pub unsafe fn levels<'a>(raw: *mut *const i32, by_ref: &mut *const i32, h: *mut Holder<'a>) {
    let _ = raw; let _ = by_ref; let _ = h;
}
"#,
        |program, slots, _, _, facts| {
            for (name, expected) in [
                ("raw", [PointerLevel::Raw, PointerLevel::Raw]),
                ("by_ref", [PointerLevel::Reference, PointerLevel::Raw]),
            ] {
                for (depth, level) in expected.into_iter().enumerate() {
                    let found = row(facts, &local_key(program, "levels", name, depth as u8));
                    assert_eq!(
                        (found.depth, found.level, found.qualifier_offset),
                        (depth as u8, Some(level), depth)
                    );
                }
            }
            for (name, expected) in [
                ("raw", [PointerLevel::Raw, PointerLevel::Raw]),
                ("ref_inner", [PointerLevel::Raw, PointerLevel::Reference]),
            ] {
                for (depth, level) in expected.into_iter().enumerate() {
                    let found = row(facts, &field_key(program, "Holder", name, depth as u8));
                    assert_eq!(
                        (found.depth, found.level, found.qualifier_offset),
                        (depth as u8, Some(level), depth)
                    );
                }
            }
            let expected = catalog(program, slots);
            assert_eq!(facts.rows.len(), expected.len(), "one row per modeled slot");
            assert_eq!(
                facts
                    .rows
                    .iter()
                    .map(|row| row.slot.clone())
                    .collect::<BTreeSet<_>>(),
                expected.into_keys().collect()
            );
        },
    );
}

#[test]
fn e5_x_facts_fatness_distinguishes_outer_inner_and_field_indices() {
    inspect(
        r#"
pub struct Fields { pointers: *mut *mut i32 }
pub unsafe fn inner(pp: *mut *mut i32) -> i32 { let p = *pp; *p.offset(1) }
pub unsafe fn outer(pp: *mut *mut i32) -> *mut i32 { *pp.offset(1) }
pub unsafe fn field_inner(s: *mut Fields) -> i32 { let p = *(*s).pointers; *p.offset(1) }
"#,
        |program, _, _, _, facts| {
            for (function, expected) in [
                ("inner", [FatnessFact::PtrDefault, FatnessFact::ArrayLike]),
                ("outer", [FatnessFact::ArrayLike, FatnessFact::PtrDefault]),
            ] {
                for (depth, expected) in expected.into_iter().enumerate() {
                    assert_eq!(
                        row(facts, &local_key(program, function, "pp", depth as u8)).fatness,
                        Availability::Present(expected),
                        "fatness {function} depth {depth}"
                    );
                }
            }
            for (depth, expected) in [FatnessFact::PtrDefault, FatnessFact::ArrayLike]
                .into_iter()
                .enumerate()
            {
                assert_eq!(
                    row(
                        facts,
                        &field_key(program, "Fields", "pointers", depth as u8)
                    )
                    .fatness,
                    Availability::Present(expected),
                    "field qualifier depth {depth}"
                );
            }
        },
    );
}

#[test]
fn e5_x_facts_missing_inner_return_and_field_facts_stay_explicit() {
    inspect(
        r#"
pub struct Record { pointer: *mut *mut i32 }
pub unsafe fn nested(pp: *mut *mut i32) { let _ = pp; }
pub unsafe fn returns(p: *mut i32) -> *mut i32 { p }
"#,
        |program, _, _, _, facts| {
            let inner = row(facts, &local_key(program, "nested", "pp", 1));
            assert_eq!(
                inner.sign,
                Availability::Missing(MissingFact::InnerSignNotRepresented)
            );
            assert_eq!(
                inner.mutability,
                Availability::Missing(MissingFact::InnerMutabilityNotRepresented)
            );
            let returned = slot_key::local_key(
                program.tcx,
                function(program, "returns"),
                RETURN_PLACE.as_usize(),
                0,
            );
            assert_eq!(
                row(facts, &returned).sign,
                Availability::Missing(MissingFact::ReturnSignNotExported)
            );
            let field = row(facts, &field_key(program, "Record", "pointer", 0));
            assert_eq!(
                field.sign,
                Availability::Missing(MissingFact::FieldSignCoverageNotExported)
            );
            assert_eq!(
                field.mutability,
                Availability::Missing(MissingFact::FieldMutabilityNotRepresented)
            );
        },
    );
}

#[test]
fn e5_x_facts_existing_sign_bits_remain_two_way_and_field_keyed() {
    inspect(
        r#"
pub struct SignedField { pointer: *mut i32 }
pub unsafe fn nonnegative(p: *mut i32) -> i32 { *p.offset(1) }
pub unsafe fn negative(p: *mut i32, n: isize) -> i32 { *p.offset(n) }
pub unsafe fn field(s: *mut SignedField, n: isize) -> i32 { let p = (*s).pointer; *p.offset(n) }
"#,
        |program, _, _, _, facts| {
            assert_eq!(
                row(facts, &local_key(program, "nonnegative", "p", 0)).sign,
                Availability::Present(SignFact::Nonnegative)
            );
            assert_eq!(
                row(facts, &local_key(program, "negative", "p", 0)).sign,
                Availability::Present(SignFact::NegOrUnknown)
            );
            assert_eq!(
                row(facts, &field_key(program, "SignedField", "pointer", 0)).sign,
                Availability::Present(SignFact::NegOrUnknown)
            );
        },
    );
}

#[test]
fn e5_x_facts_ptr_default_is_not_array_evidence_or_unregistered_array_depth() {
    inspect(
        r#"
pub struct Plain { pointer: *const i32, array: [*mut i32; 3] }
pub unsafe fn thin(p: *const i32) -> i32 { *p }
"#,
        |program, slots, _, _, facts| {
            assert_eq!(
                row(facts, &local_key(program, "thin", "p", 0)).fatness,
                Availability::Present(FatnessFact::PtrDefault)
            );
            assert_eq!(
                row(facts, &field_key(program, "Plain", "pointer", 0)).fatness,
                Availability::Present(FatnessFact::PtrDefault)
            );
            let unregistered = field_key(program, "Plain", "array", 0);
            assert!(
                !catalog(program, slots).contains_key(&unregistered),
                "array registration belongs to G"
            );
            assert!(
                facts.rows.iter().all(|row| row.slot != unregistered),
                "F must not add an unconstrained array slot"
            );
        },
    );
}

#[test]
fn e5_x_facts_null_signals_and_supplied_outer_mutability_keep_their_slots() {
    inspect(
        r#"
pub struct Holder { nullable: *mut i32, other: *mut i32 }
pub unsafe fn signals(pp: *mut *mut i32, plain: *mut i32) {
    let null_local: *mut i32 = 0 as *mut i32;
    *pp = 0 as *mut i32;
    let holder = Holder { nullable: 0 as *mut i32, other: plain };
    let observed = plain.is_null();
    *plain = 3;
    let _ = null_local; let _ = holder; let _ = observed;
}
"#,
        |program, slots, mutability, nullable, facts| {
            let all = catalog(program, slots);
            for (key, slot) in &all {
                let found = row(facts, key);
                assert_eq!(
                    found.null_use,
                    nullable.is_null_use.contains(slot),
                    "null use at {key}"
                );
                assert_eq!(
                    found.null_literal,
                    nullable.null_literal.contains(slot),
                    "null literal at {key}"
                );
                if let SlotRef::Local(did, id) = *slot {
                    let descriptor = slots.fn_local_slots[&did].slot(id);
                    if descriptor.depth == 0 {
                        let SlotOwner::Local(local) = descriptor.owner else {
                            panic!("local qualifier slot")
                        };
                        assert_eq!(
                            found.mutability,
                            Availability::Present(MutabilityFact {
                                mutable: mutability.is_mutable(did, local),
                                defaulted: mutability.is_defaulted(did, local),
                            }),
                            "supplied outer replay summary at {key}"
                        );
                    }
                }
            }
            assert!(row(facts, &local_key(program, "signals", "null_local", 0)).null_literal);
            assert!(row(facts, &local_key(program, "signals", "pp", 1)).null_literal);
            assert!(!row(facts, &local_key(program, "signals", "pp", 0)).null_literal);
            assert!(row(facts, &field_key(program, "Holder", "nullable", 0)).null_literal);
            assert!(!row(facts, &field_key(program, "Holder", "other", 0)).null_literal);
            let plain = row(facts, &local_key(program, "signals", "plain", 0));
            assert!(!plain.null_literal);
            assert_eq!(
                plain.mutability,
                Availability::Present(MutabilityFact {
                    mutable: true,
                    defaulted: false
                })
            );
        },
    );
}
